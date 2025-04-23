#!/usr/bin/env python3
"""
MC/DC Test Generator for C functions using Clang and Z3
Usage:
  python generate_mcdc_tests.py <src_dir> <include_dir> <test_dir>
"""
import os
import sys
import z3
import logging
from clang.cindex import Config, Index, CursorKind, LibclangError

# Debug log filename
log_file = "mcdc_debug_log.txt"
logging.basicConfig(
    filename=log_file,
    filemode='w',
    level=logging.DEBUG,
    format='[%(levelname)s] %(message)s'
)
print(f"[INFO] Debug log written to '{log_file}'")


def load_libclang():
    """Load libclang from environment or fallback paths."""
    path = os.getenv("LIBCLANG_PATH")
    logging.debug(f"LIBCLANG_PATH={path}")
    if path and os.path.exists(path):
        try:
            Config.set_library_file(path)
            logging.debug(f"Loaded libclang from {path}")
            return
        except LibclangError as e:
            logging.error(f"Failed to load libclang: {e}")
    for candidate in [
        r"C:\\Program Files\\LLVM\\bin\\libclang.dll",
        r"C:\\Program Files (x86)\\LLVM\\bin\\libclang.dll",
    ]:
        if os.path.exists(candidate):
            try:
                Config.set_library_file(candidate)
                logging.debug(f"Loaded libclang from {candidate}")
                return
            except LibclangError as e:
                logging.error(f"Fallback load failed for {candidate}: {e}")
    logging.fatal("libclang.dll not found or incompatible.")
    sys.exit(1)


def normalize_path(p):
    abs_p = os.path.abspath(p)
    logging.debug(f"Normalized path: {p} -> {abs_p}")
    return abs_p


def parse_headers(include_dir):
    """Parse headers to collect all struct types and their fields."""
    logging.debug(f"Parsing headers in {include_dir}")
    index = Index.create()
    types = {}
    for root, _, files in os.walk(include_dir):
        for fname in files:
            if fname.endswith('.h'):
                full_path = os.path.join(root, fname)
                logging.debug(f"Parsing header: {full_path}")
                tu = index.parse(full_path, args=[f'-I{include_dir}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.STRUCT_DECL and c.spelling:
                        fields = {f.spelling for f in c.get_children() if f.kind.name == 'FIELD_DECL'}
                        logging.debug(f"Struct {c.spelling} fields: {fields}")
                        types[c.spelling] = fields
    return types


def parse_functions(src_dir, include_dir):
    """Parse C source files to collect function definitions."""
    logging.debug(f"Parsing sources in {src_dir}")
    index = Index.create()
    funcs = []
    for root, _, files in os.walk(src_dir):
        for fname in files:
            if fname.endswith('.c'):
                full_path = os.path.join(root, fname)
                logging.debug(f"Parsing source: {full_path}")
                tu = index.parse(full_path, args=[f'-I{include_dir}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.FUNCTION_DECL and c.is_definition():
                        logging.debug(f"Found function: {c.spelling}")
                        funcs.append(c)
    return funcs


def gather_atoms_and_fields(node, fields_map):
    """
    Recursively find MEMBER_REF_EXPR and DECL_REF_EXPR nodes under 'node' that correspond to struct fields in 'fields_map'.
    Returns list of tuples ("base.field", "field").
    """
    atoms = []
    
    def visit(n):
        logging.debug(f"Visiting node: kind={n.kind}, spelling={n.spelling}")
        # Detect direct member reference expressions
        if n.kind == CursorKind.MEMBER_REF_EXPR:
            field = n.spelling
            # find base by checking first child
            base = None
            for ch in n.get_children():
                if ch.kind == CursorKind.DECL_REF_EXPR:
                    base = ch.spelling
                    break
            if base and base in fields_map and field in fields_map[base]:
                key = f"{base}.{field}"
                atoms.append((key, field))
                logging.debug(f"Matched MEMBER_REF_EXPR atom: {key}")
        # Fallback: direct field reference in DECL_REF_EXPR
        elif n.kind == CursorKind.DECL_REF_EXPR:
            name = n.spelling
            for base, fields in fields_map.items():
                if name in fields:
                    key = f"{base}.{name}"
                    if (key, name) not in atoms:
                        atoms.append((key, name))
                        logging.debug(f"Matched DECL_REF_EXPR atom: {key}")
        # recurse children
        for c in n.get_children():
            visit(c)
    visit(node)
    return atoms


def gather_conditions(fn_cursor, fields_map):
    """
    Traverse function AST to extract all condition atoms for MC/DC.
    Handles if/while conditions and local DECL_STMT initializers (ternary, binary ops).
    """
    atoms = []
    def recurse(node):
        logging.debug(f"[COND_VISIT] node={node.kind} spelling={node.spelling}")
        # IF and WHILE statements
        if node.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT):
            cond = next(node.get_children(), None)
            # Skip parentheses
            if cond and cond.kind == CursorKind.PAREN_EXPR:
                cond = next(cond.get_children(), None)
            if cond:
                logging.debug(f"[COND_EXPR] kind={cond.kind} spelling={cond.spelling}")
                atoms.extend(gather_atoms_and_fields(cond, fields_map))
        # Local variable declarations with initializer (includes ternary)
        elif node.kind == CursorKind.DECL_STMT:
            for var in node.get_children():
                if var.kind == CursorKind.VAR_DECL:
                    for init in var.get_children():
                        if init.kind in (CursorKind.UNEXPOSED_EXPR, CursorKind.BINARY_OPERATOR, CursorKind.CONDITIONAL_OPERATOR):
                            logging.debug(f"[DECL_INIT] kind={init.kind} spelling={init.spelling}")
                            atoms.extend(gather_atoms_and_fields(init, fields_map))
        # Recurse into children
        for c in node.get_children():
            recurse(c)
    recurse(fn_cursor)
    # Deduplicate
    uniq = []
    for a in atoms:
        if a not in uniq:
            uniq.append(a)
    logging.debug(f"Atoms for {fn_cursor.spelling}: {uniq}")
    return uniq


def solve_mcdc(fields, atoms):
    """
    Generate MC/DC test vectors by toggling each atom's field while others are true.
    """
    tests = []
    z3vars = {f: z3.Int(f) for f in fields}
    for atom, _ in atoms:
        fld = atom.split('.', 1)[1]
        for val in (0, 1):
            s = z3.Solver()
            for f in fields:
                s.add(z3vars[f] == (val if f == fld else 1))
            if s.check() == z3.sat:
                m = s.model()
                vec = {f: m[z3vars[f]].as_long() for f in fields}
                tests.append((atom, vec))
                logging.debug(f"Test vec for {atom}: {vec}")
                break
    return tests


def write_test_file(fn, cases, fields_map, out_dir):
    """
    Generate a GoogleTest .cpp file for the given function and MC/DC cases.
    """
    params = list(fn.get_arguments())
    names = [p.spelling for p in params]
    types_ = [p.type.spelling.replace('*', '').strip() for p in params]
    path = os.path.join(out_dir, f"testMCDC_{fn.spelling}.cpp")
    with open(path, 'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write('#include "mycode.h"\n\n')
        for i, (atom, vec) in enumerate(cases, 1):
            f.write(f'TEST({fn.spelling}_MC_DC, Case{i}) {{\n')
            # Initialize struct parameters
            for nm, tp in zip(names, types_):
                f.write(f'  {tp} {nm} = {{0}};\n')
            # Assign MC/DC values to valid struct members
            for key, val in vec.items():
                base, field = key.split('.', 1)
                f.write(f'  {base}.{field} = {val};\n')
            # Call function under test
            args_call = ', '.join(f'&{nm}' for nm in names)
            f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}({args_call})); // {atom}\n')
            f.write('}\n\n')
    logging.info(f"Generated: {path}")


def main():
    if len(sys.argv) != 4:
        print("Usage: python generate_mcdc_tests.py <src_dir> <include_dir> <test_dir>")
        return
    src = normalize_path(sys.argv[1])
    inc = normalize_path(sys.argv[2])
    tst = normalize_path(sys.argv[3])
    os.makedirs(tst, exist_ok=True)
    
    load_libclang()
    types = parse_headers(inc)
    funcs = parse_functions(src, inc)
    logging.debug(f"Parsed {len(funcs)} functions.")

    for fn in funcs:
        # Build map of parameter names to struct fields set
        params = list(fn.get_arguments())
        fields_map = {}
        for p in params:
            nm = p.spelling
            tp = p.type.spelling.replace('*', '').strip()
            if tp in types:
                fields_map[nm] = types[tp]
        if not fields_map:
            logging.warning(f"No struct parameters for {fn.spelling}")
            continue
        atoms = gather_conditions(fn, fields_map)
        if not atoms:
            logging.warning(f"No condition atoms for {fn.spelling}")
            continue
        fields = set()
        for fm in fields_map.values():
            fields.update(fm)
        cases = solve_mcdc(fields, atoms)
        # Filter cases by valid parameter base
        filtered = [(a, v) for a, v in cases if a.split('.',1)[0] in fields_map]
        if filtered:
            write_test_file(fn, filtered, fields_map, tst)
        else:
            logging.warning(f"No MC/DC cases for {fn.spelling}")

if __name__ == '__main__':
    main()
