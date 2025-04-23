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

# Debug log filename\ nlog_file = "mcdc_debug_log.txt"
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
                        fields = {fld.spelling for fld in c.get_children() if fld.kind.name == 'FIELD_DECL'}
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
    Recursively find MEMBER_REF_EXPR nodes under 'node' that correspond to struct fields in 'fields_map'.
    Returns list of tuples ("base.field", "field").
    """
    atoms = []
    def find_base(n):
        cur = n
        while cur:
            if cur.kind == CursorKind.DECL_REF_EXPR:
                return cur.spelling
            cur = getattr(cur, 'semantic_parent', None)
        return None

    def visit(n):
        if n.kind == CursorKind.MEMBER_REF_EXPR:
            field = n.spelling
            base = find_base(n)
            if base in fields_map and field in fields_map[base]:
                key = f"{base}.{field}"
                atoms.append((key, field))
                logging.debug(f"Matched atom: {key}")
        for c in n.get_children():
            visit(c)
    visit(node)
    return atoms

def gather_conditions(fn_cursor, fields_map):
    """
    Traverse function AST to extract condition atoms for MC/DC.
    Supports if, while, and conditional operators.
    """
    atoms = []
    def recurse(n):
        if n.kind == CursorKind.IF_STMT:
            # First child is the condition expression
            cond = next(n.get_children(), None)
            if cond:
                atoms.extend(gather_atoms_and_fields(cond, fields_map))
        elif n.kind == CursorKind.WHILE_STMT:
            cond = next(n.get_children(), None)
            if cond:
                atoms.extend(gather_atoms_and_fields(cond, fields_map))
        elif n.kind == CursorKind.CONDITIONAL_OPERATOR:
            # Ternary operator: condition is first child
            cond = next(n.get_children(), None)
            if cond:
                atoms.extend(gather_atoms_and_fields(cond, fields_map))
        # Recurse all children
        for c in n.get_children():
            recurse(c)
    recurse(fn_cursor)
    # Deduplicate preserving order
    uniq = []
    for a in atoms:
        if a not in uniq:
            uniq.append(a)
    logging.debug(f"Atoms for {fn_cursor.spelling}: {uniq}")
    return uniq

def solve_mcdc(fields, atoms):
    """
    Solve for MC/DC: toggle each field while others are true.
    Returns list of (atom, {field: value}) test vectors.
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
    Generate GoogleTest .cpp file with MC/DC cases.
    """
    params = list(fn.get_arguments())
    names = [p.spelling for p in params]
    types = [p.type.spelling.replace('*', '').strip() for p in params]
    path = os.path.join(out_dir, f"testMCDC_{fn.spelling}.cpp")
    with open(path, 'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write('#include "mycode.h"\n\n')
        for i, (atom, vec) in enumerate(cases, 1):
            f.write(f'TEST({fn.spelling}_MC_DC, Case{i}) {{\n')
            # Initialize all struct parameters to zero
            for nm, tp in zip(names, types):
                f.write(f'  {tp} {nm} = {{0}};\n')
            # Assign only valid struct members
            for base_field, _ in cases:
                pass
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
        # Build fields_map for parameters
        args = list(fn.get_arguments())
        fields_map = {}
        for p in args:
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
        fields = set(f for fmap in fields_map.values() for f in fmap)
        cases = solve_mcdc(fields, atoms)
        # Filter valid atoms
        filtered = [(a,v) for (a,v) in cases if a.split('.',1)[0] in fields_map]
        if filtered:
            write_test_file(fn, filtered, fields_map, tst)
        else:
            logging.warning(f"No MC/DC cases for {fn.spelling}")

if __name__ == '__main__':
    main()
