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

def parse_headers(inc_dir):
    logging.debug(f"Parsing headers in {inc_dir}")
    index = Index.create()
    types = {}
    for root, _, files in os.walk(inc_dir):
        for fname in files:
            if fname.endswith('.h'):
                full = os.path.join(root, fname)
                logging.debug(f"Parsing {full}")
                tu = index.parse(full, args=[f'-I{inc_dir}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.STRUCT_DECL and c.spelling:
                        fields = [fld.spelling for fld in c.get_children() if fld.kind.name == 'FIELD_DECL']
                        logging.debug(f"Struct {c.spelling} fields: {fields}")
                        types[c.spelling] = c
    return types

def parse_functions(src_dir, inc_dir):
    logging.debug(f"Parsing sources in {src_dir}")
    index = Index.create()
    funcs = []
    for root, _, files in os.walk(src_dir):
        for fname in files:
            if fname.endswith('.c'):
                full = os.path.join(root, fname)
                logging.debug(f"Parsing {full}")
                tu = index.parse(full, args=[f'-I{inc_dir}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.FUNCTION_DECL and c.is_definition():
                        logging.debug(f"Found function: {c.spelling}")
                        funcs.append(c)
    return funcs

def gather_atoms_and_fields(cond_cursor, fields_map):
    """
    Extract atomic conditions from the AST, mapping to struct parameters and conditional expressions.
    fields_map: dict of {param_name: set(of field names)}
    Returns list of (base.field, field) tuples.
    """
    atoms = []
    def find_base(n):
        cur = n
        while cur is not None:
            if cur.kind == CursorKind.DECL_REF_EXPR:
                return cur.spelling
            cur = getattr(cur, 'semantic_parent', None)
        return None

    def visit(node):
        # Handle member reference expressions
        if node.kind == CursorKind.MEMBER_REF_EXPR:
            field_name = node.spelling
            base = find_base(node)
            if base and base in fields_map and field_name in fields_map[base]:
                key = f"{base}.{field_name}"
                atoms.append((key, field_name))
                logging.debug(f"Matched atom: {key}")
        # Handle binary comparisons (e.g., <=, <, >, ==)
        elif node.kind == CursorKind.BINARY_OPERATOR:
            # Check children for member refs
            children = list(node.get_children())
            for ch in children:
                if ch.kind == CursorKind.MEMBER_REF_EXPR:
                    visit(ch)
        # Handle ternary conditional operator
        elif node.kind == CursorKind.CONDITIONAL_OPERATOR:
            # children: condition, trueExpr, falseExpr
            children = list(node.get_children())
            if children:
                # visit only the condition part
                visit(children[0])
        # Recurse into all children
        for child in node.get_children():
            visit(child)
    visit(cond_cursor)
    return atoms

def gather_conditions(fn_cursor, fields_map):
    """
    Traverse the function AST to collect all condition atoms based on fields_map.
    """
    atoms = []
    def recurse(node):
        if node.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT, CursorKind.CONDITIONAL_OPERATOR):
            # Visit entire expression subtree under condition
            for ch in node.get_children():
                atoms.extend(gather_atoms_and_fields(ch, fields_map))
        for ch in node.get_children():
            recurse(ch)
    recurse(fn_cursor)
    # Deduplicate
    uniq = []
    for a in atoms:
        if a not in uniq:
            uniq.append(a)
    logging.debug(f"Atoms for {fn_cursor.spelling}: {uniq}")
    return uniq

def solve_mcdc(_, atoms):
    fields = {atom.split('.',1)[1] for atom, _ in atoms}
    logging.debug(f"Solving MC/DC for fields: {fields}")
    z3vars = {f: z3.Int(f) for f in fields}
    tests = []
    for atom, _ in atoms:
        fld = atom.split('.',1)[1]
        for val in (0,1):
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

def write_test_file(fn, cases, out_dir):
    args = list(list(fn.get_arguments()))
    # Parameter names and types from signature
    name0 = args[0].spelling
    type0 = args[0].type.spelling.replace('*','').strip()
    name1 = None; type1 = None
    if len(args) > 1:
        name1 = args[1].spelling
        type1 = args[1].type.spelling.replace('*','').strip()
    path = os.path.join(out_dir, f"testMCDC_{fn.spelling}.cpp")
    with open(path, 'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write('#include "mycode.h"\n\n')
        for i, (label, vec) in enumerate(cases, 1):
            f.write(f'TEST({fn.spelling}_MC_DC, Case{i}) {{\n')
            # Init parameters
            f.write(f'  {type0} {name0} = {{0}};\n')
            if name1:
                f.write(f'  {type1} {name1} = {{0}};\n')
            # Assign only valid struct members
            for atom, _ in cases:
                pass  # skip placeholder
            for field, value in vec.items():
                if field in vec:
                    if name1 and field in cases[
                        0][1]:
                        f.write(f'  {name1}.{field} = {value};\n')
                    else:
                        f.write(f'  {name0}.{field} = {value};\n')
            # Call function under test
            if name1:
                f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}(&{name0}, &{name1})); // {label}\n')
            else:
                f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}(&{name0})); // {label}\n')
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
        # Determine struct fields from first parameter
        arg0 = list(list(fn.get_arguments()))[0]
        type0 = arg0.type.spelling.replace('*','').strip()
        cursor = types.get(type0)
        if not cursor:
            logging.warning(f"Struct {type0} not found for {fn.spelling}, skipping.")
            continue
        fields = {f.spelling for f in cursor.get_children() if f.kind.name == 'FIELD_DECL'}
        atoms = gather_conditions(fn, fields)
        cases = solve_mcdc(fields, atoms)
        # Filter to valid struct members
        base0 = list(list(fn.get_arguments()))[0].spelling
        case_filtered = []
        for atom, vec in cases:
            b, fld = atom.split('.',1)
            if b == base0 and fld in fields:
                case_filtered.append((atom, vec))
        if case_filtered:
            write_test_file(fn, case_filtered, tst)
        else:
            logging.warning(f"No MC/DC cases for {fn.spelling}")

if __name__ == '__main__':
    main()
