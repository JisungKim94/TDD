#!/usr/bin/env python3
"""
MC/DC Test Generator for C functions using Clang and Z3
Usage:
  python generate_mcdc_tests.py <src_dir> <include_dir> <test_dir>

- Parses all headers under <include_dir> to collect struct and enum definitions.
- Parses all .c files under <src_dir>, extracts functions and their conditional atoms.
- Uses Z3 to solve for MC/DC vectors for each atomic condition.
- Emits GoogleTest .cpp files under <test_dir> with EXPECT_NO_FATAL_FAILURE checks.
"""
import os
import sys
from clang.cindex import Index, CursorKind, TypeKind
from z3 import Solver, Int, Bool


def parse_headers(include_path):
    """Recursively parse headers to collect struct/enum definitions"""
    types = {}
    index = Index.create()
    for root, _, files in os.walk(include_path):
        for fname in files:
            if fname.endswith('.h'):
                path = os.path.join(root, fname)
                tu = index.parse(path, args=[f'-I{include_path}'])
                for c in tu.cursor.get_children():
                    if c.kind in (CursorKind.STRUCT_DECL, CursorKind.ENUM_DECL, CursorKind.TYPEDEF_DECL):
                        if c.spelling:
                            types[c.spelling] = c
    return types


def parse_functions(src_path, include_path):
    """Parse all .c files to find function definitions"""
    index = Index.create()
    funcs = []
    for root, _, files in os.walk(src_path):
        for fname in files:
            if fname.endswith('.c'):
                path = os.path.join(root, fname)
                tu = index.parse(path, args=[f'-I{include_path}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.FUNCTION_DECL and c.is_definition():
                        funcs.append(c)
    return funcs


def extract_atoms(expr):
    """Naive placeholder: return atomic sub-expressions as strings"""
    # TODO: implement AST-based splitting for &&, ||, ?:, comparisons, etc.
    text = expr.spelling or expr.displayname or ''
    return [text] if text else []


def gather_conditions(fn_cursor):
    """Walk AST to collect all atomic conditions in a function"""
    atoms = []
    def recurse(node):
        if node.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT, CursorKind.CONDITIONAL_OPERATOR):
            cond = list(node.get_children())[0]
            atoms.extend(extract_atoms(cond))
        for ch in node.get_children(): recurse(ch)
    recurse(fn_cursor)
    return list(dict.fromkeys(atoms))  # unique


def solve_mcdc(struct_cursor, atoms):
    """For each atom, solve for a test vector toggling that atom"""
    # Build Z3 variables for struct fields
    fields = {}
    for f in struct_cursor.get_children():
        if f.kind == CursorKind.FIELD_DECL:
            name = f.spelling
            # treat all numeric/enum as Int
            fields[name] = Int(name)

    baseline = {name: 0 for name in fields}
    tests = []
    for atom in atoms:
        s = Solver()
        # force one atom true, others baseline
        # This is placeholder: assume atom corresponds to a single field
        if atom in fields:
            s.add(fields[atom] == 1)
            for n, val in baseline.items():
                if n != atom:
                    s.add(fields[n] == val)
            if s.check().sat:
                m = s.model()
                vec = {n: m[fields[n]].as_long() for n in fields}
                tests.append((atom, vec))
    return tests


def write_test_file(fn_cursor, struct_name, cases, out_dir):
    """Generate GoogleTest .cpp file for one function"""
    fname = f"{fn_cursor.spelling}_mcdc_test.cpp"
    path = os.path.join(out_dir, fname)
    with open(path, 'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write(f'#include "{fn_cursor.spelling}.h"\n\n')
        for idx, (atom, vec) in enumerate(cases, 1):
            f.write(f'TEST({fn_cursor.spelling}_MC_DC, Case{idx}) ' + '{\n')
            f.write(f'    {struct_name} in = '+'{')
            f.write(', '.join(f'.{k}={v}' for k, v in vec.items()))
            f.write('};\n')
            f.write(f'    EXPECT_NO_FATAL_FAILURE({fn_cursor.spelling}(&in));\n')
            f.write('}\n\n')
    print(f"Generated {path}")


def main():
    if len(sys.argv) != 4:
        print("Usage: python generate_mcdc_tests.py <src_dir> <include_dir> <test_dir>")
        return
    src_dir, inc_dir, tst_dir = sys.argv[1:]
    os.makedirs(tst_dir, exist_ok=True)

    types = parse_headers(inc_dir)
    funcs = parse_functions(src_dir, inc_dir)

    for fn in funcs:
        args = list(fn.get_arguments())
        if not args:
            continue
        # assume first argument is a pointer to struct
        struct_type = args[0].type.spelling.replace('*', '').strip()
        struct_cursor = types.get(struct_type)
        if not struct_cursor:
            print(f"Struct {struct_type} not found for {fn.spelling}")
            continue
        atoms = gather_conditions(fn)
        cases = solve_mcdc(struct_cursor, atoms)
        if cases:
            write_test_file(fn, struct_type, cases, tst_dir)
        else:
            print(f"No MC/DC cases found for {fn.spelling}")

if __name__ == '__main__':
    main()
