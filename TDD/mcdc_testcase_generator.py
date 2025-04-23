#!/usr/bin/env python3
"""
MC/DC Test Generator for C functions using Clang and Z3
Usage:
  python generate_mcdc_tests.py <src_dir> <include_dir> <test_dir>

Before running, ensure libclang shared library is locatable.
You can set the environment variable LIBCLANG_PATH to the full path of your libclang.dll (Windows) or libclang.so (Linux) or libclang.dylib (macOS).
"""
import os
import sys
import z3
from clang.cindex import Config, Index, CursorKind

# Attempt to load libclang from environment if provided
libclang_path = os.getenv("LIBCLANG_PATH")
if libclang_path and os.path.exists(libclang_path):
    Config.set_library_file(libclang_path)
else:
    # Try common LLVM install locations on Windows
    possible_paths = [
        "C:\Program Files\LLVM\bin\libclang.dll",
        "C:\Program Files (x86)\LLVM\bin\libclang.dll",
    ]
    found = False
    for p in possible_paths:
        if os.path.exists(p):
            Config.set_library_file(p)
            found = True
            break
    if not found:
        sys.stderr.write(
            "Error: libclang.dll not found.
"
            "Install LLVM or set LIBCLANG_PATH to the full path of libclang.dll.
"
        )
        sys.exit(1)


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


def extract_atoms(expr_cursor):
    """Placeholder: return atomic sub-expressions as strings"""
    # TODO: implement AST-based splitting for &&, ||, ?:, comparisons, etc.
    text = expr_cursor.spelling or expr_cursor.displayname or ''
    return [text] if text else []


def gather_conditions(fn_cursor):
    """Walk AST to collect all atomic conditions in a function"""
    atoms = []
    def recurse(node):
        if node.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT, CursorKind.CONDITIONAL_OPERATOR):
            cond = next(node.get_children(), None)
            if cond:
                atoms.extend(extract_atoms(cond))
        for ch in node.get_children():
            recurse(ch)
    recurse(fn_cursor)
    # unique
    seen = set()
    unique_atoms = []
    for a in atoms:
        if a not in seen:
            seen.add(a)
            unique_atoms.append(a)
    return unique_atoms


def solve_mcdc(struct_cursor, atoms):
    """For each atom, solve for a test vector toggling that atom"""
    fields = {}
    for f in struct_cursor.get_children():
        if f.kind.name == 'FIELD_DECL':
            name = f.spelling
            fields[name] = z3.Int(name)

    baseline = {name: 0 for name in fields}
    tests = []
    for atom in atoms:
        s = z3.Solver()
        if atom in fields:
            s.add(fields[atom] == 1)
            for n, val in baseline.items():
                if n != atom:
                    s.add(fields[n] == val)
            if s.check() == z3.sat:
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
        for idx, (atom, vec) in enumerate(cases, start=1):
            f.write(f'TEST({fn_cursor.spelling}_MC_DC, Case{idx}) ' + '{\n')
            f.write(f'    {struct_name} in = '+'{')
            f.write(', '.join(f'.{k} = {v}' for k, v in vec.items()))
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
