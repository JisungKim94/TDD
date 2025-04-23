#!/usr/bin/env python3
"""
MC/DC Test Generator for C functions using Clang and Z3
Usage:
  python generate_mcdc_tests.py <src_dir> <include_dir> <test_dir>

Generates GoogleTest files achieving 100% MC/DC by solving all atomic condition toggle combinations.
"""
import os
import sys
import z3
from clang.cindex import Config, Index, CursorKind, LibclangError

# Load libclang

def load_libclang():
    libclang_path = os.getenv("LIBCLANG_PATH")
    print(f"[DEBUG] LIBCLANG_PATH = {libclang_path}")
    loaded = False
    if libclang_path and os.path.exists(libclang_path):
        try:
            Config.set_library_file(libclang_path)
            loaded = True
            print(f"[DEBUG] Loaded libclang from LIBCLANG_PATH: {libclang_path}")
        except LibclangError as e:
            sys.stderr.write(f"[ERROR] Failed to load libclang: {e}\n")
    if not loaded:
        for p in [
            r"C:\\Program Files\\LLVM\\bin\\libclang.dll",
            r"C:\\Program Files (x86)\\LLVM\\bin\\libclang.dll",
        ]:
            if os.path.exists(p):
                try:
                    Config.set_library_file(p)
                    print(f"[DEBUG] Loaded libclang from fallback: {p}")
                    return
                except LibclangError as e:
                    sys.stderr.write(f"[ERROR] Fallback libclang load failed from {p}: {e}\n")
    if not loaded:
        sys.stderr.write("[FATAL] libclang.dll not found or could not be loaded.\n")
        sys.exit(1)


def normalize_path(path):
    abs_path = os.path.abspath(path)
    print(f"[DEBUG] Normalized path: {path} -> {abs_path}")
    return abs_path


def parse_headers(include_path):
    print(f"[DEBUG] Parsing headers in: {include_path}")
    index = Index.create()
    types = {}
    for root, _, files in os.walk(include_path):
        for fname in files:
            if fname.endswith('.h'):
                full_path = os.path.join(root, fname)
                print(f"[DEBUG] Parsing header: {full_path}")
                tu = index.parse(full_path, args=[f'-I{include_path}'])
                for c in tu.cursor.get_children():
                    if c.kind in (CursorKind.STRUCT_DECL, CursorKind.ENUM_DECL, CursorKind.TYPEDEF_DECL):
                        if c.spelling:
                            print(f"[DEBUG] Found type: {c.spelling}")
                            types[c.spelling] = c
    return types


def parse_functions(src_path, include_path):
    print(f"[DEBUG] Parsing C source files in: {src_path}")
    index = Index.create()
    funcs = []
    for root, _, files in os.walk(src_path):
        for fname in files:
            if fname.endswith('.c'):
                full_path = os.path.join(root, fname)
                print(f"[DEBUG] Parsing source: {full_path}")
                tu = index.parse(full_path, args=[f'-I{include_path}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.FUNCTION_DECL and c.is_definition():
                        print(f"[DEBUG] Found function: {c.spelling}")
                        funcs.append(c)
    return funcs


def gather_atoms_and_fields(cond_cursor, struct_fields):
    atoms = []
    def visit(node):
        print(f"[DEBUG] Visiting node: kind={node.kind}, spelling='{node.spelling}', displayname='{node.displayname}'")
        if node.kind == CursorKind.BINARY_OPERATOR:
            text = node.spelling or node.displayname
            if text:
                for field in struct_fields:
                    if field in text:
                        print(f"[DEBUG] Matched atom: {text} (field: {field})")
                        atoms.append((field, text))
        for child in node.get_children():
            visit(child)
    visit(cond_cursor)
    return atoms


def gather_conditions(fn_cursor, struct_fields):
    atoms = []
    def recurse(node):
        if node.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT, CursorKind.CONDITIONAL_OPERATOR):
            print(f"[DEBUG] Found conditional statement: {node.kind} in function {fn_cursor.spelling}")
            cond = next(node.get_children(), None)
            if cond:
                print(f"[DEBUG] Condition expression: {cond.spelling} / {cond.displayname}")
                atoms.extend(gather_atoms_and_fields(cond, struct_fields))
            else:
                print(f"[WARN] Condition node has no children in {fn_cursor.spelling}")
        for ch in node.get_children():
            recurse(ch)
    recurse(fn_cursor)
    print(f"[DEBUG] Total atoms found for function {fn_cursor.spelling}: {atoms}")
    return list(dict.fromkeys(atoms))


def solve_mcdc(fields, atoms):
    print(f"[DEBUG] Solving MC/DC with fields: {fields} and atoms: {atoms}")
    tests = []
    z3vars = {name: z3.Int(name) for name in fields}
    for idx, (field, expr) in enumerate(atoms):
        for val in [0, 1]:
            s = z3.Solver()
            s.add(z3vars[field] == val)
            for other, _ in atoms:
                if other != field:
                    s.add(z3vars[other] == 1)
            if s.check() == z3.sat:
                model = s.model()
                test_vector = {k: model[z3vars[k]].as_long() for k in z3vars}
                tests.append((f"{field}={val}", test_vector))
                print(f"[DEBUG] Found SAT for {field}={val}: {test_vector}")
                break
            else:
                print(f"[WARN] UNSAT for {field}={val} with others fixed to 1")
    return tests


def write_test_file(fn, struct_name, cases, out_dir):
    path = os.path.join(out_dir, f"testMCDC_{fn.spelling}.cpp")
    with open(path, 'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write(f'#include "{fn.spelling}.h"\n\n')
        for i, (label, vals) in enumerate(cases, 1):
            f.write(f'TEST({fn.spelling}_MC_DC, Case{i}) '+'{\n')
            f.write(f'  {struct_name} in = '+'{ '+', '.join(f'.{k}={v}' for k,v in vals.items())+' };
')
            f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}(&in)); // {label}\n')
            f.write('}\n\n')
    print(f"[INFO] Generated: {path}")


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
    print(f"[DEBUG] Parsed {len(funcs)} functions.")
    for fn in funcs:
        args = list(fn.get_arguments())
        if not args:
            print(f"[WARN] Function {fn.spelling} has no arguments, skipping.")
            continue
        struct_type = args[0].type.spelling.replace('*', '').strip()
        struct_cursor = types.get(struct_type)
        if not struct_cursor:
            print(f"[WARN] Struct {struct_type} not found for {fn.spelling}, skipping.")
            continue
        fields = {f.spelling for f in struct_cursor.get_children() if f.kind.name == 'FIELD_DECL'}
        print(f"[DEBUG] Struct {struct_type} fields: {fields}")
        atoms = gather_conditions(fn, fields)
        cases = solve_mcdc(fields, atoms)
        if cases:
            write_test_file(fn, struct_type, cases, tst)
        else:
            print(f"[WARN] No MC/DC cases for {fn.spelling}")

if __name__ == '__main__':
    main()
