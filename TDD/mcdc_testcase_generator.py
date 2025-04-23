#!/usr/bin/env python3
"""
MC/DC Test Generator for C functions using Clang and Z3
Usage:
  python generate_mcdc_tests.py <src_dir> <include_dir> <test_dir>

Before running, ensure libclang shared library is locatable and version-compatible with clang.cindex.
Paths provided (absolute or relative) will be normalized.
"""
import os
import sys
import z3
from clang.cindex import Config, Index, CursorKind, LibclangError

# Load libclang with version-check
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
            sys.stderr.write(f"Error loading libclang from {libclang_path}: {e}\n")
    if not loaded:
        possible = [
            r"C:\Program Files\LLVM\bin\libclang.dll",
            r"C:\Program Files (x86)\LLVM\bin\libclang.dll",
        ]
        for p in possible:
            print(f"[DEBUG] Checking {p}")
            if os.path.exists(p):
                try:
                    Config.set_library_file(p)
                    loaded = True
                    print(f"[DEBUG] Loaded libclang from: {p}")
                    break
                except LibclangError as e:
                    sys.stderr.write(f"Error loading libclang from {p}: {e}\n")
    if not loaded:
        sys.stderr.write(
            "Fatal: libclang.dll not found or incompatible.\n"
            "Please install LLVM >=10 (https://llvm.org) or set LIBCLANG_PATH.\n"
        )
        sys.exit(1)

# Normalize path to absolute

def normalize_path(path):
    abs_path = os.path.abspath(path)
    print(f"[DEBUG] Normalized path: {path} -> {abs_path}")
    return abs_path


def parse_headers(include_path):
    index = Index.create()
    types = {}
    for root, _, files in os.walk(include_path):
        for fname in files:
            if fname.endswith('.h'):
                tu = index.parse(os.path.join(root, fname), args=[f'-I{include_path}'])
                for c in tu.cursor.get_children():
                    if c.kind in (CursorKind.STRUCT_DECL, CursorKind.ENUM_DECL, CursorKind.TYPEDEF_DECL) and c.spelling:
                        types[c.spelling] = c
    return types


def parse_functions(src_path, include_path):
    index = Index.create()
    funcs = []
    for root, _, files in os.walk(src_path):
        for fname in files:
            if fname.endswith('.c'):
                tu = index.parse(os.path.join(root, fname), args=[f'-I{include_path}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.FUNCTION_DECL and c.is_definition():
                        funcs.append(c)
    return funcs


def extract_atoms(expr):
    text = expr.spelling or expr.displayname or ''
    return [text] if text else []


def gather_conditions(fn_cursor):
    atoms = []
    def recurse(node):
        if node.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT, CursorKind.CONDITIONAL_OPERATOR):
            cond = next(node.get_children(), None)
            if cond:
                atoms.extend(extract_atoms(cond))
        for ch in node.get_children(): recurse(ch)
    recurse(fn_cursor)
    seen = set(); unique = []
    for a in atoms:
        if a not in seen:
            seen.add(a); unique.append(a)
    return unique


def solve_mcdc(struct_cursor, atoms):
    fields = {f.spelling: z3.Int(f.spelling)
              for f in struct_cursor.get_children() if f.kind.name=='FIELD_DECL'}
    baseline = {n: 0 for n in fields}
    tests = []
    for atom in atoms:
        if atom not in fields: continue
        s = z3.Solver()
        s.add(fields[atom] == 1)
        for n,v in baseline.items():
            if n!=atom: s.add(fields[n]==v)
        if s.check()==z3.sat:
            m = s.model()
            tests.append((atom, {n:m[fields[n]].as_long() for n in fields}))
    return tests


def write_test_file(fn, struct_name, cases, out_dir):
    path = os.path.join(out_dir, f"{fn.spelling}_mcdc_test.cpp")
    with open(path,'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write(f'#include "{fn.spelling}.h"\n\n')
        for i,(atom,vec) in enumerate(cases,1):
            f.write(f'TEST({fn.spelling}_MC_DC, Case{i}) '+'{\n')
            f.write(f'  {struct_name} in '+'{ '+', '.join(f'.{k}={v}' for k,v in vec.items())+' };\n')
            f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}(&in));\n')
            f.write('}\n\n')
    print(f"Generated: {path}")


def main():
    if len(sys.argv)!=4:
        print("Usage: python generate_mcdc_tests.py <src_dir> <include_dir> <test_dir>")
        sys.exit(1)
    # Normalize provided paths
    src = normalize_path(sys.argv[1])
    inc = normalize_path(sys.argv[2])
    tst = normalize_path(sys.argv[3])
    os.makedirs(tst,exist_ok=True)
    # Ensure libclang is loaded
    load_libclang()
    types = parse_headers(inc)
    funcs = parse_functions(src,inc)
    for fn in funcs:
        args=list(fn.get_arguments())
        if not args: continue
        st = args[0].type.spelling.replace('*','').strip()
        sc = types.get(st)
        if not sc:
            print(f"Struct {st} not found for {fn.spelling}")
            continue
        atoms = gather_conditions(fn)
        cases = solve_mcdc(sc, atoms)
        if cases:
            write_test_file(fn, st, cases, tst)
        else:
            print(f"No MC/DC cases for {fn.spelling}")

if __name__=='__main__': main()
