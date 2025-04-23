#!/usr/bin/env python3
"""
MC/DC Test Generator for C functions using Clang and Z3
 Falls back to skeleton tests if no MC/DC atoms found.
Usage:
  python generate_mcdc_tests.py <src_dir> <include_dir> <test_dir>
"""
import os
import sys
import logging
import z3
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
    if path and os.path.exists(path):
        try:
            Config.set_library_file(path)
            return
        except LibclangError:
            pass
    for candidate in [
        r"C:\\Program Files\\LLVM\\bin\\libclang.dll",
        r"C:\\Program Files (x86)\\LLVM\\bin\\libclang.dll",
    ]:
        if os.path.exists(candidate):
            try:
                Config.set_library_file(candidate)
                return
            except LibclangError:
                continue
    logging.fatal("libclang.dll not found.")
    sys.exit(1)

def normalize_path(p):
    return os.path.abspath(p)

def parse_headers(include_dir):
    index = Index.create()
    types = {}
    for root, _, files in os.walk(include_dir):
        for fname in files:
            if fname.endswith('.h'):
                tu = index.parse(os.path.join(root,fname), args=[f'-I{include_dir}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.STRUCT_DECL and c.spelling:
                        types[c.spelling] = {f.spelling for f in c.get_children() if f.kind.name=='FIELD_DECL'}
    return types

def parse_functions(src_dir, include_dir):
    index = Index.create()
    funcs = []
    for root,_,files in os.walk(src_dir):
        for fname in files:
            if fname.endswith('.c'):
                tu = index.parse(os.path.join(root,fname), args=[f'-I{include_dir}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.FUNCTION_DECL and c.is_definition():
                        funcs.append(c)
    return funcs

def write_skeleton(fn, fields_map, out_dir):
    logging.debug(f"Generating skeleton test for function: {fn.spelling}")
    path = os.path.join(out_dir, f"testMCDC_{fn.spelling}_skeleton.cpp")
    with open(path,'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write('#include "mycode.h"\n\n')
        f.write(f'// Skeleton MC/DC GoogleTest for {fn.spelling}\n')
        f.write(f'TEST(MCDC_{fn.spelling}, Skeleton) {{\n')
        # Declare inputs
        for p in fn.get_arguments():
            tp = p.type.spelling.replace('*','').strip()
            nm = p.spelling
            f.write(f'  {tp} {nm} = {{0}};\n')
        f.write('  // TODO: initialize fields appropriately\n')
        # Call
        args = ', '.join(f'&{p.spelling}' if '*' in p.type.spelling else p.spelling for p in fn.get_arguments())
        f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}({args}));\n')
        f.write('}\n')
    logging.info(f"Generated skeleton: {path}")

def write_test_file(fn, cases, fields_map, out_dir):
    logging.debug(f"Generating MC/DC tests for function: {fn.spelling} with {len(cases)} cases")
    path = os.path.join(out_dir, f"testMCDC_{fn.spelling}.cpp")
    with open(path,'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write('#include "mycode.h"\n\n')
        names = [p.spelling for p in fn.get_arguments()]
        is_ptr = ['*' in p.type.spelling for p in fn.get_arguments()]
        for i,(atom,vec) in enumerate(cases,1):
            f.write(f'TEST({fn.spelling}_MC_DC, Case{i}) {{\n')
            # init
            for p in fn.get_arguments():
                tp = p.type.spelling.replace('*','').strip()
                nm = p.spelling
                f.write(f'  {tp} {nm} = {{0}};\n')
            # assign
            for k,v in vec.items(): base,field=k.split('.',1); f.write(f'  {base}.{field} = {v};\n')
            # call
            args=', '.join(f'&{n}' if ptr else n for n,ptr in zip(names,is_ptr))
            f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}({args})); // {atom}\n')
            f.write('}\n\n')
    logging.info(f"Generated: {path}")

def solve_mcdc(atoms):
    logging.debug(f"Solving MC/DC for atoms: {[a for a,_ in atoms]}")
    tests=[]
    vars={k:z3.Int(k.replace('.','_')) for k,_ in atoms}
    for k,_ in atoms:
        for val in (0,1):
            s=z3.Solver(); s.add(vars[k]==val)
            for o in vars:
                if o!=k: s.add(vars[o]==1)
            if s.check()==z3.sat:
                m=s.model(); tests.append((k,{v:m[vars[v]].as_long() for v in vars})); break
    return tests

def gather_atoms_and_fields(node, fmap):
    atoms=[]; local={}
    def expr_atoms(n,store):
        if n.kind==CursorKind.MEMBER_REF_EXPR:
            fld=n.spelling; bs=None
            for c in n.get_children():
                if c.kind==CursorKind.DECL_REF_EXPR: bs=c.spelling; break
            if bs in fmap and fld in fmap[bs]: store.append((f"{bs}.{fld}",fld))
        elif n.kind==CursorKind.DECL_REF_EXPR:
            nm=n.spelling
            for b,fl in fmap.items():
                if nm in fl: store.append((f"{b}.{nm}",nm))
        for c in n.get_children(): expr_atoms(c,store)
    def scan_locals(n):
        if n.kind==CursorKind.DECL_STMT:
            for v in n.get_children():
                if v.kind==CursorKind.VAR_DECL:
                    sa=[]; expr_atoms(v,sa)
                    if sa: local[v.spelling]=sa
        for c in n.get_children(): scan_locals(c)
    def visit(n):
        expr_atoms(n,atoms)
        if n.kind==CursorKind.DECL_REF_EXPR and n.spelling in local: atoms.extend(local[n.spelling])
        for c in n.get_children(): visit(c)
    scan_locals(node); visit(node)
    # dedupe
    u=[]
    for a in atoms:
        if a not in u: u.append(a)
    return u

def gather_conditions(fn, fmap):
    at=[]
    def go(n):
        if n.kind in (CursorKind.IF_STMT,CursorKind.WHILE_STMT,CursorKind.DECL_STMT):
            for c in n.get_children(): at.extend(gather_atoms_and_fields(c,fmap))
        for c in n.get_children(): go(c)
    go(fn); return list(dict.fromkeys(at))

def has_conditions(fn_cursor):
    """Return True if function contains any conditional statements."""
    found = False
    def recurse(n):
        nonlocal found
        if n.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT, CursorKind.CONDITIONAL_OPERATOR):
            found = True
            return
        for c in n.get_children():
            if not found:
                recurse(c)
    recurse(fn_cursor)
    return found


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
    logging.debug(f"Parsed headers: {list(types.keys())}")
    funcs = parse_functions(src, inc)
    logging.debug(f"Parsed functions: {[f.spelling for f in funcs]}")
    logging.debug(f"Parsed {len(funcs)} functions.")

    for fn in funcs:
        # Determine if function has any conditional statements
        if has_conditions(fn):
            # Always generate skeleton for functions with conditionals
            write_skeleton(fn, {}, tst)
        # Build map of parameter names to struct fields
        params = list(fn.get_arguments())
        fields_map = {}
        for p in params:
            nm = p.spelling
            tp = p.type.spelling.replace('*','').strip()
            if tp in types:
                fields_map[nm] = types[tp]
        if not fields_map:
            continue
        atoms = gather_conditions(fn, fields_map)
        if not atoms:
            continue
        cases = solve_mcdc(atoms)
        # Filter cases by valid parameter base
        filtered = [(k,v) for k,v in cases if k.split('.',1)[0] in fields_map]
        if filtered:
            write_test_file(fn, filtered, fields_map, tst)

if __name__ == '__main__':
    main()
