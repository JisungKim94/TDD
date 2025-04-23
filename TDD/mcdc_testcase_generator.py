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

# Log debug info to file\log_file = "mcdc_debug_log.txt"
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
        for f in files:
            if f.endswith('.h'):
                full = os.path.join(root, f)
                logging.debug(f"Parsing {full}")
                tu = index.parse(full, args=[f'-I{inc_dir}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.STRUCT_DECL and c.spelling:
                        fields = [fld.spelling for fld in c.get_children() if fld.kind.name=='FIELD_DECL']
                        logging.debug(f"Struct {c.spelling} fields: {fields}")
                        types[c.spelling] = c
    return types

def parse_functions(src_dir, inc_dir):
    logging.debug(f"Parsing sources in {src_dir}")
    index = Index.create()
    funcs = []
    for root, _, files in os.walk(src_dir):
        for f in files:
            if f.endswith('.c'):
                full = os.path.join(root, f)
                logging.debug(f"Parsing {full}")
                tu = index.parse(full, args=[f'-I{inc_dir}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.FUNCTION_DECL and c.is_definition():
                        logging.debug(f"Found function: {c.spelling}")
                        funcs.append(c)
    return funcs

def gather_atoms_and_fields(cond, struct_fields):
    atoms = []
    def visit(node):
        if node.kind == CursorKind.MEMBER_REF_EXPR:
            grand = node.semantic_parent.semantic_parent
            if grand.kind == CursorKind.DECL_REF_EXPR:
                base = grand.spelling
                field = node.spelling
                if base in ('globalRoles','u8_Orders') and field in struct_fields:
                    key = f"{base}.{field}"
                    atoms.append((key, key))
                    logging.debug(f"Atom detected: {key}")
        for ch in node.get_children():
            visit(ch)
    visit(cond)
    return atoms

def gather_conditions(fn, struct_fields):
    atoms = []
    def recurse(n):
        if n.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT, CursorKind.CONDITIONAL_OPERATOR):
            cond = next(n.get_children(), None)
            if cond:
                atoms.extend(gather_atoms_and_fields(cond, struct_fields))
        for ch in n.get_children(): recurse(ch)
    recurse(fn)
    uniq = []
    for a in atoms:
        if a not in uniq: uniq.append(a)
    logging.debug(f"Atoms for {fn.spelling}: {uniq}")
    return uniq

def solve_mcdc(_, atoms):
    fields = {a.split('.',1)[1] for a,_ in atoms}
    logging.debug(f"Solving MC/DC for fields: {fields}")
    z3vars = {f: z3.Int(f) for f in fields}
    tests = []
    for atom,_ in atoms:
        fld = atom.split('.',1)[1]
        for val in (0,1):
            s = z3.Solver()
            for f in fields:
                s.add(z3vars[f] == (val if f==fld else 1))
            if s.check()==z3.sat:
                m = s.model()
                vec = {f:m[z3vars[f]].as_long() for f in fields}
                tests.append((atom,vec))
                logging.debug(f"Test vec for {atom}: {vec}")
                break
    return tests

def write_test_file(fn, cases, out_dir):
    args = list(fn.get_arguments())
    name0 = args[0].spelling; type0=args[0].type.spelling.replace('*','').strip()
    name1= None; type1=None
    if len(args)>1:
        name1=args[1].spelling; type1=args[1].type.spelling.replace('*','').strip()
    path=os.path.join(out_dir,f"testMCDC_{fn.spelling}.cpp")
    with open(path,'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write('#include "mycode.h"\n\n')
        for i,(lbl, vec) in enumerate(cases,1):
            f.write(f'TEST({fn.spelling}_MC_DC, Case{i}) {{\n')
            f.write(f'  {type0} {name0} = {{0}};\n')
            if name1: f.write(f'  {type1} {name1} = {{0}};\n')
            for atom, _ in cases:
                pass
            for k,v in vec.items():
                f.write(f'  {name1}.{k} = {v};\n') if name1 and k in vec else f.write(f'  {name0}.{k} = {v};\n')
            if name1:
                f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}(&{name0}, &{name1})); // {lbl}\n')
            else:
                f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}(&{name0})); // {lbl}\n')
            f.write('}\n\n')
    logging.info(f"Generated: {path}")

def main():
    if len(sys.argv)!=4: 
        print("Usage:...") 
        return
    src,inc,tst=normalize_path(sys.argv[1]),normalize_path(sys.argv[2]),normalize_path(sys.argv[3])
    os.makedirs(tst,exist_ok=True)
    load_libclang(); types=parse_headers(inc)
    for fn in parse_functions(src,inc):
        t0=fn.get_arguments()[0].type.spelling.replace('*','').strip();
        c=types.get(t0)
        if not c: continue
        fields={f.spelling for f in c.get_children() if f.kind.name=='FIELD_DECL'}
        atoms=gather_conditions(fn,fields)
        cases=solve_mcdc(fields,atoms)
        if cases: write_test_file(fn,cases,tst)
        else: logging.warning(f"No cases for {fn.spelling}")

if __name__=='__main__': main()
