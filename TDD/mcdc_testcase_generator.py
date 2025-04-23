#!/usr/bin/env python3
"""
MC/DC Test Generator for C functions using Clang and Z3
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

def normalize_path(path):
    abspath = os.path.abspath(path)
    logging.debug(f"Normalized path: {path} -> {abspath}")
    return abspath

def parse_headers(include_dir):
    logging.debug(f"Parsing headers in {include_dir}")
    index = Index.create()
    types = {}
    for root, _, files in os.walk(include_dir):
        for fname in files:
            if fname.endswith('.h'):
                full = os.path.join(root, fname)
                logging.debug(f"Parsing header: {full}")
                tu = index.parse(full, args=[f'-I{include_dir}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.STRUCT_DECL and c.spelling:
                        fields = {f.spelling for f in c.get_children() if f.kind.name == 'FIELD_DECL'}
                        logging.debug(f"Struct {c.spelling} fields: {fields}")
                        types[c.spelling] = fields
    return types

def parse_functions(src_dir, include_dir):
    logging.debug(f"Parsing sources in {src_dir}")
    index = Index.create()
    funcs = []
    for root, _, files in os.walk(src_dir):
        for fname in files:
            if fname.endswith('.c'):
                full = os.path.join(root, fname)
                logging.debug(f"Parsing source: {full}")
                tu = index.parse(full, args=[f'-I{include_dir}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.FUNCTION_DECL and c.is_definition():
                        logging.debug(f"Found function: {c.spelling}")
                        funcs.append(c)
    return funcs

def gather_atoms_and_fields(node, fields_map):
    atoms = []
    local_map = {}
    # Scan local variable initializers
    def scan_locals(n):
        if n.kind == CursorKind.DECL_STMT:
            for var in n.get_children():
                if var.kind == CursorKind.VAR_DECL:
                    name = var.spelling
                    sub_atoms = []
                    for init in var.get_children():
                        collect_atoms(init, fields_map, sub_atoms)
                    if sub_atoms:
                        local_map[name] = sub_atoms
        for c in n.get_children():
            scan_locals(c)
    def collect_atoms(n, fmap, store):
        if n.kind == CursorKind.MEMBER_REF_EXPR:
            field = n.spelling
            base = None
            for ch in n.get_children():
                if ch.kind == CursorKind.DECL_REF_EXPR:
                    base = ch.spelling
                    break
            if base in fmap and field in fmap[base]:
                store.append((f"{base}.{field}", field))
        elif n.kind == CursorKind.DECL_REF_EXPR:
            name = n.spelling
            for base, fields in fmap.items():
                if name in fields:
                    store.append((f"{base}.{name}", name))
        for c in n.get_children():
            collect_atoms(c, fmap, store)
    scan_locals(node)
    # Visit all nodes and propagate
    def visit(n):
        if n.kind in (CursorKind.MEMBER_REF_EXPR, CursorKind.DECL_REF_EXPR):
            collect_atoms(n, fields_map, atoms)
            if n.kind == CursorKind.DECL_REF_EXPR:
                nm = n.spelling
                if nm in local_map:
                    atoms.extend(local_map[nm])
        for c in n.get_children():
            visit(c)
    visit(node)
    # Deduplicate
    uniq = []
    for a in atoms:
        if a not in uniq:
            uniq.append(a)
    return uniq

def gather_conditions(fn_cursor, fields_map):
    atoms = []
    def recurse(n):
        if n.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT):
            cond = next(n.get_children(), None)
            if cond and cond.kind == CursorKind.PAREN_EXPR:
                cond = next(cond.get_children(), None)
            if cond:
                atoms.extend(gather_atoms_and_fields(cond, fields_map))
        elif n.kind == CursorKind.DECL_STMT:
            atoms.extend(gather_atoms_and_fields(n, fields_map))
        for c in n.get_children():
            recurse(c)
    recurse(fn_cursor)
    uniq = []
    for a in atoms:
        if a not in uniq:
            uniq.append(a)
    logging.debug(f"Atoms for {fn_cursor.spelling}: {uniq}")
    return uniq

def solve_mcdc(atoms):
    tests = []
    z3vars = {key: z3.Int(key.replace('.', '_')) for key, _ in atoms}
    for key, _ in atoms:
        for val in (0,1):
            s = z3.Solver()
            s.add(z3vars[key] == val)
            for other in z3vars:
                if other != key:
                    s.add(z3vars[other] == 1)
            if s.check() == z3.sat:
                m = s.model()
                vec = {k: m[z3vars[k]].as_long() for k in z3vars}
                tests.append((key, vec))
                break
    return tests

def write_test_file(fn, cases, fields_map, out_dir):
    params = list(fn.get_arguments())
    names = [p.spelling for p in params]
    orig_types = [p.type.spelling.strip() for p in params]
    base_types = [t.replace('*','').strip() for t in orig_types]
    is_ptr = ['*' in t for t in orig_types]
    path = os.path.join(out_dir, f"testMCDC_{fn.spelling}.cpp")
    with open(path, 'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write('#include "mycode.h"\n\n')
        for i, (atom, vec) in enumerate(cases,1):
            f.write(f'TEST({fn.spelling}_MC_DC, Case{i}) {{\n')
            for nm, tp in zip(names, base_types):
                f.write(f'  {tp} {nm} = {{0}};\n')
            for key, v in vec.items():
                base, field = key.split('.',1)
                f.write(f'  {base}.{field} = {v};\n')
            args = []
            for nm, ptr in zip(names, is_ptr):
                args.append(f'&{nm}' if ptr else nm)
            f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}({', '.join(args)})); // {atom}\n')
            f.write('}\n\n')
    logging.info(f"Generated: {path}")

def main():
    if len(sys.argv)!=4:
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
        fields_map = {}
        for p in fn.get_arguments():
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
        filtered = [(k,v) for k,v in cases if k.split('.',1)[0] in fields_map]
        if filtered:
            write_test_file(fn, filtered, fields_map, tst)

if __name__=='__main__':
    main()
