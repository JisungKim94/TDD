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
    def visit(n):
        logging.debug(f"Visiting node: {n.kind}, spelling={n.spelling}")
        if n.kind == CursorKind.MEMBER_REF_EXPR:
            field = n.spelling
            base = None
            # first child of MEMBER_REF_EXPR is DECL_REF_EXPR for base
            for ch in n.get_children():
                if ch.kind == CursorKind.DECL_REF_EXPR:
                    base = ch.spelling
                    break
            if base in fields_map and field in fields_map[base]:
                key = f"{base}.{field}"
                atoms.append((key, field))
                logging.debug(f"Matched atom: {key}")
        # fallback direct field name usage
        elif n.kind == CursorKind.DECL_REF_EXPR:
            name = n.spelling
            for base, fields in fields_map.items():
                if name in fields:
                    key = f"{base}.{name}"
                    if (key, name) not in atoms:
                        atoms.append((key, name))
                        logging.debug(f"Matched atom via DECL_REF: {key}")
        for ch in n.get_children():
            visit(ch)
    visit(node)
    return atoms


def gather_conditions(fn_cursor, fields_map):
    atoms = []
    def recurse(n):
        if n.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT):
            cond = next(n.get_children(), None)
            if cond and cond.kind == CursorKind.PAREN_EXPR:
                cond = next(cond.get_children(), None)
            if cond:
                logging.debug(f"Condition expr: {cond.kind}")
                atoms.extend(gather_atoms_and_fields(cond, fields_map))
        elif n.kind == CursorKind.DECL_STMT:
            for var in n.get_children():
                if var.kind == CursorKind.VAR_DECL:
                    for init in var.get_children():
                        if init.kind in (CursorKind.UNEXPOSED_EXPR,
                                         CursorKind.BINARY_OPERATOR,
                                         CursorKind.CONDITIONAL_OPERATOR):
                            logging.debug(f"Init expr: {init.kind}")
                            atoms.extend(gather_atoms_and_fields(init, fields_map))
        for ch in n.get_children():
            recurse(ch)
    recurse(fn_cursor)
    # dedupe
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
        for val in (0, 1):
            s = z3.Solver()
            s.add(z3vars[key] == val)
            for other in z3vars:
                if other != key:
                    s.add(z3vars[other] == 1)
            if s.check() == z3.sat:
                m = s.model()
                vec = {k: m[z3vars[k]].as_long() for k in z3vars}
                tests.append((key, vec))
                logging.debug(f"Test vec for {key}: {vec}")
                break
    return tests


def write_test_file(fn, cases, fields_map, out_dir):
    params = list(fn.get_arguments())
    names = [p.spelling for p in params]
    orig_types = [p.type.spelling.strip() for p in params]
    types_ = [t.replace('*','').strip() for t in orig_types]
    is_ptr = ['*' in t for t in orig_types]
    path = os.path.join(out_dir, f"testMCDC_{fn.spelling}.cpp")
    with open(path, 'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write('#include "mycode.h"\n\n')
        for i, (key, vec) in enumerate(cases, 1):
            f.write(f'TEST({fn.spelling}_MC_DC, Case{i}) {{\n')
            for name, tp in zip(names, types_):
                f.write(f'  {tp} {name} = {{0}};\n')
            for k, v in vec.items():
                base, field = k.split('.', 1)
                f.write(f'  {base}.{field} = {v};\n')
            args_call = []
            for name, ptr in zip(names, is_ptr):
                args_call.append(f'&{name}' if ptr else name)
            f.write(f'  EXPECT_NO_FATAL_FAILURE({fn.spelling}({', '.join(args_call)})); // {key}\n')
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
        params = list(fn.get_arguments())
        fields_map = {}
        for p in params:
            nm = p.spelling
            tp = p.type.spelling.replace('*','').strip()
            if tp in types:
                fields_map[nm] = types[tp]
        if not fields_map:
            logging.warning(f"No struct parameters for {fn.spelling}")
            continue
        atoms = gather_conditions(fn, fields_map)
        if not atoms:
            logging.warning(f"No condition atoms for {fn.spelling}")
            continue
        cases = solve_mcdc(atoms)
        filtered = [(k,v) for k,v in cases if k.split('.',1)[0] in fields_map]
        if filtered:
            write_test_file(fn, filtered, fields_map, tst)
        else:
            logging.warning(f"No MC/DC cases for {fn.spelling}")

if __name__ == '__main__':
    main()
