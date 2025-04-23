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

log_file = "mcdc_debug_log.txt"
logging.basicConfig(
    filename=log_file,
    filemode='w',
    level=logging.DEBUG,
    format='[%(levelname)s] %(message)s'
)
print(f"[INFO] All debug output will be saved to '{log_file}'")

def load_libclang():
    libclang_path = os.getenv("LIBCLANG_PATH")
    logging.debug(f"LIBCLANG_PATH = {libclang_path}")
    if libclang_path and os.path.exists(libclang_path):
        try:
            Config.set_library_file(libclang_path)
            logging.debug(f"Loaded libclang from LIBCLANG_PATH: {libclang_path}")
            return
        except LibclangError as e:
            logging.error(f"Failed to load libclang: {e}")
    for p in [
        r"C:\\Program Files\\LLVM\\bin\\libclang.dll",
        r"C:\\Program Files (x86)\\LLVM\\bin\\libclang.dll",
    ]:
        if os.path.exists(p):
            try:
                Config.set_library_file(p)
                logging.debug(f"Loaded libclang from fallback: {p}")
                return
            except LibclangError as e:
                logging.error(f"Fallback libclang load failed from {p}: {e}")
    logging.fatal("libclang.dll not found or could not be loaded.")
    sys.exit(1)

def normalize_path(path):
    abs_path = os.path.abspath(path)
    logging.debug(f"Normalized path: {path} -> {abs_path}")
    return abs_path

def parse_headers(include_path):
    logging.debug(f"Parsing headers in: {include_path}")
    index = Index.create()
    types = {}
    for root, _, files in os.walk(include_path):
        for fname in files:
            if fname.endswith('.h'):
                full_path = os.path.join(root, fname)
                logging.debug(f"Parsing header: {full_path}")
                tu = index.parse(full_path, args=[f'-I{include_path}'])
                for c in tu.cursor.get_children():
                    if c.kind in (CursorKind.STRUCT_DECL, CursorKind.ENUM_DECL, CursorKind.TYPEDEF_DECL):
                        if c.spelling:
                            logging.debug(f"Found type: {c.spelling}")
                            field_names = [f.spelling for f in c.get_children() if f.kind.name == 'FIELD_DECL']
                            for name in field_names:
                                logging.debug(f"[STRUCT {c.spelling}] Field: {name}")
                            types[c.spelling] = c
    return types

def parse_functions(src_path, include_path):
    logging.debug(f"Parsing C source files in: {src_path}")
    index = Index.create()
    funcs = []
    for root, _, files in os.walk(src_path):
        for fname in files:
            if fname.endswith('.c'):
                full_path = os.path.join(root, fname)
                logging.debug(f"Parsing source: {full_path}")
                tu = index.parse(full_path, args=[f'-I{include_path}'])
                for c in tu.cursor.get_children():
                    if c.kind == CursorKind.FUNCTION_DECL and c.is_definition():
                        logging.debug(f"Found function: {c.spelling}")
                        funcs.append(c)
    return funcs

def gather_atoms_and_fields(cond_cursor, struct_fields):
    atoms = []
    def visit(node):
        logging.debug(f"Visiting node: kind={node.kind}, spelling='{node.spelling}', displayname='{node.displayname}'")
        if node.kind == CursorKind.MEMBER_REF_EXPR:
            parent = node.semantic_parent
            if parent and parent.kind == CursorKind.UNEXPOSED_EXPR:
                grandparent = parent.semantic_parent
                if grandparent and grandparent.kind == CursorKind.DECL_REF_EXPR:
                    base_var = grandparent.spelling
                    field_name = node.spelling
                    combined_name = f"{base_var}.{field_name}"
                    atoms.append((combined_name, f"{combined_name} (from deref)"))
                    logging.debug(f"Matched dereferenced member: {combined_name}")
        elif node.kind == CursorKind.BINARY_OPERATOR:
            children = list(node.get_children())
            if len(children) == 2:
                lhs, rhs = children
                for side in (lhs, rhs):
                    if side.kind == CursorKind.MEMBER_REF_EXPR:
                        parent = side.semantic_parent
                        if parent and parent.kind == CursorKind.UNEXPOSED_EXPR:
                            grandparent = parent.semantic_parent
                            if grandparent and grandparent.kind == CursorKind.DECL_REF_EXPR:
                                base_var = grandparent.spelling
                                field_name = side.spelling
                                combined_name = f"{base_var}.{field_name}"
                                atoms.append((combined_name, f"{combined_name} (from comparison)"))
                                logging.debug(f"Matched member in comparison: {combined_name}")
        for child in node.get_children():
            visit(child)
    visit(cond_cursor)
    return atoms

def gather_conditions(fn_cursor, struct_fields):
    atoms = []
    def recurse(node):
        if node.kind in (CursorKind.IF_STMT, CursorKind.WHILE_STMT, CursorKind.CONDITIONAL_OPERATOR):
            logging.debug(f"Found conditional statement: {node.kind} in function {fn_cursor.spelling}")
            cond = next(node.get_children(), None)
            if cond:
                logging.debug(f"Condition expression: {cond.spelling} / {cond.displayname}")
                atoms.extend(gather_atoms_and_fields(cond, struct_fields))
            else:
                logging.warning(f"Condition node has no children in {fn_cursor.spelling}")
        for ch in node.get_children():
            recurse(ch)
    recurse(fn_cursor)
    logging.debug(f"Total atoms found for function {fn_cursor.spelling}: {atoms}")
    return list(dict.fromkeys(atoms))

def solve_mcdc(_, atoms):
    fields = {field for field, _ in atoms}
    logging.debug(f"Solving MC/DC with fields: {fields} and atoms: {atoms}")
    tests = []
    z3vars = {name: z3.Int(name) for name in fields}
    for (_, _), (field, expr) in enumerate(atoms):  # fix enumerate unpack
        for val in (0, 1):
            s = z3.Solver()
            s.add(z3vars[field] == val)
            for other, _ in atoms:
                if other != field:
                    s.add(z3vars[other] == 1)
            if s.check() == z3.sat:
                m = s.model()
                test_vec = {k: m[z3vars[k]].as_long() for k in z3vars}
                tests.append((f"{field}={val}", test_vec))
                logging.debug(f"Found SAT for {field}={val}: {test_vec}")
                break
            else:
                logging.warning(f"UNSAT for {field}={val} with others fixed to 1")
    return tests

def write_test_file(fn, cases, out_dir):
    args = list(fn.get_arguments())
    if not args:
        logging.error(f"No parameters for function {fn.spelling}, cannot generate test file.")
        return
    # dynamic parameter names and types
    name0 = args[0].spelling or 'input0'
    type0 = args[0].type.spelling.replace('*', '').strip()
    if len(args) > 1:
        name1 = args[1].spelling or 'input1'
        type1 = args[1].type.spelling.replace('*', '').strip()
    else:
        name1, type1 = None, None
    path = os.path.join(out_dir, f"testMCDC_{fn.spelling}.cpp")
    with open(path, 'w') as f:
        f.write('#include "gtest/gtest.h"\n')
        f.write('#include "mycode.h"\n')
        for i, (label, vals) in enumerate(cases, 1):
            f.write(f'TEST({fn.spelling}_MC_DC, Case{i}) {{\n')
            f.write(f'  {type0} {name0} = {{0}};\n')
            if name1:
                f.write(f'  {type1} {name1} = {{0}};\n')
            for k, v in vals.items():
                base, field = k.split('.', 1)
                f.write(f'  {base}.{field} = {v};\n')
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
        args = list(fn.get_arguments())
        if not args:
            logging.warning(f"Function {fn.spelling} has no arguments, skipping.")
            continue
        type0 = args[0].type.spelling.replace('*', '').strip()
        cursor = types.get(type0)
        if not cursor:
            logging.warning(f"Struct {type0} not found for {fn.spelling}, skipping.")
            continue
        fields = {f.spelling for f in cursor.get_children() if f.kind.name == 'FIELD_DECL'}
        logging.debug(f"Struct {type0} fields: {fields}")
        atoms = gather_conditions(fn, fields)
        cases = solve_mcdc(fields, atoms)
        if cases:
            write_test_file(fn, cases, tst)
        else:
            logging.warning(f"No MC/DC cases for {fn.spelling}")

if __name__ == '__main__':
    main()
