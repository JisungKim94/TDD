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

# Logging configuration
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

