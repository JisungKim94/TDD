#!/usr/bin/env python3
import os
import re
import sys

def extract_conditions(expr):
    tokens = re.split(r'(\|\||&&)', expr)
    return [t.strip() for t in tokens if t.strip() and t not in ('&&', '||')]

def generate_mcdc_cases(conds):
    n = len(conds)
    base = [True] * n
    cases = []
    for i in range(n):
        tc1 = base.copy()
        tc2 = base.copy()
        tc1[i] = not tc1[i]
        cases.append((tc1, tc2))
    return cases

def gen_gtest_code(func_name, conds, cases, header_relpath):
    lines = [
        '#include <gtest/gtest.h>',
        'extern "C" {',
        f'#include "{header_relpath}"',
        '}',
        ''
    ]
    testname = os.path.splitext(os.path.basename(header_relpath))[0]
    for idx, (c1, c2) in enumerate(cases):
        lines.append(f'TEST({testname}, MC_DC_Case{idx}) {{')
        args1 = ', '.join(str(int(v)) for v in c1)
        args2 = ', '.join(str(int(v)) for v in c2)
        lines.append(f'    EXPECT_EQ({func_name}({args1}), /* expected1 */);')
        lines.append(f'    EXPECT_EQ({func_name}({args2}), /* expected2 */);')
        lines.append('}')
        lines.append('')
    return "\n".join(lines)

def read_file(path):
    for enc in ('utf-8', 'cp949', 'euc-kr'):
        try:
            with open(path, 'r', encoding=enc) as f:
                return f.read()
        except UnicodeDecodeError:
            continue
    raise UnicodeDecodeError(f"Cannot decode {path} with utf-8, cp949, or euc-kr")

def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} path/to/source.c")
        sys.exit(1)

    c_path = sys.argv[1]
    if not os.path.isfile(c_path):
        print(f"Error: C source not found: {c_path}")
        sys.exit(1)

    project_root = os.path.dirname(os.path.dirname(c_path))
    header_name = os.path.splitext(os.path.basename(c_path))[0] + '.h'
    header_path = os.path.join(project_root, 'include', header_name)
    if not os.path.isfile(header_path):
        print(f"Error: Header not found: {header_path}")
        sys.exit(1)

    code = read_file(c_path)
    m = re.search(r'\bint\s+(\w+)\s*\([^)]*\)\s*\{[^}]*if\s*\(([^)]+)\)', code, re.DOTALL)
    if not m:
        print("Error: No if-statement found for MC/DC generation.")
        sys.exit(1)

    func_name, expr = m.group(1), m.group(2)
    conds = extract_conditions(expr)
    cases = generate_mcdc_cases(conds)

    test_dir = os.path.join(project_root, 'test')
    os.makedirs(test_dir, exist_ok=True)
    out_path = os.path.join(test_dir, 'mcdc_tests.cpp')
    header_relpath = os.path.relpath(header_path, test_dir).replace('\\', '/')

    with open(out_path, 'w', encoding='utf-8') as f:
        f.write(gen_gtest_code(func_name, conds, cases, header_relpath))

    print(f"MC/DC test code generated: {out_path}")

if __name__ == "__main__":
    main()
