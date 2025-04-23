# 최종 통합 버전: 함수명 유연하게 추출 + if 조건 자동 인식 + MC/DC 케이스 생성

import os
import re
import sys

def extract_conditions(expr):
    tokens = re.split(r'(\|\||&&)', expr)
    return [t.strip() for t in tokens if t.strip() and t not in ('&&', '||')]

def generate_mcdc_cases(conds):
    base = [True] * len(conds)
    cases = []
    for i in range(len(conds)):
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
    return '\n'.join(lines)

def read_file(path):
    for enc in ('utf-8', 'cp949', 'euc-kr'):
        try:
            with open(path, 'r', encoding=enc) as f:
                return f.read()
        except UnicodeDecodeError:
            continue
    raise UnicodeDecodeError(f"Cannot decode {path}")

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

    # 함수 이름 추출 (넓게 허용)
    m_func = re.search(r'\b(?:static\s+)?(?:inline\s+)?(?:\w+\s+)+(\w+)\s*\(', code)
    if not m_func:
        print("Error: No function found.")
        sys.exit(1)
    func_name = m_func.group(1)

    # 첫 번째 if 문 조건 추출
    m_if = re.search(r'if\s*\((.*?)\)', code, re.DOTALL)
    if not m_if:
        print("Error: No if-statement found for MC/DC generation.")
        sys.exit(1)
    expr = m_if.group(1)

    print(f"[INFO] Function: {func_name}")
    print(f"[INFO] Condition: {expr.strip()}")

    conds = extract_conditions(expr)
    if not conds:
        print("Error: No conditions extracted.")
        sys.exit(1)
    cases = generate_mcdc_cases(conds)

    test_dir = os.path.join(project_root, 'test')
    os.makedirs(test_dir, exist_ok=True)
    out_path = os.path.join(test_dir, 'mcdc_tests.cpp')
    header_relpath = os.path.relpath(header_path, test_dir).replace('\\', '/')

    with open(out_path, 'w', encoding='utf-8') as f:
        f.write(gen_gtest_code(func_name, conds, cases, header_relpath))

    print(f"[SUCCESS] MC/DC test code written to: {out_path}")

if __name__ == "__main__":
    main()
