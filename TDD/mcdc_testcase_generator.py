# mcdc_testcase_generator.py

import re
from itertools import product


def extract_conditions(expr):
    # 분리 연산자 처리
    tokens = re.split(r'(\&\&|\|\|)', expr)
    conds = [t.strip('() ') for t in tokens if t not in ('&&', '||')]
    # 중복 제거
    return list(dict.fromkeys(conds))


def generate_truth_table(conditions):
    # 모든 가능한 True/False 조합
    return list(product([False, True], repeat=len(conditions)))


def evaluate_expression(expr, mapping):
    temp = expr
    for cond, val in mapping.items():
        temp = temp.replace(cond, str(val))
    temp = temp.replace('&&', ' and ').replace('||', ' or ')
    return eval(temp)


def find_if_expressions(code):
    # if (...) 구문 안의 표현식 추출
    return re.findall(r'if\s*\(([^)]+)\)', code)


def generate_mcdc_pairs(expr):
    conditions = extract_conditions(expr)
    table = generate_truth_table(conditions)
    mcdc_pairs = []
    for i, cond in enumerate(conditions):
        for a in table:
            for b in table:
                if a == b: continue
                # i번째 조건만 다르고, 결과가 달라야 함
                if all(a[j] == b[j] for j in range(len(conditions)) if j != i) and a[i] != b[i]:
                    r1 = evaluate_expression(expr, dict(zip(conditions, a)))
                    r2 = evaluate_expression(expr, dict(zip(conditions, b)))
                    if r1 != r2:
                        mcdc_pairs.append((a, b))
                        break
    # flatten unique mappings
    cases = []
    seen = set()
    for a, b in mcdc_pairs:
        for tup in (a, b):
            mapping = dict(zip(conditions, tup))
            key = tuple(sorted(mapping.items()))
            if key not in seen:
                seen.add(key)
                cases.append(mapping)
    return conditions, cases


def generate_gtest(code, infile):
    exprs = find_if_expressions(code)
    out = []
    out.append('#include <gtest/gtest.h>')
    out.append(f'extern "C" {{ #include \"{infile}\" }}')
    out.append('')
    test_idx = 1
    for expr in exprs:
        conds, cases = generate_mcdc_pairs(expr)
        suite_name = f'MCDC_{test_idx}'
        for idx, case in enumerate(cases, start=1):
            args = ', '.join(f'{"true" if v else "false"}' for v in [case[c] for c in conds])
            # 변수 설정 (bool c0 = ..., c1 = ...)
            assigns = '\n    '.join(f'bool {c} = {"true" if case[c] else "false"};' for c in conds)
            # EXPECT_TRUE or EXPECT_FALSE
            result = 'EXPECT_TRUE' if evaluate_expression(expr, case) else 'EXPECT_FALSE'
            out.append(f'TEST({suite_name}, Case{idx}) {{')
            out.append(f'    {assigns}')
            out.append(f'    {result}({expr});')
            out.append('}\n')
        test_idx += 1
    return '\n'.join(out)


if __name__ == '__main__':
    import sys
    if len(sys.argv) != 2:
        print('Usage: python mcdc_testcase_generator.py <c_source_file>')
        sys.exit(1)
    c_file = sys.argv[1]
    with open(c_file) as f:
        code = f.read()
    gtest_code = generate_gtest(code, c_file)
    out_file = 'mcdc_tests.cpp'
    with open(out_file, 'w') as f:
        f.write(gtest_code)
    print(f'Generated GoogleTest MC/DC test file: {out_file}')
