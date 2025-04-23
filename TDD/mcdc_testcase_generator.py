import os
import re
import sys

def extract_condition_variables(expr):
    expr = re.sub(r'[\(\)\!\&\|\=\>\<\+\-\*/]', ' ', expr)
    tokens = set(re.findall(r'\b[a-zA-Z_]\w*\b', expr))
    keywords = {'if', 'return', 'else', 'while', 'for', 'int', 'void', 'true', 'false'}
    return [t for t in tokens if t not in keywords]

def generate_mcdc_cases(variables):
    n = len(variables)
    base = [True] * n
    cases = []
    for i in range(n):
        tc1 = base.copy()
        tc2 = base.copy()
        tc1[i] = not tc1[i]
        cases.append((tc1, tc2))
    return cases

def parse_boolean_expr(expr, vars_map):
    expr_eval = expr
    for var in vars_map:
        expr_eval = re.sub(rf'\b{re.escape(var)}\b', str(int(vars_map[var])), expr_eval)
    expr_eval = expr_eval.replace('&&', ' and ').replace('||', ' or ')
    try:
        return int(eval(expr_eval))
    except Exception:
        return '/* unknown */'

def gen_gtest_code(func_name, all_if_exprs, header_relpath, varmap_by_if):
    lines = [
        '#include <gtest/gtest.h>',
        'extern "C" {',
        f'#include "{header_relpath}"',
        '}',
        ''
    ]
    testname = os.path.splitext(os.path.basename(header_relpath))[0]
    for if_idx, expr in enumerate(all_if_exprs):
        variables = varmap_by_if[if_idx]
        cases = generate_mcdc_cases(variables)
        for case_idx, (tc1, tc2) in enumerate(cases):
            for version, inputs in enumerate([tc1, tc2]):
                var_assign = {variables[i]: inputs[i] for i in range(len(variables))}
                expected = parse_boolean_expr(expr, var_assign)
                lines.append(f'TEST({testname}, If{if_idx}_MC_DC_Case{case_idx}_{version}) {{')
                for i, var in enumerate(variables):
                    lines.append(f'    int {var} = {int(inputs[i])};')
                arg_str = ', '.join(variables)
                lines.append(f'    EXPECT_EQ({expected}, {func_name}({arg_str}));')
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

    m_func = re.search(r'\b(?:static\s+)?(?:inline\s+)?(?:\w+\s+)+(\w+)\s*\(', code)
    if not m_func:
        print("Error: No function found.")
        sys.exit(1)
    func_name = m_func.group(1)

    all_ifs = re.findall(r'if\s*\((.*?)\)', code, re.DOTALL)
    if not all_ifs:
        print("Error: No if-statements found for MC/DC generation.")
        sys.exit(1)

    print(f"[INFO] Function: {func_name}")
    print(f"[INFO] Found {len(all_ifs)} if-statement(s)")

    varmap_by_if = []
    for i, expr in enumerate(all_ifs):
        vars_used = extract_condition_variables(expr)
        print(f"[INFO] If[{i}] uses variables: {vars_used}")
        varmap_by_if.append(vars_used)

    test_dir = os.path.join(project_root, 'test')
    os.makedirs(test_dir, exist_ok=True)
    out_path = os.path.join(test_dir, 'mcdc_tests.cpp')
    header_relpath = os.path.relpath(header_path, test_dir).replace('\\', '/')

    with open(out_path, 'w', encoding='utf-8') as f:
        f.write(gen_gtest_code(func_name, all_ifs, header_relpath, varmap_by_if))

    print(f"[SUCCESS] MC/DC test code with named inputs written to: {out_path}")

if __name__ == "__main__":
    main()
