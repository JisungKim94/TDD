# 통합 버전: 구조체 인자 (포인터/값) 처리 + 구조체 멤버 기반 MC/DC 테스트 자동 생성

import os
import re
import sys
from collections import defaultdict

def read_file(path):
    for enc in ('utf-8', 'cp949', 'euc-kr'):
        try:
            with open(path, 'r', encoding=enc) as f:
                return f.read()
        except UnicodeDecodeError:
            continue
    raise UnicodeDecodeError(f"Cannot decode {path}")

def parse_structs_from_header(header_code):
    structs = {}
    typedefs = re.findall(r'typedef\s+struct\s*{([^}]+)}\s*(\w+)\s*;', header_code, re.DOTALL)
    for body, name in typedefs:
        members = re.findall(r'\b\w+\s+(\w+);', body)
        structs[name] = members
    return structs

def extract_function_signature(code):
    match = re.search(r'\b(?:\w+\s+)+(\w+)\s*\(([^)]*)\)', code)
    if not match:
        return None, []
    func_name = match.group(1)
    params = match.group(2).split(',')
    param_info = []
    for p in params:
        p = p.strip()
        if not p:
            continue
        m = re.match(r'(\w+(?:\s*\*)?)\s+(\w+)', p)
        if m:
            type_part = m.group(1).replace(' ', '')
            name = m.group(2)
            param_info.append((type_part, name))
    return func_name, param_info

def extract_condition_variables(expr):
    expr = re.sub(r'[\(\)\!\&\|\=\>\<\+\-\*/]', ' ', expr)
    tokens = set(re.findall(r'\b[a-zA-Z_]\w*\b', expr))
    keywords = {'if', 'return', 'else', 'while', 'for', 'int', 'void', 'true', 'false'}
    return [t for t in tokens if t not in keywords]

def generate_mcdc_cases(members):
    n = len(members)
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

def gen_gtest_code(func_name, if_exprs, param_info, struct_defs, header_relpath):
    lines = [
        '#include <gtest/gtest.h>',
        'extern "C" {',
        f'#include "{header_relpath}"',
        '}',
        ''
    ]

    testname = func_name
    for idx, expr in enumerate(if_exprs):
        var_names = extract_condition_variables(expr)
        struct_vars = defaultdict(list)

        # 변수이름에 따라 어떤 구조체 멤버인지 추론
        for typename, varname in param_info:
            deref = '->' if '*' in typename else '.'
            for v in var_names:
                if v.startswith(f'{varname}{deref}'):
                    member = v.split(deref)[1]
                    struct_vars[(typename.replace('*', ''), varname)].append(member)

        # 테스트케이스 생성
        for (typename, instancename), members in struct_vars.items():
            if typename not in struct_defs:
                continue
            mcdc_cases = generate_mcdc_cases(members)
            for case_idx, (c1, c2) in enumerate(mcdc_cases):
                for version, values in enumerate([c1, c2]):
                    lines.append(f'TEST({testname}, If{idx}_MC_DC_Case{case_idx}_{version}) {{')
                    lines.append(f'    {typename} {instancename} = {{')
                    for i, member in enumerate(members):
                        lines.append(f'        .{member} = {int(values[i])},')
                    lines.append(f'    }};')
                    call_args = []
                    for t, name in param_info:
                        call_args.append(f'&{name}' if '*' in t else name)
                    cond_map = {f'{instancename}->'+members[i] if '*' in t else f'{instancename}.{members[i]}': values[i]
                                for (t, name) in [param_info[0]] for i in range(len(members))}
                    expected = parse_boolean_expr(expr, cond_map)
                    lines.append(f'    EXPECT_EQ({expected}, {func_name}({", ".join(call_args)}));')
                    lines.append('}')
                    lines.append('')
    return '\n'.join(lines)

def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} path/to/source.c")
        sys.exit(1)

    c_path = sys.argv[1]
    if not os.path.isfile(c_path):
        print(f"Error: C file not found: {c_path}")
        sys.exit(1)

    project_root = os.path.dirname(os.path.dirname(c_path))
    header_name = os.path.splitext(os.path.basename(c_path))[0] + '.h'
    header_path = os.path.join(project_root, 'include', header_name)

    if not os.path.isfile(header_path):
        print(f"Error: Header file not found: {header_path}")
        sys.exit(1)

    header_code = read_file(header_path)
    struct_defs = parse_structs_from_header(header_code)

    code = read_file(c_path)
    func_name, param_info = extract_function_signature(code)
    if not func_name:
        print("Error: Could not find function definition.")
        sys.exit(1)

    all_ifs = re.findall(r'if\s*\((.*?)\)', code, re.DOTALL)
    if not all_ifs:
        print("Error: No if-statements found.")
        sys.exit(1)

    print(f"[INFO] Function: {func_name}")
    print(f"[INFO] Found {len(all_ifs)} if-statements")

    test_dir = os.path.join(project_root, 'test')
    os.makedirs(test_dir, exist_ok=True)
    out_path = os.path.join(test_dir, 'mcdc_tests.cpp')
    header_rel = os.path.relpath(header_path, test_dir).replace('\\', '/')

    with open(out_path, 'w', encoding='utf-8') as f:
        f.write(gen_gtest_code(func_name, all_ifs, param_info, struct_defs, header_rel))

    print(f"[SUCCESS] Generated: {out_path}")

if __name__ == "__main__":
    main()

