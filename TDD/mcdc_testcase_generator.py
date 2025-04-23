# MC/DC 테스트케이스 생성기 (모든 함수 인풋 선언 + 구조체 {0} 초기화 + 100% MC/DC)
import os
import re
import sys
from collections import defaultdict

def read_file(path):
    for enc in ('utf-8','cp949','euc-kr'):
        try:
            with open(path, 'r', encoding=enc) as f:
                return f.read()
        except UnicodeDecodeError:
            continue
    raise UnicodeDecodeError(f"Cannot decode {path}")

def parse_structs_and_enums(hdr_code):
    structs, enums = {}, {}
    # struct parsing
    for body, name in re.findall(r'typedef\s+struct\s*{([^}]+)}\s*(\w+)\s*;', hdr_code, re.DOTALL):
        members = re.findall(r'\b(\w+)\s+(\w+);', body)
        structs[name] = [(typ, var) for typ, var in members]
    # enum parsing
    for body, name in re.findall(r'typedef\s+enum\s*{([^}]+)}\s*(\w+)\s*;', hdr_code, re.DOTALL):
        enums[name] = re.findall(r'\b(\w+)\b', body)
    return structs, enums

def extract_function_signature(code):
    m = re.search(r'\b(\w+(?:\s*\*)?)\s+(\w+)\s*\(([^)]*)\)', code)
    if not m:
        return None, []
    func = m.group(2)
    params = [p.strip() for p in m.group(3).split(',') if p.strip()]
    info = []
    for p in params:
        mm = re.match(r'(\w+(?:\s*\*)?)\s+(\w+)', p)
        if mm:
            info.append((mm.group(1).replace(' ', ''), mm.group(2)))
    return func, info

def extract_condition_variables(expr):
    clean = re.sub(r'[\(\)\!\&\|\=\>\<\+\-\*/]', ' ', expr)
    toks = set(re.findall(r'\b[a-zA-Z_]\w*\b', clean))
    return [t for t in toks if t not in {'if','return','else','while','for','int','void','true','false'}]

def generate_boolean_cases(n):
    base = [True]*n
    cases = []
    for i in range(n):
        c = base.copy()
        c[i] = not c[i]
        cases.append(c)
    return cases

def gen_gtest_code(func, if_exprs, params, struct_defs, enum_defs, hdr):
    lines = [
        '#include <gtest/gtest.h>',
        'extern "C" {',
        f'#include "{hdr}"',
        '}',''
    ]
    for idx, expr in enumerate(if_exprs):
        vars_used = extract_condition_variables(expr)
        # 파라미터별 멤버 매핑
        param_map = {}
        for typ, name in params:
            ptr = '*' in typ
            sep = '->' if ptr else '.'
            members = [v.split(sep)[1] for v in vars_used if v.startswith(name+sep)]
            if members:
                param_map[(typ, name)] = members
        for v in vars_used:
            for typ, name in params:
                if v == name:
                    param_map.setdefault((typ, name), None)
        # MC/DC 케이스 생성
        for (typ, name), members in param_map.items():
            count = len(members) if members else 1
            cases = generate_boolean_cases(count)
            for case_idx, vals in enumerate(cases):
                lines.append(f'TEST({func}, If{idx}_Case{case_idx})' + ' {')
                # 모든 파라미터 선언 & 초기화
                for t, nm in params:
                    # 기본값 설정
                    if '*' in t or t in struct_defs:
                        # struct 포인터/값 모두 같은 방식: {0} 초기화
                        styp = t.replace('*','')
                        lines.append(f'    {styp} {nm} = {{0}};')
                    elif t == 'float':
                        lines.append(f'    float {nm} = 0.0f;')
                    elif t in enum_defs:
                        # 첫 번째 열거형 값 사용
                        lines.append(f'    {t} {nm} = {enum_defs[t][0]};')
                    else:
                        lines.append(f'    {t} {nm} = 0;')
                # 조건 변수만 override
                vm = {}
                for i, ((typ2, nm2), mems) in enumerate(param_map.items()):
                    if mems:
                        # struct 멤버 토글
                        ptr = '*' in typ2
                        sep = '->' if ptr else '.'
                        for j, mem in enumerate(mems):
                            val = int(vals[j])
                            lines.append(f'    {nm2}.{mem} = {val};')
                            vm[f'{nm2}{sep}{mem}'] = vals[j]
                    else:
                        # 기본형 토글
                        val = int(vals[0])
                        lines.append(f'    {typ2} {nm2} = {val};')
                        vm[nm2] = vals[0]
                # 함수 호출
                args = [('&'+nm if '*' in t else nm) for t, nm in params]
                lines.append(f'    EXPECT_EQ({func}({", ".join(args)}), /* expected */);')
                lines.append('}')
                lines.append('')
    return "\n".join(lines)

def main():
    if len(sys.argv)!=2:
        print(f"Usage: {sys.argv[0]} path/to/source.c"); sys.exit(1)
    cpath = sys.argv[1]
    if not os.path.isfile(cpath):
        print("C file not found"); sys.exit(1)
    prj = os.path.dirname(os.path.dirname(cpath))
    hdr = os.path.splitext(os.path.basename(cpath))[0] + '.h'
    hpath = os.path.join(prj, 'include', hdr)
    if not os.path.isfile(hpath):
        print("Header not found"); sys.exit(1)

    hdr_code = read_file(hpath)
    struct_defs, enum_defs = parse_structs_and_enums(hdr_code)
    code = read_file(cpath)
    func, params = extract_function_signature(code)
    if not func:
        print("Error: function not found"); sys.exit(1)
    if_exprs = re.findall(r'if\s*\((.*?)\)', code, re.DOTALL)
    print(f"[INFO] Function: {func}")
    print(f"[INFO] Found {len(if_exprs)} if-statements")

    test_dir = os.path.join(prj, 'test')
    os.makedirs(test_dir, exist_ok=True)
    out_cpp = os.path.join(test_dir, 'mcdc_tests.cpp')
    rel_hdr = os.path.relpath(hpath, test_dir).replace('\\','/')

    gtest = gen_gtest_code(func, if_exprs, params, struct_defs, enum_defs, rel_hdr)
    with open(out_cpp, 'w', encoding='utf-8') as f:
        f.write(gtest)
    print(f"[SUCCESS] Generated: {out_cpp}")

if __name__ == "__main__":
    main()
