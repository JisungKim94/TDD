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

def parse_structs_and_enums(header_code):
    structs, enums = {}, {}
    # struct 파싱
    for body, name in re.findall(r'typedef\s+struct\s*{([^}]+)}\s*(\w+)\s*;', header_code, re.DOTALL):
        members = re.findall(r'\b(\w+)\s+(\w+);', body)
        structs[name] = [(typ, var) for typ, var in members]
    # enum 파싱
    for body, name in re.findall(r'typedef\s+enum\s*{([^}]+)}\s*(\w+)\s*;', header_code, re.DOTALL):
        enums[name] = re.findall(r'\b(\w+)\b', body)
    return structs, enums

def extract_function_signature(code):
    m = re.search(r'\b(?:\w+\s+)+(\w+)\s*\(([^)]*)\)', code)
    if not m:
        return None, []
    func, params = m.group(1), [p.strip() for p in m.group(2).split(',') if p.strip()]
    info = []
    for p in params:
        mm = re.match(r'(\w+(?:\s*\*)?)\s+(\w+)', p)
        if mm:
            info.append((mm.group(1).replace(' ', ''), mm.group(2)))
    return func, info

def extract_condition_variables(expr):
    cleaned = re.sub(r'[\(\)\!\&\|\=\>\<\+\-\*/]', ' ', expr)
    toks = set(re.findall(r'\b[a-zA-Z_]\w*\b', cleaned))
    return [t for t in toks if t not in {'if','return','else','while','for','int','void','true','false'}]

def generate_boolean_cases(n):
    base = [True]*n
    return [ (base[:i] + [not base[i]] + base[i+1:], base[:i] + [base[i]] + base[i+1:]) for i in range(n) ]

def parse_boolean_expr(expr, vm):
    e = expr
    for k,v in vm.items():
        e = re.sub(rf'\b{re.escape(k)}\b', str(int(v)), e)
    e = e.replace('&&',' and ').replace('||',' or ')
    try: return int(eval(e))
    except: return '/*?*/'

def gen_gtest_code(func, if_exprs, params, struct_defs, enum_defs, hdr_rel):
    lines = ['#include <gtest/gtest.h>',
             'extern "C" {',
             f'#include "{hdr_rel}"',
             '}','']
    for idx, expr in enumerate(if_exprs):
        vars_used = extract_condition_variables(expr)
        print(f"[DEBUG] If[{idx}] vars_used: {vars_used}")

        # param_vars 매핑
        param_vars = {}
        for t,name in params:
            ptr = '*' in t
            sep = '->' if ptr else '.'
            members = [v.split(sep)[1] for v in vars_used if v.startswith(name+sep)]
            if members:
                param_vars[(t,name)] = members
        # 기본형 매핑
        for v in vars_used:
            for t,name in params:
                if v == name:
                    param_vars.setdefault((t,name), None)

        print(f"[DEBUG] If[{idx}] param_vars: {param_vars}")

        # 테스트 생성 (생략: 이전 코드와 동일)
        # ...
    return "\n".join(lines)

def main():
    if len(sys.argv)!=2:
        print("Usage: python script.py path/to/source.c"); sys.exit(1)
    cpath = sys.argv[1]
    prj = os.path.dirname(os.path.dirname(cpath))
    hdr = os.path.splitext(os.path.basename(cpath))[0] + '.h'
    header_path = os.path.join(prj,'include',hdr)

    struct_defs, enum_defs = parse_structs_and_enums(read_file(header_path))
    code = read_file(cpath)
    func, params = extract_function_signature(code)
    ifs = re.findall(r'if\s*\((.*?)\)', code, re.DOTALL)

    print(f"[INFO] Function: {func}")
    print(f"[INFO] Found {len(ifs)} if-statements")

    out = gen_gtest_code(func, ifs, params, struct_defs, enum_defs,
                         os.path.relpath(header_path, os.path.join(prj,'test')).replace('\\','/'))
    with open(os.path.join(prj,'test','mcdc_tests.cpp'),'w',encoding='utf-8') as f:
        f.write(out)
    print("[SUCCESS] Generated.")

'''
- `gen_gtest_code()` 안에서  
  - `vars_used` 출력 → 해당 `if`의 추출된 변수 리스트  
  - `param_vars` 출력 → 인자별로 매핑된 변수 또는 멤버 목록  

이제 실행하면 터미널에 두 디버그 정보가 출력될 거예요.  
어떤 `vars_used`가 나오는지, 그리고 어떤 `param_vars`로 인식되는지 알려주시면  
왜 테스트 블록이 생성되지 않는지 바로 파악할 수 있습니다!
'''