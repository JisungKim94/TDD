#!/usr/bin/env python3
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
    for body, name in re.findall(r'typedef\s+struct\s*{([^}]+)}\s*(\w+)\s*;', header_code, re.DOTALL):
        members = re.findall(r'\b(\w+)\s+(\w+);', body)
        structs[name] = [(typ, var) for typ, var in members]
    for body, name in re.findall(r'typedef\s+enum\s*{([^}]+)}\s*(\w+)\s*;', header_code, re.DOTALL):
        enums[name] = re.findall(r'\b(\w+)\b', body)
    return structs, enums

def extract_function_signature(code):
    m = re.search(r'\b(?:\w+\s+)+(\w+)\s*\(([^)]*)\)', code)
    if not m:
        return None, []
    func = m.group(1)
    params = [p.strip() for p in m.group(2).split(',') if p.strip()]
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
    cases = []
    for i in range(n):
        c1 = base.copy(); c2 = base.copy()
        c1[i] = not c1[i]
        cases.append((c1, c2))
    return cases

def parse_boolean_expr(expr, vm):
    e = expr
    for k,v in vm.items():
        e = re.sub(rf'\b{re.escape(k)}\b', str(int(v)), e)
    e = e.replace('&&',' and ').replace('||',' or ')
    try: return int(eval(e))
    except: return '/*?*/'

def gen_gtest_code(func, if_exprs, params, struct_defs, enum_defs, hdr):
    lines = [
        '#include <gtest/gtest.h>',
        'extern "C" {',
        f'#include "{hdr}"',
        '}',''
    ]
    for idx, expr in enumerate(if_exprs):
        vars_used = extract_condition_variables(expr)
        print(f"[DEBUG] If[{idx}] vars_used: {vars_used}")

        # 매핑
        param_vars = {}
        for t,name in params:
            ptr = '*' in t
            sep = '->' if ptr else '.'
            members = [v.split(sep)[1] for v in vars_used if v.startswith(name+sep)]
            if members:
                param_vars[(t,name)] = members
        # 기본형
        for v in vars_used:
            for t,name in params:
                if v == name:
                    param_vars.setdefault((t,name), None)

        print(f"[DEBUG] If[{idx}] param_vars: {param_vars}")

        # 테스트케이스 생성
        for (t,name), members in param_vars.items():
            # generate cases
            n = len(members) if members else 1
            cases = generate_boolean_cases(n)
            for case_idx,(c1,c2) in enumerate(cases):
                for ver,vals in enumerate([c1,c2]):
                    lines.append(f'TEST({func}, If{idx}_Case{case_idx}_{ver}) {{')
                    # 선언
                    if members:
                        styp = t.replace('*','')
                        lines.append(f'    {styp} {name} = '+'{')
                        vm = {}
                        for i,mem in enumerate(members):
                            val = vals[i]
                            # enum or basic
                            ftype = next((ft for ft,fv in struct_defs[styp] if fv==mem), None)
                            if ftype and ftype in enum_defs:
                                v = enum_defs[ftype][0]
                            else:
                                v = int(val)
                            lines.append(f'        .{mem} = {v},')
                            key = (name+'->'+mem) if '*' in t else (name+'.'+mem)
                            vm[key] = val
                        lines.append('    };')
                    else:
                        vm = {}
                        val = c1[0]  # basic uses only first
                        if t == 'float':
                            lines.append(f'    float {name} = {1.0 if val else 0.0}f;')
                        elif t in enum_defs:
                            lines.append(f'    {t} {name} = {enum_defs[t][0]};')
                        else:
                            lines.append(f'    {t} {name} = {int(val)};')
                        vm[name] = val

                    # 호출 및 검증
                    args = [('&'+nm if '*' in tp else nm) for tp,nm in params]
                    expected = parse_boolean_expr(expr, vm)
                    lines.append(f'    EXPECT_EQ({expected}, {func}({", ".join(args)}));')
                    lines.append('}')
                    lines.append('')
    return '\n'.join(lines)

def main():
    if len(sys.argv)!=2:
        print(f"Usage: {sys.argv[0]} path/to/source.c"); sys.exit(1)
    cfile = sys.argv[1]
    if not os.path.isfile(cfile):
        print("C file not found"); sys.exit(1)

    prj = os.path.dirname(os.path.dirname(cfile))
    hdr = os.path.splitext(os.path.basename(cfile))[0]+'.h'
    header_path = os.path.join(prj,'include',hdr)
    if not os.path.isfile(header_path):
        print("Header not found"); sys.exit(1)

    header_code = read_file(header_path)
    struct_defs, enum_defs = parse_structs_and_enums(header_code)

    code = read_file(cfile)
    func, params = extract_function_signature(code)
    if not func:
        print("Error: function not found"); sys.exit(1)

    if_exprs = re.findall(r'if\s*\((.*?)\)', code, re.DOTALL)
    print(f"[INFO] Function: {func}")
    print(f"[INFO] Found {len(if_exprs)} if-statements")

    out_dir = os.path.join(prj,'test')
    os.makedirs(out_dir, exist_ok=True)
    out_cpp = os.path.join(out_dir,'mcdc_tests.cpp')
    rel_hdr = os.path.relpath(header_path, out_dir).replace('\\','/')

    gtest_code = gen_gtest_code(func, if_exprs, params, struct_defs, enum_defs, rel_hdr)
    with open(out_cpp,'w',encoding='utf-8') as f:
        f.write(gtest_code)

    print(f"[SUCCESS] Generated: {out_cpp}")

if __name__=="__main__":
    main()
