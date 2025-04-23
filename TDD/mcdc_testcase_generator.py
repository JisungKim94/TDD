#!/usr/bin/env python3
import os, re, sys

def read_file(path):
    for enc in ('utf-8','cp949','euc-kr'):
        try:
            return open(path, 'r', encoding=enc).read()
        except UnicodeDecodeError:
            continue
    raise UnicodeDecodeError(f"Cannot decode {path}")

def parse_structs_and_enums(hdr):
    structs, enums = {}, {}
    # struct 파싱
    for body,name in re.findall(r'typedef\s+struct\s*{([^}]+)}\s*(\w+)\s*;', hdr, re.DOTALL):
        members = re.findall(r'\b(\w+)\s+(\w+);', body)
        structs[name] = members
    # enum 파싱
    for body,name in re.findall(r'typedef\s+enum\s*{([^}]+)}\s*(\w+)\s*;', hdr, re.DOTALL):
        enums[name] = re.findall(r'\b(\w+)\b', body)
    return structs, enums

def extract_signature(code):
    m = re.search(r'\b(\w+(?:\s*\*)?)\s+(\w+)\s*\(([^)]*)\)', code)
    if not m: return None, []
    ret, func = m.group(1).strip(), m.group(2).strip()
    params = [p.strip() for p in m.group(3).split(',') if p.strip()]
    out = []
    for p in params:
        mm = re.match(r'(\w+(?:\s*\*)?)\s+(\w+)', p)
        if mm:
            out.append((mm.group(1).replace(' ',''), mm.group(2)))
    return func, out

def extract_if_exprs(code):
    return re.findall(r'if\s*\((.*?)\)', code, re.DOTALL)

def extract_vars(expr):
    clean = re.sub(r'[^\w\.\->]', ' ', expr)
    toks = set(re.findall(r'\b[a-zA-Z_]\w*(?:->\w+|\.\w+)?\b', clean))
    return sorted(toks)

def gen_tests(func, params, if_exprs, structs, enums, hdr_rel):
    lines = [
        '#include <gtest/gtest.h>',
        'extern "C" {',
        f'#include "{hdr_rel}"',
        '}',''
    ]
    for idx, expr in enumerate(if_exprs):
        vars_used = extract_vars(expr)
        # 어떤 파라미터의 멤버/변수를 쓰는지 매핑
        mapping = []
        for typ,name in params:
            ptr = '*' in typ
            sep = '->' if ptr else '.'
            # struct member
            members = [v.split(sep,1)[1] for v in vars_used if v.startswith(name+sep)]
            if members:
                mapping.append((typ,name,members))
        # basic param
        for v in vars_used:
            for typ,name in params:
                if v==name:
                    mapping.append((typ,name,None))

        # MC/DC: mapping 각각의 조건만 toggle
        for case_idx,(typ,name,members) in enumerate(mapping):
            n = len(members) if members else 1
            for bit in range(n):
                # toggle True/False
                for val in (0,1):
                    test_name = f"If{idx}_Param{case_idx}_M{bit}_{val}"
                    lines.append(f"TEST({func}, {test_name}) {{")
                    # --- 1) 모든 파라미터 선언 & 기본 초기화 ---
                    for ptyp,pname in params:
                        base_typ = ptyp.replace('*','')
                        if '*' in ptyp or base_typ in structs:
                            # struct 포인터 or 값
                            # 내부 _val 인스턴스
                            lines.append(f"    {base_typ} {pname}_val = {{0}};")
                            if '*' in ptyp:
                                lines.append(f"    {base_typ} *{pname} = &{pname}_val;")
                            else:
                                lines.append(f"    {base_typ} {pname} = {pname}_val;")
                        elif ptyp=='float':
                            lines.append(f"    float {pname} = 0.0f;")
                        elif ptyp in enums:
                            lines.append(f"    {ptyp} {pname} = {enums[ptyp][0]};")
                        else:
                            lines.append(f"    {ptyp} {pname} = 0;")
                    # --- 2) 조건식 대상만 override ---
                    if members:
                        # struct member toggle
                        sep = '->' if '*' in typ else '.'
                        # e.g. st_Failure->failA or st_Failure.failA
                        target = f"{name}{sep}{members[bit]}"
                        value = val
                        # override
                        if '*' in typ:
                            lines.append(f"    {name}_val.{members[bit]} = {value};")
                        else:
                            lines.append(f"    {name}.{members[bit]} = {value};")
                    else:
                        # basic type toggle
                        lines.append(f"    {typ} {name} = {val};")
                    # --- 3) 호출 ---
                    args = []
                    for ptyp,pname in params:
                        args.append(f"&{pname}" if '*' in ptyp else pname)
                    lines.append(f"    EXPECT_EQ({func}({', '.join(args)}), /* expected */);")
                    lines.append("}")
                    lines.append("")
    return "\n".join(lines)

def main():
    if len(sys.argv)!=2:
        print(f"Usage: {sys.argv[0]} path/to/source.c"); sys.exit(1)
    cpath = sys.argv[1]
    if not os.path.isfile(cpath):
        print("C file not found"); sys.exit(1)

    prj = os.path.dirname(os.path.dirname(cpath))
    hdr = os.path.splitext(os.path.basename(cpath))[0] + '.h'
    hpath = os.path.join(prj,'include',hdr)
    if not os.path.isfile(hpath):
        print("Header not found"); sys.exit(1)

    hdr_code = read_file(hpath)
    structs, enums = parse_structs_and_enums(hdr_code)

    code = read_file(cpath)
    func, params = extract_signature(code)
    if not func:
        print("Function not found"); sys.exit(1)
    if_exprs = extract_if_exprs(code)

    print(f"[INFO] Function: {func}")
    print(f"[INFO] Found {len(if_exprs)} if-statements")

    out_dir = os.path.join(prj,'test'); os.makedirs(out_dir,exist_ok=True)
    out_cpp = os.path.join(out_dir,'mcdc_tests.cpp')
    rel_hdr = os.path.relpath(hpath, out_dir).replace('\\','/')

    txt = gen_tests(func, params, if_exprs, structs, enums, rel_hdr)
    with open(out_cpp,'w',encoding='utf-8') as f:
        f.write(txt)

    print(f"[SUCCESS] Generated: {out_cpp}")

if __name__=="__main__":
    main()
