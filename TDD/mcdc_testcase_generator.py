# MC/DC 테스트케이스 생성기 (모든 struct 타입 자동 감지 + {0} 초기화)

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
    # typedef struct { ... } Name;
    for body, name in re.findall(r'typedef\s+struct\s*{([^}]+)}\s*(\w+)\s*;', hdr, re.DOTALL):
        members = re.findall(r'\b(\w+)\s+(\w+);', body)
        structs[name] = members
    # typedef struct Name { ... } Name;
    for tag, body, name in re.findall(r'typedef\s+struct\s+(\w+)\s*{([^}]+)}\s*(\w+)\s*;', hdr, re.DOTALL):
        members = re.findall(r'\b(\w+)\s+(\w+);', body)
        structs[name] = members
    # enum parsing
    for body, name in re.findall(r'typedef\s+enum\s*{([^}]+)}\s*(\w+)\s*;', hdr, re.DOTALL):
        enums[name] = re.findall(r'\b(\w+)\b', body)
    return structs, enums

def extract_signature(code):
    m = re.search(r'\b(\w+(?:\s*\*)?)\s+(\w+)\s*\(([^)]*)\)', code)
    if not m: return None, []
    func = m.group(2)
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
    toks = set(re.findall(r'\b[a-zA-Z_]\w*(?:->\w+|\.\w+)?\b', expr))
    return sorted([t for t in toks if not re.match(r'^(if|for|while|return)\b', t)])

def generate_boolean_cases(n):
    base = [True]*n
    cases = []
    for i in range(n):
        c = base.copy()
        c[i] = not c[i]
        cases.append(c)
    return cases

def gen_tests(func, params, if_exprs, structs, enums, hdr_rel):
    lines = [
        '#include <gtest/gtest.h>',
        'extern "C" {',
        f'#include "{hdr_rel}"',
        '}',''
    ]
    for idx, expr in enumerate(if_exprs):
        vars_used = extract_vars(expr)
        # param → members mapping
        mapping = []
        for typ,name in params:
            base = typ.replace('*','')
            if base in structs:
                sep = '->' if '*' in typ else '.'
                members = [v.split(sep,1)[1] for v in vars_used if v.startswith(name+sep)]
                if members:
                    mapping.append((typ,name,members))
            else:
                if name in vars_used:
                    mapping.append((typ,name,None))
        # MC/DC per mapping entry
        for case_idx,(typ,name,members) in enumerate(mapping):
            n = len(members) if members else 1
            for bit in range(n):
                for val in (0,1):
                    lines.append(f'TEST({func}, If{idx}_Case{case_idx}_{bit}_{val}) {{')
                    # 1) 모든 파라미터 선언 & 초기화
                    for t,nm in params:
                        bt = t.replace('*','')
                        if bt in structs:
                            # struct pointer or value
                            lines.append(f'    {bt} {nm}_val = {{0}};')
                            if '*' in t:
                                lines.append(f'    {bt} *{nm} = &{nm}_val;')
                            else:
                                lines.append(f'    {bt} {nm} = {nm}_val;')
                        elif t=='float':
                            lines.append(f'    float {nm} = 0.0f;')
                        elif t in enums:
                            lines.append(f'    {t} {nm} = {enums[t][0]};')
                        else:
                            lines.append(f'    {t} {nm} = 0;')
                    # 2) toggle only the target
                    if members:
                        sep = '->' if '*' in typ else '.'
                        mem = members[bit]
                        if '*' in typ:
                            lines.append(f'    {name}_val.{mem} = {val};')
                        else:
                            lines.append(f'    {name}.{mem} = {val};')
                    else:
                        lines.append(f'    {typ} {name} = {val};')
                    # 3) call
                    args = [('&'+nm if '*' in t else nm) for t,nm in params]
                    lines.append(f'    EXPECT_EQ({func}({", ".join(args)}), /* expected */);')
                    lines.append('}')
                    lines.append('')
    return "\n".join(lines)

def main():
    if len(sys.argv)!=2:
        print(f"Usage: {sys.argv[0]} path/to/source.c"); sys.exit(1)
    cfile = sys.argv[1]
    prj = os.path.dirname(os.path.dirname(cfile))
    hdr = os.path.splitext(os.path.basename(cfile))[0]+'.h'
    hpath = os.path.join(prj,'include',hdr)
    hdr_code = read_file(hpath)
    structs, enums = parse_structs_and_enums(hdr_code)

    code = read_file(cfile)
    func, params = extract_signature(code)
    if_exprs = extract_if_exprs(code)

    print(f"[INFO] Function: {func}")
    print(f"[INFO] Found {len(if_exprs)} if-statements")

    out_dir = os.path.join(prj,'test'); os.makedirs(out_dir, exist_ok=True)
    out_cpp = os.path.join(out_dir,'mcdc_tests.cpp')
    rel_hdr = os.path.relpath(hpath, out_dir).replace('\\','/')

    txt = gen_tests(func, params, if_exprs, structs, enums, rel_hdr)
    with open(out_cpp,'w',encoding='utf-8') as f:
        f.write(txt)

    print(f"[SUCCESS] Generated: {out_cpp}")

if __name__=="__main__":
    main()

