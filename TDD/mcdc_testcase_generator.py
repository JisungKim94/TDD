import os
import re
import sys
import tkinter as tk
from tkinter import filedialog, messagebox

def extract_conditions(expr):
    # 단순히 &&, ||, ! 연산자 기준으로 조건 분리 (매우 단순화 버전)
    tokens = re.split(r'(\|\||&&)', expr)
    conds = []
    for t in tokens:
        t = t.strip()
        if t and t not in ('&&','||'):
            conds.append(t)
    return conds

def generate_mcdc_cases(conds):
    # N개의 조건에 대해 MC/DC 케이스(각각 하나만 토글) 생성
    n = len(conds)
    base = [True]*n
    cases = []
    for i in range(n):
        tc1 = base.copy()
        tc2 = base.copy()
        tc1[i] = not tc1[i]
        # 한 조건만 달라진 쌍
        cases.append((tc1, tc2))
    return cases

def gen_gtest_code(func_name, expr, conds, cases, header_relpath):
    code = []
    code.append('#include <gtest/gtest.h>')
    code.append('extern "C" {')
    code.append(f'    #include "{header_relpath}"')
    code.append('}')
    code.append('')
    testname = os.path.splitext(os.path.basename(header_relpath))[0]
    for idx, (c1, c2) in enumerate(cases):
        name = f"MC_DC_{testname}_{idx}"
        code.append(f'TEST({testname}, {name}) {{')
        # 표현식을 구성할 a,b,c 같은 변수 명으로 치환 (매우 단순 가정)
        # 실 사용 시 함수 인자나 전역변수로 호출 예시로 교체 필요
        args1 = ', '.join(str(int(v)) for v in c1)
        args2 = ', '.join(str(int(v)) for v in c2)
        code.append(f'    // Case {idx}: {conds}')
        code.append(f'    EXPECT_NO_FATAL_FAILURE({func_name}({args1}));')
        code.append(f'    EXPECT_NO_FATAL_FAILURE({func_name}({args2}));')
        code.append('}')
        code.append('')
    return '\n'.join(code)

def main():
    root = tk.Tk()
    root.withdraw()
    # .c 파일 선택
    c_path = filedialog.askopenfilename(
        title="테스트케이스를 생성할 .c 파일 선택",
        filetypes=[("C Source", "*.c")])
    if not c_path:
        messagebox.showinfo("취소", "파일 선택이 취소되었습니다.")
        return

    # 같은 폴더에 헤더(.h)와 작동한다고 가정
    header = os.path.splitext(os.path.basename(c_path))[0] + '.h'
    header_path = os.path.join(os.path.dirname(c_path), header)
    if not os.path.isfile(header_path):
        messagebox.showerror("오류", f"헤더 파일을 찾을 수 없습니다:\n{header_path}")
        return

    # 소스코드 읽기
    with open(c_path, 'r') as f:
        code = f.read()

    # 함수 호출 예시 찾아보기 (단순 if 구문 패턴)
    m = re.search(r'\bint\s+(\w+)\s*\([^)]*\)\s*\{[^}]*if\s*\(([^)]+)\)', code, re.DOTALL)
    if not m:
        messagebox.showerror("오류", "MC/DC 생성용 if 문을 찾을 수 없습니다.")
        return

    func_name, expr = m.group(1), m.group(2)
    conds = extract_conditions(expr)
    cases = generate_mcdc_cases(conds)

    # 테스트 코드 생성
    out_dir = os.path.dirname(c_path)
    out_path = os.path.join(out_dir, 'mcdc_tests.cpp')
    header_rel = os.path.relpath(header_path, os.path.dirname(out_path)).replace('\\','/')

    try:
        with open(out_path, 'w') as f:
            f.write(gen_gtest_code(func_name, expr, conds, cases, header_rel))
    except Exception as e:
        messagebox.showerror("오류", f"파일 생성 중 오류:\n{e}")
        return

    messagebox.showinfo("완료", f"MC/DC 테스트 코드가 생성되었습니다:\n{out_path}")

if __name__ == '__main__':
    main()
    # 머고 왜 안올라가
    