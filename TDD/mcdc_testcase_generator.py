import os
import re
import tkinter as tk
from tkinter import filedialog, messagebox

def extract_conditions(expr):
    tokens = re.split(r'(\|\||&&)', expr)
    conds = [t.strip() for t in tokens if t.strip() and t not in ('&&', '||')]
    return conds

def generate_mcdc_cases(conds):
    n = len(conds)
    base = [True] * n
    cases = []
    for i in range(n):
        tc1 = base.copy()
        tc2 = base.copy()
        tc1[i] = not tc1[i]
        cases.append((tc1, tc2))
    return cases

def gen_gtest_code(func_name, conds, cases, header_relpath):
    code = []
    code.append('#include <gtest/gtest.h>')
    code.append('extern "C" {')
    code.append(f'    #include "{header_relpath}"')
    code.append('}')
    code.append('')
    testname = os.path.splitext(os.path.basename(header_relpath))[0]
    for idx, (c1, c2) in enumerate(cases):
        code.append(f'TEST({testname}, MC_DC_Case{idx}) {{')
        args1 = ', '.join(str(int(v)) for v in c1)
        args2 = ', '.join(str(int(v)) for v in c2)
        code.append(f'    EXPECT_EQ({func_name}({args1}), /* expected1 */);')
        code.append(f'    EXPECT_EQ({func_name}({args2}), /* expected2 */);')
        code.append('}')
        code.append('')
    return '\n'.join(code)

def main():
    root = tk.Tk()
    root.withdraw()
    c_path = filedialog.askopenfilename(
        title="MC/DC 케이스 생성할 C 소스(.c) 선택",
        filetypes=[("C Source", "*.c")])
    if not c_path:
        messagebox.showinfo("취소", "파일 선택이 취소되었습니다.")
        return

    # 프로젝트 루트는 src 폴더의 상위 디렉토리
    project_root = os.path.dirname(os.path.dirname(c_path))
    # 헤더는 include 폴더 안
    header_name = os.path.splitext(os.path.basename(c_path))[0] + '.h'
    header_path = os.path.join(project_root, 'include', header_name)
    if not os.path.isfile(header_path):
        messagebox.showerror("오류", f"헤더 파일을 찾을 수 없습니다:\n{header_path}")
        return

    with open(c_path, 'r') as f:
        code = f.read()

    # 함수명과 if 조건문 추출 (단순화)
    m = re.search(r'\bint\s+(\w+)\s*\([^)]*\)\s*\{[^}]*if\s*\(([^)]+)\)', code, re.DOTALL)
    if not m:
        messagebox.showerror("오류", "if 조건문을 찾을 수 없습니다.")
        return

    func_name, expr = m.group(1), m.group(2)
    conds = extract_conditions(expr)
    cases = generate_mcdc_cases(conds)

    # 출력 파일은 test 폴더에 생성
    test_dir = os.path.join(project_root, 'test')
    if not os.path.isdir(test_dir):
        os.makedirs(test_dir)
    out_path = os.path.join(test_dir, 'mcdc_tests.cpp')
    header_relpath = os.path.relpath(header_path, test_dir).replace('\\', '/')

    try:
        with open(out_path, 'w') as f:
            f.write(gen_gtest_code(func_name, conds, cases, header_relpath))
    except Exception as e:
        messagebox.showerror("오류", f"파일 생성 실패:\n{e}")
        return

    messagebox.showinfo("완료", f"테스트 코드 생성 완료:\n{out_path}")

if __name__ == '__main__':
    main()

