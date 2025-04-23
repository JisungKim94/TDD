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
        # 실 사용 시 함수 인자나 전역
