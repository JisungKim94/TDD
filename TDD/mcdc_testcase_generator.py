# GoogleTest 코드 생성에서 EXPECT_EQ 순서 변경: EXPECT_EQ(expected, actual)

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
