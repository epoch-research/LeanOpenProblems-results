import sys

def gen_pow(n):
    lines = []
    b = bin(n)[2:]
    
    current = 1
    thms = []
    for bit in b[1:]:
        new_val = current * 2
        lines.append(f"def pow_{new_val} {{n_p}} (x : R n_p) : R n_p := mul (pow_{current} x) (pow_{current} x)")
        thms.append(f"theorem pow_{new_val}_eq {{n_p}} (x : R n_p) : pow_{new_val} x = pow x {new_val} := by\n  dsimp [pow_{new_val}]\n  rw [pow_{current}_eq, ←pow_add]")
        current = new_val
        
        if bit == '1':
            new_val = current + 1
            lines.append(f"def pow_{new_val} {{n_p}} (x : R n_p) : R n_p := mul (pow_{current} x) x")
            thms.append(f"theorem pow_{new_val}_eq {{n_p}} (x : R n_p) : pow_{new_val} x = pow x {new_val} := by\n  dsimp [pow_{new_val}]\n  rw [pow_{current}_eq]\n  rfl")
            current = new_val
            
    print("import FormalConjectures.Util.ProblemImports\nimport Submission.TestFastPow\nnamespace R\ndef pow_1 {n_p} (x : R n_p) := x")
    print("theorem pow_1_eq {n_p} (x : R n_p) : pow_1 x = pow x 1 := by simp [pow_1, pow]")
    for l in lines:
        print(l)
    for t in thms:
        print(t)
    print("end R")

gen_pow(100943)
