import sys
sys.set_int_max_str_digits(1000000)
from flint import fmpz

N = fmpz(2 * 100943 * 3**39101 - 1)

class R:
    def __init__(self, u, v):
        self.u = u % N
        self.v = v % N
    def __mul__(self, other):
        return R(self.u * other.u + fmpz(3) * self.v * other.v, self.u * other.v + self.v * other.u)

def power(a, n):
    res = R(fmpz(1), fmpz(0))
    b = bin(n)[2:]
    for bit in b:
        res = res * res
        if bit == '1':
            res = res * a
    return res

alpha = R(fmpz(2), fmpz(1))
y_M2 = power(alpha, 100943)
y_M3 = power(alpha, 2 * 100943)
y_Mp = power(alpha, 2)

def gen_cubings(start_val, prefix, num_cubes):
    lines = []
    current_val = start_val
    lines.append(f"def {prefix}_0 : R my_N_val := ({current_val.u}, {current_val.v})")
    
    CHUNK = 200
    chunks = num_cubes // CHUNK
    rem = num_cubes % CHUNK
    
    for i in range(chunks):
        next_val = current_val
        for _ in range(CHUNK):
            next_val = next_val * next_val * next_val
        lines.append(f"def {prefix}_{i+1} : R my_N_val := ({next_val.u}, {next_val.v})")
        lines.append(f"theorem {prefix}_{i+1}_eq : cube_pow {prefix}_{i} {CHUNK} = {prefix}_{i+1} := by decide")
        current_val = next_val
        
    if rem > 0:
        next_val = current_val
        for _ in range(rem):
            next_val = next_val * next_val * next_val
        lines.append(f"def {prefix}_{chunks+1} : R my_N_val := ({next_val.u}, {next_val.v})")
        lines.append(f"theorem {prefix}_{chunks+1}_eq : cube_pow {prefix}_{chunks} {rem} = {prefix}_{chunks+1} := by decide")
        current_val = next_val
        chunks += 1
        
    lines.append(f"def {prefix}_final := {prefix}_{chunks}")
    
    proof_steps = []
    proof_steps.append(f"theorem {prefix}_final_eq : cube_pow {prefix}_0 {num_cubes} = {prefix}_final := by")
    proof_steps.append(f"  dsimp [{prefix}_final]")
    
    rem_cubes = num_cubes
    for i in range(chunks):
        c = CHUNK if i < chunks - 1 or rem == 0 else rem
        if rem_cubes > c:
            proof_steps.append(f"  rw [show {rem_cubes} = {c} + {rem_cubes - c} by rfl, cube_pow_add, {prefix}_{i+1}_eq]")
        else:
            proof_steps.append(f"  rw [{prefix}_{i+1}_eq]")
        rem_cubes -= c
    proof_steps.append("  rfl")
    
    lines.extend(proof_steps)
    return lines, current_val

with open("/workspace/leanproject/Submission/TestCertDecide.lean", "w") as f:
    f.write("import FormalConjectures.Util.ProblemImports\n")
    f.write("import Submission.TestFastPow\n")
    f.write("import Submission.TestPow100943\n")
    f.write("import Submission.TestCertVals\n")
    f.write("import Submission.TestPrimality5\n")
    f.write("import Submission.TestNVal\n\n")
    f.write("set_option exponentiation.threshold 1000000\n")
    f.write("set_option maxRecDepth 100000\n\n")
    f.write("namespace R\n\n")
    f.write("instance : NeZero my_N_val := ⟨by decide⟩\n")
    f.write("def alpha : R my_N_val := (2, 1)\n\n")
    
    lines_M2, val_M2 = gen_cubings(y_M2, "chain_M2", 39101)
    f.write("\n".join(lines_M2) + "\n\n")
    
    lines_M3, val_M3 = gen_cubings(y_M3, "chain_M3", 39100)
    f.write("\n".join(lines_M3) + "\n\n")
    
    lines_Mp, val_Mp = gen_cubings(y_Mp, "chain_Mp", 39101)
    f.write("\n".join(lines_Mp) + "\n\n")
    
    lines_M, val_M = gen_cubings(y_M3, "chain_M", 39101)
    f.write("\n".join(lines_M) + "\n\n")
    f.write("end R\n")
