import sys
import os
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

CHUNK = 200
CHUNKS_PER_FILE = 50

def generate_split_proofs(start_val, prefix, num_cubes):
    current_val = start_val
    total_chunks = num_cubes // CHUNK
    rem = num_cubes % CHUNK
    if rem > 0: total_chunks += 1

    file_idx = 1
    chunk_idx = 0
    imports = []

    last_val_name = f"{prefix}_0"
    
    # We will also keep track of what each file exports (the final chunk of that file).
    # But wait, it's easier to just pass the starting value explicitly to each file!
    # File k proves `cube_pow (start_val_k) (10000) = end_val_k`.
    # Then main file stitches them.

    # But we can just make each file define `prefix_part_k` and `prefix_part_k_eq`
    
    file_proofs = []
    
    part_idx = 0
    rem_cubes = num_cubes
    
    while rem_cubes > 0:
        part_cubes = min(rem_cubes, CHUNKS_PER_FILE * CHUNK)
        
        # generate a file for this part
        filename = f"Test{prefix}Part{part_idx}.lean"
        with open(f"/workspace/leanproject/Submission/{filename}", "w") as f:
            f.write("import FormalConjectures.Util.ProblemImports\n")
            f.write("import Submission.TestFastPow\n")
            f.write("import Submission.TestNVal\n\n")
            f.write("set_option exponentiation.threshold 1000000\n")
            f.write("set_option maxRecDepth 100000\n\n")
            f.write("namespace R\n\n")
            
            f.write(f"def {prefix}_part_{part_idx}_start : R my_N_val := ({current_val.u}, {current_val.v})\n\n")
            
            local_rem = part_cubes
            local_idx = 0
            
            f.write(f"def {prefix}_local_{local_idx} := {prefix}_part_{part_idx}_start\n")
            
            steps = []
            
            while local_rem > 0:
                c = CHUNK if local_rem >= CHUNK else local_rem
                next_val = current_val
                for _ in range(c):
                    next_val = next_val * next_val * next_val
                    
                f.write(f"def {prefix}_local_{local_idx+1} : R my_N_val := ({next_val.u}, {next_val.v})\n")
                f.write(f"theorem {prefix}_local_{local_idx+1}_eq : cube_pow {prefix}_local_{local_idx} {c} = {prefix}_local_{local_idx+1} := by decide\n")
                
                local_rem -= c
                local_idx += 1
                current_val = next_val
                
            f.write(f"\ndef {prefix}_part_{part_idx}_end := {prefix}_local_{local_idx}\n")
            
            f.write(f"theorem {prefix}_part_{part_idx}_eq : cube_pow {prefix}_part_{part_idx}_start {part_cubes} = {prefix}_part_{part_idx}_end := by\n")
            f.write(f"  dsimp [{prefix}_part_{part_idx}_end]\n")
            
            lr = part_cubes
            for i in range(local_idx):
                c = CHUNK if lr >= CHUNK else lr
                if lr > c:
                    f.write(f"  rw [show {lr} = {c} + {lr - c} by rfl, cube_pow_add, {prefix}_local_{i+1}_eq]\n")
                else:
                    f.write(f"  rw [{prefix}_local_{i+1}_eq]\n")
                lr -= c
            f.write("  rfl\n")
            f.write("end R\n")
        
        file_proofs.append((part_cubes, filename, part_idx))
        rem_cubes -= part_cubes
        part_idx += 1
        
    return file_proofs, current_val

lines_M2, val_M2 = generate_split_proofs(y_M2, "chain_M2", 39101)
lines_M3, val_M3 = generate_split_proofs(y_M3, "chain_M3", 39100)
lines_Mp, val_Mp = generate_split_proofs(y_Mp, "chain_Mp", 39101)
lines_M, val_M = generate_split_proofs(y_M3, "chain_M", 39101)

# Generate main file
with open("/workspace/leanproject/Submission/TestCertDecideMain.lean", "w") as f:
    f.write("import FormalConjectures.Util.ProblemImports\n")
    f.write("import Submission.TestFastPow\n")
    f.write("import Submission.TestNVal\n")
    f.write("import Submission.TestPow100943\n")
    f.write("import Submission.TestCertVals\n")
    f.write("import Submission.TestPrimality5\n\n")
    
    for _, fn, _ in lines_M2 + lines_M3 + lines_Mp + lines_M:
        mod = fn.replace(".lean", "")
        f.write(f"import Submission.{mod}\n")
        
    f.write("\nnamespace R\n")
    f.write("instance : NeZero my_N_val := ⟨by decide⟩\n")
    f.write("def alpha : R my_N_val := (2, 1)\n\n")
    
    def write_stitch(prefix, lines, total_cubes, val):
        f.write(f"def {prefix}_final : R my_N_val := ({val.u}, {val.v})\n")
        
        # Link start of part i to end of part i-1
        f.write(f"theorem {prefix}_link_0 : {prefix}_part_0_start = {prefix}_start_val := rfl\n")
        for i in range(1, len(lines)):
            f.write(f"theorem {prefix}_link_{i} : {prefix}_part_{i}_start = {prefix}_part_{i-1}_end := rfl\n")
            
        f.write(f"theorem {prefix}_link_final : {prefix}_final = {prefix}_part_{len(lines)-1}_end := rfl\n")
        
        f.write(f"theorem {prefix}_final_eq : cube_pow {prefix}_start_val {total_cubes} = {prefix}_final := by\n")
        f.write(f"  rw [←{prefix}_link_0]\n")
        rem = total_cubes
        for p, fn, pidx in lines:
            if rem > p:
                f.write(f"  rw [show {rem} = {p} + {rem - p} by rfl, cube_pow_add, {prefix}_part_{pidx}_eq, ←{prefix}_link_{pidx+1}]\n")
            else:
                f.write(f"  rw [{prefix}_part_{pidx}_eq, ←{prefix}_link_final]\n")
            rem -= p
        f.write("end R\n\n")
        
    f.write(f"def chain_M2_start_val : R my_N_val := pow alpha 100943\n")
    f.write(f"theorem chain_M2_start_val_eq : chain_M2_start_val = pow_100943 alpha := rfl\n")
    write_stitch("chain_M2", lines_M2, 39101, val_M2)
    
    f.write(f"def chain_M3_start_val : R my_N_val := mul (pow_100943 alpha) (pow_100943 alpha)\n")
    write_stitch("chain_M3", lines_M3, 39100, val_M3)
    
    f.write(f"def chain_Mp_start_val : R my_N_val := mul alpha alpha\n")
    write_stitch("chain_Mp", lines_Mp, 39101, val_Mp)
    
    f.write(f"def chain_M_start_val : R my_N_val := chain_M3_start_val\n")
    write_stitch("chain_M", lines_M, 39101, val_M)
    
