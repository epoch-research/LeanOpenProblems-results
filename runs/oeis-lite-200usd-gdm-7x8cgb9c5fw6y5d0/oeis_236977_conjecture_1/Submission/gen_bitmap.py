import math

limit = 2000005
is_prime = [True] * limit
is_prime[0] = is_prime[1] = False
for i in range(2, int(math.isqrt(limit)) + 1):
    if is_prime[i]:
        for j in range(i*i, limit, i):
            is_prime[j] = False

# Construct the bitmap
val = 0
for i in range(limit):
    if is_prime[i]:
        val |= 1 << i

hex_str = f"0x{val:050000x}"
print("Length of hex string:", len(hex_str))

# Write a test Lean file
code = []
code.append("import FormalConjectures.Util.ProblemImports")
code.append("")
code.append("open Nat")
code.append("")
code.append(f"def prime_bitmap : Nat := {hex_str}")
code.append("")
code.append("def is_prime_fast (x : Nat) : Bool :=")
code.append("  if x < 2 then false")
code.append("  else (shiftRight prime_bitmap x) % 2 == 1")
code.append("")
code.append("theorem test_prime_1999993 : is_prime_fast 1999993 = true := by")
code.append("  decide")
code.append("")
code.append("theorem test_prime_1999994 : is_prime_fast 1999994 = false := by")
code.append("  decide")

with open("/workspace/leanproject/Submission/TestBitmapSpeed.lean", "w") as f:
    f.write("\n".join(code))
print("Test file written.")
