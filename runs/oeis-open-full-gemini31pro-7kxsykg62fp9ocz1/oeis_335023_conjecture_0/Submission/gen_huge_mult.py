import sys
import gmpy2
sys.set_int_max_str_digits(20000000)
gmpy2.get_context().precision = 20000000

print("Generating A and B...")
A = gmpy2.mpz(3) ** 1000000
B = gmpy2.mpz(5) ** 1000000
print("Multiplying...")
C = A * B

print("Writing lean file...")
with open("/workspace/leanproject/Submission/TestHugeMult.lean", "w") as f:
    f.write(f"""import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 2000000

def A : ℤ := {A}
def B : ℤ := {B}
def C : ℤ := {C}

theorem test : A * B = C := by decide
""")
print("Done.")
