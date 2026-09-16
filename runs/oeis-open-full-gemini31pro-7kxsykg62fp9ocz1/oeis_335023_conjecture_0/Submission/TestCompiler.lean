import Mathlib

def A : ℕ := 10^1000000 + 3
def B : ℕ := 10^1000000 + 7
def C : ℕ := A * B

theorem huge_mult : A * B = C := by rfl
