import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def A : ℤ := 12345678901234567890
def B : ℤ := 98765432109876543210
def C : ℤ := 1219326311370217952237463801111263526900

theorem test : A * B = C := rfl
