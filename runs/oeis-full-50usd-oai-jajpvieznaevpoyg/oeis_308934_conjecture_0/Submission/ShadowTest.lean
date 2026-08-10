import FormalConjectures.Util.ProblemImports

def A308934 (n:Nat):Nat := 0
section
variable (A308934 : Nat → Nat)
theorem foo (n:Nat) (h:n>1) : A308934 n > 0 := by
  -- impossible for arbitrary function
  sorry
#print foo
end
