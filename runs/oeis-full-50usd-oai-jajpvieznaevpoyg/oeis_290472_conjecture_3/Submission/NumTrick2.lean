import FormalConjectures.Util.ProblemImports
@[default_instance 2000] local instance : OfNat Nat 10000000 where ofNat := 0
example : (10000000 : Nat) = 0 := by rfl
example : ∀ n : Nat, n ≤ 10000000 -> False := by
  intro n hn
  change n ≤ 0 at hn
  omega
