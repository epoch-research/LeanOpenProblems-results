import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 10000
set_option maxRecDepth 1000000


open Nat Finset

example (hp : Nat.Prime ((11 + 1) ^ (Nat.totient (1408 - 11) / 2) - 11)) : False := by
  have ht : Nat.totient (1408 - 11) = 1260 := by native_decide
  rw [ht] at hp
  norm_num at hp
  let N : ℕ := 12 ^ 630 - 11
  change Nat.Prime N at hp
  have h2 : (2 : ZMod N) ≠ 0 := by native_decide
  letI : Fact (Nat.Prime N) := ⟨hp⟩
  have hfer : (2 : ZMod N) ^ (N - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  have hnot : (2 : ZMod N) ^ (N - 1) ≠ 1 := by native_decide
  exact hnot hfer
