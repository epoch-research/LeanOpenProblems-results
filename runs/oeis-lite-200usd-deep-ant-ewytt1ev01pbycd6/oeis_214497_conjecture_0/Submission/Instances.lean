import FormalConjectures.Util.ProblemImports

open Nat

/-!
# Verified instances of the A214497 conjecture

These are fully formal, `sorry`-free witnesses showing that the existence
statement of `oeis_214497_conjecture_0` holds for specific small `n`.  They
document that the conjecture is *true wherever it can be checked* (consistent
with computation up to `n = 200`), even though the universal statement over all
`n` is twin-prime-hard and hence not provable from current mathematics
(see `Submission/Implication.lean`).

Each instance exhibits a witness `k` and proves both `(3^n - k)·2^n ± 1` prime.
-/

/-- `n = 1`, witness `k = 0`: the twin primes are `5, 7`. -/
theorem A214497_inst_1 :
    ∃ k : ℕ, Nat.Prime ((3 ^ 1 - k) * (2 ^ 1) - 1) ∧ Nat.Prime ((3 ^ 1 - k) * (2 ^ 1) + 1) :=
  ⟨0, by norm_num, by norm_num⟩

/-- `n = 2`, witness `k = 6`: the twin primes are `11, 13`. -/
theorem A214497_inst_2 :
    ∃ k : ℕ, Nat.Prime ((3 ^ 2 - k) * (2 ^ 2) - 1) ∧ Nat.Prime ((3 ^ 2 - k) * (2 ^ 2) + 1) :=
  ⟨6, by norm_num, by norm_num⟩

/-- `n = 3`, witness `k = 3`: the twin primes are `191, 193`. -/
theorem A214497_inst_3 :
    ∃ k : ℕ, Nat.Prime ((3 ^ 3 - k) * (2 ^ 3) - 1) ∧ Nat.Prime ((3 ^ 3 - k) * (2 ^ 3) + 1) :=
  ⟨3, by norm_num, by norm_num⟩

/-- `n = 4`, witness `k = 9`: the twin primes are `1151, 1153`. -/
theorem A214497_inst_4 :
    ∃ k : ℕ, Nat.Prime ((3 ^ 4 - k) * (2 ^ 4) - 1) ∧ Nat.Prime ((3 ^ 4 - k) * (2 ^ 4) + 1) :=
  ⟨9, by norm_num, by norm_num⟩

/-- `n = 5`, witness `k = 9`: the twin primes are `7487, 7489`. -/
theorem A214497_inst_5 :
    ∃ k : ℕ, Nat.Prime ((3 ^ 5 - k) * (2 ^ 5) - 1) ∧ Nat.Prime ((3 ^ 5 - k) * (2 ^ 5) + 1) :=
  ⟨9, by norm_num, by norm_num⟩

/-- `n = 6`, witness `k = 6`: the twin primes are `46271, 46273`. -/
theorem A214497_inst_6 :
    ∃ k : ℕ, Nat.Prime ((3 ^ 6 - k) * (2 ^ 6) - 1) ∧ Nat.Prime ((3 ^ 6 - k) * (2 ^ 6) + 1) :=
  ⟨6, by norm_num, by norm_num⟩
