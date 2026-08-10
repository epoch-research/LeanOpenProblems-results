import FormalConjectures.Util.ProblemImports
open Set
open Nat
noncomputable def A055487 (n : ℕ) : ℕ :=
  sInf {m : ℕ | Nat.totient m = Nat.factorial n}
theorem a4 : A055487 4 = 35 := by
  unfold A055487
  apply le_antisymm
  · apply Nat.sInf_le
    decide
  · by_contra hlt
    have hs : sInf {m : ℕ | Nat.totient m = Nat.factorial 4} < 35 := Nat.lt_of_not_ge hlt
    have hmem : Nat.totient (sInf {m : ℕ | Nat.totient m = Nat.factorial 4}) = Nat.factorial 4 := by
      exact Nat.sInf_mem (s := {m : ℕ | Nat.totient m = Nat.factorial 4}) ⟨35, by decide⟩
    interval_cases sInf {m : ℕ | Nat.totient m = Nat.factorial 4} <;> revert hmem <;> decide
#print axioms a4
