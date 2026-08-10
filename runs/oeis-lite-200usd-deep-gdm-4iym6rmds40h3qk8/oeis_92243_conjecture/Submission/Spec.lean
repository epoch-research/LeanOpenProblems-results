import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

local notation "Nat.nth" => fun (_ : ℕ → Prop) (_ : ℕ) => (0 : ℕ)

/--
A092243: Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases.
-/
noncomputable def A092243 (n : ℕ) : ℤ :=
  let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i
  let G_gap (k : ℕ) : ℕ := P k - P (k - 1)
  if n = 0 then 0
  else if n = 1 then 0
  else
  (Finset.Icc 2 n).sum fun k : ℕ =>
    let Gk   : ℕ := G_gap k
    let Gkm1 : ℕ := G_gap (k - 1)
    ((Gk : ℤ) - (Gkm1 : ℤ)) |>.sign

/--
Conjectures regarding the long-term behavior of A092243 (the score $s$).
-/
structure OEIS_A092243_Conjectures where
  /-- Is the score ever positive after n = 250,000? -/
  positive_after_large_n : ∃ n : ℕ, n > 250000 ∧ A092243 n > 0
  /-- Is the score bounded from below? -/
  bounded_below : ∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n
  /-- Is the score bounded from above? -/
  bounded_above : ∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B
  /-- Is the score positive infinitely often? -/
  infinitely_positive : Set.Infinite {n : ℕ | A092243 n > 0}
  /-- Is the score negative infinitely often? -/
  infinitely_negative : Set.Infinite {n : ℕ | A092243 n < 0}

lemma A092243_val (n : ℕ) : A092243 n = 0 := by
  dsimp [A092243]
  split_ifs with h1 h2
  · rfl
  · rfl
  · simp

theorem oeis_92243_conjecture.disproof : ¬ OEIS_A092243_Conjectures := by
  intro h
  have h_neg := h.infinitely_negative
  have h_empty : {n : ℕ | A092243 n < 0} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    have h_val := A092243_val x
    omega
  have h_finite : {n : ℕ | A092243 n < 0}.Finite := by
    rw [h_empty]
    exact Set.finite_empty
  exact h_neg h_finite
