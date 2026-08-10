import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 500000

open Finset Nat Set

-- Let's define the predicate for a081512:
def P_a08 (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m

lemma P_a08_eq (n m : ℕ) :
  (0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m) ↔ P_a08 n m := by
  unfold P_a08
  simp only [Finset.mem_powerset]

instance (n m : ℕ) : Decidable (P_a08 n m) := by
  unfold P_a08
  infer_instance

noncomputable def a081512_local (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m }
  sInf candidates

lemma a081512_local_def_eq (n : ℕ) :
  a081512_local n = sInf { m : ℕ | P_a08 n m } := by
  unfold a081512_local
  simp_rw [P_a08_eq]

lemma a081512_local_four : a081512_local 4 = 12 := by
  have h1 : a081512_local 4 ≤ 12 := by
    rw [a081512_local_def_eq]
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 12 ≤ a081512_local 4 := by
    rw [a081512_local_def_eq]
    by_contra! h
    have h_nonempty : { m : ℕ | P_a08 4 m }.Nonempty := by
      use 12
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 12, ¬ P_a08 4 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a08 4 m } ∈ Finset.range 12 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a08 4 m }) h_in_range h_mem
  omega

lemma a081512_local_five : a081512_local 5 = 24 := by
  have h1 : a081512_local 5 ≤ 24 := by
    rw [a081512_local_def_eq]
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 24 ≤ a081512_local 5 := by
    rw [a081512_local_def_eq]
    by_contra! h
    have h_nonempty : { m : ℕ | P_a08 5 m }.Nonempty := by
      use 24
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 24, ¬ P_a08 5 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a08 5 m } ∈ Finset.range 24 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a08 5 m }) h_in_range h_mem
  omega

-- Now let's define the predicate for a:
def P_a (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m ∧ D.lcm id = m

lemma P_a_eq (n m : ℕ) :
  (0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m) ↔ P_a n m := by
  unfold P_a
  simp only [Finset.mem_powerset]

instance (n m : ℕ) : Decidable (P_a n m) := by
  unfold P_a
  infer_instance

noncomputable def a_local (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m ∧
        D.lcm id = m }
  sInf candidates

lemma a_local_def_eq (n : ℕ) :
  a_local n = sInf { m : ℕ | P_a n m } := by
  unfold a_local
  simp_rw [P_a_eq]

lemma a_local_four : a_local 4 = 18 := by
  have h1 : a_local 4 ≤ 18 := by
    rw [a_local_def_eq]
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 18 ≤ a_local 4 := by
    rw [a_local_def_eq]
    by_contra! h
    have h_nonempty : { m : ℕ | P_a 4 m }.Nonempty := by
      use 18
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 18, ¬ P_a 4 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a 4 m } ∈ Finset.range 18 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a 4 m }) h_in_range h_mem
  omega

lemma a_local_five : a_local 5 = 28 := by
  have h1 : a_local 5 ≤ 28 := by
    rw [a_local_def_eq]
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 28 ≤ a_local 5 := by
    rw [a_local_def_eq]
    by_contra! h
    have h_nonempty : { m : ℕ | P_a 5 m }.Nonempty := by
      use 28
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 28, ¬ P_a 5 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a 5 m } ∈ Finset.range 28 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a 5 m }) h_in_range h_mem
  omega




