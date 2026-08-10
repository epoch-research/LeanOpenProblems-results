import FormalConjectures.Util.ProblemImports

open Finset Nat Set

#check Finset.lcm_dvd

lemma lcm_dvd_of_subset_divisors {D : Finset ℕ} {m : ℕ} (hD : D ⊆ divisors m) :
    D.lcm id ∣ m := by
  apply Finset.lcm_dvd
  intro b hb
  have h_b_div := hD hb
  exact Nat.dvd_of_mem_divisors h_b_div

def P_a08 (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m

lemma P_a08_eq (n m : ℕ) :
  (0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m) ↔ P_a08 n m := by
  unfold P_a08
  simp only [Finset.mem_powerset]

noncomputable def a081512 (n : ℕ) : ℕ :=
  sInf { m : ℕ | P_a08 n m }

def P_a (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m ∧ D.lcm id = m

lemma P_a_eq (n m : ℕ) :
  (0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m) ↔ P_a n m := by
  unfold P_a
  simp only [Finset.mem_powerset]

noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | P_a n m }

lemma helper (k : ℕ) (m : ℕ) (hm : P_a08 k m) : ∃ m' ≤ m, P_a k m' := by
  induction' m using Nat.strong_induction_on with m ih
  rcases hm with ⟨h_pos, D, hD, hcard, hsum⟩
  rw [Finset.mem_powerset] at hD
  let L := D.lcm id
  have hL_dvd : L ∣ m := lcm_dvd_of_subset_divisors hD
  have hL_le : L ≤ m := Nat.le_of_dvd h_pos hL_dvd
  by_cases hL : L = m
  · use m
    refine ⟨le_rfl, ?_⟩
    rw [← P_a_eq]
    exact ⟨h_pos, D, hD, hcard, hsum, hL⟩
  · have hL_lt : L < m := lt_of_le_of_ne hL_le hL
    sorry



