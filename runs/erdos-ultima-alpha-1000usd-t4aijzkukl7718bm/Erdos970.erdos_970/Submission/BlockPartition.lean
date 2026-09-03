import Submission.BlockSieveBound

/-! A doubly dyadic partition of an arbitrary finite set of primes. -/
namespace Erdos970.BlockSieve
open Erdos970.BrunCriterion

/-- The final block includes the entire remaining tail. -/
def primeBlock (P : Finset ℕ) (J : ℕ) (j : Fin (J + 1)) : Finset ℕ :=
  P.filter (fun p => min (Nat.log 2 (Nat.log 2 p)) J = j.val)

theorem primeBlock_subset (P : Finset ℕ) (J : ℕ) (j : Fin (J + 1)) :
    primeBlock P J j ⊆ P := Finset.filter_subset _ _

theorem primeBlock_union (P : Finset ℕ) (J : ℕ) :
    Finset.univ.biUnion (primeBlock P J) = P := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact primeBlock_subset P J j hj
  · intro hp
    exact ⟨⟨min (Nat.log 2 (Nat.log 2 p)) J,
      Nat.lt_succ_of_le (min_le_right _ _)⟩, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩

theorem primeBlock_disjoint (P : Finset ℕ) (J : ℕ) :
    Pairwise (fun i j => Disjoint (primeBlock P J i) (primeBlock P J j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  apply hij
  exact Fin.ext ((Finset.mem_filter.mp hpi).2.symm.trans (Finset.mem_filter.mp hpj).2)

theorem primeBlock_log_bounds (P : Finset ℕ) (J : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (j : Fin (J + 1)) (hj : j.val < J)
    {p : ℕ} (hp : p ∈ primeBlock P J j) :
    2 ^ j.val ≤ Nat.log 2 p ∧ Nat.log 2 p < 2 ^ (j.val + 1) := by
  have hpP := primeBlock_subset P J j hp
  have hplog : 0 < Nat.log 2 p := Nat.log_pos (by decide) (hP p hpP).two_le
  have hmin := (Finset.mem_filter.mp hp).2
  have heq : Nat.log 2 (Nat.log 2 p) = j.val := by omega
  exact (Nat.log_eq_iff (Or.inr ⟨by decide, hplog.ne'⟩)).mp heq

/-- Every nonfinal block has reciprocal mass at most four. -/
theorem primeBlock_mass_small (P : Finset ℕ) (J : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (j : Fin (J + 1)) (hj : j.val < J) :
    (∑ p ∈ primeBlock P J j, (1 : ℝ) / p) ≤ 4 := by
  classical
  let A := primeBlock P J j
  let lo := 2 ^ j.val
  let hi := 2 ^ (j.val + 1)
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hmap : ∀ p ∈ A, Nat.log 2 p ∈ Finset.Ico lo hi := by
    intro p hp
    exact Finset.mem_Ico.mpr (primeBlock_log_bounds P J hP j hj hp)
  calc
    _ = ∑ l ∈ Finset.Ico lo hi, ∑ p ∈ A.filter (fun p => Nat.log 2 p = l), (1 : ℝ) / p :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ l ∈ Finset.Ico lo hi, 4 / (l : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      have hlpos : 0 < l := hlo.trans_le (Finset.mem_Ico.mp hl).1
      apply le_trans _ (dyadic_reciprocal_sum_le l hlpos)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpA, heq⟩ := Finset.mem_filter.mp hp
        have hpprime := hP p (primeBlock_subset P J j hpA)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
          ((Nat.log_eq_iff (Or.inl hlpos.ne')).mp heq), hpprime⟩
      · intro p hp hnot
        positivity
    _ ≤ ∑ l ∈ Finset.Ico lo hi, 4 / (lo : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hlo)
        (by exact_mod_cast (Finset.mem_Ico.mp hl).1)
    _ = 4 := by
      have hhi : hi = 2 * lo := by dsimp [hi, lo]; rw [pow_succ]; omega
      have hcard : (Finset.Ico lo hi).card = lo := by simp [hhi]; omega
      simp only [Finset.sum_const, hcard, nsmul_eq_mul]
      have hloR : (lo : ℝ) ≠ 0 := by exact_mod_cast hlo.ne'
      field_simp

/-- If the final cutoff exceeds the cardinality budget, the final mass is at most one. -/
theorem primeBlock_mass_last (P : Finset ℕ) (J k : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcard : P.card ≤ k) (hcut : k + 1 ≤ 2 ^ (2 ^ J)) :
    (∑ p ∈ primeBlock P J (Fin.last J), (1 : ℝ) / p) ≤ 1 := by
  have hbig (p : ℕ) (hp : p ∈ primeBlock P J (Fin.last J)) : k + 1 ≤ p := by
    have hpprime := hP p (primeBlock_subset P J (Fin.last J) hp)
    have hplog : 0 < Nat.log 2 p := Nat.log_pos (by decide) hpprime.two_le
    have hmin := (Finset.mem_filter.mp hp).2
    have hJ : J ≤ Nat.log 2 (Nat.log 2 p) := by
      simpa only [Fin.val_last, min_eq_right_iff] using hmin
    have hlo : 2 ^ J ≤ Nat.log 2 p := Nat.pow_le_of_le_log hplog.ne' hJ
    exact hcut.trans (Nat.pow_le_of_le_log hpprime.ne_zero hlo)
  calc
    _ ≤ ∑ p ∈ primeBlock P J (Fin.last J), 1 / ((k : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hbig p hp)
    _ = ((primeBlock P J (Fin.last J)).card : ℝ) / ((k : ℝ) + 1) := by
      simp [div_eq_mul_inv]
    _ ≤ 1 := by
      apply (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
      have hh := (Finset.card_le_card (primeBlock_subset P J (Fin.last J))).trans hcard
      exact_mod_cast hh.trans (Nat.le_succ k)

theorem primeBlock_card_bound (P : Finset ℕ) (J k : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcard : P.card ≤ k)
    (hcut : k + 1 ≤ 2 ^ (2 ^ J)) (j : Fin (J + 1)) :
    (primeBlock P J j).card + 1 ≤ 2 ^ (2 ^ (j.val + 1)) := by
  by_cases hj : j.val < J
  · have hsub : primeBlock P J j ⊆ Finset.Ico 1 (2 ^ (2 ^ (j.val + 1))) := by
      intro p hp
      have hpprime := hP p (primeBlock_subset P J j hp)
      refine Finset.mem_Ico.mpr ⟨hpprime.one_le, ?_⟩
      exact Nat.lt_pow_of_log_lt (by decide) (primeBlock_log_bounds P J hP j hj hp).2
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at hc
    have hpos : 0 < 2 ^ (2 ^ (j.val + 1)) := by positivity
    omega
  · have hjJ : j.val = J := by omega
    have hc := (Finset.card_le_card (primeBlock_subset P J j)).trans hcard
    calc
      _ ≤ k + 1 := Nat.add_le_add_right hc 1
      _ ≤ 2 ^ (2 ^ J) := hcut
      _ ≤ _ := by rw [hjJ]; gcongr <;> omega

#print axioms primeBlock_card_bound
#print axioms primeBlock_mass_small
#print axioms primeBlock_mass_last
end Erdos970.BlockSieve
