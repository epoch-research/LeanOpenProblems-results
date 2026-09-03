import Submission.BrunCriterion

/-! Shared-modulus residue counts have coupled errors. In particular, a zero-sum
coefficient family pays at most half its L1 cost, and the counts of two residue
classes differ by at most one. These are uniform arithmetic statements. -/
namespace Erdos970.BrunCriterion
open Finset
variable {ι : Type*} [Fintype ι]

lemma count_band_center_error (c n : ι → ℝ) (B : ℝ)
    (hn : ∀ i, B ≤ n i ∧ n i ≤ B+1) :
    |∑ i, c i * (n i - (B+1/2))| ≤ (1/2 : ℝ) * ∑ i, |c i| := by
  classical
  calc
    _ ≤ ∑ i, |c i * (n i - (B+1/2))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * (1/2 : ℝ) := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_le]
      constructor <;> linarith [(hn i).1, (hn i).2]
    _ = _ := by rw [← sum_mul, mul_comm]

/-- A common interval of width one yields a sharper error than bounding each
coordinate separately. -/
theorem count_band_error (c n : ι → ℝ) (B x : ℝ)
    (hn : ∀ i, B ≤ n i ∧ n i ≤ B+1) (hx : B ≤ x ∧ x ≤ B+1) :
    |(∑ i, c i * n i) - x * ∑ i, c i| ≤
      (1/2 : ℝ) * ((∑ i, |c i|) + |∑ i, c i|) := by
  classical
  have he : (∑ i, c i * n i) - x * ∑ i, c i =
      (∑ i, c i * (n i - (B+1/2))) + (B+1/2-x) * ∑ i, c i := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hc := count_band_center_error c n B hn
  have hb : |B+1/2-x| ≤ (1/2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  rw [abs_mul]
  have ht := mul_le_mul_of_nonneg_right hb (abs_nonneg (∑ i, c i))
  linarith

noncomputable def residueCount (m d r : ℕ) : ℕ :=
  ((range m).filter (fun j => j ≡ r [MOD d])).card

lemma residueCount_band (m d r : ℕ) (hd : 0 < d) :
    m/d ≤ residueCount m d r ∧ residueCount m d r ≤ m/d+1 := by
  classical
  rw [residueCount, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card m hd r]
  split_ifs <;> omega

/-- The reference count m/d and every residue count lie in the same unit band. -/
theorem residue_family_error (m d : ℕ) (hd : 0 < d) (r : ι → ℕ) (c : ι → ℝ) :
    |(∑ i, c i * residueCount m d (r i)) - (m : ℝ)/d * ∑ i, c i| ≤
      (1/2 : ℝ) * ((∑ i, |c i|) + |∑ i, c i|) := by
  have hn (i : ι) : (m/d : ℕ) ≤ residueCount m d (r i) ∧
      residueCount m d (r i) ≤ m/d+1 := residueCount_band m d (r i) hd
  apply count_band_error c (fun i => (residueCount m d (r i) : ℝ)) (m/d : ℕ)
  · intro i
    exact ⟨by exact_mod_cast (hn i).1, by exact_mod_cast (hn i).2⟩
  · have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    constructor
    · apply (le_div_iff₀ hdR).mpr
      exact_mod_cast Nat.div_mul_le_self m d
    · apply (div_le_iff₀ hdR).mpr
      exact_mod_cast (show m ≤ (m/d+1)*d by simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ m hd).le)

theorem residue_balanced_error (m d : ℕ) (hd : 0 < d) (r : ι → ℕ) (c : ι → ℝ)
    (hc : (∑ i, c i) = 0) :
    |∑ i, c i * residueCount m d (r i)| ≤ (1/2 : ℝ) * ∑ i, |c i| := by
  simpa only [hc, mul_zero, sub_zero, abs_zero, add_zero] using residue_family_error m d hd r c

/-- In particular, subtracting two same-modulus residue counts costs one, not two. -/
theorem residue_count_pair_error (m d r s : ℕ) (hd : 0 < d) :
    |(residueCount m d r : ℝ) - residueCount m d s| ≤ 1 := by
  obtain ⟨hrl, hru⟩ := residueCount_band m d r hd
  obtain ⟨hsl, hsu⟩ := residueCount_band m d s hd
  have hr : (residueCount m d r : ℝ) ≤ residueCount m d s + 1 := by
    exact_mod_cast (show residueCount m d r ≤ residueCount m d s + 1 by omega)
  have hs : (residueCount m d s : ℝ) ≤ residueCount m d r + 1 := by
    exact_mod_cast (show residueCount m d s ≤ residueCount m d r + 1 by omega)
  rw [abs_le]
  constructor <;> linarith

/-- Different CRT assignments to the same prime support retain the shared-modulus
error improvement. No relation between their individual residues is required. -/
theorem intersection_count_pair_error (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (r s : ℕ → ℕ) (m : ℕ) :
    |(((range m).filter (fun j => ∀ p ∈ Q, j ≡ r p [MOD p])).card : ℝ) -
      ((range m).filter (fun j => ∀ p ∈ Q, j ≡ s p [MOD p])).card| ≤ 1 := by
  classical
  obtain ⟨a, ha⟩ := intersection_residue Q hQ r
  obtain ⟨b, hb⟩ := intersection_residue Q hQ s
  simp_rw [ha, hb]
  exact residue_count_pair_error m (∏ p ∈ Q, p) a b
    (prod_pos (fun p hp => (hQ p hp).pos))

#print axioms residue_family_error
#print axioms residue_balanced_error
#print axioms intersection_count_pair_error
end Erdos970.BrunCriterion
