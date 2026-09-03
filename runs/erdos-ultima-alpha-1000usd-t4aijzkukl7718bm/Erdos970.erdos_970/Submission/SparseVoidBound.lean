import Submission.GapTailCriterion

/-!
A total-hit exponential moment bound for uniformly and independently selected
residue classes. It gives exponential decay of the covered fraction when the
sum of reciprocal moduli is bounded strictly below one. It does not treat the
dense small-prime case of the Jacobsthal conjecture.
-/
namespace Erdos970.GapAverages
open Finset Real

/-- The hit count of one selected residue, before any other sieving. -/
def residueHits (m p : ℕ) (a : Fin p) : ℕ :=
  ((range m).filter (fun x => x % p = a.val)).card

lemma residueHits_eq (m p : ℕ) (hp : 0 < p) (a : Fin p) :
    residueHits m p a = m / p + if a.val < m % p then 1 else 0 := by
  have he : residueHits m p a = ((range m).filter (fun x => x ≡ a.val [MOD p])).card := by
    simp only [residueHits, Nat.ModEq, Nat.mod_eq_of_lt a.isLt]
  rw [he, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card m hp]
  rw [Nat.mod_eq_of_lt a.isLt]

lemma residueHits_cast (m p : ℕ) (a : Fin p) :
    (residueHits m p a : ℝ) = ∑ x ∈ range m, if x % p = a.val then 1 else 0 := by
  rw [residueHits, sum_boole]

lemma sum_residueHits (m p : ℕ) (hp : 0 < p) :
    (∑ a : Fin p, (residueHits m p a : ℝ)) = m := by
  simp_rw [residueHits_cast]
  rw [sum_comm]
  simp only [coordinate_hit_sum p _ hp, sum_const, card_range, nsmul_eq_mul, mul_one]

/-- Exact affine interpolation of the one-coordinate exponential moment. -/
lemma residueHits_pow_mean (m p : ℕ) (hp : 0 < p) (b : ℝ) :
    (∑ a : Fin p, b ^ residueHits m p a) / p =
      b ^ (m / p) * (1 + (b - 1) * ((m : ℝ) / p - (m / p : ℕ))) := by
  have he (a : Fin p) : b ^ residueHits m p a =
      b ^ (m / p) * (1 + (b - 1) * ((residueHits m p a : ℝ) - (m / p : ℕ))) := by
    rw [residueHits_eq m p hp a]
    split_ifs <;> push_cast <;> simp only [pow_succ, add_zero] <;> ring
  simp_rw [he]
  rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_residueHits m p hp]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

/-- A balanced residue count has no larger exponential moment than a Poisson
variable with the same mean, for exponential bases at least one. -/
lemma residueHits_pow_mean_le (m p : ℕ) (hp : 0 < p) (b : ℝ) (hb : 1 ≤ b) :
    (∑ a : Fin p, b ^ residueHits m p a) / p ≤ exp ((b - 1) * m / p) := by
  rw [residueHits_pow_mean m p hp b]
  have hq : (m / p : ℕ) ≤ (m : ℝ) / p := Nat.cast_div_le
  have hbase : b ≤ exp (b - 1) := by linarith only [add_one_le_exp (b - 1)]
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ b) hbase (m / p)
  rw [← exp_nat_mul] at hpow
  have hr : 0 ≤ 1 + (b - 1) * ((m : ℝ) / p - (m / p : ℕ)) :=
    add_nonneg (by norm_num) (mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hq))
  have hlin : 1 + (b - 1) * ((m : ℝ) / p - (m / p : ℕ)) ≤
      exp ((b - 1) * ((m : ℝ) / p - (m / p : ℕ))) := by
    linarith only [add_one_le_exp ((b - 1) * ((m : ℝ) / p - (m / p : ℕ)))]
  calc
    _ ≤ exp ((m / p : ℕ) * (b - 1)) *
        exp ((b - 1) * ((m : ℝ) / p - (m / p : ℕ))) :=
      mul_le_mul hpow hlin hr (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

/-- The number of hits with multiplicity; overlaps are not discarded. -/
def totalHits (P : Finset ℕ) (m : ℕ) (r : Phase P) : ℕ :=
  ∑ p : P, residueHits m p.val (r p)

lemma totalHits_pow_mean_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (b : ℝ) (hb : 1 ≤ b) :
    phaseMean P (fun r => b ^ totalHits P m r) ≤
      exp ((b - 1) * m * ∑ p ∈ P, 1 / (p : ℝ)) := by
  simp only [totalHits, ← prod_pow_eq_pow_sum]
  rw [phaseMean_prod P (fun p a => b ^ residueHits m p.val a)]
  calc
    _ ≤ ∏ p : P, exp ((b - 1) * m / p.val) := by
      apply prod_le_prod
      · intro p hp
        exact div_nonneg (sum_nonneg (fun a _ => pow_nonneg (by linarith) _))
          (Nat.cast_nonneg _)
      · intro p hp
        exact residueHits_pow_mean_le m p.val (hP p.val p.property).pos b hb
    _ = _ := by
      rw [← exp_sum]
      congr 1
      rw [← sum_attach P (fun p : ℕ => 1 / (p : ℝ)), mul_sum]
      apply sum_congr rfl
      intro p hp
      ring

lemma point_nonneg (P : Finset ℕ) (x : ℕ) (r : Phase P) : 0 ≤ point P x r := by
  apply prod_nonneg
  intro p hp
  split_ifs <;> norm_num

lemma cover_of_count_zero (P : Finset ℕ) (m : ℕ) (r : Phase P)
    (hr : intervalCount P m r = 0) :
    ∀ x < m, ∃ p : P, x % p.val = (r p).val := by
  intro x hx
  by_contra hbad
  push_neg at hbad
  have hp : point P x r = 1 := by simp [point, hbad]
  have hh := single_le_sum (s := range m) (f := fun y => point P y r)
    (fun y _ => point_nonneg P y r) (mem_range.mpr hx)
  change point P x r ≤ intervalCount P m r at hh
  rw [hp, hr] at hh
  norm_num at hh

lemma length_le_totalHits_of_cover (P : Finset ℕ) (m : ℕ) (r : Phase P)
    (hr : intervalCount P m r = 0) : m ≤ totalHits P m r := by
  have he : (totalHits P m r : ℝ) =
      ∑ x ∈ range m, ∑ p : P, if x % p.val = (r p).val then (1 : ℝ) else 0 := by
    simp only [totalHits, Nat.cast_sum, residueHits_cast]
    exact sum_comm
  have hh : (m : ℝ) ≤ (totalHits P m r : ℝ) := by
    rw [he]
    calc
      (m : ℝ) = ∑ _x ∈ range m, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro x hx
        obtain ⟨p, hp⟩ := cover_of_count_zero P m r hr x (mem_range.mp hx)
        have hh := single_le_sum (s := (univ : Finset P))
          (f := fun p => if x % p.val = (r p).val then (1 : ℝ) else 0)
          (fun p _ => by dsimp only; split_ifs <;> norm_num) (mem_univ p)
        simpa only [hp, if_true] using hh
  exact_mod_cast hh

/-- A Chernoff bound for coverage. It is nontrivial only when the reciprocal
sum is sufficiently small relative to the chosen exponential base. -/
theorem coveredFraction_le_total_hit_exponential (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (b : ℝ) (hb : 1 ≤ b) :
    coveredFraction P m ≤
      exp (((b - 1) * (∑ p ∈ P, 1 / (p : ℝ)) - log b) * m) := by
  have hb0 : 0 < b := by linarith
  have hpow : 0 < b ^ m := pow_pos hb0 _
  have hmarkov : b ^ m * coveredFraction P m ≤
      phaseMean P (fun r => b ^ totalHits P m r) := by
    rw [coveredFraction, ← phaseMean_mul]
    apply phaseMean_mono
    intro r
    split_ifs with hr
    · simpa only [mul_one] using
        pow_le_pow_right₀ hb (length_le_totalHits_of_cover P m r hr)
    · simpa only [mul_zero] using (pow_nonneg hb0.le (totalHits P m r))
  have hh := hmarkov.trans (totalHits_pow_mean_le P hP m b hb)
  have hbound : coveredFraction P m ≤
      exp ((b - 1) * m * ∑ p ∈ P, 1 / (p : ℝ)) / b ^ m := by
    apply (le_div_iff₀ hpow).mpr
    rwa [mul_comm]
  apply hbound.trans_eq
  have he : b ^ m = exp ((m : ℝ) * log b) := by rw [exp_nat_mul, exp_log hb0]
  rw [he, ← exp_sub]
  congr 1
  ring

/-- An unconditional exponential bound on the sparse-reciprocal class. The
reciprocal-sum hypothesis is not true for arbitrary prime sets. -/
theorem coveredFraction_le_exp_of_reciprocal_half (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hs : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 1 / 2) (m : ℕ) :
    coveredFraction P m ≤ exp (-(m : ℝ) / 8) := by
  apply (coveredFraction_le_total_hit_exponential P hP m 2 (by norm_num)).trans
  apply exp_le_exp.mpr
  have hlog : (5 / 8 : ℝ) ≤ log 2 := by linarith only [log_two_gt_d9]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith

#print axioms residueHits_pow_mean_le
#print axioms totalHits_pow_mean_le
#print axioms coveredFraction_le_total_hit_exponential
#print axioms coveredFraction_le_exp_of_reciprocal_half

/-- The optimized total-hit bound for any fixed reciprocal budget below one. -/
theorem coveredFraction_le_exp_of_reciprocal_lt_one (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hs : (∑ p ∈ P, 1 / (p : ℝ)) ≤ α) (m : ℕ) :
    coveredFraction P m ≤ exp (-((α - 1 - log α) * m)) := by
  have hb : 1 ≤ 1 / α := one_le_one_div hα hα1.le
  apply (coveredFraction_le_total_hit_exponential P hP m (1 / α) hb).trans
  apply exp_le_exp.mpr
  have hc := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hb)
  have he : (1 / α - 1) * α - log (1 / α) = -(α - 1 - log α) := by
    rw [log_div (by norm_num) hα.ne', log_one]
    field_simp
    ring
  have hh : (1 / α - 1) * (∑ p ∈ P, 1 / (p : ℝ)) - log (1 / α) ≤
      -(α - 1 - log α) := by linarith only [hc, he]
  simpa only [neg_mul] using mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg m)

lemma sparse_exponential_rate_pos (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < α - 1 - log α := by
  linarith only [log_lt_sub_one_of_pos hα hα1.ne]

#print axioms coveredFraction_le_exp_of_reciprocal_lt_one
#print axioms sparse_exponential_rate_pos

end Erdos970.GapAverages
