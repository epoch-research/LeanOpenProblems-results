import Submission.GapPairAverage

/-! Exact moments of survivor counts under independent uniform residue phases.
The pair-correlation estimate gives a binomial upper bound for the variance.
No exponential gap-tail bound is asserted. -/
namespace Erdos970.GapAverages
open Finset

abbrev Phase (P : Finset ℕ) := (p : P) → Fin p.val

noncomputable def phaseMean (P : Finset ℕ) (f : Phase P → ℝ) : ℝ :=
  (∑ r, f r) / ∏ p : P, (p.val : ℝ)

noncomputable def point (P : Finset ℕ) (x : ℕ) (r : Phase P) : ℝ :=
  ∏ p : P, (1 - if x % p.val = (r p).val then (1 : ℝ) else 0)

noncomputable def intervalCount (P : Finset ℕ) (m : ℕ) (r : Phase P) : ℝ :=
  ∑ x ∈ range m, point P x r

lemma phaseMean_add (P : Finset ℕ) (f g : Phase P → ℝ) :
    phaseMean P (fun r => f r + g r) = phaseMean P f + phaseMean P g := by
  simp only [phaseMean, sum_add_distrib, add_div]

lemma phaseMean_mul (P : Finset ℕ) (c : ℝ) (f : Phase P → ℝ) :
    phaseMean P (fun r => c * f r) = c * phaseMean P f := by
  simp only [phaseMean, ← mul_sum]
  ring

lemma phaseMean_sum (P : Finset ℕ) {α : Type*} (S : Finset α) (f : α → Phase P → ℝ) :
    phaseMean P (fun r => ∑ x ∈ S, f x r) = ∑ x ∈ S, phaseMean P (f x) := by
  unfold phaseMean
  rw [sum_comm, sum_div]

lemma phaseMean_prod (P : Finset ℕ) (f : (p : P) → Fin p.val → ℝ) :
    phaseMean P (fun r => ∏ p : P, f p (r p)) =
      ∏ p : P, (∑ a : Fin p.val, f p a) / (p.val : ℝ) := by
  rw [phaseMean, ← Fintype.prod_sum, prod_div_distrib]

lemma coordinate_hit_sum (p x : ℕ) (hp : 0 < p) :
    (∑ a : Fin p, if x % p = a.val then (1 : ℝ) else 0) = 1 := by
  let b : Fin p := ⟨x % p, Nat.mod_lt _ hp⟩
  have he (a : Fin p) : x % p = a.val ↔ a = b := by
    change b.val = a.val ↔ a = b
    simp only [Fin.ext_iff]
    exact eq_comm
  simp_rw [he]
  simp

lemma coordinate_pair_sum (p x y : ℕ) (hp : 0 < p) :
    (∑ a : Fin p, (1 - if x % p = a.val then (1 : ℝ) else 0) *
      (1 - if y % p = a.val then (1 : ℝ) else 0)) =
      (p : ℝ) - 2 + if x % p = y % p then 1 else 0 := by
  have he (a : Fin p) : (1 - if x % p = a.val then (1 : ℝ) else 0) *
      (1 - if y % p = a.val then (1 : ℝ) else 0) =
      1 - (if x % p = a.val then 1 else 0) - (if y % p = a.val then 1 else 0) +
        if x % p = y % p then (if x % p = a.val then 1 else 0) else 0 := by
    split_ifs <;> simp_all <;> norm_num
  simp_rw [he]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    coordinate_hit_sum p x hp, coordinate_hit_sum p y hp]
  simp only [sum_const, card_fin, nsmul_eq_mul, mul_one]
  split_ifs <;> simp only [coordinate_hit_sum p x hp, sum_const_zero] <;> ring

lemma phaseMean_point (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : ℕ) :
    phaseMean P (point P x) = density P := by
  change phaseMean P (fun r => ∏ p : P,
    (1 - if x % p.val = (r p).val then (1 : ℝ) else 0)) = _
  rw [phaseMean_prod P (fun p a => 1 - if x % p.val = a.val then (1 : ℝ) else 0)]
  have he (p : P) : (∑ a : Fin p.val, (1 - if x % p.val = a.val then (1 : ℝ) else 0)) /
      (p.val : ℝ) = 1 - 1 / (p.val : ℝ) := by
    rw [sum_sub_distrib, coordinate_hit_sum p.val x (hP p.val p.property).pos]
    simp only [sum_const, card_fin, nsmul_eq_mul, mul_one]
    have hn : (p.val : ℝ) ≠ 0 := by exact_mod_cast (hP p.val p.property).ne_zero
    field_simp
  simp_rw [he]
  exact prod_attach P (fun p => 1 - 1 / (p : ℝ))

lemma phaseMean_point_pair (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x y : ℕ) (hxy : x ≤ y) :
    phaseMean P (fun r => point P x r * point P y r) = pairKernel P (y - x) := by
  have he (r : Phase P) : point P x r * point P y r =
      ∏ p : P, ((1 - if x % p.val = (r p).val then (1 : ℝ) else 0) *
        (1 - if y % p.val = (r p).val then (1 : ℝ) else 0)) := by
    simp only [point, prod_mul_distrib]
  simp_rw [he]
  rw [phaseMean_prod P (fun p a =>
    (1 - if x % p.val = a.val then (1 : ℝ) else 0) *
    (1 - if y % p.val = a.val then (1 : ℝ) else 0))]
  have hf (p : P) : ((∑ a : Fin p.val,
      (1 - if x % p.val = a.val then (1 : ℝ) else 0) *
      (1 - if y % p.val = a.val then (1 : ℝ) else 0)) / (p.val : ℝ)) =
      (1 - 2 / (p.val : ℝ)) + (1 / (p.val : ℝ)) *
        if p.val ∣ y - x then 1 else 0 := by
    rw [coordinate_pair_sum p.val x y (hP p.val p.property).pos]
    have hmod : x % p.val = y % p.val ↔ p.val ∣ y - x := Nat.modEq_iff_dvd' hxy
    simp only [hmod]
    have hn : (p.val : ℝ) ≠ 0 := by exact_mod_cast (hP p.val p.property).ne_zero
    split_ifs <;> field_simp <;> ring
  simp_rw [hf]
  exact prod_attach P (fun p : ℕ => (1 - 2 / (p : ℝ)) + (1 / (p : ℝ)) * if p ∣ y - x then 1 else 0)

lemma point_sq (P : Finset ℕ) (x : ℕ) (r : Phase P) : point P x r ^ 2 = point P x r := by
  rw [point, ← prod_pow]
  apply prod_congr rfl
  intro p hp
  split_ifs <;> norm_num

lemma intervalCount_succ (P : Finset ℕ) (m : ℕ) (r : Phase P) :
    intervalCount P (m + 1) r = intervalCount P m r + point P m r := sum_range_succ _ _

lemma phaseMean_count (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    phaseMean P (intervalCount P m) = (m : ℝ) * density P := by
  change phaseMean P (fun r => ∑ x ∈ range m, point P x r) = _
  rw [phaseMean_sum]
  simp only [phaseMean_point P hP, sum_const, card_range, nsmul_eq_mul]

lemma pairKernel_reverse_sum (P : Finset ℕ) (m : ℕ) :
    (∑ x ∈ range m, pairKernel P (m - x)) = ∑ h ∈ range m, pairKernel P (h + 1) := by
  rw [← sum_range_reflect (fun h => pairKernel P (h + 1)) m]
  apply sum_congr rfl
  intro x hx
  have hx' := mem_range.mp hx
  congr 1
  omega

lemma phaseMean_count_point_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    phaseMean P (fun r => intervalCount P m r * point P m r) ≤ (m : ℝ) * density P ^ 2 := by
  simp only [intervalCount, sum_mul]
  rw [phaseMean_sum]
  have he : (∑ x ∈ range m, phaseMean P (fun r => point P x r * point P m r)) =
      ∑ x ∈ range m, pairKernel P (m - x) := by
    apply sum_congr rfl
    intro x hx
    exact phaseMean_point_pair P hP x m (mem_range.mp hx).le
  rw [he, pairKernel_reverse_sum]
  exact sum_pairKernel_le P hP m

/-- A binomial upper bound for the second moment of the actual phase counts. -/
theorem phaseMean_count_sq_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    phaseMean P (fun r => intervalCount P m r ^ 2) ≤
      (m : ℝ) * density P + (m : ℝ) * (m - 1) * density P ^ 2 := by
  induction m with
  | zero => simp [intervalCount, phaseMean]
  | succ m ih =>
    have he (r : Phase P) : intervalCount P (m + 1) r ^ 2 =
        intervalCount P m r ^ 2 + 2 * (intervalCount P m r * point P m r) + point P m r := by
      rw [intervalCount_succ]
      nlinarith only [point_sq P m r]
    simp_rw [he]
    rw [phaseMean_add, phaseMean_add, phaseMean_mul, phaseMean_point P hP]
    have hh := phaseMean_count_point_le P hP m
    push_cast
    nlinarith only [ih, hh]

lemma phaseMean_const (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c : ℝ) :
    phaseMean P (fun _ => c) = c := by
  have hN : (∏ p : P, (p.val : ℝ)) ≠ 0 := prod_ne_zero_iff.mpr
    (fun p _ => by exact_mod_cast (hP p.val p.property).ne_zero)
  have hc : (Fintype.card (Phase P) : ℝ) = ∏ p : P, (p.val : ℝ) := by
    simp only [Phase, Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
  simp only [phaseMean, sum_const, nsmul_eq_mul, card_univ, hc]
  field_simp

lemma phaseMean_sub (P : Finset ℕ) (f g : Phase P → ℝ) :
    phaseMean P (fun r => f r - g r) = phaseMean P f - phaseMean P g := by
  simp only [phaseMean, sum_sub_distrib, sub_div]

lemma density_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : 0 < density P := by
  apply prod_pos
  intro p hp
  have hpp : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
  have hh : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr hpp
  linarith

lemma phaseMean_mono (P : Finset ℕ) {f g : Phase P → ℝ} (h : ∀ r, f r ≤ g r) :
    phaseMean P f ≤ phaseMean P g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun r _ => h r)) (by positivity)

/-- The variance of the actual uniformly phased count is no greater than the
variance of a binomial count with the same mean and interval length. -/
theorem phase_variance_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    phaseMean P (fun r => (intervalCount P m r - (m : ℝ) * density P) ^ 2) ≤
      (m : ℝ) * density P * (1 - density P) := by
  have he (r : Phase P) : (intervalCount P m r - (m : ℝ) * density P) ^ 2 =
      intervalCount P m r ^ 2 - (2 * (m : ℝ) * density P) * intervalCount P m r +
        ((m : ℝ) * density P) ^ 2 := by ring
  simp_rw [he]
  rw [phaseMean_add, phaseMean_sub, phaseMean_mul, phaseMean_count P hP,
    phaseMean_const P hP]
  nlinarith only [phaseMean_count_sq_le P hP m]

noncomputable def coveredFraction (P : Finset ℕ) (m : ℕ) : ℝ :=
  phaseMean P (fun r => if intervalCount P m r = 0 then 1 else 0)

/-- This second-moment argument gives only a reciprocal tail bound, not the
exponential tail that would be needed for the proposed counting route. -/
theorem coveredFraction_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hm : 0 < m) :
    ((m : ℝ) * density P) * coveredFraction P m ≤ 1 - density P := by
  have hmu : 0 < (m : ℝ) * density P := mul_pos (by exact_mod_cast hm) (density_pos P hP)
  have hh : ((m : ℝ) * density P) ^ 2 * coveredFraction P m ≤
      phaseMean P (fun r => (intervalCount P m r - (m : ℝ) * density P) ^ 2) := by
    rw [coveredFraction, ← phaseMean_mul]
    apply phaseMean_mono
    intro r
    split_ifs with hr
    · rw [hr]
      ring_nf
      rfl
    · simp only [mul_zero]
      exact sq_nonneg _
  have hb := hh.trans (phase_variance_le P hP m)
  apply (mul_le_mul_iff_right₀ hmu).mp
  convert hb using 1 <;> ring

#print axioms phase_variance_le
#print axioms coveredFraction_bound
#print axioms phaseMean_point_pair
#print axioms phaseMean_count_sq_le
end Erdos970.GapAverages
