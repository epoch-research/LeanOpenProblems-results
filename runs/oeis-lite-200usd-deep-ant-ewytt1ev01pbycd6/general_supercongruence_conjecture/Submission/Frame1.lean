import Mathlib
open PowerSeries
namespace ExpFrame
open Finset
noncomputable def expOfAux (D : PowerSeries ℚ) : ℕ → ℚ
  | 0 => 1
  | (m + 1) =>
      (∑ i ∈ (Finset.range (m + 1)).attach,
          expOfAux D i.1 * coeff (m - i.1) D) / (m + 1)
  termination_by n => n
  decreasing_by exact Finset.mem_range.mp i.2
theorem expOfAux_zero (D : PowerSeries ℚ) : expOfAux D 0 = 1 := by rw [expOfAux]
theorem expOfAux_succ (D : PowerSeries ℚ) (m : ℕ) :
    expOfAux D (m + 1) = (∑ i ∈ Finset.range (m + 1), expOfAux D i * coeff (m - i) D) / (m + 1) := by
  rw [expOfAux]; congr 1
  rw [← Finset.sum_attach (Finset.range (m + 1)) (fun i => expOfAux D i * coeff (m - i) D)]
noncomputable def expOf (D : PowerSeries ℚ) : PowerSeries ℚ := PowerSeries.mk (expOfAux D)
theorem coeff_expOf (D : PowerSeries ℚ) (n : ℕ) : coeff n (expOf D) = expOfAux D n := by rw [expOf, coeff_mk]
theorem expOf_coeff_zero (D : PowerSeries ℚ) : coeff 0 (expOf D) = 1 := by rw [coeff_expOf, expOfAux_zero]
theorem expOf_deriv (D : PowerSeries ℚ) : d⁄dX ℚ (expOf D) = expOf D * D := by
  ext n
  rw [coeff_derivative, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun ij => coeff ij.1 (expOf D) * coeff ij.2 D) n]
  simp only [coeff_expOf]; rw [expOfAux_succ]
  have hne : ((n : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [div_mul_cancel₀ _ hne]
theorem expOf_unique (D G : PowerSeries ℚ) (h0 : coeff 0 G = 1) (hG : d⁄dX ℚ G = G * D) : G = expOf D := by
  have key : ∀ n, coeff n G = coeff n (expOf D) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => rw [h0, expOf_coeff_zero]
      | succ m =>
        have hne : ((m : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        have hco : coeff m (d⁄dX ℚ G) = coeff m (G * D) := by rw [hG]
        rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun ij => coeff ij.1 G * coeff ij.2 D) m] at hco
        have hcE : coeff m (d⁄dX ℚ (expOf D)) = coeff m (expOf D * D) := by rw [expOf_deriv]
        rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun ij => coeff ij.1 (expOf D) * coeff ij.2 D) m] at hcE
        have hsum : (∑ k ∈ range (m + 1), coeff k G * coeff (m - k) D) = ∑ k ∈ range (m + 1), coeff k (expOf D) * coeff (m - k) D := by
          apply Finset.sum_congr rfl; intro k hk; rw [Finset.mem_range] at hk; rw [ih k (by omega)]
        rw [hsum] at hco
        have : coeff (m + 1) G * ((m : ℚ) + 1) = coeff (m + 1) (expOf D) * ((m : ℚ) + 1) := by rw [hco, hcE]
        exact mul_right_cancel₀ hne this
  exact PowerSeries.ext key
theorem expOf_zero : expOf (0 : PowerSeries ℚ) = 1 := by symm; apply expOf_unique <;> simp
theorem expOf_mul (D E : PowerSeries ℚ) : expOf D * expOf E = expOf (D + E) := by
  apply expOf_unique
  · rw [coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, expOf_coeff_zero, expOf_coeff_zero, mul_one]
  · rw [Derivation.leibniz]; simp only [smul_eq_mul]; rw [expOf_deriv, expOf_deriv]; ring
theorem expOf_pow (D : PowerSeries ℚ) (n : ℕ) : (expOf D) ^ n = expOf (n • D) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, expOf_zero]
  | succ k ih => rw [pow_succ, ih, expOf_mul, succ_nsmul]
end ExpFrame

namespace Frame1
open ExpFrame Finset

noncomputable def Exp (L : PowerSeries ℚ) : PowerSeries ℚ := expOf (d⁄dX ℚ L)

noncomputable def Up (p : ℕ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun k => coeff (p * k) f)

theorem Up_coeff (p : ℕ) (f : PowerSeries ℚ) (k : ℕ) :
    coeff k (Up p f) = coeff (p * k) f := by
  rw [Up, coeff_mk]

-- (T1)
theorem Exp_coeff_zero (L : PowerSeries ℚ) : coeff 0 (Exp L) = 1 := by
  rw [Exp, expOf_coeff_zero]

-- (T2)
theorem Exp_mul (L K : PowerSeries ℚ) : Exp L * Exp K = Exp (L + K) := by
  rw [Exp, Exp, Exp, expOf_mul, map_add]

-- (T3)
theorem Exp_pow (L : PowerSeries ℚ) (n : ℕ) : (Exp L) ^ n = Exp (n • L) := by
  rw [Exp, Exp, expOf_pow, map_nsmul]

-- (T4) chain rule
theorem derivative_expand (p : ℕ) (hp : p ≠ 0) (f : PowerSeries ℚ) :
    d⁄dX ℚ (expand p hp f)
      = expand p hp (d⁄dX ℚ f) * ((p : ℚ) • (X : PowerSeries ℚ) ^ (p - 1)) := by
  ext n
  rw [coeff_derivative, coeff_expand]
  rw [mul_smul_comm, map_smul, coeff_mul_X_pow', smul_eq_mul]
  by_cases hd : p ∣ (n + 1)
  · -- p ∣ n+1
    rw [if_pos hd]
    obtain ⟨t, ht⟩ := hd
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · simp [h] at ht
      · exact h
    have hple : p ≤ n + 1 := by rw [ht]; exact Nat.le_mul_of_pos_right p htpos
    have hle : p - 1 ≤ n := by omega
    have hdiv : (n + 1) / p = t := by
      rw [ht]; exact Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hp)
    have hpt : p * (t - 1) = p * t - p := by
      cases t with
      | zero => simp
      | succ s => rw [Nat.mul_succ, Nat.succ_sub_one]; omega
    have he : n - (p - 1) = p * (t - 1) := by omega
    have ht1 : (t - 1) + 1 = t := by omega
    have hc : (n : ℚ) + 1 = (p : ℚ) * (t : ℚ) := by exact_mod_cast ht
    have hct : ((t - 1 : ℕ) : ℚ) + 1 = (t : ℚ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]; ring
    rw [hdiv, if_pos hle, he, coeff_expand_mul, coeff_derivative, ht1, hc, hct]
    ring
  · -- ¬ p ∣ n+1
    rw [if_neg hd, zero_mul]
    by_cases hle : p - 1 ≤ n
    · rw [if_pos hle]
      have hnd : ¬ p ∣ (n - (p - 1)) := by
        intro hdvd
        apply hd
        have he : n - (p - 1) = n + 1 - p := by omega
        rw [he] at hdvd
        have h2 : n + 1 - p + p = n + 1 := Nat.sub_add_cancel (by omega)
        exact h2 ▸ Nat.dvd_add hdvd (dvd_refl p)
      rw [coeff_expand_of_not_dvd p hp _ hnd, mul_zero]
    · rw [if_neg hle, mul_zero]

-- (T5) K1
theorem expand_Exp (p : ℕ) (hp : p ≠ 0) (L : PowerSeries ℚ) :
    expand p hp (Exp L) = Exp (expand p hp L) := by
  show expand p hp (Exp L) = expOf (d⁄dX ℚ (expand p hp L))
  apply expOf_unique
  · -- constant coefficient
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_expand,
        ← coeff_zero_eq_constantCoeff_apply, Exp_coeff_zero]
  · -- ODE
    have hderiv : d⁄dX ℚ (Exp L) = Exp L * d⁄dX ℚ L := by
      rw [Exp]; exact expOf_deriv (d⁄dX ℚ L)
    rw [derivative_expand p hp (Exp L), hderiv, map_mul,
        derivative_expand p hp L, mul_assoc]

-- (T6) K2 intertwining
theorem Up_expand_mul (p : ℕ) (hp : p ≠ 0) (g h : PowerSeries ℚ) :
    Up p (expand p hp g * h) = g * Up p h := by
  ext k
  rw [Up_coeff, coeff_mul, coeff_mul]
  have hmem : ∀ a ∈ (antidiagonal (p * k)).filter (fun ij => p ∣ ij.1),
      p ∣ a.1 ∧ p ∣ a.2 := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    refine ⟨ha.2, ?_⟩
    have hd : p ∣ (a.1 + a.2) := by rw [ha.1]; exact ⟨k, rfl⟩
    exact (Nat.dvd_add_right ha.2).mp hd
  have hfilter :
      (∑ ij ∈ antidiagonal (p * k), coeff ij.1 (expand p hp g) * coeff ij.2 h)
      = ∑ ij ∈ (antidiagonal (p * k)).filter (fun ij => p ∣ ij.1),
          coeff ij.1 (expand p hp g) * coeff ij.2 h := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x hx hxn
    have hnd : ¬ p ∣ x.1 := fun hdvd => hxn (Finset.mem_filter.mpr ⟨hx, hdvd⟩)
    rw [coeff_expand_of_not_dvd p hp _ hnd, zero_mul]
  rw [hfilter]
  refine Finset.sum_bij'
      (fun ij _ => (ij.1 / p, ij.2 / p))
      (fun ab _ => (p * ab.1, p * ab.2))
      ?_ ?_ ?_ ?_ ?_
  · -- hi : maps into antidiagonal k
    intro a ha
    obtain ⟨hd1, hd2⟩ := hmem _ ha
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    obtain ⟨u, hu⟩ := hd1
    obtain ⟨v, hv⟩ := hd2
    rw [Finset.mem_antidiagonal]
    show a.1 / p + a.2 / p = k
    rw [hu, hv, Nat.mul_div_cancel_left u (Nat.pos_of_ne_zero hp),
        Nat.mul_div_cancel_left v (Nat.pos_of_ne_zero hp)]
    have hsum : p * u + p * v = p * k := by rw [← hu, ← hv]; exact ha.1
    have : p * (u + v) = p * k := by rw [Nat.mul_add]; exact hsum
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) this
  · -- hj : maps into filtered set
    intro a ha
    rw [Finset.mem_antidiagonal] at ha
    rw [Finset.mem_filter, Finset.mem_antidiagonal]
    refine ⟨?_, ⟨a.1, rfl⟩⟩
    show p * a.1 + p * a.2 = p * k
    rw [← Nat.mul_add, ha]
  · -- left_inv
    intro a ha
    obtain ⟨hd1, hd2⟩ := hmem _ ha
    show (p * (a.1 / p), p * (a.2 / p)) = a
    rw [Nat.mul_div_cancel' hd1, Nat.mul_div_cancel' hd2]
  · -- right_inv
    intro a ha
    show ((p * a.1) / p, (p * a.2) / p) = a
    rw [Nat.mul_div_cancel_left a.1 (Nat.pos_of_ne_zero hp),
        Nat.mul_div_cancel_left a.2 (Nat.pos_of_ne_zero hp)]
  · -- term equality
    intro a ha
    obtain ⟨hd1, hd2⟩ := hmem _ ha
    have hL : coeff a.1 (expand p hp g) = coeff (a.1 / p) g := by
      conv_lhs => rw [← Nat.mul_div_cancel' hd1]
      rw [coeff_expand_mul]
    have hR2 : coeff (a.2 / p) (Up p h) = coeff a.2 h := by
      rw [Up_coeff, Nat.mul_div_cancel' hd2]
    show coeff a.1 (expand p hp g) * coeff a.2 h = coeff (a.1 / p) g * coeff (a.2 / p) (Up p h)
    rw [hL, hR2]

end Frame1

