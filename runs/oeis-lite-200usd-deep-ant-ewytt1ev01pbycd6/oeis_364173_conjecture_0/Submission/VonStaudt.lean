import FormalConjectures.Util.ProblemImports

namespace VonStaudt

variable {p : ℕ} [hp : Fact p.Prime]

open Finset

/-- For `p ≥ 3` and `k ≥ 1`, we have `k + 2 ≤ p ^ k`. -/
lemma add_two_le_pow (hp3 : 3 ≤ p) : ∀ k : ℕ, 1 ≤ k → k + 2 ≤ p ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge 1 (n + 1) with h | h
    · -- n ≥ 1
      have hn : 1 ≤ n := by omega
      have ihn := ih hn
      have hpow : p ^ (n + 1) = p ^ n * p := by rw [pow_succ]
      have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ (by omega)
      nlinarith [ihn, hpn, hp3]
    · -- n + 1 = 1
      have : n = 0 := by omega
      subst this
      simpa using hp3

/-- For a prime `p ≥ 3` and `l ≥ 2`, `padicValNat p l + 2 ≤ l`. -/
lemma padicValNat_add_two_le (hp3 : 3 ≤ p) {l : ℕ} (hl : 2 ≤ l) :
    padicValNat p l + 2 ≤ l := by
  have hdvd : p ^ padicValNat p l ∣ l := pow_padicValNat_dvd
  have hle : p ^ padicValNat p l ≤ l := Nat.le_of_dvd (by omega) hdvd
  rcases Nat.eq_zero_or_pos (padicValNat p l) with h0 | hpos
  · omega
  · have := add_two_le_pow hp3 (padicValNat p l) hpos
    omega

/-- The `p`-adic norm of a natural number cast is at most `1`. -/
lemma norm_nat_le_one (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := p) (n : ℤ)
  simpa using this

/-- For `l ≠ 0`, the norm of `(l : ℚ_[p])` equals `p ^ (- padicValNat p l)`. -/
lemma norm_natCast_eq (l : ℕ) (hl : l ≠ 0) :
    ‖(l : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p l : ℤ)) := by
  have hne : (l : ℚ_[p]) ≠ 0 := by
    simpa using hl
  rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]

/-- Norm bound for a single correction term (in its "good" form with `m.choose i / (m+1-i)`),
assuming the induction hypothesis for `bernoulli i`. -/
lemma term_norm_le (hp5 : 5 ≤ p) {m i : ℕ} (hi : i < m)
    (ih : ‖((bernoulli i : ℚ) : ℚ_[p])‖ ≤ (p : ℝ)) :
    ‖((bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m + 1 - i : ℕ) : ℚ) : ℚ)
        : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  set l := m + 1 - i with hl
  have hl2 : 2 ≤ l := by omega
  have hlne : l ≠ 0 := by omega
  set v := padicValNat p l with hv
  have hvle : v + 2 ≤ l := padicValNat_add_two_le (by omega) hl2
  have hcast : ((bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ l / (l : ℚ) : ℚ) : ℚ_[p])
      = ((bernoulli i : ℚ) : ℚ_[p]) * ((m.choose i : ℕ) : ℚ_[p]) * ((p : ℕ) : ℚ_[p]) ^ l
          / ((l : ℕ) : ℚ_[p]) := by
    push_cast
    ring
  have hnl : ‖((l : ℕ) : ℚ_[p])‖ = (p : ℝ) ^ (-(v : ℤ)) := norm_natCast_eq l hlne
  rw [hcast, norm_div, norm_mul, norm_mul, norm_pow, Padic.norm_p, hnl]
  have hstep : ‖((bernoulli i : ℚ) : ℚ_[p])‖ * ‖((m.choose i : ℕ) : ℚ_[p])‖
      * ((p : ℝ)⁻¹) ^ l / (p : ℝ) ^ (-(v : ℤ))
      ≤ (p : ℝ) * 1 * ((p : ℝ)⁻¹) ^ l / (p : ℝ) ^ (-(v : ℤ)) := by
    gcongr
    exact norm_nat_le_one _
  refine hstep.trans ?_
  rw [zpow_neg, zpow_natCast, inv_pow, mul_one]
  have expand : (p : ℝ) * ((p : ℝ) ^ l)⁻¹ / ((p : ℝ) ^ v)⁻¹
      = (p : ℝ) ^ (v + 1) / (p : ℝ) ^ l := by
    field_simp
    ring
  rw [expand, inv_eq_one_div, div_le_div_iff₀ (by positivity) hpR, one_mul, ← pow_succ]
  exact pow_le_pow_right₀ hp1 (by omega)

/-- Rewriting a Faulhaber correction term into its "good" form. -/
lemma term_eq {m i : ℕ} (hi : i ≤ m) :
    bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m : ℚ) + 1)
      = bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m + 1 - i : ℕ) : ℚ) := by
  have hd1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hd2 : ((m + 1 - i : ℕ) : ℚ) ≠ 0 := by
    have : 0 < m + 1 - i := by omega
    exact_mod_cast this.ne'
  have hid : (m.choose i : ℚ) * ((m : ℚ) + 1)
      = ((m + 1).choose i : ℚ) * ((m + 1 - i : ℕ) : ℚ) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_mul_succ_eq m i)
    push_cast at h
    linarith [h]
  rw [show bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m : ℚ) + 1)
        = bernoulli i * (p : ℚ) ^ (m + 1 - i) * (((m + 1).choose i : ℚ) / ((m : ℚ) + 1)) by ring,
      show bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m + 1 - i : ℕ) : ℚ)
        = bernoulli i * (p : ℚ) ^ (m + 1 - i)
            * ((m.choose i : ℚ) / ((m + 1 - i : ℕ) : ℚ)) by ring]
  congr 1
  rw [div_eq_div_iff hd1 hd2]
  linarith [hid]

/-- The key equation `(★)`: for `m ≥ 1`,
`bernoulli m * p = (∑_{k<p} k^m) - ∑_{i<m} (good-form correction term)`. -/
lemma key_eq (m : ℕ) (hm : 1 ≤ m) :
    bernoulli m * (p : ℚ)
      = (∑ k ∈ range p, (k : ℚ) ^ m)
        - ∑ i ∈ range m,
            bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m + 1 - i : ℕ) : ℚ) := by
  have hfaul := sum_range_pow p m
  rw [Finset.sum_range_succ] at hfaul
  have hlast : bernoulli m * ((m + 1).choose m : ℚ) * (p : ℚ) ^ (m + 1 - m) / ((m : ℚ) + 1)
      = bernoulli m * (p : ℚ) := by
    rw [Nat.choose_succ_self_right, show m + 1 - m = 1 by omega]
    push_cast
    field_simp
  have hcongr : (∑ i ∈ range m,
        bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m : ℚ) + 1))
      = ∑ i ∈ range m,
          bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m + 1 - i : ℕ) : ℚ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact term_eq (Nat.le_of_lt (Finset.mem_range.mp hi))
  rw [hlast, hcongr] at hfaul
  linarith [hfaul]

/-- The power sum over `range p` equals the sum over all of `ZMod p`. -/
lemma sum_range_pow_zmod (m : ℕ) :
    (∑ k ∈ range p, ((k : ℕ) : ZMod p) ^ m) = ∑ x : ZMod p, x ^ m := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine (Finset.sum_bij' (fun x _ => ZMod.val x) (fun k _ => ((k : ℕ) : ZMod p))
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x)) (fun k _ => Finset.mem_univ _)
    (fun x _ => ZMod.natCast_zmod_val x)
    (fun k hk => ZMod.val_cast_of_lt (Finset.mem_range.mp hk)) ?_).symm
  intro x _
  rw [ZMod.natCast_zmod_val]

/-- For `m ≥ 1` with `(p - 1) ∤ m`, the sum of `m`-th powers over `ZMod p` vanishes. -/
lemma sum_pow_univ_zmod (m : ℕ) (hm : 1 ≤ m) (hdvd : ¬ (p - 1) ∣ m) :
    (∑ x : ZMod p, x ^ m) = 0 := by
  classical
  have hzero : ∑ x : ZMod p, x ^ m = ∑ x ∈ (univ \ {0} : Finset (ZMod p)), x ^ m := by
    rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))), Finset.sum_singleton,
      zero_pow (by omega : m ≠ 0), add_zero]
  rw [hzero]
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x => x, Units.val_injective⟩
  have hmap : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using isUnit_iff_ne_zero
  rw [← hmap, Finset.sum_map]
  simp only [φ, Function.Embedding.coeFn_mk]
  rw [FiniteField.sum_pow_units (ZMod p) m, ZMod.card, if_neg hdvd]

/-- Extract a lower bound on `padicValRat` from an upper bound on the `ℚ_[p]`-norm. -/
private lemma valRat_ge_of_norm_le {q : ℚ} {n : ℤ} (hq : q ≠ 0)
    (h : ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n)) : n ≤ padicValRat p q := by
  have hne : ((q : ℚ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hq
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_ratCast] at h
  rw [zpow_le_zpow_iff_right₀ hp1] at h
  omega

/-- **von Staudt–Clausen valuation bound (ℚ_[p]-norm form).** For an odd prime `p ≥ 5`,
`‖bernoulli m‖_p ≤ p`. -/
theorem norm_bernoulli_le (hp5 : 5 ≤ p) (m : ℕ) :
    ‖((bernoulli m : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hpR : (0 : ℝ) < (p : ℝ) := by
      have : (0 : ℕ) < p := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have : (1 : ℕ) ≤ p := by omega
      exact_mod_cast this
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- m = 0
      rw [bernoulli_zero]
      simpa using hp1
    · -- m ≥ 1
      -- bound on the power sum `S`
      have hS : ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])‖ ≤ 1 := by
        rw [Rat.cast_sum]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) ?_
        intro k _
        rw [Rat.cast_pow, Rat.cast_natCast, norm_pow]
        calc ‖(k : ℚ_[p])‖ ^ m ≤ 1 ^ m := by gcongr; exact norm_nat_le_one k
          _ = 1 := one_pow m
      -- bound on the correction sum
      have hC : ‖((∑ i ∈ range m,
            bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
              / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
        rw [Rat.cast_sum]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
        intro i hi
        exact term_norm_le hp5 (Finset.mem_range.mp hi) (ih i (Finset.mem_range.mp hi))
      -- combine using (★)
      have hcast := congrArg (Rat.cast : ℚ → ℚ_[p]) (key_eq (p := p) m hm)
      rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub] at hcast
      have hcombine : ‖((bernoulli m : ℚ) : ℚ_[p]) * (p : ℚ_[p])‖ ≤ 1 := by
        rw [hcast]
        have hmax :
            ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])
              - ((∑ i ∈ range m,
                  bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
                    / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖
            ≤ max ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])‖
                ‖((∑ i ∈ range m,
                    bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
                      / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ := by
          have h := Padic.nonarchimedean
            ((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])
            (-((∑ i ∈ range m,
                bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
                  / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p]))
          rwa [← sub_eq_add_neg, norm_neg] at h
        refine hmax.trans (max_le hS ?_)
        exact hC.trans (by simpa using (inv_le_one_of_one_le₀ hp1))
      rw [norm_mul, Padic.norm_p, ← div_eq_mul_inv, div_le_one hpR] at hcombine
      exact hcombine

/-- **von Staudt–Clausen: `p`-integrality of Bernoulli numbers (ℚ_[p]-norm form).**
For an odd prime `p ≥ 5` and `(p - 1) ∤ m`, we have `‖bernoulli m‖_p ≤ 1`. -/
theorem norm_bernoulli_le_one_of_not_dvd (hp5 : 5 ≤ p) (m : ℕ) (hdvd : ¬ (p - 1) ∣ m) :
    ‖((bernoulli m : ℚ) : ℚ_[p])‖ ≤ 1 := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (dvd_zero _) hdvd
    · exact h
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  -- The power sum `S` is divisible by `p`, so its norm is at most `p⁻¹`.
  have hS : ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    have hnatdvd : p ∣ ∑ k ∈ range p, k ^ m := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [sum_range_pow_zmod]
      exact sum_pow_univ_zmod m hm hdvd
    have hNeq : ((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])
        = (((∑ k ∈ range p, k ^ m : ℕ) : ℤ) : ℚ_[p]) := by
      push_cast; ring
    rw [hNeq]
    have hdvd2 : ((p : ℤ) ^ 1) ∣ ((∑ k ∈ range p, k ^ m : ℕ) : ℤ) := by
      simpa using (Int.natCast_dvd_natCast.mpr hnatdvd)
    have key := (Padic.norm_int_le_pow_iff_dvd (p := p)
      ((∑ k ∈ range p, k ^ m : ℕ) : ℤ) 1).mpr hdvd2
    rwa [Nat.cast_one, zpow_neg_one] at key
  -- The correction sum has norm at most `p⁻¹` (using the already-proven bound for `i < m`).
  have hC : ‖((∑ i ∈ range m,
        bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
          / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [Rat.cast_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
    intro i hi
    exact term_norm_le hp5 (Finset.mem_range.mp hi) (norm_bernoulli_le hp5 i)
  -- combine using (★)
  have hcast := congrArg (Rat.cast : ℚ → ℚ_[p]) (key_eq (p := p) m hm)
  rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub] at hcast
  have hcombine : ‖((bernoulli m : ℚ) : ℚ_[p]) * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [hcast]
    have hmax :
        ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])
          - ((∑ i ∈ range m,
              bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
                / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖
        ≤ max ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])‖
            ‖((∑ i ∈ range m,
                bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
                  / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ := by
      have h := Padic.nonarchimedean
        ((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])
        (-((∑ i ∈ range m,
            bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
              / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p]))
      rwa [← sub_eq_add_neg, norm_neg] at h
    exact hmax.trans (max_le hS hC)
  rw [norm_mul, Padic.norm_p] at hcombine
  have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  exact le_of_mul_le_mul_right (by rwa [one_mul]) hpinv

/-- **von Staudt–Clausen valuation bound.** For an odd prime `p ≥ 5` and any `m`,
`padicValRat p (bernoulli m) ≥ -1`. -/
theorem padicValRat_bernoulli_ge (hp5 : 5 ≤ p) (m : ℕ) :
    (-1 : ℤ) ≤ padicValRat p (bernoulli m) := by
  rcases eq_or_ne (bernoulli m) 0 with h0 | h0
  · rw [h0, padicValRat.zero]; norm_num
  · exact valRat_ge_of_norm_le h0 (by rw [neg_neg, zpow_one]; exact norm_bernoulli_le hp5 m)

/-- **von Staudt–Clausen: `p`-integrality.** For an odd prime `p ≥ 5` and `(p - 1) ∤ m`,
`padicValRat p (bernoulli m) ≥ 0`. -/
theorem padicValRat_bernoulli_nonneg (hp5 : 5 ≤ p) (m : ℕ) (hdvd : ¬ (p - 1) ∣ m) :
    (0 : ℤ) ≤ padicValRat p (bernoulli m) := by
  rcases eq_or_ne (bernoulli m) 0 with h0 | h0
  · rw [h0, padicValRat.zero]
  · exact valRat_ge_of_norm_le h0
      (by rw [neg_zero, zpow_zero]; exact norm_bernoulli_le_one_of_not_dvd hp5 m hdvd)

end VonStaudt
