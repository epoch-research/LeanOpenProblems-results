import Submission.FiniteBlockClearing
import Submission.ScaledDenominatorRoughness

/-!
Uniform reduced-denominator bounds for finite blocks of reciprocal
factorial-minus-one rows. These auxiliary results do not settle Erdős 68.
-/

namespace UniformBlockClearing

open Filter FiniteBlockClearing Erdos68Development

lemma block_den_coprime (k J : ℕ) (hk : 2 ≤ k) :
    Nat.Coprime k.factorial (block k J).den := by
  rw [block_eq_sum]
  apply ScaledDenominatorRoughness.coprime_sum_den
  intro i hi
  have hf : 1 < (k + i).factorial := Nat.one_lt_factorial.mpr (by omega)
  have he : ((k + i).factorial - 1 : ℚ) = ↑((k + i).factorial - 1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [he, one_div, Rat.inv_natCast_den_of_pos (by omega)]
  exact ScaledDenominatorRoughness.factorial_pred_coprime (by omega)

lemma block_cast (k J : ℕ) (hk : 2 ≤ k) :
    (block k J : ℝ) = ∑ i ∈ Finset.range (J + 1), term (k - 2 + i) := by
  rw [block_eq_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [term, show k - 2 + i + 2 = k + i by omega]

lemma block_bounds (k J : ℕ) (hk : 2 ≤ k) :
    0 < (block k J : ℝ) ∧ (block k J : ℝ) < 2 / (k.factorial - 1 : ℝ) := by
  rw [block_cast k J hk]
  have hs : Summable (fun i => term (k - 2 + i)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff (k - 2)).mpr summable_term
  constructor
  · exact Finset.sum_pos (fun i _ => term_pos _) (by simp)
  · calc
      _ ≤ ∑' i : ℕ, term (k - 2 + i) :=
        hs.sum_le_tsum _ (fun i _ => (term_pos _).le)
      _ ≤ (3 / 2 : ℝ) * term (k - 2) := (tail_bounds (k - 2)).2
      _ < 2 / (k.factorial - 1 : ℝ) := by
        have hp := term_pos (k - 2)
        simp only [term, Nat.sub_add_cancel hk] at hp ⊢
        calc
          _ < 2 * (1 / (k.factorial - 1 : ℝ)) :=
            mul_lt_mul_of_pos_right (by norm_num) hp
          _ = _ := by ring

lemma block_den_lower_bound (k J : ℕ) (hk : 2 ≤ k) :
    k.factorial - 1 < 2 * (block k J).den := by
  let q := block k J
  have hb := block_bounds k J hk
  have hqpos : 0 < q := by exact_mod_cast hb.1
  have hnum : (1 : ℝ) ≤ q.num := by exact_mod_cast Rat.num_pos.mpr hqpos
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hfac : (0 : ℝ) < k.factorial - 1 := by
    have hh : (1 : ℝ) < k.factorial := by exact_mod_cast Nat.one_lt_factorial.mpr hk
    linarith
  have he : (q : ℝ) * q.den = q.num := by
    have hh := Rat.num_div_den q
    have hh' : (q.num : ℝ) / q.den = q := by exact_mod_cast hh
    exact (div_eq_iff hden.ne').mp hh' |>.symm
  have hmul := mul_lt_mul_of_pos_right hb.2 hden
  have hl : (k.factorial : ℝ) - 1 < 2 * q.den := by
    rw [show 2 / (k.factorial - 1 : ℝ) * q.den =
      (2 * q.den) / (k.factorial - 1 : ℝ) by ring] at hmul
    have hh := (lt_div_iff₀ hfac).mp hmul
    change (q : ℝ) * q.den * (k.factorial - 1 : ℝ) < _ at hh
    rw [he] at hh
    nlinarith
  have hefac : ((k.factorial - 1 : ℕ) : ℝ) = k.factorial - 1 := by
    rw [Nat.cast_sub (Nat.factorial_pos k), Nat.cast_one]
  rw [← hefac] at hl
  exact_mod_cast hl

lemma block_clearing_forces_bound (C k J : ℕ) (hk : 2 ≤ k)
    (h : (block k J).den ∣ (C * k).factorial) :
    k.factorial - 1 < 2 * 2 ^ (C ^ 2 * k) := by
  rw [← FactorialClearingIndex.blockCoefficient_identity] at h
  have hd := ((block_den_coprime k J hk).symm.pow_right C).dvd_of_dvd_mul_right h
  have hb := Nat.le_of_dvd (FactorialClearingIndex.blockCoefficient_pos C k) hd
  exact (block_den_lower_bound k J hk).trans_le
    (Nat.mul_le_mul_left 2 (hb.trans (FactorialClearingIndex.blockCoefficient_bound C k)))

/-- The threshold is independent of the number of terms in the block. -/
theorem eventual_reduced_clearing_index_gt_linear (C : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ J N : ℕ,
      (block k J).den ∣ N.factorial → C * k < N := by
  filter_upwards [eventually_ge_atTop 2,
    Nat.eventually_mul_pow_lt_factorial_sub 4 (2 ^ (C ^ 2)) 0] with k hk hb
  simp only [Nat.sub_zero, ← pow_mul] at hb
  intro J N hN
  by_contra hn
  have hh := block_clearing_forces_bound C k J hk
    (hN.trans (Nat.factorial_dvd_factorial (by omega)))
  have he := Nat.sub_add_cancel (Nat.factorial_pos k)
  omega

#print axioms eventual_reduced_clearing_index_gt_linear

lemma block_den_dvd_of_prefix_den_dvd (k l M : ℕ) (hkl : k < l)
    (hk : (partialSum k).den ∣ M) (hl : (partialSum l).den ∣ M) :
    (block k (l - k - 1)).den ∣ M := by
  have he : block k (l - k - 1) = partialSum l - partialSum k := by
    have hh := prefix_add k (l - k - 1)
    rw [show k + (l - k - 1) + 1 = l by omega] at hh
    linarith
  rw [he]
  exact (Rat.sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd hl hk)

/-- No divergent cutoffs, even nonmonotone ones with unbounded jumps, can
have proportionally bounded scaling indices and integrally cleared prefixes. -/
theorem no_proportional_cutoff (K : ℕ → ℕ) (C N : ℕ)
    (hK : Tendsto K atTop atTop)
    (hlinear : ∀ n ≥ N, n ≤ C * K n)
    (hclear : ∀ n ≥ N, (partialSum (K n)).den ∣ n.factorial) : False := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    (hK.eventually (eventual_reduced_clearing_index_gt_linear (C + 1)))
  have hstable : ∀ᶠ n : ℕ in atTop, K (n + 1) = K n := by
    filter_upwards [eventually_ge_atTop (max a N), hK.eventually_ge_atTop 1]
      with n hn hkpos
    have hnN : N ≤ n := (le_max_right a N).trans hn
    have hna : a ≤ n := (le_max_left a N).trans hn
    have hc : (partialSum (K n)).den ∣ (n + 1).factorial :=
      (hclear n hnN).trans (Nat.factorial_dvd_factorial (by omega))
    have hc' := hclear (n + 1) (by omega)
    rcases lt_trichotomy (K n) (K (n + 1)) with hlt | heq | hgt
    · have hd := block_den_dvd_of_prefix_den_dvd _ _ _ hlt hc hc'
      have hh := ha n hna _ (n + 1) hd
      have hb := hlinear n hnN
      nlinarith
    · exact heq.symm
    · have hd := block_den_dvd_of_prefix_den_dvd _ _ _ hgt hc' hc
      have hh := ha (n + 1) (by omega) _ (n + 1) hd
      have hb := hlinear (n + 1) (by omega)
      nlinarith
  obtain ⟨b, hb⟩ := eventually_atTop.mp hstable
  have hconst : ∀ n ≥ b, K n = K b := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [hb n hn, ih]
  obtain ⟨n, hn, hkn⟩ := ((eventually_ge_atTop b).and
    (hK.eventually_ge_atTop (K b + 1))).exists
  rw [hconst n hn] at hkn
  omega

#print axioms no_proportional_cutoff


end UniformBlockClearing
