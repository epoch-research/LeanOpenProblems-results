import FormalConjectures.Util.ProblemImports
open Finset Nat Set
open Filter Asymptotics
open scoped Topology

lemma centralBinom_le_pow_primeCounting (n : ℕ) (hn : 0 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  classical
  let S := (Finset.range (2 * n + 1)).filter Nat.Prime
  have hfilter : ∏ p ∈ S, p ^ n.centralBinom.factorization p =
      ∏ p ∈ Finset.range (2 * n + 1), p ^ n.centralBinom.factorization p := by
    exact Finset.prod_filter_of_ne (s := Finset.range (2 * n + 1)) (p := Nat.Prime)
      (f := fun p => p ^ n.centralBinom.factorization p)
      (fun p hp hne => by
        by_contra hprime
        dsimp at hne
        rw [Nat.factorization_eq_zero_of_not_prime _ hprime, pow_zero] at hne
        exact hne rfl)
  have hprod : n.centralBinom = ∏ p ∈ S, p ^ n.centralBinom.factorization p := by
    exact (Nat.prod_pow_factorization_centralBinom n).symm.trans hfilter.symm
  rw [hprod]
  calc
    ∏ p ∈ S, p ^ n.centralBinom.factorization p
        ≤ ∏ p ∈ S, (2 * n) := by
          refine Finset.prod_le_prod' ?_
          intro p hp
          exact Nat.pow_factorization_choose_le (p := p) (n := 2 * n) (k := n) (mul_pos (by decide) hn)
    _ = (2 * n) ^ S.card := by rw [Finset.prod_const]
    _ = (2 * n) ^ Nat.primeCounting (2 * n) := by
      congr 1
      simp [S, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

example (n : ℕ) (hn : 4 ≤ n) :
    (4 : ℝ) ^ n < (n : ℝ) * ((2*n : ℕ) : ℝ) ^ Nat.primeCounting (2*n) := by
  have h1 := Nat.four_pow_lt_mul_centralBinom n hn
  have h2 := centralBinom_le_pow_primeCounting n (lt_of_lt_of_le (by decide) hn)
  exact_mod_cast (lt_of_lt_of_le h1 (Nat.mul_le_mul_left n h2))

lemma primeCounting_mul_log_lower (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n <
      (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * n : ℕ) := by
  have hpow : (4 : ℝ) ^ n < (n : ℝ) * ((2*n : ℕ) : ℝ) ^ Nat.primeCounting (2*n) := by
    have h1 := Nat.four_pow_lt_mul_centralBinom n hn
    have h2 := centralBinom_le_pow_primeCounting n (lt_of_lt_of_le (by decide) hn)
    exact_mod_cast (lt_of_lt_of_le h1 (Nat.mul_le_mul_left n h2))
  have hposL : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
  have hposR : 0 < (n : ℝ) * ((2*n : ℕ) : ℝ) ^ Nat.primeCounting (2*n) := by
    positivity
  have hlog := Real.log_lt_log hposL hpow
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  nlinarith

lemma eventually_primeCounting_even_lower (c : ℝ) (hc : c < Real.log 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      c * ((2 * n : ℕ) : ℝ) / Real.log ((2 * n : ℕ) : ℝ) ≤ Nat.primeCounting (2 * n) := by
  have hlim : Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (𝓝 0) := by
    have hgf : ∀ᶠ x : ℝ in Filter.atTop, id x = 0 → Real.log x = 0 := by
      filter_upwards [eventually_ne_atTop (0:ℝ)] with x hx h0
      exact False.elim (hx h0)
    simpa [id] using ((Asymptotics.isLittleO_iff_tendsto' (f := Real.log) (g := id) hgf).mp Real.isLittleO_log_id_atTop)
  have hpos : 0 < (Real.log 2 - c) / 4 := by
    exact div_pos (sub_pos.mpr hc) (by norm_num)
  have hlim_nat := (hlim.comp tendsto_natCast_atTop_atTop)
  have hev0 : ∀ᶠ n : ℕ in Filter.atTop, |Real.log (n : ℝ)| / (n : ℝ) < (Real.log 2 - c) / 4 := by
    simpa [Function.comp, Real.dist_eq, dist_eq_norm] using (Metric.tendsto_nhds.mp hlim_nat) _ hpos
  have hev : ∀ᶠ n : ℕ in Filter.atTop, |Real.log (n : ℝ) / (n : ℝ)| < (Real.log 2 - c) / 4 := by
    filter_upwards [hev0, eventually_ge_atTop 1] with n hn hge
    rw [abs_div]
    change |Real.log (n : ℝ)| / |(n : ℝ)| < (Real.log 2 - c) / 4
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast (Nat.zero_le n))]
    exact hn
  filter_upwards [eventually_ge_atTop 4, hev] with n hn hsmall
  have hlogpos : 0 < Real.log ((2 * n : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < 2 * n)
  have hmain := primeCounting_mul_log_lower n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hn)
  have h2npos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by positivity
  have hratio : Real.log (n : ℝ) / (n : ℝ) < (Real.log 2 - c) / 4 := by
    exact lt_of_le_of_lt (le_abs_self _) hsmall
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  -- From hmain: n*log4 - log n < pc*log(2n).
  -- It suffices to show c*(2n) <= n*log4 - log n.
  have hleft : c * ((2 * n : ℕ) : ℝ) < (n : ℝ) * Real.log 4 - Real.log n := by
    rw [hlog4]
    have hdcpos : 0 < Real.log 2 - c := sub_pos.mpr hc
    have hlogsmall : Real.log (n : ℝ) < (n : ℝ) * (Real.log 2 - c) := by
      have hmul := mul_lt_mul_of_pos_right hratio hnpos
      rw [div_mul_cancel₀ _ (ne_of_gt hnpos)] at hmul
      nlinarith [mul_pos hnpos hdcpos]
    norm_num
    nlinarith
  have hpcnonneg : (0 : ℝ) ≤ Nat.primeCounting (2 * n) := by exact_mod_cast Nat.zero_le _
  have hineq : c * ((2 * n : ℕ) : ℝ) < (Nat.primeCounting (2 * n) : ℝ) * Real.log ((2 * n : ℕ) : ℝ) := by
    exact lt_trans hleft hmain
  rw [div_le_iff₀ hlogpos]
  exact le_of_lt hineq
