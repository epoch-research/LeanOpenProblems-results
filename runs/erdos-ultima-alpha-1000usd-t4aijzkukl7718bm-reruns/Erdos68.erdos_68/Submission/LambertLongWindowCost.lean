import Submission.LambertCoefficientWindowGcd

/-! Auxiliary lower bounds on lifting a coefficient-window gcd. These are
not a proof or disproof of the irrationality conjecture. -/

namespace LambertLongWindowCost

open Finset Erdos68Development LambertCoefficientWindowGcd

noncomputable def rowTwo (n : ℕ) : ℝ :=
  if 2 ∣ n then 1 / (2 : ℝ)^(n/2) else 0

noncomputable def otherRows (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, if 3 ≤ d then 1 / (d.factorial : ℝ)^(n/d) else 0

lemma coefficient_split (n : ℕ) (hn : 0 < n) :
    (lambertCoeff n : ℝ) / n.factorial = rowTwo n + otherRows n := by
  rw [lambertCoeff_cast_div]
  have hs : (∑ d ∈ n.divisors,
      if d = 2 then 1 / (2 : ℝ)^(n/2) else 0) = rowTwo n := by
    simp [rowTwo, Nat.mem_divisors, hn.ne']
  rw [← hs, otherRows, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  by_cases h2 : d = 2
  · subst d; norm_num
  · by_cases h3 : 3 ≤ d
    · simp [h2, h3, show 2 ≤ d by omega]
    · simp [h2, h3, show ¬2 ≤ d by omega]

lemma rate_le_factorial (d : ℕ) (hd : 3 ≤ d) :
    (9/5 : ℝ)^d ≤ d.factorial := by
  induction d, hd using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ d hd ih =>
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hdR : (9/5 : ℝ) ≤ d+1 := by
      have hdR : (3:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    calc
      (9/5 : ℝ)^d * (9/5) ≤ (d.factorial : ℝ) * (9/5) := by gcongr
      _ ≤ (d.factorial : ℝ)*(d+1) := by gcongr
      _ = _ := by ring

lemma otherRows_bound (n : ℕ) :
    0 ≤ otherRows n ∧ otherRows n ≤ (n+1 : ℝ)*(5/9 : ℝ)^n := by
  have hsum : otherRows n ≤ ∑ _d ∈ n.divisors, (5/9 : ℝ)^n := by
    apply sum_le_sum
    intro d hd
    by_cases hd3 : 3 ≤ d
    · rw [if_pos hd3]
      have he := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (9/5)^d)
        (rate_le_factorial d hd3) (n/d)
      rw [← pow_mul, he] at hpow
      have hb : (5/9 : ℝ)^n = 1 / (9/5 : ℝ)^n := by
        rw [← one_div_pow]; congr 1; norm_num
      rw [hb]
      exact one_div_le_one_div_of_le (by positivity) hpow
    · rw [if_neg hd3]; positivity
  have hc : n.divisors.card ≤ n+1 := by
    rw [← card_range (n+1)]
    apply card_le_card
    intro d hd
    apply mem_range.mpr
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
      (Nat.dvd_of_mem_divisors hd)
    omega
  refine ⟨by unfold otherRows; positivity, ?_⟩
  calc
    otherRows n ≤ _ := hsum
    _ = (n.divisors.card : ℝ)*(5/9 : ℝ)^n := by simp
    _ ≤ (n+1 : ℝ)*(5/9 : ℝ)^n := by
      gcongr
      exact_mod_cast hc

lemma scaled_cast (p r i : ℕ) (hi : i ≤ r) :
    (scaled p r i : ℝ) =
      ((p+r).factorial : ℝ) * ((lambertCoeff (p+i) : ℝ)/(p+i).factorial) := by
  rw [scaled, Nat.cast_mul,
    Nat.cast_div_charZero (Nat.factorial_dvd_factorial (by omega : p+i ≤ p+r))]
  ring

lemma even_coefficient_odd (n : ℕ) (hn : 2 ≤ n) (he : 2 ∣ n) :
    lambertCoeff n % 2 = 1 := by
  have h := lambertCoeff_modEq_minFac_factorial hn
  rw [(Nat.minFac_eq_two_iff n).mpr he] at h
  simpa only [Nat.factorial, Nat.ModEq, Nat.reduceMul, Nat.one_mod] using h

lemma even_windowGcd_odd (p r : ℕ) (hp : p.Prime) (he : 2 ∣ p+r) :
    windowGcd p r % 2 = 1 := by
  have ha := even_coefficient_odd (p+r) (by have := hp.two_le; omega) he
  have hd : windowGcd p r ∣ lambertCoeff (p+r) := by
    rw [windowGcd_eq p r hp]; exact Nat.gcd_dvd_left _ _
  have hnd : ¬2 ∣ windowGcd p r := by
    intro h; have := h.trans hd; omega
  omega

lemma scaled_even_before_last (p r i : ℕ) (he : 2 ∣ p+r) (hi : i < r) :
    2 ∣ scaled p r i := by
  have hN : 0 < p+r := by omega
  have hfac : (p+i).factorial ∣ (p+r-1).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  have heq : (p+r).factorial / (p+i).factorial =
      (p+r)*((p+r-1).factorial / (p+i).factorial) := by
    conv_lhs => rw [show p+r = (p+r-1)+1 by omega, Nat.factorial_succ]
    rw [show p+r-1+1 = p+r by omega, Nat.mul_div_assoc _ hfac]
  rw [scaled, heq]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left he _) _

lemma last_weight_odd (p r : ℕ) (hp : p.Prime) (he : 2 ∣ p+r)
    (w : ℕ → ℤ)
    (hw : (windowGcd p r : ℤ) = ∑ i ∈ range (r+1), w i*(scaled p r i : ℤ)) :
    ¬(2 : ℤ) ∣ w r := by
  intro hd
  have hs : (2 : ℤ) ∣ ∑ i ∈ range (r+1), w i*(scaled p r i : ℤ) := by
    apply Finset.dvd_sum
    intro i hi
    by_cases hir : i = r
    · subst i; exact dvd_mul_of_dvd_left hd _
    · have hie : i < r := by have := mem_range.mp hi; omega
      have hh : (2 : ℤ) ∣ (scaled p r i : ℤ) := by
        exact_mod_cast scaled_even_before_last p r i he hie
      exact dvd_mul_of_dvd_right hh _
  rw [← hw] at hs
  have hsN : 2 ∣ windowGcd p r := by exact_mod_cast hs
  have ho := even_windowGcd_odd p r hp he
  omega

lemma rowTwo_separation (p r : ℕ) (he : 2 ∣ p+r) (w : ℕ → ℤ)
    (hw : ¬(2 : ℤ) ∣ w r) :
    1 ≤ (2 : ℝ)^((p+r)/2) * |∑ i ∈ range (r+1), (w i : ℝ)*rowTwo (p+i)| := by
  let z : ℤ := ∑ i ∈ range (r+1),
    if 2 ∣ p+i then w i*2^((p+r)/2-(p+i)/2) else 0
  have hz : ¬(2 : ℤ) ∣ z := by
    have hfirst : (2 : ℤ) ∣ ∑ i ∈ range r,
        if 2 ∣ p+i then w i*2^((p+r)/2-(p+i)/2) else 0 := by
      apply Finset.dvd_sum
      intro i hi
      by_cases hie : 2 ∣ p+i
      · rw [if_pos hie]
        have hi' := mem_range.mp hi
        have hexp : (p+r)/2-(p+i)/2 ≠ 0 := by omega
        exact dvd_mul_of_dvd_right (dvd_pow_self (2:ℤ) hexp) _
      · simp [hie]
    have heq : z = (∑ i ∈ range r,
        if 2 ∣ p+i then w i*2^((p+r)/2-(p+i)/2) else 0) + w r := by
      simp [z, sum_range_succ, he]
    rw [heq]
    exact fun h => hw ((dvd_add_right hfirst).mp h)
  have hz0 : z ≠ 0 := by intro h; exact hz (h ▸ dvd_zero _)
  have hbound : (1 : ℝ) ≤ |(z : ℝ)| := by
    have hh : (1 : ℤ) ≤ |z| := by
      have := abs_pos.mpr hz0
      omega
    exact_mod_cast hh
  have heq : (z : ℝ) = (2 : ℝ)^((p+r)/2) *
      (∑ i ∈ range (r+1), (w i : ℝ)*rowTwo (p+i)) := by
    rw [mul_sum]
    simp only [z, Int.cast_sum]
    apply sum_congr rfl
    intro i hi
    have hie : i ≤ r := by have := mem_range.mp hi; omega
    by_cases hi2 : 2 ∣ p+i
    · simp only [if_pos hi2, rowTwo, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      have hle : (p+i)/2 ≤ (p+r)/2 := by omega
      have hpow : (2:ℝ)^((p+r)/2-(p+i)/2) * 2^((p+i)/2) =
          2^((p+r)/2) := by rw [← pow_add, Nat.sub_add_cancel hle]
      have hne : (2:ℝ)^((p+i)/2) ≠ 0 := by positivity
      field_simp
      nlinarith [congrArg (fun x : ℝ => (w i : ℝ)*x) hpow]
    · simp [hi2, rowTwo]
  rw [heq, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2^((p+r)/2))] at hbound
  exact hbound

lemma otherRows_weighted_bound (p r : ℕ) (w : ℕ → ℤ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i ≤ r, |(w i : ℝ)| ≤ W) :
    |∑ i ∈ range (r+1), (w i : ℝ)*otherRows (p+i)| ≤
      W*(r+1)*(p+r+1)*(5/9 : ℝ)^p := by
  calc
    _ ≤ ∑ i ∈ range (r+1), |(w i : ℝ)*otherRows (p+i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range (r+1), W*(p+r+1)*(5/9 : ℝ)^p := by
      apply sum_le_sum
      intro i hi
      have hie : i ≤ r := by have := mem_range.mp hi; omega
      rw [abs_mul, abs_of_nonneg (otherRows_bound (p+i)).1]
      have hnp : (p+i+1 : ℝ) ≤ p+r+1 := by exact_mod_cast (show p+i+1 ≤ p+r+1 by omega)
      have hpow : (5/9 : ℝ)^(p+i) ≤ (5/9 : ℝ)^p :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      calc
        _ ≤ W * ((p+i+1 : ℝ)*(5/9 : ℝ)^(p+i)) := by
          gcongr
          · exact (otherRows_bound (p+i)).1
          · exact hw i hie
          · simpa only [Nat.cast_add] using (otherRows_bound (p+i)).2
        _ ≤ W * ((p+r+1 : ℝ)*(5/9 : ℝ)^p) := by gcongr
        _ = _ := by ring
    _ = _ := by simp; ring

/-- The parity obstruction survives signed weights in any prime-starting
window with an even final index. The displayed estimate retains all of the
other Lambert rows, rather than discarding their possible cancellations. -/
theorem gcd_lift_lower_bound (p r : ℕ) (hp : p.Prime) (he : 2 ∣ p+r)
    (w : ℕ → ℤ) (W : ℝ) (hW : 0 ≤ W)
    (hweights : ∀ i ≤ r, |(w i : ℝ)| ≤ W)
    (hw : (windowGcd p r : ℤ) = ∑ i ∈ range (r+1), w i*(scaled p r i : ℤ)) :
    1 ≤ (2 : ℝ)^((p+r)/2) *
      ((windowGcd p r : ℝ)/(p+r).factorial +
        W*(r+1)*(p+r+1)*(5/9 : ℝ)^p) := by
  have hsep := rowTwo_separation p r he w (last_weight_odd p r hp he w hw)
  have heq : (windowGcd p r : ℝ)/(p+r).factorial =
      (∑ i ∈ range (r+1), (w i : ℝ)*rowTwo (p+i)) +
      (∑ i ∈ range (r+1), (w i : ℝ)*otherRows (p+i)) := by
    have hcast : (windowGcd p r : ℝ) =
        ∑ i ∈ range (r+1), (w i : ℝ)*(scaled p r i : ℝ) := by exact_mod_cast hw
    rw [hcast, sum_div, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hie : i ≤ r := by have := mem_range.mp hi; omega
    rw [scaled_cast p r i hie, coefficient_split (p+i) (by have := hp.pos; omega)]
    have hne : ((p+r).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have htri : |∑ i ∈ range (r+1), (w i : ℝ)*rowTwo (p+i)| ≤
      (windowGcd p r : ℝ)/(p+r).factorial +
        W*(r+1)*(p+r+1)*(5/9 : ℝ)^p := by
    have ht := abs_sub ((windowGcd p r : ℝ)/(p+r).factorial)
      (∑ i ∈ range (r+1), (w i : ℝ)*otherRows (p+i))
    rw [heq, add_sub_cancel_right] at ht
    rw [← heq, abs_of_nonneg (by positivity : (0:ℝ) ≤
      (windowGcd p r : ℝ)/(p+r).factorial)] at ht
    exact ht.trans (add_le_add le_rfl (otherRows_weighted_bound p r w W hW hweights))
  exact hsep.trans (mul_le_mul_of_nonneg_left htri (by positivity))

lemma gcd_scaled_small (p r : ℕ) (hp : p.Prime) (he : 2 ∣ p+r)
    (hN : 4 ≤ p+r) :
    (2 : ℝ)^((p+r)/2) * ((windowGcd p r : ℝ)/(p+r).factorial) ≤ 1/2 := by
  have hg0 := windowGcd_pos p r hp
  have hodd := even_windowGcd_odd p r hp he
  have hne : windowGcd p r ≠ p+r := by omega
  obtain ⟨k, hk⟩ := windowGcd_dvd_index p r hp
  have hk2 : 2 ≤ k := by
    by_contra h
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with rfl | rfl <;> simp_all
  have htwog : 2*windowGcd p r ≤ p+r := by
    nlinarith
  have hf := even_factorial_lower ((p+r)/2-2)
  have heq : 2*(((p+r)/2-2)+2) = p+r := by omega
  have hexp : (p+r)/2-2+2 = (p+r)/2 := by omega
  rw [heq, hexp] at hf
  have hle : 2*windowGcd p r*2^((p+r)/2) ≤ (p+r).factorial :=
    (Nat.mul_le_mul_right _ htwog).trans hf
  have hleR : 2*(windowGcd p r : ℝ)*2^((p+r)/2) ≤ (p+r).factorial := by
    exact_mod_cast hle
  have hfac : (0 : ℝ) < (p+r).factorial := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hfac]
  linarith

/-- A quantitative signed lifting cost for all even-ended windows. In
particular, for N=p+r at most 3p/2, its exponential ratio prevents
polynomial-size full weight bounds as p grows. -/
theorem gcd_lift_weight_cost (p r : ℕ) (hp : p.Prime) (he : 2 ∣ p+r)
    (hN : 4 ≤ p+r) (w : ℕ → ℤ) (W : ℝ) (hW : 0 ≤ W)
    (hweights : ∀ i ≤ r, |(w i : ℝ)| ≤ W)
    (hw : (windowGcd p r : ℤ) = ∑ i ∈ range (r+1), w i*(scaled p r i : ℤ)) :
    (9/5 : ℝ)^p ≤ (2 : ℝ)^((p+r)/2+1)*W*(r+1)*(p+r+1) := by
  have h := gcd_lift_lower_bound p r hp he w W hW hweights hw
  have hs := gcd_scaled_small p r hp he hN
  have ht : (1/2 : ℝ) ≤ (2 : ℝ)^((p+r)/2)*
      (W*(r+1)*(p+r+1)*(5/9 : ℝ)^p) := by nlinarith
  have hprod : (5/9 : ℝ)^p*(9/5 : ℝ)^p = 1 := by
    rw [← mul_pow]; norm_num
  calc
    (9/5 : ℝ)^p = 2*(1/2 : ℝ)*(9/5 : ℝ)^p := by ring
    _ ≤ 2*((2 : ℝ)^((p+r)/2)*(W*(r+1)*(p+r+1)*(5/9 : ℝ)^p)) *
        (9/5 : ℝ)^p := by gcongr
    _ = (2*(2 : ℝ)^((p+r)/2)*W*(r+1)*(p+r+1))*
        ((5/9 : ℝ)^p*(9/5 : ℝ)^p) := by ring
    _ = _ := by rw [hprod, mul_one, pow_succ]; ring

/-- For windows of relative length at most one half, the full lifting
height has an exponential lower bound, even when every digit is signed. -/
theorem short_window_exponential_cost (p r : ℕ) (hp : p.Prime)
    (he : 2 ∣ p+r) (hN : 4 ≤ p+r) (hr : 2*r ≤ p)
    (w : ℕ → ℤ) (W : ℝ) (hW : 0 ≤ W)
    (hweights : ∀ i ≤ r, |(w i : ℝ)| ≤ W)
    (hw : (windowGcd p r : ℤ) = ∑ i ∈ range (r+1), w i*(scaled p r i : ℤ)) :
    (6561/5000 : ℝ)^p ≤ (2*W*(r+1)*(p+r+1))^4 := by
  let C : ℝ := 2*W*(r+1)*(p+r+1)
  have h := gcd_lift_weight_cost p r hp he hN w W hW hweights hw
  have hc : (9/5 : ℝ)^p ≤ (2 : ℝ)^((p+r)/2)*C := by
    dsimp [C]
    rw [pow_succ] at h
    nlinarith
  have hfour := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (9/5)^p) hc 4
  have hpow : ((2 : ℝ)^((p+r)/2))^4 ≤ (2 : ℝ)^(3*p) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hident : (6561/5000 : ℝ)^p * (2 : ℝ)^(3*p) = ((9/5 : ℝ)^p)^4 := by
    calc
      _ = ((6561/5000 : ℝ)*(2^3))^p := by rw [mul_pow, pow_mul]
      _ = ((9/5 : ℝ)^4)^p := by norm_num
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 4 p]
  have hbound : (6561/5000 : ℝ)^p * (2 : ℝ)^(3*p) ≤ C^4 * (2 : ℝ)^(3*p) := by
    rw [hident]
    calc
      _ ≤ ((2 : ℝ)^((p+r)/2)*C)^4 := hfour
      _ = ((2 : ℝ)^((p+r)/2))^4 * C^4 := mul_pow _ _ _
      _ ≤ (2 : ℝ)^(3*p)*C^4 := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (by positivity : (0:ℝ) < 2^(3*p))).mp hbound

#print axioms short_window_exponential_cost
#print axioms gcd_lift_weight_cost
#print axioms gcd_lift_lower_bound

end LambertLongWindowCost
