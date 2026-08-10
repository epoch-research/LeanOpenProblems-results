import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$. If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs


set_option maxHeartbeats 1000000

private def cfA (n k : ℕ) : ℤ :=
  if k = n then 4
  else if k + 1 = n then (5 * (n : ℤ) - 4)
  else if k + 1 < n then
    (k : ℤ) * cfA n (k + 1) - ((k + 1 : ℕ) : ℤ) * cfA n (k + 2)
  else 0
termination_by n - k

private theorem cfA_self (n : ℕ) : cfA n n = 4 := by simp [cfA]

private theorem cfA_pred (n : ℕ) (hn : 1 ≤ n) : cfA n (n-1) = 5*(n:ℤ)-4 := by
  rw [cfA]
  have hne : n - 1 ≠ n := by omega
  have hs : n - 1 + 1 = n := by omega
  simp [hne, hs]

private theorem cfA_rec (n k : ℕ) (h : k + 1 < n) :
    cfA n k = (k : ℤ) * cfA n (k + 1) - ((k + 1 : ℕ) : ℤ) * cfA n (k + 2) := by
  rw [cfA]
  have hkn : k ≠ n := by omega
  have hk1 : k + 1 ≠ n := by omega
  simp [hkn, hk1, h]

private def coeffU (k : ℕ) : ℤ :=
  if k = 2 then 1
  else if k = 3 then 0
  else if 4 ≤ k then ((k - 2 : ℕ) : ℤ) * (coeffU (k - 1) - coeffU (k - 2))
  else 0
termination_by k

private theorem coeffU_two : coeffU 2 = 1 := by simp [coeffU]
private theorem coeffU_three : coeffU 3 = 0 := by simp [coeffU]

private theorem coeffU_rec (k : ℕ) (hk : 2 ≤ k) :
    coeffU (k+2) = (k : ℤ) * (coeffU (k+1) - coeffU k) := by
  rw [coeffU]
  have hk0 : k ≠ 0 := by omega
  have hne2 : k + 2 ≠ 2 := by omega
  have hne3 : k + 2 ≠ 3 := by omega
  have h4 : 4 ≤ k + 2 := by omega
  have hs1 : k + 2 - 2 = k := by omega
  have hs2 : k + 2 - 1 = k + 1 := by omega
  simp [hk0, hne2, hne3, h4, hs1, hs2]

private theorem cfA_scaled (n k : ℕ) (h2 : 2 ≤ k) (hkn : k ≤ n) :
    ((Nat.factorial (k-1) : ℕ) : ℤ) * cfA n k =
      coeffU k * cfA n 2 + ((k - 2 : ℕ) : ℤ) * (2 * cfA n 3) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk2 : k = 2
    · subst hk2
      simp [coeffU_two]
    · by_cases hk3 : k = 3
      · subst hk3
        simp [coeffU_three]
      · have hk4 : 4 ≤ k := by omega
        have hkm2_2 : 2 ≤ k - 2 := by omega
        have hkm1_2 : 2 ≤ k - 1 := by omega
        have hkm2n : k - 2 ≤ n := by omega
        have hkm1n : k - 1 ≤ n := by omega
        have ih2 := ih (k-2) (by omega) hkm2_2 hkm2n
        have ih1 := ih (k-1) (by omega) hkm1_2 hkm1n
        have hrecA := cfA_rec n (k-2) (by omega : (k - 2) + 1 < n)
        have hfac : Nat.factorial (k - 1) = (k - 1) * Nat.factorial (k - 2) := by
          have h : k - 1 = (k - 2) + 1 := by omega
          rw [h, Nat.factorial_succ]
        have hfac2 : Nat.factorial (k - 2) = (k - 2) * Nat.factorial (k - 3) := by
          have h : k - 2 = (k - 3) + 1 := by omega
          rw [h, Nat.factorial_succ]
        have hcoeff : coeffU k = ((k-2 : ℕ) : ℤ) * (coeffU (k-1) - coeffU (k-2)) := by
          have := coeffU_rec (k-2) (by omega : 2 ≤ k-2)
          have hs : k - 2 + 2 = k := by omega
          have hs1 : k - 2 + 1 = k - 1 := by omega
          simpa [hs, hs1] using this
        have hA : (((k - 1 : ℕ) : ℤ) * cfA n k) = ((k - 2 : ℕ) : ℤ) * cfA n (k-1) - cfA n (k-2) := by
          have hs1 : k - 2 + 1 = k - 1 := by omega
          have hs2 : k - 2 + 2 = k := by omega
          rw [hs1, hs2] at hrecA
          nlinarith
        have ih1' : ((Nat.factorial (k-2) : ℕ) : ℤ) * cfA n (k-1) =
            coeffU (k-1) * cfA n 2 + ((k - 3 : ℕ) : ℤ) * (2 * cfA n 3) := by
          have s1 : k - 1 - 1 = k - 2 := by omega
          have s2 : k - 1 - 2 = k - 3 := by omega
          simpa [s1, s2] using ih1
        have ih2' : ((Nat.factorial (k-3) : ℕ) : ℤ) * cfA n (k-2) =
            coeffU (k-2) * cfA n 2 + ((k - 4 : ℕ) : ℤ) * (2 * cfA n 3) := by
          have s1 : k - 2 - 1 = k - 3 := by omega
          have s2 : k - 2 - 2 = k - 4 := by omega
          simpa [s1, s2] using ih2
        have hf2z : ((Nat.factorial (k-2) : ℕ) : ℤ) = ((k - 2 : ℕ) : ℤ) * ((Nat.factorial (k-3) : ℕ) : ℤ) := by
          rw [hfac2, Nat.cast_mul]
        have hf1z : ((Nat.factorial (k-1) : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) * ((k - 2 : ℕ) : ℤ) * ((Nat.factorial (k-3) : ℕ) : ℤ) := by
          rw [hfac, Nat.cast_mul, hf2z]
          ring
        have hmain : ((Nat.factorial (k-1) : ℕ) : ℤ) * cfA n k =
            ((k - 2 : ℕ) : ℤ) * (((Nat.factorial (k-2) : ℕ) : ℤ) * cfA n (k-1)) -
            ((k - 2 : ℕ) : ℤ) * (((Nat.factorial (k-3) : ℕ) : ℤ) * cfA n (k-2)) := by
          calc
            ((Nat.factorial (k-1) : ℕ) : ℤ) * cfA n k
                = (((k - 2 : ℕ) : ℤ) * ((Nat.factorial (k-3) : ℕ) : ℤ)) * (((k - 1 : ℕ) : ℤ) * cfA n k) := by rw [hf1z]; ring
            _ = (((k - 2 : ℕ) : ℤ) * ((Nat.factorial (k-3) : ℕ) : ℤ)) * (((k - 2 : ℕ) : ℤ) * cfA n (k-1) - cfA n (k-2)) := by rw [hA]
            _ = ((k - 2 : ℕ) : ℤ) * (((Nat.factorial (k-2) : ℕ) : ℤ) * cfA n (k-1)) -
                ((k - 2 : ℕ) : ℤ) * (((Nat.factorial (k-3) : ℕ) : ℤ) * cfA n (k-2)) := by rw [hf2z]; ring
        have c2 : ((k - 3 : ℕ) : ℤ) - ((k - 4 : ℕ) : ℤ) = 1 := by omega
        rw [hmain, ih1', ih2', hcoeff]
        ring_nf
        linear_combination (((k - 2 : ℕ) : ℤ) * (2 * cfA n 3)) * c2

private theorem coeffU_det (n : ℕ) (hn : 3 ≤ n) :
    ((n - 3 : ℕ) : ℤ) * coeffU n - ((n - 2 : ℕ) : ℤ) * coeffU (n-1)
      = - ((Nat.factorial (n-2) : ℕ) : ℤ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [coeffU_two, coeffU_three]
  | succ n hn ih =>
      have hrec : coeffU (n+1) = ((n-1 : ℕ) : ℤ) * (coeffU n - coeffU (n-1)) := by
        have := coeffU_rec (n-1) (by omega : 2 ≤ n-1)
        have hnp : n - 1 + 2 = n + 1 := by omega
        have hnp1 : n - 1 + 1 = n := by omega
        simpa [hnp, hnp1] using this
      have hfac : Nat.factorial (n - 1) = (n - 1) * Nat.factorial (n - 2) := by
        have h1 : n - 1 = (n - 2) + 1 := by omega
        rw [h1, Nat.factorial_succ]
      have hnsub1 : (n + 1 - 3 : ℕ) = n - 2 := by omega
      have hnsub2 : (n + 1 - 2 : ℕ) = n - 1 := by omega
      rw [hnsub1, hnsub2, hrec]
      have hnminus : n + 1 - 1 = n := by omega
      rw [hnminus, hfac, Nat.cast_mul]
      have hcast1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      have hcast2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
      have hcast3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
      rw [hcast1, hcast2]
      rw [hcast2, hcast3] at ih
      nlinarith

private theorem cfA_two_formula (n : ℕ) (hn : 3 ≤ n) :
    cfA n 2 = (n : ℤ)^2 + 2*(n:ℤ) - 4 := by
  have hscaledn := cfA_scaled n n (by omega) (le_rfl)
  have hscaledpred := cfA_scaled n (n-1) (by omega) (by omega)
  rw [cfA_self] at hscaledn
  rw [cfA_pred n (by omega)] at hscaledpred
  have sN1 : n - 1 - 1 = n - 2 := by omega
  have sN2 : n - 1 - 2 = n - 3 := by omega
  rw [sN1, sN2] at hscaledpred
  have hdet := coeffU_det n hn
  have hfacpred : Nat.factorial (n-1) = (n-1) * Nat.factorial (n-2) := by
    have h : n - 1 = (n - 2) + 1 := by omega
    rw [h, Nat.factorial_succ]
  rw [hfacpred, Nat.cast_mul] at hscaledn
  have c1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have c2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have c3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  rw [c1, c2] at hscaledn
  rw [c3] at hscaledpred
  rw [c2, c3] at hdet
  have hcombo : ((Nat.factorial (n-2) : ℕ) : ℤ) * cfA n 2 =
      ((Nat.factorial (n-2) : ℕ) : ℤ) * ((n : ℤ)^2 + 2*(n:ℤ) - 4) := by
    linear_combination hdet * cfA n 2 + ((n : ℤ) - 3) * hscaledn - ((n : ℤ) - 2) * hscaledpred
  have hfacnz : ((Nat.factorial (n-2) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-2)
  exact mul_left_cancel₀ hfacnz hcombo

private theorem cfd_eq_cfA_div (n k : ℕ) (hn : 3 ≤ n) (h2 : 2 ≤ k) (hk : k ≤ n - 1)
    (hnz : ∀ j : ℕ, k + 1 ≤ j → j ≤ n → cfA n j ≠ 0) :
    continued_fraction_denominator n k = (cfA n k : ℚ) / (cfA n (k+1) : ℚ) := by
  let d := n - k
  have main : ∀ k' : ℕ, n - k' ≤ d → 2 ≤ k' → k' ≤ n - 1 →
      (∀ j : ℕ, k' + 1 ≤ j → j ≤ n → cfA n j ≠ 0) →
      continued_fraction_denominator n k' = (cfA n k' : ℚ) / (cfA n (k'+1) : ℚ) := by
    intro k'
    induction hd : n - k' using Nat.strong_induction_on generalizing k' with
    | h m ih =>
      intro hm h2' hk' hnz'
      by_cases hbase : k' = n - 1
      · subst hbase
        rw [continued_fraction_denominator]
        have hnle2 : ¬ n ≤ 2 := by omega
        have hrange : 2 ≤ n - 1 ∧ n - 1 ≤ n - 1 := by omega
        have hs : n - 1 + 1 = n := by omega
        simp [hnle2, hrange, cfA_pred n (by omega), hs, cfA_self]
        field_simp
        have hn1 : 1 ≤ n := by omega
        rw [Nat.cast_sub hn1]
        norm_num
        ring
      · have hklt : k' + 1 < n := by omega
        rw [continued_fraction_denominator]
        have hnle2 : ¬ n ≤ 2 := by omega
        have hrange : 2 ≤ k' ∧ k' ≤ n - 1 := ⟨h2', hk'⟩
        have hnotbase : ¬ k' = n - 1 := hbase
        simp [hnle2, hrange, hnotbase]
        have hmeas : n - (k' + 1) < m := by omega
        have ihnext : continued_fraction_denominator n (k'+1) = (cfA n (k'+1) : ℚ) / (cfA n (k'+2) : ℚ) := by
          apply ih (n - (k' + 1)) hmeas (k' + 1) rfl
          · omega
          · omega
          · omega
          · intro j hj1 hjn
            apply hnz' j <;> omega
        rw [ihnext]
        have hrec := cfA_rec n k' hklt
        rw [hrec]
        have hden1 : (cfA n (k'+1) : ℚ) ≠ 0 := by exact_mod_cast hnz' (k'+1) (by omega) (by omega)
        have hden2 : (cfA n (k'+2) : ℚ) ≠ 0 := by exact_mod_cast hnz' (k'+2) (by omega) (by omega)
        field_simp [hden1, hden2]
        push_cast
        ring
  exact main k (by simp [d]) h2 hk hnz

private theorem A363347_eq_of_good (p n q : ℕ) (hp : p.Prime) (hn : 3 ≤ n) (hnp : n < p)
    (hqpos : 0 < q) (hqle : q ≤ n - 1) (hqc : q.Coprime (2 * (n - 2)))
    (hA2nat : n * n + 2 * n - 4 = p * q) :
    A363347 n = p := by
  have hp2 : p ≠ 2 := by omega
  have hpgt2 : 2 < p := hp.two_le.lt_of_ne hp2.symm
  have hA2z : cfA n 2 = (p : ℤ) * (q : ℤ) := by
    rw [cfA_two_formula n hn]
    have hge : 4 ≤ n * n + 2 * n := by
      have hmul : 3 * 3 ≤ n * n := Nat.mul_le_mul hn hn
      nlinarith
    have hz : (n : ℤ)^2 + 2*(n:ℤ) - 4 = (n * n + 2 * n - 4 : ℕ) := by
      rw [Nat.cast_sub hge, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
      ring
    rw [hz, hA2nat]
    norm_num
  have hscaledn := cfA_scaled n n (by omega) (le_rfl)
  rw [cfA_self, hA2z] at hscaledn
  have hfac_dvd_nat : q ∣ Nat.factorial (n - 1) := Nat.dvd_factorial hqpos hqle
  have hq_dvd_A3 : (q : ℤ) ∣ cfA n 3 := by
    have hq_dvd_A2 : (q : ℤ) ∣ (p : ℤ) * (q : ℤ) := dvd_mul_left _ _
    have hq_dvd_fac : (q : ℤ) ∣ ((Nat.factorial (n - 1) : ℕ) : ℤ) := by exact_mod_cast hfac_dvd_nat
    have hq_dvd_fourfac : (q : ℤ) ∣ 4 * ((Nat.factorial (n - 1) : ℕ) : ℤ) := dvd_mul_of_dvd_right hq_dvd_fac 4
    have hq_dvd_uA2 : (q : ℤ) ∣ coeffU n * ((p : ℤ) * (q : ℤ)) := dvd_mul_of_dvd_right hq_dvd_A2 (coeffU n)
    have hq_dvd_prod : (q : ℤ) ∣ ((n - 2 : ℕ) : ℤ) * (2 * cfA n 3) := by
      have : ((n - 2 : ℕ) : ℤ) * (2 * cfA n 3) = 4 * ((Nat.factorial (n - 1) : ℕ) : ℤ) - coeffU n * ((p : ℤ) * (q : ℤ)) := by
        nlinarith [hscaledn]
      rw [this]
      exact dvd_sub hq_dvd_fourfac hq_dvd_uA2
    have hq_dvd_prod' : (q : ℤ) ∣ ((2 * (n - 2) : ℕ) : ℤ) * cfA n 3 := by
      convert hq_dvd_prod using 1
      · rw [Nat.cast_mul]
        ring
    have hgcd : Int.gcd (q : ℤ) ((2 * (n - 2) : ℕ) : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact Nat.coprime_iff_gcd_eq_one.mp hqc
    exact Int.dvd_of_dvd_mul_right_of_gcd_one hq_dvd_prod' hgcd
  have hp_not_dvd_A3 : ¬ (p : ℤ) ∣ cfA n 3 := by
    intro hpA3
    have hp_dvd_A2 : (p : ℤ) ∣ (p : ℤ) * (q : ℤ) := dvd_mul_right _ _
    have hp_dvd_uA2 : (p : ℤ) ∣ coeffU n * ((p : ℤ) * (q : ℤ)) := dvd_mul_of_dvd_right hp_dvd_A2 (coeffU n)
    have hp_dvd_term : (p : ℤ) ∣ ((n - 2 : ℕ) : ℤ) * (2 * cfA n 3) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpA3 2) _
    have hp_dvd_fourfac_int : (p : ℤ) ∣ 4 * ((Nat.factorial (n - 1) : ℕ) : ℤ) := by
      have : 4 * ((Nat.factorial (n - 1) : ℕ) : ℤ) = coeffU n * ((p : ℤ) * (q : ℤ)) + ((n - 2 : ℕ) : ℤ) * (2 * cfA n 3) := by
        nlinarith [hscaledn]
      rw [this]
      exact dvd_add hp_dvd_uA2 hp_dvd_term
    have hp_dvd_fourfac_nat : p ∣ 4 * Nat.factorial (n - 1) := by
      exact_mod_cast hp_dvd_fourfac_int
    have hnot4 : ¬ p ∣ 4 := by
      intro h
      have hp_le4 : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
      interval_cases p
      all_goals first | omega | norm_num [Nat.Prime] at hp
    have hnotfac : ¬ p ∣ Nat.factorial (n - 1) := by
      rw [hp.dvd_factorial]
      omega
    rcases (hp.dvd_mul.mp hp_dvd_fourfac_nat) with h4 | hf
    · exact hnot4 h4
    · exact hnotfac hf
  have hnz : ∀ j : ℕ, 3 ≤ j → j ≤ n → cfA n j ≠ 0 := by
    intro j hj3 hjn hzj
    have hsj := cfA_scaled n j (by omega) hjn
    rw [hzj, hA2z] at hsj
    have hp_dvd_left : (p : ℤ) ∣ ((Nat.factorial (j - 1) : ℕ) : ℤ) * 0 := by simp
    have hp_dvd_coeff : (p : ℤ) ∣ coeffU j * ((p : ℤ) * (q : ℤ)) := dvd_mul_of_dvd_right (dvd_mul_right (p:ℤ) (q:ℤ)) (coeffU j)
    have hp_dvd_jterm : (p : ℤ) ∣ ((j - 2 : ℕ) : ℤ) * (2 * cfA n 3) := by
      have : ((j - 2 : ℕ) : ℤ) * (2 * cfA n 3) = - coeffU j * ((p : ℤ) * (q : ℤ)) := by
        nlinarith [hsj]
      rw [this]
      simpa [neg_mul] using dvd_neg.mpr hp_dvd_coeff
    have hp_dvd_nat : p ∣ (2 * (j - 2)) := by
      have hp_dvd_abs : (p : ℤ) ∣ (((2 * (j - 2) : ℕ) : ℤ) * cfA n 3) := by
        convert hp_dvd_jterm using 1
        · rw [Nat.cast_mul]
          ring
      by_contra hnot
      have hcop : Int.gcd (p : ℤ) (((2 * (j - 2) : ℕ) : ℤ)) = 1 := by
        rw [Int.gcd_natCast_natCast]
        apply Nat.coprime_iff_gcd_eq_one.mp
        exact hp.coprime_iff_not_dvd.mpr hnot
      exact hp_not_dvd_A3 (Int.dvd_of_dvd_mul_right_of_gcd_one hp_dvd_abs hcop)
    have hnot_dvd_two : ¬ p ∣ 2 := by
      intro h2dvd
      have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2dvd
      omega
    have hnot_dvd_j : ¬ p ∣ (j - 2) := by
      intro hjdvd
      have hposj : 0 < j - 2 := by omega
      have hlej : j - 2 < p := by omega
      exact (not_le_of_gt hlej) (Nat.le_of_dvd hposj hjdvd)
    rcases hp.dvd_mul.mp hp_dvd_nat with h2dvd | hjdvd
    · exact hnot_dvd_two h2dvd
    · exact hnot_dvd_j hjdvd
  obtain ⟨b, hb⟩ := hq_dvd_A3
  have hbne : b ≠ 0 := by
    intro hb0
    rw [hb0, mul_zero] at hb
    exact hp_not_dvd_A3 (by rw [hb]; exact dvd_zero _)
  have hp_not_dvd_b : ¬ (p : ℤ) ∣ b := by
    intro hpb
    exact hp_not_dvd_A3 (by rw [hb]; exact dvd_mul_of_dvd_right hpb (q:ℤ))
  have hcfd : continued_fraction_denominator n 2 = (p : ℚ) / (b : ℚ) := by
    have h := cfd_eq_cfA_div n 2 hn (by omega) (by omega) (by
      intro j hj hjn
      exact hnz j (by omega) hjn)
    rw [h, hA2z, hb]
    have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hqpos.ne'
    field_simp [hqQ]
    push_cast
    ring
  have hnumabs : ((continued_fraction_denominator n 2).num.natAbs) = p := by
    rw [hcfd]
    change (((p : ℤ) : ℚ) / (b : ℚ)).num.natAbs = p
    rw [Rat.intCast_div_eq_divInt, Rat.num_divInt]
    have hgcd : b.gcd (p : ℤ) = 1 := by
      by_contra hg
      have hpdvdg : (b.gcd (p : ℤ)) ∣ p := by
        exact_mod_cast Int.gcd_dvd_right b (p:ℤ)
      rcases hp.eq_one_or_self_of_dvd (b.gcd (p : ℤ)) hpdvdg with h1 | hp_eq
      · exact hg h1
      · have : (p : ℤ) ∣ b := by
          rw [← hp_eq]
          exact Int.gcd_dvd_left b (p:ℤ)
        exact hp_not_dvd_b this
    rw [hgcd]
    norm_num
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_sign]
    simp [hbne]
  simp [A363347, not_le.mpr (by omega : 2 < n), hnumabs]

private theorem coprime_q_rsub (p r q : ℕ) (hr4 : 4 ≤ r) (hodd : Odd q)
    (hmul : p * q = r*r - 5) : q.Coprime (r - 3) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := q.gcd (r - 3)
  change d = 1
  have hdq : d ∣ q := Nat.gcd_dvd_left q (r-3)
  have hdr : d ∣ r - 3 := Nat.gcd_dvd_right q (r-3)
  have hdmul : d ∣ p*q := dvd_mul_of_dvd_right hdq p
  rw [hmul] at hdmul
  have hge : 5 ≤ r*r := by nlinarith
  have hdint1 : (d:ℤ) ∣ ((r*r - 5 : ℕ) : ℤ) := by exact_mod_cast hdmul
  rw [Int.ofNat_sub hge, Nat.cast_mul] at hdint1
  have hdint2 : (d:ℤ) ∣ ((r - 3 : ℕ) : ℤ) := by exact_mod_cast hdr
  have hdint2' : (d:ℤ) ∣ (r:ℤ) - 3 := by
    rwa [Nat.cast_sub (by omega : 3 ≤ r)] at hdint2
  have hd4int : (d:ℤ) ∣ (4:ℤ) := by
    have hprod : (d:ℤ) ∣ ((r:ℤ)+3) * ((r:ℤ)-3) := dvd_mul_of_dvd_right hdint2' ((r:ℤ)+3)
    have hsub := dvd_sub hdint1 hprod
    convert hsub using 1 <;> ring
  have hd4 : d ∣ 4 := by exact_mod_cast hd4int
  have hodd_d : Odd d := Odd.of_dvd_nat hodd hdq
  have hdle4 : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
  interval_cases d <;> first | rfl | (rcases hodd_d with ⟨k,hk⟩; omega) | (rcases hd4 with ⟨c,hc⟩; omega)

private theorem root_odd_good (p r : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (hr4 : 4 ≤ r) (hpr4 : 4 ≤ p - r)
    (hmod : r*r ≡ 5 [MOD p]) (hodd : Odd ((r*r - 5) / p)) :
    let n := r - 1; let q := (r*r - 5) / p
    3 ≤ n ∧ n < p ∧ 0 < q ∧ q ≤ n - 1 ∧ q.Coprime (2 * (n - 2)) ∧ n*n+2*n-4 = p*q := by
  intro n q
  have hrp : r < p := by omega
  have hp0 : 0 < p := hp.pos
  have hge5 : 5 ≤ r*r := by nlinarith
  have hpdvd : p ∣ r*r - 5 := by
    have hdint : (p:ℤ) ∣ ((r*r - 5 : ℕ) : ℤ) := by
      have hd := Nat.ModEq.dvd hmod
      rw [Int.ofNat_sub hge5]
      have hdneg : (p:ℤ) ∣ -(↑5 - ↑(r*r) : ℤ) := dvd_neg.mpr hd
      convert hdneg using 1 <;> ring
    exact_mod_cast hdint
  have hmulq : p * q = r*r - 5 := by
    dsimp [q]
    exact Nat.mul_div_cancel' hpdvd
  have hqpos : 0 < q := by
    have hrr : 16 ≤ r*r := Nat.mul_le_mul hr4 hr4
    have hgt : 0 < r*r - 5 := by omega
    rw [← hmulq] at hgt
    exact Nat.pos_of_mul_pos_left hgt
  have hn3 : 3 ≤ n := by dsimp [n]; omega
  have hnp : n < p := by dsimp [n]; omega
  have hqle : q ≤ n - 1 := by
    have hpger4 : r + 4 ≤ p := by omega
    have hineq : r*r - 5 ≤ p * (r - 2) := by
      have hmono : (r + 4) * (r - 2) ≤ p * (r - 2) := Nat.mul_le_mul_right (r-2) hpger4
      have hcalc : r*r - 5 ≤ (r + 4) * (r - 2) := by
        have hcalcZ : ((r*r - 5 : ℕ) : ℤ) ≤ (((r + 4) * (r - 2) : ℕ) : ℤ) := by
          rw [Nat.cast_sub hge5, Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ r)]
          ring_nf
          omega
        exact_mod_cast hcalcZ
      exact le_trans hcalc hmono
    rw [← hmulq] at hineq
    have := Nat.le_of_mul_le_mul_left hineq hp0
    simpa [n] using this
  have hcop1 : q.Coprime (r - 3) := coprime_q_rsub p r q hr4 hodd hmulq
  have hcop2 : q.Coprime 2 := (Nat.coprime_two_right).mpr hodd
  have hcop : q.Coprime (2 * (n - 2)) := by
    have hnsub : n - 2 = r - 3 := by dsimp [n]; omega
    rw [hnsub]
    exact Nat.Coprime.mul_right hcop2 hcop1
  have hA : n*n + 2*n - 4 = p*q := by
    have heq : n*n + 2*n - 4 = r*r - 5 := by
      dsimp [n]
      have hgeL : 4 ≤ (r - 1) * (r - 1) + 2 * (r - 1) := by
        have hrr : 3 ≤ r - 1 := by omega
        nlinarith [Nat.mul_le_mul hrr hrr]
      have hz : (((r - 1) * (r - 1) + 2 * (r - 1) - 4 : ℕ) : ℤ) = ((r*r - 5 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hgeL, Nat.cast_sub hge5]
        push_cast
        rw [Nat.cast_sub (by omega : 1 ≤ r)]
        ring
      exact_mod_cast hz
    rw [heq, ← hmulq]
  exact ⟨hn3, hnp, hqpos, hqle, hcop, hA⟩

private theorem comp_root (p a : ℕ) [NeZero p] (ha : a < p) (hmoda : a*a ≡ 5 [MOD p]) :
    (p-a)*(p-a) ≡ 5 [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff] at hmoda ⊢
  rw [Nat.cast_mul]
  have hsum : ((p - a : ℕ) : ZMod p) + (a : ZMod p) = 0 := by
    rw [← Nat.cast_add, Nat.sub_add_cancel (le_of_lt ha), ZMod.natCast_self]
  have hneg : ((p - a : ℕ) : ZMod p) = - (a : ZMod p) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hsum
  rw [hneg, neg_mul_neg]
  simpa [Nat.cast_mul] using hmoda

private theorem odd_sq_sub_five_of_even (a : ℕ) (ha : Even a) (ha4 : 4 ≤ a) : Odd (a*a - 5) := by
  rcases ha with ⟨k,hk⟩
  subst a
  have hk2 : 2 ≤ k := by omega
  use 2*(k*k)-3
  have hz : (((k+k)*(k+k)-5:ℕ):ℤ) = ((2*(2*(k*k)-3)+1:ℕ):ℤ) := by
    rw [Nat.cast_sub (by nlinarith : 5 ≤ (k+k)*(k+k))]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
    rw [Nat.cast_sub (by nlinarith : 3 ≤ 2*(k*k))]
    push_cast
    ring
  exact_mod_cast hz

private theorem odd_quot_of_even_root (p r : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (hr4 : 4 ≤ r)
    (hmod : r*r ≡ 5 [MOD p]) (heven : Even r) : Odd ((r*r-5)/p) := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hge5 : 5 ≤ r*r := by nlinarith [Nat.mul_le_mul hr4 hr4]
  have hpdvd : p ∣ r*r - 5 := by
    have hdint : (p:ℤ) ∣ ((r*r - 5 : ℕ) : ℤ) := by
      have hd := Nat.ModEq.dvd hmod
      rw [Int.ofNat_sub hge5]
      have hdneg : (p:ℤ) ∣ -(↑5 - ↑(r*r) : ℤ) := dvd_neg.mpr hd
      convert hdneg using 1 <;> ring
    exact_mod_cast hdint
  let q := (r*r-5)/p
  have hmulq : p*q = r*r-5 := by exact Nat.mul_div_cancel' hpdvd
  have hNodd : Odd (r*r-5) := odd_sq_sub_five_of_even r heven hr4
  have hpqodd : Odd (p*q) := by rwa [hmulq]
  exact (Nat.odd_mul.mp hpqodd).2

private theorem exists_odd_root (p : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (hs : IsSquare (5 : ZMod p)) :
    ∃ r, 4 ≤ r ∧ 4 ≤ p - r ∧ r*r ≡ 5 [MOD p] ∧ Odd ((r*r-5)/p) := by
  haveI : NeZero p := ⟨by omega⟩
  rcases hs with ⟨x, hx⟩
  let a := x.val
  have hval : a < p := ZMod.val_lt x
  have hmoda : a*a ≡ 5 [MOD p] := by
    have hx' : (a : ZMod p)^2 = (5 : ZMod p) := by
      simpa [a, ZMod.natCast_zmod_val, pow_two] using hx.symm
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa [pow_two] using hx'
  have ha4 : 4 ≤ a := by
    by_contra h
    have ha3 : a ≤ 3 := by omega
    interval_cases a <;> rw [Nat.ModEq] at hmoda <;>
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega : 5 < p)] at hmoda <;>
      norm_num at hmoda
  have hbmod : (p-a)*(p-a) ≡ 5 [MOD p] := comp_root p a hval hmoda
  have hb4 : 4 ≤ p - a := by
    by_contra h
    have hb3 : p - a ≤ 3 := by omega
    interval_cases (p-a) <;> rw [Nat.ModEq] at hbmod <;>
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega : 5 < p)] at hbmod <;>
      norm_num at hbmod
  rcases even_or_odd a with haeven | haodd
  · exact ⟨a, ha4, hb4, hmoda, odd_quot_of_even_root p a hp hp11 ha4 hmoda haeven⟩
  · have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hbeven : Even (p - a) := by
      rcases hpodd with ⟨u,hu⟩
      rcases haodd with ⟨v,hv⟩
      subst p; subst a
      have hvu : v < u := by omega
      use u - v
      omega
    exact ⟨p-a, hb4, by omega, hbmod, odd_quot_of_even_root p (p-a) hp hp11 hb4 hbmod hbeven⟩




/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p :=
  by
    intro p hpall
    have hp : p.Prime := hpall.1
    have hmod10 := hpall.2
    have hp11 : 11 ≤ p := by
      by_contra h
      have hp10 : p ≤ 10 := by omega
      interval_cases p
      any_goals norm_num [Nat.Prime] at hp
      all_goals norm_num [Nat.ModEq] at hmod10
    have hmod5 : p % 5 = 1 ∨ p % 5 = 4 := by
      rcases hmod10 with h | h
      · left
        have h5 : p ≡ 1 [MOD 5] := Nat.ModEq.of_dvd (by norm_num : 5 ∣ 10) h
        simpa [Nat.ModEq] using h5
      · right
        have h5 : p ≡ 9 [MOD 5] := Nat.ModEq.of_dvd (by norm_num : 5 ∣ 10) h
        simpa [Nat.ModEq] using h5
    have hs : IsSquare (5 : ZMod p) := by
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hpne2 : p ≠ 2 := by omega
      have hs5 : IsSquare (p : ZMod 5) := by
        rcases hmod5 with h | h
        · use 1
          norm_num
          rw [← ZMod.natCast_mod p 5, h]
          norm_num
        · use 2
          norm_num
          rw [← ZMod.natCast_mod p 5, h]
          norm_num
      have hiff := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p:=5) (q:=p) (by norm_num) hpne2
      exact hiff.mp hs5
    obtain ⟨r, hr4, hpr4, hroot, hodd⟩ := exists_odd_root p hp hp11 hs
    let n := r - 1
    let q := (r*r - 5) / p
    have hgood := root_odd_good p r hp hp11 hr4 hpr4 hroot hodd
    dsimp [n, q] at hgood
    rcases hgood with ⟨hn3, hnp, hqpos, hqle, hqc, hA⟩
    exact ⟨n, A363347_eq_of_good p n q hp hn3 hnp hqpos hqle hqc hA⟩
