import Submission.DirectPadeSpecialization

/-!
Derivative specialization congruences for direct-series Padé data.
Auxiliary arithmetic only; this does not settle Erdős problem 68.
-/

namespace DirectPadeDerivativeCongruence

open Finset DirectPadeSpecialization

noncomputable def directPrefix (N : ℕ) : ℚ :=
  ∑ k ∈ range N, 1 / (k.factorial - 1 : ℚ)

lemma prefix_succ (N : ℕ) :
    directPrefix (N+1) = directPrefix N + 1 / (N.factorial - 1 : ℚ) :=
  sum_range_succ _ _

lemma late_coefficient (L n : ℕ) (hL : 2 ≤ L) (hn : L ≤ n) :
    ∃ r : ℚ, L.factorial.Coprime r.den ∧
      (L.factorial : ℚ) * r = 1 + 1 / (n.factorial - 1 : ℚ) := by
  let r : ℚ := ((n.factorial / L.factorial : ℕ) : ℚ) /
    ((n.factorial - 1 : ℕ) : ℚ)
  have hf : 2 ≤ n.factorial := by
    simpa using Nat.factorial_le (hL.trans hn)
  have hp : 0 < n.factorial - 1 := by omega
  refine ⟨r, ?_, ?_⟩
  · exact integer_quotient_den_coprime L.factorial (n.factorial-1)
      (n.factorial / L.factorial : ℤ) hp
      (ScaledDenominatorRoughness.factorial_pred_coprime hn)
  · have hdiv := Nat.factorial_dvd_factorial hn
    have hne : (L.factorial : ℚ) ≠ 0 := by positivity
    have hd : (n.factorial - 1 : ℚ) ≠ 0 := by
      have hh : (2 : ℚ) ≤ n.factorial := by exact_mod_cast hf
      linarith
    dsimp [r]
    rw [Nat.cast_div hdiv hne, Nat.cast_sub (by omega : 1 ≤ n.factorial)]
    push_cast
    field_simp
    ring

lemma prefix_decomposition (L n : ℕ) (hL : 2 ≤ L) (hn : L ≤ n) :
    ∃ r : ℚ, L.factorial.Coprime r.den ∧
      directPrefix n = directPrefix L - ((n-L : ℕ) : ℚ) + (L.factorial : ℚ) * r := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨0, by simp, by simp⟩
  | succ n hn ih =>
    obtain ⟨r, hcr, hr⟩ := ih
    obtain ⟨t, hct, ht⟩ := late_coefficient L n hL hn
    refine ⟨r+t, ?_, ?_⟩
    · exact Nat.Coprime.of_dvd_right (Rat.add_den_dvd _ _) (hcr.mul_right hct)
    · rw [prefix_succ, hr, Nat.succ_sub hn]
      push_cast
      linarith

/-- Congruence for a weighted sum of direct prefixes with a divisible retained
weight. D clears only the early prefix; late denominator primes are retained. -/
theorem weighted_prefix_congruence {ι : Type*} (s : Finset ι)
    (w : ι → ℤ) (n : ι → ℕ) (L : ℕ) (D a b : ℤ)
    (hL : 2 ≤ L) (hn : ∀ i ∈ s, L ≤ n i)
    (hD : (D : ℚ) * directPrefix L = a)
    (hW : (L.factorial : ℤ) ∣ ∑ i ∈ s, w i)
    (hB : ∑ i ∈ s, (w i : ℚ) * directPrefix (n i) = b) :
    (L.factorial : ℤ) ∣ D * (b + ∑ i ∈ s, w i * (n i : ℤ)) := by
  classical
  choose r hc hr using fun i : ι => prefix_decomposition L (max L (n i))
    hL (le_max_left _ _)
  have hrow : ∀ i ∈ s,
      (L.factorial : ℚ) * ((D * w i : ℤ) * r i) =
        (D : ℚ) * ((w i : ℚ) * directPrefix (n i) + (w i : ℚ) * n i) -
          (w i : ℚ) * ((a : ℚ) + (D : ℚ) * L) := by
    intro i hi
    have he := hr i
    rw [max_eq_right (hn i hi)] at he
    rw [Nat.cast_sub (hn i hi)] at he
    have he' : (L.factorial : ℚ) * r i =
        directPrefix (n i) - directPrefix L + ((n i : ℚ) - L) := by linarith
    calc
      _ = (D : ℚ) * (w i : ℚ) * ((L.factorial : ℚ) * r i) := by push_cast; ring
      _ = _ := by rw [he', ← hD]; ring
  let R : ℚ := ∑ i ∈ s, (D * w i : ℤ) * r i
  have hR : L.factorial.Coprime R.den := by
    apply ScaledDenominatorRoughness.coprime_sum_den
    intro i hi
    apply Nat.Coprime.of_dvd_right (Rat.mul_den_dvd _ _)
    simpa only [← Int.cast_mul, Rat.den_intCast, one_mul] using hc i
  have he : (L.factorial : ℚ) * R =
      ((D * (b + ∑ i ∈ s, w i * (n i : ℤ)) -
        (∑ i ∈ s, w i) * (a + D * (L : ℤ)) : ℤ) : ℚ) := by
    dsimp [R]
    rw [mul_sum]
    calc
      _ = ∑ i ∈ s,
          ((D : ℚ) * ((w i : ℚ) * directPrefix (n i) + (w i : ℚ) * n i) -
            (w i : ℚ) * ((a : ℚ) + (D : ℚ) * L)) := by
        exact sum_congr rfl hrow
      _ = _ := by
        rw [sum_sub_distrib, ← mul_sum, sum_add_distrib, hB, ← sum_mul]
        push_cast
        ring
  have hd := integer_multiple_of_coprime_den L.factorial R _ hR he
  have hw := dvd_mul_of_dvd_left hW (a + D * (L : ℤ))
  have hh := dvd_add hd hw
  simpa only [sub_add_cancel] using hh

lemma derivative_eval_one (Q : Polynomial ℤ) :
    Q.derivative.eval 1 = ∑ j ∈ range (Q.natDegree+1), Q.coeff j * (j : ℤ) := by
  rw [Polynomial.derivative_eval, Polynomial.sum_over_range]
  · simp
  · intro n
    simp

/-- Value at one of the degree-N truncation of Q times the direct series. -/
noncomputable def numeratorAtOne (Q : Polynomial ℤ) (N : ℕ) : ℚ :=
  ∑ j ∈ range (Q.natDegree+1), (Q.coeff j : ℚ) * directPrefix (N-j+1)

lemma weighted_index_sum (Q : Polynomial ℤ) (N : ℕ) (hN : Q.natDegree ≤ N) :
    ∑ j ∈ range (Q.natDegree+1), Q.coeff j * ((N-j+1 : ℕ) : ℤ) =
      ((N+1 : ℕ) : ℤ) * Q.eval 1 - Q.derivative.eval 1 := by
  rw [derivative_eval_one, Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one]
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  have hjN : j ≤ N := (by have := mem_range.mp hj; omega : j ≤ Q.natDegree).trans hN
  rw [Nat.cast_add, Nat.cast_sub hjN]
  push_cast
  ring

/-- A specialization congruence with the reduced denominator of the early
prefix as its only extra multiplier. The hypothesis concerns an integral
specialized numerator, not integrality of every numerator coefficient. -/
theorem factorial_dvd_numerator_sub_derivative (Q : Polynomial ℤ) (N L : ℕ) (b : ℤ)
    (hL : 2 ≤ L) (hgap : Q.natDegree + L ≤ N)
    (hjet : ∑ j ∈ range (Q.natDegree+1),
      (Q.coeff j : ℚ) / ((N-j).factorial - 1 : ℚ) = 0)
    (hb : numeratorAtOne Q N = b) :
    (L.factorial : ℤ) ∣ (directPrefix L).den * (b - Q.derivative.eval 1) := by
  have hW' := factorial_dvd_specialization Q N (by omega) hjet
  have hfac : (L.factorial : ℤ) ∣ ((N-Q.natDegree).factorial : ℤ) := by
    exact_mod_cast Nat.factorial_dvd_factorial (show L ≤ N-Q.natDegree by omega)
  have hW := hfac.trans hW'
  have hd := weighted_prefix_congruence (range (Q.natDegree+1)) Q.coeff
    (fun j => N-j+1) L (directPrefix L).den (directPrefix L).num b hL
    (by intro j hj; dsimp only; have := mem_range.mp hj; omega)
    (by simp [mul_comm])
    (by simpa [Polynomial.eval_eq_sum_range] using hW) hb
  rw [weighted_index_sum Q N (by omega)] at hd
  have hw : (L.factorial : ℤ) ∣
      (directPrefix L).den * (((N+1 : ℕ) : ℤ) * Q.eval 1) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hW _) _
  have hh := dvd_sub hd hw
  convert hh using 1
  ring

lemma numeratorAtOne_eq_sum_coeff (Q : Polynomial ℤ) (N : ℕ)
    (hN : Q.natDegree ≤ N) :
    numeratorAtOne Q N = ∑ k ∈ range (N+1), PowerSeries.coeff k
      ((Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) * directSeries) := by
  symm
  calc
    _ = ∑ k ∈ range (N+1), ∑ j ∈ range (k+1),
        (Q.coeff j : ℚ) / ((k-j).factorial - 1 : ℚ) := by
      apply sum_congr rfl
      intro k hk
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i
            (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) *
              PowerSeries.coeff j directSeries) k]
      simp only [Polynomial.coeff_coe, Polynomial.coeff_map, directSeries,
        PowerSeries.coeff_mk, mul_one_div]
      rfl
    _ = ∑ j ∈ range (N+1), ∑ k ∈ range (N+1-j),
        (Q.coeff j : ℚ) / (k.factorial - 1 : ℚ) :=
      sum_range_diag_flip (N+1) (fun j k => (Q.coeff j : ℚ) / (k.factorial - 1 : ℚ))
    _ = ∑ j ∈ range (N+1), (Q.coeff j : ℚ) * directPrefix (N+1-j) := by
      simp only [directPrefix, mul_sum, mul_one_div]
    _ = numeratorAtOne Q N := by
      rw [numeratorAtOne]
      symm
      have hs : (∑ j ∈ range (Q.natDegree+1),
          (Q.coeff j : ℚ) * directPrefix (N+1-j)) =
          ∑ j ∈ range (N+1), (Q.coeff j : ℚ) * directPrefix (N+1-j) := by
        apply sum_subset (range_mono (by omega))
        intro j hj hj'
        have hd : Q.natDegree < j := by
          simp only [mem_range] at hj'
          omega
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt hd]
      rw [← hs]
      apply sum_congr rfl
      intro j hj
      have hjN : j ≤ N := by have := mem_range.mp hj; omega
      rw [show N-j+1 = N+1-j by omega]

lemma numeratorAtOne_eq_eval (P : Polynomial ℚ) (Q : Polynomial ℤ) (N : ℕ)
    (hP : P.natDegree ≤ N) (hQ : Q.natDegree ≤ N)
    (hjet : ∀ k ≤ N, PowerSeries.coeff k
      ((Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) * directSeries -
        (P : PowerSeries ℚ)) = 0) :
    numeratorAtOne Q N = P.eval 1 := by
  rw [numeratorAtOne_eq_sum_coeff Q N hQ,
    Polynomial.eval_eq_sum_range' (show P.natDegree < N+1 by omega)]
  simp only [one_pow, mul_one]
  apply sum_congr rfl
  intro k hk
  have he := hjet k (by have := mem_range.mp hk; omega)
  simpa only [map_sub, Polynomial.coeff_coe, sub_eq_zero] using he

/-- Formal-series Padé version. No real or p-adic limiting value is asserted. -/
theorem pade_factorial_dvd_numerator_sub_derivative
    (P : Polynomial ℚ) (Q : Polynomial ℤ) (N L : ℕ) (b : ℤ)
    (hP : P.natDegree < N) (hL : 2 ≤ L) (hgap : Q.natDegree + L ≤ N)
    (hjet : ∀ k ≤ N, PowerSeries.coeff k
      ((Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) * directSeries -
        (P : PowerSeries ℚ)) = 0)
    (hb : P.eval 1 = b) :
    (L.factorial : ℤ) ∣ (directPrefix L).den * (b - Q.derivative.eval 1) := by
  apply factorial_dvd_numerator_sub_derivative Q N L b hL hgap
  · have he := hjet N le_rfl
    rw [map_sub, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt hP, sub_zero,
      direct_product_coefficient Q N (by omega)] at he
    exact he
  · exact (numeratorAtOne_eq_eval P Q N hP.le (by omega) hjet).trans hb

/-- A common specialized factor coming from L!, and coprime to the early
prefix denominator, must also divide Q'(1). This does not bound that factor. -/
theorem factorial_common_factor_dvd_derivative (Q : Polynomial ℤ)
    (N L : ℕ) (b g : ℤ) (hL : 2 ≤ L) (hgap : Q.natDegree + L ≤ N)
    (hjet : ∑ j ∈ range (Q.natDegree+1),
      (Q.coeff j : ℚ) / ((N-j).factorial - 1 : ℚ) = 0)
    (hb : numeratorAtOne Q N = b)
    (hg : g ∣ (L.factorial : ℤ)) (hgb : g ∣ b)
    (hc : IsCoprime g ((directPrefix L).den : ℤ)) :
    g ∣ Q.derivative.eval 1 := by
  have hd := hg.trans (factorial_dvd_numerator_sub_derivative Q N L b hL hgap hjet hb)
  have hdb : g ∣ (directPrefix L).den * b := dvd_mul_of_dvd_right hgb _
  have hh : g ∣ (directPrefix L).den * Q.derivative.eval 1 := by
    convert dvd_sub hdb hd using 1
    ring
  exact hc.dvd_of_dvd_mul_left hh

end DirectPadeDerivativeCongruence

#print axioms DirectPadeDerivativeCongruence.weighted_prefix_congruence
#print axioms DirectPadeDerivativeCongruence.factorial_dvd_numerator_sub_derivative
#print axioms DirectPadeDerivativeCongruence.pade_factorial_dvd_numerator_sub_derivative
#print axioms DirectPadeDerivativeCongruence.factorial_common_factor_dvd_derivative
