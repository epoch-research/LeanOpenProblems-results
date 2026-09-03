import Submission.SelbergCost

/-! Logarithmic upper bounds for the Selberg normalizing sum. These are
auxiliary sieve estimates, not the quadratic Jacobsthal conjecture. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def coprimeHarmonic (N R : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 R).filter (fun n => N.Coprime n), 1 / (n : ℝ)

lemma coprimeHarmonic_le (N R : ℕ) (hN : 0 < N) :
    coprimeHarmonic N R ≤ (N : ℝ) + (N.totient : ℝ) / N * (1 + log R) := by
  classical
  let S := (Icc 1 R).filter (fun n => N.Coprime n)
  let U := (range N).filter (fun n => N.Coprime n)
  have hsplit := sum_filter_add_sum_filter_not S (fun n => n < N)
    (fun n => 1 / (n : ℝ))
  have hsmall : (∑ n ∈ S.filter (fun n => n < N), 1 / (n : ℝ)) ≤ N := by
    calc
      _ ≤ ∑ _n ∈ S.filter (fun n => n < N), (1 : ℝ) := by
        apply sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hn).1).1).1
        exact (div_le_one (by exact_mod_cast (show 0 < n by omega))).mpr
          (by exact_mod_cast hn1)
      _ = ((S.filter (fun n => n < N)).card : ℝ) := by simp
      _ ≤ N := by
        exact_mod_cast (show (S.filter (fun n => n < N)).card ≤ N from
          (card_le_card (show S.filter (fun n => n < N) ⊆ range N from
            fun n hn => mem_range.mpr (mem_filter.mp hn).2)).trans_eq (card_range N))
  let T := S.filter (fun n => ¬n < N)
  let f : ℕ → ℕ × ℕ := fun n => (n / N, n % N)
  have hf : Function.Injective f := by
    intro a b hab
    have hq := congrArg Prod.fst hab
    have hr := congrArg Prod.snd hab
    dsimp [f] at hq hr
    have ha := Nat.mod_add_div a N
    have hb := Nat.mod_add_div b N
    rw [hq, hr] at ha
    exact ha.symm.trans hb
  have hmaps : T.image f ⊆ Icc 1 R ×ˢ U := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    obtain ⟨hnS, hnN⟩ := mem_filter.mp hn
    obtain ⟨hnR, hnc⟩ := mem_filter.mp hnS
    obtain ⟨hn1, hnR⟩ := mem_Icc.mp hnR
    refine mem_product.mpr ⟨mem_Icc.mpr ⟨Nat.div_pos (by omega) hN,
      (Nat.div_le_self n N).trans hnR⟩, ?_⟩
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt n hN), by
      change Nat.gcd N (n % N) = 1
      rw [Nat.gcd_comm, ← Nat.gcd_rec]
      exact hnc⟩
  have hlarge : (∑ n ∈ T, 1 / (n : ℝ)) ≤
      (N.totient : ℝ) / N * (harmonic R : ℝ) := by
    calc
      _ ≤ ∑ n ∈ T, 1 / ((N : ℝ) * (n / N : ℕ)) := by
        apply sum_le_sum
        intro n hn
        have hnN : N ≤ n := by have := (mem_filter.mp hn).2; omega
        have hq : 0 < n / N := Nat.div_pos hnN hN
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast (Nat.mul_div_le n N)
      _ = ∑ z ∈ T.image f, 1 / ((N : ℝ) * (z.1 : ℝ)) := by
        rw [sum_image hf.injOn]
      _ ≤ ∑ z ∈ Icc 1 R ×ˢ U, 1 / ((N : ℝ) * (z.1 : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hmaps (fun _ _ _ => by positivity)
      _ = (N.totient : ℝ) / N * (harmonic R : ℝ) := by
        rw [sum_product]
        simp only [sum_const, nsmul_eq_mul]
        have hU : U.card = N.totient := (Nat.totient_eq_card_coprime N).symm
        rw [hU]
        rw [harmonic_eq_sum_Icc]
        push_cast
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log R)
    (show 0 ≤ (N.totient : ℝ) / N by positivity)
  change _ = coprimeHarmonic N R at hsplit
  change _ + (∑ n ∈ T, 1 / (n : ℝ)) = _ at hsplit
  linarith

noncomputable def primeWeight (Q : Finset ℕ) : ℝ :=
  ∏ p ∈ Q, 1 / ((p : ℝ) - 1)

noncomputable def primeNormalizer (P : Finset ℕ) (R : ℕ) : ℝ :=
  ∑ Q ∈ smallDivisorFamily P R, primeWeight Q

lemma primeWeight_nonneg (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    0 ≤ primeWeight Q := by
  apply prod_nonneg
  intro p hp
  have : (1 : ℝ) < p := by exact_mod_cast (hQ p hp).one_lt
  exact (one_div_pos.mpr (sub_pos.mpr this)).le

lemma primeWeight_expansion (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    primeWeight Q = (1 / (∏ p ∈ Q, p : ℕ) : ℝ) *
      ∑ T ∈ Q.powerset, primeWeight T := by
  unfold primeWeight
  rw [← prod_one_add]
  rw [Nat.cast_prod, one_div, ← prod_inv_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hQ p hp).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast (hQ p hp).one_lt
    linarith
  field_simp
  <;> ring

lemma superset_reciprocal_sum_le (P T : Finset ℕ) (N R : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPN : ∀ p ∈ P, N.Coprime p) :
    (∑ Q ∈ (smallDivisorFamily P R).filter (fun Q => T ⊆ Q),
      (1 / (∏ p ∈ Q, p : ℕ) : ℝ)) ≤
      (1 / (∏ p ∈ T, p : ℕ) : ℝ) * coprimeHarmonic N R := by
  classical
  let S := (smallDivisorFamily P R).filter (fun Q => T ⊆ Q)
  let f : Finset ℕ → ℕ := fun Q => ∏ p ∈ Q \ T, p
  have hmaps : S.image f ⊆ (Icc 1 R).filter (fun n => N.Coprime n) := by
    intro n hn
    obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hn
    obtain ⟨hQR, hTQ⟩ := mem_filter.mp hQ
    obtain ⟨hQP, hQR⟩ := mem_smallDivisorFamily P Q R |>.mp hQR
    have hf0 : 0 < f Q := prod_pos (fun p hp => (hP p (hQP (mem_sdiff.mp hp).1)).pos)
    have hfQ : f Q ≤ ∏ p ∈ Q, p :=
      prod_le_prod_of_subset_of_one_le' sdiff_subset (fun p hp _ => (hP p (hQP hp)).one_le)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hf0, hfQ.trans hQR⟩, ?_⟩
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    exact hPN p (hQP (mem_sdiff.mp hp).1)
  have hinj : Set.InjOn f (↑S : Set (Finset ℕ)) := by
    intro A hA B hB hab
    have ha := mem_filter.mp hA
    have hb := mem_filter.mp hB
    have hAP := (mem_smallDivisorFamily P A R |>.mp ha.1).1
    have hBP := (mem_smallDivisorFamily P B R |>.mp hb.1).1
    have he : (∏ p ∈ A, p) = ∏ p ∈ B, p := by
      rw [← prod_sdiff ha.2, ← prod_sdiff hb.2]
      change f A * _ = f B * _
      rw [hab]
    have hfacA := Nat.primeFactors_prod (fun p hp => hP p (hAP hp))
    have hfacB := Nat.primeFactors_prod (fun p hp => hP p (hBP hp))
    rw [← hfacA, ← hfacB, he]
  calc
    _ = (1 / (∏ p ∈ T, p : ℕ) : ℝ) * ∑ Q ∈ S, 1 / (f Q : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro Q hQ
      have hprod := prod_sdiff (f := id) (mem_filter.mp hQ).2
      have he : (∏ p ∈ Q, p : ℕ) = f Q * ∏ p ∈ T, p := hprod.symm
      rw [he, Nat.cast_mul]
      simp only [one_div, mul_inv_rev]
    _ = (1 / (∏ p ∈ T, p : ℕ) : ℝ) * ∑ n ∈ S.image f, 1 / (n : ℝ) := by
      rw [sum_image hinj]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum_of_subset_of_nonneg hmaps (fun _ _ _ => by positivity)

lemma rough_primeNormalizer_le (P : Finset ℕ) (N R : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPN : ∀ p ∈ P, N.Coprime p) :
    primeNormalizer P R ≤ coprimeHarmonic N R *
      ∏ p ∈ P, (1 + 1 / ((p : ℝ) * (p - 1))) := by
  classical
  have hexp (Q : Finset ℕ) (hQ : Q ∈ smallDivisorFamily P R) :
      primeWeight Q = ∑ T ∈ P.powerset,
        if T ⊆ Q then primeWeight T * (1 / (∏ p ∈ Q, p : ℕ) : ℝ) else 0 := by
    have hQP := (mem_smallDivisorFamily P Q R |>.mp hQ).1
    rw [primeWeight_expansion Q (fun p hp => hP p (hQP hp))]
    have he : P.powerset.filter (fun T => T ⊆ Q) = Q.powerset := by
      ext T
      simp only [mem_filter, mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨h.trans hQP, h⟩⟩
    rw [← sum_filter, he, mul_sum]
    apply sum_congr rfl
    intro T hT
    ring
  rw [primeNormalizer, sum_congr rfl hexp, sum_comm]
  calc
    _ = ∑ T ∈ P.powerset, primeWeight T *
        ∑ Q ∈ (smallDivisorFamily P R).filter (fun Q => T ⊆ Q),
          (1 / (∏ p ∈ Q, p : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro T hT
      rw [← sum_filter, mul_sum]
    _ ≤ ∑ T ∈ P.powerset, primeWeight T *
        ((1 / (∏ p ∈ T, p : ℕ) : ℝ) * coprimeHarmonic N R) := by
      apply sum_le_sum
      intro T hT
      exact mul_le_mul_of_nonneg_left (superset_reciprocal_sum_le P T N R hP hPN)
        (primeWeight_nonneg T (fun p hp => hP p (mem_powerset.mp hT hp)))
    _ = coprimeHarmonic N R * ∏ p ∈ P, (1 + 1 / ((p : ℝ) * (p - 1))) := by
      rw [prod_one_add, mul_sum]
      apply sum_congr rfl
      intro T hT
      unfold primeWeight
      rw [Nat.cast_prod, one_div, ← prod_inv_distrib]
      have he : (∏ p ∈ T, 1 / ((p : ℝ) - 1)) * (∏ p ∈ T, (p : ℝ)⁻¹) =
          ∏ p ∈ T, 1 / ((p : ℝ) * (p - 1)) := by
        rw [← prod_mul_distrib]
        apply prod_congr rfl
        intro p hp
        simp only [one_div, mul_inv_rev]
      rw [← he]
      ring

lemma primeNormalizer_nonneg (P : Finset ℕ) (R : ℕ)
    (hP : ∀ p ∈ P, p.Prime) : 0 ≤ primeNormalizer P R := by
  apply sum_nonneg
  intro Q hQ
  exact primeWeight_nonneg Q (fun p hp => hP p ((mem_smallDivisorFamily P Q R |>.mp hQ).1 hp))

lemma primeNormalizer_mono (P Q : Finset ℕ) (R : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q) :
    primeNormalizer P R ≤ primeNormalizer Q R := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro T hT
    obtain ⟨hTP, hTR⟩ := mem_smallDivisorFamily P T R |>.mp hT
    exact (mem_smallDivisorFamily Q T R).mpr ⟨hTP.trans hPQ, hTR⟩
  · intro T hT _
    exact primeWeight_nonneg T (fun p hp => hQ p ((mem_smallDivisorFamily Q T R |>.mp hT).1 hp))

lemma primeNormalizer_as_sum (P : Finset ℕ) (R : ℕ) :
    primeNormalizer P R = ∑ Q ∈ P.powerset,
      if (∏ p ∈ Q, p) ≤ R then primeWeight Q else 0 := by
  simp only [primeNormalizer, smallDivisorFamily, sum_filter]

lemma primeNormalizer_insert_le (P : Finset ℕ) (p R : ℕ)
    (hP : ∀ q ∈ P, q.Prime) (hp : p.Prime) :
    primeNormalizer (insert p P) R ≤ (1 + 1 / ((p : ℝ) - 1)) * primeNormalizer P R := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hw : 0 ≤ 1 / ((p : ℝ) - 1) := (one_div_pos.mpr (sub_pos.mpr hp1)).le
  by_cases hpmem : p ∈ P
  · rw [insert_eq_of_mem hpmem]
    have hh := mul_nonneg hw (primeNormalizer_nonneg P R hP)
    nlinarith only [hh]
  · rw [primeNormalizer_as_sum, sum_powerset_insert hpmem, ← primeNormalizer_as_sum]
    have hsum : (∑ Q ∈ P.powerset,
        if (∏ q ∈ insert p Q, q) ≤ R then primeWeight (insert p Q) else 0) ≤
        (1 / ((p : ℝ) - 1)) * primeNormalizer P R := by
      rw [primeNormalizer_as_sum, mul_sum]
      apply sum_le_sum
      intro Q hQ
      have hQP := mem_powerset.mp hQ
      have hpQ : p ∉ Q := fun hh => hpmem (hQP hh)
      rw [prod_insert hpQ]
      by_cases hprod : p * (∏ q ∈ Q, q) ≤ R
      · rw [if_pos hprod]
        have hQR : (∏ q ∈ Q, q) ≤ R := by
          have hh := Nat.le_mul_of_pos_left (∏ q ∈ Q, q) hp.pos
          exact hh.trans hprod
        rw [if_pos hQR]
        simp only [primeWeight, prod_insert hpQ, le_refl]
      · rw [if_neg hprod]
        apply mul_nonneg hw
        split_ifs
        · exact primeWeight_nonneg Q (fun q hq => hP q (hQP hq))
        · rfl
    nlinarith only [hsum]

lemma primeNormalizer_union_le (H P : Finset ℕ) (R : ℕ)
    (hH : ∀ p ∈ H, p.Prime) (hP : ∀ p ∈ P, p.Prime) :
    primeNormalizer (H ∪ P) R ≤
      (∏ p ∈ H, (1 + 1 / ((p : ℝ) - 1))) * primeNormalizer P R := by
  classical
  induction H using Finset.induction_on with
  | empty => simp
  | @insert p H hpH ih =>
    have hp := hH p (mem_insert_self _ _)
    have hH' := fun q hq => hH q (mem_insert_of_mem hq)
    rw [insert_union, prod_insert hpH]
    have hh := primeNormalizer_insert_le (H ∪ P) p R
      (fun q hq => (mem_union.mp hq).elim (hH' q) (hP q)) hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hcoef : 0 ≤ 1 + 1 / ((p : ℝ) - 1) := by
      have : 0 < (p : ℝ) - 1 := by linarith
      positivity
    exact hh.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (ih hH') hcoef)

lemma correction_tail_le (P : Finset ℕ) (B : ℕ) (hB : 0 < B)
    (hP : ∀ p ∈ P, B < p) :
    (∑ p ∈ P, 1 / ((p : ℝ) * (p - 1))) ≤ 1 / (B : ℝ) := by
  classical
  let M := B + P.sup id + 1
  have hBM : B ≤ M := by dsimp [M]; omega
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (↑P : Set ℕ) := by
    intro p hp q hq he
    dsimp only at he
    have := hP p hp
    have := hP q hq
    omega
  have hmaps : P.image (fun p : ℕ => p - 1) ⊆ Ico B M := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    have hlo := hP p hp
    have hhi : p ≤ P.sup id := le_sup (f := id) hp
    exact mem_Ico.mpr ⟨by omega, by dsimp [M]; omega⟩
  have hterm (p : ℕ) (hp : p ∈ P) :
      1 / ((p : ℝ) * (p - 1)) = -(1 / ((p - 1 + 1 : ℕ) : ℝ)) - -(1 / ((p - 1 : ℕ) : ℝ)) := by
    have hp2 : 2 ≤ p := by have := hP p hp; omega
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p), Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    field_simp
    <;> ring
  calc
    _ = ∑ p ∈ P, (-(1 / ((p - 1 + 1 : ℕ) : ℝ)) - -(1 / ((p - 1 : ℕ) : ℝ))) :=
      sum_congr rfl hterm
    _ = ∑ n ∈ P.image (fun p : ℕ => p - 1), (-(1 / ((n + 1 : ℕ) : ℝ)) - -(1 / (n : ℝ))) := by
      rw [sum_image hinj]
    _ ≤ ∑ n ∈ Ico B M, (-(1 / ((n + 1 : ℕ) : ℝ)) - -(1 / (n : ℝ))) := by
      apply sum_le_sum_of_subset_of_nonneg hmaps
      intro n hn _
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Ico.mp hn).1; omega)
      have hh := one_div_le_one_div_of_le hn0
        (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast (Nat.le_succ n))
      linarith
    _ = -(1 / (M : ℝ)) - -(1 / (B : ℝ)) := sum_Ico_sub (fun n : ℕ => -(1 / (n : ℝ))) hBM
    _ ≤ _ := by
      have : 0 ≤ 1 / (M : ℝ) := by positivity
      linarith

lemma correction_product_le (P : Finset ℕ) (B : ℕ) (hB : 0 < B)
    (hP : ∀ p ∈ P, B < p) :
    (∏ p ∈ P, (1 + 1 / ((p : ℝ) * (p - 1)))) ≤ exp (1 / (B : ℝ)) := by
  have hnon (p : ℕ) (hp : p ∈ P) : 0 ≤ 1 / ((p : ℝ) * (p - 1)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (show 2 ≤ p by have := hP p hp; omega)
    have : 0 ≤ (p : ℝ) - 1 := by linarith
    positivity
  calc
    _ ≤ ∏ p ∈ P, exp (1 / ((p : ℝ) * (p - 1))) := by
      apply prod_le_prod (fun p hp => by linarith [hnon p hp])
      intro p hp
      linarith [add_one_le_exp (1 / ((p : ℝ) * (p - 1)))]
    _ = exp (∑ p ∈ P, 1 / ((p : ℝ) * (p - 1))) := (exp_sum _ _).symm
    _ ≤ _ := exp_le_exp.mpr (correction_tail_le P B hB hP)

lemma totient_core_factor (N : ℕ) (hN : 0 < N) :
    (∏ p ∈ N.primeFactors, (1 + 1 / ((p : ℝ) - 1))) *
      ((N.totient : ℝ) / N) = 1 := by
  have he := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors N)
  push_cast at he
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [he, mul_div_cancel_left₀ _ hN0, ← prod_mul_distrib]
  apply prod_eq_one
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    linarith
  field_simp
  <;> ring

noncomputable def normalizerOffset (B : ℕ) : ℝ :=
  exp (1 / (B : ℝ)) *
    ((∏ p ∈ B.factorial.primeFactors, (1 + 1 / ((p : ℝ) - 1))) * B.factorial + 1)

lemma normalizerOffset_pos (B : ℕ) : 0 < normalizerOffset B := by
  unfold normalizerOffset
  apply mul_pos (exp_pos _)
  have hprod : 0 ≤ ∏ p ∈ B.factorial.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
    apply prod_nonneg
    intro p hp
    have hp1 : 0 < (p : ℝ) - 1 := by
      have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      linarith
    positivity
  positivity

/-- A finite small-prime core gives an upper coefficient arbitrarily close to
one, without an appeal to an asymptotic theorem about squarefree totients. -/
theorem primeNormalizer_log_upper (P : Finset ℕ) (R B : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hB : 0 < B) :
    primeNormalizer P R ≤ exp (1 / (B : ℝ)) * log R + normalizerOffset B := by
  classical
  let N := B.factorial
  let H := N.primeFactors
  let T := P \ H
  let a : ℝ := ∏ p ∈ H, (1 + 1 / ((p : ℝ) - 1))
  let d : ℝ := (N.totient : ℝ) / N
  have hN : 0 < N := Nat.factorial_pos B
  have hH : ∀ p ∈ H, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hT : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_sdiff.mp hp).1
  have hTN : ∀ p ∈ T, N.Coprime p := by
    intro p hp
    apply Nat.Coprime.symm
    apply (hT p hp).coprime_iff_not_dvd.mpr
    intro hdiv
    exact (mem_sdiff.mp hp).2 (Nat.mem_primeFactors.mpr ⟨hT p hp, hdiv, hN.ne'⟩)
  have hTB : ∀ p ∈ T, B < p := by
    intro p hp
    by_contra hbad
    have hd : p ∣ N := (hT p hp).dvd_factorial.mpr (by omega)
    exact ((hT p hp).coprime_iff_not_dvd.mp (hTN p hp).symm) hd
  have ha : 0 ≤ a := by
    apply prod_nonneg
    intro p hp
    have hp1 : 0 < (p : ℝ) - 1 := by
      have : (1 : ℝ) < p := by exact_mod_cast (hH p hp).one_lt
      linarith
    positivity
  have had : a * d = 1 := totient_core_factor N hN
  have hc0 : 0 ≤ coprimeHarmonic N R := sum_nonneg (fun _ _ => by positivity)
  have htail : primeNormalizer T R ≤
      ((N : ℝ) + d * (1 + log R)) * exp (1 / (B : ℝ)) := by
    calc
      _ ≤ coprimeHarmonic N R * ∏ p ∈ T, (1 + 1 / ((p : ℝ) * (p - 1))) :=
        rough_primeNormalizer_le T N R hT hTN
      _ ≤ coprimeHarmonic N R * exp (1 / (B : ℝ)) :=
        mul_le_mul_of_nonneg_left (correction_product_le T B hB hTB) hc0
      _ ≤ _ := mul_le_mul_of_nonneg_right (coprimeHarmonic_le N R hN) (exp_pos _).le
  have hsub : P ⊆ H ∪ T := by
    intro p hp
    by_cases hpH : p ∈ H
    · exact mem_union_left _ hpH
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hp, hpH⟩)
  calc
    _ ≤ primeNormalizer (H ∪ T) R := primeNormalizer_mono P (H ∪ T) R
      (fun p hp => (mem_union.mp hp).elim (hH p) (hT p)) hsub
    _ ≤ a * primeNormalizer T R := primeNormalizer_union_le H T R hH hT
    _ ≤ a * (((N : ℝ) + d * (1 + log R)) * exp (1 / (B : ℝ))) :=
      mul_le_mul_of_nonneg_left htail ha
    _ = exp (1 / (B : ℝ)) * log R + normalizerOffset B := by
      have he : a * (((N : ℝ) + d * (1 + log R)) * exp (1 / (B : ℝ))) =
          exp (1 / (B : ℝ)) * ((a * d) * log R + (a * N + a * d)) := by ring
      rw [he, had]
      simp only [one_mul]
      change _ = exp (1 / (B : ℝ)) * log R + exp (1 / (B : ℝ)) * (a * N + 1)
      ring

lemma exp_one_div_sixty_five_le : exp ((1 : ℝ) / 65) ≤ 65 / 64 := by
  have hl := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 65 / 64)
  have hh : (1 : ℝ) / 65 ≤ log (65 / 64) := by norm_num at hl ⊢; linarith
  have he := exp_le_exp.mpr hh
  simpa only [exp_log (by norm_num : (0 : ℝ) < 65 / 64)] using he

/-- A concrete near-sharp coefficient for the normalizer, uniform in P and R. -/
theorem primeNormalizer_log_upper_concrete (P : Finset ℕ) (R : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeNormalizer P R ≤ (65 / 64) * log R + normalizerOffset 65 := by
  have hl : 0 ≤ log (R : ℝ) := by
    by_cases hR : R = 0
    · simp [hR]
    · exact log_nonneg (by exact_mod_cast (show 1 ≤ R by omega))
  have hh := primeNormalizer_log_upper P R 65 hP (by omega)
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_right exp_one_div_sixty_five_le hl) le_rfl)

#print axioms coprimeHarmonic_le
#print axioms rough_primeNormalizer_le
#print axioms primeNormalizer_log_upper
#print axioms primeNormalizer_log_upper_concrete
end Erdos970.FiniteSelberg
