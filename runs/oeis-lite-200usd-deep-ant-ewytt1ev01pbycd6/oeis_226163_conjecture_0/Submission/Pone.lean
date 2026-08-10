import FormalConjectures.Util.ProblemImports

open Matrix Finset

/-- p ≡ 1 mod 4 direction: the reduced matrix mod p is nonsingular. -/
theorem detMbar_ne {p : ℕ} [Fact p.Prime] (hp1 : p % 4 = 1) :
    (Matrix.of (fun i j : Fin (p / 2) =>
      (((i : ℕ) + 1 : ZMod p) ^ 2 - ((Nat.factorial (p / 2)) : ZMod p) * ((j : ℕ) + 1 : ZMod p)) ^ (p / 2))).det ≠ 0 := by
  classical
  have hp : p.Prime := Fact.out
  set m := p / 2 with hm
  -- Numeric facts
  have hodd : p % 2 = 1 := by omega
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  have hpm : p = 2 * m + 1 := by omega
  have hmp : m < p := by omega
  have hm2 : 2 ≤ m := by omega
  have hmeven : m % 2 = 0 := by omega
  have hmEven : Even m := Nat.even_iff.mpr hmeven
  -- F = m! mod p
  set F : ZMod p := (Nat.factorial m : ZMod p) with hF
  have hm1 : (-1 : ZMod p) ^ m = 1 := hmEven.neg_one_pow
  have hm2' : (-1 : ZMod p) ^ (m + 1) = -1 := by rw [pow_succ, hm1, one_mul]
  have hFne : F ≠ 0 := by
    rw [hF, ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have : p ≤ m := hp.dvd_factorial.mp hdvd
    omega
  have hchoose : ∀ t, t ≤ m → (m.choose t : ZMod p) ≠ 0 := by
    intro t ht hc
    have h1 : m.choose t * Nat.factorial t * Nat.factorial (m - t) = Nat.factorial m := Nat.choose_mul_factorial_mul_factorial ht
    have h2 : ((m.choose t : ℕ) : ZMod p) * ((Nat.factorial t : ℕ) : ZMod p) * ((Nat.factorial (m - t) : ℕ) : ZMod p)
        = ((Nat.factorial m : ℕ) : ZMod p) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, h1]
    rw [hc, zero_mul, zero_mul] at h2
    exact hFne (hF.trans h2.symm)
  have hne : ∀ i : Fin m, ((i : ℕ) + 1 : ZMod p) ≠ 0 := by
    intro i hcon
    rw [show ((i : ℕ) + 1 : ZMod p) = (((i : ℕ) + 1 : ℕ) : ZMod p) by push_cast; ring,
        ZMod.natCast_eq_zero_iff] at hcon
    have hle := Nat.le_of_dvd (by omega) hcon
    have := i.2
    omega
  have hsinj : Function.Injective (fun j : Fin m => ((j : ℕ) + 1 : ZMod p)) := by
    intro a b hab
    have ha := a.2
    have hb := b.2
    dsimp only at hab
    rw [show ((a : ℕ) + 1 : ZMod p) = (((a : ℕ) + 1 : ℕ) : ZMod p) by push_cast; ring,
        show ((b : ℕ) + 1 : ZMod p) = (((b : ℕ) + 1 : ℕ) : ZMod p) by push_cast; ring,
        ZMod.natCast_eq_natCast_iff'] at hab
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hab
    exact Fin.ext (by omega)
  have hρinj : Function.Injective (fun i : Fin m => (((i : ℕ) + 1 : ZMod p)) ^ 2) := by
    intro a b hab
    have ha := a.2
    have hb := b.2
    dsimp only at hab
    have hfac : (((a : ℕ) + 1 : ZMod p) - ((b : ℕ) + 1)) * (((a : ℕ) + 1 : ZMod p) + ((b : ℕ) + 1)) = 0 := by
      linear_combination hab
    rcases mul_eq_zero.mp hfac with h | h
    · have hthis : ((a : ℕ) + 1 : ZMod p) = ((b : ℕ) + 1) := by linear_combination h
      rw [show ((a : ℕ) + 1 : ZMod p) = (((a : ℕ) + 1 : ℕ) : ZMod p) by push_cast; ring,
          show ((b : ℕ) + 1 : ZMod p) = (((b : ℕ) + 1 : ℕ) : ZMod p) by push_cast; ring,
          ZMod.natCast_eq_natCast_iff'] at hthis
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hthis
      exact Fin.ext (by omega)
    · exfalso
      rw [show ((a : ℕ) + 1 : ZMod p) + ((b : ℕ) + 1) = (((a : ℕ) + 1 + ((b : ℕ) + 1) : ℕ) : ZMod p) by push_cast; ring,
          ZMod.natCast_eq_zero_iff] at h
      have hle := Nat.le_of_dvd (by omega) h
      omega
  have hXpow : ∀ i : Fin m, (((i : ℕ) + 1 : ZMod p) ^ 2) ^ m = 1 := by
    intro i
    rw [← pow_mul, show 2 * m = p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one (hne i)
  ----------------------------------------------------------------------------
  -- Wilson block: F^2 = -1 and F^(m+1) ≠ 1
  ----------------------------------------------------------------------------
  have hprodF : (∏ i ∈ range m, ((i : ZMod p) + 1)) = F := by
    have hh : (∏ i ∈ range m, ((i : ℕ) + 1) : ℕ) = Nat.factorial m := Finset.prod_range_add_one_eq_factorial m
    rw [hF, ← hh]
    push_cast
    rfl
  have hcast : ((2 * m).factorial : ZMod p) = ∏ i ∈ range (2 * m), ((i : ZMod p) + 1) := by
    rw [Nat.factorial_eq_prod_range_add_one]
    push_cast
    rfl
  have hsplit : (∏ i ∈ range (2 * m), ((i : ZMod p) + 1))
      = (∏ i ∈ range m, ((i : ZMod p) + 1)) * (∏ i ∈ range m, (((m + i : ℕ) : ZMod p) + 1)) := by
    rw [two_mul, Finset.prod_range_add]
  have hterm : ∀ i ∈ range m, ((m + i : ℕ) : ZMod p) + 1 = -((m - i : ℕ) : ZMod p) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hzero : ((m + i : ℕ) : ZMod p) + 1 + ((m - i : ℕ) : ZMod p) = 0 := by
      rw [show ((m + i : ℕ) : ZMod p) + 1 = ((m + i + 1 : ℕ) : ZMod p) by push_cast; ring,
          ← Nat.cast_add, show (m + i + 1) + (m - i) = p by omega, ZMod.natCast_self]
    exact eq_neg_of_add_eq_zero_left hzero
  have hrefl : (∏ i ∈ range m, ((m - i : ℕ) : ZMod p)) = (∏ i ∈ range m, ((i : ZMod p) + 1)) := by
    rw [← Finset.prod_range_reflect (fun j => ((j : ZMod p) + 1)) m]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hmi : m - i = (m - 1 - i) + 1 := by omega
    rw [hmi]
    push_cast
    ring
  have hsecond : (∏ i ∈ range m, (((m + i : ℕ) : ZMod p) + 1)) = (-1) ^ m * F := by
    rw [Finset.prod_congr rfl hterm, Finset.prod_neg, Finset.card_range, hrefl, hprodF]
  have hfact2 : ((2 * m).factorial : ZMod p) = (-1) ^ m * F ^ 2 := by
    rw [hcast, hsplit, hprodF, hsecond]
    ring
  have hF2 : F ^ 2 = -1 := by
    have hw' : ((2 * m).factorial : ZMod p) = -1 := by
      have := ZMod.wilsons_lemma (p := p)
      rwa [show p - 1 = 2 * m by omega] at this
    rw [hfact2, hm1, one_mul] at hw'
    exact hw'
  have h1ne : (1 : ZMod p) ≠ -1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hle := Nat.le_of_dvd (by norm_num) h2
    omega
  have hFne1 : F ≠ 1 := by
    intro h
    have heq : F ^ 2 = (1 : ZMod p) ^ 2 := by rw [h]
    rw [hF2, one_pow] at heq
    exact h1ne heq.symm
  have hFnem1 : F ≠ -1 := by
    intro h
    have heq : F ^ 2 = (-1 : ZMod p) ^ 2 := by rw [h]
    rw [hF2, neg_one_sq] at heq
    exact h1ne heq.symm
  have hFm1 : F ^ (m + 1) ≠ 1 := by
    have hmm : m + 1 = 2 * (m / 2) + 1 := by omega
    rcases Nat.even_or_odd (m / 2) with he | ho
    · intro hcon
      rw [hmm, pow_succ, pow_mul, hF2, he.neg_one_pow, one_mul] at hcon
      exact hFne1 hcon
    · intro hcon
      rw [hmm, pow_succ, pow_mul, hF2, ho.neg_one_pow, neg_one_mul] at hcon
      exact hFnem1 (by linear_combination -hcon)
  ----------------------------------------------------------------------------
  -- Set up the matrix and obtain a nontrivial kernel vector
  ----------------------------------------------------------------------------
  set M := Matrix.of (fun i j : Fin m =>
      (((i : ℕ) + 1 : ZMod p) ^ 2 - F * ((j : ℕ) + 1 : ZMod p)) ^ m) with hMdef
  intro hdet
  obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  -- moments
  set μ : ℕ → ZMod p := fun k => ∑ j : Fin m, v j * ((j : ℕ) + 1 : ZMod p) ^ k with hμ
  set a : ℕ → ZMod p := fun t => (m.choose t : ZMod p) * (-F) ^ (m - t) * μ (m - t) with ha
  ----------------------------------------------------------------------------
  -- STEP 1: the row equation
  ----------------------------------------------------------------------------
  have key : ∀ i : Fin m, ∑ t ∈ range (m + 1), (((i : ℕ) + 1 : ZMod p) ^ 2) ^ t * a t = 0 := by
    intro i
    have h0' : (∑ j : Fin m, M i j * v j) = 0 := by
      have h := congrFun hMv i
      simpa [Matrix.mulVec, dotProduct] using h
    have e1 : ∀ j : Fin m, M i j * v j
        = ∑ t ∈ range (m + 1), (((i : ℕ) + 1 : ZMod p) ^ 2) ^ t
            * ((-F) ^ (m - t) * (((j : ℕ) + 1 : ZMod p)) ^ (m - t)) * (m.choose t : ZMod p) * v j := by
      intro j
      simp only [hMdef, Matrix.of_apply]
      rw [sub_eq_add_neg, ← neg_mul, add_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [mul_pow]
    have step1 : (∑ j : Fin m, M i j * v j)
        = ∑ t ∈ range (m + 1), (((i : ℕ) + 1 : ZMod p) ^ 2) ^ t * a t := by
      rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => e1 j)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      simp only [ha, hμ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [← step1]; exact h0'
  ----------------------------------------------------------------------------
  -- STEP 2: Fermat reduces degree
  ----------------------------------------------------------------------------
  have step2 : ∀ i : Fin m, ∑ t ∈ range m, (((i : ℕ) + 1 : ZMod p) ^ 2) ^ t * a t = - μ 0 := by
    intro i
    have hk := key i
    rw [Finset.sum_range_succ, hXpow i, one_mul] at hk
    have ham : a m = μ 0 := by simp [ha]
    rw [ham] at hk
    linear_combination hk
  ----------------------------------------------------------------------------
  -- STEP 3: Vandermonde inversion #1
  ----------------------------------------------------------------------------
  set w : Fin m → ZMod p := fun t => a (t : ℕ) + (if (t : ℕ) = 0 then μ 0 else 0) with hw
  have hwv : ∀ j : Fin m, ∑ i : Fin m, (((j : ℕ) + 1 : ZMod p) ^ 2) ^ (i : ℕ) * w i = 0 := by
    intro j
    have hsplit2 : ∑ i : Fin m, (((j : ℕ) + 1 : ZMod p) ^ 2) ^ (i : ℕ) * w i
        = (∑ i : Fin m, (((j : ℕ) + 1 : ZMod p) ^ 2) ^ (i : ℕ) * a (i : ℕ))
          + ∑ i : Fin m, (((j : ℕ) + 1 : ZMod p) ^ 2) ^ (i : ℕ) * (if (i : ℕ) = 0 then μ 0 else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hw]
      ring
    rw [hsplit2]
    have hA : (∑ i : Fin m, (((j : ℕ) + 1 : ZMod p) ^ 2) ^ (i : ℕ) * a (i : ℕ)) = - μ 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun t => (((j : ℕ) + 1 : ZMod p) ^ 2) ^ t * a t) m]
      exact step2 j
    have hB : (∑ i : Fin m, (((j : ℕ) + 1 : ZMod p) ^ 2) ^ (i : ℕ) * (if (i : ℕ) = 0 then μ 0 else 0)) = μ 0 := by
      rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin m)]
      · simp
      · intro i _ hi
        rw [if_neg (fun h => hi (Fin.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hA, hB]; ring
  have hw0 : w = 0 :=
    eq_zero_of_forall_index_sum_pow_mul_eq_zero
      (f := fun i : Fin m => (((i : ℕ) + 1 : ZMod p)) ^ 2) hρinj hwv
  have hwk : ∀ i : Fin m, w i = 0 := fun i => congrFun hw0 i
  have ha0' : a 0 + μ 0 = 0 := by
    have h := hwk (⟨0, by omega⟩ : Fin m)
    simpa [hw] using h
  have hak : ∀ k, 1 ≤ k → k < m → a k = 0 := by
    intro k hk1 hk2
    have h := hwk (⟨k, hk2⟩ : Fin m)
    have hk0 : ¬ (k = 0) := by omega
    simpa [hw, hk0] using h
  ----------------------------------------------------------------------------
  -- STEP 4: extract moment conditions
  ----------------------------------------------------------------------------
  have hμk : ∀ k, 1 ≤ k → k < m → μ k = 0 := by
    intro k hk1 hk2
    have hat : a (m - k) = 0 := hak (m - k) (by omega) (by omega)
    have ha' : (↑(m.choose (m - k)) : ZMod p) * (-F) ^ k * μ k = 0 := by
      have hthis := hat
      simp only [ha] at hthis
      rw [show m - (m - k) = k by omega] at hthis
      exact hthis
    rcases mul_eq_zero.mp ha' with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (hchoose (m - k) (by omega))
      · exact absurd h' (pow_ne_zero _ (neg_ne_zero.mpr hFne))
    · exact h
  have hstar : (-F) ^ m * μ m = - μ 0 := by
    have ea0 : a 0 = (-F) ^ m * μ m := by
      simp only [ha, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
    have hthis : a 0 = - μ 0 := by linear_combination ha0'
    rw [ea0] at hthis
    exact hthis
  ----------------------------------------------------------------------------
  -- STEP 5: Newton via the polynomial g = ∏ (X - (k+1))
  ----------------------------------------------------------------------------
  set g : Polynomial (ZMod p) := ∏ k ∈ range m, (Polynomial.X - Polynomial.C ((k : ℕ) + 1 : ZMod p)) with hg
  have P2 : ∀ j : Fin m, g.eval (((j : ℕ) + 1 : ZMod p)) = 0 := by
    intro j
    rw [hg, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_range.mpr j.2) ?_
    simp [Polynomial.eval_sub, Polynomial.eval_X]
  have hdeg : g.natDegree < m + 1 := by
    have h1 : g.natDegree ≤ ∑ k ∈ range m, (Polynomial.X - Polynomial.C ((k : ℕ) + 1 : ZMod p)).natDegree := by
      rw [hg]; exact Polynomial.natDegree_prod_le _ _
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul,
      mul_one] at h1
    omega
  have hdegeq : g.natDegree = m := by
    rw [hg, Polynomial.natDegree_prod]
    · simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul,
        mul_one]
    · intro k _; exact Polynomial.X_sub_C_ne_zero _
  have hmonic : g.Monic := by
    rw [hg]
    exact Polynomial.monic_prod_of_monic _ _ (fun k _ => Polynomial.monic_X_sub_C _)
  have P4 : g.coeff m = 1 := by
    have h := hmonic.coeff_natDegree
    rwa [hdegeq] at h
  have P3 : g.coeff 0 = (-1) ^ m * F := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hg, Polynomial.eval_prod]
    have hterm3 : ∀ k ∈ range m,
        Polynomial.eval 0 (Polynomial.X - Polynomial.C ((k : ℕ) + 1 : ZMod p)) = -(((k : ℕ) + 1 : ZMod p)) := by
      intro k _
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    rw [Finset.prod_congr rfl hterm3, Finset.prod_neg, Finset.card_range, hprodF]
  have P5 : ∑ l ∈ range (m + 1), g.coeff l * μ l = 0 := by
    have key2 : ∀ j : Fin m,
        g.eval (((j : ℕ) + 1 : ZMod p)) = ∑ l ∈ range (m + 1), g.coeff l * (((j : ℕ) + 1 : ZMod p)) ^ l := by
      intro j
      exact Polynomial.eval_eq_sum_range' hdeg _
    calc ∑ l ∈ range (m + 1), g.coeff l * μ l
        = ∑ l ∈ range (m + 1), ∑ j : Fin m, g.coeff l * (v j * (((j : ℕ) + 1 : ZMod p)) ^ l) := by
          apply Finset.sum_congr rfl
          intro l _
          simp only [hμ, Finset.mul_sum]
      _ = ∑ j : Fin m, ∑ l ∈ range (m + 1), g.coeff l * (v j * (((j : ℕ) + 1 : ZMod p)) ^ l) :=
          Finset.sum_comm
      _ = ∑ j : Fin m, v j * g.eval (((j : ℕ) + 1 : ZMod p)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [key2 j, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
      _ = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          rw [P2 j, mul_zero]
  have hnewton : μ m = (-1) ^ (m + 1) * F * μ 0 := by
    have hsum := P5
    rw [Finset.sum_range_succ, P4, one_mul] at hsum
    have hmid : (∑ l ∈ range m, g.coeff l * μ l) = g.coeff 0 * μ 0 := by
      rw [Finset.sum_eq_single 0]
      · intro l hl hl0
        rw [Finset.mem_range] at hl
        rw [hμk l (by omega) hl, mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hmid, P3] at hsum
    linear_combination hsum
  ----------------------------------------------------------------------------
  -- STEP 6: combine
  ----------------------------------------------------------------------------
  have hstar' : F ^ m * μ m = - μ 0 := by
    rw [← hstar, neg_pow, hm1, one_mul]
  have hnewton' : μ m = - F * μ 0 := by
    rw [hnewton, hm2']
    ring
  have hcombine : (F ^ (m + 1) - 1) * μ 0 = 0 := by
    have htmp : F ^ m * (- F * μ 0) = - μ 0 := by rw [← hnewton']; exact hstar'
    rw [pow_succ]
    linear_combination - htmp
  ----------------------------------------------------------------------------
  -- STEP 7/8: μ 0 = 0, all moments vanish, v = 0
  ----------------------------------------------------------------------------
  have hμ0 : μ 0 = 0 := by
    rcases mul_eq_zero.mp hcombine with h | h
    · exact absurd (by linear_combination h : F ^ (m + 1) = 1) hFm1
    · exact h
  have hμall : ∀ k, k < m → μ k = 0 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0]; exact hμ0
    · exact hμk k h0 hk
  have hvzero : v = 0 := by
    apply eq_zero_of_forall_pow_sum_mul_pow_eq_zero hsinj
    intro i
    have h := hμall (i : ℕ) i.2
    rw [hμ] at h
    exact h
  exact hv0 hvzero
