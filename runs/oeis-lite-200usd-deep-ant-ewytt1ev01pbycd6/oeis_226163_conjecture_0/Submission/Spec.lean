import FormalConjectures.Util.ProblemImports

set_option linter.unusedSectionVars false

open Matrix Finset

/-! ## Character sum over a monic quadratic (copied from CharSum). -/

section Helpers

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private lemma char_sum_sq :
    ∑ x : F, quadraticChar F (x ^ 2) = (Fintype.card F : ℤ) - 1 := by
  have h1 : ∀ x : F, quadraticChar F (x ^ 2) = (if x = 0 then (0 : ℤ) else 1) := by
    intro x
    rcases eq_or_ne x 0 with h | h
    · subst h
      rw [show (0 : F) ^ 2 = 0 from by ring, quadraticChar_zero]
      simp
    · rw [if_neg h]; exact quadraticChar_sq_one' h
  have e1 : ∑ x : F, (if x = 0 then (1 : ℤ) else 0) = 1 := by simp
  have e2 : ∑ _x : F, (1 : ℤ) = (Fintype.card F : ℤ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  calc ∑ x : F, quadraticChar F (x ^ 2)
      = ∑ x : F, (if x = 0 then (0 : ℤ) else 1) := Finset.sum_congr rfl (fun x _ => h1 x)
    _ = ∑ x : F, ((1 : ℤ) - (if x = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl; intro x _; by_cases hx : x = 0 <;> simp [hx]
    _ = (∑ _x : F, (1 : ℤ)) - ∑ x : F, (if x = 0 then (1 : ℤ) else 0) := by
        rw [Finset.sum_sub_distrib]
    _ = (Fintype.card F : ℤ) - 1 := by rw [e1, e2]

private lemma char_sum_sq_add (hF : ringChar F ≠ 2) (δ : F) :
    ∑ x : F, quadraticChar F (x ^ 2 + δ) =
      if δ = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  by_cases hδ : δ = 0
  · subst hδ; simpa using char_sum_sq
  · rw [if_neg hδ]
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    have hcard : ∀ x : F, (quadraticChar F (x ^ 2 + δ) + 1 : ℤ)
        = ((univ.filter (fun y => y ^ 2 = x ^ 2 + δ)).card : ℤ) := by
      intro x
      rw [← quadraticChar_card_sqrts hF (x ^ 2 + δ), Set.toFinset_setOf]
    have hfub : (univ.filter (fun p : F × F => p.2 ^ 2 = p.1 ^ 2 + δ)).card
        = ∑ x : F, (univ.filter (fun y => y ^ 2 = x ^ 2 + δ)).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.card_filter]
    have hbij : (univ.filter (fun p : F × F => p.2 ^ 2 = p.1 ^ 2 + δ)).card
        = (univ.filter (fun q : F × F => q.1 * q.2 = δ)).card := by
      apply Finset.card_nbij' (fun p : F × F => (p.2 - p.1, p.2 + p.1))
                              (fun q : F × F => ((q.2 - q.1) / 2, (q.2 + q.1) / 2))
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rw [show (p.2 - p.1) * (p.2 + p.1) = p.2 ^ 2 - p.1 ^ 2 from by ring, hp]; ring
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        have key : ((q.2 + q.1) / 2) ^ 2 - ((q.2 - q.1) / 2) ^ 2 = q.1 * q.2 := by
          rw [div_pow, div_pow, div_sub_div_same, div_eq_iff (pow_ne_zero 2 h2)]; ring
        rw [← hq, ← key]; ring
      · intro p _
        have e1 : ((p.2 + p.1) - (p.2 - p.1)) / 2 = p.1 := by rw [div_eq_iff h2]; ring
        have e2 : ((p.2 + p.1) + (p.2 - p.1)) / 2 = p.2 := by rw [div_eq_iff h2]; ring
        show (((p.2 + p.1) - (p.2 - p.1)) / 2, ((p.2 + p.1) + (p.2 - p.1)) / 2) = p
        rw [e1, e2]
      · intro q _
        have e1 : (q.2 + q.1) / 2 - (q.2 - q.1) / 2 = q.1 := by
          rw [div_sub_div_same, div_eq_iff h2]; ring
        have e2 : (q.2 + q.1) / 2 + (q.2 - q.1) / 2 = q.2 := by
          rw [← add_div, div_eq_iff h2]; ring
        show ((q.2 + q.1) / 2 - (q.2 - q.1) / 2, (q.2 + q.1) / 2 + (q.2 - q.1) / 2) = q
        rw [e1, e2]
    have hcount : (univ.filter (fun q : F × F => q.1 * q.2 = δ)).card = Fintype.card F - 1 := by
      have hcard_ne : (univ.filter (fun u : F => u ≠ 0)).card = Fintype.card F - 1 := by
        rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
      rw [← hcard_ne]
      apply Finset.card_nbij' (fun q : F × F => q.1) (fun u : F => (u, δ / u))
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        intro h0
        rw [h0, zero_mul] at hq
        exact hδ hq.symm
      · intro u hu
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        exact mul_div_cancel₀ δ hu
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        have hq1 : q.1 ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hq; exact hδ hq.symm
        show (q.1, δ / q.1) = q
        have : δ / q.1 = q.2 := by rw [div_eq_iff hq1, ← hq]; ring
        rw [this]
      · intro u hu
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        show ((u, δ / u) : F × F).1 = u
        rfl
    have hsum1 : (∑ x : F, (quadraticChar F (x ^ 2 + δ) + 1)) = (Fintype.card F : ℤ) - 1 := by
      have heq : (∑ x : F, (quadraticChar F (x ^ 2 + δ) + 1))
          = (((∑ x : F, (univ.filter (fun y => y ^ 2 = x ^ 2 + δ)).card) : ℕ) : ℤ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl (fun x _ => hcard x)
      rw [heq, ← hfub, hbij, hcount, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
    have hone : ∑ _x : F, (1 : ℤ) = (Fintype.card F : ℤ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hsplit : (∑ x : F, (quadraticChar F (x ^ 2 + δ) + 1))
        = (∑ x : F, quadraticChar F (x ^ 2 + δ)) + (Fintype.card F : ℤ) := by
      rw [Finset.sum_add_distrib, hone]
    rw [hsplit] at hsum1
    linarith

end Helpers

theorem char_sum_quadratic {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (β γ : F) :
    ∑ x : F, quadraticChar F (x^2 + β*x + γ) =
      if β^2 - 4*γ = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 from by norm_num]; exact mul_ne_zero h2 h2
  have key : ∑ x : F, quadraticChar F (x ^ 2 + β * x + γ)
      = ∑ x : F, quadraticChar F (x ^ 2 + (γ - β ^ 2 / 4)) := by
    apply Fintype.sum_equiv (Equiv.addRight (β / 2))
    intro x
    simp only [Equiv.coe_addRight]
    congr 1
    field_simp
    ring
  have hiff : (β ^ 2 - 4 * γ = 0) ↔ (γ - β ^ 2 / 4 = 0) := by
    rw [sub_eq_zero, sub_eq_zero, eq_div_iff h4]
    constructor <;> intro h <;> linear_combination -h
  rw [key, char_sum_sq_add hF (γ - β ^ 2 / 4)]
  by_cases h : β ^ 2 - 4 * γ = 0
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]

/-! ## Abstract linear-algebra lemmas (copied from AbsLin). -/

theorem orthogonal_odd_det_one_sub {m : ℕ} (hm : Odd m)
    (O : Matrix (Fin m) (Fin m) ℚ)
    (horth : Oᵀ * O = 1) (hdet : O.det = 1) :
    (1 - O).det = 0 := by
  have hOOt : O * Oᵀ = 1 := mul_eq_one_comm.2 horth
  have h1 : (O - 1).det = (1 - O).det := by
    have step : O - 1 = O * (1 - Oᵀ) := by
      rw [Matrix.mul_sub, Matrix.mul_one, hOOt]
    rw [step, Matrix.det_mul, hdet, one_mul]
    have : (1 - Oᵀ) = (1 - O)ᵀ := by
      rw [Matrix.transpose_sub, Matrix.transpose_one]
    rw [this, Matrix.det_transpose]
  have h2 : (O - 1).det = - (1 - O).det := by
    have : O - 1 = -(1 - O) := (neg_sub 1 O).symm
    rw [this, Matrix.det_neg, Fintype.card_fin, hm.neg_one_pow, neg_one_mul]
  linarith [h1, h2]

theorem abstract_singular {m : ℕ} (hm : Odd m)
    (S Z : Matrix (Fin m) (Fin m) ℚ)
    (hnorm : S * Sᵀ = Sᵀ * S) (hS : IsUnit S.det)
    (hZsym : Zᵀ = Z) (hZ2 : Z * Z = 1) (hZdet : Z.det = 1) :
    (S - Sᵀ * Z).det = 0 := by
  set O : Matrix (Fin m) (Fin m) ℚ := S⁻¹ * Sᵀ * Z with hO
  have hSO : S * O = Sᵀ * Z := by
    rw [hO, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv S hS, Matrix.one_mul]
  have horth : Oᵀ * O = 1 := by
    have hSinv : IsUnit (Sᵀ).det := by rwa [Matrix.det_transpose]
    have hOt : Oᵀ = Z * S * (Sᵀ)⁻¹ := by
      rw [hO]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hZsym]
      rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
      rw [Matrix.mul_assoc]
    rw [hOt, hO]
    have hcomm : (Sᵀ)⁻¹ * S⁻¹ = S⁻¹ * (Sᵀ)⁻¹ := by
      have e1 : (S * Sᵀ)⁻¹ = (Sᵀ * S)⁻¹ := by rw [hnorm]
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev] at e1
      exact e1
    calc Z * S * (Sᵀ)⁻¹ * (S⁻¹ * Sᵀ * Z)
        = Z * S * ((Sᵀ)⁻¹ * S⁻¹) * Sᵀ * Z := by
          simp only [Matrix.mul_assoc]
      _ = Z * S * (S⁻¹ * (Sᵀ)⁻¹) * Sᵀ * Z := by rw [hcomm]
      _ = Z * (S * S⁻¹) * ((Sᵀ)⁻¹ * Sᵀ) * Z := by
          simp only [Matrix.mul_assoc]
      _ = Z * 1 * 1 * Z := by
          rw [Matrix.mul_nonsing_inv S hS, Matrix.nonsing_inv_mul Sᵀ hSinv]
      _ = Z * Z := by rw [Matrix.mul_one, Matrix.mul_one]
      _ = 1 := hZ2
  have hOdet : O.det = 1 := by
    rw [hO, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hZdet, mul_one]
    have : (S⁻¹).det * S.det = 1 := by
      rw [← Matrix.det_mul, Matrix.nonsing_inv_mul S hS, Matrix.det_one]
    rw [this]
  have hkey : (1 - O).det = 0 := orthogonal_odd_det_one_sub hm O horth hOdet
  have hfact : S - Sᵀ * Z = S * (1 - O) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hSO]
  rw [hfact, Matrix.det_mul, hkey, mul_zero]


/-! ## p ≡ 3 mod 4 direction.  Foundation: QR/NQR sum-split and character identities. -/

/-! ## p ≡ 1 mod 4 direction (reduced matrix mod p is nonsingular), copied from Pone. -/

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


namespace Pthree

variable {p : ℕ} [Fact p.Prime]

local notation "χ" => quadraticChar (ZMod p)

/-- ringChar of `ZMod p` is `p`. -/
lemma ringChar_zmod : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p

/-- `Fintype.card (ZMod p) = p`. -/
lemma card_zmod : Fintype.card (ZMod p) = p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  exact ZMod.card p

section Char3

variable (hp3 : p % 4 = 3)

include hp3

lemma p_odd : p % 2 = 1 := by omega

lemma p_ne_two : p ≠ 2 := by intro h; rw [h] at hp3; norm_num at hp3

lemma ringChar_ne_two : ringChar (ZMod p) ≠ 2 := by
  rw [ringChar_zmod]
  intro h; exact p_ne_two hp3 h

/-- For `p ≡ 3 mod 4`, `χ(-1) = -1`. -/
lemma chi_neg_one : χ (-1 : ZMod p) = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare]
  rw [FiniteField.isSquare_neg_one_iff, card_zmod]
  omega

/-- The dimension. -/
def m : ℕ := p / 2

lemma p_eq : p = 2 * (m (p := p)) + 1 := by
  have := p_odd hp3
  unfold m; omega

lemma m_pos : 0 < m (p := p) := by
  have := (Fact.out : p.Prime).two_le
  unfold m; omega

lemma m_lt_p : m (p := p) < p := by have := p_eq hp3; omega

/-- The squares enumeration `ρ i = (i+1)²`. -/
def ρ (i : Fin (m (p := p))) : ZMod p := ((i : ℕ) + 1 : ZMod p) ^ 2

/-- The base `i+1` is nonzero in `ZMod p`. -/
lemma base_ne (i : Fin (m (p := p))) : ((i : ℕ) + 1 : ZMod p) ≠ 0 := by
  have hlt : (i : ℕ) + 1 < p := by
    have := i.2; have := m_lt_p hp3; omega
  rw [show ((i : ℕ) + 1 : ZMod p) = (((i : ℕ) + 1 : ℕ) : ZMod p) by push_cast; ring]
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have : p ≤ (i : ℕ) + 1 := Nat.le_of_dvd (by omega) hdvd
  omega

lemma rho_ne (i : Fin (m (p := p))) : ρ i ≠ 0 := by
  unfold ρ; exact pow_ne_zero 2 (base_ne hp3 i)

lemma chi_rho (i : Fin (m (p := p))) : χ (ρ i) = 1 := by
  unfold ρ; exact quadraticChar_sq_one' (base_ne hp3 i)

/-- `ρ` is injective. -/
lemma rho_inj : Function.Injective (ρ (p := p)) := by
  intro i j hij
  unfold ρ at hij
  have hfac : (((i : ℕ) + 1 : ZMod p) - ((j : ℕ) + 1 : ZMod p))
      * (((i : ℕ) + 1 : ZMod p) + ((j : ℕ) + 1 : ZMod p)) = 0 := by
    linear_combination hij
  rcases mul_eq_zero.mp hfac with h | h
  · -- a = b, so i+1 = j+1 as naturals
    have heq : ((i : ℕ) + 1 : ZMod p) = ((j : ℕ) + 1 : ZMod p) := by linear_combination h
    rw [show ((i : ℕ) + 1 : ZMod p) = (((i : ℕ) + 1 : ℕ) : ZMod p) by push_cast; ring,
        show ((j : ℕ) + 1 : ZMod p) = (((j : ℕ) + 1 : ℕ) : ZMod p) by push_cast; ring,
        ZMod.natCast_eq_natCast_iff] at heq
    have hi := i.2; have hj := j.2; have hml := m_lt_p hp3
    have : (i : ℕ) + 1 = (j : ℕ) + 1 := (Nat.ModEq.eq_of_lt_of_lt heq (by omega) (by omega))
    exact Fin.ext (by omega)
  · -- a + b = 0, impossible: 2 ≤ (i+1)+(j+1) ≤ 2m < p
    exfalso
    have habs : (((i : ℕ) + 1 + ((j : ℕ) + 1) : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at habs
    have hi := i.2; have hj := j.2; have hp := p_eq hp3
    have hle : (i : ℕ) + 1 + ((j : ℕ) + 1) ≤ 2 * m (p := p) := by omega
    have := Nat.le_of_dvd (by omega) habs
    omega

/-- `ρ i ≠ -(ρ j)` (a square is never the negative of a square when `-1` is a non-residue). -/
lemma rho_ne_neg_rho (i j : Fin (m (p := p))) : ρ i ≠ -(ρ j) := by
  intro h
  have h1 : χ (ρ i) = 1 := chi_rho hp3 i
  have h2 : χ (-(ρ j)) = -1 := by
    rw [show (-(ρ j)) = (-1) * ρ j by ring, map_mul, chi_neg_one hp3, chi_rho hp3 j]; ring
  rw [h] at h1
  rw [h1] at h2
  norm_num at h2

/-- The combined enumeration of all nonzero residues: squares and their negatives. -/
def φ : Fin (m (p := p)) ⊕ Fin (m (p := p)) → ZMod p :=
  Sum.elim (ρ (p := p)) (fun i => -(ρ (p := p) i))

lemma phi_inj : Function.Injective (φ (p := p)) := by
  intro x y hxy
  cases x with
  | inl a => cases y with
    | inl b =>
        simp only [φ, Sum.elim_inl] at hxy
        exact congrArg Sum.inl (rho_inj hp3 hxy)
    | inr b =>
        simp only [φ, Sum.elim_inl, Sum.elim_inr] at hxy
        exact absurd hxy (rho_ne_neg_rho hp3 a b)
  | inr a => cases y with
    | inl b =>
        simp only [φ, Sum.elim_inl, Sum.elim_inr] at hxy
        exact absurd hxy.symm (rho_ne_neg_rho hp3 b a)
    | inr b =>
        simp only [φ, Sum.elim_inr] at hxy
        exact congrArg Sum.inr (rho_inj hp3 (neg_inj.mp hxy))

lemma phi_ne_zero (x : Fin (m (p := p)) ⊕ Fin (m (p := p))) : φ x ≠ 0 := by
  cases x with
  | inl i => simpa only [φ, Sum.elim_inl] using rho_ne hp3 i
  | inr i => simpa only [φ, Sum.elim_inr, neg_ne_zero] using rho_ne hp3 i

lemma image_phi : (univ.image (φ (p := p))) = univ.erase 0 := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨x, hx⟩ := hy
    rw [Finset.mem_erase]
    exact ⟨hx ▸ phi_ne_zero hp3 x, Finset.mem_univ _⟩
  · rw [Finset.card_image_of_injective _ (phi_inj hp3)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0)]
    simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, card_zmod]
    have := p_eq hp3
    omega

/-- The QR/NQR sum-split: summing a function over squares and over negatives-of-squares
gives the sum over all nonzero residues. -/
lemma sum_split (g : ZMod p → ℤ) :
    (∑ i, g (ρ (p := p) i)) + (∑ i, g (-(ρ (p := p) i))) = (∑ u : ZMod p, g u) - g 0 := by
  have h1 : (∑ i, g (ρ (p := p) i)) + (∑ i, g (-(ρ (p := p) i)))
      = ∑ x : Fin (m (p := p)) ⊕ Fin (m (p := p)), g (φ x) := by
    rw [Fintype.sum_sum_type]
    rfl
  rw [h1]
  rw [← Finset.sum_image (g := φ (p := p)) (f := g) (fun a _ b _ hab => phi_inj hp3 hab)]
  rw [image_phi hp3]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0)]

/-- Full character sum over a monic quadratic, specialised to `ZMod p`. -/
lemma full_char_sum (β γ : ZMod p) :
    (∑ u : ZMod p, χ (u ^ 2 + β * u + γ)) = if β ^ 2 - 4 * γ = 0 then (p : ℤ) - 1 else -1 := by
  rw [char_sum_quadratic (ringChar_ne_two hp3) β γ, card_zmod]

/-- The "difference" matrix `N i j = χ(ρ i - ρ j)`. -/
def N (p : ℕ) [Fact p.Prime] : Matrix (Fin (m (p := p))) (Fin (m (p := p))) ℤ :=
  fun i j => quadraticChar (ZMod p) (ρ i - ρ j)

/-- The "sum" matrix `P i j = χ(ρ i + ρ j)`. -/
def P (p : ℕ) [Fact p.Prime] : Matrix (Fin (m (p := p))) (Fin (m (p := p))) ℤ :=
  fun i j => quadraticChar (ZMod p) (ρ i + ρ j)

/-- `(ρ i - ρ j)² = 0 ↔ i = j`. -/
lemma rho_sub_sq_zero_iff (i j : Fin (m (p := p))) : (ρ i - ρ j) ^ 2 = 0 ↔ i = j := by
  rw [pow_eq_zero_iff (by norm_num), sub_eq_zero]
  constructor
  · intro h; exact rho_inj hp3 h
  · intro h; rw [h]

/-- The key identity `N² - P² = 2E - pI` (entrywise). -/
lemma N2_sub_P2 (i j : Fin (m (p := p))) :
    (N p * N p - P p * P p) i j = if i = j then (2 - (p : ℤ)) else 2 := by
  -- abbreviation
  set f : ZMod p → ℤ := fun u => χ (ρ i - u) * χ (u - ρ j) with hf
  -- N*N at (i,j)
  have hNN : (N p * N p) i j = ∑ k, f (ρ k) := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp only [N, hf]
  -- P*P at (i,j)
  have hPterm : ∀ k, P p i k * P p k j = -(f (-(ρ k))) := by
    intro k
    simp only [P, hf]
    rw [show ρ i - -(ρ k) = ρ i + ρ k by ring,
        show -(ρ k) - ρ j = (-1) * (ρ k + ρ j) by ring, map_mul, chi_neg_one hp3]
    ring
  have hPP : (P p * P p) i j = - ∑ k, f (-(ρ k)) := by
    rw [Matrix.mul_apply, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => hPterm k)
  -- combine via sum-split
  have hcomb : (N p * N p - P p * P p) i j = (∑ u : ZMod p, f u) - f 0 := by
    rw [Matrix.sub_apply, hNN, hPP, sub_neg_eq_add, sum_split hp3 f]
  rw [hcomb]
  -- evaluate ∑ u, f u
  have hfu : ∀ u : ZMod p, f u = - χ (u ^ 2 + (-(ρ i + ρ j)) * u + ρ i * ρ j) := by
    intro u
    simp only [hf]
    rw [← map_mul,
        show (ρ i - u) * (u - ρ j) = (-1) * (u ^ 2 + (-(ρ i + ρ j)) * u + ρ i * ρ j) by ring,
        map_mul, chi_neg_one hp3]
    ring
  have hsum : (∑ u : ZMod p, f u) = if i = j then (1 - (p : ℤ)) else 1 := by
    rw [Finset.sum_congr rfl (fun u _ => hfu u), Finset.sum_neg_distrib, full_char_sum hp3]
    have hdisc : (-(ρ i + ρ j)) ^ 2 - 4 * (ρ i * ρ j) = (ρ i - ρ j) ^ 2 := by ring
    rw [hdisc]
    by_cases hij : i = j
    · rw [if_pos ((rho_sub_sq_zero_iff hp3 i j).mpr hij), if_pos hij]; ring
    · rw [if_neg (fun hc => hij ((rho_sub_sq_zero_iff hp3 i j).mp hc)), if_neg hij]; ring
  -- evaluate f 0
  have hf0 : f 0 = -1 := by
    simp only [hf]
    rw [show (ρ i - 0) = ρ i by ring, show (0 - ρ j) = (-1) * ρ j by ring, map_mul,
        chi_neg_one hp3, chi_rho hp3 i, chi_rho hp3 j]
    ring
  rw [hsum, hf0]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij]; ring
  · rw [if_neg hij, if_neg hij]; ring

/-- `ρ i + ρ j ≠ 0`. -/
lemma rho_add_ne (i j : Fin (m (p := p))) : ρ i + ρ j ≠ 0 := by
  intro h
  exact rho_ne_neg_rho hp3 i j (by linear_combination h)

/-- The commutation identity `N P = P N` (entrywise difference is zero). -/
lemma NP_sub_PN (i j : Fin (m (p := p))) : (N p * P p - P p * N p) i j = 0 := by
  set h : ZMod p → ℤ := fun u => χ (ρ i - u) * χ (u + ρ j) with hh
  have hNP : (N p * P p) i j = ∑ k, h (ρ k) := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp only [N, P, hh]
  have hPNterm : ∀ k, P p i k * N p k j = -(h (-(ρ k))) := by
    intro k
    simp only [P, N, hh]
    rw [show ρ i - -(ρ k) = ρ i + ρ k by ring,
        show -(ρ k) + ρ j = (-1) * (ρ k - ρ j) by ring, map_mul, chi_neg_one hp3]
    ring
  have hPN : (P p * N p) i j = - ∑ k, h (-(ρ k)) := by
    rw [Matrix.mul_apply, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => hPNterm k)
  have hcomb : (N p * P p - P p * N p) i j = (∑ u : ZMod p, h u) - h 0 := by
    rw [Matrix.sub_apply, hNP, hPN, sub_neg_eq_add, sum_split hp3 h]
  rw [hcomb]
  have hhu : ∀ u : ZMod p, h u = - χ (u ^ 2 + (ρ j - ρ i) * u + (-(ρ i * ρ j))) := by
    intro u
    simp only [hh]
    rw [← map_mul,
        show (ρ i - u) * (u + ρ j) = (-1) * (u ^ 2 + (ρ j - ρ i) * u + (-(ρ i * ρ j))) by ring,
        map_mul, chi_neg_one hp3]
    ring
  have hsum : (∑ u : ZMod p, h u) = 1 := by
    rw [Finset.sum_congr rfl (fun u _ => hhu u), Finset.sum_neg_distrib, full_char_sum hp3]
    have hdisc : (ρ j - ρ i) ^ 2 - 4 * (-(ρ i * ρ j)) = (ρ i + ρ j) ^ 2 := by ring
    rw [hdisc, if_neg (pow_ne_zero 2 (rho_add_ne hp3 i j))]
    ring
  have hh0 : h 0 = 1 := by
    simp only [hh]
    rw [show (ρ i - 0) = ρ i by ring, show (0 + ρ j) = ρ j by ring, chi_rho hp3 i, chi_rho hp3 j]
    norm_num
  rw [hsum, hh0]; ring

/-- `N P = P N`. -/
lemma NP_comm : N p * P p = P p * N p := by
  ext i j
  have := NP_sub_PN hp3 i j
  rw [Matrix.sub_apply, sub_eq_zero] at this
  exact this

/-- `N` is skew-symmetric. -/
lemma N_transpose : (N p)ᵀ = -(N p) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, N]
  rw [show ρ j - ρ i = (-1) * (ρ i - ρ j) by ring, map_mul, chi_neg_one hp3]; ring

/-- `P` is symmetric. -/
lemma P_transpose : (P p)ᵀ = P p := by
  ext i j
  simp only [Matrix.transpose_apply, P]
  rw [show ρ j + ρ i = ρ i + ρ j by ring]

/-- The all-ones matrix over `ℚ`. -/
def Eones (p : ℕ) : Matrix (Fin (m (p := p))) (Fin (m (p := p))) ℚ := fun _ _ => 1

/-- The integer matrix `S = N + P`. -/
def Sint (p : ℕ) [Fact p.Prime] : Matrix (Fin (m (p := p))) (Fin (m (p := p))) ℤ := N p + P p

/-- The rational matrix `S = N + P`. -/
def Sq (p : ℕ) [Fact p.Prime] : Matrix (Fin (m (p := p))) (Fin (m (p := p))) ℚ :=
  (Sint p).map (Int.castRingHom ℚ)

/-- Transpose of `Sint`. -/
lemma Sint_transpose : (Sint p)ᵀ = P p - N p := by
  rw [Sint, Matrix.transpose_add, N_transpose hp3, P_transpose hp3]; abel

/-- `Sint * (Sint)ᵀ = -(N² - P²)`. -/
lemma Sint_mul_transpose : Sint p * (Sint p)ᵀ = -(N p * N p - P p * P p) := by
  rw [Sint_transpose hp3, Sint, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [NP_comm hp3]
  abel

/-- `(Sint)ᵀ * Sint = -(N² - P²)`. -/
lemma transpose_mul_Sint : (Sint p)ᵀ * Sint p = -(N p * N p - P p * P p) := by
  rw [Sint_transpose hp3, Sint, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
  rw [NP_comm hp3]
  abel

/-- `Sq p * (Sq p)ᵀ = (Sint p * (Sint p)ᵀ).map (Int.cast)`. -/
lemma Sq_mul_transpose_map :
    Sq p * (Sq p)ᵀ = (Sint p * (Sint p)ᵀ).map (Int.castRingHom ℚ) := by
  rw [Sq, ← Matrix.transpose_map, ← Matrix.map_mul]

/-- `Sq` is normal. -/
lemma Sq_normal : Sq p * (Sq p)ᵀ = (Sq p)ᵀ * Sq p := by
  have h2 : (Sq p)ᵀ * Sq p = ((Sint p)ᵀ * Sint p).map (Int.castRingHom ℚ) := by
    rw [Sq, ← Matrix.transpose_map, ← Matrix.map_mul]
  rw [Sq_mul_transpose_map hp3, h2, Sint_mul_transpose hp3, transpose_mul_Sint hp3]

/-- `Sq * Sqᵀ = p·I - 2·E`. -/
lemma Sq_mul_transpose :
    Sq p * (Sq p)ᵀ = (p : ℚ) • (1 : Matrix (Fin (m (p := p))) (Fin (m (p := p))) ℚ)
      - (2 : ℚ) • Eones p := by
  rw [Sq_mul_transpose_map hp3, Sint_mul_transpose hp3]
  ext i j
  rw [Matrix.map_apply, Matrix.neg_apply, N2_sub_P2 hp3 i j]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Eones, smul_eq_mul,
    mul_one, eq_intCast]
  by_cases hij : i = j
  · simp only [hij, if_true]; push_cast; ring
  · simp only [hij, if_false]; push_cast; ring

/-- `Eones` applied to a vector gives the constant sum. -/
lemma Eones_mulVec (v : Fin (m (p := p)) → ℚ) (i : Fin (m (p := p))) :
    (Eones p *ᵥ v) i = ∑ k, v k := by
  simp only [Matrix.mulVec, Eones, dotProduct, one_mul]

/-- The kernel of `Sq * Sqᵀ` is trivial, hence its determinant is nonzero. -/
lemma SSt_det_ne : (Sq p * (Sq p)ᵀ).det ≠ 0 := by
  intro hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
  obtain ⟨v, hv, hmul⟩ := hdet
  apply hv
  have hp0 : (p : ℚ) ≠ 0 := by
    have := (Fact.out : p.Prime).pos; positivity
  -- key: p * v i = 2 * (∑ v) for each i
  have key : ∀ i, (p : ℚ) * v i = 2 * (∑ k, v k) := by
    intro i
    have hi := congrFun hmul i
    rw [Sq_mul_transpose hp3, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec] at hi
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Eones_mulVec hp3, smul_eq_mul,
        smul_eq_mul, Pi.zero_apply] at hi
    linarith [hi]
  set T : ℚ := ∑ k, v k with hT
  -- sum the key relations: p * T = 2 * m * T
  have hpT : (p : ℚ) * T = 2 * (m (p := p) : ℚ) * T := by
    have : (∑ i, (p : ℚ) * v i) = ∑ _i : Fin (m (p := p)), 2 * T :=
      Finset.sum_congr rfl (fun i _ => key i)
    rw [← Finset.mul_sum, ← hT, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at this
    rw [this]; ring
  -- p = 2m+1, so T = 0
  have hpm : (p : ℚ) = 2 * (m (p := p) : ℚ) + 1 := by
    have := p_eq hp3; exact_mod_cast this
  have hT0 : T = 0 := by
    rw [hpm] at hpT; linear_combination hpT
  -- hence v = 0
  funext i
  have := key i
  rw [hT0, mul_zero] at this
  rw [Pi.zero_apply]
  exact (mul_eq_zero.mp this).resolve_left hp0

/-- `Sq` has unit determinant. -/
lemma Sq_isUnit_det : IsUnit (Sq p).det := by
  have hne : (Sq p).det ≠ 0 := by
    intro h
    apply SSt_det_ne hp3
    rw [Matrix.det_mul, Matrix.det_transpose, h, mul_zero]
  exact Ne.isUnit hne

/-- `m` is odd when `p ≡ 3 mod 4`. -/
lemma m_odd : Odd (m (p := p)) := by
  rw [Nat.odd_iff]
  unfold m
  omega

/-- The constant `C̄ = (m! : ZMod p)`. -/
def Cbar (p : ℕ) [Fact p.Prime] : ZMod p := (Nat.factorial (m (p := p)) : ZMod p)

lemma Cbar_ne : Cbar p ≠ 0 := by
  rw [Cbar, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := (Fact.out : p.Prime).dvd_factorial.mp hdvd
  have := m_lt_p hp3
  omega

/-- The column values `w j = C̄ · (j+1)`. -/
def wcol (p : ℕ) [Fact p.Prime] (j : Fin (m (p := p))) : ZMod p := Cbar p * ((j : ℕ) + 1)

lemma wcol_ne (j : Fin (m (p := p))) : wcol p j ≠ 0 := by
  rw [wcol]
  exact mul_ne_zero (Cbar_ne hp3) (base_ne hp3 j)

/-- The integer matrix with entries `χ(ρ i - w j)`. -/
def MintChi (p : ℕ) [Fact p.Prime] : Matrix (Fin (m (p := p))) (Fin (m (p := p))) ℤ :=
  fun i j => quadraticChar (ZMod p) (ρ i - wcol p j)

/-- Every nonzero residue is `±(k+1)` for some `k : Fin m`. -/
lemma exists_pm_rep (t : ZMod p) (ht : t ≠ 0) :
    ∃ k : Fin (m (p := p)), t = ((k : ℕ) + 1 : ZMod p) ∨ t = -((k : ℕ) + 1 : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hp := p_eq hp3
  have hvlt : t.val < p := ZMod.val_lt t
  have htv : t = (t.val : ZMod p) := (ZMod.natCast_zmod_val t).symm
  have hv0 : 0 < t.val := by
    rcases Nat.eq_zero_or_pos t.val with h | h
    · exfalso; apply ht; rw [htv, h]; simp
    · exact h
  rcases Nat.lt_or_ge t.val (m (p := p) + 1) with hcase | hcase
  · refine ⟨⟨t.val - 1, by omega⟩, Or.inl ?_⟩
    conv_lhs => rw [htv]
    show (↑t.val : ZMod p) = (↑(t.val - 1) : ZMod p) + 1
    have h : (t.val : ℕ) = (t.val - 1) + 1 := by omega
    rw [show ((t.val - 1 : ℕ) : ZMod p) + 1 = (((t.val - 1) + 1 : ℕ) : ZMod p) by push_cast; ring,
        ← h]
  · refine ⟨⟨p - t.val - 1, by omega⟩, Or.inr ?_⟩
    conv_lhs => rw [htv]
    show (↑t.val : ZMod p) = -((↑(p - t.val - 1) : ZMod p) + 1)
    have hpv : ((p - t.val - 1) + 1 : ℕ) = p - t.val := by omega
    have h1 : (↑(p - t.val - 1) : ZMod p) + 1 = (↑(p - t.val) : ZMod p) := by
      rw [show ((p - t.val - 1 : ℕ) : ZMod p) + 1 = (((p - t.val - 1) + 1 : ℕ) : ZMod p) by
            push_cast; ring, hpv]
    rw [h1]
    have h2 : (↑(p - t.val) : ZMod p) = -(↑t.val : ZMod p) := by
      rw [Nat.cast_sub (le_of_lt hvlt), ZMod.natCast_self, zero_sub]
    rw [h2, neg_neg]

/-- Every nonzero square is `ρ k` for some `k`. -/
lemma rho_surj (s : ZMod p) (hs0 : s ≠ 0) (hsq : χ s = 1) : ∃ k, ρ k = s := by
  have hsquare : IsSquare s := (quadraticChar_one_iff_isSquare hs0).mp hsq
  obtain ⟨r, hr⟩ := hsquare
  have hr0 : r ≠ 0 := by
    intro h; apply hs0; rw [hr, h, mul_zero]
  obtain ⟨k, hk⟩ := exists_pm_rep hp3 r hr0
  refine ⟨k, ?_⟩
  unfold ρ
  rcases hk with hk | hk
  · rw [hr, hk]; ring
  · rw [hr, hk]; ring

/-- The quadratic-residue representative of `±wcol`. -/
noncomputable def qrep (p : ℕ) [Fact p.Prime] (j : Fin (m (p := p))) : ZMod p :=
  if quadraticChar (ZMod p) (wcol p j) = 1 then wcol p j else -(wcol p j)

lemma qrep_ne (j : Fin (m (p := p))) : qrep p j ≠ 0 := by
  unfold qrep
  by_cases h : quadraticChar (ZMod p) (wcol p j) = 1
  · rw [if_pos h]; exact wcol_ne hp3 j
  · rw [if_neg h, neg_ne_zero]; exact wcol_ne hp3 j

lemma qrep_chi (j : Fin (m (p := p))) : χ (qrep p j) = 1 := by
  unfold qrep
  by_cases h : χ (wcol p j) = 1
  · rw [if_pos h]; exact h
  · have hneg : χ (wcol p j) = -1 := (quadraticChar_dichotomy (wcol_ne hp3 j)).resolve_left h
    rw [if_neg h, show -(wcol p j) = (-1) * (wcol p j) by ring, map_mul, chi_neg_one hp3, hneg]
    ring

lemma qrep_sq (j : Fin (m (p := p))) : (qrep p j) ^ 2 = (wcol p j) ^ 2 := by
  unfold qrep
  by_cases h : χ (wcol p j) = 1
  · rw [if_pos h]
  · rw [if_neg h]; ring

lemma wcol_sq (j : Fin (m (p := p))) : (wcol p j) ^ 2 = (Cbar p) ^ 2 * ρ j := by
  simp only [wcol, ρ]; ring

lemma qrep_inj : Function.Injective (qrep p) := by
  intro j j' h
  have h2 : (qrep p j) ^ 2 = (qrep p j') ^ 2 := by rw [h]
  rw [qrep_sq hp3, qrep_sq hp3, wcol_sq hp3, wcol_sq hp3] at h2
  have h3 : ρ j = ρ j' := mul_left_cancel₀ (pow_ne_zero 2 (Cbar_ne hp3)) h2
  exact rho_inj hp3 h3

/-- The column-permutation map: `qrep p j = ρ (sigma p hp3 j)`. -/
noncomputable def sigma (p : ℕ) [Fact p.Prime] (hp3 : p % 4 = 3) (j : Fin (m (p := p))) :
    Fin (m (p := p)) :=
  Classical.choose (rho_surj hp3 (qrep p j) (qrep_ne hp3 j) (qrep_chi hp3 j))

lemma sigma_spec (j : Fin (m (p := p))) : ρ (sigma p hp3 j) = qrep p j :=
  Classical.choose_spec (rho_surj hp3 (qrep p j) (qrep_ne hp3 j) (qrep_chi hp3 j))

lemma sigma_inj : Function.Injective (sigma p hp3) := by
  intro j j' h
  apply qrep_inj hp3
  have e1 := sigma_spec hp3 j
  have e2 := sigma_spec hp3 j'
  rw [h] at e1
  rw [e2] at e1
  exact e1.symm

noncomputable def sigmaEquiv (p : ℕ) [Fact p.Prime] (hp3 : p % 4 = 3) :
    Equiv.Perm (Fin (m (p := p))) :=
  Equiv.ofBijective (sigma p hp3) (Finite.injective_iff_bijective.mp (sigma_inj hp3))

lemma sigmaEquiv_apply (j : Fin (m (p := p))) : sigmaEquiv p hp3 j = sigma p hp3 j := rfl

/-- The matrix entry decomposition. -/
lemma MintChi_entry (i j : Fin (m (p := p))) :
    MintChi p i j =
      if χ (wcol p j) = 1 then N p i (sigma p hp3 j) else P p i (sigma p hp3 j) := by
  simp only [MintChi]
  by_cases h : χ (wcol p j) = 1
  · rw [if_pos h]
    have hq : qrep p j = wcol p j := by unfold qrep; rw [if_pos h]
    have hs := sigma_spec hp3 j
    rw [hq] at hs
    simp only [N]
    rw [hs]
  · rw [if_neg h]
    have hq : qrep p j = -(wcol p j) := by unfold qrep; rw [if_neg h]
    have hs := sigma_spec hp3 j
    rw [hq] at hs
    simp only [P]
    rw [show ρ i + ρ (sigma p hp3 j) = ρ i - wcol p j by rw [hs]; ring]

/-- Entrywise skew-symmetry of `N`. -/
lemma N_skew (a b : Fin (m (p := p))) : N p a b = -(N p b a) := by
  have := congrFun (congrFun (N_transpose hp3) b) a
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
  exact this

/-- Entrywise symmetry of `P`. -/
lemma P_symm (a b : Fin (m (p := p))) : P p a b = P p b a := by
  have := congrFun (congrFun (P_transpose hp3) b) a
  simp only [Matrix.transpose_apply] at this
  exact this

/-- `Sq` entry in terms of `N` and `P`. -/
lemma Sq_entry (a b : Fin (m (p := p))) : Sq p a b = ((N p a b : ℚ) + (P p a b : ℚ)) := by
  simp only [Sq, Matrix.map_apply, Sint, Matrix.add_apply, eq_intCast, Int.cast_add]

theorem MintChi_det_zero : (MintChi p).det = 0 := by
  classical
  set σe := sigmaEquiv p hp3 with hσe
  set η : Fin (m (p := p)) → ℚ := fun k => (χ (wcol p (σe.symm k)) : ℚ) with hη
  set Z : Matrix (Fin (m (p := p))) (Fin (m (p := p))) ℚ := Matrix.diagonal η with hZ
  -- helper facts about σe and η
  have hσj : ∀ j, σe j = sigma p hp3 j := by
    intro j; rw [hσe]; exact sigmaEquiv_apply hp3 j
  have hση : ∀ j, η (σe j) = (χ (wcol p j) : ℚ) := by
    intro j; simp only [hη, Equiv.symm_apply_apply]
  -- Z is symmetric
  have hZsym : Zᵀ = Z := by rw [hZ, Matrix.diagonal_transpose]
  -- Z * Z = 1
  have hηsq : ∀ k, η k * η k = 1 := by
    intro k
    rcases quadraticChar_dichotomy (wcol_ne hp3 (σe.symm k)) with h | h <;>
      simp only [hη, h] <;> norm_num
  have hZ2 : Z * Z = 1 := by
    rw [hZ, Matrix.diagonal_mul_diagonal]
    rw [show (fun k => η k * η k) = (fun _ : Fin (m (p := p)) => (1 : ℚ)) from funext hηsq]
    exact Matrix.diagonal_one
  -- the product of wcol values
  have hprodw : (∏ i, wcol p i) = (Cbar p) ^ (m (p := p) + 1) := by
    have hfn : (∏ i : Fin (m (p := p)), ((i : ℕ) + 1)) = Nat.factorial (m (p := p)) := by
      rw [Fin.prod_univ_eq_prod_range (fun i => i + 1) (m (p := p))]
      exact Finset.prod_range_add_one_eq_factorial _
    have hfc : (∏ i : Fin (m (p := p)), ((i : ℕ) + 1 : ZMod p)) = Cbar p := by
      rw [Cbar, ← hfn, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i _
      push_cast
      ring
    simp only [wcol]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hfc,
      pow_succ]
  -- χ of that product is 1
  have hχ : χ (∏ i, wcol p i) = 1 := by
    rw [hprodw, map_pow]
    have hev : Even (m (p := p) + 1) := by
      rcases m_odd hp3 with ⟨t, ht⟩
      exact ⟨t + 1, by omega⟩
    rcases quadraticChar_dichotomy (Cbar_ne hp3) with h | h
    · rw [h, one_pow]
    · rw [h, hev.neg_one_pow]
  -- Z.det = 1
  have hZdet : Z.det = 1 := by
    rw [hZ, Matrix.det_diagonal]
    have hreidx : ∏ i, η i = ∏ i, (χ (wcol p i) : ℚ) := by
      rw [← Equiv.prod_comp σe.symm (fun j => (χ (wcol p j) : ℚ))]
    rw [hreidx, ← Int.cast_prod, ← map_prod (quadraticChar (ZMod p)) (fun i => wcol p i), hχ]
    norm_num
  -- abstract singularity
  have hsing : (Sq p - (Sq p)ᵀ * Z).det = 0 :=
    abstract_singular (m_odd hp3) (Sq p) Z (Sq_normal hp3) (Sq_isUnit_det hp3) hZsym hZ2 hZdet
  have hG : ((1 / 2 : ℚ) • (Sq p - (Sq p)ᵀ * Z)).det = 0 := by
    rw [Matrix.det_smul, hsing, mul_zero]
  -- the column-permutation identity
  have hMap : (MintChi p).map (Int.castRingHom ℚ)
      = ((1 / 2 : ℚ) • (Sq p - (Sq p)ᵀ * Z)).submatrix id σe := by
    ext i j
    rw [Matrix.map_apply, eq_intCast, MintChi_entry hp3 i j, ← hσj j,
      Matrix.submatrix_apply, id_eq, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
      hZ, Matrix.mul_diagonal, Matrix.transpose_apply, Sq_entry hp3 i (σe j),
      Sq_entry hp3 (σe j) i, N_skew hp3 (σe j) i, P_symm hp3 (σe j) i, hση j]
    by_cases h : χ (wcol p j) = 1
    · rw [if_pos h, h]; push_cast; ring
    · have hneg : χ (wcol p j) = -1 := (quadraticChar_dichotomy (wcol_ne hp3 j)).resolve_left h
      rw [if_neg h, hneg]; push_cast; ring
  -- conclude
  have hdet0 : ((MintChi p).map (Int.castRingHom ℚ)).det = 0 := by
    rw [hMap, Matrix.det_permute', hG, mul_zero]
  have hmapdet : (Int.castRingHom ℚ) ((MintChi p).det)
      = ((MintChi p).map (Int.castRingHom ℚ)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hfinal : (Int.castRingHom ℚ) ((MintChi p).det) = 0 := by rw [hmapdet, hdet0]
  rw [eq_intCast] at hfinal
  exact_mod_cast hfinal


end Char3

/-- For `p ≡ 1 mod 4`, `det (MintChi p) ≠ 0`, via reduction mod `p` (uses `detMbar_ne`). -/
lemma MintChi_ne_of_one (hp1 : p % 4 = 1) : (MintChi p).det ≠ 0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ringChar_zmod]; omega
  have hmap : (MintChi p).map (Int.castRingHom (ZMod p)) =
      Matrix.of (fun i j : Fin (p / 2) =>
        (((i : ℕ) + 1 : ZMod p) ^ 2 - ((Nat.factorial (p / 2)) : ZMod p) * ((j : ℕ) + 1 : ZMod p))
          ^ (p / 2)) := by
    ext i j
    rw [Matrix.map_apply, MintChi]
    simp only [Matrix.of_apply]
    rw [eq_intCast, quadraticChar_eq_pow_of_char_ne_two' hchar, card_zmod]
    congr 1
  intro hdet
  apply detMbar_ne hp1
  have h2 : ((MintChi p).map (Int.castRingHom (ZMod p))).det
      = (Int.castRingHom (ZMod p)) ((MintChi p).det) := by
    rw [← RingHom.mapMatrix_apply]
    exact (RingHom.map_det _ _).symm
  rw [← hmap, h2, hdet, map_zero]

/-- Main iff over an odd prime `p`. -/
lemma MintChi_det_iff (hodd : p % 2 = 1) : (MintChi p).det = 0 ↔ p % 4 = 3 := by
  constructor
  · intro hdet
    by_contra h3
    have h1 : p % 4 = 1 := by omega
    exact MintChi_ne_of_one h1 hdet
  · intro h3
    exact MintChi_det_zero h3

end Pthree


open Nat Int

noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else
  let p : ℕ := Nat.nth Nat.Prime (n - 1)
  let m : ℕ := (p - 1) / 2
  let C : ℤ := m.factorial.cast
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast
    let arg : ℤ := i' * i' - C * j'
    jacobiSym arg p
  M.det

theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  set p : ℕ := Nat.nth Nat.Prime (n - 1) with hp_def
  have hp_prime : Nat.Prime p := Nat.prime_nth_prime (n - 1)
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have hp_ne2 : p ≠ 2 := by
    intro hcon
    rw [hp_def, ← Nat.nth_prime_zero_eq_two] at hcon
    have := Nat.nth_injective Nat.infinite_setOf_prime hcon
    omega
  have hodd : p % 2 = 1 := hp_prime.eq_two_or_odd.resolve_left hp_ne2
  have e : (p - 1) / 2 = p / 2 := by omega
  have hAeq : A226163 n = (Pthree.MintChi p).det := by
    rw [A226163, dif_neg (by omega : ¬ n < 2)]
    simp only []
    rw [← Matrix.det_submatrix_equiv_self (finCongr e) (Pthree.MintChi p)]
    congr 1
    funext i j
    simp only [Matrix.submatrix_apply, Pthree.MintChi, Pthree.ρ, Pthree.wcol, Pthree.Cbar, Pthree.m]
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    unfold legendreSym
    congr 1
    have hi : ((finCongr e i : Fin (p / 2)) : ℕ) = (i : ℕ) := finCongr_apply_coe e i
    have hj : ((finCongr e j : Fin (p / 2)) : ℕ) = (j : ℕ) := finCongr_apply_coe e j
    rw [hi, hj]
    have e2 : (Nat.nth Nat.Prime (n - 1) - 1) / 2 = p / 2 := by rw [← hp_def]; exact e
    have hfactZ : (((Nat.nth Nat.Prime (n - 1) - 1) / 2).factorial : ℤ)
        = ((p / 2).factorial : ℤ) := by rw [e2]
    rw [hfactZ]
    push_cast
    ring
  rw [hAeq]
  exact Pthree.MintChi_det_iff hodd
