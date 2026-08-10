import Submission.dominant

open PowerSeries Finset

/-! ## Elementary power bound -/

lemma pow5ge : ∀ n : ℕ, 4 * n + 1 ≤ 5 ^ n
  | 0 => by norm_num
  | (n + 1) => by
    have ih := pow5ge n
    have h2 : 5 * (4 * n + 1) ≤ 5 * 5 ^ n := mul_le_mul_left' ih 5
    have he : 5 ^ (n + 1) = 5 * 5 ^ n := by rw [pow_succ]; ring
    omega

/-! ## Absorption identity for `Ring.choose` -/

/-- `(k+1)·C(N,k+1) = N·C(N-1,k)` (committee–chair identity for `Ring.choose`). -/
lemma absorb (N : ℤ) (k : ℕ) :
    ((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1) = N * Ring.choose (N - 1) k := by
  have hk : ((k.factorial : ℤ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hk
  have e1 : (k.factorial : ℤ) * (((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1))
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    have hpk : (∏ i ∈ range (k+1), (N - (i:ℤ)))
        = ((k+1).factorial : ℤ) * Ring.choose N (k+1) := by
      have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N (k+1)
      rw [nsmul_eq_mul] at h
      rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
      exact h
    rw [hpk]
    have : ((k + 1).factorial : ℤ) = ((k + 1 : ℕ) : ℤ) * (k.factorial : ℤ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [this]; ring
  have e2 : (k.factorial : ℤ) * (N * Ring.choose (N - 1) k)
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    have hpk : (∏ i ∈ range k, ((N - 1) - (i:ℤ))) = (k.factorial : ℤ) * Ring.choose (N-1) k := by
      have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) (N-1) k
      rw [nsmul_eq_mul] at h
      rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
      exact h
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    rw [show (∏ i ∈ range k, (N - ((i:ℤ) + 1))) = ∏ i ∈ range k, ((N - 1) - (i:ℤ)) from
      Finset.prod_congr rfl (fun i _ => by ring)]
    rw [hpk]; ring
  rw [e1, e2]

/-! ## Arithmetic (valuation) lemmas -/

/-- ARITH1: for `p ≥ 5` prime and `j ≥ 3`,
`v_p(j) + v_p((j-1)!) + v_p((j-2)!) + 3 ≤ j`. -/
lemma arith1 (p j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 3 ≤ j) :
    padicValNat p j + padicValNat p (j-1).factorial + padicValNat p (j-2).factorial + 3 ≤ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfact : j.factorial = j * (j-1).factorial := by
    conv_lhs => rw [show j = (j-1)+1 from by omega]
    rw [Nat.factorial_succ, show (j-1)+1 = j from by omega]
  have hsplit : padicValNat p j.factorial
      = padicValNat p j + padicValNat p (j-1).factorial := by
    rw [hfact, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
  have h4 : 4 ≤ p - 1 := by omega
  -- Legendre bounds
  have hL1 : (p - 1) * padicValNat p j.factorial < j :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  have hL2 : (p - 1) * padicValNat p (j-2).factorial < (j-2) :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  have b1 : 4 * padicValNat p j.factorial < j :=
    lt_of_le_of_lt (mul_le_mul_right' h4 _) hL1
  have b2 : 4 * padicValNat p (j-2).factorial < (j-2) :=
    lt_of_le_of_lt (mul_le_mul_right' h4 _) hL2
  omega

/-- ARITH2: for `p ≥ 5` prime, `j ≥ 3` and `p^E ≤ j - 1`,
`v_p(j) + 2E + 3 ≤ j`. -/
lemma arith2 (p E j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 3 ≤ j)
    (hb : p ^ E ≤ j - 1) :
    padicValNat p j + 2 * E + 3 ≤ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Bound on E
  have h5E : (5:ℕ) ^ E ≤ p ^ E := Nat.pow_le_pow_left hp5 E
  have hEb : 4 * E + 1 ≤ j - 1 := le_trans (pow5ge E) (le_trans h5E hb)
  -- Bound on v_p(j)
  have hvjdvd : p ^ (padicValNat p j) ∣ j := pow_padicValNat_dvd
  have hvjle : p ^ (padicValNat p j) ≤ j := Nat.le_of_dvd (by omega) hvjdvd
  have h5vj : (5:ℕ) ^ (padicValNat p j) ≤ p ^ (padicValNat p j) := Nat.pow_le_pow_left hp5 _
  have hvjb : 4 * padicValNat p j + 1 ≤ j := le_trans (pow5ge _) (le_trans h5vj hvjle)
  omega

/-! ## Divisibility combination lemmas -/

lemma combine_dom (p : ℕ) (E vj F j : ℕ) (C L : ℤ)
    (h1 : (p:ℤ)^E ∣ (p:ℤ)^vj * C)
    (h2 : (p:ℤ)^(2*E) ∣ (p:ℤ)^F * L)
    (harith : vj + F + 3 ≤ j) :
    (p:ℤ)^(3*E+3) ∣ C * (p:ℤ)^j * L := by
  have hmul := mul_dvd_mul h1 h2
  have hL : (p:ℤ)^E * (p:ℤ)^(2*E) = (p:ℤ)^(3*E) := by
    rw [← pow_add, show E + 2*E = 3*E from by ring]
  have hR : ((p:ℤ)^vj * C) * ((p:ℤ)^F * L) = (p:ℤ)^(vj+F) * (C*L) := by
    rw [pow_add]; ring
  rw [hL, hR] at hmul
  have hmul2 := mul_dvd_mul_left ((p:ℤ)^(j-vj-F)) hmul
  have e1 : (p:ℤ)^(j-vj-F) * (p:ℤ)^(3*E) = (p:ℤ)^((j-vj-F)+3*E) := by rw [← pow_add]
  have e2 : (p:ℤ)^(j-vj-F) * ((p:ℤ)^(vj+F) * (C*L)) = (p:ℤ)^j * (C*L) := by
    rw [← mul_assoc, ← pow_add, show (j-vj-F)+(vj+F) = j from by omega]
  rw [e1, e2] at hmul2
  have hfin : (p:ℤ)^(3*E+3) ∣ (p:ℤ)^((j-vj-F)+3*E) := pow_dvd_pow _ (by omega)
  have hfinal := dvd_trans hfin hmul2
  rwa [show (p:ℤ)^j * (C*L) = C * (p:ℤ)^j * L from by ring] at hfinal

lemma combine_small (p : ℕ) (E vj j : ℕ) (C L : ℤ)
    (h1 : (p:ℤ)^E ∣ (p:ℤ)^vj * C)
    (harith : vj + 2*E + 3 ≤ j) :
    (p:ℤ)^(3*E+3) ∣ C * (p:ℤ)^j * L := by
  have hm : (p:ℤ)^E ∣ ((p:ℤ)^vj * C) * L := h1.mul_right L
  have hm2 := mul_dvd_mul_left ((p:ℤ)^(j-vj)) hm
  have e1 : (p:ℤ)^(j-vj) * (p:ℤ)^E = (p:ℤ)^((j-vj)+E) := by rw [← pow_add]
  have e2 : (p:ℤ)^(j-vj) * (((p:ℤ)^vj * C) * L) = (p:ℤ)^j * (C*L) := by
    rw [show ((p:ℤ)^vj * C) * L = (p:ℤ)^vj * (C*L) from by ring, ← mul_assoc, ← pow_add,
      show (j-vj)+vj = j from by omega]
  rw [e1, e2] at hm2
  have hfin : (p:ℤ)^(3*E+3) ∣ (p:ℤ)^((j-vj)+E) := pow_dvd_pow _ (by omega)
  have hfinal := dvd_trans hfin hm2
  rwa [show (p:ℤ)^j * (C*L) = C * (p:ℤ)^j * L from by ring] at hfinal

/-! ## Main theorem -/

theorem termDvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ) (M : ℕ) (hM : 0 < M) (j : ℕ)
    (hj : 3 ≤ j) :
    (p : ℤ) ^ (3 * padicValNat p M + 3)
      ∣ Ring.choose (A * (M:ℤ)) j * (p : ℤ) ^ j * ℓ (ψ p j) (A * (M:ℤ)) M := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- p^E divides A*M
  have hpEM : p ^ (padicValNat p M) ∣ M := pow_padicValNat_dvd
  have hpEAM : (p:ℤ) ^ (padicValNat p M) ∣ A * (M:ℤ) := by
    have hMint : (p:ℤ) ^ (padicValNat p M) ∣ (M:ℤ) := by exact_mod_cast hpEM
    exact hMint.mul_left A
  -- (i): p^E ∣ j * C
  have hi : (p:ℤ) ^ (padicValNat p M) ∣ ((j:ℕ):ℤ) * Ring.choose (A * (M:ℤ)) j := by
    have habs := absorb (A * (M:ℤ)) (j-1)
    rw [show (j-1)+1 = j from by omega] at habs
    rw [habs]
    exact hpEAM.mul_right _
  -- corollary: p^E ∣ p^(v_p j) * C
  have hcor : (p:ℤ) ^ (padicValNat p M)
      ∣ (p:ℤ) ^ (padicValNat p j) * Ring.choose (A * (M:ℤ)) j := by
    obtain ⟨jc, hjc⟩ := (pow_padicValNat_dvd : p ^ (padicValNat p j) ∣ j)
    have hpjc : ¬ (p ∣ jc) := by
      rintro ⟨t, ht⟩
      refine pow_succ_padicValNat_not_dvd (p := p) (n := j) (show j ≠ 0 from by omega) ⟨t, ?_⟩
      rw [pow_succ, mul_assoc, ← ht]
      exact hjc
    have hjcZ : ((j:ℕ):ℤ) = (p:ℤ) ^ (padicValNat p j) * (jc:ℤ) := by
      exact_mod_cast hjc
    rw [hjcZ] at hi
    have hi2 : (p:ℤ) ^ (padicValNat p M)
        ∣ ((p:ℤ) ^ (padicValNat p j) * Ring.choose (A * (M:ℤ)) j) * (jc:ℤ) := by
      have hre : (p:ℤ) ^ (padicValNat p j) * (jc:ℤ) * Ring.choose (A * (M:ℤ)) j
          = ((p:ℤ) ^ (padicValNat p j) * Ring.choose (A * (M:ℤ)) j) * (jc:ℤ) := by ring
      rwa [hre] at hi
    have hcop : IsCoprime ((p:ℤ) ^ (padicValNat p M)) ((jc:ℤ)) :=
      (((hp.coprime_iff_not_dvd).mpr hpjc).isCoprime).pow_left
    exact hcop.dvd_of_dvd_mul_right hi2
  -- Regime split
  by_cases hcase : j - 1 < p ^ (padicValNat p M)
  · -- Dominant
    have hprop := prop5dom p hp hp5 A M hM j hj hcase
    refine combine_dom p (padicValNat p M) (padicValNat p j)
      (padicValNat p (j-1).factorial + padicValNat p (j-2).factorial) j
      (Ring.choose (A * (M:ℤ)) j) (ℓ (ψ p j) (A * (M:ℤ)) M) hcor hprop ?_
    have := arith1 p j hp hp5 hj
    omega
  · -- Small
    have hb : p ^ (padicValNat p M) ≤ j - 1 := Nat.le_of_not_lt hcase
    refine combine_small p (padicValNat p M) (padicValNat p j) j
      (Ring.choose (A * (M:ℤ)) j) (ℓ (ψ p j) (A * (M:ℤ)) M) hcor ?_
    have := arith2 p (padicValNat p M) j hp hp5 hj hb
    omega

#print axioms termDvd
