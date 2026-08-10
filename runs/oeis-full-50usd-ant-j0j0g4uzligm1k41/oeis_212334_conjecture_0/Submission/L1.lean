import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/- Exact integer identity (cleared-denominator Lucas).
   For N = p^r, M = p^(r-1):  with the product over i in [0,k] coprime to p,
   C(N-1,k) * ∏ i  =  (∏ (N - i)) * C(M-1, k/p).
-/

-- the recurrence we need:  choose N (k+1) * (k+1) = choose N k * (N - k)
example (N k : ℕ) : N.choose (k+1) * (k+1) = N.choose k * (N - k) :=
  Nat.choose_succ_right_eq N k

-- product of integers over coprime-to-p indices up to k
noncomputable def Pp (p k : ℕ) : ℤ := ∏ i ∈ (Finset.range (k+1)).filter (fun i => ¬ p ∣ i), (i : ℤ)
noncomputable def Qp (p r k : ℕ) : ℤ :=
  ∏ i ∈ (Finset.range (k+1)).filter (fun i => ¬ p ∣ i), ((p^r : ℤ) - i)

lemma Pp_succ (p k : ℕ) :
    Pp p (k+1) = if p ∣ (k+1) then Pp p k else (k+1 : ℤ) * Pp p k := by
  rcases Classical.em (p ∣ (k+1)) with h | h
  · rw [if_pos h]; unfold Pp
    rw [Finset.range_succ, Finset.filter_insert, if_neg (not_not.mpr h)]
  · rw [if_neg h]; unfold Pp
    rw [Finset.range_succ, Finset.filter_insert, if_pos h, Finset.prod_insert (by simp)]
    push_cast; ring

lemma Qp_succ (p r k : ℕ) :
    Qp p r (k+1) = if p ∣ (k+1) then Qp p r k else ((p^r : ℤ) - (k+1)) * Qp p r k := by
  rcases Classical.em (p ∣ (k+1)) with h | h
  · rw [if_pos h]; unfold Qp
    rw [Finset.range_succ, Finset.filter_insert, if_neg (not_not.mpr h)]
  · rw [if_neg h]; unfold Qp
    rw [Finset.range_succ, Finset.filter_insert, if_pos h, Finset.prod_insert (by simp)]
    push_cast; ring

lemma L1_exact (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    ∀ k, ((p^r - 1).choose k : ℤ) * Pp p k = Qp p r k * ((p^(r-1) - 1).choose (k / p) : ℤ) := by
  intro k
  have hppos : 0 < p := hp.pos
  induction k with
  | zero =>
    simp [Pp, Qp, Finset.range_one, Finset.filter_singleton, Nat.dvd_zero, Nat.zero_div]
  | succ k ih =>
    set N1 := p^r - 1 with hN1
    set M1 := p^(r-1) - 1 with hM1
    by_cases hdvd : p ∣ (k+1)
    · -- p ∣ k+1, set q = (k+1)/p
      have hd := hdvd
      obtain ⟨q, hq⟩ := hd
      have hq0 : q ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at hq; omega
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hq2 : k + 1 = p * q' + p := by rw [hq]; ring
      have hqval : (k+1)/p = q' + 1 := by rw [hq]; exact Nat.mul_div_cancel_left _ hppos
      have hkval : k / p = q' := by
        have h1 : k = p * q' + (p - 1) := by omega
        rw [h1, Nat.mul_add_div hppos, Nat.div_eq_of_lt (by omega)]; ring
      rw [Pp_succ, if_pos hdvd, Qp_succ, if_pos hdvd, hqval]
      have recN : (N1.choose (k+1) : ℤ) * (k+1) = (N1.choose k : ℤ) * ((N1 - k : ℕ) : ℤ) := by
        exact_mod_cast Nat.choose_succ_right_eq N1 k
      have hpr_eq : p^r = p * p^(r-1) := by
        conv_lhs => rw [show r = (r-1)+1 from by omega]
        rw [pow_succ']
      rcases lt_or_ge (q'+1) (p^(r-1)+1) with hqc | hqc
      · -- main case
        have hqle : q'+1 ≤ p^(r-1) := by omega
        have hCB : p*(q'+1) ≤ p*p^(r-1) := Nat.mul_le_mul_left _ hqle
        have hNk : N1 - k = p*(p^(r-1)-(q'+1)) := by
          rw [hN1, hpr_eq, Nat.mul_sub]; omega
        have relA : (N1.choose (k+1):ℤ) * ((q':ℤ)+1)
            = (N1.choose k:ℤ) * ((p^(r-1)-(q'+1):ℕ):ℤ) := by
          have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hppos.ne'
          apply mul_left_cancel₀ hp0
          have e1 : ((k:ℤ)+1) = (p:ℤ) * ((q':ℤ)+1) := by exact_mod_cast hq
          have e2 : ((N1 - k : ℕ):ℤ) = (p:ℤ) * ((p^(r-1)-(q'+1):ℕ):ℤ) := by
            rw [hNk]; push_cast; ring
          calc (p:ℤ) * ((N1.choose (k+1):ℤ) * ((q':ℤ)+1))
              = (N1.choose (k+1):ℤ) * ((k:ℤ)+1) := by rw [e1]; ring
            _ = (N1.choose k:ℤ) * ((N1 - k : ℕ):ℤ) := recN
            _ = (p:ℤ) * ((N1.choose k:ℤ) * ((p^(r-1)-(q'+1):ℕ):ℤ)) := by rw [e2]; ring
        have hMq : M1 - q' = p^(r-1)-(q'+1) := by rw [hM1]; omega
        have relB : (M1.choose (q'+1):ℤ) * ((q':ℤ)+1)
            = (M1.choose q':ℤ) * ((p^(r-1)-(q'+1):ℕ):ℤ) := by
          have := Nat.choose_succ_right_eq M1 q'
          rw [← hMq]; exact_mod_cast this
        have final : ((q':ℤ)+1) * ((N1.choose (k+1):ℤ) * Pp p k)
            = ((q':ℤ)+1) * (Qp p r k * (M1.choose (q'+1):ℤ)) := by
          calc ((q':ℤ)+1) * ((N1.choose (k+1):ℤ) * Pp p k)
              = ((N1.choose (k+1):ℤ) * ((q':ℤ)+1)) * Pp p k := by ring
            _ = ((N1.choose k:ℤ) * ((p^(r-1)-(q'+1):ℕ):ℤ)) * Pp p k := by rw [relA]
            _ = ((p^(r-1)-(q'+1):ℕ):ℤ) * ((N1.choose k:ℤ) * Pp p k) := by ring
            _ = ((p^(r-1)-(q'+1):ℕ):ℤ) * (Qp p r k * (M1.choose (k/p):ℤ)) := by rw [ih]
            _ = ((p^(r-1)-(q'+1):ℕ):ℤ) * (Qp p r k * (M1.choose q':ℤ)) := by rw [hkval]
            _ = Qp p r k * ((M1.choose q':ℤ) * ((p^(r-1)-(q'+1):ℕ):ℤ)) := by ring
            _ = Qp p r k * ((M1.choose (q'+1):ℤ) * ((q':ℤ)+1)) := by rw [relB]
            _ = ((q':ℤ)+1) * (Qp p r k * (M1.choose (q'+1):ℤ)) := by ring
        exact mul_left_cancel₀ (by positivity) final
      · -- q'+1 > p^(r-1): both choose vanish
        have hz1 : N1.choose (k+1) = 0 := by
          apply Nat.choose_eq_zero_of_lt; rw [hN1]
          have h2 : p^r ≤ p*(q'+1) := by rw [hpr_eq]; exact Nat.mul_le_mul_left _ (by omega)
          omega
        have hz2 : M1.choose (q'+1) = 0 := by
          apply Nat.choose_eq_zero_of_lt; rw [hM1]; omega
        rw [hz1, hz2]; push_cast; ring
    · -- p ∤ k+1
      have hqe : (k+1)/p = k/p := by
        rw [Nat.succ_div]; simp [hdvd]
      rw [Pp_succ, if_neg hdvd, Qp_succ, if_neg hdvd, hqe]
      have recN : (N1.choose (k+1) : ℤ) * (k+1) = (N1.choose k : ℤ) * ((N1 - k : ℕ) : ℤ) := by
        exact_mod_cast Nat.choose_succ_right_eq N1 k
      -- goal: C(N1,k+1) * ((k+1)*Pp) = (p^r-(k+1)) * Qp * C(M1,k/p)
      have key : (N1.choose (k+1):ℤ) * ((k+1 : ℤ) * Pp p k)
          = ((N1 - k : ℕ):ℤ) * (Qp p r k * (M1.choose (k/p):ℤ)) := by
        rw [show (N1.choose (k+1):ℤ) * ((k+1:ℤ) * Pp p k)
              = ((N1.choose (k+1):ℤ)*(k+1)) * Pp p k by ring, recN, ← ih]; ring
      rw [key]
      -- now show ((N1-k:ℕ):ℤ) = (p^r:ℤ) - (k+1)  OR  C(M1,k/p)=0
      rcases lt_or_ge k (p^r) with hk | hk
      · have hk1 : k ≤ p^r - 1 := by omega
        have h1le : 1 ≤ p^r := Nat.one_le_pow _ _ hppos
        have hcast : ((N1 - k : ℕ):ℤ) = (p^r : ℤ) - (k+1) := by
          rw [hN1, Nat.cast_sub hk1, Nat.cast_sub h1le]; push_cast; ring
        rw [hcast]; ring
      · have hpr1 : 1 ≤ p^(r-1) := Nat.one_le_pow _ _ hppos
        have hdiv : p^(r-1) ≤ k/p := by
          rw [Nat.le_div_iff_mul_le hppos]
          calc p^(r-1) * p = p^r := by rw [← pow_succ]; congr 1; omega
            _ ≤ k := hk
        have hz : M1.choose (k/p) = 0 := by
          apply Nat.choose_eq_zero_of_lt; rw [hM1]; omega
        rw [hz]; simp

-- card of coprime-to-p indices in [0,k]
lemma card_coprime (p k : ℕ) (hp : Nat.Prime p) :
    ((Finset.range (k+1)).filter (fun i => ¬ p ∣ i)).card = k - k / p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.range_succ, Finset.filter_insert]
    by_cases h : p ∣ (k+1)
    · rw [if_neg (not_not.mpr h), ih]
      obtain ⟨q, hq⟩ := h
      have hq0 : q ≠ 0 := by rintro rfl; simp at hq
      have hk1 : (k+1)/p = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hp.pos
      have hk0 : k/p = q - 1 := by
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        have hq2 : k + 1 = p * q' + p := by rw [hq]; ring
        have h1 : k = p * q' + (p - 1) := by have := hp.pos; omega
        rw [h1, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by have := hp.pos; omega)]; omega
      omega
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]
      have hk1 : (k+1)/p = k/p := by rw [Nat.succ_div]; simp [h]
      have : k / p ≤ k := Nat.div_le_self k p
      omega

lemma L1_mod (p r k : ℕ) (hp : Nat.Prime p) (hr : 3 ≤ r) :
    ((p^r - 1).choose k : ZMod (p^3))
      = (-1)^(k - k/p) * ((p^(r-1) - 1).choose (k/p) : ZMod (p^3)) := by
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  set R := ZMod (p^3)
  set A := (Finset.range (k+1)).filter (fun i => ¬ p ∣ i) with hA
  have hpr0 : ((p^r : ℕ) : R) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow p hr
  -- cast L1_exact via ring hom
  have hex := L1_exact p r hp (by omega) k
  have h := congrArg (Int.castRingHom R) hex
  rw [map_mul, map_mul, Pp, Qp, map_prod, map_prod] at h
  simp only [Int.coe_castRingHom, Int.cast_natCast, Int.cast_sub, Int.cast_pow,
    Int.cast_natCast] at h
  -- h : (Cn:R) * ∏ (i:R) = (∏ ((p^r:R)-(i:R))) * (Cm:R)
  have hQ : (∏ i ∈ A, (((p:R))^r - (i : R))) = (∏ i ∈ A, (-(i : R))) := by
    apply Finset.prod_congr rfl
    intro i _
    have hh : ((p:R))^r = 0 := by rw [← Nat.cast_pow]; exact hpr0
    rw [hh]; ring
  rw [hQ] at h
  -- ∏ (-(i:R)) = (-1)^card * ∏ (i:R)
  have hcardA : A.card = k - k/p := by rw [hA]; exact card_coprime p k hp
  have hneg : (∏ i ∈ A, (-(i : R))) = (-1)^(k - k/p) * (∏ i ∈ A, (i : R)) := by
    rw [Finset.prod_neg, hcardA]
  rw [hneg] at h
  -- PpR is a unit
  have hunit : IsUnit (∏ i ∈ A, (i : R)) := by
    rw [IsUnit.prod_iff]
    intro i hi
    rw [hA, Finset.mem_filter] at hi
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hi.2).symm))
  apply hunit.mul_right_cancel
  rw [h]; ring

-- ===================== L2 : ascending binomial =====================
noncomputable def Qp2 (p r m : ℕ) : ℤ :=
  ∏ i ∈ (Finset.range (m+1)).filter (fun i => ¬ p ∣ i), ((p^r : ℤ) + i)

lemma Qp2_succ (p r m : ℕ) :
    Qp2 p r (m+1) = if p ∣ (m+1) then Qp2 p r m else ((p^r : ℤ) + (m+1)) * Qp2 p r m := by
  rcases Classical.em (p ∣ (m+1)) with h | h
  · rw [if_pos h]; unfold Qp2
    rw [Finset.range_succ, Finset.filter_insert, if_neg (not_not.mpr h)]
  · rw [if_neg h]; unfold Qp2
    rw [Finset.range_succ, Finset.filter_insert, if_pos h, Finset.prod_insert (by simp)]
    push_cast; ring

lemma L2_exact (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    ∀ m, ((p^r + m).choose m : ℤ) * Pp p m
      = Qp2 p r m * ((p^(r-1) + m/p).choose (m/p) : ℤ) := by
  intro m
  have hppos : 0 < p := hp.pos
  have hpr_eq : p^r = p * p^(r-1) := by
    conv_lhs => rw [show r = (r-1)+1 from by omega]
    rw [pow_succ']
  induction m with
  | zero => simp [Pp, Qp2, Finset.range_one, Finset.filter_singleton, Nat.zero_div]
  | succ m ih =>
    -- recurrence: (p^r+m+1)*C(p^r+m,m) = C(p^r+m+1,m+1)*(m+1)
    have heqm : p^r + (m+1) = p^r + m + 1 := by ring
    have rec0 := Nat.succ_mul_choose_eq (p^r + m) m
    have recZ : ((p^r : ℤ) + m + 1) * ((p^r + m).choose m : ℤ)
        = ((p^r + (m+1)).choose (m+1) : ℤ) * (m+1) := by
      rw [heqm]; exact_mod_cast rec0
    by_cases hdvd : p ∣ (m+1)
    · have hd := hdvd
      obtain ⟨q, hq⟩ := hd
      have hq0 : q ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at hq; omega
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hq2 : m + 1 = p * q' + p := by rw [hq]; ring
      have hqval : (m+1)/p = q' + 1 := by rw [hq]; exact Nat.mul_div_cancel_left _ hppos
      have hmval : m / p = q' := by
        have h1 : m = p * q' + (p - 1) := by omega
        rw [h1, Nat.mul_add_div hppos, Nat.div_eq_of_lt (by omega)]; ring
      rw [Pp_succ, if_pos hdvd, Qp2_succ, if_pos hdvd, hqval]
      -- relA : C(p^r+m+1,m+1)*q = (p^(r-1)+q)*C(p^r+m,m)   [after cancel p]
      have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hppos.ne'
      have hpr : ((p^r:ℤ)) = (p:ℤ)*((p^(r-1):ℤ)) := by exact_mod_cast hpr_eq
      have hmm : ((m:ℤ)+1) = (p:ℤ)*((q':ℤ)+1) := by exact_mod_cast hq
      have e1 : ((p^r:ℤ) + m + 1) = (p:ℤ) * ((p^(r-1):ℤ) + (q'+1)) := by
        rw [hpr]; linear_combination hmm
      have relA : ((p^r + (m+1)).choose (m+1):ℤ) * ((q':ℤ)+1)
          = ((p^(r-1):ℤ) + (q'+1)) * ((p^r + m).choose m:ℤ) := by
        apply mul_left_cancel₀ hp0
        calc (p:ℤ) * (((p^r + (m+1)).choose (m+1):ℤ) * ((q':ℤ)+1))
            = ((p^r + (m+1)).choose (m+1):ℤ) * ((m:ℤ)+1) := by rw [hmm]; ring
          _ = ((p^r:ℤ) + m + 1) * ((p^r + m).choose m:ℤ) := by rw [recZ]
          _ = (p:ℤ) * (((p^(r-1):ℤ) + (q'+1)) * ((p^r + m).choose m:ℤ)) := by rw [e1]; ring
      have recB : ((p^(r-1):ℤ) + q' + 1) * ((p^(r-1) + q').choose q' : ℤ)
          = ((p^(r-1) + (q'+1)).choose (q'+1) : ℤ) * ((q':ℤ)+1) := by
        have heqb : p^(r-1) + (q'+1) = p^(r-1) + q' + 1 := by ring
        rw [heqb]; exact_mod_cast Nat.succ_mul_choose_eq (p^(r-1) + q') q'
      have final : ((q':ℤ)+1) * (((p^r + (m+1)).choose (m+1):ℤ) * Pp p m)
          = ((q':ℤ)+1) * (Qp2 p r m * ((p^(r-1) + (q'+1)).choose (q'+1):ℤ)) := by
        calc ((q':ℤ)+1) * (((p^r + (m+1)).choose (m+1):ℤ) * Pp p m)
            = (((p^r + (m+1)).choose (m+1):ℤ) * ((q':ℤ)+1)) * Pp p m := by ring
          _ = (((p^(r-1):ℤ) + (q'+1)) * ((p^r + m).choose m:ℤ)) * Pp p m := by rw [relA]
          _ = ((p^(r-1):ℤ) + (q'+1)) * (((p^r + m).choose m:ℤ) * Pp p m) := by ring
          _ = ((p^(r-1):ℤ) + (q'+1)) * (Qp2 p r m * ((p^(r-1) + m/p).choose (m/p):ℤ)) := by rw [ih]
          _ = ((p^(r-1):ℤ) + (q'+1)) * (Qp2 p r m * ((p^(r-1) + q').choose q':ℤ)) := by rw [hmval]
          _ = Qp2 p r m * (((p^(r-1) + (q'+1)).choose (q'+1):ℤ) * ((q':ℤ)+1)) := by rw [← recB]; ring
          _ = ((q':ℤ)+1) * (Qp2 p r m * ((p^(r-1) + (q'+1)).choose (q'+1):ℤ)) := by ring
      exact mul_left_cancel₀ (by positivity) final
    · -- p ∤ m+1
      have hqe : (m+1)/p = m/p := by rw [Nat.succ_div]; simp [hdvd]
      rw [Pp_succ, if_neg hdvd, Qp2_succ, if_neg hdvd, hqe]
      calc ((p^r + (m+1)).choose (m+1):ℤ) * ((m+1:ℤ) * Pp p m)
          = (((p^r + (m+1)).choose (m+1):ℤ) * (m+1)) * Pp p m := by ring
        _ = (((p^r:ℤ) + m + 1) * ((p^r + m).choose m:ℤ)) * Pp p m := by rw [← recZ]
        _ = ((p^r:ℤ) + (m+1)) * (((p^r + m).choose m:ℤ) * Pp p m) := by ring
        _ = ((p^r:ℤ) + (m+1)) * (Qp2 p r m * ((p^(r-1) + m/p).choose (m/p):ℤ)) := by rw [ih]
        _ = ((p^r:ℤ) + (m+1)) * Qp2 p r m * ((p^(r-1) + m/p).choose (m/p):ℤ) := by ring

lemma L2_mod (p r m : ℕ) (hp : Nat.Prime p) (hr : 3 ≤ r) :
    ((p^r + m).choose m : ZMod (p^3))
      = ((p^(r-1) + m/p).choose (m/p) : ZMod (p^3)) := by
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  set R := ZMod (p^3)
  set A := (Finset.range (m+1)).filter (fun i => ¬ p ∣ i) with hA
  have hpr0 : ((p^r : ℕ) : R) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow p hr
  have hex := L2_exact p r hp (by omega) m
  have h := congrArg (Int.castRingHom R) hex
  rw [map_mul, map_mul, Pp, Qp2, map_prod, map_prod] at h
  simp only [Int.coe_castRingHom, Int.cast_natCast, Int.cast_add, Int.cast_pow,
    Int.cast_natCast] at h
  have hQ : (∏ i ∈ A, (((p:R))^r + (i : R))) = (∏ i ∈ A, (i : R)) := by
    apply Finset.prod_congr rfl
    intro i _
    have hh : ((p:R))^r = 0 := by rw [← Nat.cast_pow]; exact hpr0
    rw [hh]; ring
  rw [hQ] at h
  have hunit : IsUnit (∏ i ∈ A, (i : R)) := by
    rw [IsUnit.prod_iff]
    intro i hi
    rw [hA, Finset.mem_filter] at hi
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hi.2).symm))
  apply hunit.mul_right_cancel
  rw [h]; ring

-- W(k) mod p^3 in terms of level (r-1) binomials
lemma W_mod (p r k : ℕ) (hp : Nat.Prime p) (hr : 3 ≤ r) (hk0 : 1 ≤ k) (hkp : ¬ p ∣ k) :
    ((p^r-1).choose (k-1) : ZMod (p^3)) * ((p^r-1).choose k : ZMod (p^3))
        * ((p^r+k-1).choose (p^r) : ZMod (p^3))^2
      = - (((p^(r-1)-1).choose (k/p) : ZMod (p^3))
          * ((p^(r-1)+k/p).choose (k/p) : ZMod (p^3)))^2 := by
  have hk1m : (k-1)/p = k/p := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Nat.succ_div, if_neg hkp, Nat.add_zero]
  have hadd : p^r + k - 1 = p^r + (k-1) := by have := Nat.one_le_pow r p hp.pos; omega
  have hsymm : (p^r+k-1).choose (p^r) = (p^r+k-1).choose (k-1) := by
    have hle : p^r ≤ p^r+k-1 := by have := Nat.one_le_pow r p hp.pos; omega
    have hnk : (p^r+k-1) - p^r = k-1 := by have := Nat.one_le_pow r p hp.pos; omega
    rw [← Nat.choose_symm hle, hnk]
  have hA1 := L1_mod p r (k-1) hp hr
  have hA2 := L1_mod p r k hp hr
  rw [hk1m] at hA1
  have hA3 : ((p^r+k-1).choose (p^r) : ZMod (p^3))
      = ((p^(r-1)+k/p).choose (k/p) : ZMod (p^3)) := by
    rw [hsymm, hadd, L2_mod p r (k-1) hp hr, hk1m]
  rw [hA1, hA2, hA3]
  have hsign : ((-1 : ZMod (p^3)))^((k-1) - (k/p)) * (-1)^(k - (k/p)) = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨k - k/p - 1, by
      have := Nat.div_lt_self hk0 hp.one_lt; omega⟩
  rw [show (((-1 : ZMod (p^3)))^((k-1) - (k/p)) * ((p^(r-1)-1).choose (k/p) : ZMod (p^3)))
        * ((-1)^(k - (k/p)) * ((p^(r-1)-1).choose (k/p) : ZMod (p^3)))
        * ((p^(r-1)+k/p).choose (k/p) : ZMod (p^3))^2
      = (((-1 : ZMod (p^3)))^((k-1) - (k/p)) * (-1)^(k - (k/p)))
        * (((p^(r-1)-1).choose (k/p) : ZMod (p^3)) * ((p^(r-1)+k/p).choose (k/p) : ZMod (p^3)))^2
      from by ring, hsign]
  ring

-- ===================== term and W identity =====================
def term (n k : ℕ) : ℤ :=
  (n.choose k : ℤ) * ((n - 1).choose k) * ((n + k - 1).choose k) ^ 2

lemma I1nat (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) : k * N.choose k = N * (N-1).choose (k-1) := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N'+1 := ⟨N-1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.add_one_mul_choose_eq N' k']; ring

lemma I2nat (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    k * (N+k-1).choose k = N * (N+k-1).choose N := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
  set n := N+(k'+1)-1 with hn
  have h := Nat.choose_succ_right_eq n k'
  have hnk : n - k' = N := by omega
  have hkn : k' ≤ n := by omega
  have hsymm : n.choose k' = n.choose N := by rw [← hnk, Nat.choose_symm hkn]
  rw [hnk, hsymm] at h
  rw [Nat.mul_comm (k'+1), h, Nat.mul_comm]

-- Wident :  k^3 * term(p^r,k) = p^(3r) * W(k)
lemma Wident (p r k : ℕ) (hp : Nat.Prime p) (hk1 : 1 ≤ k) (hk : k < p^r) :
    (k:ℤ)^3 * term (p^r) k
    = (p:ℤ)^(3*r) * ((p^r-1).choose (k-1) * (p^r-1).choose k * ((p^r+k-1).choose (p^r))^2) := by
  have hN : 1 ≤ p^r := Nat.one_le_pow _ _ hp.pos
  have e1 := I1nat (p^r) k hN hk1
  have e2 := I2nat (p^r) k hN hk1
  have e1Z : (k:ℤ) * (p^r).choose k = (p^r:ℤ) * (p^r-1).choose (k-1) := by exact_mod_cast e1
  have e2Z : (k:ℤ) * (p^r+k-1).choose k = (p^r:ℤ) * (p^r+k-1).choose (p^r) := by exact_mod_cast e2
  have hpr : ((p^r : ℕ) : ℤ) = (p:ℤ)^r := by push_cast; ring
  unfold term
  have key : (k:ℤ)^3 * (((p^r).choose k:ℤ) * ((p^r-1).choose k) * ((p^r+k-1).choose k)^2)
      = ((k:ℤ) * (p^r).choose k) * ((p^r-1).choose k) * ((k:ℤ) * (p^r+k-1).choose k)^2 := by ring
  rw [key, e1Z, e2Z, show 3*r = r*3 from by ring, pow_mul]
  ring

-- divisibility of term by p^(3r) for p∤k
lemma term_dvd (p r k : ℕ) (hp : Nat.Prime p) (hk1 : 1 ≤ k) (hk : k < p^r) (hkp : ¬ p ∣ k) :
    (p:ℤ)^(3*r) ∣ term (p^r) k := by
  have hW := Wident p r k hp hk1 hk
  have hdvd : (p:ℤ)^(3*r) ∣ (k:ℤ)^3 * term (p^r) k := ⟨_, hW⟩
  have hcp : IsCoprime ((p:ℤ)) ((k:ℤ)) :=
    (Nat.isCoprime_iff_coprime).mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hkp)
  have hcop : IsCoprime ((p:ℤ)^(3*r)) ((k:ℤ)^3) := hcp.pow
  exact hcop.dvd_of_dvd_mul_left hdvd

-- the integer u(k) = term/p^(3r), satisfies k^3 * u = W
noncomputable def uu (p r k : ℕ) : ℤ := term (p^r) k / (p:ℤ)^(3*r)

lemma term_eq_uu (p r k : ℕ) (hp : Nat.Prime p) (hk1 : 1 ≤ k) (hk : k < p^r) (hkp : ¬ p ∣ k) :
    term (p^r) k = (p:ℤ)^(3*r) * uu p r k := by
  rw [uu, Int.mul_ediv_cancel' (term_dvd p r k hp hk1 hk hkp)]

lemma uu_mul (p r k : ℕ) (hp : Nat.Prime p) (hk1 : 1 ≤ k) (hk : k < p^r) (hkp : ¬ p ∣ k) :
    (k:ℤ)^3 * uu p r k
      = ((p^r-1).choose (k-1) * (p^r-1).choose k * ((p^r+k-1).choose (p^r))^2 : ℤ) := by
  have hW := Wident p r k hp hk1 hk
  have ht := term_eq_uu p r k hp hk1 hk hkp
  have hp0 : ((p:ℤ)^(3*r)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.pos.ne')
  apply mul_left_cancel₀ hp0
  rw [show (p:ℤ)^(3*r) * ((k:ℤ)^3 * uu p r k) = (k:ℤ)^3 * ((p:ℤ)^(3*r) * uu p r k) by ring,
      ← ht, hW]

-- The harmonic core (to be proven): sum of uu over coprime residues ≡ 0 mod p^3
def Fset (p r : ℕ) : Finset ℕ := (Finset.range (p^r)).filter (fun k => ¬ p ∣ k)

lemma L1_modg (p s e k : ℕ) (hp : Nat.Prime p) (hes : e ≤ s) (he : 1 ≤ e) :
    ((p^s - 1).choose k : ZMod (p^e))
      = (-1)^(k - k/p) * ((p^(s-1) - 1).choose (k/p) : ZMod (p^e)) := by
  haveI : NeZero (p^e) := ⟨by have := hp.pos; positivity⟩
  set R := ZMod (p^e)
  set A := (Finset.range (k+1)).filter (fun i => ¬ p ∣ i) with hA
  have hpr0 : ((p^s : ℕ) : R) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow p hes
  have hex := L1_exact p s hp (by omega) k
  have h := congrArg (Int.castRingHom R) hex
  rw [map_mul, map_mul, Pp, Qp, map_prod, map_prod] at h
  simp only [Int.coe_castRingHom, Int.cast_natCast, Int.cast_sub, Int.cast_pow,
    Int.cast_natCast] at h
  have hQ : (∏ i ∈ A, (((p:R))^s - (i : R))) = (∏ i ∈ A, (-(i : R))) := by
    apply Finset.prod_congr rfl
    intro i _
    have hh : ((p:R))^s = 0 := by rw [← Nat.cast_pow]; exact hpr0
    rw [hh]; ring
  rw [hQ] at h
  have hcardA : A.card = k - k/p := by rw [hA]; exact card_coprime p k hp
  have hneg : (∏ i ∈ A, (-(i : R))) = (-1)^(k - k/p) * (∏ i ∈ A, (i : R)) := by
    rw [Finset.prod_neg, hcardA]
  rw [hneg] at h
  have hunit : IsUnit (∏ i ∈ A, (i : R)) := by
    rw [IsUnit.prod_iff]
    intro i hi
    rw [hA, Finset.mem_filter] at hi
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hi.2).symm))
  apply hunit.mul_right_cancel
  rw [h]; ring

lemma L2_modg (p s e m : ℕ) (hp : Nat.Prime p) (hes : e ≤ s) (he : 1 ≤ e) :
    ((p^s + m).choose m : ZMod (p^e))
      = ((p^(s-1) + m/p).choose (m/p) : ZMod (p^e)) := by
  haveI : NeZero (p^e) := ⟨by have := hp.pos; positivity⟩
  set R := ZMod (p^e)
  set A := (Finset.range (m+1)).filter (fun i => ¬ p ∣ i) with hA
  have hpr0 : ((p^s : ℕ) : R) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow p hes
  have hex := L2_exact p s hp (by omega) m
  have h := congrArg (Int.castRingHom R) hex
  rw [map_mul, map_mul, Pp, Qp2, map_prod, map_prod] at h
  simp only [Int.coe_castRingHom, Int.cast_natCast, Int.cast_add, Int.cast_pow,
    Int.cast_natCast] at h
  have hQ : (∏ i ∈ A, (((p:R))^s + (i : R))) = (∏ i ∈ A, (i : R)) := by
    apply Finset.prod_congr rfl
    intro i _
    have hh : ((p:R))^s = 0 := by rw [← Nat.cast_pow]; exact hpr0
    rw [hh]; ring
  rw [hQ] at h
  have hunit : IsUnit (∏ i ∈ A, (i : R)) := by
    rw [IsUnit.prod_iff]
    intro i hi
    rw [hA, Finset.mem_filter] at hi
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hi.2).symm))
  apply hunit.mul_right_cancel
  rw [h]; ring

-- ===================== harmonic core machinery =====================

theorem reindex_sum (n q : ℕ) (hq : 0 < q) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ k ∈ range (q * n), f k = ∑ a ∈ range n, ∑ b ∈ range q, f (q * a + b) := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (i := fun k => (k / q, k % q)) (j := fun x => q * x.1 + x.2)
  · intro k hk; rw [mem_range] at hk; rw [mem_product, mem_range, mem_range]
    exact ⟨Nat.div_lt_of_lt_mul hk, Nat.mod_lt _ hq⟩
  · intro x hx; rw [mem_product, mem_range, mem_range] at hx; rw [mem_range]
    have : x.1 + 1 ≤ n := hx.1; nlinarith [hx.2, this, hq]
  · intro k hk; exact Nat.div_add_mod k q
  · intro x hx; rw [mem_product, mem_range, mem_range] at hx
    have h1 : (q * x.1 + x.2) / q = x.1 := by rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hx.2, add_zero]
    have h2 : (q * x.1 + x.2) % q = x.2 := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hx.2]
    rw [h1, h2]
  · intro k hk; rw [Nat.div_add_mod]

def Vnat (p t m : ℕ) : ℕ := (p^t - 1).choose m * (p^t + m).choose m

theorem Vred (p t e m : ℕ) (hp : Nat.Prime p) (het : e ≤ t) (he : 1 ≤ e) :
    ((Vnat p t m : ℕ) : ZMod (p^e))^2 = ((Vnat p (t-1) (m/p) : ℕ) : ZMod (p^e))^2 := by
  have e1 := L1_modg p t e m hp het he
  have e2 := L2_modg p t e m hp het he
  unfold Vnat
  push_cast
  rw [e1, e2]
  have hsq : ((-1:ZMod (p^e))^(m - m/p))^2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  set A := ((p^(t-1)-1).choose (m/p) : ZMod (p^e))
  set B := ((p^(t-1)+m/p).choose (m/p) : ZMod (p^e))
  have : ((-1:ZMod (p^e))^(m - m/p) * A * B)^2 = (((-1:ZMod (p^e))^(m-m/p))^2) * (A*B)^2 := by ring
  rw [this, hsq, one_mul]

theorem Vrec (p t e : ℕ) (hp : Nat.Prime p) (het : e ≤ t) (he : 1 ≤ e) (ht : 1 ≤ t) :
    (∑ m ∈ range (p^t), ((Vnat p t m : ℕ) : ZMod (p^e))^2)
      = (p : ZMod (p^e)) * ∑ m ∈ range (p^(t-1)), ((Vnat p (t-1) m : ℕ) : ZMod (p^e))^2 := by
  have hpe : p^t = p * p^(t-1) := by
    conv_lhs => rw [show t = (t-1)+1 by omega]
    rw [pow_succ']
  rw [hpe, reindex_sum (p^(t-1)) p hp.pos, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hinner : ∀ b ∈ range p, ((Vnat p t (p*a+b) : ℕ) : ZMod (p^e))^2
      = ((Vnat p (t-1) a : ℕ) : ZMod (p^e))^2 := by
    intro b hb; rw [mem_range] at hb; rw [Vred p t e (p*a+b) hp het he]
    congr 2; rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hb, add_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem prec (p a b : ℕ) (hp : 0 < p) (hab : a ≤ b) (z : ZMod (p^b))
    (h : ZMod.castHom (pow_dvd_pow p hab) (ZMod (p^a)) z = 0) :
    ((p^a : ℕ) : ZMod (p^b)) ∣ z := by
  haveI : NeZero (p^b) := ⟨by positivity⟩
  have hcast : ZMod.castHom (pow_dvd_pow p hab) (ZMod (p^a)) z = ((z.val : ℕ) : ZMod (p^a)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [hcast, ZMod.natCast_eq_zero_iff] at h
  obtain ⟨t, ht⟩ := h
  refine ⟨(t : ZMod (p^b)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  rw [ht]; push_cast; ring

theorem precp (p : ℕ) (hp : 0 < p) (z : ZMod (p^3))
    (h : ZMod.castHom (show p ∣ p^3 by exact dvd_pow_self p (by norm_num)) (ZMod p) z = 0) :
    (p : ZMod (p^3)) ∣ z := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  have hcast : (ZMod.castHom (show p ∣ p^3 by exact dvd_pow_self p (by norm_num)) (ZMod p)) z
      = ((z.val : ℕ) : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [hcast, ZMod.natCast_eq_zero_iff] at h
  obtain ⟨t, ht⟩ := h
  refine ⟨(t : ZMod (p^3)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  rw [ht]; push_cast; ring

theorem pcast_sq_zero (p : ℕ) : (p : ZMod (p^2))^2 = 0 := by
  have : ((p^2 : ℕ) : ZMod (p^2)) = 0 := ZMod.natCast_self _
  push_cast at this; exact this

theorem factC1 (p t : ℕ) (hp : Nat.Prime p) (ht : 1 ≤ t) :
    (∑ m ∈ range (p^t), ((Vnat p t m : ℕ) : ZMod (p^1))^2) = 0 := by
  rw [Vrec p t 1 hp ht le_rfl ht]
  have : (p : ZMod (p^1)) = 0 := by rw [ZMod.natCast_eq_zero_iff, pow_one]
  rw [this, zero_mul]

theorem Ldvd (p s : ℕ) (hp : Nat.Prime p) (hs : 1 ≤ s) :
    ((p^1 : ℕ) : ZMod (p^2)) ∣ ∑ m ∈ range (p^s), ((Vnat p s m : ℕ) : ZMod (p^2))^2 := by
  apply prec p 1 2 hp.pos (by norm_num)
  rw [map_sum]
  have : ∀ m ∈ range (p^s), ZMod.castHom (pow_dvd_pow p (show (1:ℕ) ≤ 2 by norm_num)) (ZMod (p^1))
        (((Vnat p s m : ℕ) : ZMod (p^2))^2) = ((Vnat p s m : ℕ) : ZMod (p^1))^2 := by
    intro m hm; rw [map_pow, map_natCast]
  rw [Finset.sum_congr rfl this]
  exact factC1 p s hp hs

theorem factC (p s : ℕ) (hp : Nat.Prime p) (hs : 2 ≤ s) :
    (∑ m ∈ range (p^s), ((Vnat p s m : ℕ) : ZMod (p^2))^2) = 0 := by
  rw [Vrec p s 2 hp hs (by norm_num) (by omega)]
  obtain ⟨w, hw⟩ := Ldvd p (s-1) hp (by omega)
  rw [hw]
  have h2 : ((p^1:ℕ):ZMod (p^2)) = (p : ZMod (p^2)) := by rw [pow_one]
  rw [h2]
  rw [show (p : ZMod (p^2)) * ((p : ZMod (p^2)) * w) = (p:ZMod (p^2))^2 * w by ring, pcast_sq_zero, zero_mul]

theorem factD (p s : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hs : 2 ≤ s) :
    (∑ m ∈ range (p^s), (m : ZMod (p^2)) * ((Vnat p s m : ℕ) : ZMod (p^2))^2) = 0 := by
  set G : ZMod (p^2) := ∑ b ∈ range p, (b : ZMod (p^2)) with hG
  have hpe : p^s = p * p^(s-1) := by
    conv_lhs => rw [show s = (s-1)+1 by omega]; rw [pow_succ']
  have hmain : (∑ m ∈ range (p^s), (m : ZMod (p^2)) * ((Vnat p s m : ℕ) : ZMod (p^2))^2)
      = (∑ a ∈ range (p^(s-1)), ((Vnat p (s-1) a : ℕ) : ZMod (p^2))^2) * G := by
    rw [hpe, reindex_sum (p^(s-1)) p hp.pos, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    have hinner : ∀ b ∈ range p,
        ((p*a+b : ℕ) : ZMod (p^2)) * ((Vnat p s (p*a+b) : ℕ) : ZMod (p^2))^2
        = ((p*a+b : ℕ) : ZMod (p^2)) * ((Vnat p (s-1) a : ℕ) : ZMod (p^2))^2 := by
      intro b hb; rw [mem_range] at hb
      rw [Vred p s 2 (p*a+b) hp (by omega) (by norm_num)]
      congr 3
      rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hb, add_zero]
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
    have hsum : (∑ b ∈ range p, ((p*a+b : ℕ) : ZMod (p^2))) = G := by
      have : (∑ b ∈ range p, ((p*a+b : ℕ) : ZMod (p^2)))
          = (∑ b ∈ range p, ((p:ZMod (p^2))*(a:ZMod (p^2)) + (b:ZMod (p^2)))) := by
        apply Finset.sum_congr rfl; intro b hb; push_cast; ring
      rw [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hG]
      rw [show (p:ZMod (p^2)) * ((p:ZMod (p^2))*(a:ZMod (p^2))) = (p:ZMod (p^2))^2 * (a:ZMod (p^2)) by ring]
      rw [pcast_sq_zero, zero_mul, zero_add]
    rw [hsum]; ring
  rw [hmain]
  obtain ⟨w, hw⟩ := Ldvd p (s-1) hp (by omega)
  have h2 : ((p^1:ℕ):ZMod (p^2)) = (p : ZMod (p^2)) := by rw [pow_one]
  rw [h2] at hw
  have hGdvd : p ∣ ∑ b ∈ range p, b := by
    have h2x := Finset.sum_range_id_mul_two p
    have hd2 : p ∣ (∑ b ∈ range p, b) * 2 := by rw [h2x]; exact Dvd.intro _ rfl
    exact (Nat.Coprime.dvd_of_dvd_mul_right (by
      have hnd : ¬ p ∣ 2 := by
        intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd) hd2)
  obtain ⟨c, hc⟩ := hGdvd
  have hGval : G = (p : ZMod (p^2)) * (c : ZMod (p^2)) := by
    rw [hG]
    have : (∑ b ∈ range p, (b : ZMod (p^2))) = ((∑ b ∈ range p, b : ℕ) : ZMod (p^2)) := by push_cast; rfl
    rw [this, hc]; push_cast; ring
  rw [hw, hGval]
  rw [show ((p:ZMod (p^2)) * w) * ((p:ZMod (p^2)) * c) = (p:ZMod (p^2))^2 * (w*c) by ring, pcast_sq_zero, zero_mul]

theorem factC3 (p s : ℕ) (hp : Nat.Prime p) (hs : 2 ≤ s) :
    ((p^2:ℕ):ZMod (p^3)) ∣ ∑ m ∈ range (p^s), ((Vnat p s m : ℕ):ZMod (p^3))^2 := by
  apply prec p 2 3 hp.pos (by norm_num)
  rw [map_sum]
  have : ∀ m ∈ range (p^s), ZMod.castHom (pow_dvd_pow p (show (2:ℕ) ≤ 3 by norm_num)) (ZMod (p^2))
        (((Vnat p s m : ℕ) : ZMod (p^3))^2) = ((Vnat p s m : ℕ) : ZMod (p^2))^2 := by
    intro m hm; rw [map_pow, map_natCast]
  rw [Finset.sum_congr rfl this]; exact factC p s hp hs

theorem factD3 (p s : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hs : 2 ≤ s) :
    ((p^2:ℕ):ZMod (p^3)) ∣ ∑ m ∈ range (p^s), (m:ZMod (p^3))*((Vnat p s m : ℕ):ZMod (p^3))^2 := by
  apply prec p 2 3 hp.pos (by norm_num)
  rw [map_sum]
  have : ∀ m ∈ range (p^s), ZMod.castHom (pow_dvd_pow p (show (2:ℕ) ≤ 3 by norm_num)) (ZMod (p^2))
        ((m:ZMod (p^3))*((Vnat p s m : ℕ) : ZMod (p^3))^2)
        = (m:ZMod (p^2))*((Vnat p s m : ℕ) : ZMod (p^2))^2 := by
    intro m hm; rw [map_mul, map_pow, map_natCast, map_natCast]
  rw [Finset.sum_congr rfl this]; exact factD p s hp h5 hs

theorem map_ringinv {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  obtain ⟨u, rfl⟩ := hx
  rw [Ring.inverse_unit u]
  have h1 : f ((u : Rˣ) : R) = ((Units.map (f : R →* S) u : Sˣ) : S) := (Units.coe_map _ u).symm
  rw [h1, Ring.inverse_unit, ← map_inv, Units.coe_map]
  rfl

theorem sum_zmod_range (p : ℕ) [NeZero p] (G : ZMod p → ZMod p) :
    ∑ x : ZMod p, G x = ∑ a ∈ range p, G (a : ZMod p) := by
  refine Finset.sum_nbij' (fun x => x.val) (fun a => (a : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro x hx; rw [mem_range]; exact ZMod.val_lt x
  · intro a ha; exact mem_univ _
  · intro x hx; exact ZMod.natCast_zmod_val x
  · intro a ha; rw [mem_range] at ha; exact ZMod.val_natCast_of_lt ha
  · intro x hx; exact congrArg G (ZMod.natCast_zmod_val x).symm

theorem psum_zero (p j : ℕ) (hp : Nat.Prime p) (hj : ¬ (p-1) ∣ j) (hj0 : 1 ≤ j) :
    (∑ a ∈ (range p).filter (fun a => a ≠ 0), (Ring.inverse (a : ZMod p))^j) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hstep1 : (∑ a ∈ (range p).filter (fun a => a ≠ 0), (Ring.inverse (a : ZMod p))^j)
      = ∑ a ∈ range p, (Ring.inverse (a : ZMod p))^j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hxnot
    rw [Finset.mem_filter] at hxnot; push_neg at hxnot
    rw [hxnot hx]; simp [Ring.inverse_zero, zero_pow (by omega : j ≠ 0)]
  rw [hstep1, ← sum_zmod_range p (fun x => (Ring.inverse x)^j)]
  simp only [Ring.inverse_eq_inv]
  have hbij : (∑ x : ZMod p, (x⁻¹)^j) = ∑ x : ZMod p, x^j := by
    apply Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹) <;> intro x hx
    · exact mem_univ _
    · exact mem_univ _
    · exact inv_inv x
    · exact inv_inv x
    · rfl
  rw [hbij]
  have hmap : (univ : Finset (ZMod p)ˣ).map ⟨Units.val, Units.val_injective⟩ = univ \ {(0 : ZMod p)} := by
    ext x
    simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff, mem_singleton]
    exact isUnit_iff_ne_zero
  have h0 : (∑ x : ZMod p, x^j) = ∑ x ∈ univ \ {(0:ZMod p)}, x^j := by
    rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p)))]
    rw [Finset.sum_singleton, zero_pow (by omega : j ≠ 0), add_zero]
  rw [h0, ← hmap, Finset.sum_map]
  have hu := FiniteField.sum_pow_units (ZMod p) j
  rw [ZMod.card] at hu
  simp only [Function.Embedding.coeFn_mk]
  rw [hu, if_neg hj]

theorem inv_expand (R : Type*) [CommRing R] (x u : R) (hx : x^3 = 0) (hu : IsUnit u) :
    Ring.inverse (x + u) = Ring.inverse u - x * (Ring.inverse u)^2 + x^2 * (Ring.inverse u)^3 := by
  set v := Ring.inverse u with hv
  have huv : u * v = 1 := Ring.mul_inverse_cancel u hu
  set w := v - x*v^2 + x^2*v^3 with hw
  have key : (x + u) * w = 1 := by
    rw [hw]; linear_combination (1 - x*v + x^2*v^2) * huv + v^3 * hx
  have hunit : IsUnit (x+u) := isUnit_of_mul_eq_one w key
  have hinv := Ring.inverse_mul_cancel (x+u) hunit
  calc Ring.inverse (x+u) = Ring.inverse (x+u) * ((x+u) * w) := by rw [key, mul_one]
    _ = (Ring.inverse (x+u) * (x+u)) * w := by ring
    _ = w := by rw [hinv, one_mul]

theorem inv3_expand (R : Type*) [CommRing R] (x u : R) (hx : x^3 = 0) (hu : IsUnit u) :
    (Ring.inverse (x + u))^3
      = (Ring.inverse u)^3 - 3*x*(Ring.inverse u)^4 + 6*x^2*(Ring.inverse u)^5 := by
  rw [inv_expand R x u hx hu]
  set v := Ring.inverse u
  linear_combination (v^9*x^3 - 3*v^8*x^2 + 6*v^7*x - 7*v^6) * hx

theorem psum3 (p j : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hj : ¬ (p-1) ∣ j) (hj0 : 1 ≤ j) :
    ((p:ℕ):ZMod (p^3)) ∣ ∑ a ∈ (range p).filter (fun a => a ≠ 0), (Ring.inverse (a : ZMod (p^3)))^j := by
  apply precp p hp.pos
  rw [map_sum]
  have : ∀ a ∈ (range p).filter (fun a => a ≠ 0),
      ZMod.castHom (show p ∣ p^3 by exact dvd_pow_self p (by norm_num)) (ZMod p)
        ((Ring.inverse (a : ZMod (p^3)))^j) = (Ring.inverse (a : ZMod p))^j := by
    intro a ha
    rw [Finset.mem_filter, mem_range] at ha
    have hu : IsUnit ((a:ZMod (p^3))) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr (by
        intro hd; exact ha.2 (Nat.eq_zero_of_dvd_of_lt hd ha.1))).symm))
    rw [map_pow, map_ringinv _ _ hu, map_natCast]
  rw [Finset.sum_congr rfl this]; exact psum_zero p j hp hj hj0

theorem pcube0 (p : ℕ) : ((p:ZMod (p^3)))^3 = 0 := by
  have : ((p^3:ℕ):ZMod (p^3)) = 0 := ZMod.natCast_self _
  push_cast at this; convert this using 2

theorem hkey_ax (p r k : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hr : 3 ≤ r) (hk0 : 1 ≤ k)
    (hk : k < p^r) (hkp : ¬ p ∣ k) :
    ((k:ZMod (p^3)))^3 * (uu p r k : ZMod (p^3)) = -((Vnat p (r-1) (k/p) : ℕ):ZMod (p^3))^2 := by
  have h := congrArg (Int.castRingHom (ZMod (p^3))) (uu_mul p r k hp hk0 hk hkp)
  simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_pow, Int.cast_natCast] at h
  rw [h]
  rw [W_mod p r k hp hr hk0 hkp]
  unfold Vnat
  push_cast
  ring

lemma harmonic_core (p r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hr : 3 ≤ r) :
    (∑ k ∈ Fset p r, (uu p r k : ZMod (p^3))) = 0 := by
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  -- per element rewrite
  have huu : ∀ k ∈ Fset p r, (uu p r k : ZMod (p^3))
      = -(Ring.inverse (k:ZMod (p^3)))^3 * ((Vnat p (r-1) (k/p) : ℕ):ZMod (p^3))^2 := by
    intro k hk
    rw [Fset, mem_filter, mem_range] at hk
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun h => hk.2 (h ▸ dvd_zero p))
    have hunit : IsUnit ((k:ZMod (p^3))) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hk.2).symm))
    have hv := Ring.inverse_mul_cancel (k:ZMod (p^3)) hunit
    have key := hkey_ax p r k hp h5 hr hk1 hk.1 hk.2
    -- multiply key by inverse^3
    set v := Ring.inverse (k:ZMod (p^3)) with hvdef
    have hvk3 : v^3 * ((k:ZMod (p^3)))^3 = 1 := by
      rw [← mul_pow, hv, one_pow]
    calc (uu p r k : ZMod (p^3)) = (v^3 * ((k:ZMod (p^3)))^3) * (uu p r k : ZMod (p^3)) := by rw [hvk3, one_mul]
      _ = v^3 * (((k:ZMod (p^3)))^3 * (uu p r k : ZMod (p^3))) := by ring
      _ = v^3 * (-((Vnat p (r-1) (k/p) : ℕ):ZMod (p^3))^2) := by rw [key]
      _ = -v^3 * ((Vnat p (r-1) (k/p) : ℕ):ZMod (p^3))^2 := by ring
  rw [Finset.sum_congr rfl huu]
  set F : ℕ → ZMod (p^3) := fun k => -(Ring.inverse (k:ZMod (p^3)))^3 * ((Vnat p (r-1) (k/p) : ℕ):ZMod (p^3))^2 with hF
  -- reindex Fset
  have hreindex : (∑ k ∈ Fset p r, F k)
      = ∑ m ∈ range (p^(r-1)), ∑ a ∈ (range p).filter (fun a => a ≠ 0), F (p*m+a) := by
    rw [Fset, Finset.sum_filter]
    have hpe : p^r = p * p^(r-1) := by
      conv_lhs => rw [show r = (r-1)+1 by omega]; rw [pow_succ']
    rw [hpe, reindex_sum (p^(r-1)) p hp.pos]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    rw [mem_range] at ha
    have hdvd_iff : p ∣ (p*m+a) ↔ a = 0 := by
      constructor
      · intro h
        have hpa : p ∣ a := (Nat.dvd_add_right (dvd_mul_right p m)).mp h
        exact Nat.eq_zero_of_dvd_of_lt hpa ha
      · intro h; rw [h, add_zero]; exact dvd_mul_right p m
    exact if_congr (not_congr hdvd_iff) rfl rfl
  rw [hreindex]
  set Af := (range p).filter (fun a => a ≠ 0) with hAf
  set P : ZMod (p^3) := (p:ZMod (p^3)) with hP
  -- per (m,a) expansion
  have hexp : ∀ m ∈ range (p^(r-1)), ∀ a ∈ Af, F (p*m+a)
      = -(((Vnat p (r-1) m:ℕ):ZMod (p^3))^2) * (Ring.inverse (a:ZMod (p^3)))^3
        + 3*P*(m:ZMod (p^3))*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2 * (Ring.inverse (a:ZMod (p^3)))^4
        - 6*P^2*(m:ZMod (p^3))^2*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2 * (Ring.inverse (a:ZMod (p^3)))^5 := by
    intro m hm a ha
    rw [hAf, mem_filter, mem_range] at ha
    have hu : IsUnit ((a:ZMod (p^3))) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr (by
        intro hd; exact ha.2 (Nat.eq_zero_of_dvd_of_lt hd ha.1))).symm))
    have hx3 : (P*(m:ZMod (p^3)))^3 = 0 := by
      rw [mul_pow, hP, pcube0, zero_mul]
    have hcast : ((p*m+a:ℕ):ZMod (p^3)) = P*(m:ZMod (p^3)) + (a:ZMod (p^3)) := by
      push_cast [hP]; ring
    have hdiv : (p*m+a)/p = m := by
      rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt ha.1, add_zero]
    rw [hF]
    simp only [hdiv, hcast]
    rw [inv3_expand (ZMod (p^3)) (P*(m:ZMod (p^3))) (a:ZMod (p^3)) hx3 hu]
    ring
  rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun a ha => hexp m hm a ha))]
  -- inner sum over a
  have hinner : ∀ m ∈ range (p^(r-1)),
      (∑ a ∈ Af, (-(((Vnat p (r-1) m:ℕ):ZMod (p^3))^2) * (Ring.inverse (a:ZMod (p^3)))^3
        + 3*P*(m:ZMod (p^3))*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2 * (Ring.inverse (a:ZMod (p^3)))^4
        - 6*P^2*(m:ZMod (p^3))^2*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2 * (Ring.inverse (a:ZMod (p^3)))^5))
      = -(((Vnat p (r-1) m:ℕ):ZMod (p^3))^2) * (∑ a ∈ Af, (Ring.inverse (a:ZMod (p^3)))^3)
        + 3*P*(m:ZMod (p^3))*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2 * (∑ a ∈ Af, (Ring.inverse (a:ZMod (p^3)))^4)
        - 6*P^2*(m:ZMod (p^3))^2*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2 * (∑ a ∈ Af, (Ring.inverse (a:ZMod (p^3)))^5) := by
    intro m hm
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl hinner]
  -- now pull constants out over m
  set S3 := ∑ a ∈ Af, (Ring.inverse (a:ZMod (p^3)))^3 with hS3
  set S4 := ∑ a ∈ Af, (Ring.inverse (a:ZMod (p^3)))^4 with hS4
  set S5 := ∑ a ∈ Af, (Ring.inverse (a:ZMod (p^3)))^5 with hS5
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : (∑ m ∈ range (p^(r-1)), -(((Vnat p (r-1) m:ℕ):ZMod (p^3))^2) * S3)
      = -S3 * (∑ m ∈ range (p^(r-1)), ((Vnat p (r-1) m:ℕ):ZMod (p^3))^2) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m hm; ring
  have hB : (∑ m ∈ range (p^(r-1)), 3*P*(m:ZMod (p^3))*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2 * S4)
      = 3*P*S4 * (∑ m ∈ range (p^(r-1)), (m:ZMod (p^3))*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m hm; ring
  have hC : (∑ m ∈ range (p^(r-1)), 6*P^2*(m:ZMod (p^3))^2*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2 * S5)
      = 6*P^2*S5 * (∑ m ∈ range (p^(r-1)), (m:ZMod (p^3))^2*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m hm; ring
  rw [hA, hB, hC]
  set C := ∑ m ∈ range (p^(r-1)), (m:ZMod (p^3))^2*((Vnat p (r-1) m:ℕ):ZMod (p^3))^2 with hCdef
  obtain ⟨w1, hw1⟩ := factC3 p (r-1) hp (by omega)
  obtain ⟨w2, hw2⟩ := factD3 p (r-1) hp h5 (by omega)
  obtain ⟨c3, hc3⟩ := psum3 p 3 hp h5 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) (by norm_num)
  obtain ⟨c5, hc5⟩ := psum3 p 5 hp h5 (fun h => by
    have hle := Nat.le_of_dvd (by norm_num) h
    have : p = 5 ∨ p = 6 := by omega
    rcases this with h5'|h6
    · rw [h5'] at h; norm_num at h
    · rw [h6] at hp; norm_num at hp) (by norm_num)
  rw [← hS3] at hc3; rw [← hS5] at hc5
  rw [hc3, hc5, hw1, hw2]
  have hpp : ((p:ℕ):ZMod (p^3)) = P := by rw [hP]
  have hp2 : ((p^2:ℕ):ZMod (p^3)) = P^2 := by rw [hP]; push_cast; ring
  have hP3 : P^3 = 0 := by rw [hP]; exact pcube0 p
  rw [hpp, hp2]
  linear_combination (-(c3*w1) + 3*(S4*w2) - 6*(c5*C)) * hP3
lemma key_Snew_ge3 (p r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hr : 3 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣ ∑ k ∈ Fset p r, term (p ^ r) k := by
  -- factor out p^(3r)
  have hfac : ∑ k ∈ Fset p r, term (p ^ r) k
      = (p:ℤ)^(3*r) * ∑ k ∈ Fset p r, uu p r k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Fset, Finset.mem_filter, Finset.mem_range] at hk
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (by rintro rfl; exact hk.2 (dvd_zero p))
    exact term_eq_uu p r k hp hk1 hk.1 hk.2
  rw [hfac, pow_add]
  apply mul_dvd_mul_left
  have hgoal : (p:ℤ)^3 = ((p^3:ℕ):ℤ) := by push_cast; ring
  rw [hgoal, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact harmonic_core p r hp h5 hr

-- ===================== key_match reduction (building block) =====================
-- W' and W'' brackets (the "Wident RHS" data for the multiples-of-p case)
noncomputable def Wbr (N k : ℕ) : ℤ :=
  ((N-1).choose (k-1) : ℤ) * (N-1).choose k * ((N+k-1).choose N)^2

/-- Exact reduction for the `key_match` sum: it expresses the level-`r` vs level-`(r-1)`
term difference (weighted by `m^3`) as `p^(3r-3)` times a binomial difference `W'(m) - W''(m)`.
This is the foundation for proving `key_match` by the same power-sum-cancellation method as
`harmonic_core`, *without* needing Wolstenholme's theorem. -/
theorem km_reduction (p r m : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) (hm1 : 1 ≤ m) (hm : m < p^(r-1)) :
    (m:ℤ)^3 * (term (p^r) (p*m) - term (p^(r-1)) m)
      = (p:ℤ)^(3*r-3) * (Wbr (p^r) (p*m) - Wbr (p^(r-1)) m) := by
  have hppos : 0 < p := hp.pos
  have hpm1 : 1 ≤ p*m := by have := hp.pos; nlinarith
  have hpmlt : p*m < p^r := by
    have hpe : p^r = p * p^(r-1) := by conv_lhs => rw [show r = (r-1)+1 by omega]; rw [pow_succ']
    rw [hpe]; exact (Nat.mul_lt_mul_left hppos).mpr hm
  have e1 : ((p*m:ℕ):ℤ)^3 * term (p^r) (p*m) = (p:ℤ)^(3*r) * Wbr (p^r) (p*m) := by
    rw [Wident p r (p*m) hp hpm1 hpmlt]; unfold Wbr; push_cast; ring
  have e2 : (m:ℤ)^3 * term (p^(r-1)) m = (p:ℤ)^(3*(r-1)) * Wbr (p^(r-1)) m := by
    rw [Wident p (r-1) m hp hm1 hm]; unfold Wbr; ring
  have hpm3 : ((p*m:ℕ):ℤ)^3 = (p:ℤ)^3 * (m:ℤ)^3 := by push_cast; ring
  rw [hpm3] at e1
  have e1' : (m:ℤ)^3 * term (p^r) (p*m) = (p:ℤ)^(3*r-3) * Wbr (p^r) (p*m) := by
    have hp3 : (p:ℤ)^3 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hppos.ne')
    apply mul_left_cancel₀ hp3
    rw [show (p:ℤ)^3 * ((m:ℤ)^3 * term (p^r) (p*m)) = (p:ℤ)^3 * (m:ℤ)^3 * term (p^r) (p*m) by ring, e1]
    rw [show (p:ℤ)^3 * ((p:ℤ)^(3*r-3) * Wbr (p^r) (p*m)) = (p:ℤ)^(3 + (3*r-3)) * Wbr (p^r) (p*m) by rw [pow_add]; ring]
    congr 2; omega
  have e2' : (m:ℤ)^3 * term (p^(r-1)) m = (p:ℤ)^(3*r-3) * Wbr (p^(r-1)) m := by
    rw [e2]; congr 2; omega
  rw [mul_sub, e1', e2', ← mul_sub]
