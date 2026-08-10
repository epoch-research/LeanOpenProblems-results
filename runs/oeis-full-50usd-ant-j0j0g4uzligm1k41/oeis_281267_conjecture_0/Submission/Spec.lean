import FormalConjectures.Util.ProblemImports

open Finset

section ADef
open Polynomial Nat

/--
A281267: Main diagonal of A276554.
The sequence $a(n)$ is the coefficient of $x^n$ in the polynomial
$$\prod_{k=1}^n (1 - x^k)^{n k}$$
-/
noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Polynomial ℤ :=
    (Ico 1 (n + 1)).prod fun k : ℕ =>
      (1 - X ^ k) ^ (n * k)
  P_n.coeff n

end ADef

open scoped ArithmeticFunction.sigma
open PowerSeries



noncomputable def fc : ℕ → ℚ
  | 0 => 1
  | (n+1) => (-1/(n+1 : ℚ)) * ∑ m ∈ Finset.range (n+1), ((σ 2 (m+1) : ℕ) : ℚ) * fc (n - m)
decreasing_by exact Nat.lt_succ_of_le (Nat.sub_le n m)

noncomputable def Fs : ℚ⟦X⟧ := PowerSeries.mk fc
noncomputable def Es : ℚ⟦X⟧ := PowerSeries.mk (fun m => ((σ 2 m : ℕ) : ℚ))

lemma coeff_Es (m : ℕ) : (coeff (R:=ℚ) m) Es = ((σ 2 m : ℕ):ℚ) := by simp [Es]
lemma coeff_Fs (m : ℕ) : (coeff (R:=ℚ) m) Fs = fc m := by simp [Fs]

lemma fc_rec (n : ℕ) :
    (n+1 : ℚ) * fc (n+1) = - ∑ m ∈ Finset.range (n+1), ((σ 2 (m+1) : ℕ):ℚ) * fc (n-m) := by
  conv_lhs => rw [fc]
  field_simp

lemma coeff_Es0 : (coeff (R:=ℚ) 0) Es = 0 := by rw [coeff_Es]; simp

lemma ode : (X : ℚ⟦X⟧) * (d⁄dX ℚ) Fs = - Es * Fs := by
  ext j
  rcases j with _ | n
  · rw [neg_mul, map_neg, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    simp [coeff_Es0]
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_Fs, mul_comm, fc_rec n]
    rw [neg_mul, map_neg, PowerSeries.coeff_mul]
    congr 1
    conv_rhs => rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_Es, coeff_Fs]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [ArithmeticFunction.map_zero, Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro m hm
    congr 2
    omega

-- recurrence for coefficients of Fs^M
noncomputable def cM (M : ℕ) (j : ℕ) : ℚ := (coeff (R:=ℚ) j) (Fs ^ M)

lemma ode_pow (M : ℕ) (hM : 1 ≤ M) :
    (X : ℚ⟦X⟧) * (d⁄dX ℚ) (Fs ^ M) = -(M:ℚ⟦X⟧) * (Es * Fs ^ M) := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
  have h1 : X * ((M:ℚ⟦X⟧) * (Fs ^ (M-1) * (d⁄dX ℚ) Fs))
       = (M:ℚ⟦X⟧) * (Fs ^ (M-1) * (X * (d⁄dX ℚ) Fs)) := by ring
  rw [h1, ode]
  have hpow : Fs ^ (M-1) * Fs = Fs ^ M := by
    rw [← pow_succ]; congr 1; omega
  ring_nf
  rw [← hpow]
  ring

lemma coeff_Es_mul (g : ℚ⟦X⟧) (n : ℕ) :
    (coeff (R:=ℚ) (n+1)) (Es * g) = ∑ m ∈ range (n+1), ((σ 2 (m+1):ℕ):ℚ) * (coeff (n-m)) g := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_Es]
  rw [Finset.sum_range_succ']
  simp only [ArithmeticFunction.map_zero, Nat.cast_zero, zero_mul, add_zero, Nat.succ_sub_succ]

lemma cM_rec (M n : ℕ) (hM : 1 ≤ M) :
    ((n+1:ℕ):ℚ) * cM M (n+1)
      = -(M:ℚ) * ∑ m ∈ range (n+1), ((σ 2 (m+1):ℕ):ℚ) * cM M (n-m) := by
  have h := congrArg (coeff (R:=ℚ) (n+1)) (ode_pow M hM)
  rw [coeff_succ_X_mul, coeff_derivative] at h
  rw [show -(M:ℚ⟦X⟧) = PowerSeries.C (-(M:ℚ)) by rw [map_neg, map_natCast],
      PowerSeries.coeff_C_mul] at h
  rw [coeff_Es_mul] at h
  simp only [cM]
  rw [← h]; push_cast; ring


noncomputable def invGeom (k : ℕ) : ℚ⟦X⟧ := mk (fun m => if k ∣ m then (1:ℚ) else 0)

lemma coeff_invGeom (k m : ℕ) : (coeff (R:=ℚ) m) (invGeom k) = if k ∣ m then 1 else 0 := by
  simp [invGeom]

lemma one_sub_mul_invGeom (k : ℕ) (hk : 1 ≤ k) :
    ((1 : ℚ⟦X⟧) - X^k) * invGeom k = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_invGeom, coeff_X_pow_mul', coeff_invGeom]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [PowerSeries.coeff_one]
    simp only [if_pos (dvd_zero k), if_true]
    rw [if_neg (by omega : ¬ k ≤ 0)]
    simp
  · rw [PowerSeries.coeff_one, if_neg hn.ne']
    by_cases hkn : k ≤ n
    · rw [if_pos hkn]
      by_cases hd : k ∣ n
      · rw [if_pos hd, if_pos (Nat.dvd_sub hd dvd_rfl), sub_self]
      · rw [if_neg hd, if_neg (fun h => hd (by
          have := Nat.sub_add_cancel hkn; exact this ▸ Nat.dvd_add h dvd_rfl)), sub_zero]
    · rw [if_neg hkn, sub_zero, if_neg (fun h => hkn (Nat.le_of_dvd hn h))]

lemma invGeom_mul_pow (k : ℕ) (hk : 1 ≤ k) :
    invGeom k * ((1:ℚ⟦X⟧) - X^k)^k = (1 - X^k)^(k-1) := by
  have hpow : ((1:ℚ⟦X⟧)-X^k)^k = ((1:ℚ⟦X⟧)-X^k) * ((1:ℚ⟦X⟧)-X^k)^(k-1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow, ← mul_assoc, mul_comm (invGeom k) ((1:ℚ⟦X⟧)-X^k), one_sub_mul_invGeom k hk, one_mul]

lemma factor_ode (k : ℕ) (hk : 1 ≤ k) :
    (X:ℚ⟦X⟧) * (d⁄dX ℚ) (((1:ℚ⟦X⟧)-X^k)^k)
      = (-((k:ℚ⟦X⟧))^2 * X^k * invGeom k) * ((1:ℚ⟦X⟧)-X^k)^k := by
  have hd : (d⁄dX ℚ) ((1:ℚ⟦X⟧) - X^k) = -((k:ℚ⟦X⟧) * X^(k-1)) := by
    rw [map_sub, Derivation.leibniz_pow, PowerSeries.derivative_X]
    simp [nsmul_eq_mul]
  rw [Derivation.leibniz_pow, hd]
  rw [smul_eq_mul, nsmul_eq_mul]
  rw [mul_assoc (-((k:ℚ⟦X⟧))^2 * X^k) (invGeom k) (((1:ℚ⟦X⟧)-X^k)^k), invGeom_mul_pow k hk]
  have hxk : (X:ℚ⟦X⟧) * ((k:ℚ⟦X⟧) * ((1-X^k)^(k-1) * -((k:ℚ⟦X⟧)*X^(k-1))))
           = -((k:ℚ⟦X⟧))^2 * (X * X^(k-1)) * (1-X^k)^(k-1) := by ring
  rw [hxk, ← pow_succ']
  rw [show (k-1)+1 = k by omega]

lemma prod_ode (s : Finset ℕ) (hs : ∀ k ∈ s, 1 ≤ k) :
    (X:ℚ⟦X⟧) * (d⁄dX ℚ) (∏ k ∈ s, ((1:ℚ⟦X⟧)-X^k)^k)
      = (∑ k ∈ s, (-((k:ℚ⟦X⟧))^2 * X^k * invGeom k)) * (∏ k ∈ s, ((1:ℚ⟦X⟧)-X^k)^k) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hIH := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
    have haa : 1 ≤ a := hs a (Finset.mem_insert_self a s)
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
    rw [show (X:ℚ⟦X⟧) * (((1:ℚ⟦X⟧)-X^a)^a * (d⁄dX ℚ) (∏ k ∈ s, ((1:ℚ⟦X⟧)-X^k)^k))
          = ((1:ℚ⟦X⟧)-X^a)^a * (X * (d⁄dX ℚ) (∏ k ∈ s, ((1:ℚ⟦X⟧)-X^k)^k)) by ring]
    rw [show (X:ℚ⟦X⟧) * ((∏ k ∈ s, ((1:ℚ⟦X⟧)-X^k)^k) * (d⁄dX ℚ) (((1:ℚ⟦X⟧)-X^a)^a))
          = (X * (d⁄dX ℚ) (((1:ℚ⟦X⟧)-X^a)^a)) * (∏ k ∈ s, ((1:ℚ⟦X⟧)-X^k)^k) by ring]
    rw [hIH, factor_ode a haa]
    ring

lemma filter_dvd_eq_divisors (i N : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (Finset.Ico 1 (N+1)).filter (· ∣ i) = i.divisors := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ico, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hk1, hkN⟩, hki⟩; exact ⟨hki, by omega⟩
  · rintro ⟨hki, hi0⟩
    refine ⟨⟨?_, ?_⟩, hki⟩
    · rcases Nat.eq_zero_or_pos k with h|h
      · subst h; simp at hki; omega
      · exact h
    · have := Nat.le_of_dvd hi hki; omega

lemma coeff_term (k i : ℕ) :
    (coeff (R:=ℚ) i) ((k:ℚ⟦X⟧)^2 * X^k * invGeom k)
      = (k:ℚ)^2 * (if k ≤ i ∧ k ∣ i then 1 else 0) := by
  have hc : ((k:ℚ⟦X⟧))^2 = PowerSeries.C ((k:ℚ)^2) := by
    rw [map_pow, map_natCast]
  rw [mul_assoc, hc, PowerSeries.coeff_C_mul, coeff_X_pow_mul', coeff_invGeom]
  by_cases hki : k ≤ i
  · rw [if_pos hki]
    by_cases hd : k ∣ i
    · have : k ∣ i - k := Nat.dvd_sub hd dvd_rfl
      rw [if_pos this, if_pos ⟨hki, hd⟩]
    · rw [if_neg (fun h => hd (by have := Nat.sub_add_cancel hki; exact this ▸ Nat.dvd_add h dvd_rfl)),
          if_neg (fun h => hd h.2)]
  · rw [if_neg hki, if_neg (fun h => hki h.1), mul_zero]

lemma coeff_Hsum (N i : ℕ) (hi1 : 1 ≤ i) (hiN : i ≤ N) :
    (coeff (R:=ℚ) i) (∑ k ∈ Finset.Ico 1 (N+1), (k:ℚ⟦X⟧)^2 * X^k * invGeom k)
      = ((σ 2 i : ℕ) : ℚ) := by
  rw [map_sum]
  simp_rw [coeff_term]
  have hstep : ∀ k ∈ Finset.Ico 1 (N+1), (k:ℚ)^2 * (if k ≤ i ∧ k ∣ i then (1:ℚ) else 0)
      = if k ∣ i then (k:ℚ)^2 else 0 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    by_cases hd : k ∣ i
    · have : k ≤ i := Nat.le_of_dvd hi1 hd
      rw [if_pos ⟨this, hd⟩, if_pos hd, mul_one]
    · rw [if_neg (fun h => hd h.2), if_neg hd, mul_zero]
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, filter_dvd_eq_divisors i N hi1 hiN]
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  rfl

noncomputable def GzQ (N : ℕ) : ℚ⟦X⟧ := ∏ k ∈ Finset.Ico 1 (N+1), ((1:ℚ⟦X⟧)-X^k)^k
noncomputable def Hsum (N : ℕ) : ℚ⟦X⟧ := ∑ k ∈ Finset.Ico 1 (N+1), (k:ℚ⟦X⟧)^2 * X^k * invGeom k

lemma coeff_Hsum0 (N : ℕ) : (coeff (R:=ℚ) 0) (Hsum N) = 0 := by
  rw [Hsum, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_Ico] at hk
  rw [coeff_term]
  simp only [Nat.le_zero]
  rw [if_neg (by rintro ⟨h,_⟩; omega), mul_zero]

lemma GzQ_ode (N : ℕ) : (X:ℚ⟦X⟧) * (d⁄dX ℚ) (GzQ N) = (-(Hsum N)) * GzQ N := by
  rw [GzQ, prod_ode _ (by intro k hk; rw [Finset.mem_Ico] at hk; omega)]
  congr 1
  rw [Hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _; ring

lemma GzQ_rec (N n : ℕ) (hnN : n + 1 ≤ N) :
    ((n+1:ℕ):ℚ) * (coeff (R:=ℚ) (n+1)) (GzQ N)
      = -∑ m ∈ range (n+1), ((σ 2 (m+1):ℕ):ℚ) * (coeff (n-m)) (GzQ N) := by
  have h := congrArg (coeff (R:=ℚ) (n+1)) (GzQ_ode N)
  rw [coeff_succ_X_mul, coeff_derivative, neg_mul, map_neg, PowerSeries.coeff_mul] at h
  rw [show ((n+1:ℕ):ℚ) = ((n:ℚ)+1) by push_cast; ring, mul_comm, h]
  congr 1
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ']
  rw [coeff_Hsum0]
  simp only [zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  rw [Hsum, coeff_Hsum N (m+1) (by omega) (by omega), Nat.succ_sub_succ]

lemma coeff_zero_GzQ (N : ℕ) : (coeff (R:=ℚ) 0) (GzQ N) = 1 := by
  rw [GzQ, PowerSeries.coeff_zero_eq_constantCoeff, map_prod]
  apply Finset.prod_eq_one
  intro k hk
  rw [Finset.mem_Ico] at hk
  rw [map_pow, map_sub, map_one, map_pow, PowerSeries.constantCoeff_X,
      zero_pow (by omega), sub_zero, one_pow]

lemma fc_zero : fc 0 = 1 := by rw [fc]

lemma connect (N : ℕ) : ∀ j, j ≤ N → fc j = (coeff (R:=ℚ) j) (GzQ N) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    match j with
    | 0 => rw [coeff_zero_GzQ, fc_zero]
    | (n+1) =>
      have hfc := fc_rec n
      have hgz := GzQ_rec N n hj
      have hsum : ∑ m ∈ range (n+1), ((σ 2 (m+1):ℕ):ℚ) * fc (n-m)
                = ∑ m ∈ range (n+1), ((σ 2 (m+1):ℕ):ℚ) * (coeff (n-m)) (GzQ N) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_range] at hm
        rw [ih (n-m) (by omega) (by omega)]
      have key : ((n+1:ℕ):ℚ) * fc (n+1) = ((n+1:ℕ):ℚ) * (coeff (n+1)) (GzQ N) := by
        rw [hgz, ← hsum, ← hfc]; push_cast; ring
      have hne : ((n+1:ℕ):ℚ) ≠ 0 := by positivity
      exact mul_left_cancel₀ hne key

noncomputable def aa (n : ℕ) : ℤ :=
  (∏ k ∈ Finset.Ico 1 (n + 1), ((1:Polynomial ℤ) - Polynomial.X ^ k) ^ (n * k)).coeff n

lemma coeff_pow_congr {A B : ℚ⟦X⟧} {N : ℕ} (h : ∀ j < N, (coeff (R:=ℚ) j) A = coeff j B) (M : ℕ) :
    ∀ j < N, (coeff (R:=ℚ) j) (A^M) = coeff j (B^M) := by
  have h1 : (X:ℚ⟦X⟧)^N ∣ (A - B) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro j hj; rw [map_sub, h j hj, sub_self]
  have h2 : (X:ℚ⟦X⟧)^N ∣ (A^M - B^M) := dvd_trans h1 (sub_dvd_pow_sub_pow A B M)
  rw [PowerSeries.X_pow_dvd_iff] at h2
  intro j hj; have := h2 j hj; rw [map_sub, sub_eq_zero] at this; exact this

noncomputable def Φcoe : Polynomial ℤ →+* ℚ⟦X⟧ :=
  (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

lemma coeff_Φcoe (P : Polynomial ℤ) (m : ℕ) : (coeff (R:=ℚ) m) (Φcoe P) = ((P.coeff m : ℤ) : ℚ) := by
  simp only [Φcoe, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeff_coe, Polynomial.coe_mapRingHom, Polynomial.coeff_map, eq_intCast]

lemma Φcoe_X : Φcoe (Polynomial.X) = (X : ℚ⟦X⟧) := by
  simp only [Φcoe, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

noncomputable def GzP (N : ℕ) : Polynomial ℤ := ∏ k ∈ Finset.Ico 1 (N+1), ((1:Polynomial ℤ) - Polynomial.X ^ k) ^ k

lemma Φcoe_GzP (N : ℕ) : Φcoe (GzP N) = GzQ N := by
  rw [GzP, GzQ, map_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [map_pow, map_sub, map_one, map_pow, Φcoe_X]

lemma a_eq (n : ℕ) : ((aa n : ℤ) : ℚ) = (coeff (R:=ℚ) n) (Fs ^ n) := by
  have h1 : ((aa n : ℤ):ℚ) = (coeff (R:=ℚ) n) (Φcoe (∏ k ∈ Finset.Ico 1 (n + 1), ((1:Polynomial ℤ) - Polynomial.X ^ k) ^ (n * k))) := by
    rw [coeff_Φcoe]; rfl
  rw [h1]
  have h2 : Φcoe (∏ k ∈ Finset.Ico 1 (n + 1), ((1:Polynomial ℤ) - Polynomial.X ^ k) ^ (n * k)) = (GzQ n)^n := by
    rw [map_prod, GzQ, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro k _
    rw [map_pow, map_sub, map_one, map_pow, Φcoe_X, ← pow_mul]
    congr 1; ring
  rw [h2]
  have h3 : ∀ j < n+1, (coeff (R:=ℚ) j) (GzQ n) = coeff j Fs := by
    intro j hj; rw [← connect n j (by omega), coeff_Fs]
  exact coeff_pow_congr h3 n n (by omega)

lemma cM_int (M j : ℕ) : ∃ z : ℤ, cM M j = (z:ℚ) := by
  have h3 : ∀ i < j+1, (coeff (R:=ℚ) i) Fs = coeff i (GzQ (j+1)) := by
    intro i hi; rw [coeff_Fs, connect (j+1) i (by omega)]
  have hcong := coeff_pow_congr h3 M j (by omega)
  refine ⟨((GzP (j+1))^M).coeff j, ?_⟩
  rw [cM, hcong, ← Φcoe_GzP, ← map_pow, coeff_Φcoe]

-- ===== sigma helper lemmas =====
lemma sigma2_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (σ 2) (p ^ i) = ∑ j ∈ range (i + 1), p ^ (2 * j) := by
  rw [ArithmeticFunction.sigma_apply_prime_pow hp]
  apply Finset.sum_congr rfl; intro j _; ring_nf

lemma sigma2_mul_prime {p : ℕ} (hp : p.Prime) {s : ℕ} (hs : 0 < s) :
    (σ 2) (p * s) =
      (σ 2) s + p ^ (2 * (s.factorization p + 1)) * (σ 2) (ordCompl[p] s) := by
  set a := s.factorization p with ha
  set s' := ordCompl[p] s with hs'
  have hsne : s ≠ 0 := hs.ne'
  have hfac : p ^ a * s' = s := Nat.ordProj_mul_ordCompl_eq_self s p
  have hcop : Nat.Coprime (p ^ a) s' :=
    (Nat.coprime_ordCompl hp hsne).pow_left a
  have hcop2 : Nat.Coprime (p ^ (a+1)) s' :=
    (Nat.coprime_ordCompl hp hsne).pow_left (a+1)
  have hmul := ArithmeticFunction.isMultiplicative_sigma (k := 2)
  have e1 : (σ 2) s = (σ 2) (p ^ a) * (σ 2) s' := by
    rw [← hfac, hmul.map_mul_of_coprime hcop]
  have e2 : (σ 2) (p * s) = (σ 2) (p ^ (a+1)) * (σ 2) s' := by
    have : p * s = p ^ (a+1) * s' := by rw [← hfac]; ring
    rw [this, hmul.map_mul_of_coprime hcop2]
  have e3 : (σ 2) (p ^ (a+1)) = (σ 2) (p ^ a) + p ^ (2 * (a+1)) := by
    rw [sigma2_prime_pow hp, sigma2_prime_pow hp, Finset.sum_range_succ]
  rw [e2, e3, e1, add_mul]

-- ===== expand & Phi setup =====
lemma derivative_expand (p : ℕ) (hp : p ≠ 0) (g : ℚ⟦X⟧) :
    (d⁄dX ℚ) (PowerSeries.expand p hp g)
      = (p:ℚ⟦X⟧) * X^(p-1) * PowerSeries.expand p hp ((d⁄dX ℚ) g) := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
  have hp0 : 0 < p := by omega
  ext n
  rw [coeff_derivative, PowerSeries.coeff_expand]
  rw [mul_assoc, show ((p:ℚ⟦X⟧)) = PowerSeries.C (p:ℚ) by rw [map_natCast]]
  rw [PowerSeries.coeff_C_mul, coeff_X_pow_mul']
  by_cases hpn : p ∣ (n+1)
  · rw [if_pos hpn]
    obtain ⟨q, hnq⟩ : ∃ q, n + 1 = p * q := hpn
    have hq1 : 1 ≤ q := by rcases Nat.eq_zero_or_pos q with h|h
                           · rw [h, mul_zero] at hnq; omega
                           · exact h
    have epq : p * (q-1) + p = p * q := by
      have h : (q-1)+1 = q := Nat.succ_pred_eq_of_pos hq1
      calc p*(q-1)+p = p*((q-1)+1) := by ring
        _ = p*q := by rw [h]
    have hpge : p ≤ p * q := Nat.le_mul_of_pos_right p hq1
    have hpn1 : p - 1 ≤ n := by omega
    rw [if_pos hpn1]
    have hm : n - (p-1) = p * (q-1) := by omega
    rw [hm, PowerSeries.coeff_expand, if_pos (Dvd.intro _ rfl),
        Nat.mul_div_cancel_left _ hp0, coeff_derivative]
    rw [show (n+1)/p = q from by rw [hnq, Nat.mul_div_cancel_left _ hp0]]
    rw [show q-1+1 = q from Nat.succ_pred_eq_of_pos hq1]
    have hcast : ((n:ℚ) + 1) = (p:ℚ) * (q:ℚ) := by
      have : (n:ℚ)+1 = ((n+1:ℕ):ℚ) := by push_cast; ring
      rw [this, hnq]; push_cast; ring
    have hcast2 : ((q-1:ℕ):ℚ) + 1 = (q:ℚ) := by rw [Nat.cast_sub hq1]; push_cast; ring
    rw [hcast, hcast2]; ring
  · rw [if_neg hpn]
    by_cases hpn1 : p - 1 ≤ n
    · rw [if_pos hpn1]
      have hnd : ¬ p ∣ (n - (p-1)) := by
        intro h
        apply hpn
        have h2 : p ∣ (n - (p-1)) + p := Dvd.dvd.add h (dvd_refl p)
        have : (n - (p-1)) + p = n + 1 := by omega
        rwa [this] at h2
      rw [PowerSeries.coeff_expand, if_neg hnd]; simp
    · rw [if_neg hpn1]; simp

lemma constantCoeff_Fs : PowerSeries.constantCoeff Fs = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_Fs, fc_zero]

lemma expand_Fs_ode (p : ℕ) (hp : p ≠ 0) :
    (X:ℚ⟦X⟧) * (d⁄dX ℚ) (PowerSeries.expand p hp Fs)
      = -((p:ℚ⟦X⟧) * PowerSeries.expand p hp Es) * PowerSeries.expand p hp Fs := by
  have hde := derivative_expand p hp Fs
  rw [hde]
  have hxx : (X:ℚ⟦X⟧) * X^(p-1) = X^p := by rw [← pow_succ']; congr 1; omega
  rw [show (X:ℚ⟦X⟧) * ((p:ℚ⟦X⟧) * X^(p-1) * PowerSeries.expand p hp ((d⁄dX ℚ) Fs))
        = (p:ℚ⟦X⟧) * ((X * X^(p-1)) * PowerSeries.expand p hp ((d⁄dX ℚ) Fs)) by ring]
  rw [hxx, ← PowerSeries.expand_X p hp, ← map_mul, ode, map_mul, map_neg]
  ring

noncomputable def bigPhi (p : ℕ) (hp : p ≠ 0) : ℚ⟦X⟧ :=
  (PowerSeries.expand p hp Fs)⁻¹ * Fs^p

lemma cc_expand_Fs (p : ℕ) (hp : p ≠ 0) :
    PowerSeries.constantCoeff (PowerSeries.expand p hp Fs) = 1 := by
  rw [PowerSeries.constantCoeff_expand, constantCoeff_Fs]

lemma expand_Fs_ne (p : ℕ) (hp : p ≠ 0) : PowerSeries.expand p hp Fs ≠ 0 := by
  intro h
  have := cc_expand_Fs p hp
  rw [h] at this; simp at this

lemma expand_mul_Phi (p : ℕ) (hp : p ≠ 0) :
    PowerSeries.expand p hp Fs * bigPhi p hp = Fs^p := by
  rw [bigPhi, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [cc_expand_Fs]; exact one_ne_zero),
      one_mul]

lemma Fs_pow_mul (p : ℕ) (hp : p ≠ 0) (M : ℕ) :
    Fs^(M*p) = PowerSeries.expand p hp (Fs^M) * bigPhi p hp ^ M := by
  rw [map_pow, ← mul_pow, expand_mul_Phi, ← pow_mul]
  congr 1; ring

noncomputable def Bser (p : ℕ) (hp : p ≠ 0) : ℚ⟦X⟧ :=
  -((p:ℚ⟦X⟧) * Es) + (p:ℚ⟦X⟧) * PowerSeries.expand p hp Es

lemma Phi_ode (p : ℕ) (hp : p ≠ 0) :
    (X:ℚ⟦X⟧) * (d⁄dX ℚ) (bigPhi p hp) = Bser p hp * bigPhi p hp := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
  have A1 : (X:ℚ⟦X⟧) * (d⁄dX ℚ) (Fs^p) = -(p:ℚ⟦X⟧) * (Es * Fs^p) := ode_pow p hp1
  have A2 : PowerSeries.expand p hp Fs * bigPhi p hp = Fs^p := expand_mul_Phi p hp
  have A3 : (X:ℚ⟦X⟧) * (d⁄dX ℚ) (PowerSeries.expand p hp Fs)
      = -((p:ℚ⟦X⟧) * PowerSeries.expand p hp Es) * PowerSeries.expand p hp Fs := expand_Fs_ode p hp
  have leib : (d⁄dX ℚ) (PowerSeries.expand p hp Fs * bigPhi p hp)
      = PowerSeries.expand p hp Fs * (d⁄dX ℚ) (bigPhi p hp)
        + bigPhi p hp * (d⁄dX ℚ) (PowerSeries.expand p hp Fs) := by
    rw [Derivation.leibniz]; simp only [smul_eq_mul]
  have hXD : (X:ℚ⟦X⟧) * (d⁄dX ℚ) (PowerSeries.expand p hp Fs * bigPhi p hp)
      = PowerSeries.expand p hp Fs * ((X:ℚ⟦X⟧) * (d⁄dX ℚ) (bigPhi p hp))
        + bigPhi p hp * ((X:ℚ⟦X⟧) * (d⁄dX ℚ) (PowerSeries.expand p hp Fs)) := by
    rw [leib]; ring
  have main : PowerSeries.expand p hp Fs * ((X:ℚ⟦X⟧) * (d⁄dX ℚ) (bigPhi p hp))
        + bigPhi p hp * ((X:ℚ⟦X⟧) * (d⁄dX ℚ) (PowerSeries.expand p hp Fs))
      = -(p:ℚ⟦X⟧) * (Es * (PowerSeries.expand p hp Fs * bigPhi p hp)) := by
    rw [← hXD, A2]; exact A1
  apply mul_left_cancel₀ (expand_Fs_ne p hp)
  rw [Bser]
  linear_combination main - bigPhi p hp * A3

-- ===== vpge infrastructure =====
def vpge (p : ℕ) (c : ℤ) (x : ℚ) : Prop := x = 0 ∨ c ≤ padicValRat p x

lemma vpge_zero (p : ℕ) (c : ℤ) : vpge p c 0 := Or.inl rfl

lemma vpge_mono {p : ℕ} {c c' : ℤ} {x : ℚ} (h : vpge p c x) (hc : c' ≤ c) : vpge p c' x := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans hc h)

lemma vpge_add {p : ℕ} [Fact p.Prime] {c : ℤ} {a b : ℚ} (ha : vpge p c a) (hb : vpge p c b) :
    vpge p c (a + b) := by
  rcases ha with ha | ha
  · rw [ha, zero_add]; exact hb
  rcases hb with hb | hb
  · rw [hb, add_zero]; exact Or.inr ha
  by_cases hab : a + b = 0
  · exact Or.inl hab
  · exact Or.inr (le_trans (le_min ha hb) (padicValRat.min_le_padicValRat_add hab))

lemma vpge_mul {p : ℕ} [Fact p.Prime] {c d : ℤ} {a b : ℚ} (ha : vpge p c a) (hb : vpge p d b) :
    vpge p (c + d) (a * b) := by
  by_cases hA : a = 0
  · rw [hA, zero_mul]; exact Or.inl rfl
  by_cases hB : b = 0
  · rw [hB, mul_zero]; exact Or.inl rfl
  · right
    have ha' : c ≤ padicValRat p a := ha.resolve_left hA
    have hb' : d ≤ padicValRat p b := hb.resolve_left hB
    rw [padicValRat.mul hA hB]; linarith

lemma vpge_sum {p : ℕ} [Fact p.Prime] {ι : Type*} {c : ℤ} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, vpge p c (f i)) : vpge p c (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp; exact vpge_zero p c
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact vpge_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma vpge_intCast {p : ℕ} [Fact p.Prime] (z : ℤ) : vpge p 0 (z:ℚ) := by
  by_cases h : z = 0
  · rw [h]; exact Or.inl (by simp)
  · right; rw [padicValRat.of_int]; exact_mod_cast Nat.zero_le _

lemma vpge_of_dvd {p : ℕ} [Fact p.Prime] {k : ℕ} {m : ℤ} (h : (p:ℤ)^k ∣ m) :
    vpge p (k:ℤ) (m:ℚ) := by
  by_cases hm : m = 0
  · left; rw [hm]; simp
  · right
    rw [padicValRat.of_int]
    have hp : Fact p.Prime := ‹_›
    have hdvd : p^k ∣ m.natAbs := by
      rw [← Int.ofNat_dvd_left, show ((p^k:ℕ):ℤ) = (p:ℤ)^k by push_cast; ring]; exact h
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp.out (by simpa using hm)).mp hdvd
    rw [show padicValInt p m = m.natAbs.factorization p from by
          rw [Nat.factorization_def _ hp.out]; rfl]
    exact_mod_cast hle

lemma vpge_int {p : ℕ} [Fact p.Prime] {c : ℤ} {n : ℤ} (hc : 0 ≤ c) (h : vpge p c (n:ℚ)) :
    (p:ℤ)^c.toNat ∣ n := by
  by_cases hn0 : n = 0
  · subst hn0; exact dvd_zero _
  · rcases h with h0 | h0
    · exact absurd (by exact_mod_cast h0) hn0
    · rw [padicValRat.of_int] at h0
      have hle : c.toNat ≤ padicValInt p n := by omega
      rw [show ((p:ℤ)^c.toNat) = ((p^c.toNat:ℕ):ℤ) by push_cast; ring, Int.ofNat_dvd_left]
      have hp : Fact p.Prime := ‹_›
      rw [Nat.Prime.pow_dvd_iff_le_factorization hp.out (by simpa using hn0)]
      rw [show padicValInt p n = n.natAbs.factorization p from by
            rw [Nat.factorization_def _ hp.out]; rfl] at hle
      exact hle

-- ===== Bser coefficients and valuation =====
lemma coeff_Bser (p : ℕ) (hp : p ≠ 0) (t : ℕ) :
    coeff (R:=ℚ) t (Bser p hp)
      = -((p:ℚ) * ((σ 2 t : ℕ):ℚ)) + (p:ℚ) * (if p ∣ t then ((σ 2 (t/p):ℕ):ℚ) else 0) := by
  rw [Bser, map_add, map_neg,
      show ((p:ℚ⟦X⟧)) = PowerSeries.C (p:ℚ) by rw [map_natCast]]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_Es, PowerSeries.coeff_expand]
  by_cases h : p ∣ t
  · rw [if_pos h, if_pos h, coeff_Es]
  · rw [if_neg h, if_neg h]

lemma coeff_zero_Bser (p : ℕ) (hp : p ≠ 0) : coeff (R:=ℚ) 0 (Bser p hp) = 0 := by
  rw [coeff_Bser]; simp

noncomputable def Bcoe (p t : ℕ) : ℤ :=
  -(p:ℤ) * (σ 2 t : ℤ) + (p:ℤ) * (if p ∣ t then (σ 2 (t/p) : ℤ) else 0)

lemma coeff_Bser_int (p : ℕ) (hp : p ≠ 0) (t : ℕ) :
    coeff (R:=ℚ) t (Bser p hp) = ((Bcoe p t : ℤ):ℚ) := by
  rw [coeff_Bser, Bcoe]
  by_cases h : p ∣ t <;> simp [h] <;> push_cast <;> ring

lemma Bcoe_dvd (p : ℕ) (hp : p.Prime) (t : ℕ) :
    (p:ℤ)^(2*(t.factorization p)+1) ∣ Bcoe p t := by
  by_cases hd : p ∣ t
  · obtain ⟨s, rfl⟩ := hd
    by_cases hs : s = 0
    · subst hs; simp [Bcoe]
    · have hs1 : 0 < s := Nat.pos_of_ne_zero hs
      have hfac : (p*s).factorization p = s.factorization p + 1 := by
        rw [Nat.factorization_mul hp.pos.ne' hs, Finsupp.add_apply, hp.factorization_self]
        omega
      have hpsdiv : (p*s)/p = s := Nat.mul_div_cancel_left s hp.pos
      have hsig := sigma2_mul_prime hp hs1
      have hcast : (σ 2 (p*s):ℤ)
          = (σ 2 s:ℤ) + (p:ℤ)^(2*(s.factorization p+1)) * (σ 2 (ordCompl[p] s):ℤ) := by
        exact_mod_cast hsig
      have hpow : (p:ℤ)^(2*(s.factorization p+1)+1)
          = (p:ℤ) * (p:ℤ)^(2*(s.factorization p+1)) := by rw [pow_succ']
      have hkey : Bcoe p (p*s)
          = -((p:ℤ)^(2*(s.factorization p+1)+1)) * (σ 2 (ordCompl[p] s):ℤ) := by
        simp only [Bcoe, if_pos (dvd_mul_right p s), hpsdiv]
        rw [hcast, hpow]; ring
      rw [hfac, hkey]
      exact ⟨-(σ 2 (ordCompl[p] s):ℤ), by ring⟩
  · rw [Nat.factorization_eq_zero_of_not_dvd hd]
    simp only [Bcoe, if_neg hd, mul_zero, add_zero]
    exact ⟨-(σ 2 t:ℤ), by ring⟩

-- ===== Psi =====
noncomputable def Psi (p : ℕ) (hp : p ≠ 0) : ℚ⟦X⟧ :=
  mk (fun t => coeff (R:=ℚ) t (Bser p hp) / (t:ℚ))

lemma coeff_Psi (p : ℕ) (hp : p ≠ 0) (t : ℕ) :
    coeff (R:=ℚ) t (Psi p hp) = coeff (R:=ℚ) t (Bser p hp) / (t:ℚ) := by simp [Psi]

lemma Psi_ode (p : ℕ) (hp : p ≠ 0) :
    (X:ℚ⟦X⟧) * (d⁄dX ℚ) (Psi p hp) = Bser p hp := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_X, zero_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_Bser]
  | succ m =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_Psi]
    push_cast; field_simp

lemma Psi_val (p : ℕ) (hp : p.Prime) (t : ℕ) (ht : 1 ≤ t) :
    vpge p ((t.factorization p : ℤ) + 1) (coeff (R:=ℚ) t (Psi p hp.ne_zero)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [coeff_Psi, coeff_Bser_int]
  by_cases hB : Bcoe p t = 0
  · left; rw [hB]; simp
  · right
    have htne : (t:ℚ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
    have hBne : ((Bcoe p t : ℤ):ℚ) ≠ 0 := by exact_mod_cast hB
    rw [padicValRat.div hBne htne]
    have h1 : (2*(t.factorization p:ℤ)+1) ≤ padicValRat p ((Bcoe p t : ℤ):ℚ) := by
      have hv := vpge_of_dvd (Bcoe_dvd p hp t)
      rcases hv with h|h
      · exact absurd (by exact_mod_cast h) hB
      · rw [show (2*(t.factorization p:ℤ)+1) = ((2*(t.factorization p)+1:ℕ):ℤ) by push_cast; ring]
        exact h
    have h2 : padicValRat p ((t:ℕ):ℚ) = (t.factorization p:ℤ) := by
      rw [padicValRat.of_nat, Nat.factorization_def _ hp]
    rw [h2]; linarith

-- ===== closed form of Phi^M =====
lemma cc_Phi (p : ℕ) (hp : p ≠ 0) : PowerSeries.constantCoeff (bigPhi p hp) = 1 := by
  rw [bigPhi, map_mul, PowerSeries.constantCoeff_inv, cc_expand_Fs, map_pow, constantCoeff_Fs,
      one_pow, inv_one, one_mul]

lemma psi_pow_order (p : ℕ) (hp : p ≠ 0) (d t : ℕ) (h : t < d) :
    coeff (R:=ℚ) t (Psi p hp ^ d) = 0 := by
  have hX : (X:ℚ⟦X⟧) ∣ Psi p hp := by
    rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_Psi]; simp
  have : (X:ℚ⟦X⟧)^d ∣ Psi p hp ^ d := pow_dvd_pow_of_dvd hX d
  rw [PowerSeries.X_pow_dvd_iff] at this
  exact this t h

lemma phi_pow_ode (p : ℕ) (hp : p ≠ 0) (M : ℕ) :
    (X:ℚ⟦X⟧) * (d⁄dX ℚ) (bigPhi p hp ^ M) = (M:ℚ⟦X⟧) * Bser p hp * bigPhi p hp ^ M := by
  rcases Nat.eq_zero_or_pos M with h|h
  · subst h; simp
  · rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
    have h1 : (X:ℚ⟦X⟧) * ((M:ℚ⟦X⟧) * (bigPhi p hp ^ (M-1) * (d⁄dX ℚ) (bigPhi p hp)))
        = (M:ℚ⟦X⟧) * (bigPhi p hp ^ (M-1) * ((X:ℚ⟦X⟧) * (d⁄dX ℚ) (bigPhi p hp))) := by ring
    rw [h1, Phi_ode]
    have hpow : bigPhi p hp ^ (M-1) * bigPhi p hp = bigPhi p hp ^ M := by
      rw [← pow_succ]; congr 1; omega
    rw [show (M:ℚ⟦X⟧) * (bigPhi p hp ^ (M-1) * (Bser p hp * bigPhi p hp))
          = (M:ℚ⟦X⟧) * Bser p hp * (bigPhi p hp ^ (M-1) * bigPhi p hp) by ring, hpow]

lemma coeff_Bser_mul (p : ℕ) (hp : p ≠ 0) (g : ℚ⟦X⟧) (n : ℕ) :
    coeff (R:=ℚ) (n+1) (Bser p hp * g)
      = ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp) * coeff (n-m) g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ', coeff_zero_Bser]
  simp only [zero_mul, add_zero, Nat.succ_sub_succ]

lemma phiM_rec (p : ℕ) (hp : p ≠ 0) (M n : ℕ) :
    ((n+1:ℕ):ℚ) * coeff (n+1) (bigPhi p hp ^ M)
      = (M:ℚ) * ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp) * coeff (n-m) (bigPhi p hp ^ M) := by
  have h := congrArg (coeff (R:=ℚ) (n+1)) (phi_pow_ode p hp M)
  rw [coeff_succ_X_mul, coeff_derivative,
      mul_assoc, show ((M:ℚ⟦X⟧)) = PowerSeries.C (M:ℚ) by rw [map_natCast],
      PowerSeries.coeff_C_mul, coeff_Bser_mul] at h
  rw [← h]; push_cast; ring

lemma psid_ode (p : ℕ) (hp : p ≠ 0) (d : ℕ) :
    (X:ℚ⟦X⟧) * (d⁄dX ℚ) (Psi p hp ^ d) = (d:ℚ⟦X⟧) * (Bser p hp * Psi p hp ^ (d-1)) := by
  rcases Nat.eq_zero_or_pos d with h|h
  · subst h; simp
  · rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
    have h1 : (X:ℚ⟦X⟧) * ((d:ℚ⟦X⟧) * (Psi p hp ^ (d-1) * (d⁄dX ℚ) (Psi p hp)))
        = (d:ℚ⟦X⟧) * (Psi p hp ^ (d-1) * ((X:ℚ⟦X⟧) * (d⁄dX ℚ) (Psi p hp))) := by ring
    rw [h1, Psi_ode]; ring

lemma psid_rec (p : ℕ) (hp : p ≠ 0) (d n : ℕ) :
    ((n+1:ℕ):ℚ) * coeff (n+1) (Psi p hp ^ d)
      = (d:ℚ) * ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp) * coeff (n-m) (Psi p hp ^ (d-1)) := by
  have h := congrArg (coeff (R:=ℚ) (n+1)) (psid_ode p hp d)
  rw [coeff_succ_X_mul, coeff_derivative,
      show ((d:ℚ⟦X⟧)) = PowerSeries.C (d:ℚ) by rw [map_natCast],
      PowerSeries.coeff_C_mul, coeff_Bser_mul] at h
  rw [← h]; push_cast; ring

noncomputable def psiExp (p : ℕ) (hp : p ≠ 0) (M t : ℕ) : ℚ :=
  ∑ d ∈ range (t+1), (M:ℚ)^d / (d.factorial:ℚ) * coeff (R:=ℚ) t (Psi p hp ^ d)

lemma clForm_rec (p : ℕ) (hp : p ≠ 0) (M n : ℕ) :
    ((n+1:ℕ):ℚ) * psiExp p hp M (n+1)
      = (M:ℚ) * ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp) * psiExp p hp M (n-m) := by
  calc ((n+1:ℕ):ℚ) * psiExp p hp M (n+1)
      = ∑ d ∈ range (n+2), (M:ℚ)^d/(d.factorial:ℚ)
          * (((n+1:ℕ):ℚ) * coeff (n+1) (Psi p hp ^ d)) := by
        rw [psiExp, Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring
    _ = ∑ d ∈ range (n+2), (M:ℚ)^d/(d.factorial:ℚ)
          * ((d:ℚ) * ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp)
                * coeff (n-m) (Psi p hp ^ (d-1))) := by
        apply Finset.sum_congr rfl; intro d _; rw [psid_rec p hp d n]
    _ = ∑ e ∈ range (n+1), (M:ℚ)^(e+1)/(e.factorial:ℚ)
          * ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp) * coeff (n-m) (Psi p hp ^ e) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.factorial_zero, Nat.cast_zero, pow_zero, mul_zero, zero_mul, add_zero,
          Nat.cast_one, Nat.add_sub_cancel]
        apply Finset.sum_congr rfl; intro e _
        have hfe : (e.factorial:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero e)
        have hse : ((e+1:ℕ):ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero e)
        rw [Nat.factorial_succ]
        push_cast
        field_simp
    _ = ∑ e ∈ range (n+1), ∑ m ∈ range (n+1),
          (M:ℚ)^(e+1)/(e.factorial:ℚ) * (coeff (m+1) (Bser p hp) * coeff (n-m) (Psi p hp ^ e)) := by
        apply Finset.sum_congr rfl; intro e _; rw [Finset.mul_sum]
    _ = ∑ m ∈ range (n+1), ∑ e ∈ range (n+1),
          (M:ℚ)^(e+1)/(e.factorial:ℚ) * (coeff (m+1) (Bser p hp) * coeff (n-m) (Psi p hp ^ e)) :=
        Finset.sum_comm
    _ = ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp)
          * ((M:ℚ) * ∑ e ∈ range (n+1), (M:ℚ)^e/(e.factorial:ℚ) * coeff (n-m) (Psi p hp ^ e)) := by
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _; ring
    _ = ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp) * ((M:ℚ) * psiExp p hp M (n-m)) := by
        apply Finset.sum_congr rfl; intro m hm
        have hpsi : (M:ℚ) * ∑ e ∈ range (n+1), (M:ℚ)^e/(e.factorial:ℚ) * coeff (n-m) (Psi p hp ^ e)
                  = (M:ℚ) * psiExp p hp M (n-m) := by
          congr 1
          rw [psiExp]
          have hsub : range (n-m+1) ⊆ range (n+1) := by
            intro x hx; rw [Finset.mem_range] at hx ⊢; omega
          refine (Finset.sum_subset hsub ?_).symm
          intro e hmem he
          rw [Finset.mem_range, not_lt] at he
          have hlt : n - m < e := by omega
          rw [psi_pow_order p hp e (n-m) hlt, mul_zero]
        rw [hpsi]
    _ = (M:ℚ) * ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp) * psiExp p hp M (n-m) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring

lemma closed_form (p : ℕ) (hp : p ≠ 0) (M : ℕ) :
    ∀ t, coeff (R:=ℚ) t (bigPhi p hp ^ M) = psiExp p hp M t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    match t with
    | 0 =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, cc_Phi, one_pow]
      rw [psiExp]
      simp
    | (n+1) =>
      have hrec1 := phiM_rec p hp M n
      have hrec2 := clForm_rec p hp M n
      have hsum : ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp) * coeff (n-m) (bigPhi p hp ^ M)
                = ∑ m ∈ range (n+1), coeff (m+1) (Bser p hp) * psiExp p hp M (n-m) := by
        apply Finset.sum_congr rfl; intro m hm
        rw [Finset.mem_range] at hm
        rw [ih (n-m) (by omega)]
      have key : ((n+1:ℕ):ℚ) * coeff (n+1) (bigPhi p hp ^ M)
               = ((n+1:ℕ):ℚ) * psiExp p hp M (n+1) := by
        rw [hrec1, hrec2, hsum]
      have hne : ((n+1:ℕ):ℚ) ≠ 0 := by positivity
      exact mul_left_cancel₀ hne key

-- ===== valuation of powers of Psi and factorial =====
lemma psi_val1 (p : ℕ) (hp : p.Prime) (i : ℕ) :
    vpge p 1 (coeff (R:=ℚ) i (Psi p hp.ne_zero)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos i with h|h
  · subst h; left; rw [coeff_Psi]; simp
  · exact vpge_mono (Psi_val p hp i h) (by omega)

lemma psi_pow_val (p : ℕ) (hp : p.Prime) :
    ∀ (d t : ℕ), vpge p (d:ℤ) (coeff (R:=ℚ) t (Psi p hp.ne_zero ^ d)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro d
  induction d with
  | zero =>
    intro t; rw [pow_zero, PowerSeries.coeff_one]
    by_cases h : t = 0
    · rw [if_pos h]; simpa using vpge_of_dvd (k:=0) (m:=(1:ℤ)) (by simp)
    · rw [if_neg h]; exact vpge_zero p 0
  | succ d ih =>
    intro t
    rw [pow_succ, mul_comm, PowerSeries.coeff_mul,
        show ((d+1:ℕ):ℤ) = 1 + (d:ℤ) by push_cast; ring]
    apply vpge_sum
    intro x _
    exact vpge_mul (psi_val1 p hp x.1) (ih x.2)

lemma vp_factorial_le (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (d : ℕ) (hd : 2 ≤ d) :
    padicValNat p d.factorial ≤ d - 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := sub_one_mul_padicValNat_factorial (p:=p) d
  have hds : 1 ≤ (p.digits d).sum := by
    have hne : p.digits d ≠ [] := by
      rw [Nat.digits_ne_nil_iff_ne_zero]; omega
    have hlast : (p.digits d).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero p (by omega)
    have hmem : (p.digits d).getLast hne ∈ p.digits d := List.getLast_mem hne
    have : (p.digits d).getLast hne ≤ (p.digits d).sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    omega
  have h2 : 2 * padicValNat p d.factorial ≤ (p-1) * padicValNat p d.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  set Y := (p-1) * padicValNat p d.factorial with hY
  omega

lemma vpge_div_nat {p : ℕ} [Fact p.Prime] {cnum cden : ℤ} {num : ℚ} {den : ℕ}
    (hden0 : den ≠ 0) (hnum : vpge p cnum num) (hden : (den.factorization p : ℤ) ≤ cden) :
    vpge p (cnum - cden) (num / (den:ℚ)) := by
  rcases hnum with h|h
  · left; rw [h, zero_div]
  · by_cases hnum0 : num = 0
    · left; rw [hnum0, zero_div]
    · right
      have hd : (den:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hden0
      rw [padicValRat.div hnum0 hd]
      have hval : padicValRat p (den:ℚ) = (den.factorization p:ℤ) := by
        rw [padicValRat.of_nat, Nat.factorization_def _ (Fact.out)]
      rw [hval]; linarith

lemma vpge_Mpow (p : ℕ) (hp : p.Prime) (M d : ℕ) :
    vpge p ((d:ℤ) * (M.factorization p)) ((M:ℚ)^d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpw : (p:ℤ)^(M.factorization p) ∣ (M:ℤ) := by
    have := Nat.ordProj_dvd M p
    have h2 : (p^(M.factorization p) : ℕ) ∣ M := Nat.ordProj_dvd M p
    exact_mod_cast h2
  have hdvd : (p:ℤ)^(d * M.factorization p) ∣ (M:ℤ)^d := by
    rw [mul_comm, pow_mul]
    exact pow_dvd_pow_of_dvd hpw d
  have hv := vpge_of_dvd (k := d * M.factorization p) (m := (M:ℤ)^d) hdvd
  rw [show ((d:ℤ) * (M.factorization p)) = ((d * M.factorization p : ℕ):ℤ) by push_cast; ring]
  have : (((M:ℤ)^d : ℤ):ℚ) = (M:ℚ)^d := by push_cast; ring
  rwa [this] at hv

-- ===== R = Phi^M - 1 - M*Psi and its valuation =====
noncomputable def Rser (p : ℕ) (hp : p ≠ 0) (M : ℕ) : ℚ⟦X⟧ :=
  bigPhi p hp ^ M - 1 - (M:ℚ⟦X⟧) * Psi p hp

lemma Rval (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (M b : ℕ) :
    vpge p (2*(M.factorization p) + 2 : ℤ) (coeff (R:=ℚ) b (Rser p hp.ne_zero M)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have h0 : coeff (R:=ℚ) 0 (Rser p hp.ne_zero M) = 0 := by
      rw [Rser, map_sub, map_sub, PowerSeries.coeff_zero_eq_constantCoeff, map_pow, cc_Phi, one_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_one, if_pos rfl,
          show (M:ℚ⟦X⟧) = PowerSeries.C (M:ℚ) by rw [map_natCast], PowerSeries.coeff_C_mul,
          coeff_Psi]
      simp
    rw [h0]; exact vpge_zero p _
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b-1, by omega⟩
    have hpeel : coeff (R:=ℚ) (c+1) (Rser p hp.ne_zero M)
        = ∑ j ∈ range c, (M:ℚ)^(j+1+1)/((j+1+1).factorial:ℚ)
              * coeff (c+1) (Psi p hp.ne_zero ^ (j+1+1)) := by
      rw [Rser, map_sub, map_sub, closed_form p hp.ne_zero M (c+1), psiExp,
          show (M:ℚ⟦X⟧) = PowerSeries.C (M:ℚ) by rw [map_natCast], PowerSeries.coeff_C_mul]
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
        one_mul, div_one, zero_add]
      rw [PowerSeries.coeff_one, if_neg (by omega : ¬ (c+1 = 0))]
      ring
    rw [hpeel]
    apply vpge_sum
    intro j _
    rw [div_mul_eq_mul_div]
    have hnum : vpge p ((↑(j+1+1):ℤ)*(M.factorization p) + ↑(j+1+1))
        ((M:ℚ)^(j+1+1) * coeff (c+1) (Psi p hp.ne_zero ^ (j+1+1))) :=
      vpge_mul (vpge_Mpow p hp M (j+1+1)) (psi_pow_val p hp (j+1+1) (c+1))
    have hle : ((((j+1+1).factorial).factorization p : ℤ)) ≤ (((j+1+1)-2 : ℕ):ℤ) := by
      rw [Nat.factorization_def _ hp]
      exact_mod_cast vp_factorial_le p hp hp3 (j+1+1) (by omega)
    have hdiv := vpge_div_nat (den := (j+1+1).factorial) (Nat.factorial_ne_zero _) hnum hle
    refine vpge_mono hdiv ?_
    have h2d : (2:ℤ) ≤ (↑(j+1+1):ℤ) := by exact_mod_cast (by omega : 2 ≤ j+1+1)
    have hcast : (((j+1+1)-2 : ℕ):ℤ) = (↑(j+1+1):ℤ) - 2 := by omega
    rw [hcast]
    have hmul : (2:ℤ) * (M.factorization p) ≤ (↑(j+1+1):ℤ) * (M.factorization p) :=
      mul_le_mul_of_nonneg_right h2d (by positivity)
    linarith

-- ===== valuation of cM =====
lemma vpge_natCast {p : ℕ} [Fact p.Prime] (n : ℕ) : vpge p 0 (n:ℚ) := by
  rw [show ((n:ℕ):ℚ) = (((n:ℤ)):ℚ) by push_cast; ring]
  exact vpge_intCast (n:ℤ)

lemma cM_val (p : ℕ) (hp : p.Prime) (M ℓ : ℕ) (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ) :
    vpge p ((M.factorization p:ℤ) - ℓ.factorization p) (cM M ℓ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n+1 := ⟨ℓ-1, by omega⟩
  have hrec := cM_rec M n hM
  set S := ∑ m ∈ range (n+1), ((σ 2 (m+1):ℕ):ℚ) * cM M (n-m) with hSdef
  have hpwM : (p:ℤ)^(M.factorization p) ∣ (M:ℤ) := by exact_mod_cast Nat.ordProj_dvd M p
  have hSval : vpge p 0 S := by
    rw [hSdef]; apply vpge_sum; intro m _
    obtain ⟨zc, hzc⟩ := cM_int M (n-m)
    rw [hzc]
    have h := vpge_mul (vpge_natCast (p := p) (σ 2 (m+1))) (vpge_intCast (p := p) zc)
    rwa [add_zero] at h
  have hMval : vpge p (M.factorization p:ℤ) (-(M:ℚ)) := by
    rw [show (-(M:ℚ)) = ((-(M:ℤ)):ℚ) by push_cast; ring]
    exact vpge_of_dvd ((dvd_neg).mpr hpwM)
  have hnum : vpge p (M.factorization p:ℤ) (-(M:ℚ) * S) := by
    have h := vpge_mul hMval hSval
    rwa [add_zero] at h
  have hcm : cM M (n+1) = (-(M:ℚ) * S)/((n+1:ℕ):ℚ) := by
    rw [eq_div_iff (by positivity : ((n+1:ℕ):ℚ) ≠ 0), mul_comm, hrec]
  rw [hcm]
  exact vpge_div_nat (den := n+1) (by omega) hnum (le_refl _)

-- ===== term bound (ultrametric) =====
lemma term_bound (p : ℕ) (hp : p.Prime) (M a b : ℕ) (hM : 1 ≤ M) (hab : a + b = M * p) :
    vpge p ((M.factorization p:ℤ)+2)
      (coeff (R:=ℚ) a (PowerSeries.expand p hp.ne_zero (Fs^M)) * coeff (R:=ℚ) b (Psi p hp.ne_zero)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpa : p ∣ a
  · obtain ⟨ℓ, rfl⟩ := hpa
    have hexa : coeff (R:=ℚ) (p*ℓ) (PowerSeries.expand p hp.ne_zero (Fs^M)) = cM M ℓ := by
      rw [PowerSeries.coeff_expand_mul]; rfl
    rw [hexa]
    have hcomm : M*p = p*M := mul_comm M p
    have hℓM : ℓ ≤ M := by
      have h1 : p*ℓ ≤ p*M := by omega
      exact Nat.le_of_mul_le_mul_left h1 hp.pos
    have hbval : b = p*(M-ℓ) := by
      have hdist : p*(M-ℓ)+p*ℓ = p*M := by rw [← Nat.mul_add]; congr 1; omega
      omega
    by_cases hb0 : b = 0
    · rw [hb0, show coeff (R:=ℚ) 0 (Psi p hp.ne_zero) = 0 from by rw [coeff_Psi]; simp, mul_zero]
      exact vpge_zero p _
    · have hb1 : 1 ≤ b := by omega
      have hMℓ1 : 1 ≤ M - ℓ := by
        rcases Nat.eq_zero_or_pos (M-ℓ) with h|h
        · rw [h, mul_zero] at hbval; omega
        · exact h
      have hfacb : b.factorization p = (M-ℓ).factorization p + 1 := by
        rw [hbval, Nat.factorization_mul hp.pos.ne' (by omega), Finsupp.add_apply,
            hp.factorization_self]; omega
      have hpsib := Psi_val p hp b hb1
      by_cases hbig : M.factorization p ≤ (M-ℓ).factorization p
      · obtain ⟨z, hz⟩ := cM_int M ℓ
        rw [hz]
        have hmul := vpge_mul (vpge_intCast (p := p) z) hpsib
        refine vpge_mono hmul ?_
        rw [hfacb]
        have hbb : (M.factorization p:ℤ) ≤ (M-ℓ).factorization p := by exact_mod_cast hbig
        push_cast
        omega
      · have hℓ1 : 1 ≤ ℓ := by
          by_contra hc
          push_neg at hc
          rw [show ℓ = 0 by omega, Nat.sub_zero] at hbig
          exact hbig (le_refl _)
        have heq : ℓ.factorization p = (M-ℓ).factorization p := by
          have hMne : M ≠ 0 := by omega
          have hℓne : ℓ ≠ 0 := by omega
          have hMℓne : M - ℓ ≠ 0 := by omega
          have hd1 : p^((M-ℓ).factorization p) ∣ M :=
            (Nat.Prime.pow_dvd_iff_le_factorization hp hMne).mpr (by omega)
          have hd2 : p^((M-ℓ).factorization p) ∣ (M-ℓ) :=
            (Nat.Prime.pow_dvd_iff_le_factorization hp hMℓne).mpr (le_refl _)
          have hd3 : p^((M-ℓ).factorization p) ∣ ℓ := by
            have hsub : p^((M-ℓ).factorization p) ∣ M - (M-ℓ) := Nat.dvd_sub hd1 hd2
            rwa [Nat.sub_sub_self hℓM] at hsub
          have hle1 : (M-ℓ).factorization p ≤ ℓ.factorization p :=
            (Nat.Prime.pow_dvd_iff_le_factorization hp hℓne).mp hd3
          have hle2 : ℓ.factorization p ≤ (M-ℓ).factorization p := by
            by_contra hc2
            push_neg at hc2
            have h4 : p^((M-ℓ).factorization p + 1) ∣ ℓ :=
              (Nat.Prime.pow_dvd_iff_le_factorization hp hℓne).mpr (by omega)
            have h5 : p^((M-ℓ).factorization p + 1) ∣ M :=
              (Nat.Prime.pow_dvd_iff_le_factorization hp hMne).mpr (by omega)
            have h6 : p^((M-ℓ).factorization p + 1) ∣ (M-ℓ) := Nat.dvd_sub h5 h4
            have := (Nat.Prime.pow_dvd_iff_le_factorization hp hMℓne).mp h6
            omega
          omega
        have hcm := cM_val p hp M ℓ hM hℓ1
        have hmul := vpge_mul hcm hpsib
        refine vpge_mono hmul ?_
        rw [hfacb]
        have heqz : (ℓ.factorization p:ℤ) = (M-ℓ).factorization p := by exact_mod_cast heq
        push_cast
        omega
  · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hpa, zero_mul]
    exact vpge_zero p _

-- ===== reduced claim and main theorem =====
lemma RC (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (M : ℕ) (hM : 1 ≤ M) :
    (p:ℤ)^(2*(M.factorization p)+2) ∣ (aa (M*p) - aa M : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAMp : ((aa (M*p):ℤ):ℚ)
      = coeff (M*p) (PowerSeries.expand p hp.ne_zero (Fs^M) * bigPhi p hp.ne_zero ^ M) := by
    rw [a_eq (M*p), Fs_pow_mul p hp.ne_zero M]
  have hAM : ((aa M:ℤ):ℚ) = coeff (M*p) (PowerSeries.expand p hp.ne_zero (Fs^M)) := by
    rw [a_eq M, mul_comm M p, PowerSeries.coeff_expand_mul]
  have hfinal : ((aa (M*p):ℤ):ℚ) - ((aa M:ℤ):ℚ)
      = coeff (M*p) (PowerSeries.expand p hp.ne_zero (Fs^M) * Rser p hp.ne_zero M)
        + (M:ℚ) * coeff (M*p) (PowerSeries.expand p hp.ne_zero (Fs^M) * Psi p hp.ne_zero) := by
    rw [hAMp, hAM, ← map_sub]
    have hexpand : PowerSeries.expand p hp.ne_zero (Fs^M) * bigPhi p hp.ne_zero ^ M
        - PowerSeries.expand p hp.ne_zero (Fs^M)
        = PowerSeries.expand p hp.ne_zero (Fs^M) * Rser p hp.ne_zero M
          + PowerSeries.expand p hp.ne_zero (Fs^M) * ((M:ℚ⟦X⟧) * Psi p hp.ne_zero) := by
      rw [Rser]; ring
    rw [hexpand, map_add]
    congr 1
    rw [show PowerSeries.expand p hp.ne_zero (Fs^M) * ((M:ℚ⟦X⟧) * Psi p hp.ne_zero)
          = (M:ℚ⟦X⟧) * (PowerSeries.expand p hp.ne_zero (Fs^M) * Psi p hp.ne_zero) by ring,
        show (M:ℚ⟦X⟧) = PowerSeries.C (M:ℚ) by rw [map_natCast], PowerSeries.coeff_C_mul]
  have hexval : ∀ a, vpge p 0 (coeff (R:=ℚ) a (PowerSeries.expand p hp.ne_zero (Fs^M))) := by
    intro a
    rw [PowerSeries.coeff_expand]
    by_cases hpa : p ∣ a
    · rw [if_pos hpa]
      obtain ⟨z, hz⟩ := cM_int M (a/p)
      rw [show coeff (R:=ℚ) (a/p) (Fs^M) = cM M (a/p) from rfl, hz]
      exact vpge_intCast z
    · rw [if_neg hpa]; exact vpge_zero p 0
  have hPartB : vpge p (2*(M.factorization p)+2:ℤ)
      (coeff (M*p) (PowerSeries.expand p hp.ne_zero (Fs^M) * Rser p hp.ne_zero M)) := by
    rw [PowerSeries.coeff_mul]
    apply vpge_sum
    intro x _
    have h := vpge_mul (hexval x.1) (Rval p hp hp3 M x.2)
    rwa [zero_add] at h
  have hPartAc : vpge p ((M.factorization p:ℤ)+2)
      (coeff (M*p) (PowerSeries.expand p hp.ne_zero (Fs^M) * Psi p hp.ne_zero)) := by
    rw [PowerSeries.coeff_mul]
    apply vpge_sum
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    exact term_bound p hp M x.1 x.2 hM hx
  have hMval : vpge p (M.factorization p:ℤ) ((M:ℚ)) := by
    rw [show ((M:ℚ)) = ((M:ℤ):ℚ) by push_cast; ring]
    exact vpge_of_dvd (by exact_mod_cast Nat.ordProj_dvd M p)
  have hfinval : vpge p (2*(M.factorization p)+2:ℤ) (((aa (M*p):ℤ):ℚ) - ((aa M:ℤ):ℚ)) := by
    rw [hfinal]
    refine vpge_add hPartB ?_
    have h := vpge_mul hMval hPartAc
    have he : (M.factorization p:ℤ) + ((M.factorization p:ℤ)+2) = 2*(M.factorization p)+2 := by ring
    rwa [he] at h
  have hv : vpge p (2*(M.factorization p)+2:ℤ) (((aa (M*p) - aa M : ℤ)):ℚ) := by
    rw [show (((aa (M*p) - aa M:ℤ)):ℚ) = ((aa (M*p):ℤ):ℚ) - ((aa M:ℤ):ℚ) by push_cast; ring]
    exact hfinval
  have hd := vpge_int (c := (2*(M.factorization p)+2:ℤ)) (by positivity) hv
  rwa [show ((2*(M.factorization p)+2:ℤ)).toNat = 2*(M.factorization p)+2 by omega] at hd

theorem main_thm (p n k : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    aa (n * p ^ k) ≡ aa (n * p ^ (k - 1)) [ZMOD ((p ^ (2 * k) : ℕ) : ℤ)] := by
  set M := n * p^(k-1) with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]; exact Nat.mul_pos (by omega) (pow_pos hp.pos (k-1))
  have hMp : M * p = n * p^k := by
    rw [hMdef, mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]
  have hw : k - 1 ≤ M.factorization p := by
    rw [hMdef, Nat.factorization_mul (by omega) (pow_ne_zero _ hp.pos.ne'),
        Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self,
        smul_eq_mul]
    omega
  have hdvd := RC p hp hp3 M hM1
  have hpow : (p:ℤ)^(2*k) ∣ (p:ℤ)^(2*(M.factorization p)+2) := by
    apply pow_dvd_pow; omega
  have hdvd2 : (p:ℤ)^(2*k) ∣ (aa (M*p) - aa M : ℤ) := dvd_trans hpow hdvd
  rw [Int.modEq_iff_dvd, show (((p^(2*k):ℕ)):ℤ) = (p:ℤ)^(2*k) by push_cast; ring]
  rw [hMp] at hdvd2
  exact (dvd_sub_comm).mp hdvd2

/--
Conjecture: the stronger supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k)) hold for all primes p >= 3 and all positive integers n and k.
-/
theorem oeis_281267_conjecture_0 (p : ℕ) (n k : ℕ) :
  Nat.Prime p → 3 ≤ p → 1 ≤ n → 1 ≤ k →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD ((p ^ (2 * k) : ℕ) : ℤ)] :=
by
  intro hp hp3 hn hk
  exact main_thm p n k hp hp3 hn hk
