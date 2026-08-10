import FormalConjectures.Util.ProblemImports

section EngineSection
open Finset Complex
open scoped Real

noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / n)

lemma zeta_pow_n (n : ℕ) (hn : 0 < n) : (zeta n) ^ n = 1 := by
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [zeta, ← Complex.exp_nat_mul,
    show (n:ℂ) * (2 * Real.pi * I / n) = (2 * Real.pi * I / n) * n by ring,
    div_mul_cancel₀ _ hnc, Complex.exp_two_pi_mul_I]

noncomputable def gs (n : ℕ) (t : ℤ) : ℂ := ∑ k ∈ range n, zeta n ^ (t * (k:ℤ) ^ 2)

-- reindex range n sum over ZMod n
lemma sum_zmod_eq_range (p : ℕ) [NeZero p] (f : ZMod p → ℂ) :
    ∑ x : ZMod p, f x = ∑ k ∈ range p, f (k : ZMod p) := by
  apply Finset.sum_bij (fun (x : ZMod p) _ => x.val)
  · intro x _; simp [ZMod.val_lt]
  · intro x _ y _ h; simpa using ZMod.val_injective p h
  · intro k hk; exact ⟨(k : ZMod p), Finset.mem_univ _, by
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)]⟩
  · intro x _; rw [ZMod.natCast_val, ZMod.cast_id]

-- zeta p ^ (m : ℤ) depends only on m mod p
lemma zeta_zpow_val (p : ℕ) [NeZero p] (m : ℤ) :
    zeta p ^ m = zeta p ^ ((m : ZMod p).val) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  set v : ℕ := (m : ZMod p).val with hvdef
  have hcong : (v : ℤ) ≡ m [ZMOD (p:ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_natCast, hvdef]
    exact ZMod.natCast_rightInverse _
  obtain ⟨c, hc⟩ := (Int.modEq_iff_dvd.mp hcong)
  have hpval : zeta p ^ p = 1 := zeta_pow_n p hp
  have hzne : zeta p ≠ 0 := by simp only [zeta, ne_eq]; exact Complex.exp_ne_zero _
  have hm : m = (v : ℤ) + p * c := by linarith [hc]
  rw [hm, zpow_add₀ hzne, zpow_natCast, zpow_mul, zpow_natCast, hpval, one_zpow, mul_one]

noncomputable def psiC (p : ℕ) [NeZero p] : AddChar (ZMod p) ℂ :=
  AddChar.zmodChar p (zeta_pow_n p (Nat.pos_of_ne_zero (NeZero.ne p)))

lemma psiC_apply (p : ℕ) [NeZero p] (a : ZMod p) :
    psiC p a = zeta p ^ a.val := by
  simp [psiC, AddChar.zmodChar_apply]

-- bridge: gs p t = ∑_{x : ZMod p} ψ (↑t * x^2)
lemma gs_eq_sum (p : ℕ) [NeZero p] (t : ℤ) :
    gs p t = ∑ x : ZMod p, psiC p ((t : ZMod p) * x ^ 2) := by
  rw [sum_zmod_eq_range]
  unfold gs
  apply Finset.sum_congr rfl
  intro k hk
  have hcast : ((t * (k:ℤ)^2 : ℤ) : ZMod p) = (t : ZMod p) * (k:ZMod p)^2 := by
    push_cast; ring
  rw [psiC_apply, zeta_zpow_val p (t * (k:ℤ)^2), hcast]

open AddChar in
/-- Sum over x of ψ(c x²) equals the Gauss sum of the quadratic character. -/
lemma sum_psi_sq_eq_gaussSum (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (c : ZMod p) (hc : c ≠ 0) :
    ∑ x : ZMod p, psiC p (c * x ^ 2)
      = gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
          (mulShift (psiC p) c) := by
  have hrc : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp2
  set χℂ : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) with hχℂ
  -- group the sum by value of x^2
  rw [← Finset.sum_fiberwise (g := fun x : ZMod p => x ^ 2)
        (f := fun x : ZMod p => psiC p (c * x ^ 2))]
  -- inner sum is constant
  have step : ∀ y : ZMod p,
      (∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = y), psiC p (c * x ^ 2))
        = (χℂ y + 1) * (mulShift (psiC p) c y) := by
    intro y
    have hset : Finset.univ.filter (fun x : ZMod p => x ^ 2 = y) = {x | x ^ 2 = y}.toFinset := by
      ext x; simp [Set.mem_toFinset]
    have hcard : ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℤ)
        = quadraticChar (ZMod p) y + 1 := by
      rw [hset]; exact_mod_cast quadraticChar_card_sqrts hrc y
    have hconst : ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = y), psiC p (c * x ^ 2)
        = ∑ _x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = y), psiC p (c * y) := by
      apply Finset.sum_congr rfl; intro x hx; rw [Finset.mem_filter] at hx; rw [hx.2]
    rw [hconst, Finset.sum_const, nsmul_eq_mul, mulShift_apply]
    congr 1
    rw [hχℂ, MulChar.ringHomComp_apply, Int.coe_castRingHom]
    have hc2 : ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℂ)
        = ((quadraticChar (ZMod p) y : ℤ) : ℂ) + 1 := by
      exact_mod_cast hcard
    rw [hc2]
  simp_rw [step]
  -- expand: ∑ (χ y + 1)·ψ(cy) = gaussSum + ∑ ψ(cy)
  rw [gaussSum]
  rw [Finset.sum_congr rfl (fun y _ => by ring :
    ∀ y ∈ Finset.univ, (χℂ y + 1) * (mulShift (psiC p) c y)
      = χℂ y * (mulShift (psiC p) c y) + (mulShift (psiC p) c y))]
  rw [Finset.sum_add_distrib]
  have hprim : (psiC p).IsPrimitive := by
    have hpr : IsPrimitiveRoot (zeta p) p := by
      have := Complex.isPrimitiveRoot_exp p (NeZero.ne p)
      simpa only [zeta] using this
    exact AddChar.zmodChar_primitive_of_primitive_root p hpr
  have hzero : ∑ y : ZMod p, (mulShift (psiC p) c y) = 0 := by
    apply AddChar.sum_eq_zero_of_ne_one
    exact hprim hc
  rw [hzero, add_zero]

/-- gs p 1 as a Gauss sum. -/
lemma gs_one_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    gs p 1 = gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (psiC p) := by
  rw [gs_eq_sum p 1]
  have : ((1 : ℤ) : ZMod p) = 1 := by norm_num
  rw [this]
  rw [sum_psi_sq_eq_gaussSum p hp2 1 one_ne_zero]
  rw [AddChar.mulShift_one]

/-- Prime character property: gs p t = χ(t) · gs p 1 for t coprime to p. -/
lemma gs_char_prime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (t : ℤ)
    (ht : IsUnit (t : ZMod p)) :
    gs p t = ((quadraticChar (ZMod p) (t : ZMod p) : ℤ) : ℂ) * gs p 1 := by
  set χℂ : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) with hχℂ
  obtain ⟨u, hu⟩ := ht
  have hgst : gs p t = gaussSum χℂ (AddChar.mulShift (psiC p) (t : ZMod p)) := by
    rw [gs_eq_sum p t, sum_psi_sq_eq_gaussSum p hp2 (t : ZMod p) ?_]
    rw [← hu]; exact u.ne_zero
  have hshift := gaussSum_mulShift χℂ (psiC p) u
  rw [hu] at hshift
  -- hshift : χℂ ↑t * gaussSum χℂ (mulShift (psiC p) ↑t) = gaussSum χℂ (psiC p)
  rw [← hgst, ← gs_one_eq p hp2] at hshift
  -- hshift : χℂ ↑t * gs p t = gs p 1
  have htne : (t : ZMod p) ≠ 0 := by rw [← hu]; exact u.ne_zero
  have hval : χℂ (t : ZMod p) = (((quadraticChar (ZMod p) (t : ZMod p)) : ℤ) : ℂ) := by
    rw [hχℂ, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  have hquad : χℂ (t : ZMod p) * χℂ (t : ZMod p) = 1 := by
    rcases quadraticChar_isQuadratic (ZMod p) (t : ZMod p) with h0 | h1 | hm1
    · exact absurd ((quadraticChar_eq_zero_iff).mp h0) htne
    · rw [hval, h1]; norm_num
    · rw [hval, hm1]; norm_num
  rw [← hval]
  -- from hshift: χℂ↑t * gs p t = gs p 1, multiply by χℂ↑t
  have hc := congrArg (fun z => χℂ (t : ZMod p) * z) hshift
  simp only at hc
  rw [← mul_assoc, hquad, one_mul] at hc
  exact hc




-- ===== recursion lemmas =====
lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := by
  simp only [zeta, ne_eq]; exact Complex.exp_ne_zero _
-- zeta (p^k) ^ (p^(k-1)) = zeta p   (when written appropriately)
-- We'll need: zeta N ^ d = zeta (N/d) when d ∣ N
lemma zeta_pow_div (N d : ℕ) (hd : d ∣ N) (hd0 : 0 < d) :
    zeta N ^ d = zeta (N / d) := by
  obtain ⟨q, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left q hd0]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp [zeta]
  · rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    have hdc : (d:ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hqc : (q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hdq : ((d * q : ℕ) : ℂ) = (d:ℂ) * (q:ℂ) := by push_cast; ring
    rw [hdq]
    field_simp

-- reindex range (A*p) by (a,c) ↦ a + A*c
lemma sum_range_mul_reindex (A p : ℕ) (hA : 0 < A) (f : ℕ → ℂ) :
    ∑ j ∈ range (A * p), f j = ∑ a ∈ range A, ∑ c ∈ range p, f (a + A * c) := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun j => (j % A, j / A)) (fun ac => ac.1 + A * ac.2)
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hA, ?_⟩
    exact Nat.div_lt_of_lt_mul hj
  · intro ac hac
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hac
    rw [Finset.mem_range]
    calc ac.1 + A * ac.2 < A + A * ac.2 := by omega
      _ ≤ A * p := by
          have : A + A * ac.2 = A * (ac.2 + 1) := by ring
          rw [this]; exact Nat.mul_le_mul_left A hac.2
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.mod_add_div]
  · intro ac hac
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hac
    have h1 : (ac.1 + A * ac.2) % A = ac.1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hac.1]
    have h2 : (ac.1 + A * ac.2) / A = ac.2 := by
      rw [Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt hac.1, zero_add]
    rw [Prod.ext_iff]; exact ⟨h1, h2⟩
  · intro j _; simp only []; congr 1; exact (Nat.mod_add_div j A).symm

-- geometric: sum over range p of r^c, r^p = 1
lemma geom_root_sum (p : ℕ) (hp : 0 < p) (r : ℂ) (hr : r ^ p = 1) :
    ∑ c ∈ range p, r ^ c = if r = 1 then (p : ℂ) else 0 := by
  by_cases h1 : r = 1
  · simp [h1]
  · rw [if_neg h1, geom_sum_eq h1, hr]; simp

-- main recursion
lemma gs_ppow_rec (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) (t : ℤ)
    (ht : ¬ (p : ℤ) ∣ t) :
    gs (p ^ k) t = (p : ℂ) * gs (p ^ (k - 2)) t := by
  obtain ⟨e, rfl⟩ : ∃ e, k = e + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hp0 : 0 < p := hp.pos
  set N := p ^ (e + 2) with hN
  set A := p ^ (e + 1) with hA
  set m := p ^ e with hm
  have hNeq : N = A * p := by rw [hN, hA]; ring
  have hAeq : A = p * m := by rw [hA, hm]; ring
  have hAm : A = m * p := by rw [hAeq]; ring
  have hzN : zeta N ≠ 0 := zeta_ne_zero N
  have hzp : zeta p ≠ 0 := zeta_ne_zero p
  -- zeta N ^ A = zeta p
  have hNA : zeta N ^ A = zeta p := by
    have hdvd : A ∣ N := ⟨p, hNeq⟩
    have := zeta_pow_div N A hdvd (by positivity)
    rwa [show N / A = p by rw [hNeq]; exact Nat.mul_div_cancel_left p (by positivity)] at this
  -- zeta N ^ (p^2) = zeta m
  have hNp2 : zeta N ^ (p ^ 2) = zeta m := by
    have hdvd : p ^ 2 ∣ N := ⟨m, by rw [hN, hm]; ring⟩
    have := zeta_pow_div N (p ^ 2) hdvd (by positivity)
    rwa [show N / p ^ 2 = m by rw [hN, hm]; rw [show e + 2 = 2 + e by ring, pow_add,
      Nat.mul_div_cancel_left _ (by positivity)]] at this
  -- main: rewrite gs and reindex
  unfold gs
  rw [show range N = range (A * p) by rw [hNeq],
    sum_range_mul_reindex A p (by rw [hA]; exact pow_pos hp0 _)]
  -- per-term simplification
  have key : ∀ a ∈ range A, ∀ c ∈ range p,
      zeta N ^ (t * ((a + A * c : ℕ) : ℤ) ^ 2)
        = zeta N ^ (t * (a : ℤ) ^ 2) * (zeta p ^ (2 * t * (a : ℤ))) ^ c := by
    intro a _ c _
    rw [show ((a + A * c : ℕ) : ℤ) = (a : ℤ) + (A : ℤ) * (c : ℤ) by push_cast; ring]
    have hexp : t * ((a : ℤ) + (A : ℤ) * (c : ℤ)) ^ 2
        = t * (a : ℤ) ^ 2 + (A : ℤ) * (2 * t * (a : ℤ) * (c : ℤ))
          + (N : ℤ) * (t * (m : ℤ) * (c : ℤ) ^ 2) := by
      have : (A : ℤ) ^ 2 = (N : ℤ) * (m : ℤ) := by
        rw [hAm]; push_cast; rw [hNeq, hAm]; push_cast; ring
      ring_nf
      rw [show ((A:ℤ))^2 = (N:ℤ)*(m:ℤ) from this]
      ring
    rw [hexp, zpow_add₀ hzN, zpow_add₀ hzN]
    -- the N*... term is 1
    have hNterm : zeta N ^ ((N : ℤ) * (t * (m : ℤ) * (c : ℤ) ^ 2)) = 1 := by
      rw [zpow_mul, zpow_natCast, zeta_pow_n N (by rw [hN]; positivity), one_zpow]
    rw [hNterm, mul_one]
    -- the A*... term
    have hAterm : zeta N ^ ((A : ℤ) * (2 * t * (a : ℤ) * (c : ℤ)))
        = (zeta p ^ (2 * t * (a : ℤ))) ^ c := by
      rw [zpow_mul, zpow_natCast, hNA]
      rw [show (2 * t * (a : ℤ) * (c : ℤ)) = (2 * t * (a : ℤ)) * (c : ℤ) by ring]
      rw [zpow_mul, zpow_natCast]
    rw [hAterm]
  rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun c hc => key a ha c hc))]
  -- now inner sum over c
  have inner : ∀ a ∈ range A,
      (∑ c ∈ range p, zeta N ^ (t * (a : ℤ) ^ 2) * (zeta p ^ (2 * t * (a : ℤ))) ^ c)
        = if (p : ℤ) ∣ (a : ℤ) then (p : ℂ) * zeta N ^ (t * (a : ℤ) ^ 2) else 0 := by
    intro a _
    rw [← Finset.mul_sum]
    have hroot : (zeta p ^ (2 * t * (a : ℤ))) ^ p = 1 := by
      rw [← zpow_natCast (zeta p ^ (2 * t * (a:ℤ))) p, ← zpow_mul,
        show (2 * t * (a:ℤ)) * (p:ℤ) = (2 * t * (a:ℤ)) * (p:ℤ) from rfl]
      rw [show (2 * t * (a:ℤ)) * (p:ℤ) = (p:ℤ) * (2 * t * (a:ℤ)) by ring,
        zpow_mul, zpow_natCast, zeta_pow_n p hp0, one_zpow]
    rw [geom_root_sum p hp0 _ hroot]
    -- r = 1 ↔ p ∣ a
    have hprim : IsPrimitiveRoot (zeta p) p := by
      have h2 := Complex.isPrimitiveRoot_exp p hp0.ne'
      simpa only [zeta] using h2
    have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hiff : zeta p ^ (2 * t * (a : ℤ)) = 1 ↔ (p : ℤ) ∣ (a : ℤ) := by
      rw [hprim.zpow_eq_one_iff_dvd]
      constructor
      · intro h
        rcases (hpprime.dvd_mul).mp h with h1 | h2
        · rcases (hpprime.dvd_mul).mp h1 with h3 | h4
          · exfalso
            have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h3
            have hle' : p ≤ 2 := by exact_mod_cast hle
            have hge : 2 ≤ p := hp.two_le
            exact hp2 (by omega)
          · exact absurd h4 ht
        · exact h2
      · intro h
        exact Dvd.dvd.mul_left h _
    by_cases hd : (p : ℤ) ∣ (a : ℤ)
    · rw [if_pos hd, if_pos (hiff.mpr hd)]; ring
    · rw [if_neg hd, if_neg (fun h => hd (hiff.mp h)), mul_zero]
  rw [Finset.sum_congr rfl inner]
  -- now sum over a in range A of (if p∣a then p*zetaN^(t a²) else 0)
  rw [hAeq, sum_range_mul_reindex p m hp0]
  rw [Finset.sum_eq_single (0 : ℕ)
    (by intro x hx hx0
        apply Finset.sum_eq_zero
        intro y _
        rw [if_neg]
        intro hdvd
        apply hx0
        have hd2 : p ∣ (x + p * y) := by exact_mod_cast hdvd
        rw [Nat.add_comm] at hd2
        exact Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_add_right ⟨y, rfl⟩).mp hd2)
          (Finset.mem_range.mp hx))
    (by intro h; exact absurd (Finset.mem_range.mpr hp0) h)]
  -- main: f 0 = p * gs m t
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hdvd0 : (p : ℤ) ∣ ((0 + p * y : ℕ) : ℤ) := by push_cast; exact ⟨y, by ring⟩
  rw [if_pos hdvd0]
  congr 1
  rw [show ((0 + p * y : ℕ) : ℤ) = (p : ℤ) * (y : ℤ) by push_cast; ring]
  rw [show t * ((p : ℤ) * (y : ℤ)) ^ 2 = ((p ^ 2 : ℕ) : ℤ) * (t * (y : ℤ) ^ 2) by push_cast; ring]
  rw [zpow_mul, zpow_natCast, hNp2]

-- nonzero in field
lemma tcast_ne (p : ℕ) [Fact p.Prime] (t : ℤ) (ht : ¬ (p : ℤ) ∣ t) : (t : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ht

lemma tcast_isUnit (p : ℕ) [Fact p.Prime] (t : ℤ) (ht : ¬ (p : ℤ) ∣ t) : IsUnit (t : ZMod p) :=
  isUnit_iff_ne_zero.mpr (tcast_ne p t ht)

lemma qc_sq (p : ℕ) [Fact p.Prime] (t : ℤ) (ht : ¬ (p : ℤ) ∣ t) :
    (quadraticChar (ZMod p) (t : ZMod p)) ^ 2 = 1 := by
  have hne := tcast_ne p t ht
  rcases quadraticChar_isQuadratic (ZMod p) (t : ZMod p) with h0 | h1 | hm1
  · exact absurd ((quadraticChar_eq_zero_iff).mp h0) hne
  · rw [h1]; norm_num
  · rw [hm1]; norm_num

lemma gs_at_one (t : ℤ) : gs 1 t = 1 := by
  simp only [gs, Finset.range_one, Finset.sum_singleton, Nat.cast_zero]
  norm_num

-- prime power closed form
lemma gs_ppow_char (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (t : ℤ) (ht : ¬ (p : ℤ) ∣ t) (k : ℕ) :
    gs (p ^ k) t = (((quadraticChar (ZMod p) (t : ZMod p)) ^ k : ℤ) : ℂ) * gs (p ^ k) 1 := by
  have hp : p.Prime := Fact.out
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have h1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h
    have : p ≤ 1 := by exact_mod_cast h1
    have := hp.two_le; omega
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    match k with
    | 0 =>
      simp only [pow_zero, Int.cast_one, one_mul, gs_at_one]
    | 1 =>
      simp only [pow_one]
      rw [gs_char_prime p hp2 t (tcast_isUnit p t ht)]
    | (n + 2) =>
      have hrec := gs_ppow_rec p (n + 2) hp hp2 (by omega) t ht
      have hrec1 := gs_ppow_rec p (n + 2) hp hp2 (by omega) 1 hp1
      have IHn := IH n (by omega)
      simp only [Nat.add_sub_cancel] at hrec hrec1
      rw [hrec, IHn, hrec1]
      have hqsq : ((quadraticChar (ZMod p) (t : ZMod p)) ^ (n + 2) : ℤ)
          = ((quadraticChar (ZMod p) (t : ZMod p)) ^ n : ℤ) := by
        rw [pow_add, qc_sq p t ht, mul_one]
      rw [hqsq]
      ring

-- ===== 2-adic =====
-- halving: gs(2^j,t) = 2 * (half-range sum), j ≥ 2
lemma gs_two_halve (j : ℕ) (hj : 2 ≤ j) (t : ℤ) :
    gs (2 ^ j) t = 2 * ∑ w ∈ range (2 ^ (j - 1)), zeta (2 ^ j) ^ (t * (w : ℤ) ^ 2) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  rw [show i + 2 - 1 = i + 1 by omega]
  unfold gs
  rw [show (2 : ℕ) ^ (i + 2) = 2 ^ (i + 1) * 2 by ring,
    sum_range_mul_reindex (2 ^ (i + 1)) 2 (by positivity)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hzne : zeta (2 ^ (i + 1) * 2) ≠ 0 := zeta_ne_zero _
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  set M := 2 ^ (i + 1) * 2 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hc0 : zeta M ^ (t * ((u + 2 ^ (i + 1) * 0 : ℕ) : ℤ) ^ 2)
      = zeta M ^ (t * (u : ℤ) ^ 2) := by norm_num
  have hc1 : zeta M ^ (t * ((u + 2 ^ (i + 1) * 1 : ℕ) : ℤ) ^ 2)
      = zeta M ^ (t * (u : ℤ) ^ 2) := by
    have hsplit : t * ((u + 2 ^ (i + 1) * 1 : ℕ) : ℤ) ^ 2
        = t * (u : ℤ) ^ 2 + (M : ℤ) * (t * (u : ℤ)) + (M : ℤ) * (t * ((2 ^ i : ℕ) : ℤ)) := by
      rw [hM]; push_cast; ring
    rw [hsplit, zpow_add₀ hzne, zpow_add₀ hzne]
    have e1 : zeta M ^ ((M : ℤ) * (t * (u : ℤ))) = 1 := by
      rw [zpow_mul, zpow_natCast, zeta_pow_n M hMpos, one_zpow]
    have e2 : zeta M ^ ((M : ℤ) * (t * ((2 ^ i : ℕ) : ℤ))) = 1 := by
      rw [zpow_mul, zpow_natCast, zeta_pow_n M hMpos, one_zpow]
    rw [e1, e2, mul_one, mul_one]
  rw [hc0, hc1]; ring

lemma zeta_two : zeta 2 = -1 := by
  rw [zeta]
  rw [show (2 * Real.pi * I / (2:ℕ)) = Real.pi * I by push_cast; ring]
  rw [Complex.exp_pi_mul_I]

-- 2-adic recursion: k ≥ 4, t odd
lemma gs_two_rec (k : ℕ) (hk : 4 ≤ k) (t : ℤ) (ht : Odd t) :
    gs (2 ^ k) t = 2 * gs (2 ^ (k - 2)) t := by
  obtain ⟨e, rfl⟩ : ∃ e, k = e + 4 := ⟨k - 4, by omega⟩
  simp only [show e + 4 - 2 = e + 2 by omega]
  set N := 2 ^ (e + 4) with hN
  set M := 2 ^ (e + 2) with hM
  have hNeq : N = M * 4 := by rw [hN, hM]; ring
  have hMpos : 0 < M := by rw [hM]; positivity
  have hzN : zeta N ≠ 0 := zeta_ne_zero N
  -- zeta N ^ (2^(e+3)) = zeta 2 = -1
  have hhalf : zeta N ^ (2 ^ (e + 3)) = -1 := by
    have hdvd : (2 ^ (e + 3)) ∣ N := ⟨2, by rw [hN]; ring⟩
    have := zeta_pow_div N (2 ^ (e + 3)) hdvd (by positivity)
    rw [show N / 2 ^ (e + 3) = 2 by rw [hN, show e + 4 = (e+3) + 1 by ring, pow_succ,
      Nat.mul_div_cancel_left _ (by positivity)]] at this
    rw [this, zeta_two]
  -- zeta N ^ 4 = zeta M
  have hN4 : zeta N ^ 4 = zeta M := by
    have hdvd : 4 ∣ N := ⟨M, by rw [hN, hM]; ring⟩
    have := zeta_pow_div N 4 hdvd (by norm_num)
    rwa [show N / 4 = M by rw [hN, hM, show (2:ℕ) ^ (e + 4) = 2 ^ (e + 2) * 4 by ring]; simp] at this
  unfold gs
  rw [show range N = range (M * 4) by rw [hNeq], sum_range_mul_reindex M 4 hMpos]
  -- per-term
  have key : ∀ u ∈ range M, ∀ c ∈ range 4,
      zeta N ^ (t * ((u + M * c : ℕ) : ℤ) ^ 2)
        = zeta N ^ (t * (u : ℤ) ^ 2) * ((-1 : ℂ) ^ (t * (u : ℤ))) ^ c := by
    intro u _ c _
    rw [show ((u + M * c : ℕ) : ℤ) = (u : ℤ) + (M : ℤ) * (c : ℤ) by push_cast; ring]
    have hsplit : t * ((u : ℤ) + (M : ℤ) * (c : ℤ)) ^ 2
        = t * (u : ℤ) ^ 2 + (2 ^ (e + 3) : ℕ) * (t * (u : ℤ) * (c : ℤ))
          + (N : ℤ) * (t * ((2 ^ e : ℕ) : ℤ) * (c : ℤ) ^ 2) := by
      have hM2 : (M : ℤ) ^ 2 = (N : ℤ) * ((2 ^ e : ℕ) : ℤ) := by
        rw [hM, hN]; push_cast; ring
      have h2M : (2 : ℤ) * (M : ℤ) = ((2 ^ (e + 3) : ℕ) : ℤ) := by
        rw [hM]; push_cast; ring
      have expand : t * ((u : ℤ) + (M : ℤ) * (c : ℤ)) ^ 2
          = t * (u : ℤ) ^ 2 + (2 * (M : ℤ)) * (t * (u : ℤ) * (c : ℤ))
            + (M : ℤ) ^ 2 * (t * (c : ℤ) ^ 2) := by ring
      rw [expand, h2M, hM2]; ring
    rw [hsplit, zpow_add₀ hzN, zpow_add₀ hzN]
    have hNterm : zeta N ^ ((N : ℤ) * (t * ((2 ^ e : ℕ) : ℤ) * (c : ℤ) ^ 2)) = 1 := by
      rw [zpow_mul, zpow_natCast, zeta_pow_n N (by rw [hN]; positivity), one_zpow]
    rw [hNterm, mul_one]
    have hMterm : zeta N ^ ((2 ^ (e + 3) : ℕ) * (t * (u : ℤ) * (c : ℤ)))
        = ((-1 : ℂ) ^ (t * (u : ℤ))) ^ c := by
      rw [zpow_mul, zpow_natCast, hhalf]
      rw [show (t * (u : ℤ) * (c : ℤ)) = (t * (u : ℤ)) * (c : ℤ) by ring, zpow_mul, zpow_natCast]
    rw [hMterm]
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun c hc => key u hu c hc))]
  -- inner sum over c, geom with r = (-1)^(t*u)
  have inner : ∀ u ∈ range M,
      (∑ c ∈ range 4, zeta N ^ (t * (u : ℤ) ^ 2) * ((-1 : ℂ) ^ (t * (u : ℤ))) ^ c)
        = if 2 ∣ u then (4 : ℂ) * zeta N ^ (t * (u : ℤ) ^ 2) else 0 := by
    intro u _
    rw [← Finset.mul_sum]
    have hroot : ((-1 : ℂ) ^ (t * (u : ℤ))) ^ 4 = 1 := by
      rw [← zpow_natCast ((-1:ℂ) ^ (t*(u:ℤ))) 4, ← zpow_mul,
        show (t * (u:ℤ)) * ((4:ℕ):ℤ) = ((4:ℕ):ℤ) * (t * (u:ℤ)) by push_cast; ring, zpow_mul,
        zpow_natCast]
      norm_num
    rw [geom_root_sum 4 (by norm_num) _ hroot]
    have hiff : (-1 : ℂ) ^ (t * (u : ℤ)) = 1 ↔ 2 ∣ u := by
      rcases ht with ⟨s, hs⟩
      constructor
      · intro h
        by_contra hodd
        have hu : Odd u := Nat.not_even_iff_odd.mp (fun he => hodd he.two_dvd)
        rcases hu with ⟨v, hv⟩
        have : (-1 : ℂ) ^ (t * (u : ℤ)) = -1 := by
          rw [show t * (u : ℤ) = 2 * (2 * s * (v : ℤ) + s + (v : ℤ)) + 1 by
            rw [hs, hv]; push_cast; ring]
          rw [zpow_add₀ (by norm_num), zpow_mul]
          norm_num
        rw [this] at h; norm_num at h
      · intro h
        obtain ⟨v, rfl⟩ := h
        rw [show t * ((2 * v : ℕ) : ℤ) = 2 * (t * v) by push_cast; ring, zpow_mul]
        norm_num
    by_cases hd : 2 ∣ u
    · rw [if_pos hd, if_pos (hiff.mpr hd)]; ring
    · rw [if_neg hd, if_neg (fun h => hd (hiff.mp h)), mul_zero]
  rw [Finset.sum_congr rfl inner]
  rw [show M = 2 * (2 ^ (e + 1)) by rw [hM]; ring, sum_range_mul_reindex 2 (2 ^ (e + 1)) (by norm_num)]
  rw [Finset.sum_eq_single (0 : ℕ)
    (by intro x hx hx0
        apply Finset.sum_eq_zero
        intro y _
        rw [if_neg]
        intro hdvd
        apply hx0
        rw [Finset.mem_range] at hx
        have : x = 0 := by omega
        exact this)
    (by intro h; exact absurd (Finset.mem_range.mpr (by norm_num)) h)]
  -- main: fold RHS sum to gs and apply halve
  rw [show (2 * 2 ^ (e + 1) : ℕ) = 2 ^ (e + 2) by ring,
    show (∑ k ∈ range (2 ^ (e + 2)), zeta (2 ^ (e + 2)) ^ (t * (k : ℤ) ^ 2)) = gs (2 ^ (e + 2)) t from rfl,
    gs_two_halve (e + 2) (by omega) t, show (e + 2 - 1) = e + 1 by omega,
    ← mul_assoc, show (2 : ℂ) * 2 = 4 by norm_num, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [if_pos ⟨c, by ring⟩,
    show ((0 + 2 * c : ℕ) : ℤ) = 2 * (c : ℤ) by push_cast; ring,
    show t * (2 * (c : ℤ)) ^ 2 = ((4 : ℕ) : ℤ) * (t * (c : ℤ) ^ 2) by push_cast; ring,
    zpow_mul, zpow_natCast, hN4]

lemma cexp_zpow (w : ℂ) (z : ℤ) : Complex.exp w ^ z = Complex.exp ((z : ℂ) * w) := by
  rw [Complex.exp_int_mul]

-- zeta factorization via Bezout
lemma zeta_mul_factor (m₁ m₂ : ℕ) (hm1 : 0 < m₁) (hm2 : 0 < m₂)
    (a b : ℤ) (hab : a * m₂ + b * m₁ = 1) (z : ℤ) :
    zeta (m₁ * m₂) ^ z = zeta m₁ ^ (a * z) * zeta m₂ ^ (b * z) := by
  have h1 : (m₁ : ℂ) ≠ 0 := by exact_mod_cast hm1.ne'
  have h2 : (m₂ : ℂ) ≠ 0 := by exact_mod_cast hm2.ne'
  simp only [zeta, cexp_zpow]
  rw [← Complex.exp_add]
  congr 1
  have hab' : (a : ℂ) * m₂ + (b : ℂ) * m₁ = 1 := by exact_mod_cast hab
  push_cast
  have hsum : (a:ℂ)/m₁ + (b:ℂ)/m₂ = 1/((m₁:ℂ)*(m₂:ℂ)) := by
    field_simp
    linear_combination hab'
  rw [show (z:ℂ)*(2*(Real.pi:ℂ)*I/((m₁:ℂ)*(m₂:ℂ))) = ((z:ℂ)*(2*(Real.pi:ℂ)*I))*(1/((m₁:ℂ)*(m₂:ℂ))) by ring,
    show (a:ℂ)*z*(2*(Real.pi:ℂ)*I/m₁) = ((z:ℂ)*(2*(Real.pi:ℂ)*I))*((a:ℂ)/m₁) by ring,
    show (b:ℂ)*z*(2*(Real.pi:ℂ)*I/m₂) = ((z:ℂ)*(2*(Real.pi:ℂ)*I))*((b:ℂ)/m₂) by ring,
    ← mul_add, hsum]

-- gs over ZMod, with ring-element exponent
lemma gsZ (n : ℕ) [NeZero n] (c : ℤ) :
    gs n c = ∑ u : ZMod n, zeta n ^ (((c : ZMod n) * u ^ 2).val) := by
  unfold gs
  rw [sum_zmod_eq_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [zeta_zpow_val n (c * (k : ℤ) ^ 2)]
  congr 2
  push_cast
  ring

-- chineseRemainder components are the casts
lemma crt_fst (m₁ m₂ : ℕ) [NeZero (m₁ * m₂)] (hcop : Nat.Coprime m₁ m₂) (x : ZMod (m₁ * m₂)) :
    (ZMod.chineseRemainder hcop x).1 = ((x.val : ℕ) : ZMod m₁) := by
  have hdvd : m₁ ∣ m₁ * m₂ := ⟨m₂, rfl⟩
  have hx := RingHom.congr_fun
    (RingHom.ext_zmod ((RingHom.fst (ZMod m₁) (ZMod m₂)).comp (ZMod.chineseRemainder hcop).toRingHom)
      (ZMod.castHom hdvd (ZMod m₁))) x
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_fst,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hx
  rw [hx, ZMod.castHom_apply]
  exact (ZMod.natCast_val x).symm

lemma crt_snd (m₁ m₂ : ℕ) [NeZero (m₁ * m₂)] (hcop : Nat.Coprime m₁ m₂) (x : ZMod (m₁ * m₂)) :
    (ZMod.chineseRemainder hcop x).2 = ((x.val : ℕ) : ZMod m₂) := by
  have hdvd : m₂ ∣ m₁ * m₂ := ⟨m₁, by ring⟩
  have hx := RingHom.congr_fun
    (RingHom.ext_zmod ((RingHom.snd (ZMod m₁) (ZMod m₂)).comp (ZMod.chineseRemainder hcop).toRingHom)
      (ZMod.castHom hdvd (ZMod m₂))) x
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_snd,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hx
  rw [hx, ZMod.castHom_apply]
  exact (ZMod.natCast_val x).symm

-- CRT multiplicativity of gs
lemma gs_crt (m₁ m₂ : ℕ) [NeZero m₁] [NeZero m₂] (hm1 : 0 < m₁) (hm2 : 0 < m₂)
    (hcop : Nat.Coprime m₁ m₂) (a b : ℤ) (hab : a * m₂ + b * m₁ = 1) (t : ℤ) :
    gs (m₁ * m₂) t = gs m₁ (a * t) * gs m₂ (b * t) := by
  haveI : NeZero (m₁ * m₂) := ⟨by positivity⟩
  -- expand gs(m₁m₂,t) using factorization, over ZMod(m₁m₂)
  have step1 : gs (m₁ * m₂) t
      = ∑ x : ZMod (m₁ * m₂),
          zeta m₁ ^ (((a * t : ZMod m₁) * ((x.val : ℕ) : ZMod m₁) ^ 2).val)
            * zeta m₂ ^ (((b * t : ZMod m₂) * ((x.val : ℕ) : ZMod m₂) ^ 2).val) := by
    unfold gs
    rw [sum_zmod_eq_range]
    apply Finset.sum_congr rfl
    intro x hx
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hx)]
    rw [zeta_mul_factor m₁ m₂ hm1 hm2 a b hab (t * (x : ℤ) ^ 2)]
    congr 1
    · rw [show a * (t * (x : ℤ) ^ 2) = (a * t) * (x : ℤ) ^ 2 by ring, zeta_zpow_val m₁]
      congr 2
      push_cast; ring
    · rw [show b * (t * (x : ℤ) ^ 2) = (b * t) * (x : ℤ) ^ 2 by ring, zeta_zpow_val m₂]
      congr 2
      push_cast; ring
  rw [step1]
  -- reindex via chineseRemainder
  have hmatch : (∑ x : ZMod (m₁ * m₂),
        zeta m₁ ^ (((a * t : ZMod m₁) * ((x.val : ℕ) : ZMod m₁) ^ 2).val)
          * zeta m₂ ^ (((b * t : ZMod m₂) * ((x.val : ℕ) : ZMod m₂) ^ 2).val))
      = ∑ x : ZMod (m₁ * m₂),
        (fun p : ZMod m₁ × ZMod m₂ =>
          zeta m₁ ^ (((a * t : ZMod m₁) * p.1 ^ 2).val)
            * zeta m₂ ^ (((b * t : ZMod m₂) * p.2 ^ 2).val))
          ((ZMod.chineseRemainder hcop).toEquiv x) := by
    apply Finset.sum_congr rfl
    intro x _
    simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]
    rw [crt_fst, crt_snd]
  rw [hmatch, Equiv.sum_comp (ZMod.chineseRemainder hcop).toEquiv
    (fun p : ZMod m₁ × ZMod m₂ =>
      zeta m₁ ^ (((a * t : ZMod m₁) * p.1 ^ 2).val)
        * zeta m₂ ^ (((b * t : ZMod m₂) * p.2 ^ 2).val))]
  rw [Fintype.sum_prod_type, gsZ m₁ (a * t), gsZ m₂ (b * t), Finset.sum_mul_sum]
  simp only [Int.cast_mul]


-- legendreSym p t = quadraticChar (ZMod p) (t : ZMod p), as ℤ
example (p : ℕ) [Fact p.Prime] (t : ℤ) :
    (legendreSym p t : ℤ) = (quadraticChar (ZMod p) (t : ZMod p) : ℤ) := rfl

lemma gs_odd_jacobi : ∀ m : ℕ, Odd m → ∀ t : ℤ, IsCoprime t (m:ℤ) →
    gs m t = ((jacobiSym t m : ℤ) : ℂ) * gs m 1 := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      intro hodd t hcop
      haveI : Fact p.Prime := ⟨hp⟩
      have hp2le : 2 ≤ p := hp.two_le
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hn.ne'⟩)) hodd
      have hpdvd : (p:ℤ) ∣ ((p^n : ℕ) : ℤ) := by
        rw [show ((p^n:ℕ):ℤ) = (p:ℤ)^n by push_cast; ring]
        exact dvd_pow_self _ hn.ne'
      have hpt : ¬ (p : ℤ) ∣ t := by
        intro hdvd
        have hu := hcop.isUnit_of_dvd' hdvd hpdvd
        rw [Int.isUnit_iff] at hu
        have : (2:ℤ) ≤ (p:ℤ) := by exact_mod_cast hp2le
        rcases hu with h | h <;> omega
      rw [gs_ppow_char p hp2 t hpt n]
      congr 2
      have h1 : ((quadraticChar (ZMod p) (t : ZMod p)) ^ n : ℤ) = (legendreSym p t) ^ n := rfl
      rw [h1, jacobiSym.legendreSym.to_jacobiSym, jacobiSym.pow_right]
  | zero => intro hodd; exact absurd hodd (by decide)
  | one => intro hodd t hcop; rw [gs_at_one, gs_at_one, jacobiSym.one_right]; norm_num
  | coprime a b ha1 hb1 hcopab iha ihb =>
      intro hodd t hcop
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      haveI : NeZero a := ⟨by omega⟩
      haveI : NeZero b := ⟨by omega⟩
      obtain ⟨hoa, hob⟩ := Nat.odd_mul.mp hodd
      obtain ⟨α, β, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcopab.symm)
      have hcop' : IsCoprime t ((a:ℤ)*(b:ℤ)) := by rwa [Nat.cast_mul] at hcop
      have hta : IsCoprime t (a:ℤ) := hcop'.of_mul_right_left
      have htb : IsCoprime t (b:ℤ) := hcop'.of_mul_right_right
      have halpha : IsCoprime (α:ℤ) (a:ℤ) := ⟨(b:ℤ), β, by linear_combination hab⟩
      have hbeta : IsCoprime (β:ℤ) (b:ℤ) := ⟨(a:ℤ), α, by linear_combination hab⟩
      have hcrt_t := gs_crt a b ha0 hb0 hcopab α β hab t
      have hcrt_1 := gs_crt a b ha0 hb0 hcopab α β hab 1
      simp only [mul_one] at hcrt_1
      rw [hcrt_t, iha hoa (α*t) (halpha.mul_left hta), ihb hob (β*t) (hbeta.mul_left htb),
          hcrt_1, iha hoa α halpha, ihb hob β hbeta,
          jacobiSym.mul_left α t a, jacobiSym.mul_left β t b]
      have hJ : (jacobiSym t (a*b) : ℤ) = (jacobiSym t a : ℤ) * (jacobiSym t b : ℤ) :=
        jacobiSym.mul_right t a b
      rw [hJ]
      push_cast
      ring


lemma zeta_four : zeta 4 = I := by
  unfold zeta
  rw [show (2*(Real.pi:ℂ)*I/((4:ℕ):ℂ)) = (Real.pi:ℂ)/2*I by push_cast; ring,
     Complex.exp_pi_div_two_mul_I]

lemma I_zpow_four_mul (s : ℤ) : I ^ (4 * s) = 1 := by
  rw [zpow_mul, show (I:ℂ)^(4:ℤ) = 1 by rw [show (4:ℤ) = ((4:ℕ):ℤ) from rfl, zpow_natCast]; norm_num,
    one_zpow]

lemma gs_four (s : ℤ) : gs 4 s = 2 * (1 + I ^ s) := by
  unfold gs
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [zeta_four]
  norm_num
  rw [show I ^ (s * 4) = 1 by rw [mul_comm]; exact I_zpow_four_mul s,
      show I ^ (s * 9) = I ^ s by rw [show (9:ℤ) = 4*2+1 by ring, mul_add, mul_one, zpow_add₀ Complex.I_ne_zero, show s*(4*2) = 4*(s*2) by ring, I_zpow_four_mul (s*2), one_mul]]
  ring

lemma zeta_eight_pow8 : zeta 8 ^ (8:ℤ) = 1 := by
  rw [show (8:ℤ) = ((8:ℕ):ℤ) from rfl, zpow_natCast]; exact zeta_pow_n 8 (by norm_num)

lemma zeta_eight_pow4 : zeta 8 ^ (4:ℤ) = -1 := by
  unfold zeta
  rw [show (4:ℤ) = ((4:ℕ):ℤ) from rfl, zpow_natCast, ← Complex.exp_nat_mul,
     show ((4:ℕ):ℂ) * (2*(Real.pi:ℂ)*I/((8:ℕ):ℂ)) = (Real.pi:ℂ)*I by push_cast; ring,
     Complex.exp_pi_mul_I]

lemma gs_eight (s : ℤ) (hs : Odd s) : gs 8 s = 4 * zeta 8 ^ s := by
  have hred : ∀ c d : ℤ, zeta 8 ^ (s*(8*c+d)) = zeta 8 ^ (s*d) := by
    intro c d
    rw [show s*(8*c+d) = 8*(s*c) + s*d by ring, zpow_add₀ (zeta_ne_zero 8), zpow_mul,
       zeta_eight_pow8, one_zpow, one_mul]
  unfold gs
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num
  rw [show s*9 = s*(8*1+1) by ring, hred 1 1,
      show s*16 = s*(8*2+0) by ring, hred 2 0,
      show s*25 = s*(8*3+1) by ring, hred 3 1,
      show s*36 = s*(8*4+4) by ring, hred 4 4,
      show s*49 = s*(8*6+1) by ring, hred 6 1]
  simp only [mul_zero, mul_one, zpow_zero]
  rw [show s*4 = 4*s by ring, zpow_mul, zeta_eight_pow4]
  rw [hs.neg_one_zpow]
  ring

lemma gs_two_even (j : ℕ) (hj : 1 ≤ j) (s : ℤ) (hs : Odd s) :
    gs (2 ^ (2 * j)) s = 2 ^ j * (1 + I ^ s) := by
  induction j with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; rw [show 2*(0+1) = 2 from rfl, show (2:ℕ)^2 = 4 from rfl, gs_four]; ring
    · have hk : 4 ≤ 2*(i+1) := by omega
      rw [gs_two_rec (2*(i+1)) hk s hs, show 2*(i+1)-2 = 2*i by omega, ih hi]
      rw [pow_succ]; ring

lemma gs_two_odd (j : ℕ) (hj : 1 ≤ j) (s : ℤ) (hs : Odd s) :
    gs (2 ^ (2 * j + 1)) s = 2 ^ (j + 1) * zeta 8 ^ s := by
  induction j with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; rw [show 2*(0+1)+1 = 3 from rfl, show (2:ℕ)^3 = 8 from rfl, gs_eight s hs]; ring
    · have hk : 4 ≤ 2*(i+1)+1 := by omega
      rw [gs_two_rec (2*(i+1)+1) hk s hs, show 2*(i+1)+1-2 = 2*i+1 by omega, ih hi]
      rw [pow_succ]; ring

-- I^s for s odd: re = 0, im = ±1 by s mod 4
lemma I_zpow_odd (s : ℤ) (hs : Odd s) : I ^ s = if s % 4 = 1 then I else -I := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, (r = 1 ∨ r = 3) ∧ s = 4*q + r := by
    rcases hs with ⟨j, hj⟩
    refine ⟨j/2, if j % 2 = 0 then 1 else 3, by omega, by omega⟩
  rw [zpow_add₀ Complex.I_ne_zero, I_zpow_four_mul, one_mul]
  rcases hr with rfl | rfl
  · rw [zpow_one]; norm_num [Int.add_mul_emod_self_left]
  · rw [show (3:ℤ) = 2+1 by ring, zpow_add₀ Complex.I_ne_zero, zpow_one,
       show (2:ℤ) = ((2:ℕ):ℤ) from rfl, zpow_natCast]
    norm_num [Int.add_mul_emod_self_left, Complex.I_sq]

lemma zeta_eight_val : zeta 8 = (((Real.sqrt 2)/2 : ℝ):ℂ) * (1 + I) := by
  unfold zeta
  rw [show (2*(Real.pi:ℂ)*I/((8:ℕ):ℂ)) = ((Real.pi/4:ℝ):ℂ)*I by push_cast; ring,
     Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
     Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring

lemma zeta_eight_zpow_reim (s : ℤ) (hs : Odd s) :
    (zeta 8 ^ s).re = (Real.sqrt 2 / 2) * (if s % 8 = 1 ∨ s % 8 = 7 then 1 else -1) ∧
    (zeta 8 ^ s).im = (Real.sqrt 2 / 2) * (if s % 8 = 1 ∨ s % 8 = 3 then 1 else -1) := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨q, r, hr, hsr⟩ : ∃ q r, (r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) ∧ s = 8*q + r := by
    obtain ⟨j, hj⟩ := hs
    exact ⟨s/8, s%8, by omega, by omega⟩
  have hz8r : zeta 8 ^ s = zeta 8 ^ r := by
    rw [hsr, zpow_add₀ (zeta_ne_zero 8), zpow_mul, zeta_eight_pow8, one_zpow, one_mul]
  rw [hz8r]
  have hsmod : s % 8 = r := by omega
  rw [hsmod]
  have hz8sq : zeta 8 ^ (2:ℤ) = I := by
    rw [show (2:ℤ) = ((2:ℕ):ℤ) from rfl, zpow_natCast]
    unfold zeta
    rw [← Complex.exp_nat_mul,
       show ((2:ℕ):ℂ)*(2*(Real.pi:ℂ)*I/((8:ℕ):ℂ)) = (Real.pi:ℂ)/2*I by push_cast; ring,
       Complex.exp_pi_div_two_mul_I]
  have h3 : zeta 8 ^ (3:ℤ) = I * zeta 8 := by
    rw [show (3:ℤ) = 2+1 by ring, zpow_add₀ (zeta_ne_zero 8), hz8sq, zpow_one]
  have h5 : zeta 8 ^ (5:ℤ) = -zeta 8 := by
    rw [show (5:ℤ) = 2+2+1 by ring, zpow_add₀ (zeta_ne_zero 8), zpow_add₀ (zeta_ne_zero 8),
       hz8sq, zpow_one]; rw [Complex.I_mul_I]; ring
  have h7 : zeta 8 ^ (7:ℤ) = -I * zeta 8 := by
    rw [show (7:ℤ) = 2+2+2+1 by ring, zpow_add₀ (zeta_ne_zero 8), zpow_add₀ (zeta_ne_zero 8),
       zpow_add₀ (zeta_ne_zero 8), hz8sq, zpow_one]
    rw [Complex.I_mul_I]; ring
  rcases hr with rfl | rfl | rfl | rfl
  · rw [zpow_one, zeta_eight_val]
    constructor <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  · rw [h3, zeta_eight_val]
    constructor <;> simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring
  · rw [h5, zeta_eight_val]
    constructor <;> simp [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im] <;> ring
  · rw [h7, zeta_eight_val]
    constructor <;> simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring
end EngineSection

section S5
open Finset Complex
open scoped Real

lemma zeta_zpow (n : ℕ) (a : ℤ) : (zeta n) ^ a = Complex.exp (2 * Real.pi * I * a / n) := by
  rw [zeta, ← Complex.exp_int_mul]
  congr 1; push_cast; ring

lemma geom_root_sumZ (n : ℕ) (hn : 0 < n) (j : ℤ) :
    (∑ a ∈ Finset.range n, (zeta n) ^ (j * a)) = if (n:ℤ) ∣ j then (n : ℂ) else 0 := by
  have hxn : (zeta n ^ j) ^ n = 1 := by
    rw [← zpow_natCast (zeta n ^ j) n, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      zeta_pow_n n hn, one_zpow]
  have hterm : ∀ a : ℕ, (zeta n) ^ (j * (a:ℤ)) = (zeta n ^ j) ^ a := by
    intro a; rw [zpow_mul, zpow_natCast]
  simp_rw [hterm]
  by_cases hj : (n:ℤ) ∣ j
  · rw [if_pos hj]
    have hx1 : zeta n ^ j = 1 := by
      obtain ⟨c, rfl⟩ := hj
      rw [zpow_mul, zpow_natCast, zeta_pow_n n hn, one_zpow]
    simp [hx1]
  · rw [if_neg hj]
    have hx1 : zeta n ^ j ≠ 1 := by
      intro h
      apply hj
      rw [zeta_zpow, Complex.exp_eq_one_iff] at h
      obtain ⟨k, hk⟩ := h
      have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [div_eq_iff hnc] at hk
      have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, I_ne_zero]
      have hj2 : (j:ℂ) = (k:ℂ) * n := mul_left_cancel₀ hpi (by linear_combination hk)
      have hz : (j:ℤ) = k * n := by exact_mod_cast hj2
      exact ⟨k, by rw [hz]; ring⟩
    rw [geom_sum_eq hx1, hxn, sub_self, zero_div]

lemma deriv_root_sum (z : ℂ) (n : ℕ) (hn : 0 < n) (hzn : z ^ n = 1) (hz1 : z ≠ 1) :
    (z - 1) * (∑ a ∈ range n, (a:ℂ) * z ^ a) = n := by
  set T := ∑ a ∈ range n, (a:ℂ) * z ^ a with hT
  have hG : ∑ a ∈ range n, z ^ a = 0 := by
    rw [geom_sum_eq hz1, hzn, sub_self, zero_div]
  have e1 : ∑ a ∈ range n, ((a:ℂ) + 1) * z ^ (a+1)
      = z * T + z * (∑ a ∈ range n, z ^ a) := by
    rw [hT, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _; ring
  have e2 : ∑ a ∈ range n, ((a:ℂ) + 1) * z ^ (a+1) = T + n := by
    have h3 : ∑ b ∈ range (n+1), (b:ℂ) * z ^ b
        = ∑ a ∈ range n, ((a:ℂ) + 1) * z ^ (a+1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, pow_zero, add_zero]
      apply Finset.sum_congr rfl; intro a _; push_cast; ring
    rw [Finset.sum_range_succ, hzn, mul_one, ← hT] at h3
    rw [← h3]
  rw [hG, mul_zero, add_zero] at e1
  rw [e2] at e1
  linear_combination -e1


lemma div_iff_mod (n k a : ℕ) (hn : 0 < n) (ha : a < n) :
    (n:ℤ) ∣ ((k:ℤ) ^ 2 - a) ↔ a = k ^ 2 % n := by
  rw [show ((k:ℤ) ^ 2 - a) = ((k ^ 2 : ℕ):ℤ) - ((a : ℕ):ℤ) by push_cast; ring,
    ← Int.modEq_iff_dvd, Int.natCast_modEq_iff]
  constructor
  · intro h
    have := (Nat.ModEq.symm h)
    rw [Nat.ModEq] at this
    rw [Nat.mod_eq_of_lt ha] at this
    omega
  · intro h
    subst h
    exact Nat.mod_modEq _ _

lemma ortho_k (n k : ℕ) (hn : 0 < n) :
    ((k ^ 2 % n : ℕ):ℂ) = (1/(n:ℂ)) *
      ∑ a ∈ range n, (a:ℂ) * ∑ t ∈ range n, zeta n ^ ((t:ℤ) * ((k:ℤ) ^ 2 - a)) := by
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hinner : ∀ a ∈ range n, (∑ t ∈ range n, zeta n ^ ((t:ℤ) * ((k:ℤ) ^ 2 - a)))
      = if a = k ^ 2 % n then (n:ℂ) else 0 := by
    intro a ha
    rw [Finset.mem_range] at ha
    have he : (∑ t ∈ range n, zeta n ^ ((t:ℤ) * ((k:ℤ) ^ 2 - a)))
        = ∑ t ∈ range n, zeta n ^ (((k:ℤ) ^ 2 - a) * (t:ℤ)) := by
      apply Finset.sum_congr rfl; intro t _; rw [mul_comm]
    rw [he, geom_root_sumZ n hn]
    simp only [div_iff_mod n k a hn ha]
  rw [Finset.sum_congr rfl (fun a ha => by rw [hinner a ha])]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (range n) (k ^ 2 % n) (fun a => (a:ℂ) * (n:ℂ))]
  rw [if_pos (Finset.mem_range.mpr (Nat.mod_lt _ hn))]
  field_simp

lemma zeta_factor (n : ℕ) (t : ℤ) (k a : ℕ) :
    zeta n ^ (t * ((k:ℤ) ^ 2 - a)) = zeta n ^ (t * (k:ℤ) ^ 2) * zeta n ^ (-t * (a:ℤ)) := by
  rw [← zpow_add₀ (by rw [zeta]; exact Complex.exp_ne_zero _)]
  congr 1; ring

lemma S_formula (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range n, ((k ^ 2 % n : ℕ):ℂ))
      = (1/(n:ℂ)) * ∑ t ∈ range n,
          gs n t * (∑ a ∈ range n, (a:ℂ) * zeta n ^ (-t * (a:ℤ))) := by
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_congr rfl (fun k _ => ortho_k n k hn), ← Finset.mul_sum]
  congr 1
  -- ∑_k ∑_a a ∑_t zeta^(t(k²-a)) = ∑_t gs·∑_a a zeta^(-ta)
  -- first move everything to triple sum ∑_k ∑_a ∑_t a·zeta^(...)
  have step1 : (∑ k ∈ range n, ∑ a ∈ range n, (a:ℂ) * ∑ t ∈ range n, zeta n ^ ((t:ℤ) * ((k:ℤ) ^ 2 - a)))
      = ∑ t ∈ range n, ∑ k ∈ range n, ∑ a ∈ range n,
          zeta n ^ (t * (k:ℤ) ^ 2) * ((a:ℂ) * zeta n ^ (-t * (a:ℤ))) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro a _
    rw [zeta_factor]; ring
  rw [step1]
  apply Finset.sum_congr rfl; intro t _
  rw [gs, Finset.sum_mul_sum]

lemma zeta_zpow_ne_one (n : ℕ) (hn : 0 < n) (j : ℤ) (h : ¬(n:ℤ) ∣ j) : zeta n ^ j ≠ 1 := by
  intro hh
  apply h
  rw [zeta_zpow, Complex.exp_eq_one_iff] at hh
  obtain ⟨k, hk⟩ := hh
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_eq_iff hnc] at hk
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hj2 : (j:ℂ) = (k:ℂ) * n := mul_left_cancel₀ hpi (by linear_combination hk)
  have hz : (j:ℤ) = k * n := by exact_mod_cast hj2
  exact ⟨k, by rw [hz]; ring⟩

lemma zeta_zpow_pow_n (n : ℕ) (hn : 0 < n) (j : ℤ) : (zeta n ^ j) ^ n = 1 := by
  rw [← zpow_natCast (zeta n ^ j) n, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    zeta_pow_n n hn, one_zpow]

lemma gs_zero (n : ℕ) : gs n 0 = n := by
  simp [gs]

lemma inner_sum_pos (n t : ℕ) (hn : 0 < n) (ht : 1 ≤ t) (htn : t < n) :
    ∑ a ∈ range n, (a:ℂ) * zeta n ^ (-(t:ℤ) * (a:ℤ)) = n / (zeta n ^ (-(t:ℤ)) - 1) := by
  have hz1 : zeta n ^ (-(t:ℤ)) ≠ 1 := by
    apply zeta_zpow_ne_one n hn
    rw [Int.dvd_neg]
    intro hd
    have := Int.le_of_dvd (by exact_mod_cast ht) hd
    omega
  have hzn := zeta_zpow_pow_n n hn (-(t:ℤ))
  have hrw : ∑ a ∈ range n, (a:ℂ) * zeta n ^ (-(t:ℤ) * (a:ℤ))
      = ∑ a ∈ range n, (a:ℂ) * (zeta n ^ (-(t:ℤ))) ^ a := by
    apply Finset.sum_congr rfl; intro a _; rw [zpow_mul, zpow_natCast]
  rw [hrw, eq_div_iff (sub_ne_zero.mpr hz1)]
  linear_combination deriv_root_sum (zeta n ^ (-(t:ℤ))) n hn hzn hz1

lemma sum_range_cast (n : ℕ) (hn : 0 < n) :
    (∑ a ∈ range n, (a:ℂ)) = (n:ℂ) * ((n:ℂ) - 1) / 2 := by
  have h := Finset.sum_range_id_mul_two n
  have hc : (∑ a ∈ range n, (a:ℂ)) * 2 = (n:ℂ) * ((n:ℂ) - 1) := by
    have := congrArg (fun x : ℕ => (x:ℂ)) h
    push_cast at this
    rw [show ((n:ℂ) - 1) = ((n - 1 : ℕ):ℂ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    push_cast
    convert this using 2
  linear_combination hc / 2

lemma S_formula_final (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range n, ((k ^ 2 % n : ℕ):ℂ))
      = (n:ℂ) * ((n:ℂ) - 1) / 2 + ∑ t ∈ Finset.Ico 1 n, gs n t / (zeta n ^ (-(t:ℤ)) - 1) := by
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [S_formula n hn]
  nth_rewrite 1 [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ n), mul_add]
  congr 1
  · rw [show Finset.Ico 0 1 = {0} from rfl, Finset.sum_singleton, Nat.cast_zero, gs_zero]
    have h0 : ∑ a ∈ range n, (a:ℂ) * zeta n ^ (-(0:ℤ) * (a:ℤ)) = (n:ℂ) * ((n:ℂ) - 1) / 2 := by
      rw [← sum_range_cast n hn]
      apply Finset.sum_congr rfl; intro a _
      simp
    rw [h0]
    field_simp
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t ht
    rw [Finset.mem_Ico] at ht
    rw [inner_sum_pos n t hn ht.1 ht.2]
    field_simp

lemma cot_identity (n t : ℕ) (hn : 0 < n) (ht : 1 ≤ t) (htn : t < n) :
    (zeta n ^ (-(t:ℤ)) + 1) / (zeta n ^ (-(t:ℤ)) - 1)
      = I * Complex.cot (π * t / n) := by
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set θ : ℂ := π * t / n with hθ
  have hz : zeta n ^ (-(t:ℤ)) = (Complex.exp (2 * I * θ))⁻¹ := by
    rw [zeta_zpow, ← Complex.exp_neg]
    congr 1
    push_cast
    rw [hθ]; field_simp
  have hw1 : Complex.exp (2 * I * θ) ≠ 1 := by
    rw [show 2 * I * θ = 2 * Real.pi * I * ((t:ℤ):ℂ) / n by rw [hθ]; push_cast; ring,
      ← zeta_zpow]
    apply zeta_zpow_ne_one n hn
    intro hdvd
    have := Int.le_of_dvd (by exact_mod_cast ht) hdvd
    omega
  rw [Complex.cot_eq_exp_ratio, hz]
  have hwne : Complex.exp (2 * I * θ) ≠ 0 := Complex.exp_ne_zero _
  have hw1' : Complex.exp (2 * I * θ) - 1 ≠ 0 := sub_ne_zero.mpr hw1
  field_simp
  ring

lemma dvd_sq_iff (n k : ℕ) : (n:ℤ) ∣ (k:ℤ) ^ 2 ↔ k ^ 2 % n = 0 := by
  rw [show ((k:ℤ) ^ 2) = ((k ^ 2 : ℕ):ℤ) by push_cast; ring, Int.natCast_dvd_natCast,
    Nat.dvd_iff_mod_eq_zero]

lemma Z_formula (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range n, (if (n:ℤ) ∣ (k:ℤ) ^ 2 then (1:ℂ) else 0))
      = 1 + (1/(n:ℂ)) * ∑ t ∈ Finset.Ico 1 n, gs n t := by
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hind : ∀ (k : ℕ), (if (n:ℤ) ∣ (k:ℤ) ^ 2 then (1:ℂ) else 0)
      = (1/(n:ℂ)) * ∑ t ∈ range n, zeta n ^ ((t:ℤ) * (k:ℤ) ^ 2) := by
    intro k
    have he : (∑ t ∈ range n, zeta n ^ ((t:ℤ) * (k:ℤ) ^ 2))
        = ∑ t ∈ range n, zeta n ^ ((k:ℤ) ^ 2 * (t:ℤ)) := by
      apply Finset.sum_congr rfl; intro t _; rw [mul_comm]
    rw [he, geom_root_sumZ n hn]
    by_cases h : (n:ℤ) ∣ (k:ℤ) ^ 2 <;> simp [h, hnc]
  rw [Finset.sum_congr rfl (fun k _ => hind k), ← Finset.mul_sum]
  have hswap : (∑ k ∈ range n, ∑ t ∈ range n, zeta n ^ ((t:ℤ) * (k:ℤ) ^ 2))
      = ∑ t ∈ range n, gs n t := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro t _; rw [gs]
  rw [hswap]
  nth_rewrite 1 [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ n)]
  rw [show Finset.Ico 0 1 = {0} from rfl, Finset.sum_singleton, Nat.cast_zero, gs_zero]
  field_simp

lemma Wcount_C (n : ℕ) (hn : 0 < n) :
    ((Finset.filter (fun k => k ^ 2 % n ≠ 0) (range n)).card : ℂ)
      = (n:ℂ) - ∑ k ∈ range n, (if (n:ℤ) ∣ (k:ℤ) ^ 2 then (1:ℂ) else 0) := by
  have hind : (∑ k ∈ range n, (if (n:ℤ) ∣ (k:ℤ) ^ 2 then (1:ℂ) else 0))
      = ((Finset.filter (fun k => k ^ 2 % n = 0) (range n)).card : ℂ) := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl; intro k _
    simp only [dvd_sq_iff]
  rw [hind]
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := range n) (p := fun k => k ^ 2 % n ≠ 0)
  rw [Finset.card_range] at hpart
  have : ((Finset.filter (fun k => ¬ k ^ 2 % n ≠ 0) (range n)).card)
      = (Finset.filter (fun k => k ^ 2 % n = 0) (range n)).card := by
    congr 1; apply Finset.filter_congr; intro k _; simp
  rw [this] at hpart
  have hc : ((Finset.filter (fun k => k ^ 2 % n ≠ 0) (range n)).card : ℂ)
      + ((Finset.filter (fun k => k ^ 2 % n = 0) (range n)).card : ℂ) = (n:ℂ) := by
    exact_mod_cast hpart
  linear_combination hc

lemma D_complex (n : ℕ) (hn : 0 < n) :
    (n:ℂ) * ((Finset.filter (fun k => k ^ 2 % n ≠ 0) (range n)).card)
        - 2 * (∑ k ∈ range n, ((k ^ 2 % n : ℕ):ℂ))
      = -∑ t ∈ Finset.Ico 1 n, gs n t * (I * Complex.cot (π * t / n)) := by
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : ∀ t ∈ Finset.Ico 1 n, gs n t * (I * Complex.cot (π * ↑t / ↑n))
      = gs n t + 2 * (gs n t / (zeta n ^ (-(t:ℤ)) - 1)) := by
    intro t ht; rw [Finset.mem_Ico] at ht
    rw [← cot_identity n t hn ht.1 ht.2]
    have hz1 : zeta n ^ (-(t:ℤ)) - 1 ≠ 0 := by
      apply sub_ne_zero.mpr; apply zeta_zpow_ne_one n hn; rw [Int.dvd_neg]
      intro hd; have := Int.le_of_dvd (by exact_mod_cast ht.1) hd; omega
    field_simp; ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Wcount_C n hn, Z_formula n hn, S_formula_final n hn]
  field_simp
  ring

lemma D_real (n : ℕ) (hn : 0 < n) :
    (n:ℝ) * ((Finset.filter (fun k => k ^ 2 % n ≠ 0) (range n)).card : ℝ)
        - 2 * (∑ k ∈ range n, ((k ^ 2 % n : ℕ):ℝ))
      = ∑ t ∈ Finset.Ico 1 n, (gs n t).im * Real.cot (Real.pi * t / n) := by
  have hcot : ∀ t : ℕ, Complex.cot ((π:ℂ) * t / n) = ((Real.cot (Real.pi * t / n) : ℝ):ℂ) := by
    intro t
    rw [show ((π:ℂ) * t / n) = ((Real.pi * (t:ℝ) / n : ℝ):ℂ) by push_cast; ring,
      Complex.ofReal_cot]
  have h := D_complex n hn
  have hLeq : (n:ℂ) * ((Finset.filter (fun k => k ^ 2 % n ≠ 0) (range n)).card)
        - 2 * (∑ k ∈ range n, ((k ^ 2 % n : ℕ):ℂ))
      = (((n:ℝ) * ((Finset.filter (fun k => k ^ 2 % n ≠ 0) (range n)).card : ℝ)
        - 2 * (∑ k ∈ range n, ((k ^ 2 % n : ℕ):ℝ)) : ℝ):ℂ) := by push_cast; ring
  have h2 := congrArg Complex.re h
  rw [hLeq, Complex.ofReal_re, Complex.neg_re, Complex.re_sum] at h2
  rw [h2, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro t _
  simp only [hcot, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub, mul_one,
    neg_mul, neg_neg]
  ring

lemma periodic_sum (m : ℕ) (f : ℕ → ℂ) (hf : ∀ k, f (k + m) = f k) (d : ℕ) :
    ∑ k ∈ range (d * m), f k = d • ∑ k ∈ range m, f k := by
  have hper : ∀ e k, f (e * m + k) = f k := by
    intro e
    induction e with
    | zero => simp
    | succ p ih => intro k; rw [Nat.succ_mul, show p * m + m + k = (p*m+k) + m by ring, hf, ih]
  induction d with
  | zero => simp
  | succ e ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    apply Finset.sum_congr rfl; intro k _
    rw [show e * m + k = e * m + k from rfl, hper]

lemma zeta_div_pow (n d : ℕ) (hd : d ∣ n) (j : ℤ) :
    zeta (n / d) ^ j = zeta n ^ (d * j) := by
  obtain ⟨m, rfl⟩ := hd
  by_cases hd0 : d = 0
  · subst hd0; simp [zeta]
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  rw [zeta_zpow, zeta_zpow]
  congr 1
  have hdc : (d:ℂ) ≠ 0 := by exact_mod_cast hd0
  push_cast
  rw [mul_div_assoc (2 * ↑π * I), mul_div_assoc (2 * ↑π * I), mul_div_mul_left _ _ hdc]

end S5

section GaussSection
open Finset Complex Real Filter
open scoped Real Topology

/-- Gaussian summability over `ℤ`. -/
lemma summable_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℤ => Real.exp (-c * m ^ 2)) := by
  have him : (0:ℝ) < ((c/π : ℝ) * Complex.I).im := by
    simp [Complex.mul_im]; positivity
  have hsum := (summable_jacobiTheta₂_term_iff (0:ℂ) ((c/π : ℝ) * Complex.I)).mpr him
  rw [← summable_norm_iff] at hsum
  refine hsum.congr (fun m => ?_)
  rw [jacobiTheta₂_term, Complex.norm_exp]
  rw [show (2 * π * I * m * 0 + π * I * m ^ 2 * ((c/π : ℝ) * Complex.I)) = (((-c * m ^ 2 : ℝ)):ℂ) by
    push_cast; field_simp; ring_nf; rw [Complex.I_sq]; ring]
  exact (Complex.ofReal_re _).symm ▸ rfl

/-- Norm of the dual theta term. -/
lemma dual_term_norm (t : ℝ) (ht : 0 < t) (x : ℝ) (m : ℤ) :
    ‖Complex.exp (-π * m ^ 2 / t) * Complex.exp (2 * π * I * m * x)‖ = Real.exp (-π * m ^ 2 / t) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  have h1 : (-(π:ℂ) * m ^ 2 / t).re = -π * m ^ 2 / t := by
    rw [show (-(π:ℂ) * m ^ 2 / t) = (((-π * m ^ 2 / t : ℝ)):ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have h2 : (2 * (π:ℂ) * I * m * x).re = 0 := by
    rw [show (2 * (π:ℂ) * I * m * x) = ((2*π*m*x : ℝ):ℂ) * I by push_cast; ring]
    simp
  rw [h1, h2, Real.exp_zero, mul_one]

/-- Summability of the dual theta term norms. -/
lemma summable_dual_norm (t : ℝ) (ht : 0 < t) (x : ℝ) :
    Summable (fun m : ℤ => ‖Complex.exp (-π * m ^ 2 / t) * Complex.exp (2 * π * I * m * x)‖) := by
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => le_of_eq (dual_term_norm t ht x m))
  -- ∑ exp(-πm²/t) summable. Compare to jacobiTheta₂ term summability.
  have : (0:ℝ) < (Complex.I / t).im := by simp [Complex.div_im, ht]
  have hsum := (summable_jacobiTheta₂_term_iff (0:ℂ) (Complex.I / t)).mpr this
  rw [← summable_norm_iff] at hsum
  refine hsum.congr (fun m => ?_)
  rw [jacobiTheta₂_term, Complex.norm_exp]
  congr 1
  rw [show (2 * π * I * m * 0 + π * I * m ^ 2 * (Complex.I / t)) = (((-π * m ^ 2 / t : ℝ)):ℂ) by
    push_cast; rw [div_eq_mul_inv]; ring_nf; rw [Complex.I_sq]; ring]
  exact Complex.ofReal_re _

/-- The dual theta sum `g(t,x) := ∑ₘ exp(-πm²/t) exp(2πImx)` tends to `1` as `t → 0⁺`. -/
theorem dual_theta_tendsto_one (x : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => ∑' m : ℤ, Complex.exp (-π * m ^ 2 / t) * Complex.exp (2 * π * I * m * x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hlim : (1 : ℂ) = ∑' m : ℤ, (if m = 0 then (1:ℂ) else 0) := (tsum_ite_eq 0 1).symm
  rw [hlim]
  apply tendsto_tsum_of_dominated_convergence (bound := fun m : ℤ => Real.exp (-π * m ^ 2))
  · exact summable_exp_neg_mul_sq Real.pi_pos
  · intro m
    by_cases hm : m = 0
    · subst hm
      simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, zero_div, neg_zero, Complex.exp_zero, mul_zero, one_mul, if_pos]
      simpa using tendsto_const_nhds
    · simp only [if_neg hm]
      have hc : 0 < π * (m:ℝ) ^ 2 := by
        have : (m:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
        positivity
      have hinv : Filter.Tendsto (fun t : ℝ => t⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
        tendsto_inv_nhdsGT_zero
      have h2 : Filter.Tendsto (fun t : ℝ => π * (m:ℝ) ^ 2 * t⁻¹) (nhdsWithin 0 (Set.Ioi 0))
          Filter.atTop := hinv.const_mul_atTop hc
      have h3 : Filter.Tendsto (fun t : ℝ => -π * (m:ℝ) ^ 2 / t) (nhdsWithin 0 (Set.Ioi 0))
          Filter.atBot := by
        have := tendsto_neg_atTop_atBot.comp h2
        refine this.congr (fun t => ?_)
        simp only [Function.comp_apply]; ring
      have h4 : Filter.Tendsto (fun t : ℝ => Real.exp (-π * (m:ℝ) ^ 2 / t))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := Real.tendsto_exp_atBot.comp h3
      have h5 : Filter.Tendsto (fun t : ℝ => Complex.exp (-π * (m:ℂ) ^ 2 / t))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hcomp := (Complex.continuous_ofReal.tendsto 0).comp h4
        simp only [Complex.ofReal_zero] at hcomp
        refine hcomp.congr (fun t => ?_)
        rw [Function.comp_apply, Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      have : (0:ℂ) = Complex.exp (2 * π * I * m * x) * 0 := by ring
      rw [this]
      exact (h5.const_mul _).congr (fun t => by ring)
  · have h_lt1 : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
      Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num)))
        (fun t ht => ht)
    filter_upwards [self_mem_nhdsWithin, h_lt1] with t ht0 ht1 m
    rw [dual_term_norm t ht0 x m, Real.exp_le_exp]
    have ht0' : (0:ℝ) < t := ht0
    have hmsq : (0:ℝ) ≤ (m:ℝ) ^ 2 := sq_nonneg _
    rw [div_le_iff₀ ht0']
    have hp : (0:ℝ) ≤ π * (m:ℝ) ^ 2 := mul_nonneg Real.pi_pos.le hmsq
    nlinarith [mul_nonneg hp (by linarith : (0:ℝ) ≤ 1 - t)]

/-- Complex version of the theta transformation, the cleaner object to work with. -/
theorem theta_complex_transform (α : ℝ) (hα : 0 < α) (x : ℝ) :
    (∑' m : ℤ, Complex.exp (-(α:ℂ) * (m + x) ^ 2)) =
      Real.sqrt (π / α) * ∑' m : ℤ, Complex.exp (-π ^ 2 * m ^ 2 / α)
        * Complex.exp (2 * π * I * m * x) := by
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hα' : (α:ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have ha : 0 < ((α:ℂ)/π).re := by
    rw [div_re]; simp [Complex.normSq]; positivity
  have key := Complex.tsum_exp_neg_quadratic ha (-(α*x)/π : ℝ)
  -- Step 1: rewrite LHS as cexp(-αx²) * (key's LHS sum)
  have hL : (∑' m : ℤ, Complex.exp (-(α:ℂ) * (m + x) ^ 2)) =
      Complex.exp (-(α:ℂ)*x^2) *
        ∑' m : ℤ, Complex.exp (-π * ((α:ℂ)/π) * m ^ 2 + 2 * π * ((-(α*x)/π : ℝ):ℂ) * m) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [hL, key]
  -- Step 2: simplify constant and RHS sum
  have hconst : (1 : ℂ) / ((α:ℂ)/π) ^ (1/2 : ℂ) = (Real.sqrt (π/α) : ℂ) := by
    rw [show ((α:ℂ)/π) = (((α/π : ℝ)):ℂ) by push_cast; ring,
        show (1/2 : ℂ) = (((1/2 : ℝ)):ℂ) by norm_num,
        ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_one, ← Complex.ofReal_div]
    rw [Real.sqrt_eq_rpow]
    congr 1
    rw [one_div, ← Real.inv_rpow (by positivity), inv_div]
  -- Now combine the cexp(-αx²) constant with the sum
  rw [hconst, mul_left_comm]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hb : ((-(α*x)/π : ℝ):ℂ) = -((α:ℂ)*x)/π := by push_cast; ring
  rw [hb]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The shifted theta tends to `1/√t`-scaled: `√t·∑ₘ exp(-πt(m+x)²) → 1`. -/
theorem shifted_theta_asymp (x : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => (Real.sqrt t : ℂ) * ∑' m : ℤ, Complex.exp (-(π * t : ℝ) * (m + x) ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have key : ∀ t : ℝ, 0 < t →
      (Real.sqrt t : ℂ) * ∑' m : ℤ, Complex.exp (-(π * t : ℝ) * (m + x) ^ 2) =
        ∑' m : ℤ, Complex.exp (-π * m ^ 2 / t) * Complex.exp (2 * π * I * m * x) := by
    intro t ht
    have he : ((π * t : ℝ) : ℂ) = ((π * t : ℝ) : ℂ) := rfl
    rw [show (fun m : ℤ => Complex.exp (-(π * t : ℝ) * (m + x) ^ 2))
          = (fun m : ℤ => Complex.exp (-((π*t:ℝ):ℂ) * (m + x) ^ 2)) from rfl]
    rw [theta_complex_transform (π * t) (by positivity) x, ← mul_assoc]
    have hsqrt : (Real.sqrt t : ℂ) * (Real.sqrt (π / (π * t)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul ht.le,
        show t * (π / (π * t)) = 1 by field_simp]
      simp
    rw [hsqrt, one_mul]
    refine tsum_congr (fun m => ?_)
    congr 1
    congr 1
    push_cast
    field_simp
  apply Filter.Tendsto.congr' _ (dual_theta_tendsto_one x)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (key t ht).symm

/-- The classical quadratic Gauss sum `g(N) = ∑_{k<N} exp(2πik²/N)`. -/
noncomputable def gaussSumC (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N)

/-- The regularized theta `G(N,ε) = ∑_{n∈ℤ} exp(-π(ε - 2i/N)n²)`. -/
noncomputable def Gtheta (N : ℕ) (ε : ℝ) : ℂ :=
  ∑' n : ℤ, Complex.exp (-(π:ℂ) * ((ε:ℂ) - 2 * I / N) * n ^ 2)

/-- Norm of the regularized theta term. -/
lemma Greg_term_norm (N : ℕ) (ε : ℝ) (n : ℤ) :
    ‖Complex.exp (-(π:ℂ) * ((ε:ℂ) - 2 * I / N) * n ^ 2)‖ = Real.exp (-(π * ε) * n ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  have : (-(π:ℂ) * ((ε:ℂ) - 2 * I / N) * n ^ 2)
      = (((-(π*ε)*n^2 : ℝ)):ℂ) + (2 * π / N * n ^ 2 : ℝ) * I := by
    push_cast; ring
  rw [this, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
  ring

/-- Summability of the regularized theta term. -/
lemma summable_Greg (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    Summable (fun n : ℤ => Complex.exp (-(π:ℂ) * ((ε:ℂ) - 2 * I / N) * n ^ 2)) := by
  rw [← summable_norm_iff]
  apply (summable_exp_neg_mul_sq (c := π * ε) (by positivity)).congr
  intro n
  rw [Greg_term_norm]

/-- Period-N regrouping of the regularized theta. -/
theorem Gtheta_decomp (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    Gtheta N ε = ∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N) *
      ∑' m : ℤ, Complex.exp (-(π * ε : ℝ) * (k + N * m) ^ 2) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  set F : ℤ → ℂ := fun n => Complex.exp (-(π:ℂ) * ((ε:ℂ) - 2 * I / N) * n ^ 2) with hF
  have hsum : Summable F := summable_Greg N hN ε hε
  have hsum2 : Summable (fun p : ℤ × Fin N => F ((Int.divModEquiv N).symm p)) :=
    hsum.comp_injective (Int.divModEquiv N).symm.injective
  -- term identity: F(q*N + r) = exp(2πi r²/N) · exp(-(πε)(r+Nq)²)
  have hterm : ∀ (q : ℤ) (r : Fin N),
      F ((Int.divModEquiv N).symm (q, r)) =
        Complex.exp (2 * π * I * (r:ℕ) ^ 2 / N) *
          Complex.exp (-(π * ε : ℝ) * ((r:ℕ) + N * q) ^ 2) := by
    intro q r
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hsymm : (Int.divModEquiv N).symm (q, r) = q * (N:ℤ) + (r:ℕ) := rfl
    rw [show Complex.exp (2 * π * I * (r:ℕ) ^ 2 / N)
            * Complex.exp (-(π * ε : ℝ) * ((r:ℕ) + N * q) ^ 2)
          = Complex.exp (2 * π * I * (r:ℕ) ^ 2 / N + -(π * ε : ℝ) * ((r:ℕ) + N * q) ^ 2)
        from (Complex.exp_add _ _).symm]
    rw [hF]
    simp only [hsymm]
    rw [show (((q * (N:ℤ) + (r:ℕ) : ℤ)):ℂ) = (q:ℂ) * N + (r:ℕ) from by push_cast; ring]
    rw [show -(π:ℂ) * ((ε:ℂ) - 2 * I / N) * ((q:ℂ) * N + (r:ℕ)) ^ 2
          = (2 * π * I * (r:ℕ) ^ 2 / N + -(π * ε : ℝ) * ((r:ℕ) + N * q) ^ 2)
            + ((q ^ 2 * N + 2 * q * (r:ℕ) : ℤ) : ℂ) * (2 * π * I)
        from by push_cast; field_simp [hNc]; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- regroup via n = q*N + r
  unfold Gtheta
  rw [← hF, ← (Int.divModEquiv N).symm.tsum_eq F]
  rw [hsum2.tsum_prod' (fun q => (hasSum_fintype
        (fun r : Fin N => F ((Int.divModEquiv N).symm (q, r)))).summable)]
  simp_rw [tsum_fintype]
  rw [Summable.tsum_finsetSum (fun r _ => ?_)]
  · -- reindex Fin N → range N
    rw [← Fin.sum_univ_eq_sum_range (fun k => Complex.exp (2 * π * I * k ^ 2 / N) *
          ∑' m : ℤ, Complex.exp (-(π * ε : ℝ) * (k + N * m) ^ 2))]
    apply Finset.sum_congr rfl
    intro r _
    rw [← tsum_mul_left]
    refine tsum_congr (fun q => ?_)
    rw [hterm q r]
  · -- summability of q ↦ F(symm(q,r)) for fixed r
    exact hsum2.comp_injective (fun a b h => by simpa using h)

-- The LHS limit: `√ε · Gtheta(N,ε) → gaussSumC(N)/N` as `ε → 0⁺`.
set_option maxHeartbeats 1000000 in
theorem sqrt_eps_Gtheta_limit (N : ℕ) (hN : 0 < N) :
    Filter.Tendsto (fun ε : ℝ => (Real.sqrt ε : ℂ) * Gtheta N ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (gaussSumC N / N)) := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNr' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  -- ε ↦ ε·N² maps the punctured nbhd to itself
  have htN : Filter.Tendsto (fun ε : ℝ => ε * (N:ℝ) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Filter.Tendsto (fun ε : ℝ => ε * (N:ℝ) ^ 2) (nhds 0) (nhds 0) := by
        have := (continuous_mul_right ((N:ℝ) ^ 2)).tendsto 0; simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : 0 < ε := hε
      exact mul_pos hε' (by positivity)
  -- for each k, the inner shifted theta (scaled) tends to 1
  have hk : ∀ k : ℕ,
      Filter.Tendsto (fun ε : ℝ => (Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ) *
        ∑' m : ℤ, Complex.exp (-(π * (ε * (N:ℝ) ^ 2) : ℝ) * (m + (k:ℝ) / N) ^ 2))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    intro k
    refine Filter.Tendsto.congr (fun ε => ?_) ((shifted_theta_asymp ((k:ℝ) / N)).comp htN)
    simp only [Function.comp_apply]
    refine congrArg (HMul.hMul (Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ)) (tsum_congr (fun m => ?_))
    congr 1
    push_cast
    ring
  -- inner term identity
  have hinner : ∀ ε : ℝ, 0 < ε → ∀ k : ℕ,
      (Real.sqrt ε : ℂ) * ∑' m : ℤ, Complex.exp (-(π * ε : ℝ) * (k + N * m) ^ 2) =
        (1 / N) * ((Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ) *
          ∑' m : ℤ, Complex.exp (-(π * (ε * (N:ℝ) ^ 2) : ℝ) * (m + (k:ℝ) / N) ^ 2)) := by
    intro ε hε k
    have hcoef : (Real.sqrt ε : ℂ) = (1 / N) * (Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ) := by
      rw [Real.sqrt_mul hε.le, Real.sqrt_sq hNr.le, Complex.ofReal_mul,
        Complex.ofReal_natCast]
      field_simp
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    have hA : Complex.exp (-(π * ε : ℝ) * ((k:ℂ) + N * m) ^ 2) =
        Complex.exp (-(π * (ε * (N:ℝ) ^ 2) : ℝ) * ((m:ℂ) + (k:ℝ) / N) ^ 2) := by
      congr 1
      push_cast
      field_simp
      ring
    rw [hA, hcoef]
    ring
  -- rewrite √ε·Gtheta as a finite sum of these
  have hrw : ∀ ε : ℝ, 0 < ε →
      (Real.sqrt ε : ℂ) * Gtheta N ε =
        ∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N) *
          ((1 / N) * ((Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ) *
            ∑' m : ℤ, Complex.exp (-(π * (ε * (N:ℝ) ^ 2) : ℝ) * (m + (k:ℝ) / N) ^ 2))) := by
    intro ε hε
    rw [Gtheta_decomp N hN ε hε, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_left_comm, hinner ε hε k]
  -- conclude
  have hlim : Filter.Tendsto
      (fun ε : ℝ => ∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N) *
          ((1 / N) * ((Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ) *
            ∑' m : ℤ, Complex.exp (-(π * (ε * (N:ℝ) ^ 2) : ℝ) * (m + (k:ℝ) / N) ^ 2))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N) * ((1 / N) * 1))) := by
    apply tendsto_finset_sum
    intro k _
    exact (((hk k).const_mul ((1:ℂ) / N)).const_mul (Complex.exp (2 * π * I * k ^ 2 / N)))
  have heq : (∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N) * ((1 / N) * 1))
      = gaussSumC N / N := by
    unfold gaussSumC
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_one]
    field_simp
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hrw ε hε).symm

-- Complex shifted theta limit: if `s ε → 0` with `Re(s ε) > 0` and `Re(1/s ε) → ∞`,
-- then `(s ε)^{1/2} · ∑ₘ exp(-π s ε (m+x)²) → 1`. Complex analogue of `shifted_theta_asymp`.
set_option maxHeartbeats 1000000 in
theorem complex_shifted_theta (x : ℝ) (l : Filter ℝ) (s : ℝ → ℂ)
    (hs : Filter.Tendsto s l (nhds 0)) (hre : ∀ᶠ ε in l, 0 < (s ε).re)
    (hdom : Filter.Tendsto (fun ε => (s ε).re / Complex.normSq (s ε)) l Filter.atTop) :
    Filter.Tendsto (fun ε => (s ε) ^ (1/2 : ℂ) *
        ∑' m : ℤ, Complex.exp (-π * (s ε) * (m + x) ^ 2)) l (nhds 1) := by
  -- Poisson transform pointwise (where Re(s ε) > 0)
  have key : ∀ᶠ ε in l, (s ε) ^ (1/2 : ℂ) *
        ∑' m : ℤ, Complex.exp (-π * (s ε) * (m + x) ^ 2)
      = Complex.exp (-π * (s ε) * x ^ 2) *
          ∑' n : ℤ, Complex.exp (-π / (s ε) * (n - I * (s ε) * x) ^ 2) := by
    filter_upwards [hre] with ε hε
    have hP := Complex.tsum_exp_neg_quadratic hε (-(s ε) * x)
    -- ∑ exp(-π s m² + 2π(-s x) m) = 1/s^{1/2} ∑ exp(-π/s (n + I(-s x))²)
    have hLHS : ∑' m : ℤ, Complex.exp (-π * (s ε) * (m + x) ^ 2)
        = Complex.exp (-π * (s ε) * x ^ 2) *
          ∑' m : ℤ, Complex.exp (-π * (s ε) * m ^ 2 + 2 * π * (-(s ε) * x) * m) := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun m => ?_)
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hLHS, hP]
    rw [mul_comm ((s ε) ^ (1/2 : ℂ)), mul_assoc]
    congr 1
    rw [mul_comm, ← mul_assoc]
    rw [show (s ε) ^ (1/2 : ℂ) * (1 / (s ε) ^ (1/2 : ℂ)) = 1 from ?_, one_mul]
    · refine tsum_congr (fun n => ?_)
      congr 2
      ring
    · rw [mul_one_div, div_self]
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      left
      intro h0
      rw [h0] at hε
      simp at hε
  rw [tendsto_congr' key]
  -- limit of product: exp(-π s x²) → 1, dual sum → 1
  have h1 : Filter.Tendsto (fun ε => Complex.exp (-π * (s ε) * x ^ 2)) l (nhds 1) := by
    have : Filter.Tendsto (fun ε => -π * (s ε) * x ^ 2) l (nhds 0) := by
      have := (hs.const_mul (-(π:ℂ))).mul_const ((x:ℂ) ^ 2)
      simpa using this
    have hc := (Complex.continuous_exp.tendsto 0).comp this
    simpa using hc
  have hre0 : Filter.Tendsto (fun ε => (s ε).re) l (nhds 0) :=
    (Complex.continuous_re.tendsto 0).comp hs
  -- norm of the dual term
  have hnorm : ∀ n : ℤ, ∀ ε, 0 < (s ε).re →
      ‖Complex.exp (-π / (s ε) * (n - I * (s ε) * x) ^ 2)‖
      = Real.exp (-π * n ^ 2 * ((s ε).re / Complex.normSq (s ε)) + π * x ^ 2 * (s ε).re) := by
    intro n ε hε
    have hsne : s ε ≠ 0 := fun h => by rw [h] at hε; simp at hε
    rw [Complex.norm_exp]
    congr 1
    rw [show -π / (s ε) * ((n:ℂ) - I * (s ε) * x) ^ 2
          = ((-π * (n:ℝ) ^ 2 : ℝ):ℂ) * (s ε)⁻¹ + ((2 * π * (n:ℝ) * x : ℝ):ℂ) * I
            + ((π * x ^ 2 : ℝ):ℂ) * (s ε) by
        field_simp
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring]
    rw [Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
        Complex.re_ofReal_mul, Complex.inv_re]
    simp only [Complex.I_re, mul_zero, add_zero]
  have h2 : Filter.Tendsto
      (fun ε => ∑' n : ℤ, Complex.exp (-π / (s ε) * (n - I * (s ε) * x) ^ 2)) l (nhds 1) := by
    have hbound : Summable (fun n : ℤ => Real.exp (π * x ^ 2) * Real.exp (-π * n ^ 2)) :=
      (summable_exp_neg_mul_sq Real.pi_pos).mul_left _
    rw [show (1 : ℂ) = ∑' n : ℤ, (if n = 0 then (1:ℂ) else 0) from (tsum_ite_eq 0 1).symm]
    apply tendsto_tsum_of_dominated_convergence hbound
    · -- pointwise limits
      intro n
      by_cases hn : n = 0
      · subst hn
        simp only [↓reduceIte]
        have hlim0 : Filter.Tendsto
            (fun ε => -π / (s ε) * ((0:ℤ) - I * (s ε) * x) ^ 2) l (nhds 0) := by
          have heq2 : (fun ε => -π / (s ε) * ((0:ℤ) - I * (s ε) * x) ^ 2)
              = (fun ε => π * (s ε) * x ^ 2) := by
            funext ε
            by_cases h0 : s ε = 0
            · simp [h0]
            · field_simp
              ring_nf
              rw [Complex.I_sq]; ring
          rw [heq2]
          have := (hs.const_mul ((π:ℂ))).mul_const ((x:ℂ) ^ 2)
          simpa using this
        have hc := (Complex.continuous_exp.tendsto 0).comp hlim0
        simpa using hc
      · simp only [if_neg hn]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        -- ‖T_n‖ = exp(A ε) with A ε → -∞
        have hAtend : Filter.Tendsto
            (fun ε => -π * (n:ℝ) ^ 2 * ((s ε).re / Complex.normSq (s ε)) + π * x ^ 2 * (s ε).re)
            l Filter.atBot := by
          have hne : (n:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
          have hpos : (0:ℝ) < π * (n:ℝ) ^ 2 := by positivity
          have hfirst : Filter.Tendsto
              (fun ε => -(π * (n:ℝ) ^ 2) * ((s ε).re / Complex.normSq (s ε))) l Filter.atBot :=
            Filter.Tendsto.const_mul_atTop_of_neg (by linarith) hdom
          have hsecond : Filter.Tendsto (fun ε => (π * x ^ 2) * (s ε).re) l (nhds 0) := by
            have := hre0.const_mul (π * x ^ 2); simpa using this
          refine (hfirst.atBot_add hsecond).congr (fun ε => ?_)
          ring
        refine Filter.Tendsto.congr' ?_ (Real.tendsto_exp_atBot.comp hAtend)
        filter_upwards [hre] with ε hε
        rw [Function.comp_apply, hnorm n ε hε]
    · -- domination
      have hsre1 : ∀ᶠ ε in l, (s ε).re ≤ 1 :=
        hre0.eventually (eventually_le_nhds (by norm_num))
      filter_upwards [hre, hdom.eventually_ge_atTop 1, hsre1] with ε hε hdomε hsre n
      rw [hnorm n ε hε]
      have hb : Real.exp (π * x ^ 2) * Real.exp (-π * n ^ 2)
          = Real.exp (π * x ^ 2 + -π * n ^ 2) := (Real.exp_add _ _).symm
      rw [hb, Real.exp_le_exp]
      have hpi : (0:ℝ) < π := Real.pi_pos
      have hn2 : (0:ℝ) ≤ (n:ℝ) ^ 2 := sq_nonneg _
      have hx2 : (0:ℝ) ≤ x ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hpi.le hn2) (by linarith : (0:ℝ) ≤ (s ε).re / Complex.normSq (s ε) - 1),
        mul_nonneg (mul_nonneg hpi.le hx2) (by linarith : (0:ℝ) ≤ 1 - (s ε).re)]
  have := h1.mul h2
  simpa using this

/-- Poisson dual of `Gtheta`: with `b = ε - 2i/N` (so `Re b = ε > 0`),
`Gtheta N ε = b^{-1/2} · ∑ₙ exp(-π n²/b)`. -/
lemma Gtheta_poisson (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Gtheta N ε = 1 / ((ε:ℂ) - 2 * I / N) ^ (1/2 : ℂ) *
      ∑' n : ℤ, Complex.exp (-(π:ℂ) / ((ε:ℂ) - 2 * I / N) * n ^ 2) := by
  have hre : 0 < ((ε:ℂ) - 2 * I / N).re := by
    have : ((ε:ℂ) - 2 * I / N).re = ε := by
      simp [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im]
    rw [this]; exact hε
  unfold Gtheta
  exact Complex.tsum_exp_neg_mul_int_sq hre

/-- Norm of the dual term. -/
lemma dual_term_norm2 (b : ℂ) (n : ℤ) :
    ‖Complex.exp (-(π:ℂ) / b * n ^ 2)‖ = Real.exp (-(π * (b.re / Complex.normSq b)) * (n:ℝ) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  have h : -(π:ℂ) / b * (n:ℂ) ^ 2 = (((-(π * (n:ℝ) ^ 2)) : ℝ) : ℂ) * b⁻¹ := by
    push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.inv_re]
  ring

/-- Dual decomposition (mod-2 regrouping with phase extraction).  With `b = ε - 2i/N`
and `s = 4/b - 2iN`, the dual theta splits as a sum over `j ∈ {0,1}`. -/
theorem dual_decomp (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (∑' n : ℤ, Complex.exp (-(π:ℂ) / ((ε:ℂ) - 2 * I / N) * n ^ 2)) =
      ∑ j ∈ Finset.range 2, Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
        ∑' m : ℤ, Complex.exp (-(π:ℂ) * (4 / ((ε:ℂ) - 2 * I / N) - 2 * I * N) * (m + (j:ℝ) / 2) ^ 2) := by
  set b : ℂ := (ε:ℂ) - 2 * I / N with hb
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbre : b.re = ε := by
    simp [hb, Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im]
  have hbne : b ≠ 0 := by
    intro h; rw [h] at hbre; simp at hbre; exact hε.ne' hbre.symm
  set s : ℂ := 4 / b - 2 * I * N with hs
  set F : ℤ → ℂ := fun n => Complex.exp (-(π:ℂ) / b * n ^ 2) with hF
  have hsum : Summable F := by
    rw [← summable_norm_iff]
    have hc : 0 < π * (b.re / Complex.normSq b) := by
      apply mul_pos Real.pi_pos
      apply div_pos
      · rw [hbre]; exact hε
      · exact Complex.normSq_pos.mpr hbne
    apply (summable_exp_neg_mul_sq hc).congr
    intro n; rw [hF, dual_term_norm2 b n]
  have hsum2 : Summable (fun p : ℤ × Fin 2 => F ((Int.divModEquiv 2).symm p)) :=
    hsum.comp_injective (Int.divModEquiv 2).symm.injective
  have hterm : ∀ (q : ℤ) (r : Fin 2),
      F ((Int.divModEquiv 2).symm (q, r)) =
        Complex.exp (-(π:ℂ) * I * N * (r:ℕ) ^ 2 / 2) *
          Complex.exp (-(π:ℂ) * s * ((q:ℂ) + ((r:ℕ):ℝ) / 2) ^ 2) := by
    intro q r
    have key : -(π:ℂ) / b * (((Int.divModEquiv 2).symm (q, r) : ℤ) : ℂ) ^ 2
        = (-(π:ℂ) * I * N * (r:ℕ) ^ 2 / 2 + -(π:ℂ) * s * ((q:ℂ) + ((r:ℕ):ℝ) / 2) ^ 2)
          + ((-(N:ℤ) * (q ^ 2 + q * (r:ℕ)) : ℤ) : ℂ) * (2 * π * I) := by
      have hsymm : ((Int.divModEquiv 2).symm (q, r) : ℤ) = q * 2 + (r:ℕ) := rfl
      rw [hsymm, hs]; push_cast; field_simp; ring
    rw [hF]
    show Complex.exp (-(π:ℂ) / b * (((Int.divModEquiv 2).symm (q, r) : ℤ) : ℂ) ^ 2) = _
    rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add]
  rw [← (Int.divModEquiv 2).symm.tsum_eq F]
  rw [hsum2.tsum_prod' (fun q => (hasSum_fintype
        (fun r : Fin 2 => F ((Int.divModEquiv 2).symm (q, r)))).summable)]
  simp_rw [tsum_fintype]
  rw [Summable.tsum_finsetSum (fun r _ => ?_)]
  · rw [← Fin.sum_univ_eq_sum_range (fun j => Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
          ∑' m : ℤ, Complex.exp (-(π:ℂ) * s * ((m:ℂ) + (j:ℝ) / 2) ^ 2))]
    apply Finset.sum_congr rfl
    intro r _
    rw [← tsum_mul_left]
    refine tsum_congr (fun q => ?_)
    rw [hterm q r]
  · exact hsum2.comp_injective (fun a b h => by simpa using h)



lemma G_const (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (Real.sqrt ε : ℂ) * (((ε:ℂ) - 2 * I / N) ^ (1/2 : ℂ))⁻¹ *
        (((4 / ((ε:ℂ) - 2 * I / N) - 2 * I * N)) ^ (1/2 : ℂ))⁻¹
      = ((-2 * I * N : ℂ)) ^ (-1/2 : ℂ) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have h2N : (-2 * I * N : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, neg_eq_zero, not_or]
    exact ⟨⟨by norm_num, I_ne_zero⟩, hNc⟩
  have hbX : (ε:ℂ) - 2 * I / N ≠ 0 := by
    intro h
    have : ((ε:ℂ) - 2 * I / N).re = ε := by
      simp [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im]
    rw [h] at this; simp at this; exact hε.ne' this.symm
  set b : ℂ := (ε:ℂ) - 2 * I / N with hb
  set s : ℂ := 4 / b - 2 * I * N with hs
  have hbinv : b * (4 / b) = 4 := by rw [mul_comm]; exact div_mul_cancel₀ 4 hbX
  have hbs : b * s = (ε:ℂ) * (-2 * I * N) := by
    rw [hs, mul_sub, hbinv, hb]; field_simp; linear_combination (4:ℂ) * Complex.I_sq
  have hsne : s ≠ 0 := by
    intro h; rw [h, mul_zero] at hbs
    rcases mul_eq_zero.mp hbs.symm with h1 | h1
    · exact hεc h1
    · exact h2N h1
  have h1s : s⁻¹ = (((((N:ℝ) ^ 2 * ε)⁻¹) : ℝ) : ℂ) + (((((2 * N : ℝ))⁻¹) : ℝ) : ℂ) * I := by
    have hseq : s = (ε:ℂ) * (-2 * I * N) / b := by
      rw [eq_div_iff hbX, mul_comm]; exact hbs
    rw [hseq, inv_div, hb]; push_cast; field_simp; ring_nf; simp only [Complex.I_sq]; ring
  have hsre : 0 < s.re := by
    have hre : (0:ℝ) < s⁻¹.re := by
      rw [h1s, Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero,
        Complex.ofReal_re]
      exact inv_pos.mpr (mul_pos (pow_pos hNr 2) hε)
    rw [Complex.inv_re] at hre
    rcases div_pos_iff.mp hre with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h (not_lt.mpr (Complex.normSq_nonneg s))
  have hargb : |arg b| < π / 2 := by
    rw [hb]; refine Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ?_)
    simp [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im]; exact hε
  have hargs : |arg s| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hsre)
  have hargsum : arg b + arg s ∈ Set.Ioc (-π) π := by
    rw [abs_lt] at hargb hargs
    exact ⟨by nlinarith [hargb.1, hargs.1], by nlinarith [hargb.2, hargs.2, Real.pi_pos]⟩
  have hsqrt : (Real.sqrt ε : ℂ) = ((ε:ℂ)) ^ (1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hε.le]; norm_num
  rw [hsqrt, ← Complex.cpow_neg, ← Complex.cpow_neg]
  rw [Complex.cpow_def_of_ne_zero hεc, Complex.cpow_def_of_ne_zero hbX,
      Complex.cpow_def_of_ne_zero hsne, Complex.cpow_def_of_ne_zero h2N,
      ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hlogmul : Complex.log b + Complex.log s = Complex.log ((ε:ℂ) * (-2 * I * N)) := by
    rw [← hbs]; exact (Complex.log_mul hbX hsne hargsum).symm
  rw [Complex.log_ofReal_mul hε h2N, Complex.ofReal_log hε.le] at hlogmul
  linear_combination (-1/2 : ℂ) * hlogmul



lemma neg2IN_cpow (N : ℕ) (hN : 0 < N) :
    (-2 * I * (N:ℂ)) ^ (-1/2 : ℂ) = (1 + I) / (2 * (Real.sqrt N : ℂ)) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have h2N : (-2 * I * (N:ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, neg_eq_zero, not_or]
    refine ⟨⟨by norm_num, I_ne_zero⟩, ?_⟩; exact_mod_cast hN.ne'
  have heq : (-2 * I * (N:ℂ)) = ((-2 * N : ℝ):ℂ) * I := by push_cast; ring
  have hnorm : ‖(-2 * I * (N:ℂ))‖ = 2 * N := by
    rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith)]
    ring
  have hre : (-2 * I * (N:ℂ)).re = 0 := by rw [heq]; simp
  have him : (-2 * I * (N:ℂ)).im < 0 := by rw [heq]; simp; nlinarith
  have harg : Complex.arg (-2 * I * (N:ℂ)) = -(π/2) := by
    rw [Complex.arg_eq_neg_pi_div_two_iff]; exact ⟨hre, him⟩
  rw [Complex.cpow_def_of_ne_zero h2N, Complex.log, hnorm, harg]
  have h2Npos : (0:ℝ) < 2 * N := by nlinarith
  have hsqrtN : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hexp : ((Real.log (2 * N) : ℂ) + (((-(π/2)):ℝ) : ℂ) * I) * (-1/2 : ℂ)
      = ((-(Real.log (2 * N) / 2) : ℝ) : ℂ) + ((π/4 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hA : Real.exp (-(Real.log (2 * (N:ℝ)) / 2)) = 1 / Real.sqrt (2 * N) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h2Npos, one_div, ← Real.exp_neg]
    congr 1; ring
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsN : Real.sqrt (N:ℝ) ≠ 0 := hsqrtN.ne'
  have hscalar : (1/Real.sqrt (2*(N:ℝ))) * (Real.sqrt 2 / 2) = 1/(2*Real.sqrt N) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2) N]
    field_simp
  rw [hA]
  have e1 : (↑(1/Real.sqrt (2*(N:ℝ))) : ℂ) * (↑(Real.sqrt 2/2) + ↑(Real.sqrt 2/2) * I)
      = ↑((1/Real.sqrt (2*(N:ℝ)))*(Real.sqrt 2/2)) * (1 + I) := by push_cast; ring
  rw [e1, hscalar]; push_cast; ring
noncomputable def sfun (N : ℕ) (ε : ℝ) : ℂ := 4 / ((ε:ℂ) - 2 * I / N) - 2 * I * N

-- basic facts
lemma bX_ne (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) : (ε:ℂ) - 2 * I / N ≠ 0 := by
  intro h
  have : ((ε:ℂ) - 2 * I / N).re = ε := by
    simp [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im]
  rw [h] at this; simp at this; exact hε.ne' this.symm

lemma sfun_ne (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) : sfun N ε ≠ 0 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have h2N : (-2 * I * N : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, neg_eq_zero, not_or]
    exact ⟨⟨by norm_num, I_ne_zero⟩, hNc⟩
  have hbX := bX_ne N hN ε hε
  have hbinv : ((ε:ℂ) - 2 * I / N) * (4 / ((ε:ℂ) - 2 * I / N)) = 4 := by
    rw [mul_comm]; exact div_mul_cancel₀ 4 hbX
  have hbs : ((ε:ℂ) - 2 * I / N) * sfun N ε = (ε:ℂ) * (-2 * I * N) := by
    rw [sfun, mul_sub, hbinv]; field_simp; linear_combination (4:ℂ) * Complex.I_sq
  intro h
  rw [h, mul_zero] at hbs
  rcases mul_eq_zero.mp hbs.symm with h1 | h1
  · exact hεc h1
  · exact h2N h1

lemma scpow_ne (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) : (sfun N ε) ^ (1/2 : ℂ) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (sfun_ne N hN ε hε)]
  exact Complex.exp_ne_zero _

lemma H_decomp (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (Real.sqrt ε : ℂ) * Gtheta N ε =
      ∑ j ∈ Finset.range 2, Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
        ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)) *
        ((sfun N ε) ^ (1/2 : ℂ) *
          ∑' m : ℤ, Complex.exp (-(π:ℂ) * (sfun N ε) * ((m:ℂ) + (j:ℝ) / 2) ^ 2)) := by
  rw [Gtheta_poisson N ε hε, dual_decomp N hN ε hε]
  rw [mul_sum, mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  set b : ℂ := (ε:ℂ) - 2 * I / N with hb
  set s : ℂ := 4 / b - 2 * I * N with hs
  have hsfun : sfun N ε = s := by rw [sfun, hs, hb]
  rw [hsfun]
  have hsne : (s ^ (1/2 : ℂ)) ≠ 0 := by rw [← hsfun]; exact scpow_ne N hN ε hε
  have hGc := G_const N hN ε hε
  rw [← hb, ← hs] at hGc
  set E : ℂ := Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) with hE
  set V : ℂ := ∑' m : ℤ, Complex.exp (-(π:ℂ) * s * ((m:ℂ) + (j:ℝ) / 2) ^ 2) with hV
  have hcancel : (s ^ (1/2 : ℂ))⁻¹ * s ^ (1/2 : ℂ) = 1 := inv_mul_cancel₀ hsne
  calc (Real.sqrt ε : ℂ) * (1 / b ^ (1/2 : ℂ) * (E * V))
      = E * V * ((Real.sqrt ε : ℂ) * (b ^ (1/2 : ℂ))⁻¹) := by rw [one_div]; ring
    _ = E * V * ((Real.sqrt ε : ℂ) * (b ^ (1/2 : ℂ))⁻¹) * ((s ^ (1/2 : ℂ))⁻¹ * s ^ (1/2 : ℂ)) := by
          rw [hcancel]; ring
    _ = E * ((Real.sqrt ε : ℂ) * (b ^ (1/2 : ℂ))⁻¹ * (s ^ (1/2 : ℂ))⁻¹) * (s ^ (1/2 : ℂ) * V) := by ring
    _ = E * (-2 * I * N : ℂ) ^ (-1/2 : ℂ) * (s ^ (1/2 : ℂ) * V) := by rw [hGc]

lemma sfun_formula (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    sfun N ε = (ε:ℂ) * (-2 * I * N) / ((ε:ℂ) - 2 * I / N) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbX := bX_ne N hN ε hε
  have hbinv : ((ε:ℂ) - 2 * I / N) * (4 / ((ε:ℂ) - 2 * I / N)) = 4 := by
    rw [mul_comm]; exact div_mul_cancel₀ 4 hbX
  have hbs : ((ε:ℂ) - 2 * I / N) * sfun N ε = (ε:ℂ) * (-2 * I * N) := by
    rw [sfun, mul_sub, hbinv]; field_simp; linear_combination (4:ℂ) * Complex.I_sq
  rw [eq_div_iff hbX, mul_comm]; exact hbs

lemma sfun_inv (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (sfun N ε)⁻¹ = (((((N:ℝ) ^ 2 * ε)⁻¹) : ℝ) : ℂ) + (((((2 * N : ℝ))⁻¹) : ℝ) : ℂ) * I := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hεc : (ε:ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  rw [sfun_formula N hN ε hε, inv_div]
  rw [div_eq_iff (by simp [hεc, hNc, I_ne_zero])]
  push_cast
  field_simp
  linear_combination ((ε:ℂ)*(N:ℂ)) * Complex.I_sq

lemma sfun_re_pos (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) : 0 < (sfun N ε).re := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hre : (0:ℝ) < (sfun N ε)⁻¹.re := by
    rw [sfun_inv N hN ε hε, Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero, Complex.ofReal_re]
    exact inv_pos.mpr (mul_pos (pow_pos hNr 2) hε)
  rw [Complex.inv_re] at hre
  rcases div_pos_iff.mp hre with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · exact absurd h (not_lt.mpr (Complex.normSq_nonneg _))

lemma sfun_redivnsq (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (sfun N ε).re / Complex.normSq (sfun N ε) = ((N:ℝ) ^ 2 * ε)⁻¹ := by
  have h := Complex.inv_re (sfun N ε)
  rw [sfun_inv N hN ε hε] at h
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero,
    Complex.ofReal_re] at h
  exact h.symm

lemma sfun_tendsto (N : ℕ) (hN : 0 < N) :
    Tendsto (sfun N) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hden0 : ((0:ℝ):ℂ) - 2 * I / N ≠ 0 := by
    simp only [Complex.ofReal_zero, zero_sub, neg_ne_zero]
    rw [div_ne_zero_iff]
    exact ⟨by simp [I_ne_zero], hNc⟩
  have hcont : ContinuousAt (fun x:ℝ => (x:ℂ) * (-2 * I * N) / ((x:ℂ) - 2 * I / N)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hden0
  have hval : (fun x:ℝ => (x:ℂ) * (-2 * I * N) / ((x:ℂ) - 2 * I / N)) 0 = 0 := by simp
  have ht : Tendsto (fun x:ℝ => (x:ℂ) * (-2 * I * N) / ((x:ℂ) - 2 * I / N)) (𝓝 0) (𝓝 0) := by
    have h := hcont.tendsto
    simpa only [Complex.ofReal_zero, zero_mul, zero_div] using h
  refine (ht.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (sfun_formula N hN x hx).symm

lemma sfun_dom (N : ℕ) (hN : 0 < N) :
    Tendsto (fun ε => (sfun N ε).re / Complex.normSq (sfun N ε)) (𝓝[>] (0:ℝ)) atTop := by
  have h1 : Tendsto (fun ε:ℝ => ε⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun ε:ℝ => ((N:ℝ) ^ 2)⁻¹ * ε⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) h1
  refine (h2.congr (fun ε => by rw [← mul_inv])).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (sfun_redivnsq N hN ε hε).symm

lemma exp_neg_pi_I_half : Complex.exp (-(π:ℂ) * I / 2) = -I := by
  rw [show -(π:ℂ) * I / 2 = ((-(π/2):ℝ):ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.cos_pi_div_two,
    Real.sin_neg, Real.sin_pi_div_two]
  push_cast; ring

set_option maxHeartbeats 1000000 in
lemma gaussSumC_div (N : ℕ) (hN : 0 < N) :
    gaussSumC N / N = ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)) * (1 + (-I) ^ N) := by
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hre_ev : ∀ᶠ ε in 𝓝[>](0:ℝ), 0 < (sfun N ε).re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε; exact sfun_re_pos N hN ε hε
  have hU : ∀ j : ℕ, Tendsto (fun ε => (sfun N ε) ^ (1/2:ℂ) *
      ∑' m : ℤ, Complex.exp (-(π:ℂ) * (sfun N ε) * ((m:ℂ) + (j:ℝ)/2) ^ 2)) (𝓝[>](0:ℝ)) (𝓝 1) := by
    intro j
    refine Filter.Tendsto.congr ?_ (complex_shifted_theta ((j:ℝ)/2) (𝓝[>](0:ℝ)) (sfun N)
      (sfun_tendsto N hN) hre_ev (sfun_dom N hN))
    intro ε
    congr 1
    exact tsum_congr (fun m => by congr 1; push_cast; ring)
  have hterm : ∀ j : ℕ, Tendsto (fun ε => Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
      ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)) * ((sfun N ε) ^ (1/2:ℂ) *
        ∑' m : ℤ, Complex.exp (-(π:ℂ) * (sfun N ε) * ((m:ℂ) + (j:ℝ)/2) ^ 2)))
      (𝓝[>](0:ℝ)) (𝓝 (Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) * ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)))) := by
    intro j
    have h := (hU j).const_mul (Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
      ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)))
    rwa [mul_one] at h
  have hsum : Tendsto (fun ε => (Real.sqrt ε:ℂ) * Gtheta N ε) (𝓝[>](0:ℝ))
      (𝓝 (∑ j ∈ Finset.range 2, Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
        ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)))) := by
    refine (tendsto_finset_sum (Finset.range 2) (fun j _ => hterm j)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (H_decomp N hN ε hε).symm
  have huniq : gaussSumC N / N = ∑ j ∈ Finset.range 2,
      Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) * ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)) :=
    tendsto_nhds_unique (sqrt_eps_Gtheta_limit N hN) hsum
  have hexpN : Complex.exp (-(π:ℂ) * I * N / 2) = (-I) ^ N := by
    rw [show -(π:ℂ) * I * N / 2 = (N:ℂ) * (-(π:ℂ) * I / 2) by ring, Complex.exp_nat_mul,
      exp_neg_pi_I_half]
  rw [huniq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.cast_zero, Nat.cast_one, one_pow, mul_one, zero_add]
  rw [show -(π:ℂ) * I * N * (0:ℂ) ^ 2 / 2 = 0 by ring, Complex.exp_zero, hexpN]
  ring

lemma gaussSumC_value (N : ℕ) (hN : 0 < N) :
    gaussSumC N = (Real.sqrt N : ℂ) * (1 + I) / 2 * (1 + (-I) ^ N) := by
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have huniq := gaussSumC_div N hN
  rw [neg2IN_cpow N hN, div_eq_iff hNc] at huniq
  have hNeq : (N:ℂ) = (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    norm_cast
  rw [huniq, hNeq]
  field_simp
end GaussSection

section BridgeSection
open Complex Filter Topology ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.zeta

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- For `1 < s.re`, `LSeries (zetaMul χ) s = riemannZeta s * L(χ, s)`. -/
theorem LSeries_zetaMul_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(zetaMul χ) s = riemannZeta s * χ.LFunction s := by
  rw [zetaMul, ← coe_mul, LSeries_convolution']
  · congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · rw [χ.LFunction_eq_LSeries hs]
      exact LSeries_congr (fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm) s
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re χ hs

open scoped ComplexOrder

/-- `riemannZeta x > 0` for real `x > 1`. -/
theorem riemannZeta_pos_of_one_lt {x : ℝ} (hx : 1 < x) : (0 : ℂ) < riemannZeta x := by
  rw [← LSeries_zeta_eq_riemannZeta (by simpa using hx)]
  refine LSeries.positive (a := ↗ζ) (fun n => ?_) ?_ ?_
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [zeta_apply_ne hn, Nat.cast_one]; exact zero_le_one
  · simp only [zeta_apply_ne one_ne_zero, Nat.cast_one]; exact zero_lt_one
  · rw [abscissaOfAbsConv_zeta]; exact_mod_cast hx

/-- For real `x > 1` and quadratic `χ`, `L(χ, x)` is a positive real. -/
theorem LFunction_pos_of_quadratic {χ : DirichletCharacter ℂ N}
    (hχ : χ ^ 2 = 1) {x : ℝ} (hx : 1 < x) :
    (0 : ℂ) < χ.LFunction x := by
  have hz : (0 : ℂ) < riemannZeta x := riemannZeta_pos_of_one_lt hx
  have hzm : (0 : ℂ) < LSeries ↗(zetaMul χ) x := by
    refine LSeries.positive (fun n => zetaMul_nonneg hχ n) ?_ ?_
    · exact χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one
    · refine lt_of_le_of_lt ?_ (by exact_mod_cast hx : (1 : EReal) < (x : ℝ))
      exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
        fun _ a => χ.LSeriesSummable_zetaMul a
  rw [LSeries_zetaMul_eq χ (by simpa using hx)] at hzm
  exact (mul_pos_iff_of_pos_left hz).mp hzm

/-- For a nontrivial quadratic character `χ`, `L(χ, 1) > 0`. -/
theorem LFunction_one_pos {χ : DirichletCharacter ℂ N}
    (hχ : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    (0 : ℂ) < χ.LFunction 1 := by
  -- continuity of `x ↦ L(χ, x)` at `1`
  have hcont : ContinuousAt (fun x : ℝ => χ.LFunction x) 1 := by
    have h1 : ContinuousAt χ.LFunction (((1 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_one]
      exact (χ.differentiableAt_LFunction 1 (Or.inr hχ1)).continuousAt
    exact h1.comp Complex.continuous_ofReal.continuousAt
  have htend : Tendsto (fun x : ℝ => χ.LFunction x) (𝓝[>] 1) (𝓝 (χ.LFunction 1)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- eventually positive on `(1, ∞)`
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 1, (0 : ℂ) < χ.LFunction x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact LFunction_pos_of_quadratic hχ hx
  -- imaginary part is `0` in the limit
  have him : (χ.LFunction 1).im = 0 := by
    have h1 : Tendsto (fun x : ℝ => (χ.LFunction x).im) (𝓝[>] 1) (𝓝 (χ.LFunction 1).im) :=
      (Complex.continuous_im.continuousAt.tendsto).comp htend
    have h2 : (fun x : ℝ => (χ.LFunction x).im) =ᶠ[𝓝[>] 1] (fun _ => 0) := by
      filter_upwards [hev] with x hx
      exact ((Complex.pos_iff).mp hx).2.symm
    exact tendsto_nhds_unique (h1.congr' h2) tendsto_const_nhds
  -- real part is `≥ 0` in the limit
  have hre : 0 ≤ (χ.LFunction 1).re := by
    have h1 : Tendsto (fun x : ℝ => (χ.LFunction x).re) (𝓝[>] 1) (𝓝 (χ.LFunction 1).re) :=
      (Complex.continuous_re.continuousAt.tendsto).comp htend
    refine ge_of_tendsto h1 ?_
    filter_upwards [hev] with x hx
    exact ((Complex.pos_iff).mp hx).1.le
  -- nonvanishing
  have hne : χ.LFunction 1 ≠ 0 := LFunction_apply_one_ne_zero hχ1
  rw [Complex.pos_iff]
  refine ⟨hre.lt_of_ne ?_, him.symm⟩
  intro h
  exact hne (Complex.ext_iff.mpr ⟨by rw [Complex.zero_re]; exact h.symm,
    by rw [Complex.zero_im]; exact him⟩)

end DirichletCharacter
open Complex Filter Topology
open scoped Real

lemma tendsto_inv_add_nat (x : ℂ) :
    Tendsto (fun N : ℕ => 1 / (x + (N:ℂ))) atTop (𝓝 0) := by
  have hb : ∀ᶠ N : ℕ in atTop, ‖1 / (x + (N:ℂ))‖ ≤ 1 / ((N:ℝ) - ‖x‖) := by
    filter_upwards [eventually_gt_atTop (⌈‖x‖⌉₊ + 1)] with N hN
    have hxlt : ‖x‖ < N := by
      calc ‖x‖ ≤ ⌈‖x‖⌉₊ := Nat.le_ceil _
        _ < N := by exact_mod_cast (by omega : ⌈‖x‖⌉₊ < N)
    have hpos : (0:ℝ) < (N:ℝ) - ‖x‖ := by linarith
    have hle : (N:ℝ) - ‖x‖ ≤ ‖x + (N:ℂ)‖ := by
      have h2 : ‖(N:ℂ)‖ - ‖x‖ ≤ ‖x + (N:ℂ)‖ := by
        have hh := norm_sub_norm_le (N:ℂ) (-x)
        simp only [norm_neg, sub_neg_eq_add, add_comm] at hh
        exact hh
      rw [Complex.norm_natCast] at h2; exact h2
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hpos hle
  have h1 : Tendsto (fun N : ℕ => (N:ℝ) - ‖x‖) atTop atTop := by
    apply Filter.tendsto_atTop_add_const_right atTop (-‖x‖) tendsto_natCast_atTop_atTop |>.congr
    intro N; ring
  exact squeeze_zero_norm' hb (by simpa [one_div] using h1.inv_tendsto_atTop)

-- Summability of the telescoping difference
lemma summable_telescope (x : ℂ) (hx : ∀ n : ℕ, x + (n:ℂ) ≠ 0) :
    Summable (fun n : ℕ => 1 / (x + (n:ℂ)) - 1 / (x + ((n:ℂ)+1))) := by
  have heq : ∀ n : ℕ, 1 / (x + (n:ℂ)) - 1 / (x + ((n:ℂ)+1))
      = 1 / ((x + (n:ℂ)) * (x + ((n:ℂ)+1))) := by
    intro n
    have h1 := hx n
    have h2 : x + ((n:ℂ)+1) ≠ 0 := by have := hx (n+1); push_cast at this; convert this using 2
    field_simp
    ring
  rw [funext heq]
  apply Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => 4 / ((n:ℝ))^2)
  · simpa [mul_one_div] using ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).mul_left 4
  · filter_upwards [eventually_gt_atTop (2 * ⌈‖x‖⌉₊ + 2)] with n hn
    have hxn : ‖x‖ < n / 2 := by
      have : (⌈‖x‖⌉₊ : ℝ) < n / 2 := by
        have : (2:ℝ) * ⌈‖x‖⌉₊ < n := by exact_mod_cast (by omega : 2 * ⌈‖x‖⌉₊ < n)
        linarith
      calc ‖x‖ ≤ ⌈‖x‖⌉₊ := Nat.le_ceil _
        _ < n / 2 := this
    have hb1 : (n:ℝ)/2 ≤ ‖x + (n:ℂ)‖ := by
      have hh := norm_sub_norm_le (n:ℂ) (-x)
      simp only [norm_neg, sub_neg_eq_add, add_comm, Complex.norm_natCast] at hh
      linarith
    have hb2 : (n:ℝ)/2 ≤ ‖x + ((n:ℂ)+1)‖ := by
      have hh := norm_sub_norm_le ((n:ℂ)+1) (-x)
      simp only [norm_neg, sub_neg_eq_add] at hh
      have hn1 : (n:ℝ) ≤ ‖(n:ℂ)+1‖ := by
        rw [show ((n:ℂ)+1) = ((n+1 : ℕ):ℂ) by push_cast; ring, Complex.norm_natCast]
        exact_mod_cast Nat.le_succ n
      have hcomm : ‖(n:ℂ)+1 + x‖ = ‖x + ((n:ℂ)+1)‖ := by rw [add_comm]
      rw [hcomm] at hh
      linarith
    rw [norm_div, norm_one, norm_mul]
    have hprod : (n:ℝ)/2 * ((n:ℝ)/2) ≤ ‖x + (n:ℂ)‖ * ‖x + ((n:ℂ)+1)‖ :=
      mul_le_mul hb1 hb2 (by positivity) (by positivity)
    have hn0 : (0:ℝ) < (n:ℝ)^2/4 := by
      have : (0:ℕ) < n := by omega
      have : (0:ℝ) < (n:ℝ) := by exact_mod_cast this
      positivity
    have hD : (n:ℝ)^2/4 ≤ ‖x + (n:ℂ)‖ * ‖x + ((n:ℂ)+1)‖ := by nlinarith [hprod]
    calc 1 / (‖x + (n:ℂ)‖ * ‖x + ((n:ℂ)+1)‖) ≤ 1 / ((n:ℝ)^2/4) :=
          one_div_le_one_div_of_le hn0 hD
      _ = 4 / (n:ℝ)^2 := by ring

-- Step 7: the cotangent identity at s = 1.
lemma cot_value_sum (x : ℂ) (hx : x ∈ Complex.integerComplement) :
    ∑' n : ℕ, (1 / (x + (n:ℂ)) - 1 / ((n:ℂ) + 1 - x)) = (π : ℂ) * Complex.cot (π * x) := by
  have hxn : ∀ n : ℕ, x + (n:ℂ) ≠ 0 := fun n => by
    have := Complex.integerComplement_add_ne_zero hx (n : ℤ); push_cast at this ⊢; convert this using 2
  have hc : HasSum (cotTerm x) ((π : ℂ) * Complex.cot (π * x) - 1 / x) := by
    have := (Summable_cotTerm hx).hasSum
    rwa [show ∑' n, cotTerm x n = (π : ℂ) * Complex.cot (π * x) - 1 / x from
      (cot_series_rep' hx).symm] at this
  have hd : HasSum (fun n : ℕ => 1 / (x + (n:ℂ)) - 1 / (x + ((n:ℂ)+1))) (1 / x) :=
    (summable_telescope x hxn).hasSum_iff_tendsto_nat.mpr (by
      have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N,
          (1 / (x + (n:ℂ)) - 1 / (x + ((n:ℂ)+1))) = 1 / x - 1 / (x + (N:ℂ)) := by
        intro N
        induction N with
        | zero => simp
        | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
      simp_rw [hpartial]
      simpa using (tendsto_const_nhds (x := (1/x : ℂ))).sub (tendsto_inv_add_nat x))
  have hsum := hc.add hd
  have heq : (fun n : ℕ => cotTerm x n + (1 / (x + (n:ℂ)) - 1 / (x + ((n:ℂ)+1))))
      = (fun n : ℕ => 1 / (x + (n:ℂ)) - 1 / ((n:ℂ) + 1 - x)) := by
    funext n
    simp only [cotTerm]
    have h1 : x - ((n:ℂ) + 1) ≠ 0 := by
      intro hc
      exact Complex.integerComplement_add_ne_zero hx (-(n+1) : ℤ) (by push_cast; linear_combination hc)
    have h2 : (n:ℂ) + 1 - x ≠ 0 := fun h => h1 (by linear_combination -h)
    have h3 : x + ((n:ℂ)+1) ≠ 0 := by have := hxn (n+1); push_cast at this; exact this
    field_simp
    ring
  rw [heq] at hsum
  rw [hsum.tsum_eq]
  ring


open Complex Filter Topology Set HurwitzZeta
open scoped Real

lemma diff_rpow_bound (e : ℝ) (he1 : 1 ≤ e) (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)^(-e) - ((n:ℝ)+1)^(-e) ≤ e / ((n:ℝ) * ((n:ℝ)+1)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (0:ℝ) < (n:ℝ)+1 := by positivity
  set t : ℝ := (n:ℝ)/((n:ℝ)+1) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hn1]; linarith
  have hne : (n:ℝ)^e ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos e)
  have hn1e : ((n:ℝ)+1)^e ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn1 e)
  have hfac : ((n:ℝ)+1)^(-e) = (n:ℝ)^(-e) * t^e := by
    rw [ht, Real.div_rpow hnpos.le hn1.le, Real.rpow_neg hnpos.le, Real.rpow_neg hn1.le]
    field_simp
  have hbern : 1 - e/((n:ℝ)+1) ≤ t^e := by
    have hs : (-1:ℝ) ≤ -(1/((n:ℝ)+1)) := by
      rw [neg_le, neg_neg, div_le_one hn1]; linarith
    have key := one_add_mul_self_le_rpow_one_add hs he1
    have hts : 1 + -(1/((n:ℝ)+1)) = t := by rw [ht]; field_simp; ring
    rw [hts] at key
    have : 1 + e * -(1/((n:ℝ)+1)) = 1 - e/((n:ℝ)+1) := by ring
    linarith [key]
  have hstep1 : (n:ℝ)^(-e) - ((n:ℝ)+1)^(-e) = (n:ℝ)^(-e) * (1 - t^e) := by rw [hfac]; ring
  have hnre_le : (n:ℝ)^(-e) ≤ (n:ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  have htle1 : t^e ≤ 1 := Real.rpow_le_one ht0 ht1 (by linarith)
  calc (n:ℝ)^(-e) - ((n:ℝ)+1)^(-e) = (n:ℝ)^(-e) * (1 - t^e) := hstep1
    _ ≤ (n:ℝ)⁻¹ * (e/((n:ℝ)+1)) := by
        apply mul_le_mul hnre_le (by linarith) (by linarith) (by positivity)
    _ = e/((n:ℝ)*((n:ℝ)+1)) := by field_simp

lemma cterm_eq (a e : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    (1 / ((n:ℂ)+(a:ℂ))^(e:ℂ) - 1/((n:ℂ)+1-(a:ℂ))^(e:ℂ))/2
      = (((1/((n:ℝ)+a)^e - 1/((n:ℝ)+1-a)^e)/2 : ℝ) : ℂ) := by
  have hx : (0:ℝ) ≤ (n:ℝ)+a := by positivity
  have hy : (0:ℝ) ≤ (n:ℝ)+1-a := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have e1 : ((n:ℂ)+(a:ℂ)) = (((n:ℝ)+a : ℝ):ℂ) := by push_cast; ring
  have e2 : ((n:ℂ)+1-(a:ℂ)) = (((n:ℝ)+1-a : ℝ):ℂ) := by push_cast; ring
  rw [e1, e2, ← Complex.ofReal_cpow hx, ← Complex.ofReal_cpow hy]
  push_cast
  ring

lemma cterm_norm_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (e : ℝ) (he1 : 1 ≤ e) (he2 : e ≤ 2) (n : ℕ) :
    ‖(1 / ((n:ℂ)+(a:ℂ))^(e:ℂ) - 1/((n:ℂ)+1-(a:ℂ))^(e:ℂ))/2‖
      ≤ (if n = 0 then (a^(-2:ℝ)+(1-a)^(-2:ℝ))/2 else 1/(n:ℝ)^2) := by
  rw [cterm_eq a e ha0 ha1 n, Complex.norm_real, Real.norm_eq_abs]
  have hx : (0:ℝ) < (n:ℝ)+a := by positivity
  have hy : (0:ℝ) < (n:ℝ)+1-a := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hxe : 1/((n:ℝ)+a)^e = ((n:ℝ)+a)^(-e) := by rw [Real.rpow_neg hx.le, one_div]
  have hye : 1/((n:ℝ)+1-a)^e = ((n:ℝ)+1-a)^(-e) := by rw [Real.rpow_neg hy.le, one_div]
  rw [hxe, hye]
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    simp only [if_pos rfl, Nat.cast_zero, zero_add]
    -- |a^(-e) - (1-a)^(-e)|/2 ≤ (a^(-2)+(1-a)^(-2))/2
    have hae : a^(-e) ≤ a^(-2:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge ha0 ha1.le; linarith
    have hbe : (1-a)^(-e) ≤ (1-a)^(-2:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith); linarith
    have hapos : 0 ≤ a^(-e) := Real.rpow_nonneg ha0.le _
    have hbpos : 0 ≤ (1-a)^(-e) := Real.rpow_nonneg (by linarith) _
    have hX : |a^(-e) - (1-a)^(-e)| ≤ a^(-2:ℝ)+(1-a)^(-2:ℝ) := by
      rw [abs_sub_le_iff]; constructor <;> nlinarith [hae, hbe, hapos, hbpos]
    calc |(a^(-e) - (1-a)^(-e))/2| = |a^(-e) - (1-a)^(-e)|/2 := by rw [abs_div]; norm_num
      _ ≤ (a^(-2:ℝ)+(1-a)^(-2:ℝ))/2 := by linarith
  · have hn1 : 1 ≤ n := hn0
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
    rw [if_neg (by omega)]
    -- |x^(-e) - y^(-e)| ≤ n^(-e)-(n+1)^(-e)
    have hxn : (n:ℝ) ≤ (n:ℝ)+a := by linarith
    have hxn1 : (n:ℝ)+a ≤ (n:ℝ)+1 := by linarith
    have hyn : (n:ℝ) ≤ (n:ℝ)+1-a := by linarith
    have hyn1 : (n:ℝ)+1-a ≤ (n:ℝ)+1 := by linarith
    have hxlo : ((n:ℝ)+1)^(-e) ≤ ((n:ℝ)+a)^(-e) := Real.rpow_le_rpow_of_nonpos hx hxn1 (by linarith)
    have hxhi : ((n:ℝ)+a)^(-e) ≤ (n:ℝ)^(-e) := Real.rpow_le_rpow_of_nonpos hnpos hxn (by linarith)
    have hylo : ((n:ℝ)+1)^(-e) ≤ ((n:ℝ)+1-a)^(-e) := Real.rpow_le_rpow_of_nonpos hy hyn1 (by linarith)
    have hyhi : ((n:ℝ)+1-a)^(-e) ≤ (n:ℝ)^(-e) := Real.rpow_le_rpow_of_nonpos hnpos hyn (by linarith)
    have hdiff := diff_rpow_bound e he1 n hn1
    have hbound2 : e / ((n:ℝ)*((n:ℝ)+1)) ≤ 2/(n:ℝ)^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hnpos]
    have hkey : |((n:ℝ)+a)^(-e) - ((n:ℝ)+1-a)^(-e)| ≤ (n:ℝ)^(-e) - ((n:ℝ)+1)^(-e) := by
      rw [abs_sub_le_iff]; constructor <;> linarith
    rw [abs_div, abs_of_pos (show (0:ℝ)<2 by norm_num)]
    calc |((n:ℝ)+a)^(-e) - ((n:ℝ)+1-a)^(-e)|/2 ≤ ((n:ℝ)^(-e) - ((n:ℝ)+1)^(-e))/2 := by linarith
      _ ≤ (e/((n:ℝ)*((n:ℝ)+1)))/2 := by linarith
      _ ≤ (2/(n:ℝ)^2)/2 := by linarith
      _ = 1/(n:ℝ)^2 := by ring

open scoped Real in
theorem hurwitzZetaOdd_one_eq_tsum (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    hurwitzZetaOdd (↑a) 1
      = ∑' n : ℕ, (1/((n:ℂ)+(a:ℂ)) - 1/((n:ℂ)+1-(a:ℂ)))/2 := by
  have ha_mem : a ∈ Icc (0:ℝ) 1 := ⟨ha0.le, ha1.le⟩
  set u : ℕ → ℝ := fun m => 1 + 1/((m:ℝ)+1) with hu
  have hu_gt : ∀ m, (1:ℝ) < u m := by
    intro m; rw [hu]; simp only; have : (0:ℝ) < 1/((m:ℝ)+1) := by positivity
    linarith
  have hu_le : ∀ m, u m ≤ 2 := by
    intro m; rw [hu]; simp only
    have hm : (0:ℝ) ≤ m := by positivity
    have : 1/((m:ℝ)+1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  -- term functions
  set f : ℕ → ℕ → ℂ := fun m n =>
    (1 / ((n:ℂ)+(a:ℂ))^(u m:ℂ) - 1/((n:ℂ)+1-(a:ℂ))^(u m:ℂ))/2 with hf
  set g : ℕ → ℂ := fun n => (1/((n:ℂ)+(a:ℂ)) - 1/((n:ℂ)+1-(a:ℂ)))/2 with hg
  -- bound
  set C₀ : ℝ := (a^(-2:ℝ)+(1-a)^(-2:ℝ))/2 with hC
  set bnd : ℕ → ℝ := fun n => if n = 0 then C₀ else 1/(n:ℝ)^2 with hbnd
  have hsum : Summable bnd := by
    have h2 : Summable (fun n : ℕ => 1/(n:ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hfin : Summable (fun n : ℕ => if n = 0 then C₀ else 0) := by
      apply summable_of_ne_finset_zero (s := {0})
      intro n hn; simp only [Finset.mem_singleton] at hn; rw [if_neg hn]
    have : bnd = (fun n:ℕ => 1/(n:ℝ)^2) + (fun n:ℕ => if n = 0 then C₀ else 0) := by
      funext n; rw [hbnd]; simp only [Pi.add_apply]
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · rw [if_neg (by omega), if_neg (by omega)]; ring
    rw [this]; exact h2.add hfin
  -- step A: continuity limit
  have hcontA : Tendsto (fun m => hurwitzZetaOdd (↑a) (↑(u m))) atTop (𝓝 (hurwitzZetaOdd (↑a) 1)) := by
    have huc : Tendsto (fun m => (↑(u m) : ℂ)) atTop (𝓝 (1:ℂ)) := by
      have : Tendsto (fun m : ℕ => u m) atTop (𝓝 (1:ℝ)) := by
        rw [hu]
        simpa using (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun m : ℕ => (1:ℝ) + 1/((m:ℝ)+1)) atTop (𝓝 (1+0)))
      exact (Complex.continuous_ofReal.tendsto 1).comp this
    exact ((differentiable_hurwitzZetaOdd (↑a)).continuous.tendsto 1).comp huc
  -- step B: hasSum equality
  have hB : ∀ m, hurwitzZetaOdd (↑a) (↑(u m)) = ∑' n, f m n := by
    intro m
    have hs : 1 < (↑(u m) : ℂ).re := by rw [Complex.ofReal_re]; exact hu_gt m
    exact ((hasSum_nat_hurwitzZetaOdd_of_mem_Icc ha_mem hs).tsum_eq).symm
  -- step C: Tannery
  have hbase1 : ∀ n : ℕ, ((n:ℂ)+(a:ℂ)) ≠ 0 := by
    intro n
    have : ((n:ℂ)+(a:ℂ)) = (((n:ℝ)+a : ℝ):ℂ) := by push_cast; ring
    rw [this]; exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hbase2 : ∀ n : ℕ, ((n:ℂ)+1-(a:ℂ)) ≠ 0 := by
    intro n
    have : ((n:ℂ)+1-(a:ℂ)) = (((n:ℝ)+1-a : ℝ):ℂ) := by push_cast; ring
    rw [this]; refine Complex.ofReal_ne_zero.mpr (ne_of_gt ?_)
    have : (0:ℝ) ≤ n := by positivity
    linarith
  have hab : ∀ n : ℕ, Tendsto (fun m => f m n) atTop (𝓝 (g n)) := by
    intro n
    have hF : ContinuousAt (fun s:ℂ => (1/((n:ℂ)+(a:ℂ))^s - 1/((n:ℂ)+1-(a:ℂ))^s)/2) 1 := by
      apply ContinuousAt.div_const
      apply ContinuousAt.sub
      · simp only [one_div]
        exact (continuousAt_const_cpow (hbase1 n)).inv₀
          (by rw [Complex.cpow_one]; exact hbase1 n)
      · simp only [one_div]
        exact (continuousAt_const_cpow (hbase2 n)).inv₀
          (by rw [Complex.cpow_one]; exact hbase2 n)
    have huc : Tendsto (fun m => (↑(u m) : ℂ)) atTop (𝓝 (1:ℂ)) := by
      have : Tendsto (fun m : ℕ => u m) atTop (𝓝 (1:ℝ)) := by
        rw [hu]
        simpa using (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun m : ℕ => (1:ℝ) + 1/((m:ℝ)+1)) atTop (𝓝 (1+0)))
      exact (Complex.continuous_ofReal.tendsto 1).comp this
    have hcomp := (hF.tendsto).comp huc
    show Tendsto (fun m => (1/((n:ℂ)+(a:ℂ))^(↑(u m):ℂ) - 1/((n:ℂ)+1-(a:ℂ))^(↑(u m):ℂ))/2)
        atTop (𝓝 (g n))
    have hg1 : (1/((n:ℂ)+(a:ℂ))^(1:ℂ) - 1/((n:ℂ)+1-(a:ℂ))^(1:ℂ))/2 = g n := by
      simp only [Complex.cpow_one, hg]
    rw [← hg1]
    exact hcomp
  have hboundev : ∀ᶠ m in atTop, ∀ n, ‖f m n‖ ≤ bnd n := by
    apply Filter.Eventually.of_forall
    intro m n
    rw [hf, hbnd]; simp only
    exact cterm_norm_bound a ha0 ha1 (u m) (hu_gt m).le (hu_le m) n
  have hC' : Tendsto (fun m => ∑' n, f m n) atTop (𝓝 (∑' n, g n)) :=
    tendsto_tsum_of_dominated_convergence hsum hab hboundev
  -- combine
  have hAeq : Tendsto (fun m => hurwitzZetaOdd (↑a) (↑(u m))) atTop (𝓝 (∑' n, g n)) := by
    apply hC'.congr; intro m; exact (hB m).symm
  exact tendsto_nhds_unique hcontA hAeq

open scoped Real in
theorem hurwitzZetaOdd_one_value (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    hurwitzZetaOdd (↑a) 1 = (↑π/2 : ℂ) * Complex.cot (↑π * ↑a) := by
  rw [hurwitzZetaOdd_one_eq_tsum a ha0 ha1]
  have hx : (↑a:ℂ) ∈ Complex.integerComplement := by
    rw [Complex.integerComplement.mem_iff]
    rintro ⟨n, hn⟩
    have hna : (n:ℝ) = a := by exact_mod_cast hn
    have h0 : (0:ℝ) < n := hna ▸ ha0
    have h1 : (n:ℝ) < 1 := hna ▸ ha1
    have : (0:ℤ) < n := by exact_mod_cast h0
    have : n < 1 := by exact_mod_cast h1
    omega
  have hcot := cot_value_sum (↑a) hx
  have hterm : (fun n : ℕ => (1/((n:ℂ)+(a:ℂ)) - 1/((n:ℂ)+1-(a:ℂ)))/2)
      = (fun n : ℕ => (1/((↑a:ℂ)+(n:ℂ)) - 1/((n:ℂ)+1-(↑a:ℂ))) / 2) := by
    funext n; rw [add_comm (↑a:ℂ) (n:ℂ)]
  rw [hterm, tsum_div_const, hcot]
  ring

open scoped Real in
lemma cot_sum_eq_LFunction (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m)
    (hodd : Function.Odd (fun a : ZMod m => χ a)) :
    ∑ j : ZMod m, χ j * Complex.cot ((π:ℂ) * (j.val:ℂ) / (m:ℂ))
      = (2 * (m:ℂ) / (π:ℂ)) * χ.LFunction 1 := by
  have hmπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hzo0 : hurwitzZetaOdd (0 : UnitAddCircle) 1 = 0 := by
    have := hurwitzZetaOdd_neg (0 : UnitAddCircle) 1
    rw [neg_zero] at this
    linear_combination this / 2
  rw [DirichletCharacter.LFunction, ZMod.LFunction_def_odd hodd 1, Complex.cpow_neg_one]
  have hterm : ∀ j : ZMod m, (χ j) * hurwitzZetaOdd (ZMod.toAddCircle j) 1
      = (π:ℂ)/2 * (χ j * Complex.cot ((π:ℂ)*(j.val:ℂ)/(m:ℂ))) := by
    intro j
    rcases eq_or_ne j 0 with hj | hj
    · subst hj
      rw [ZMod.toAddCircle_apply]
      rw [show (((0:ZMod m).val : ℝ)/m : ℝ) = (0:ℝ) by simp,
        show ((0:ℝ):UnitAddCircle) = 0 by simp, hzo0]
      have hc0 : Complex.cot ((π:ℂ)*((0:ZMod m).val:ℂ)/(m:ℂ)) = 0 := by
        simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div]
        rw [Complex.cot_eq_cos_div_sin, Complex.sin_zero, div_zero]
      rw [hc0]; ring
    · have hval1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr (by rwa [ne_eq, ZMod.val_eq_zero])
      have hvalm : j.val < m := ZMod.val_lt j
      have hmr : (0:ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
      set a : ℝ := (j.val:ℝ)/m with ha
      have ha0 : 0 < a := by rw [ha]; positivity
      have ha1 : a < 1 := by rw [ha, div_lt_one hmr]; exact_mod_cast hvalm
      rw [ZMod.toAddCircle_apply, hurwitzZetaOdd_one_value a ha0 ha1]
      have hcot : Complex.cot ((π:ℂ)*((a:ℝ):ℂ)) = Complex.cot ((π:ℂ)*(j.val:ℂ)/(m:ℂ)) := by
        congr 1; rw [ha]; push_cast; ring
      rw [hcot]; ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]
  field_simp

open scoped ComplexOrder in
open scoped Real in
lemma cot_sum_even_zero (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m) (hev : χ (-1) = 1) :
    ∑ j : ZMod m, χ j * Complex.cot ((π:ℂ) * (j.val:ℂ) / (m:ℂ)) = 0 := by
  have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hneg : ∀ j : ZMod m, χ (-j) * Complex.cot ((π:ℂ)*((-j).val:ℂ)/(m:ℂ))
      = -(χ j * Complex.cot ((π:ℂ)*(j.val:ℂ)/(m:ℂ))) := by
    intro j
    have h1 : χ (-j) = χ j := by rw [show (-j) = (-1)*j by ring, map_mul, hev, one_mul]
    have h2 : Complex.cot ((π:ℂ)*((-j).val:ℂ)/(m:ℂ)) = -Complex.cot ((π:ℂ)*(j.val:ℂ)/(m:ℂ)) := by
      rcases eq_or_ne j 0 with hj0 | hj0
      · subst hj0; simp [Complex.cot_eq_cos_div_sin, Complex.sin_zero]
      · rw [ZMod.neg_val, if_neg hj0]
        have hle : j.val ≤ m := (ZMod.val_lt j).le
        rw [Nat.cast_sub hle]
        have harg : (π:ℂ)*((m:ℂ)-(j.val:ℂ))/m = (π:ℂ) - ((π:ℂ)*(j.val:ℂ)/m) := by
          field_simp
        rw [harg, Complex.cot_eq_cos_div_sin, Complex.cos_pi_sub, Complex.sin_pi_sub,
            Complex.cot_eq_cos_div_sin]
        ring
    rw [h1, h2]; ring
  have hsum := (Equiv.sum_comp (Equiv.neg (ZMod m))
    (fun j : ZMod m => χ j * Complex.cot ((π:ℂ)*(j.val:ℂ)/(m:ℂ)))).symm
  have key : (∑ j : ZMod m, χ j * Complex.cot ((π:ℂ)*(j.val:ℂ)/(m:ℂ)))
      = -(∑ j : ZMod m, χ j * Complex.cot ((π:ℂ)*(j.val:ℂ)/(m:ℂ))) := by
    conv_lhs => rw [hsum]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Equiv.neg_apply]
    exact hneg j
  exact CharZero.neg_eq_self_iff.mp key.symm

open scoped ComplexOrder in
open scoped Real in
lemma cotsum_re_nonneg (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m) (hq : χ ^ 2 = 1) :
    0 ≤ (∑ j : ZMod m, χ j * Complex.cot ((π:ℂ) * (j.val:ℂ) / (m:ℂ))).re := by
  have hpm : χ (-1) = 1 ∨ χ (-1) = -1 := by
    have h : (χ (-1))^2 = 1 := by rw [← map_pow]; rw [show ((-1:ZMod m))^2 = 1 by ring, map_one]
    have h' : χ (-1) * χ (-1) = 1 := by rw [← pow_two]; exact h
    rcases mul_self_eq_one_iff.mp h' with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  rcases hpm with hev | hodd
  · rw [cot_sum_even_zero m χ hev]; simp
  · have hodd' : Function.Odd (fun a : ZMod m => χ a) := by
      intro a; show χ (-a) = -χ a
      rw [show -a = (-1)*a by ring, map_mul, hodd, neg_one_mul]
    have hne1 : χ ≠ 1 := by
      intro h; rw [h, MulChar.one_apply (IsUnit.neg isUnit_one)] at hodd
      exact absurd hodd (by norm_num)
    rw [cot_sum_eq_LFunction m χ hodd']
    have hL := DirichletCharacter.LFunction_one_pos hq hne1
    rw [Complex.pos_iff] at hL
    have hfac : (2*(m:ℂ)/(π:ℂ)) = (((2*m/π : ℝ)):ℂ) := by push_cast; ring
    rw [hfac, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h1 : (0:ℝ) ≤ 2*(m:ℝ)/π := by positivity
    exact mul_nonneg h1 hL.1.le
end BridgeSection

section FinalSection
open Finset Complex
open scoped Real

lemma gs_one_eq_gaussSumC (N : ℕ) : gs N 1 = gaussSumC N := by
  unfold gs gaussSumC
  apply Finset.sum_congr rfl
  intro k _
  rw [zeta_zpow]
  congr 1
  push_cast
  ring

lemma negI_pow_four (q : ℕ) : (-I) ^ (4 * q) = 1 := by
  rw [pow_mul]
  rw [show (-I)^4 = 1 by rw [show (4:ℕ) = 2+2 by rfl, pow_add, sq]; rw [neg_mul_neg, Complex.I_mul_I]; ring]
  rw [one_pow]

lemma gs_one_odd_value (m : ℕ) (hm : Odd m) (hpos : 0 < m) :
    gs m 1 = if m % 4 = 1 then ((Real.sqrt m : ℝ):ℂ) else I * ((Real.sqrt m : ℝ):ℂ) := by
  rw [gs_one_eq_gaussSumC, gaussSumC_value m hpos]
  obtain ⟨q, r, hr, hmr⟩ : ∃ q r, (r = 1 ∨ r = 3) ∧ m = 4*q + r := by
    obtain ⟨j, hj⟩ := hm
    refine ⟨m/4, m%4, ?_, by omega⟩
    omega
  have hnegI : (-I:ℂ)^m = (-I)^r := by
    rw [hmr, pow_add, negI_pow_four, one_mul]
  have hmod : m % 4 = r := by omega
  rw [hnegI, hmod]
  rcases hr with rfl | rfl
  · -- r = 1
    rw [if_pos rfl]
    rw [pow_one]
    have : (1 + -I) = (1 - I) := by ring
    rw [this]
    rw [show ((Real.sqrt m:ℝ):ℂ) * (1+I)/2 * (1-I) = ((Real.sqrt m:ℝ):ℂ) * ((1+I)*(1-I)/2) by ring]
    rw [show (1+I)*(1-I) = (2:ℂ) by rw [show (1+I)*(1-I) = 1 - I*I by ring, Complex.I_mul_I]; ring]
    ring
  · -- r = 3
    rw [if_neg (by norm_num)]
    have h3 : (-I:ℂ)^3 = I := by
      rw [show (3:ℕ) = 2+1 by rfl, pow_add, sq, pow_one, neg_mul_neg, Complex.I_mul_I]; ring
    rw [h3]
    rw [show ((Real.sqrt m:ℝ):ℂ) * (1+I)/2 * (1+I) = ((Real.sqrt m:ℝ):ℂ) * ((1+I)*(1+I)/2) by ring]
    rw [show (1+I)*(1+I) = (2:ℂ)*I by rw [show (1+I)*(1+I) = 1 + 2*I + I*I by ring, Complex.I_mul_I]; ring]
    ring

lemma gs_scale (d m : ℕ) (hd : 0 < d) (hm : 0 < m) (t₀ : ℤ) :
    gs (d * m) (d * t₀) = (d : ℂ) * gs m t₀ := by
  unfold gs
  have hsumm : ∀ k : ℕ, zeta (d*m) ^ ((d*t₀) * (k:ℤ)^2) = zeta m ^ (t₀ * (k:ℤ)^2) := by
    intro k
    have hdvd : d ∣ d * m := dvd_mul_right d m
    have := zeta_div_pow (d*m) d hdvd (t₀ * (k:ℤ)^2)
    rw [Nat.mul_div_cancel_left m hd] at this
    rw [this]
    congr 1
    ring
  simp_rw [hsumm]
  -- now ∑_{k∈range (d*m)} f k = d • ∑_{k∈range m} f k
  set f : ℕ → ℂ := fun k => zeta m ^ (t₀ * (k:ℤ)^2) with hf
  have hper : ∀ k, f (k + m) = f k := by
    intro k
    simp only [hf]
    have hexp : t₀ * ((k + m : ℕ):ℤ)^2 = t₀ * (k:ℤ)^2 + (m:ℤ) * (t₀ * (2*(k:ℤ) + (m:ℤ))) := by
      push_cast; ring
    rw [hexp, zpow_add₀ (zeta_ne_zero m)]
    have h1 : zeta m ^ ((m:ℤ) * (t₀ * (2*(k:ℤ) + (m:ℤ)))) = 1 := by
      rw [zpow_mul, zpow_natCast, zeta_pow_n m hm, one_zpow]
    rw [h1, mul_one]
  have hps := periodic_sum m f hper d
  rw [hps, nsmul_eq_mul]

/-- The Jacobi-symbol Dirichlet character mod `m`. -/
noncomputable def jacobiChar (m : ℕ) [NeZero m] : DirichletCharacter ℂ m :=
  MulChar.mk
    { toFun := fun x => ((jacobiSym (x.val : ℤ) m : ℤ) : ℂ)
      map_one' := by
        show ((jacobiSym ((1 : ZMod m).val : ℤ) m : ℤ) : ℂ) = 1
        rcases eq_or_ne m 1 with h1 | h1
        · subst h1
          simp [jacobiSym.one_right]
        · have hf : Fact (1 < m) := ⟨by have := (NeZero.ne m); omega⟩
          rw [ZMod.val_one]
          simp [jacobiSym.one_left]
      map_mul' := by
        intro x y
        show ((jacobiSym (((x*y).val : ℤ)) m : ℤ) : ℂ)
          = ((jacobiSym ((x.val:ℤ)) m : ℤ):ℂ) * ((jacobiSym ((y.val:ℤ)) m :ℤ):ℂ)
        have key : jacobiSym (((x*y).val : ℤ)) m
            = jacobiSym (x.val:ℤ) m * jacobiSym (y.val:ℤ) m := by
          rw [← jacobiSym.mul_left]
          rw [jacobiSym.mod_left ((x.val:ℤ)*(y.val:ℤ)) m,
              jacobiSym.mod_left (((x*y).val:ℤ)) m]
          congr 1
          rw [ZMod.val_mul]
          push_cast [Int.natCast_mod]
          exact Int.emod_emod_of_dvd _ (dvd_refl _)
        rw [key]; push_cast; ring }
    (by
      intro a ha
      show ((jacobiSym ((a.val:ℤ)) m :ℤ):ℂ) = 0
      have haeq : (↑(a.val) : ZMod m) = a := by rw [ZMod.natCast_val, ZMod.cast_id]
      have hcop : ¬ (a.val).Coprime m := by
        rw [← ZMod.isUnit_iff_coprime, haeq]; exact ha
      have hz : jacobiSym (a.val : ℤ) m = 0 := by
        rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]; exact hcop
      rw [hz]; simp)

@[simp] lemma jacobiChar_apply (m : ℕ) [NeZero m] (x : ZMod m) :
    jacobiChar m x = ((jacobiSym (x.val : ℤ) m : ℤ) : ℂ) := rfl

lemma jacobiChar_sq (m : ℕ) [NeZero m] : (jacobiChar m)^2 = 1 := by
  apply MulChar.ext
  intro a
  rw [sq, MulChar.mul_apply, MulChar.one_apply a.isUnit, jacobiChar_apply]
  have hcop : ((a : ZMod m).val : ℤ).gcd m = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact ZMod.val_coe_unit_coprime a
  rcases jacobiSym.eq_one_or_neg_one hcop with h | h <;> rw [h] <;> norm_num

lemma zmod_sum_range (m : ℕ) [NeZero m] (F : ZMod m → ℂ) :
    ∑ j : ZMod m, F j = ∑ s ∈ Finset.range m, F (s : ZMod m) := by
  apply Finset.sum_nbij' (fun j : ZMod m => (j.val : ℕ)) (fun s : ℕ => (s : ZMod m))
  · intro a _; simp only [Finset.mem_range]; exact ZMod.val_lt a
  · intro a _; exact Finset.mem_univ _
  · intro a _; rw [ZMod.natCast_val, ZMod.cast_id]
  · intro a ha; rw [Finset.mem_range] at ha; rw [ZMod.val_natCast_of_lt ha]
  · intro a _; rw [ZMod.natCast_val, ZMod.cast_id]

/-- The cotangent-weighted Gauss-sum-imaginary sum at modulus `m`. -/
noncomputable def Pchar (m : ℕ) : ℝ :=
  ∑ s ∈ Finset.filter (fun s => Nat.Coprime s m) (Finset.Ico 1 m),
    (gs m (s:ℤ)).im * Real.cot (Real.pi * (s:ℝ) / (m:ℝ))

lemma char_unit_real {m : ℕ} (χ : DirichletCharacter ℂ m) (hq : χ ^ 2 = 1)
    (x : ZMod m) (hx : IsUnit x) : χ x = 1 ∨ χ x = -1 := by
  have h : (χ x) * (χ x) = 1 := by
    rw [← MulChar.mul_apply, ← sq, hq, MulChar.one_apply hx]
  exact mul_self_eq_one_iff.mp h

lemma P_nonneg_of_char (m : ℕ) (hm : 2 ≤ m) (χ : DirichletCharacter ℂ m)
    (hq : χ ^ 2 = 1) (hpos : 0 ≤ (gs m 1).im)
    (hid : ∀ s : ℕ, Nat.Coprime s m → (gs m (s:ℤ)).im = (gs m 1).im * (χ (s : ZMod m)).re) :
    0 ≤ Pchar m := by
  have hne : NeZero m := ⟨by omega⟩
  -- the cot character sum over ZMod
  set cs : ℂ := ∑ j : ZMod m, χ j * Complex.cot ((Real.pi:ℂ) * (j.val:ℂ) / (m:ℂ)) with hcs
  have hcsre : 0 ≤ cs.re := cotsum_re_nonneg m χ hq
  -- rewrite cs over range m
  have hcs2 : cs = ∑ s ∈ Finset.range m,
      χ (s : ZMod m) * Complex.cot ((Real.pi:ℂ) * (s:ℂ) / (m:ℂ)) := by
    rw [hcs, zmod_sum_range m]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    rw [ZMod.val_natCast_of_lt hs]
  -- range m = {0} insert (Ico 1 m); zero term vanishes
  have hsplit : ∑ s ∈ Finset.range m,
      χ (s : ZMod m) * Complex.cot ((Real.pi:ℂ) * (s:ℂ) / (m:ℂ))
      = ∑ s ∈ Finset.Ico 1 m,
      χ (s : ZMod m) * Complex.cot ((Real.pi:ℂ) * (s:ℂ) / (m:ℂ)) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ m)]
    have h0 : ¬ IsUnit (0 : ZMod m) := by
      haveI : Fact (1 < m) := ⟨by omega⟩
      rw [isUnit_zero_iff]; exact zero_ne_one
    have hz : ∑ s ∈ (Finset.Ico 0 1 : Finset ℕ),
        χ (s : ZMod m) * Complex.cot ((Real.pi:ℂ) * (s:ℂ) / (m:ℂ)) = 0 := by
      rw [Nat.Ico_zero_eq_range, Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
        MulChar.map_nonunit χ h0, zero_mul]
    rw [hz, zero_add]
  -- restrict to coprime
  have hcop : ∑ s ∈ Finset.Ico 1 m,
      χ (s : ZMod m) * Complex.cot ((Real.pi:ℂ) * (s:ℂ) / (m:ℂ))
      = ∑ s ∈ Finset.filter (fun s => Nat.Coprime s m) (Finset.Ico 1 m),
      χ (s : ZMod m) * Complex.cot ((Real.pi:ℂ) * (s:ℂ) / (m:ℂ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 m) (fun s => Nat.Coprime s m)]
    have hz : ∑ s ∈ Finset.filter (fun s => ¬ Nat.Coprime s m) (Finset.Ico 1 m),
        χ (s : ZMod m) * Complex.cot ((Real.pi:ℂ) * (s:ℂ) / (m:ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      rw [Finset.mem_filter] at hs
      have : ¬ IsUnit ((s:ℕ) : ZMod m) := by
        rw [ZMod.isUnit_iff_coprime]; exact hs.2
      rw [MulChar.map_nonunit χ this, zero_mul]
    rw [hz, add_zero]
  -- combine
  have hcsval : cs = ∑ s ∈ Finset.filter (fun s => Nat.Coprime s m) (Finset.Ico 1 m),
      χ (s : ZMod m) * Complex.cot ((Real.pi:ℂ) * (s:ℂ) / (m:ℂ)) := by
    rw [hcs2, hsplit, hcop]
  -- Pchar = (gs m 1).im * cs.re
  have hPeq : Pchar m = (gs m 1).im * cs.re := by
    rw [hcsval, Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_filter] at hs
    have harg : ((Real.pi:ℂ) * (s:ℂ) / (m:ℂ)) = ((Real.pi * (s:ℝ) / (m:ℝ) : ℝ):ℂ) := by
      push_cast; ring
    rw [harg, ← Complex.ofReal_cot]
    have hxre : (χ (s : ZMod m) * ((Real.cot (Real.pi * (s:ℝ) / (m:ℝ)) : ℝ):ℂ)).re
        = (χ (s : ZMod m)).re * Real.cot (Real.pi * (s:ℝ) / (m:ℝ)) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hxre, hid s hs.2]
    ring
  rw [hPeq]
  exact mul_nonneg hpos hcsre

lemma gs_one_im_nonneg (m : ℕ) (hm : 0 < m) : 0 ≤ (gs m 1).im := by
  rw [gs_one_eq_gaussSumC, gaussSumC_value m hm]
  obtain ⟨q, r, hr, hmr⟩ : ∃ q r, (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) ∧ m = 4*q + r :=
    ⟨m/4, m%4, by omega, by omega⟩
  have hnegI : (-I:ℂ)^m = (-I)^r := by rw [hmr, pow_add, negI_pow_four, one_mul]
  have hsqrt : (0:ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  rw [hnegI]
  rcases hr with rfl | rfl | rfl | rfl
  · simp only [pow_zero]
    rw [show ((Real.sqrt m:ℝ):ℂ) * (1+I)/2 * (1+1) = ((Real.sqrt m:ℝ):ℂ) * (1+I) by ring]
    simp [Complex.mul_im, Complex.add_im]
  · simp only [pow_one]
    rw [show ((Real.sqrt m:ℝ):ℂ) * (1+I)/2 * (1+(-I)) = ((Real.sqrt m:ℝ):ℂ) * ((1+I)*(1-I)/2) by ring,
       show (1+I)*(1-I) = (2:ℂ) by rw [show (1+I)*(1-I)=1-I*I by ring, Complex.I_mul_I]; ring]
    simp [Complex.mul_im]
  · rw [show (-I:ℂ)^2 = -1 by rw [sq, neg_mul_neg, Complex.I_mul_I],
       show ((Real.sqrt m:ℝ):ℂ) * (1+I)/2 * (1+-1) = 0 by ring]
    simp
  · rw [show (-I:ℂ)^3 = I by rw [show (3:ℕ)=2+1 by rfl, pow_add, sq, pow_one, neg_mul_neg, Complex.I_mul_I]; ring,
       show ((Real.sqrt m:ℝ):ℂ) * (1+I)/2 * (1+I) = ((Real.sqrt m:ℝ):ℂ) * ((1+I)*(1+I)/2) by ring,
       show (1+I)*(1+I) = (2:ℂ)*I by rw [show (1+I)*(1+I)=1+2*I+I*I by ring, Complex.I_mul_I]; ring]
    simp [Complex.mul_im]

lemma gs_im_jacobi (m : ℕ) [NeZero m] (hm : Odd m) (s : ℕ) (hcop : Nat.Coprime s m) :
    (gs m (s:ℤ)).im = (gs m 1).im * (jacobiChar m (s : ZMod m)).re := by
  have hpos : 0 < m := by rcases hm with ⟨k, hk⟩; omega
  haveI : NeZero m := ⟨by omega⟩
  have hcopZ : IsCoprime (s:ℤ) (m:ℤ) := (Nat.isCoprime_iff_coprime).mpr hcop
  have hg := gs_odd_jacobi m hm (s:ℤ) hcopZ
  have hjs : jacobiSym ((s:ZMod m).val : ℤ) m = jacobiSym (s:ℤ) m := by
    rw [jacobiSym.mod_left (s:ℤ) m, ZMod.val_natCast]
    congr 1
  have hjeq : jacobiChar m (s : ZMod m) = ((jacobiSym (s:ℤ) m : ℤ) : ℂ) := by
    rw [jacobiChar_apply, hjs]
  rw [hg, hjeq, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]
  ring

lemma gs_two_val (t : ℤ) : gs 2 t = 1 + (-1 : ℂ) ^ t := by
  unfold gs
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zeta_two]
  norm_num

lemma gs_two_mod4_eq_zero (m : ℕ) (hm4 : m % 4 = 2) (t : ℤ) (ht : Odd t) :
    gs m t = 0 := by
  set m₀ := m / 2 with hm0def
  have hmeq : m = 2 * m₀ := by omega
  have hm0odd : Odd m₀ := by
    rcases Nat.even_or_odd m₀ with he | ho
    · exfalso; obtain ⟨c, hc⟩ := he; omega
    · exact ho
  haveI : NeZero m₀ := ⟨by rcases hm0odd with ⟨k, hk⟩; omega⟩
  have hcop2 : Nat.Coprime 2 m₀ := Nat.coprime_two_left.mpr hm0odd
  have hic : IsCoprime (m₀:ℤ) (2:ℤ) :=
    (Nat.isCoprime_iff_coprime).mpr hcop2.symm
  obtain ⟨a, b, hab⟩ := hic
  -- gs(2*m₀) t = gs 2 (a t) * gs m₀ (b t)
  have hcrt := gs_crt 2 m₀ (by norm_num) (by rcases hm0odd with ⟨k, hk⟩; omega)
    hcop2 a b (by push_cast; linear_combination hab) t
  rw [hmeq, hcrt]
  -- gs 2 (a*t) = 0 since a*t odd
  have haodd : Odd a := by
    have hodd : Odd (a * (m₀:ℤ)) := by
      have heq : a * (m₀:ℤ) = 1 - b*2 := by linarith [hab]
      rw [heq]; exact ⟨-b, by ring⟩
    rw [Int.odd_mul] at hodd
    exact hodd.1
  have hatodd : Odd (a * t) := haodd.mul ht
  have : gs 2 (a * t) = 0 := by
    rw [gs_two_val, Odd.neg_one_zpow hatodd]; ring
  rw [this, zero_mul]

lemma Pchar_nonneg_two_mod4 (m : ℕ) (hm4 : m % 4 = 2) : 0 ≤ Pchar m := by
  have hm2 : 2 ≤ m := by omega
  haveI : NeZero m := ⟨by omega⟩
  refine P_nonneg_of_char m hm2 (jacobiChar m) (jacobiChar_sq m)
    (gs_one_im_nonneg m (by omega)) (fun s hs => ?_)
  -- s coprime to m (even) ⇒ s odd ⇒ gs = 0
  have hmeven : 2 ∣ m := by omega
  have hsodd : Odd s := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    have hd : 2 ∣ Nat.gcd s m := Nat.dvd_gcd h.two_dvd hmeven
    rw [Nat.Coprime] at hs
    omega
  have h1 : gs m 1 = 0 := gs_two_mod4_eq_zero m hm4 1 ⟨0, by ring⟩
  have hs0 : gs m (s:ℤ) = 0 :=
    gs_two_mod4_eq_zero m hm4 (s:ℤ) (by exact_mod_cast hsodd)
  rw [hs0, h1]; simp

lemma Pchar_nonneg_odd (m : ℕ) (hm : Odd m) (hm2 : 2 ≤ m) : 0 ≤ Pchar m := by
  haveI : NeZero m := ⟨by omega⟩
  exact P_nonneg_of_char m hm2 (jacobiChar m) (jacobiChar_sq m)
    (gs_one_im_nonneg m (by omega)) (fun s hs => gs_im_jacobi m hm s hs)

lemma jacobiSym_val_eq (m₀ : ℕ) [NeZero m₀] (s : ℕ) :
    jacobiSym ((s : ZMod m₀).val : ℤ) m₀ = jacobiSym (s:ℤ) m₀ := by
  rw [jacobiSym.mod_left (s:ℤ) m₀, ZMod.val_natCast]
  congr 1

lemma changeLevel_jacobi_apply (m m₀ : ℕ) [NeZero m] [NeZero m₀] (h : m₀ ∣ m)
    (s : ℕ) (hco : Nat.Coprime s m) :
    (DirichletCharacter.changeLevel h (jacobiChar m₀)) (s : ZMod m)
      = ((jacobiSym (s:ℤ) m₀ : ℤ) : ℂ) := by
  have hu := DirichletCharacter.changeLevel_eq_cast_of_dvd (jacobiChar m₀) h
    (ZMod.unitOfCoprime s hco)
  rw [ZMod.coe_unitOfCoprime] at hu
  rw [hu]
  have hcast : ((s : ZMod m)).cast = (s : ZMod m₀) := by
    rw [ZMod.cast_natCast h]
  rw [hcast, jacobiChar_apply, jacobiSym_val_eq]

lemma I_zpow_odd_re (s : ℤ) (hs : Odd s) : (I^s).re = 0 := by
  rw [I_zpow_odd s hs]; split <;> simp
lemma I_zpow_odd_im (s : ℤ) (hs : Odd s) : (I^s).im = if s % 4 = 1 then (1:ℝ) else -1 := by
  rw [I_zpow_odd s hs]; split <;> simp

lemma changeLevel_two_apply (m c : ℕ) [NeZero m] [NeZero c] (hc : c ∣ m)
    (ψ : MulChar (ZMod c) ℤ) (s : ℕ) (hco : Nat.Coprime s m) :
    (DirichletCharacter.changeLevel hc (ψ.ringHomComp (Int.castRingHom ℂ))) (s : ZMod m)
      = ((ψ (s : ZMod c) : ℤ) : ℂ) := by
  have hu := DirichletCharacter.changeLevel_eq_cast_of_dvd (ψ.ringHomComp (Int.castRingHom ℂ)) hc
    (ZMod.unitOfCoprime s hco)
  rw [ZMod.coe_unitOfCoprime] at hu
  rw [hu, MulChar.ringHomComp_apply,
      show ((s:ZMod m)).cast = (s:ZMod c) from ZMod.cast_natCast hc s]
  rfl

lemma I_zpow_im_chi4 (x : ℤ) (hx : Odd x) :
    (I ^ x).im = ((ZMod.χ₄ (x : ZMod 4) : ℤ) : ℝ) := by
  rw [I_zpow_odd_im x hx, ZMod.χ₄_int_eq_if_mod_four]
  have hx2 : x % 2 ≠ 0 := by rcases hx with ⟨k, hk⟩; omega
  rw [if_neg hx2]
  by_cases h : x % 4 = 1 <;> simp [h]

lemma zeta8_im_chi8' (x : ℤ) (hx : Odd x) :
    (zeta 8 ^ x).im = (Real.sqrt 2 / 2) * ((ZMod.χ₈' (x : ZMod 8) : ℤ) : ℝ) := by
  rw [(zeta_eight_zpow_reim x hx).2, ZMod.χ₈'_int_eq_if_mod_eight]
  have hx2 : x % 2 ≠ 0 := by rcases hx with ⟨k, hk⟩; omega
  rw [if_neg hx2]
  by_cases h : x % 8 = 1 ∨ x % 8 = 3 <;> simp [h]

lemma zeta8_re_chi8 (x : ℤ) (hx : Odd x) :
    (zeta 8 ^ x).re = (Real.sqrt 2 / 2) * ((ZMod.χ₈ (x : ZMod 8) : ℤ) : ℝ) := by
  rw [(zeta_eight_zpow_reim x hx).1, ZMod.χ₈_int_eq_if_mod_eight]
  have hx2 : x % 2 ≠ 0 := by rcases hx with ⟨k, hk⟩; omega
  rw [if_neg hx2]
  by_cases h : x % 8 = 1 ∨ x % 8 = 7 <;> simp [h]

lemma zero_mod4_crt (m : ℕ) (hm4 : m % 4 = 0) (hm2 : 2 ≤ m) :
    ∃ (a m₀ : ℕ) (α β : ℤ), 2 ≤ a ∧ Odd m₀ ∧ 0 < m₀ ∧ m = 2 ^ a * m₀ ∧
      Odd α ∧ m₀ ∣ m ∧ IsCoprime β (m₀ : ℤ) ∧
      (∀ t : ℤ, gs m t = gs (2 ^ a) (α * t) * gs m₀ (β * t)) := by
  have hm0 : m ≠ 0 := by omega
  set a := m.factorization 2 with hadef
  set m₀ := m / 2 ^ a with hm0def
  have hdvd : 2 ^ a ∣ m := Nat.ordProj_dvd m 2
  have hsplit : 2 ^ a * m₀ = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have hm0odd : Odd m₀ := by
    have h2 : ¬ 2 ∣ m₀ := Nat.not_dvd_ordCompl Nat.prime_two hm0
    rw [Nat.odd_iff]; omega
  have hm0pos : 0 < m₀ := Nat.ordCompl_pos 2 hm0
  have ha2 : 2 ≤ a := by
    rw [hadef, ← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0]
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [← this]; omega
  have hcop : Nat.Coprime (2 ^ a) m₀ :=
    (Nat.coprime_two_left.mpr hm0odd).pow_left a
  haveI : NeZero (2 ^ a) := ⟨by positivity⟩
  haveI : NeZero m₀ := ⟨hm0pos.ne'⟩
  have hicop : IsCoprime ((2 ^ a : ℕ) : ℤ) ((m₀ : ℕ) : ℤ) :=
    (Nat.isCoprime_iff_coprime).mpr hcop
  obtain ⟨α, β, hab⟩ := hicop.symm  -- α * m₀ + β * 2^a = 1
  have haodd : Odd α := by
    have hodd : Odd (α * (m₀ : ℤ)) := by
      have heq : α * (m₀ : ℤ) = 1 - β * (2 ^ a : ℕ) := by
        push_cast at hab ⊢; linarith [hab]
      rw [heq]
      have h2a : (2:ℤ) ∣ ((2 ^ a : ℕ) : ℤ) := by
        have : (2:ℤ) ∣ (2:ℤ)^a := dvd_pow_self 2 (by omega : a ≠ 0)
        push_cast; exact this
      obtain ⟨c, hc⟩ := h2a
      rw [hc]; exact ⟨-(β * c), by ring⟩
    exact (Int.odd_mul.mp hodd).1
  have hbcop : IsCoprime β (m₀ : ℤ) := by
    refine ⟨((2 ^ a : ℕ) : ℤ), α, ?_⟩
    push_cast at hab ⊢; linarith [hab]
  refine ⟨a, m₀, α, β, ha2, hm0odd, hm0pos, hsplit.symm, haodd,
    ⟨2 ^ a, by rw [← hsplit]; ring⟩, hbcop, ?_⟩
  intro t
  have := gs_crt (2 ^ a) m₀ (by positivity) hm0pos hcop α β
    (by push_cast at hab ⊢; linarith [hab]) t
  rw [← hsplit]
  exact this

lemma changeLevel_sq {n m : ℕ} (h : n ∣ m) (χ : DirichletCharacter ℂ n) (hχ : χ ^ 2 = 1) :
    (DirichletCharacter.changeLevel h χ) ^ 2 = 1 := by
  rw [← map_pow, hχ, map_one]

lemma Pchar_nonneg_zero_mod4 (m : ℕ) (hm4 : m % 4 = 0) (hm2 : 2 ≤ m) : 0 ≤ Pchar m := by
  obtain ⟨a, m₀, α, β, ha2, hm0odd, hm0pos, hmeq, haodd, hm0dvd, hbcop, hgs⟩ :=
    zero_mod4_crt m hm4 hm2
  haveI hNZm : NeZero m := ⟨by omega⟩
  haveI hNZm0 : NeZero m₀ := ⟨hm0pos.ne'⟩
  have hgm1 : gs m₀ 1 =
      if m₀ % 4 = 1 then ((Real.sqrt m₀ : ℝ) : ℂ) else I * ((Real.sqrt m₀ : ℝ) : ℂ) :=
    gs_one_odd_value m₀ hm0odd hm0pos
  have h2m : 2 ∣ m := by omega
  have hsodd : ∀ s : ℕ, Nat.Coprime s m → Odd s := by
    intro s hs
    rw [Nat.odd_iff]
    rcases Nat.even_or_odd s with he | ho
    · exfalso; rw [Nat.Coprime] at hs
      have := Nat.dvd_gcd he.two_dvd h2m; omega
    · exact Nat.odd_iff.mp ho
  have hscop0 : ∀ s : ℕ, Nat.Coprime s m → IsCoprime (s : ℤ) (m₀ : ℤ) := by
    intro s hs
    exact (Nat.isCoprime_iff_coprime).mpr (hs.coprime_dvd_right hm0dvd)
  have hfac : ∀ s : ℕ, Nat.Coprime s m →
      gs m (s:ℤ) = gs (2^a) (α*(s:ℤ)) * ((jacobiSym (β*(s:ℤ)) m₀ : ℤ):ℂ) * gs m₀ 1 := by
    intro s hs
    rw [hgs (s:ℤ), gs_odd_jacobi m₀ hm0odd (β*(s:ℤ)) (hbcop.mul_left (hscop0 s hs))]
    ring
  set Q : ℕ → ℝ := fun s => (gs (2^a) (α*(s:ℤ)) * gs m₀ 1).im with hQdef
  have hQ : ∀ s : ℕ, Nat.Coprime s m →
      (gs m (s:ℤ)).im = (jacobiSym (β*(s:ℤ)) m₀ : ℤ) * Q s := by
    intro s hs
    rw [hfac s hs]
    rw [show gs (2^a) (α*(s:ℤ)) * ((jacobiSym (β*(s:ℤ)) m₀:ℤ):ℂ) * gs m₀ 1
        = ((jacobiSym (β*(s:ℤ)) m₀:ℤ):ℂ) * (gs (2^a) (α*(s:ℤ)) * gs m₀ 1) by ring,
        Complex.mul_im, Complex.intCast_re, Complex.intCast_im]
    simp [hQdef]
  -- Jacobi multiplicativity, and value at s=1
  have hJmul : ∀ s : ℕ, jacobiSym (β*(s:ℤ)) m₀ = jacobiSym β m₀ * jacobiSym (s:ℤ) m₀ := by
    intro s; rw [jacobiSym.mul_left]
  have hαs_odd : ∀ s : ℕ, Nat.Coprime s m → Odd (α * (s:ℤ)) :=
    fun s hs => haodd.mul (by exact_mod_cast hsodd s hs)
  -- The common reduction of `hid` to `Q s = Q 1 * χ2val s`
  have key : ∀ (χ : DirichletCharacter ℂ m) (χ2val : ℕ → ℝ),
      χ ^ 2 = 1 →
      (∀ s : ℕ, Nat.Coprime s m → (χ (s : ZMod m)).re = (jacobiSym (s:ℤ) m₀ : ℤ) * χ2val s) →
      (∀ s : ℕ, Nat.Coprime s m → Q s = Q 1 * χ2val s) →
      0 ≤ Pchar m := by
    intro χ χ2val hχsq hχval hQmul
    refine P_nonneg_of_char m hm2 χ hχsq (gs_one_im_nonneg m (by omega)) ?_
    intro s hs
    have hco1 : Nat.Coprime 1 m := Nat.coprime_one_left m
    rw [hQ s hs, hJmul s, hχval s hs, hQmul s hs]
    have h1 : (gs m 1).im = (jacobiSym β m₀ : ℤ) * Q 1 := by
      have h := hQ 1 hco1
      simpa using h
    rw [h1]
    push_cast
    ring
  rcases Nat.even_or_odd a with ⟨j, hjaE⟩ | ⟨j, hjaO⟩
  · -- a even, a = j + j
    have ha' : a = 2 * j := by omega
    have hj1 : 1 ≤ j := by omega
    have h4 : (4:ℕ) ∣ m := by
      rw [hmeq, ha']
      exact Dvd.dvd.mul_right
        (by rw [show (4:ℕ) = 2^2 from rfl]; exact pow_dvd_pow 2 (by omega)) m₀
    have hm0m4 : m₀ % 4 = 1 ∨ m₀ % 4 = 3 := by rcases hm0odd with ⟨k, hk⟩; omega
    rcases hm0m4 with hm0mod | hm0mod
    · -- Case 1: even a, m₀ % 4 = 1
      refine key (DirichletCharacter.changeLevel hm0dvd (jacobiChar m₀)
          * DirichletCharacter.changeLevel h4 (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)))
          (fun s => ((ZMod.χ₄ ((s:ℕ):ZMod 4):ℤ):ℝ)) ?_ ?_ ?_
      · rw [mul_pow, changeLevel_sq hm0dvd _ (jacobiChar_sq m₀),
            changeLevel_sq h4 _ ((ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one), mul_one]
      · intro s hs
        dsimp only
        rw [MulChar.mul_apply, changeLevel_jacobi_apply m m₀ hm0dvd s hs,
            changeLevel_two_apply m 4 h4 ZMod.χ₄ s hs]
        simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
        push_cast; ring
      · have hQval : ∀ s:ℕ, Nat.Coprime s m →
            Q s = (2^j * Real.sqrt m₀) * ((ZMod.χ₄ ((α*(s:ℤ)):ZMod 4):ℤ):ℝ) := by
          intro s hs
          have hx : Odd (α*(s:ℤ)) := hαs_odd s hs
          simp only [hQdef]
          rw [hgm1, if_pos hm0mod, show (2:ℕ)^a = 2^(2*j) by rw [ha'], gs_two_even j hj1 _ hx,
              show (2:ℂ)^j*(1+I^(α*(s:ℤ)))*((Real.sqrt m₀:ℝ):ℂ)
                 = (((2:ℝ)^j*Real.sqrt m₀:ℝ):ℂ)*(1+I^(α*(s:ℤ))) by push_cast; ring,
              Complex.im_ofReal_mul, Complex.add_im, Complex.one_im, zero_add, I_zpow_im_chi4 _ hx]
          push_cast; ring
        have hmul4 : ∀ s:ℕ, ((ZMod.χ₄ ((α*(s:ℤ)):ZMod 4):ℤ):ℝ)
            = ((ZMod.χ₄ (α:ZMod 4):ℤ):ℝ) * ((ZMod.χ₄ ((s:ℕ):ZMod 4):ℤ):ℝ) := by
          intro s
          rw [show ((α*(s:ℤ)):ZMod 4) = (α:ZMod 4)*((s:ℕ):ZMod 4) by push_cast; ring, map_mul]
          push_cast; ring
        intro s hs
        dsimp only
        rw [hQval s hs, hQval 1 (Nat.coprime_one_left m), hmul4 s, hmul4 1]
        have h1 : ((ZMod.χ₄ (((1:ℕ)):ZMod 4):ℤ):ℝ) = 1 := by norm_num [map_one]
        rw [h1]; ring
    · -- Case 2: even a, m₀ % 4 = 3
      refine key (DirichletCharacter.changeLevel hm0dvd (jacobiChar m₀))
          (fun _ => (1:ℝ)) ?_ ?_ ?_
      · exact changeLevel_sq hm0dvd _ (jacobiChar_sq m₀)
      · intro s hs
        dsimp only
        rw [changeLevel_jacobi_apply m m₀ hm0dvd s hs, Complex.intCast_re]
        ring
      · have hQval : ∀ s:ℕ, Nat.Coprime s m → Q s = 2^j * Real.sqrt m₀ := by
          intro s hs
          have hx : Odd (α*(s:ℤ)) := hαs_odd s hs
          simp only [hQdef]
          rw [hgm1, if_neg (by omega : ¬ m₀%4=1), show (2:ℕ)^a = 2^(2*j) by rw [ha'],
              gs_two_even j hj1 _ hx,
              show (2:ℂ)^j*(1+I^(α*(s:ℤ)))*(I*((Real.sqrt m₀:ℝ):ℂ))
                 = (((2:ℝ)^j*Real.sqrt m₀:ℝ):ℂ)*((1+I^(α*(s:ℤ)))*I) by push_cast; ring,
              Complex.im_ofReal_mul, Complex.mul_I_im, Complex.add_re, Complex.one_re,
              I_zpow_odd_re _ hx]
          push_cast; ring
        intro s hs
        dsimp only
        rw [hQval s hs, hQval 1 (Nat.coprime_one_left m)]
        ring
  · -- a odd, a = 2*j+1
    have hj1 : 1 ≤ j := by omega
    have h8 : (8:ℕ) ∣ m := by
      rw [hmeq, hjaO]
      exact Dvd.dvd.mul_right
        (by rw [show (8:ℕ) = 2^3 from rfl]; exact pow_dvd_pow 2 (by omega)) m₀
    have hm0m4 : m₀ % 4 = 1 ∨ m₀ % 4 = 3 := by rcases hm0odd with ⟨k, hk⟩; omega
    rcases hm0m4 with hm0mod | hm0mod
    · -- Case 3: odd a, m₀ % 4 = 1
      refine key (DirichletCharacter.changeLevel hm0dvd (jacobiChar m₀)
          * DirichletCharacter.changeLevel h8 (ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)))
          (fun s => ((ZMod.χ₈' ((s:ℕ):ZMod 8):ℤ):ℝ)) ?_ ?_ ?_
      · rw [mul_pow, changeLevel_sq hm0dvd _ (jacobiChar_sq m₀),
            changeLevel_sq h8 _ ((ZMod.isQuadratic_χ₈'.comp (Int.castRingHom ℂ)).sq_eq_one), mul_one]
      · intro s hs
        dsimp only
        rw [MulChar.mul_apply, changeLevel_jacobi_apply m m₀ hm0dvd s hs,
            changeLevel_two_apply m 8 h8 ZMod.χ₈' s hs]
        simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
        push_cast; ring
      · have hQval : ∀ s:ℕ, Nat.Coprime s m →
            Q s = (2^(j+1) * Real.sqrt m₀ * (Real.sqrt 2/2))
              * ((ZMod.χ₈' ((α*(s:ℤ)):ZMod 8):ℤ):ℝ) := by
          intro s hs
          have hx : Odd (α*(s:ℤ)) := hαs_odd s hs
          simp only [hQdef]
          rw [hgm1, if_pos hm0mod, show (2:ℕ)^a = 2^(2*j+1) by rw [hjaO], gs_two_odd j hj1 _ hx,
              show (2:ℂ)^(j+1)*zeta 8^(α*(s:ℤ))*((Real.sqrt m₀:ℝ):ℂ)
                 = (((2:ℝ)^(j+1)*Real.sqrt m₀:ℝ):ℂ)*(zeta 8^(α*(s:ℤ))) by push_cast; ring,
              Complex.im_ofReal_mul, zeta8_im_chi8' _ hx]
          push_cast; ring
        have hmul8 : ∀ s:ℕ, ((ZMod.χ₈' ((α*(s:ℤ)):ZMod 8):ℤ):ℝ)
            = ((ZMod.χ₈' (α:ZMod 8):ℤ):ℝ) * ((ZMod.χ₈' ((s:ℕ):ZMod 8):ℤ):ℝ) := by
          intro s
          rw [show ((α*(s:ℤ)):ZMod 8) = (α:ZMod 8)*((s:ℕ):ZMod 8) by push_cast; ring, map_mul]
          push_cast; ring
        intro s hs
        dsimp only
        rw [hQval s hs, hQval 1 (Nat.coprime_one_left m), hmul8 s, hmul8 1]
        have h1 : ((ZMod.χ₈' (((1:ℕ)):ZMod 8):ℤ):ℝ) = 1 := by norm_num [map_one]
        rw [h1]; ring
    · -- Case 4: odd a, m₀ % 4 = 3
      refine key (DirichletCharacter.changeLevel hm0dvd (jacobiChar m₀)
          * DirichletCharacter.changeLevel h8 (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)))
          (fun s => ((ZMod.χ₈ ((s:ℕ):ZMod 8):ℤ):ℝ)) ?_ ?_ ?_
      · rw [mul_pow, changeLevel_sq hm0dvd _ (jacobiChar_sq m₀),
            changeLevel_sq h8 _ ((ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)).sq_eq_one), mul_one]
      · intro s hs
        dsimp only
        rw [MulChar.mul_apply, changeLevel_jacobi_apply m m₀ hm0dvd s hs,
            changeLevel_two_apply m 8 h8 ZMod.χ₈ s hs]
        simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
        push_cast; ring
      · have hQval : ∀ s:ℕ, Nat.Coprime s m →
            Q s = (2^(j+1) * Real.sqrt m₀ * (Real.sqrt 2/2))
              * ((ZMod.χ₈ ((α*(s:ℤ)):ZMod 8):ℤ):ℝ) := by
          intro s hs
          have hx : Odd (α*(s:ℤ)) := hαs_odd s hs
          simp only [hQdef]
          rw [hgm1, if_neg (by omega : ¬ m₀%4=1), show (2:ℕ)^a = 2^(2*j+1) by rw [hjaO],
              gs_two_odd j hj1 _ hx,
              show (2:ℂ)^(j+1)*zeta 8^(α*(s:ℤ))*(I*((Real.sqrt m₀:ℝ):ℂ))
                 = (((2:ℝ)^(j+1)*Real.sqrt m₀:ℝ):ℂ)*(zeta 8^(α*(s:ℤ))*I) by push_cast; ring,
              Complex.im_ofReal_mul, Complex.mul_I_im, zeta8_re_chi8 _ hx]
          push_cast; ring
        have hmul8 : ∀ s:ℕ, ((ZMod.χ₈ ((α*(s:ℤ)):ZMod 8):ℤ):ℝ)
            = ((ZMod.χ₈ (α:ZMod 8):ℤ):ℝ) * ((ZMod.χ₈ ((s:ℕ):ZMod 8):ℤ):ℝ) := by
          intro s
          rw [show ((α*(s:ℤ)):ZMod 8) = (α:ZMod 8)*((s:ℕ):ZMod 8) by push_cast; ring, map_mul]
          push_cast; ring
        intro s hs
        dsimp only
        rw [hQval s hs, hQval 1 (Nat.coprime_one_left m), hmul8 s, hmul8 1]
        have h1 : ((ZMod.χ₈ (((1:ℕ)):ZMod 8):ℤ):ℝ) = 1 := by norm_num [map_one]
        rw [h1]; ring

lemma Pchar_nonneg (m : ℕ) : 0 ≤ Pchar m := by
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · interval_cases m <;> simp [Pchar]
  · rcases Nat.even_or_odd m with he | ho
    · have hcase : m % 4 = 0 ∨ m % 4 = 2 := by
        obtain ⟨c, hc⟩ := he; omega
      rcases hcase with h0 | h2
      · exact Pchar_nonneg_zero_mod4 m h0 hge
      · exact Pchar_nonneg_two_mod4 m h2
    · exact Pchar_nonneg_odd m ho hge

noncomputable def Dval (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico 1 n, (gs n (t:ℤ)).im * Real.cot (Real.pi * (t:ℝ) / (n:ℝ))

lemma Dval_fiber (n m : ℕ) (hn : 0 < n) (hmd : m ∣ n) :
    ∑ t ∈ (Finset.Ico 1 n).filter (fun t => n / Nat.gcd t n = m),
        (gs n (t:ℤ)).im * Real.cot (Real.pi * (t:ℝ) / (n:ℝ))
      = ((n/m : ℕ) : ℝ) * Pchar m := by
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hmd hn
  set d := n / m with hddef
  have hd0 : 0 < d := Nat.div_pos (Nat.le_of_dvd hn hmd) hm0
  have hdm : d * m = n := Nat.div_mul_cancel hmd
  rw [Pchar, Finset.mul_sum]
  apply Finset.sum_nbij' (fun t => t / d) (fun s => d * s)
  · -- i maps into target
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht ⊢
    obtain ⟨⟨ht1, ht2⟩, hfib⟩ := ht
    have hgcdn : Nat.gcd t n ∣ n := Nat.gcd_dvd_right t n
    have hgcd : Nat.gcd t n = d := by
      have : Nat.gcd t n * m = n := by rw [← hfib]; exact Nat.mul_div_cancel' hgcdn
      have hdm' : d * m = n := hdm
      have := this.trans hdm'.symm
      exact Nat.eq_of_mul_eq_mul_right hm0 this
    have hdt : d ∣ t := hgcd ▸ Nat.gcd_dvd_left t n
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.one_le_div_iff hd0 |>.2 (Nat.le_of_dvd ht1 hdt)
    · rw [Nat.div_lt_iff_lt_mul hd0]; rw [mul_comm]; rw [hdm]; exact ht2
    · have hco := Nat.coprime_div_gcd_div_gcd (m := t) (n := n) (by rw [hgcd]; exact hd0)
      rw [hgcd] at hco
      have hmd2 : n / d = m := by rw [hddef] at *; rw [Nat.div_div_self hmd hn.ne']
      rwa [hmd2] at hco
  · -- j maps into source
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_Ico] at hs ⊢
    obtain ⟨⟨hs1, hs2⟩, hco⟩ := hs
    have hgcds : Nat.gcd (d * s) n = d := by
      rw [← hdm, Nat.gcd_mul_left]
      rw [Nat.Coprime] at hco; rw [hco, mul_one]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.one_le_iff_ne_zero.2 (by positivity)
    · rw [← hdm]; exact (Nat.mul_lt_mul_left hd0).mpr hs2
    · rw [hgcds]; rw [hddef] at *; rw [Nat.div_div_self hmd hn.ne']
  · -- left inverse
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht
    obtain ⟨⟨ht1, ht2⟩, hfib⟩ := ht
    have hgcdn : Nat.gcd t n ∣ n := Nat.gcd_dvd_right t n
    have hgcd : Nat.gcd t n = d := by
      have : Nat.gcd t n * m = n := by rw [← hfib]; exact Nat.mul_div_cancel' hgcdn
      exact Nat.eq_of_mul_eq_mul_right hm0 (this.trans hdm.symm)
    have hdt : d ∣ t := hgcd ▸ Nat.gcd_dvd_left t n
    exact Nat.mul_div_cancel' hdt
  · -- right inverse
    intro s _
    exact Nat.mul_div_cancel_left s hd0
  · -- value
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht
    obtain ⟨⟨ht1, ht2⟩, hfib⟩ := ht
    have hgcdn : Nat.gcd t n ∣ n := Nat.gcd_dvd_right t n
    have hgcd : Nat.gcd t n = d := by
      have : Nat.gcd t n * m = n := by rw [← hfib]; exact Nat.mul_div_cancel' hgcdn
      exact Nat.eq_of_mul_eq_mul_right hm0 (this.trans hdm.symm)
    have hdt : d ∣ t := hgcd ▸ Nat.gcd_dvd_left t n
    set s := t / d with hsdef
    have hts : t = d * s := (Nat.mul_div_cancel' hdt).symm
    -- gs n t = d * gs m s
    have hgseq : gs n (t:ℤ) = (d:ℂ) * gs m (s:ℤ) := by
      have hcast : (t:ℤ) = (d:ℤ) * (s:ℤ) := by rw [hts]; push_cast; ring
      rw [hcast, ← hdm]
      exact gs_scale d m hd0 hm0 (s:ℤ)
    have hcot : Real.cot (Real.pi * (t:ℝ) / (n:ℝ)) = Real.cot (Real.pi * (s:ℝ) / (m:ℝ)) := by
      congr 1
      rw [hts, ← hdm]
      push_cast
      field_simp
    rw [hgseq, hcot, Complex.mul_im, Complex.natCast_re, Complex.natCast_im]
    ring

lemma Dval_nonneg (n : ℕ) (hn : 0 < n) (hP : ∀ m, 0 ≤ Pchar m) : 0 ≤ Dval n := by
  have hmaps : ∀ t ∈ Finset.Ico 1 n, n / Nat.gcd t n ∈ n.divisors := by
    intro t ht
    rw [Nat.mem_divisors]
    refine ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right t n), hn.ne'⟩
  have hkey : Dval n = ∑ m ∈ n.divisors,
      ∑ t ∈ (Finset.Ico 1 n).filter (fun t => n / Nat.gcd t n = m),
        (gs n (t:ℤ)).im * Real.cot (Real.pi * (t:ℝ) / (n:ℝ)) := by
    rw [Dval, ← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [hkey]
  apply Finset.sum_nonneg
  intro m hm
  rw [Nat.mem_divisors] at hm
  rw [Dval_fiber n m hn hm.1]
  exact mul_nonneg (by positivity) (hP m)

end FinalSection

section Arithmetic
open Finset

def A048153' (n : ℕ) : ℕ := Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

def Sneg' (n : ℕ) : ℕ := Finset.sum (Finset.range n) (fun k => (n - k ^ 2 % n) % n)

def Wcount' (n : ℕ) : ℕ :=
  (Finset.filter (fun k => k ^ 2 % n ≠ 0) (Finset.range n)).card

theorem S_add_Sneg' (n : ℕ) (hn : 1 ≤ n) :
    A048153' n + Sneg' n = n * Wcount' n := by
  unfold A048153' Sneg' Wcount'
  rw [← Finset.sum_add_distrib, Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hlt : k ^ 2 % n < n := Nat.mod_lt _ hn
  by_cases h : k ^ 2 % n = 0
  · simp [h, Nat.mod_self]
  · have h2 : n - k ^ 2 % n < n := by omega
    rw [Nat.mod_eq_of_lt h2, if_pos h]
    omega

theorem core (n : ℕ) (hn : 1 ≤ n) : A048153' n ≤ Sneg' n := by
  have hDval : 0 ≤ Dval n := Dval_nonneg n hn Pchar_nonneg
  have hD := D_real n hn
  -- D_real : (n)*Wcount' - 2*A_real = Dval n
  have hDeq : Dval n = (n:ℝ) * ((Wcount' n : ℕ) : ℝ) - 2 * ((A048153' n : ℕ) : ℝ) := by
    rw [Dval, ← hD]
    simp only [Wcount', A048153', Nat.cast_sum]
  rw [hDeq] at hDval
  -- 2 A_real ≤ n Wcount_real
  have h2A : 2 * ((A048153' n : ℕ):ℝ) ≤ (n:ℝ) * ((Wcount' n:ℕ):ℝ) := by linarith
  have h2An : 2 * A048153' n ≤ n * Wcount' n := by
    have : ((2 * A048153' n : ℕ):ℝ) ≤ ((n * Wcount' n : ℕ):ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hid := S_add_Sneg' n hn
  omega

theorem oeis_48153_conjecture_0' (n : ℕ) (h : 1 ≤ n) : A048153' n ≤ (n ^ 2 - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have hmaster : 2 * A048153' n ≤ n * (n - 1) := by
    have hid := S_add_Sneg' n h
    have hcore := core n h
    have hw : Wcount' n ≤ n - 1 := by
      unfold Wcount'
      have hsub : (Finset.filter (fun k => k ^ 2 % n ≠ 0) (Finset.range n)) ⊆ (Finset.range n).erase 0 := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_range] at hk
        rw [Finset.mem_erase, Finset.mem_range]
        refine ⟨?_, hk.1⟩
        intro h0; apply hk.2; rw [h0]; simp
      calc (Finset.filter (fun k => k ^ 2 % n ≠ 0) (Finset.range n)).card
          ≤ ((Finset.range n).erase 0).card := Finset.card_le_card hsub
        _ = n - 1 := by
            rw [Finset.card_erase_of_mem (by rw [Finset.mem_range]; omega), Finset.card_range]
    have h1 : 2 * A048153' n ≤ n * Wcount' n := by omega
    calc 2 * A048153' n ≤ n * Wcount' n := h1
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n hw
  have h1 : n * (n - 1) ≤ n ^ 2 - 1 := by
    cases n with
    | zero => simp
    | succ k => simp only [Nat.succ_sub_one]; ring_nf; omega
  calc A048153' n * 2 = 2 * A048153' n := by ring
    _ ≤ n * (n - 1) := hmaster
    _ ≤ n ^ 2 - 1 := h1

end Arithmetic

open Finset in
/--
A048153: $a(n) = \sum_{k=1}^n (k^2 \bmod n)$.
This sequence is defined in Lean as the sum of $k^2 \bmod n$ for $k \in \{0, 1, \dots, n-1\}$.
-/
def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

/--
Conjecture: a(n) <= (n^2-1)/2. - _Aspen A.M. Meissner_, Mar 06 2025
We require $n \ge 1$ for the difference $n^2 - 1$ to be a natural number.
The division `/ 2` is natural number (integer) division.
-/
theorem oeis_48153_conjecture_0 (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 :=
  oeis_48153_conjecture_0' n h
