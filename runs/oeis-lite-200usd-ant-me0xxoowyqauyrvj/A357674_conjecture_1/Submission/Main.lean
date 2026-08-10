import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

-- ===== Newton identities =====

variable {R : Type*} [CommRing R]

/-- Elementary symmetric "sum of products over k-subsets". -/
def Esym (a : ℕ → R) (k : ℕ) (s : Finset ℕ) : R := ∑ t ∈ powersetCard k s, ∏ i ∈ t, a i

/-- Power sum. -/
def Psym (a : ℕ → R) (k : ℕ) (s : Finset ℕ) : R := ∑ i ∈ s, (a i) ^ k

theorem Esym_zero (a : ℕ → R) (s : Finset ℕ) : Esym a 0 s = 1 := by
  rw [Esym, powersetCard_zero]; simp

theorem Esym_one (a : ℕ → R) (s : Finset ℕ) : Esym a 1 s = ∑ i ∈ s, a i := by
  rw [Esym, powersetCard_one, Finset.sum_map]
  simp

theorem Esym_succ_insert (a : ℕ → R) (k : ℕ) {b : ℕ} {s : Finset ℕ} (hb : b ∉ s) :
    Esym a (k + 1) (insert b s) = Esym a (k + 1) s + a b * Esym a k s := by
  rw [Esym, Esym, Esym, powersetCard_succ_insert hb, Finset.sum_union, Finset.mul_sum]
  · congr 1
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_powersetCard] at ht
      rw [Finset.prod_insert (fun hbt => hb (ht.1 hbt))]
    · intro t ht t' ht' himg
      rw [Finset.mem_coe, Finset.mem_powersetCard] at ht ht'
      have hbt : b ∉ t := fun hbt => hb (ht.1 hbt)
      have hbt' : b ∉ t' := fun hbt => hb (ht'.1 hbt)
      have := congrArg (fun u => Finset.erase u b) himg
      simpa [Finset.erase_insert hbt, Finset.erase_insert hbt'] using this
  · apply Finset.disjoint_left.mpr
    intro t ht htimg
    rw [Finset.mem_powersetCard] at ht
    rw [Finset.mem_image] at htimg
    obtain ⟨t', _, rfl⟩ := htimg
    exact hb (ht.1 (Finset.mem_insert_self b t'))

theorem newton2 (a : ℕ → R) (s : Finset ℕ) :
    2 * Esym a 2 s = (Psym a 1 s) ^ 2 - Psym a 2 s := by
  induction s using Finset.induction with
  | empty => simp [Esym, Psym, powersetCard]
  | @insert b s hb ih =>
    have hE2 := Esym_succ_insert a 1 hb
    rw [Esym_one] at hE2
    have hP1 : Psym a 1 (insert b s) = a b + Psym a 1 s := by
      rw [Psym, Psym, Finset.sum_insert hb]; simp
    have hP2 : Psym a 2 (insert b s) = (a b)^2 + Psym a 2 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hP1' : Psym a 1 s = ∑ i ∈ s, a i := by rw [Psym]; simp
    rw [hE2, hP1, hP2, ← hP1']
    rw [mul_add, ih]
    ring

theorem newton3 (a : ℕ → R) (s : Finset ℕ) :
    3 * Esym a 3 s = Esym a 2 s * Psym a 1 s - Psym a 1 s * Psym a 2 s + Psym a 3 s := by
  induction s using Finset.induction with
  | empty => simp [Esym, Psym, powersetCard]
  | @insert b s hb ih =>
    have hE3 := Esym_succ_insert a 2 hb
    have hE2 := Esym_succ_insert a 1 hb
    rw [Esym_one] at hE2
    have hP1' : (∑ i ∈ s, a i) = Psym a 1 s := by rw [Psym]; simp
    rw [hP1'] at hE2
    have hP1 : Psym a 1 (insert b s) = a b + Psym a 1 s := by
      rw [Psym, Psym, Finset.sum_insert hb]; simp
    have hP2 : Psym a 2 (insert b s) = (a b)^2 + Psym a 2 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hP3 : Psym a 3 (insert b s) = (a b)^3 + Psym a 3 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hN2 := newton2 a s
    rw [hE3, hE2, hP1, hP2, hP3]
    linear_combination ih + (a b) * hN2

theorem newton4 (a : ℕ → R) (s : Finset ℕ) :
    4 * Esym a 4 s
      = Esym a 3 s * Psym a 1 s - Esym a 2 s * Psym a 2 s
        + Psym a 1 s * Psym a 3 s - Psym a 4 s := by
  induction s using Finset.induction with
  | empty => simp [Esym, Psym, powersetCard]
  | @insert b s hb ih =>
    have hE4 := Esym_succ_insert a 3 hb
    have hE3 := Esym_succ_insert a 2 hb
    have hE2 := Esym_succ_insert a 1 hb
    rw [Esym_one] at hE2
    have hP1' : (∑ i ∈ s, a i) = Psym a 1 s := by rw [Psym]; simp
    rw [hP1'] at hE2
    have hP1 : Psym a 1 (insert b s) = a b + Psym a 1 s := by
      rw [Psym, Psym, Finset.sum_insert hb]; simp
    have hP2 : Psym a 2 (insert b s) = (a b)^2 + Psym a 2 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hP3 : Psym a 3 (insert b s) = (a b)^3 + Psym a 3 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hP4 : Psym a 4 (insert b s) = (a b)^4 + Psym a 4 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hN3 := newton3 a s
    rw [hE4, hE3, hE2, hP1, hP2, hP3, hP4]
    linear_combination ih + (a b) * hN3

-- ===== Harmonic infra =====

theorem sum_pow_Ico_zero (p k : ℕ) [hpp : Fact p.Prime] (hk1 : 1 ≤ k) (hk2 : k < p - 1) :
    ∑ j ∈ Ico 1 p, ((j : ZMod p)) ^ k = 0 := by
  have hp0 : 0 < p := hpp.out.pos
  have hcard : k < Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; exact hk2
  have h1 : ∑ x : ZMod p, x ^ k = 0 := FiniteField.sum_pow_lt_card_sub_one (ZMod p) k hcard
  have hbij : ∑ x : ZMod p, x ^ k = ∑ j ∈ range p, ((j : ZMod p)) ^ k := by
    apply Finset.sum_nbij' (fun x => ZMod.val x) (fun n => (n : ZMod p))
    · intro x _; rw [mem_range]; exact ZMod.val_lt x
    · intro n _; exact mem_univ _
    · intro x _; exact ZMod.natCast_rightInverse x
    · intro n hn; rw [mem_range] at hn; exact ZMod.val_cast_of_lt hn
    · intro x _; rw [ZMod.natCast_rightInverse x]
  rw [hbij] at h1
  have hsplit : range p = insert 0 (Ico 1 p) := by
    ext x; simp only [mem_range, mem_insert, mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp)] at h1
  simp only [Nat.cast_zero, zero_pow (by omega : k ≠ 0)] at h1
  rw [zero_add] at h1
  exact h1

variable {p : ℕ}

-- integer divisibility transfers to ZMod (p^5) divisibility
theorem dvd_cast_of_dvd (k N : ℕ) (h : p^k ∣ N) :
    (p : ZMod (p^5))^k ∣ (N : ZMod (p^5)) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨(m : ZMod (p^5)), ?_⟩
  rw [hm]; push_cast; ring

-- The per-term reflection expansion of an inverse
theorem inv_pmi_expand [Fact p.Prime] (hp5 : 5 ≤ p) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i < p) :
    ((p - i : ℕ) : ZMod (p^5))⁻¹
      = -(((i:ZMod (p^5)))⁻¹ + (p:ZMod (p^5)) * ((i:ZMod (p^5)))⁻¹^2
          + (p:ZMod (p^5))^2 * ((i:ZMod (p^5)))⁻¹^3 + (p:ZMod (p^5))^3 * ((i:ZMod (p^5)))⁻¹^4
          + (p:ZMod (p^5))^4 * ((i:ZMod (p^5)))⁻¹^5) := by
  haveI : NeZero (p^5) := ⟨by positivity⟩
  set P := (p : ZMod (p^5))
  -- i is a unit
  have hiu : IsUnit ((i:ℕ):ZMod (p^5)) := by
    have hpi : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hcop : Nat.Coprime i p := Nat.coprime_comm.mp (((Fact.out (p := p.Prime)).coprime_iff_not_dvd).mpr hpi)
    exact (ZMod.isUnit_iff_coprime i (p^5)).mpr (hcop.pow_right 5)
  have hinv : ((i:ZMod (p^5))) * ((i:ZMod (p^5)))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hiu
  -- (p - i) is a unit
  have hpmiu : IsUnit (((p - i:ℕ)):ZMod (p^5)) := by
    have hpi : ¬ p ∣ (p - i) := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hcop : Nat.Coprime (p-i) p := Nat.coprime_comm.mp (((Fact.out (p := p.Prime)).coprime_iff_not_dvd).mpr hpi)
    exact (ZMod.isUnit_iff_coprime (p-i) (p^5)).mpr (hcop.pow_right 5)
  have hinvpmi : (((p-i:ℕ)):ZMod (p^5)) * (((p-i:ℕ)):ZMod (p^5))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hpmiu
  have hcast : (((p - i:ℕ)):ZMod (p^5)) = P - (i:ZMod (p^5)) := by
    rw [Nat.cast_sub (by omega)]
  have hP5 : P^5 = 0 := by
    have : P^5 = ((p^5:ℕ):ZMod (p^5)) := by push_cast; ring
    rw [this]; exact ZMod.natCast_self _
  -- show (p-i) * RHS = 1, then conclude
  set I := ((i:ZMod (p^5)))⁻¹ with hI
  have key : (((p-i:ℕ)):ZMod (p^5)) * (-(I + P*I^2 + P^2*I^3 + P^3*I^4 + P^4*I^5)) = 1 := by
    rw [hcast]
    have step1 : (P - (i:ZMod (p^5))) * (-I) = 1 - P*I := by
      have h : (P - (i:ZMod (p^5)))*(-I) = -(P*I) + (i:ZMod (p^5))*I := by ring
      rw [h, hinv]; ring
    calc (P - (i:ZMod (p^5))) * (-(I + P*I^2 + P^2*I^3 + P^3*I^4 + P^4*I^5))
        = ((P - (i:ZMod (p^5)))*(-I))*(1 + P*I + P^2*I^2 + P^3*I^3 + P^4*I^4) := by ring
      _ = (1 - P*I)*(1 + P*I + P^2*I^2 + P^3*I^3 + P^4*I^4) := by rw [step1]
      _ = 1 - (P*I)^5 := by ring
      _ = 1 := by rw [mul_pow, hP5]; ring
  exact hpmiu.mul_left_cancel (by rw [hinvpmi, key])

-- Harmonic sums in ZMod (p^5)
noncomputable def Hs (p j : ℕ) : ZMod (p^5) := ∑ i ∈ Ico 1 p, ((i:ZMod (p^5)))⁻¹ ^ j

-- reindexing i ↦ p - i on Ico 1 p
theorem sum_reflect [Fact p.Prime] (f : ℕ → ZMod (p^5)) :
    ∑ i ∈ Ico 1 p, f (p - i) = ∑ i ∈ Ico 1 p, f i := by
  apply Finset.sum_nbij' (fun i => p - i) (fun i => p - i)
  · intro i hi; rw [mem_Ico] at hi ⊢; omega
  · intro i hi; rw [mem_Ico] at hi ⊢; omega
  · intro i hi; rw [mem_Ico] at hi; omega
  · intro i hi; rw [mem_Ico] at hi; omega
  · intro i hi; rfl

-- P1 : 2 * H1 = -(p H2 + p^2 H3 + p^3 H4 + p^4 H5)
theorem pairing_P1 [Fact p.Prime] (hp5 : 5 ≤ p) :
    2 * Hs p 1 = -((p:ZMod (p^5)) * Hs p 2 + (p:ZMod (p^5))^2 * Hs p 3
      + (p:ZMod (p^5))^3 * Hs p 4 + (p:ZMod (p^5))^4 * Hs p 5) := by
  have hrefl : ∑ i ∈ Ico 1 p, ((p - i : ℕ):ZMod (p^5))⁻¹ = Hs p 1 := by
    have := sum_reflect (p := p) (fun i => ((i:ℕ):ZMod (p^5))⁻¹)
    simpa [Hs, pow_one] using this
  have hexp : ∀ i ∈ Ico 1 p, ((i:ZMod (p^5)))⁻¹ + ((p - i : ℕ):ZMod (p^5))⁻¹
      = -((p:ZMod (p^5)) * ((i:ZMod (p^5)))⁻¹^2 + (p:ZMod (p^5))^2 * ((i:ZMod (p^5)))⁻¹^3
          + (p:ZMod (p^5))^3 * ((i:ZMod (p^5)))⁻¹^4 + (p:ZMod (p^5))^4 * ((i:ZMod (p^5)))⁻¹^5) := by
    intro i hi
    rw [mem_Ico] at hi
    rw [inv_pmi_expand hp5 i hi.1 hi.2]; ring
  have hsum : ∑ i ∈ Ico 1 p, (((i:ZMod (p^5)))⁻¹ + ((p - i : ℕ):ZMod (p^5))⁻¹)
      = ∑ i ∈ Ico 1 p, (-((p:ZMod (p^5)) * ((i:ZMod (p^5)))⁻¹^2 + (p:ZMod (p^5))^2 * ((i:ZMod (p^5)))⁻¹^3
          + (p:ZMod (p^5))^3 * ((i:ZMod (p^5)))⁻¹^4 + (p:ZMod (p^5))^4 * ((i:ZMod (p^5)))⁻¹^5)) :=
    Finset.sum_congr rfl hexp
  rw [Finset.sum_add_distrib, hrefl] at hsum
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hH1 : (∑ x ∈ Ico 1 p, ((x:ZMod (p^5)))⁻¹) = Hs p 1 := by simp [Hs, pow_one]
  rw [hH1, show Hs p 1 + Hs p 1 = 2 * Hs p 1 from by ring] at hsum
  exact hsum

-- helper: cast to ZMod p detects divisibility by p
theorem dvd_p_of_val_cast_zero (hp : 0 < p) (x : ZMod (p^5))
    (h : ((x.val : ZMod p)) = 0) : (p : ZMod (p^5)) ∣ x := by
  haveI : NeZero (p^5) := ⟨by positivity⟩
  rw [ZMod.natCast_eq_zero_iff x.val p] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨(m : ZMod (p^5)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [hm]; push_cast; ring

-- inverse power sum vanishes mod p
theorem sum_inv_pow_zero [Fact p.Prime] (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ p - 2) :
    ∑ i ∈ Ico 1 p, ((i:ZMod p))⁻¹ ^ j = 0 := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hterm : ∀ i ∈ Ico 1 p, ((i:ZMod p))⁻¹ ^ j = ((i:ZMod p)) ^ (p - 1 - j) := by
    intro i hi
    rw [mem_Ico] at hi
    have hi0 : (i:ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd; have := Nat.le_of_dvd (by omega) hd; omega
    have hfermat : (i:ZMod p) ^ (p-1) = 1 := ZMod.pow_card_sub_one_eq_one hi0
    have hu : IsUnit ((i:ZMod p) ^ j) := (hi0.isUnit).pow j
    have hmul : (i:ZMod p) * (i:ZMod p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hi0.isUnit
    apply hu.mul_left_cancel
    rw [← mul_pow, hmul, one_pow, ← pow_add, show j + (p-1-j) = p-1 by omega, hfermat]
  rw [show (∑ i ∈ Ico 1 p, ((i:ZMod p))⁻¹ ^ j) = ∑ i ∈ Ico 1 p, ((i:ZMod p)) ^ (p - 1 - j) from
    Finset.sum_congr rfl hterm]
  exact sum_pow_Ico_zero p (p-1-j) (by omega) (by omega)

-- The reduction ring hom ZMod (p^5) → ZMod p
noncomputable def fcast (p : ℕ) : ZMod (p^5) →+* ZMod p :=
  ZMod.castHom (⟨p^4, by ring⟩ : p ∣ p^5) (ZMod p)

theorem fcast_natCast (p n : ℕ) : fcast p (n : ZMod (p^5)) = (n : ZMod p) := by
  rw [fcast]; exact map_natCast _ n

theorem fcast_inv [Fact p.Prime] (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i < p) :
    fcast p ((i : ZMod (p^5))⁻¹) = ((i : ZMod p))⁻¹ := by
  have hpi : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hiu : IsUnit ((i : ZMod (p^5))) := by
    have hcop : Nat.Coprime i p := Nat.coprime_comm.mp
      (((Fact.out (p := p.Prime)).coprime_iff_not_dvd).mpr hpi)
    exact (ZMod.isUnit_iff_coprime i (p^5)).mpr (hcop.pow_right 5)
  have h1 : (i : ZMod (p^5)) * (i : ZMod (p^5))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hiu
  have h2 := congrArg (fcast p) h1
  rw [map_mul, map_one, fcast_natCast] at h2
  have hi0 : (i : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpi
  calc fcast p ((i : ZMod (p^5))⁻¹)
      = (i : ZMod p)⁻¹ * ((i : ZMod p) * fcast p ((i : ZMod (p^5))⁻¹)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hi0, one_mul]
    _ = (i : ZMod p)⁻¹ * 1 := by rw [h2]
    _ = (i : ZMod p)⁻¹ := mul_one _

theorem Hs_dvd_p [Fact p.Prime] (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ p - 2) :
    (p : ZMod (p^5)) ∣ Hs p j := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  haveI : NeZero (p^5) := ⟨by positivity⟩
  apply dvd_p_of_val_cast_zero (by omega)
  rw [ZMod.natCast_val]
  have hcast : (ZMod.cast (Hs p j) : ZMod p) = fcast p (Hs p j) := (ZMod.castHom_apply _).symm
  rw [hcast, Hs, map_sum]
  have hcong : ∀ i ∈ Ico 1 p, fcast p (((i:ZMod (p^5)))⁻¹ ^ j) = ((i:ZMod p))⁻¹ ^ j := by
    intro i hi; rw [mem_Ico] at hi; rw [map_pow, fcast_inv i hi.1 hi.2]
  rw [Finset.sum_congr rfl hcong]
  exact sum_inv_pow_zero j hj1 hj2

theorem pairing_P2 [Fact p.Prime] (hp5 : 5 ≤ p) :
    (0 : ZMod (p^5)) = 2 * (p : ZMod (p^5)) * Hs p 3 + 3 * (p : ZMod (p^5))^2 * Hs p 4
      + 4 * (p : ZMod (p^5))^3 * Hs p 5 + 5 * (p : ZMod (p^5))^4 * Hs p 6 := by
  set P := (p : ZMod (p^5)) with hP
  have hP5 : P^5 = 0 := by
    have : P^5 = ((p^5:ℕ):ZMod (p^5)) := by push_cast; ring
    rw [this]; exact ZMod.natCast_self _
  have hrefl : ∑ i ∈ Ico 1 p, ((p - i : ℕ):ZMod (p^5))⁻¹ ^ 2 = Hs p 2 := by
    have := sum_reflect (p := p) (fun i => ((i:ℕ):ZMod (p^5))⁻¹ ^ 2)
    simpa [Hs] using this
  have hexp : ∀ i ∈ Ico 1 p, ((p - i : ℕ):ZMod (p^5))⁻¹ ^ 2
      = ((i:ZMod (p^5)))⁻¹^2 + 2*P*((i:ZMod (p^5)))⁻¹^3 + 3*P^2*((i:ZMod (p^5)))⁻¹^4
        + 4*P^3*((i:ZMod (p^5)))⁻¹^5 + 5*P^4*((i:ZMod (p^5)))⁻¹^6 := by
    intro i hi
    rw [mem_Ico] at hi
    set I := ((i:ZMod (p^5)))⁻¹ with hI
    rw [inv_pmi_expand hp5 i hi.1 hi.2]
    have hid : (-(I + P*I^2 + P^2*I^3 + P^3*I^4 + P^4*I^5))^2
        = (I^2 + 2*P*I^3 + 3*P^2*I^4 + 4*P^3*I^5 + 5*P^4*I^6)
          + P^5 * (4*I^7 + 3*P*I^8 + 2*P^2*I^9 + P^3*I^10) := by ring
    rw [hid, hP5]; ring
  have hsum := Finset.sum_congr rfl hexp
  rw [hrefl] at hsum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have e3 : (∑ i ∈ Ico 1 p, ((i:ZMod (p^5)))⁻¹^3) = Hs p 3 := rfl
  have e4 : (∑ i ∈ Ico 1 p, ((i:ZMod (p^5)))⁻¹^4) = Hs p 4 := rfl
  have e5 : (∑ i ∈ Ico 1 p, ((i:ZMod (p^5)))⁻¹^5) = Hs p 5 := rfl
  have e6 : (∑ i ∈ Ico 1 p, ((i:ZMod (p^5)))⁻¹^6) = Hs p 6 := rfl
  have e2 : (∑ i ∈ Ico 1 p, ((i:ZMod (p^5)))⁻¹^2) = Hs p 2 := rfl
  rw [e2, e3, e4, e5, e6] at hsum
  -- hsum : Hs2 = Hs2 + 2P Hs3 + 3P^2 Hs4 + 4P^3 Hs5 + 5P^4 Hs6
  linear_combination hsum

-- ===== prod_one_add_trunc =====

-- Truncated product expansion: if all products of ≥5 elements vanish, the product expands to degree 4.
theorem prod_one_add_trunc {ι R : Type*} [CommRing R] [DecidableEq ι] (a : ι → R) (s : Finset ι)
    (h : ∀ t ⊆ s, 5 ≤ #t → ∏ i ∈ t, a i = 0) (hs : 5 ≤ #s) :
    ∏ i ∈ s, (1 + a i) = ∑ j ∈ range 5, ∑ t ∈ powersetCard j s, ∏ i ∈ t, a i := by
  rw [Finset.prod_one_add, Finset.sum_powerset]
  have hsplit : range (#s + 1) = range 5 ∪ Ico 5 (#s + 1) := by
    ext x; simp only [mem_range, mem_union, mem_Ico]; omega
  rw [hsplit, Finset.sum_union]
  · have hzero : ∑ j ∈ Ico 5 (#s + 1), ∑ t ∈ powersetCard j s, ∏ i ∈ t, a i = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [mem_Ico] at hj
      apply Finset.sum_eq_zero
      intro t ht
      rw [Finset.mem_powersetCard] at ht
      exact h t ht.1 (by rw [ht.2]; exact hj.1)
    rw [hzero, add_zero]
  · rw [range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 5 (#s + 1)

-- ===== Binomial-to-product bridge =====
theorem binom_prod_nat_gen (p t : ℕ) (hp1 : 1 ≤ p) :
    (p-1)! * ((t+1)*p-1).choose (p-1) = ∏ j ∈ Ico 1 p, (t*p+j) := by
  have h1 : ((t+1)*p-1).descFactorial (p-1) = (p-1)! * ((t+1)*p-1).choose (p-1) :=
    Nat.descFactorial_eq_factorial_mul_choose ((t+1)*p-1) (p-1)
  have h2 : ((t+1)*p-1).descFactorial (p-1) = ∏ i ∈ range (p-1), ((t+1)*p-1-i) :=
    Nat.descFactorial_eq_prod_range ((t+1)*p-1) (p-1)
  rw [← h1, h2]
  apply Finset.prod_nbij' (fun i => p-1-i) (fun j => p-1-j)
  · intro i hi; rw [mem_range] at hi; rw [mem_Ico]; omega
  · intro j hj; rw [mem_Ico] at hj; rw [mem_range]; omega
  · intro i hi; rw [mem_range] at hi; omega
  · intro j hj; rw [mem_Ico] at hj; omega
  · intro i hi; rw [mem_range] at hi
    have hexp : (t+1)*p = t*p + p := by ring
    omega

theorem binom_prod_zmod (p t : ℕ) (hp : p.Prime) (hp1 : 1 ≤ p) :
    (((t+1)*p-1).choose (p-1) : ZMod (p^5))
      = ∏ j ∈ Ico 1 p, (1 + (t:ZMod (p^5))*(p:ZMod (p^5)) * ((j:ZMod (p^5)))⁻¹) := by
  haveI : NeZero (p^5) := ⟨by positivity⟩
  have hunit : ∀ j, j ∈ Ico 1 p → IsUnit ((j:ZMod (p^5))) := by
    intro j hj; rw [mem_Ico] at hj
    have hpj : ¬ p ∣ j := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hcop : Nat.Coprime j p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hpj)
    exact (ZMod.isUnit_iff_coprime j (p^5)).mpr (hcop.pow_right 5)
  have hfacunit : IsUnit (((p-1)! : ℕ) : ZMod (p^5)) := by
    have hpf : ¬ p ∣ (p-1)! := by rw [hp.dvd_factorial]; omega
    have hcop : Nat.Coprime ((p-1)!) p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hpf)
    exact (ZMod.isUnit_iff_coprime _ (p^5)).mpr (hcop.pow_right 5)
  have hnat := binom_prod_nat_gen p t hp1
  -- cast to ZMod
  have hcast : (((p-1)! : ℕ) : ZMod (p^5)) * (((t+1)*p-1).choose (p-1) : ZMod (p^5))
      = ∏ j ∈ Ico 1 p, ((t:ZMod (p^5))*(p:ZMod (p^5)) + (j:ZMod (p^5))) := by
    have := congrArg (fun n : ℕ => (n : ZMod (p^5))) hnat
    push_cast at this
    convert this using 2
  have hfacprod : (((p-1)! : ℕ) : ZMod (p^5)) = ∏ j ∈ Ico 1 p, (j : ZMod (p^5)) := by
    have := Finset.prod_Ico_id_eq_factorial (p-1)
    rw [show p-1+1 = p by omega] at this
    rw [← this]; push_cast; rfl
  have hrw : ∏ j ∈ Ico 1 p, ((t:ZMod (p^5))*(p:ZMod (p^5)) + (j:ZMod (p^5)))
      = (((p-1)! : ℕ) : ZMod (p^5)) * ∏ j ∈ Ico 1 p, (1 + (t:ZMod (p^5))*(p:ZMod (p^5)) * ((j:ZMod (p^5)))⁻¹) := by
    rw [hfacprod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    have hju := hunit j hj
    have hjinv : (j:ZMod (p^5)) * ((j:ZMod (p^5)))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hju
    have : (j:ZMod (p^5)) * (1 + (t:ZMod (p^5))*(p:ZMod (p^5)) * ((j:ZMod (p^5)))⁻¹)
        = (t:ZMod (p^5))*(p:ZMod (p^5)) + (j:ZMod (p^5)) := by
      have h := hjinv
      ring_nf
      ring_nf at h
      linear_combination (t*(p:ZMod (p^5))) * h
    rw [this]
  rw [hrw] at hcast
  exact hfacunit.mul_left_cancel hcast

noncomputable def S1z (p : ℕ) : ℤ := ∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k : ℤ)

theorem S1z_eq (p : ℕ) (hp1 : 1 ≤ p) : S1z p = ((3*p).choose p : ℤ) := by
  unfold S1z
  have reindex : ∀ k ∈ range (2*p+1), (p+k-1).choose k = (k+(p-1)).choose (p-1) := by
    intro k _
    have h1 : p+k-1 = k+(p-1) := by omega
    rw [h1]
    have := Nat.choose_symm (Nat.le_add_left (p-1) k)
    rw [show k+(p-1)-(p-1)=k by omega] at this
    exact this
  rw [Finset.sum_congr rfl (fun k hk => by rw [reindex k hk])]
  have hsum := Nat.sum_range_add_choose (2*p) (p-1)
  rw [← Nat.cast_sum, hsum]
  congr 2
  · omega
  · omega

-- ===== Derived harmonic facts and product expansion =====
section S1prep
variable {p : ℕ}

theorem isUnit_natCast_lt_prime (hp : p.Prime) {n : ℕ} (hn0 : 0 < n) (hnp : n < p) :
    IsUnit ((n : ℕ) : ZMod (p^5)) := by
  have hpn : ¬ p ∣ n := fun hd => by have := Nat.le_of_dvd hn0 hd; omega
  have hcop : Nat.Coprime n p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hpn)
  exact (ZMod.isUnit_iff_coprime n (p^5)).mpr (hcop.pow_right 5)

theorem two_unit5 [Fact p.Prime] (hp5 : 5 ≤ p) : IsUnit (2 : ZMod (p^5)) := by
  rw [show (2:ZMod (p^5)) = ((2:ℕ):ZMod (p^5)) by norm_cast]
  exact isUnit_natCast_lt_prime (Fact.out) (by norm_num) (by omega)

theorem pP5 [Fact p.Prime] : (p:ZMod (p^5))^5 = 0 := by
  have : (p:ZMod (p^5))^5 = ((p^5:ℕ):ZMod (p^5)) := by push_cast; ring
  rw [this]; exact ZMod.natCast_self _

theorem Hs1_dvd_p2 [Fact p.Prime] (hp5 : 5 ≤ p) : (p:ZMod (p^5))^2 ∣ Hs p 1 := by
  obtain ⟨a2, ha2⟩ := Hs_dvd_p (p := p) 2 (by omega) (by omega)
  have hpair := pairing_P1 (p:=p) hp5
  have h2u := two_unit5 (p:=p) hp5
  refine ⟨(2:ZMod (p^5))⁻¹ * (-(a2 + Hs p 3 + (p:ZMod (p^5))*Hs p 4 + (p:ZMod (p^5))^2 * Hs p 5)), ?_⟩
  have hinv2 : (2:ZMod (p^5))⁻¹ * 2 = 1 := ZMod.inv_mul_of_unit _ h2u
  have h2 : (2:ZMod (p^5)) * Hs p 1
      = (p:ZMod (p^5))^2 * (-(a2 + Hs p 3 + (p:ZMod (p^5))*Hs p 4 + (p:ZMod (p^5))^2 * Hs p 5)) := by
    rw [hpair, ha2]; ring
  calc Hs p 1 = (2:ZMod (p^5))⁻¹ * (2 * Hs p 1) := by rw [← mul_assoc, hinv2, one_mul]
    _ = (2:ZMod (p^5))⁻¹ * ((p:ZMod (p^5))^2 * _) := by rw [h2]
    _ = _ := by ring

theorem pHs4_zero [Fact p.Prime] (hp7 : 7 ≤ p) : (p:ZMod (p^5))^4 * Hs p 4 = 0 := by
  obtain ⟨b, hb⟩ := Hs_dvd_p (p := p) 4 (by omega) (by omega)
  rw [hb]
  have h5 := pP5 (p:=p)
  calc (p:ZMod (p^5))^4 * ((p:ZMod (p^5)) * b) = (p:ZMod (p^5))^5 * b := by ring
    _ = 0 := by rw [h5]; ring

theorem pHs3_zero [Fact p.Prime] (hp7 : 7 ≤ p) : (p:ZMod (p^5))^3 * Hs p 3 = 0 := by
  have hP2 := pairing_P2 (p:=p) (by omega)
  have h5 := pP5 (p:=p)
  have hp4 := pHs4_zero (p:=p) hp7
  have h2u := two_unit5 (p:=p) (by omega)
  -- multiply pairing_P2 by p^2:
  have key : (2:ZMod (p^5)) * ((p:ZMod (p^5))^3 * Hs p 3) = 0 := by
    have e : (p:ZMod (p^5))^2 * (0 : ZMod (p^5))
        = (p:ZMod (p^5))^2 * (2 * (p:ZMod (p^5)) * Hs p 3 + 3 * (p:ZMod (p^5))^2 * Hs p 4
            + 4 * (p:ZMod (p^5))^3 * Hs p 5 + 5 * (p:ZMod (p^5))^4 * Hs p 6) := by rw [← hP2]
    have expand : (p:ZMod (p^5))^2 * (2 * (p:ZMod (p^5)) * Hs p 3 + 3 * (p:ZMod (p^5))^2 * Hs p 4
            + 4 * (p:ZMod (p^5))^3 * Hs p 5 + 5 * (p:ZMod (p^5))^4 * Hs p 6)
        = 2 * ((p:ZMod (p^5))^3 * Hs p 3) + 3 * ((p:ZMod (p^5))^4 * Hs p 4)
          + (p:ZMod (p^5))^5 * (4 * Hs p 5 + 5 * (p:ZMod (p^5)) * Hs p 6) := by ring
    rw [expand, h5, hp4] at e
    linear_combination -e
  calc (p:ZMod (p^5))^3 * Hs p 3
      = (2:ZMod (p^5))⁻¹ * ((2:ZMod (p^5)) * ((p:ZMod (p^5))^3 * Hs p 3)) := by
        rw [← mul_assoc, ZMod.inv_mul_of_unit _ h2u, one_mul]
    _ = 0 := by rw [key]; ring

end S1prep

section ProdExpand
variable {p : ℕ}

-- Psym of inverses equals Hs
theorem Psym_inv_eq_Hs (k : ℕ) :
    Psym (fun j => ((j:ZMod (p^5)))⁻¹) k (Ico 1 p) = Hs p k := rfl

theorem nat_unit5 [Fact p.Prime] (n : ℕ) (hn0 : 0 < n) (hnp : n < p) :
    IsUnit ((n:ℕ) : ZMod (p^5)) := isUnit_natCast_lt_prime (Fact.out) hn0 hnp

theorem E3_zero [Fact p.Prime] (hp7 : 7 ≤ p) :
    (p:ZMod (p^5))^3 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 3 (Ico 1 p) = 0 := by
  have hN3 := newton3 (fun j => ((j:ZMod (p^5)))⁻¹) (Ico 1 p)
  rw [Psym_inv_eq_Hs, Psym_inv_eq_Hs, Psym_inv_eq_Hs] at hN3
  obtain ⟨x, hx⟩ := Hs1_dvd_p2 (p:=p) (by omega)
  have hHs3 := pHs3_zero (p:=p) hp7
  have h5 := pP5 (p:=p)
  have h3u : IsUnit ((3:ℕ):ZMod (p^5)) := nat_unit5 3 (by norm_num) (by omega)
  rw [show ((3:ℕ):ZMod (p^5)) = 3 by norm_cast] at h3u
  -- 3 * (P^3 E3) = P^3 * (3 E3) = P^3 (E2 Hs1 - Hs1 Hs2 + Hs3)
  have key : (3:ZMod (p^5)) * ((p:ZMod (p^5))^3 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 3 (Ico 1 p)) = 0 := by
    have e : (3:ZMod (p^5)) * ((p:ZMod (p^5))^3 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 3 (Ico 1 p))
        = (p:ZMod (p^5))^3 * (3 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 3 (Ico 1 p)) := by ring
    rw [e, hN3, hx]
    linear_combination (Esym (fun j => ((j:ZMod (p^5)))⁻¹) 2 (Ico 1 p) * x - x * Hs p 2) * h5 + hHs3
  calc (p:ZMod (p^5))^3 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 3 (Ico 1 p)
      = (3:ZMod (p^5))⁻¹ * (3 * ((p:ZMod (p^5))^3 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 3 (Ico 1 p))) := by
        rw [← mul_assoc, ZMod.inv_mul_of_unit _ h3u, one_mul]
    _ = 0 := by rw [key]; ring

theorem E4_zero [Fact p.Prime] (hp7 : 7 ≤ p) :
    (p:ZMod (p^5))^4 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 4 (Ico 1 p) = 0 := by
  have hN4 := newton4 (fun j => ((j:ZMod (p^5)))⁻¹) (Ico 1 p)
  rw [Psym_inv_eq_Hs, Psym_inv_eq_Hs, Psym_inv_eq_Hs, Psym_inv_eq_Hs] at hN4
  obtain ⟨x, hx⟩ := Hs1_dvd_p2 (p:=p) (by omega)
  obtain ⟨y, hy⟩ := Hs_dvd_p (p := p) 2 (by omega) (by omega)
  obtain ⟨z, hz⟩ := Hs_dvd_p (p := p) 4 (by omega) (by omega)
  have h5 := pP5 (p:=p)
  have h4u : IsUnit ((4:ℕ):ZMod (p^5)) := nat_unit5 4 (by norm_num) (by omega)
  rw [show ((4:ℕ):ZMod (p^5)) = 4 by norm_cast] at h4u
  have key : (4:ZMod (p^5)) * ((p:ZMod (p^5))^4 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 4 (Ico 1 p)) = 0 := by
    have e : (4:ZMod (p^5)) * ((p:ZMod (p^5))^4 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 4 (Ico 1 p))
        = (p:ZMod (p^5))^4 * (4 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 4 (Ico 1 p)) := by ring
    rw [e, hN4, hx, hy, hz]
    linear_combination
      (Esym (fun j => ((j:ZMod (p^5)))⁻¹) 3 (Ico 1 p) * x * (p:ZMod (p^5))
        - Esym (fun j => ((j:ZMod (p^5)))⁻¹) 2 (Ico 1 p) * y
        + x * Hs p 3 * (p:ZMod (p^5)) - z) * h5
  calc (p:ZMod (p^5))^4 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 4 (Ico 1 p)
      = (4:ZMod (p^5))⁻¹ * (4 * ((p:ZMod (p^5))^4 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 4 (Ico 1 p))) := by
        rw [← mul_assoc, ZMod.inv_mul_of_unit _ h4u, one_mul]
    _ = 0 := by rw [key]; ring

theorem prod_one_add_pinv [Fact p.Prime] (t : ℕ) (hp7 : 7 ≤ p) :
    ∏ j ∈ Ico 1 p, (1 + (t:ZMod (p^5))*(p:ZMod (p^5)) * ((j:ZMod (p^5)))⁻¹)
      = 1 - (t:ZMod (p^5))*((t:ZMod (p^5))+1)*(2:ZMod (p^5))⁻¹*(p:ZMod (p^5))^2 * Hs p 2 := by
  -- abbreviations
  have hlayer : ∀ k : ℕ,
      ∑ t' ∈ powersetCard k (Ico 1 p), ∏ i ∈ t', ((t:ZMod (p^5))*(p:ZMod (p^5)) * ((i:ZMod (p^5)))⁻¹)
        = ((t:ZMod (p^5))*(p:ZMod (p^5)))^k * Esym (fun i => ((i:ZMod (p^5)))⁻¹) k (Ico 1 p) := by
    intro k
    rw [Esym, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t' ht'
    rw [Finset.mem_powersetCard] at ht'
    rw [Finset.prod_mul_distrib, Finset.prod_const, ht'.2]
  have htrunc : ∏ j ∈ Ico 1 p, (1 + (t:ZMod (p^5))*(p:ZMod (p^5)) * ((j:ZMod (p^5)))⁻¹)
      = 1 + ((t:ZMod (p^5))*(p:ZMod (p^5))) * Hs p 1
        + ((t:ZMod (p^5))*(p:ZMod (p^5)))^2 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 2 (Ico 1 p)
        + ((t:ZMod (p^5))*(p:ZMod (p^5)))^3 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 3 (Ico 1 p)
        + ((t:ZMod (p^5))*(p:ZMod (p^5)))^4 * Esym (fun j => ((j:ZMod (p^5)))⁻¹) 4 (Ico 1 p) := by
    have hcond : ∀ t' ⊆ Ico 1 p, 5 ≤ #t' →
        ∏ i ∈ t', ((t:ZMod (p^5))*(p:ZMod (p^5)) * ((i:ZMod (p^5)))⁻¹) = 0 := by
      intro t' _ hcard
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      have hz : ((t:ZMod (p^5))*(p:ZMod (p^5)))^(#t') = 0 := by
        have h5 : ((t:ZMod (p^5))*(p:ZMod (p^5)))^5 = 0 := by
          rw [mul_pow, pP5 (p:=p)]; ring
        calc ((t:ZMod (p^5))*(p:ZMod (p^5)))^(#t')
            = ((t:ZMod (p^5))*(p:ZMod (p^5)))^5 * ((t:ZMod (p^5))*(p:ZMod (p^5)))^(#t'-5) := by
              rw [← pow_add]; congr 1; omega
          _ = 0 := by rw [h5]; ring
      rw [hz, zero_mul]
    have hscond : 5 ≤ #(Ico 1 p) := by rw [Nat.card_Ico]; omega
    have htr := prod_one_add_trunc (R := ZMod (p^5)) (ι := ℕ)
      (fun j => (t:ZMod (p^5))*(p:ZMod (p^5)) * ((j:ZMod (p^5)))⁻¹) (Ico 1 p) hcond hscond
    rw [htr]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    rw [hlayer 0, hlayer 1, hlayer 2, hlayer 3, hlayer 4]
    rw [Esym_zero]
    have hE1 : Esym (fun i => ((i:ZMod (p^5)))⁻¹) 1 (Ico 1 p) = Hs p 1 := by
      rw [Esym_one, Hs]; apply Finset.sum_congr rfl; intro i _; rw [pow_one]
    rw [hE1]; ring
  -- collect facts
  have hpair := pairing_P1 (p:=p) (by omega)
  have hN2 := newton2 (fun j => ((j:ZMod (p^5)))⁻¹) (Ico 1 p)
  rw [Psym_inv_eq_Hs, Psym_inv_eq_Hs] at hN2
  have hE3 := E3_zero (p:=p) hp7
  have hE4 := E4_zero (p:=p) hp7
  have hHs3 := pHs3_zero (p:=p) hp7
  have hHs4 := pHs4_zero (p:=p) hp7
  have h5 := pP5 (p:=p)
  have hHs1sq : (p:ZMod (p^5))^2 * (Hs p 1)^2 = 0 := by
    obtain ⟨x, hx⟩ := Hs1_dvd_p2 (p:=p) (by omega)
    rw [hx]
    calc (p:ZMod (p^5))^2 * ((p:ZMod (p^5))^2 * x)^2
        = (p:ZMod (p^5))^5 * ((p:ZMod (p^5)) * x^2) := by ring
      _ = 0 := by rw [h5]; ring
  have h2u := two_unit5 (p:=p) (by omega)
  have hinv2 : (2:ZMod (p^5))⁻¹ * 2 = 1 := ZMod.inv_mul_of_unit _ h2u
  -- the doubled identity
  have h2prod : 2 * ∏ j ∈ Ico 1 p, (1 + (t:ZMod (p^5))*(p:ZMod (p^5)) * ((j:ZMod (p^5)))⁻¹)
      = 2 - (t:ZMod (p^5))*((t:ZMod (p^5))+1)*(p:ZMod (p^5))^2 * Hs p 2 := by
    rw [htrunc]
    linear_combination
      ((t:ZMod (p^5))*(p:ZMod (p^5)))*hpair
        + ((t:ZMod (p^5))^2*(p:ZMod (p^5))^2)*hN2
        + (2*(t:ZMod (p^5))^3)*hE3
        + (2*(t:ZMod (p^5))^4)*hE4
        + (-(t:ZMod (p^5)))*hHs3
        + (-(t:ZMod (p^5)))*hHs4
        + (-(t:ZMod (p^5))*Hs p 5)*h5
        + ((t:ZMod (p^5))^2)*hHs1sq
  calc ∏ j ∈ Ico 1 p, (1 + (t:ZMod (p^5))*(p:ZMod (p^5)) * ((j:ZMod (p^5)))⁻¹)
      = (2:ZMod (p^5))⁻¹ * (2 * ∏ j ∈ Ico 1 p, (1 + (t:ZMod (p^5))*(p:ZMod (p^5)) * ((j:ZMod (p^5)))⁻¹)) := by
        rw [← mul_assoc, hinv2, one_mul]
    _ = (2:ZMod (p^5))⁻¹ * (2 - (t:ZMod (p^5))*((t:ZMod (p^5))+1)*(p:ZMod (p^5))^2 * Hs p 2) := by rw [h2prod]
    _ = _ := by rw [mul_sub, hinv2]; ring

end ProdExpand
