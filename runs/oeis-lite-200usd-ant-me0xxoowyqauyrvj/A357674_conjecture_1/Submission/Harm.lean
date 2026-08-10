import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

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
