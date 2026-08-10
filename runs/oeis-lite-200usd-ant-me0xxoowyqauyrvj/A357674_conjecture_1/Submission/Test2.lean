import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

theorem binom_prod_nat (p : ℕ) (hp1 : 1 ≤ p) :
    (p-1)! * (3*p-1).choose (p-1) = ∏ j ∈ Ico 1 p, (2*p+j) := by
  have h1 : (3*p-1).descFactorial (p-1) = (p-1)! * (3*p-1).choose (p-1) :=
    Nat.descFactorial_eq_factorial_mul_choose (3*p-1) (p-1)
  have h2 : (3*p-1).descFactorial (p-1) = ∏ i ∈ range (p-1), (3*p-1-i) :=
    Nat.descFactorial_eq_prod_range (3*p-1) (p-1)
  rw [← h1, h2]
  apply Finset.prod_nbij' (fun i => p-1-i) (fun j => p-1-j)
  · intro i hi; rw [mem_range] at hi; rw [mem_Ico]; omega
  · intro j hj; rw [mem_Ico] at hj; rw [mem_range]; omega
  · intro i hi; rw [mem_range] at hi; omega
  · intro j hj; rw [mem_Ico] at hj; omega
  · intro i hi; rw [mem_range] at hi; omega

theorem cbinom (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (wolst1 : (p:ℤ)^2 ∣ ∑ j ∈ Ico 1 p, ∏ i ∈ (Ico 1 p).erase j, (i:ℤ))
    (wolst2 : (p:ℤ) ∣ ∑ i ∈ Ico 1 p, (∏ j ∈ (Ico 1 p).erase i, (j:ℤ))^2)
    (prod_one_add_cube : ∀ {ι R : Type} [inst : CommRing R] [inst2 : DecidableEq ι] (a : ι → R),
      (∀ i j k, a i * a j * a k = 0) → ∀ (s : Finset ι),
      2 * ∏ i ∈ s, (1 + a i) = 2 + 2 * (∑ i ∈ s, a i) + ((∑ i ∈ s, a i)^2 - ∑ i ∈ s, (a i)^2)) :
    ((3*p-1).choose (p-1) : ZMod (p^3)) = 1 := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  have hp1 : 1 ≤ p := by omega
  -- units
  have hunit : ∀ j : ℕ, 1 ≤ j → j < p → IsUnit ((j:ℕ):ZMod (p^3)) := by
    intro j hj1 hj2
    have hpj : ¬ p ∣ j := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hcop : Nat.Coprime j p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hpj)
    exact (ZMod.isUnit_iff_coprime j (p^3)).mpr (hcop.pow_right 3)
  have hfacunit : IsUnit (((p-1)! : ℕ) : ZMod (p^3)) := by
    have hpf : ¬ p ∣ (p-1)! := by rw [hp.dvd_factorial]; omega
    have hcop : Nat.Coprime ((p-1)!) p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hpf)
    exact (ZMod.isUnit_iff_coprime ((p-1)!) (p^3)).mpr (hcop.pow_right 3)
  have h2unit : IsUnit ((2:ℕ) : ZMod (p^3)) := by
    have hp2 : ¬ p ∣ 2 := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hcop : Nat.Coprime 2 p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hp2)
    exact (ZMod.isUnit_iff_coprime 2 (p^3)).mpr (hcop.pow_right 3)
  set a : ℕ → ZMod (p^3) := fun j => 2*(p:ZMod (p^3))*((j:ZMod (p^3)))⁻¹ with ha
  have hp3z : ((p:ZMod (p^3)))^3 = 0 := by
    have : ((p:ZMod (p^3)))^3 = ((p^3:ℕ):ZMod (p^3)) := by push_cast; ring
    rw [this]; exact ZMod.natCast_self _
  have htriple : ∀ i j k, a i * a j * a k = 0 := by
    intro i j k
    have he : a i * a j * a k = ((p:ZMod (p^3)))^3 * (8 * ((i:ZMod (p^3)))⁻¹ * ((j:ZMod (p^3)))⁻¹ * ((k:ZMod (p^3)))⁻¹) := by
      simp only [ha]; ring
    rw [he, hp3z, zero_mul]
  -- factorial as product
  have hfac_eq : (((p-1)! : ℕ) : ZMod (p^3)) = ∏ i ∈ Ico 1 p, ((i:ℕ):ZMod (p^3)) := by
    have := Finset.prod_Ico_id_eq_factorial (p-1)
    rw [show (p-1)+1 = p by omega] at this
    rw [← this, Nat.cast_prod]
  -- bridge P_j
  have hPbridge : ∀ j ∈ Ico 1 p, (((p-1)! : ℕ):ZMod (p^3)) * ((j:ZMod (p^3)))⁻¹ = ∏ i ∈ (Ico 1 p).erase j, ((i:ℕ):ZMod (p^3)) := by
    intro j hj
    rw [mem_Ico] at hj
    have hju : IsUnit ((j:ZMod (p^3))) := hunit j hj.1 hj.2
    have hsplit : (((p-1)! : ℕ):ZMod (p^3)) = (j:ZMod (p^3)) * ∏ i ∈ (Ico 1 p).erase j, ((i:ℕ):ZMod (p^3)) := by
      rw [hfac_eq]; exact (Finset.mul_prod_erase (Ico 1 p) (fun i => ((i:ℕ):ZMod (p^3))) (mem_Ico.2 hj)).symm
    rw [hsplit, mul_right_comm, ZMod.mul_inv_of_unit _ hju, one_mul]
  -- term bridge for sum a
  have hterm1 : ∀ j ∈ Ico 1 p, (((p-1)! : ℕ):ZMod (p^3)) * a j
      = 2*(p:ZMod (p^3))*∏ i ∈ (Ico 1 p).erase j, ((i:ℕ):ZMod (p^3)) := by
    intro j hj
    have hb := hPbridge j hj
    simp only [ha]
    rw [show (((p-1)! : ℕ):ZMod (p^3))*(2*(p:ZMod (p^3))*((j:ZMod (p^3)))⁻¹)
        = 2*(p:ZMod (p^3))*((((p-1)! : ℕ):ZMod (p^3))*((j:ZMod (p^3)))⁻¹) by ring, hb]
  have hbridge1 : (((p-1)! : ℕ):ZMod (p^3))*(∑ j ∈ Ico 1 p, a j)
      = 2*(p:ZMod (p^3))*(∑ j ∈ Ico 1 p, ∏ i ∈ (Ico 1 p).erase j, ((i:ℕ):ZMod (p^3))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm1
  have hsumPcast : (∑ j ∈ Ico 1 p, ∏ i ∈ (Ico 1 p).erase j, ((i:ℕ):ZMod (p^3)))
      = (((∑ j ∈ Ico 1 p, ∏ i ∈ (Ico 1 p).erase j, (i:ℤ)) : ℤ) : ZMod (p^3)) := by
    push_cast; rfl
  have hsumA0 : ∑ j ∈ Ico 1 p, a j = 0 := by
    apply (IsUnit.mul_right_eq_zero hfacunit).mp
    rw [hbridge1, hsumPcast]
    rw [show 2*(p:ZMod (p^3))*(((∑ j ∈ Ico 1 p, ∏ i ∈ (Ico 1 p).erase j, (i:ℤ)) : ℤ) : ZMod (p^3))
        = (((2*(p:ℤ)*(∑ j ∈ Ico 1 p, ∏ i ∈ (Ico 1 p).erase j, (i:ℤ))) : ℤ) : ZMod (p^3)) by push_cast; ring]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨m, hm⟩ := wolst1
    rw [hm]; push_cast; exact ⟨2*m, by ring⟩
  -- term bridge for sum a^2
  have hPbridge2 : ∀ j ∈ Ico 1 p, (((p-1)! : ℕ):ZMod (p^3))^2 * ((j:ZMod (p^3)))⁻¹^2
      = (∏ i ∈ (Ico 1 p).erase j, ((i:ℕ):ZMod (p^3)))^2 := by
    intro j hj
    have hb := hPbridge j hj
    rw [show (((p-1)! : ℕ):ZMod (p^3))^2 * ((j:ZMod (p^3)))⁻¹^2
        = ((((p-1)! : ℕ):ZMod (p^3)) * ((j:ZMod (p^3)))⁻¹)^2 by ring, hb]
  have hterm2 : ∀ j ∈ Ico 1 p, (((p-1)! : ℕ):ZMod (p^3))^2 * (a j)^2
      = 4*(p:ZMod (p^3))^2*(∏ i ∈ (Ico 1 p).erase j, ((i:ℕ):ZMod (p^3)))^2 := by
    intro j hj
    have hb := hPbridge2 j hj
    simp only [ha]
    rw [show (((p-1)! : ℕ):ZMod (p^3))^2 * (2*(p:ZMod (p^3))*((j:ZMod (p^3)))⁻¹)^2
        = 4*(p:ZMod (p^3))^2*((((p-1)! : ℕ):ZMod (p^3))^2*((j:ZMod (p^3)))⁻¹^2) by ring, hb]
  have hbridge2 : (((p-1)! : ℕ):ZMod (p^3))^2*(∑ j ∈ Ico 1 p, (a j)^2)
      = 4*(p:ZMod (p^3))^2*(∑ j ∈ Ico 1 p, (∏ i ∈ (Ico 1 p).erase j, ((i:ℕ):ZMod (p^3)))^2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm2
  have hsumPcast2 : (∑ j ∈ Ico 1 p, (∏ i ∈ (Ico 1 p).erase j, ((i:ℕ):ZMod (p^3)))^2)
      = (((∑ i ∈ Ico 1 p, (∏ j ∈ (Ico 1 p).erase i, (j:ℤ))^2) : ℤ) : ZMod (p^3)) := by
    push_cast; rfl
  have hsumA20 : ∑ j ∈ Ico 1 p, (a j)^2 = 0 := by
    apply (IsUnit.mul_right_eq_zero (hfacunit.pow 2)).mp
    rw [hbridge2, hsumPcast2]
    rw [show 4*(p:ZMod (p^3))^2*(((∑ i ∈ Ico 1 p, (∏ j ∈ (Ico 1 p).erase i, (j:ℤ))^2) : ℤ) : ZMod (p^3))
        = (((4*(p:ℤ)^2*(∑ i ∈ Ico 1 p, (∏ j ∈ (Ico 1 p).erase i, (j:ℤ))^2)) : ℤ) : ZMod (p^3)) by push_cast; ring]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨m, hm⟩ := wolst2
    rw [hm]; push_cast; exact ⟨4*m, by ring⟩
  -- prod = 1
  have hprod1 : ∏ j ∈ Ico 1 p, (1 + a j) = 1 := by
    have h2p := prod_one_add_cube a htriple (Ico 1 p)
    rw [hsumA0, hsumA20] at h2p
    simp only [mul_zero, sub_zero, add_zero] at h2p
    -- 2 * prod = 2
    apply (IsUnit.mul_left_cancel (by exact_mod_cast h2unit))
    rw [mul_one]
    have : (2:ZMod (p^3)) = ((2:ℕ):ZMod (p^3)) := by push_cast; ring
    rw [this] at h2p ⊢
    convert h2p using 2
    push_cast; ring
  -- factor each term
  have hfactor : ∀ j ∈ Ico 1 p, ((2*p+j : ℕ):ZMod (p^3)) = ((j:ℕ):ZMod (p^3)) * (1 + a j) := by
    intro j hj
    rw [mem_Ico] at hj
    have hju : IsUnit ((j:ZMod (p^3))) := hunit j hj.1 hj.2
    have hinv : (j:ZMod (p^3)) * ((j:ZMod (p^3)))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hju
    simp only [ha]
    push_cast
    rw [mul_add, mul_one,
      show (j:ZMod (p^3))*(2*(p:ZMod (p^3))*((j:ZMod (p^3)))⁻¹)
        = 2*(p:ZMod (p^3))*((j:ZMod (p^3))*((j:ZMod (p^3)))⁻¹) by ring, hinv]
    ring
  have hprodfac : ∏ j ∈ Ico 1 p, ((2*p+j : ℕ):ZMod (p^3))
      = (((p-1)! : ℕ):ZMod (p^3)) * ∏ j ∈ Ico 1 p, (1 + a j) := by
    rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, ← hfac_eq]
  have hcast_id : (((p-1)! : ℕ):ZMod (p^3)) * ((3*p-1).choose (p-1) : ZMod (p^3))
      = ∏ j ∈ Ico 1 p, ((2*p+j : ℕ):ZMod (p^3)) := by
    have h := binom_prod_nat p hp1
    calc (((p-1)! : ℕ):ZMod (p^3)) * ((3*p-1).choose (p-1) : ZMod (p^3))
        = (((p-1)! * (3*p-1).choose (p-1) : ℕ):ZMod (p^3)) := by push_cast; ring
      _ = ((∏ j ∈ Ico 1 p, (2*p+j) : ℕ):ZMod (p^3)) := by rw [h]
      _ = ∏ j ∈ Ico 1 p, ((2*p+j : ℕ):ZMod (p^3)) := by push_cast; rfl
  have hfinal : (((p-1)! : ℕ):ZMod (p^3)) * ((3*p-1).choose (p-1) : ZMod (p^3))
      = (((p-1)! : ℕ):ZMod (p^3)) * 1 := by
    rw [hcast_id, hprodfac, hprod1]
  exact IsUnit.mul_left_cancel hfacunit hfinal
