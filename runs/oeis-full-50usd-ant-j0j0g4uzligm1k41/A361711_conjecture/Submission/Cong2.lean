import Submission.Cong
import Submission.Split
import Submission.Test1

open Finset BigOperators Nat

set_option maxHeartbeats 2000000 in
/-- Key divisibility: `p^k` divides the elementary symmetric "T0" sum. -/
theorem pk_dvd_T0 (p k M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) (hM : 2*M+1 = p^k) :
    ((p^k : ℕ):ℤ) ∣ ∑ i ∈ (Finset.range M).filter (fun i => ¬ p ∣ (i+1)),
        ∏ j ∈ ((Finset.range M).filter (fun i => ¬ p ∣ (i+1))).erase i, ((j:ℤ)+1)^2 := by
  haveI : NeZero (p^k) := ⟨(pow_pos (by omega : 0 < p) k).ne'⟩
  have hpk1 : 1 < p^k := by
    have := Nat.le_self_pow (show k ≠ 0 by omega) p; omega
  set VF := (Finset.range M).filter (fun i => ¬ p ∣ (i+1)) with hVF
  set Vfull := (Finset.range (2*M)).filter (fun i => ¬ p ∣ (i+1)) with hVfull
  -- units 2 and 3
  have h2unit : IsUnit (2:ZMod (p^k)) := by
    rw [show (2:ZMod (p^k)) = ((2:ℕ):ZMod (p^k)) from by push_cast; ring, ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right k
  -- membership helpers
  have hvf : ∀ a, a ∈ VF → a < M ∧ ¬ p ∣ (a+1) := by
    intro a ha; rw [hVF, Finset.mem_filter, Finset.mem_range] at ha; exact ha
  have hsd : ∀ a, a ∈ Vfull \ VF → M ≤ a ∧ a < 2*M ∧ ¬ p ∣ (a+1) := by
    intro a ha
    rw [Finset.mem_sdiff, hVfull, hVF, Finset.mem_filter, Finset.mem_range,
        Finset.mem_filter, Finset.mem_range] at ha
    refine ⟨?_, ha.1.1, ha.1.2⟩
    by_contra h; push_neg at h
    exact ha.2 ⟨h, ha.1.2⟩
  have hcopV : ∀ a ∈ Vfull, Nat.Coprime (a+1) (p^k) := by
    intro a ha
    rw [hVfull, Finset.mem_filter] at ha
    exact (((hp.coprime_iff_not_dvd.mpr ha.2)).symm).pow_right k
  have hupos : ∀ b : (ZMod (p^k))ˣ, 1 ≤ (b:ZMod (p^k)).val := by
    intro b
    rcases Nat.eq_zero_or_pos (b:ZMod (p^k)).val with h0|h0
    · exfalso
      have hcp := ZMod.val_coe_unit_coprime b
      rw [h0, Nat.coprime_zero_left] at hcp
      omega
    · exact h0
  have hundvd : ∀ b : (ZMod (p^k))ˣ, ¬ p ∣ (b:ZMod (p^k)).val := by
    intro b
    have hcp := ZMod.val_coe_unit_coprime b
    have hpdvd : p ∣ p^k := dvd_pow_self p (by omega : k ≠ 0)
    exact (hp.coprime_iff_not_dvd).mp (Nat.Coprime.coprime_dvd_right hpdvd hcp).symm
  -- negation cast helper
  have hneg : ∀ a, a ≤ 2*M → ((2*M - a : ℕ):ZMod (p^k)) = -((a:ZMod (p^k))+1) := by
    intro a hle
    have hcast : ((2*M-a:ℕ):ZMod (p^k)) = ((2*M:ℕ):ZMod (p^k)) - (a:ZMod (p^k)) := by
      rw [Nat.cast_sub hle]
    rw [hcast]
    have h2 : ((2*M:ℕ):ZMod (p^k)) = -1 := by
      have hz : ((2*M+1:ℕ):ZMod (p^k)) = 0 := by rw [hM, ZMod.natCast_self]
      push_cast at hz ⊢
      linear_combination hz
    rw [h2]; ring
  -- reduce to ZMod
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  -- per-term factoring
  have key : (∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ZMod (p^k))+1)^2)
           = (∏ j ∈ VF, ((j:ZMod (p^k))+1)^2) * ∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hunit : IsUnit (((i:ZMod (p^k))+1)^2) := by
      have h1 : IsUnit ((i:ZMod (p^k))+1) := by
        rw [show ((i:ZMod (p^k))+1) = ((i+1:ℕ):ZMod (p^k)) from by push_cast; ring, ZMod.isUnit_iff_coprime]
        exact (((hp.coprime_iff_not_dvd.mpr (hvf i hi).2)).symm).pow_right k
      exact h1.pow 2
    have hW : (∏ j ∈ VF, ((j:ZMod (p^k))+1)^2)
            = (((i:ZMod (p^k))+1)^2) * ∏ j ∈ VF.erase i, ((j:ZMod (p^k))+1)^2 :=
      (Finset.mul_prod_erase VF (fun j => ((j:ZMod (p^k))+1)^2) hi).symm
    rw [hW]
    rw [show (((i:ZMod (p^k))+1)^2 * ∏ j ∈ VF.erase i, ((j:ZMod (p^k))+1)^2) * Ring.inverse (((i:ZMod (p^k))+1)^2)
          = (∏ j ∈ VF.erase i, ((j:ZMod (p^k))+1)^2) * (((i:ZMod (p^k))+1)^2 * Ring.inverse (((i:ZMod (p^k))+1)^2)) from by ring]
    rw [Ring.mul_inverse_cancel _ hunit, mul_one]
  rw [key]
  -- main sum is zero
  have hsum0 : (∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2)) = 0 := by
    -- full sum over Vfull equals the units sum, which is 0
    have hb : (∑ i ∈ Vfull, Ring.inverse (((i:ZMod (p^k))+1)^2))
            = ∑ w : (ZMod (p^k))ˣ, Ring.inverse (((w:ZMod (p^k)))^2) := by
      apply Finset.sum_bij' (fun a ha => ZMod.unitOfCoprime (a+1) (hcopV a ha))
        (fun b _ => (b:ZMod (p^k)).val - 1)
        (fun a ha => Finset.mem_univ _)
        ?_ ?_ ?_ ?_
      · -- hj
        intro b _
        simp only [hVfull, Finset.mem_filter, Finset.mem_range]
        have hbv : (b:ZMod (p^k)).val < p^k := ZMod.val_lt _
        refine ⟨by omega, ?_⟩
        rw [Nat.sub_add_cancel (hupos b)]; exact hundvd b
      · -- left_inv
        intro a ha
        have haM : a < 2*M := by rw [hVfull, Finset.mem_filter, Finset.mem_range] at ha; exact ha.1
        simp only [ZMod.coe_unitOfCoprime]
        rw [ZMod.val_natCast_of_lt (by omega : a+1 < p^k)]
        omega
      · -- right_inv
        intro b _
        apply Units.ext
        simp only [ZMod.coe_unitOfCoprime]
        rw [Nat.sub_add_cancel (hupos b)]
        exact ZMod.natCast_zmod_val _
      · -- summand correspondence
        intro a ha
        dsimp only
        congr 1
        rw [ZMod.coe_unitOfCoprime]
        push_cast; ring
    -- units sum is 0
    have hconv : ∀ w : (ZMod (p^k))ˣ, Ring.inverse (((w:ZMod (p^k)))^2) = ((↑(w⁻¹) : ZMod (p^k)))^2 := by
      intro w
      rw [show ((w:ZMod (p^k)))^2 = ((w^2 : (ZMod (p^k))ˣ):ZMod (p^k)) from (Units.val_pow_eq_pow_val w 2).symm,
          Ring.inverse_unit, show ((w^2:(ZMod (p^k))ˣ))⁻¹ = (w⁻¹)^2 from (inv_pow w 2).symm,
          Units.val_pow_eq_pow_val]
    have hreindex : (∑ w : (ZMod (p^k))ˣ, ((↑(w⁻¹) : ZMod (p^k)))^2)
                  = ∑ w : (ZMod (p^k))ˣ, ((↑w : ZMod (p^k)))^2 :=
      Equiv.sum_comp (Equiv.inv (ZMod (p^k))ˣ) (fun w => ((↑w:ZMod (p^k)))^2)
    have hfull0 : (∑ i ∈ Vfull, Ring.inverse (((i:ZMod (p^k))+1)^2)) = 0 := by
      rw [hb]
      simp_rw [hconv]
      rw [hreindex]
      exact unitsq_sum_zero (p^k) h2unit
        (by rw [show (3:ZMod (p^k)) = ((3:ℕ):ZMod (p^k)) from by push_cast; ring, ZMod.isUnit_iff_coprime]
            exact ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega)).pow_right k)
    -- doubling
    have hVFsub : VF ⊆ Vfull := by
      intro x hx
      rw [hVF, Finset.mem_filter, Finset.mem_range] at hx
      rw [hVfull, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hx.2⟩
    have hbij : (∑ i ∈ Vfull \ VF, Ring.inverse (((i:ZMod (p^k))+1)^2))
              = ∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2) := by
      apply Finset.sum_bij' (fun a _ => 2*M-1-a) (fun a _ => 2*M-1-a) ?_ ?_ ?_ ?_ ?_
      · -- maps Vfull\VF into VF
        intro a ha
        obtain ⟨h1, h2, h3⟩ := hsd a ha
        simp only [hVF, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        intro hd
        have hpk : p ∣ (2*M+1) := by rw [hM]; exact dvd_pow_self p (by omega : k ≠ 0)
        have : p ∣ (a+1) := by
          have := Nat.dvd_sub hpk hd
          rwa [show 2*M+1 - (2*M-1-a+1) = a+1 from by omega] at this
        exact h3 this
      · -- maps VF into Vfull\VF
        intro a ha
        obtain ⟨h1, h2⟩ := hvf a ha
        have hnd : ¬ p ∣ (2*M-1-a+1) := by
          intro hd
          have hpk : p ∣ (2*M+1) := by rw [hM]; exact dvd_pow_self p (by omega : k ≠ 0)
          have : p ∣ (a+1) := by
            have := Nat.dvd_sub hpk hd
            rwa [show 2*M+1 - (2*M-1-a+1) = a+1 from by omega] at this
          exact h2 this
        simp only [Finset.mem_sdiff, hVfull, hVF, Finset.mem_filter, Finset.mem_range]
        refine ⟨⟨by omega, hnd⟩, ?_⟩
        rintro ⟨hlt, _⟩; omega
      · intro a ha; obtain ⟨h1, h2, _⟩ := hsd a ha; dsimp only; omega
      · intro a ha; obtain ⟨h1, _⟩ := hvf a ha; dsimp only; omega
      · -- summand correspondence
        intro a ha
        obtain ⟨h1, h2, _⟩ := hsd a ha
        dsimp only
        congr 1
        rw [show ((2*M-1-a:ℕ):ZMod (p^k)) + 1 = ((2*M-a:ℕ):ZMod (p^k)) from by
              rw [← Nat.cast_add_one]; congr 1; omega,
            hneg a (by omega)]
        ring
    have hsplit : (∑ i ∈ Vfull \ VF, Ring.inverse (((i:ZMod (p^k))+1)^2))
                + (∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2))
                = ∑ i ∈ Vfull, Ring.inverse (((i:ZMod (p^k))+1)^2) := Finset.sum_sdiff hVFsub
    -- hsplit : ∑_{Vfull\VF} + ∑_VF = ∑_Vfull
    have hdbl : (∑ i ∈ Vfull, Ring.inverse (((i:ZMod (p^k))+1)^2))
              = 2 * ∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2) := by
      rw [← hsplit, hbij]; ring
    have hS : (2:ZMod (p^k)) * (∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2)) = 0 := by
      rw [← hdbl]; exact hfull0
    exact (h2unit.mul_right_eq_zero).mp hS
  rw [hsum0, mul_zero]

/-- `u` divides `∏(xᵢ - u) - ∏xᵢ`. -/
theorem divu_lemma (s : Finset ℕ) (x : ℕ → ℤ) (u : ℤ) :
    u ∣ ((∏ i ∈ s, (x i - u)) - ∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    rw [show (x a - u) * ∏ i ∈ s, (x i - u) - x a * ∏ i ∈ s, x i
          = x a * ((∏ i ∈ s, (x i - u)) - ∏ i ∈ s, x i) - u * ∏ i ∈ s, (x i - u) from by ring]
    exact dvd_sub (ih.mul_left (x a)) (dvd_mul_right u _)

/-- `u^2` divides `∏(xᵢ - u) - ∏xᵢ + u·∑ᵢ∏_{j≠i}xⱼ`. -/
theorem expand_lemma (s : Finset ℕ) (x : ℕ → ℤ) (u : ℤ) :
    u^2 ∣ ((∏ i ∈ s, (x i - u)) - (∏ i ∈ s, x i) + u * ∑ i ∈ s, ∏ j ∈ s.erase i, x j) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hRa : ∏ j ∈ (insert a s).erase a, x j = ∏ j ∈ s, x j := by rw [Finset.erase_insert ha]
    have hRs : ∑ i ∈ s, ∏ j ∈ (insert a s).erase i, x j
             = x a * ∑ i ∈ s, ∏ j ∈ s.erase i, x j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hai : a ≠ i := by rintro rfl; exact ha hi
      rw [Finset.erase_insert_of_ne hai,
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    rw [hRa, hRs]
    rw [show (x a - u) * ∏ i ∈ s, (x i - u) - x a * ∏ i ∈ s, x i
            + u * ((∏ i ∈ s, x i) + x a * ∑ i ∈ s, ∏ j ∈ s.erase i, x j)
          = x a * ((∏ i ∈ s, (x i - u)) - (∏ i ∈ s, x i) + u * ∑ i ∈ s, ∏ j ∈ s.erase i, x j)
            - u * ((∏ i ∈ s, (x i - u)) - ∏ i ∈ s, x i) from by ring]
    refine dvd_sub (ih.mul_left (x a)) ?_
    rw [pow_two]
    exact mul_dvd_mul_left u (divu_lemma s x u)

/-- The closed-form integer value at odd arguments. -/
def Aint (m : ℕ) : ℤ := (-1:ℤ)^m * (Gnat m : ℤ)

theorem Aint_cast (m : ℕ) : ((Aint m : ℤ):ℚ) = gq m := by
  simp only [Aint, gq]; push_cast; ring

/-- Core divisibility: `p^(3k)` divides `Aint M - Aint M'`. -/
theorem core_dvd (p k M M' d : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k)
    (hMk : 2*M+1 = p^k) (hM'k : 2*M'+1 = p^(k-1)) (hd : 2*d+1 = p) (hMM' : M = p*M'+d) :
    ((p:ℤ)^(3*k)) ∣ (Aint M - Aint M') := by
  classical
  set VF := (Finset.range M).filter (fun i => ¬ p ∣ (i+1)) with hVF
  -- ℚ product-split
  have hMc : (2*(M:ℚ)+1) = (p:ℚ)^k := by
    have h := congrArg (Nat.cast : ℕ → ℚ) hMk
    push_cast at h; linarith
  have hps : aaq (2*M+1) = (∏ i ∈ VF, (1 - (2*(M:ℚ)+1)^2/((i:ℚ)+1)^2)) * aaq (2*M'+1) := by
    rw [prodrep M,
        ← Finset.prod_filter_mul_prod_filter_not (Finset.range M) (fun i => p ∣ (i+1))
            (fun i => (1 - (2*(M:ℚ)+1)^2/((i:ℚ)+1)^2)),
        hfilterprod p M M' d (by omega) hd hMM', ← prodrep M']
    ring
  -- rewrite each VF factor; introduce p^(2k)
  have hsq : (2*(M:ℚ)+1)^2 = (p:ℚ)^(2*k) := by rw [hMc, ← pow_mul]; congr 1; ring
  have hterm : ∀ i ∈ VF, (1 - (2*(M:ℚ)+1)^2/((i:ℚ)+1)^2)
      = (((i:ℚ)+1)^2 - (p:ℚ)^(2*k))/((i:ℚ)+1)^2 := by
    intro i _
    have hne : ((i:ℚ)+1)^2 ≠ 0 := by positivity
    rw [hsq]; field_simp
  -- denominators
  have hDcast : ((∏ i ∈ VF, ((i:ℤ)+1)^2 : ℤ):ℚ) = ∏ i ∈ VF, ((i:ℚ)+1)^2 := by
    rw [Int.cast_prod]; exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  have hNcast : ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k)) : ℤ):ℚ)
              = ∏ i ∈ VF, (((i:ℚ)+1)^2 - (p:ℚ)^(2*k)) := by
    rw [Int.cast_prod]; exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  have hDne : (∏ i ∈ VF, ((i:ℚ)+1)^2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr; intro i _; positivity
  -- the cleared-denominator ℚ identity
  have hQ : (∏ i ∈ VF, ((i:ℚ)+1)^2) * gq M
          = (∏ i ∈ VF, (((i:ℚ)+1)^2 - (p:ℚ)^(2*k))) * gq M' := by
    have hh : gq M = (∏ i ∈ VF, (((i:ℚ)+1)^2 - (p:ℚ)^(2*k)))
                    / (∏ i ∈ VF, ((i:ℚ)+1)^2) * gq M' := by
      rw [← closedform M, ← closedform M', hps]
      rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib]
    rw [hh]; field_simp
  -- cast to ℤ : KEYI
  have hKEYI : (∏ i ∈ VF, ((i:ℤ)+1)^2) * Aint M
             = (∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) * Aint M' := by
    have : ((∏ i ∈ VF, ((i:ℤ)+1)^2 : ℤ):ℚ) * (Aint M : ℚ)
         = ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k)) : ℤ):ℚ) * (Aint M' : ℚ) := by
      rw [hDcast, hNcast, Aint_cast, Aint_cast]; exact hQ
    exact_mod_cast this
  -- p^k ∣ T0z
  have hT0 : (p:ℤ)^k ∣ ∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2 := by
    have hpk := pk_dvd_T0 p k M hp hp5 hk hMk
    rw [← hVF] at hpk
    have hcast : ((p^k:ℕ):ℤ) = (p:ℤ)^k := by push_cast; ring
    rwa [hcast] at hpk
  -- p^(3k) ∣ Nz - Dz
  have hexp : ((p:ℤ)^(2*k))^2 ∣ ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k)))
        - (∏ i ∈ VF, ((i:ℤ)+1)^2) + (p:ℤ)^(2*k) * ∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2) :=
    expand_lemma VF (fun i => ((i:ℤ)+1)^2) ((p:ℤ)^(2*k))
  have hNminusD : ((p:ℤ)^(3*k)) ∣ ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) - (∏ i ∈ VF, ((i:ℤ)+1)^2)) := by
    have h1 : ((p:ℤ)^(3*k)) ∣ ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) - (∏ i ∈ VF, ((i:ℤ)+1)^2)
                + (p:ℤ)^(2*k) * ∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2) := by
      refine dvd_trans (pow_dvd_pow (p:ℤ) (by omega : 3*k ≤ 4*k)) ?_
      have he : ((p:ℤ)^(2*k))^2 = (p:ℤ)^(4*k) := by rw [← pow_mul]; ring_nf
      rw [← he]; exact hexp
    have h2 : ((p:ℤ)^(3*k)) ∣ ((p:ℤ)^(2*k) * ∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2) := by
      have hmm : (p:ℤ)^(2*k) * (p:ℤ)^k ∣ (p:ℤ)^(2*k) * ∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2 :=
        mul_dvd_mul_left _ hT0
      rwa [← pow_add, show 2*k+k = 3*k from by ring] at hmm
    have h3 := dvd_sub h1 h2
    rwa [show (∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) - (∏ i ∈ VF, ((i:ℤ)+1)^2)
              + (p:ℤ)^(2*k) * (∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2)
              - (p:ℤ)^(2*k) * (∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2)
            = (∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) - (∏ i ∈ VF, ((i:ℤ)+1)^2) from by ring] at h3
  -- p^(3k) ∣ Dz * (Aint M - Aint M')
  have hDdiff : ((p:ℤ)^(3*k)) ∣ (∏ i ∈ VF, ((i:ℤ)+1)^2) * (Aint M - Aint M') := by
    have heq : (∏ i ∈ VF, ((i:ℤ)+1)^2) * (Aint M - Aint M')
             = ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) - (∏ i ∈ VF, ((i:ℤ)+1)^2)) * Aint M' := by
      linear_combination hKEYI
    rw [heq]; exact hNminusD.mul_right _
  -- coprimality and cancellation
  have hcop : IsCoprime ((p:ℤ)^(3*k)) (∏ i ∈ VF, ((i:ℤ)+1)^2) := by
    apply IsCoprime.pow_left
    apply IsCoprime.prod_right
    intro i hi
    apply IsCoprime.pow_right
    rw [hVF, Finset.mem_filter] at hi
    rw [show ((i:ℤ)+1) = ((i+1:ℕ):ℤ) from by push_cast; ring]
    exact Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hi.2)
  exact hcop.dvd_of_dvd_mul_left hDdiff
