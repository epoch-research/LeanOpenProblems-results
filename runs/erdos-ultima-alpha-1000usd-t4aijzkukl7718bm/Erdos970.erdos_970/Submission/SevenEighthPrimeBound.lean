import Submission.SelbergSeventhEnergy
import Submission.SevenEighthTail

/-! A prime-class survivor bound at cardinality t^8 and length O(t^22).
This gives exponent 11/4, not the conjectured exponent two. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def sevenEighthCutoffScale : ℕ :=
  1024 + ⌈exp (1024 * cubicEnergyError + 2048 * (WeightedMertens.boundConstant + 1) + 1)⌉₊

lemma sevenEighthCutoffScale_ge : 1024 ≤ sevenEighthCutoffScale := by unfold sevenEighthCutoffScale; omega

lemma sevenEighthCutoffScale_log : 1024 * cubicEnergyError + 2048 * (WeightedMertens.boundConstant + 1) + 1 ≤ log (sevenEighthCutoffScale : ℝ) := by
  have he := Nat.le_ceil (exp (1024 * cubicEnergyError + 2048 * (WeightedMertens.boundConstant + 1) + 1))
  have hd : exp (1024 * cubicEnergyError + 2048 * (WeightedMertens.boundConstant + 1) + 1) ≤ (sevenEighthCutoffScale : ℝ) := by
    unfold sevenEighthCutoffScale
    push_cast
    linarith
  have hh := log_le_log (exp_pos _) hd
  simpa only [log_exp] using hh

noncomputable def sevenEighthBoundConstant : ℝ :=
  1024 * exp 4 * (sevenEighthCutoffScale : ℝ) ^ 2 * (sevenEighthCutoffScale + 2)

lemma sevenEighthBoundConstant_pos : 0 < sevenEighthBoundConstant := by
  unfold sevenEighthBoundConstant
  have hh : (0 : ℝ) < sevenEighthCutoffScale := by exact_mod_cast (show 0 < sevenEighthCutoffScale by have := sevenEighthCutoffScale_ge; omega)
  positivity

/-- Every configuration of at most t^8 prime classes has a survivor in
intervals longer than one absolute constant times t^22. -/
theorem prime_survivor_seven_eighths (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℕ) (ht : 0 < t) (hcard : P.card ≤ t ^ 8) (r : ℕ → ℕ) (m : ℕ)
    (hm : sevenEighthBoundConstant * (t : ℝ) ^ 22 < m) :
    ∃ j < m, ∀ p ∈ P, ¬j ≡ r p [MOD p] := by
  classical
  let D := sevenEighthCutoffScale
  let R := D * t ^ 7
  let S := P ∪ (R + 1).primesBelow
  let p : S → ℕ := Subtype.val
  let L := log (R : ℝ)
  let q : S → ℝ := fun i => 1 / (p i : ℝ)
  let c : Finset S → ℝ := fun Q => weight q Q * softProfile (fun i => log (p i : ℝ)) L Q
  have hD1024 : 1024 ≤ D := sevenEighthCutoffScale_ge
  have hDpos : 0 < D := by omega
  have ht7 : 1 ≤ t ^ 7 := one_le_pow₀ ht
  have ht8 : 1 ≤ t ^ 8 := one_le_pow₀ ht
  have h78 : t ^ 7 ≤ t ^ 8 := pow_le_pow_right₀ ht (by omega)
  have hDR : D ≤ R := by dsimp [R]; nlinarith
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hS : ∀ a ∈ S, a.Prime := by
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact hP a ha
    · exact (WeightedMertens.mem_primes.mp ha).1
  have hp : ∀ i, (p i).Prime := fun i => hS i.val i.property
  have hinj : Function.Injective p := Subtype.val_injective
  have hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a := by
    intro a ha haR
    exact ⟨⟨a, mem_union_right _ (WeightedMertens.mem_primes.mpr ⟨ha, haR⟩)⟩, rfl⟩
  have hlog : 1024 * cubicEnergyError + 2048 * (WeightedMertens.boundConstant + 1) + 1 ≤ L := by
    have hd0 : (0 : ℝ) < D := by exact_mod_cast hDpos
    exact sevenEighthCutoffScale_log.trans (log_le_log hd0 (by exact_mod_cast hDR))
  have hL : 1 ≤ L := by linarith [cubicEnergyError_pos, WeightedMertens.boundConstant_pos]
  have hlarge : 1024 * cubicEnergyError ≤ L := by linarith [WeightedMertens.boundConstant_pos]
  have htailset : S.filter (fun a => R < a) = P.filter (fun a => R < a) := by
    ext a
    simp only [S, mem_filter, mem_union]
    constructor
    · rintro ⟨ha | ha, hRa⟩
      · exact ⟨ha, hRa⟩
      · have := (WeightedMertens.mem_primes.mp ha).2
        omega
    · rintro ⟨ha, hRa⟩
      exact ⟨Or.inl ha, hRa⟩
  have htail : (∑ i ∈ (univ : Finset S).filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 1 / 7 := by
    have he : (∑ i ∈ (univ : Finset S).filter (fun i => R < p i), 1 / (p i : ℝ)) =
        ∑ a ∈ P.filter (fun a => R < a), 1 / (a : ℝ) := by
      rw [← htailset]
      simp only [sum_filter]
      exact sum_coe_sort S (fun a : ℕ => if R < a then 1 / (a : ℝ) else 0)
    rw [he]
    have hlogD : 2048 * (WeightedMertens.boundConstant + 1) ≤ log (D : ℝ) := by
      have hh := sevenEighthCutoffScale_log
      change 1024 * cubicEnergyError + 2048 * (WeightedMertens.boundConstant + 1) + 1 ≤ log (D : ℝ) at hh
      linarith [cubicEnergyError_pos]
    exact WeightedMertens.tail_seven_eighths P hP t D ht hD1024 hlogD hcard
  have henergy : L ^ 3 / 1024 ≤ kernelEnergy q c :=
    prime_soft_energy_seventh p hp hinj R hRpos hfull hL hlarge htail
  have henergypos : 0 < kernelEnergy q c :=
    lt_of_lt_of_le (by
      have : 0 < L := by linarith
      positivity) henergy
  have hcost : kernelCost q c ≤ L * exp 2 * (R : ℝ) := by
    have hh := prime_soft_cost_le p hp hinj L (by linarith)
    rw [exp_log hR0] at hh
    exact hh
  have hcost0 : 0 ≤ kernelCost q c := sum_nonneg (fun _ _ => abs_nonneg _)
  have hcostsq : kernelCost q c ^ 2 ≤ exp 4 * (R : ℝ) ^ 2 * L ^ 2 := by
    have hh := (sq_le_sq₀ hcost0 (by positivity : 0 ≤ L * exp 2 * (R : ℝ))).mpr hcost
    have he : (L * exp 2 * (R : ℝ)) ^ 2 = exp 4 * (R : ℝ) ^ 2 * L ^ 2 := by
      rw [mul_pow, mul_pow, ← exp_nat_mul]
      norm_num
      ring
    exact hh.trans_eq he
  have hcostenergy : kernelCost q c ^ 2 ≤ 1024 * exp 4 * (R : ℝ) ^ 2 * kernelEnergy q c := by
    have hLpow : L ^ 2 ≤ L ^ 3 := by nlinarith [sq_nonneg (L - 1)]
    have h1 := mul_le_mul_of_nonneg_left hLpow (show 0 ≤ exp 4 * (R : ℝ) ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 1024 * exp 4 * (R : ℝ) ^ 2 by positivity)
    nlinarith only [hcostsq, h1, h2]
  have hsmallcard : (R + 1).primesBelow.card ≤ R := by
    have hsub : (R + 1).primesBelow ⊆ Icc 1 R := by
      intro a ha
      obtain ⟨hap, haR⟩ := WeightedMertens.mem_primes.mp ha
      exact mem_Icc.mpr ⟨hap.pos, haR⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  have hScard : S.card ≤ t ^ 8 + R :=
    (card_union_le P (R + 1).primesBelow).trans (Nat.add_le_add hcard hsmallcard)
  have hScardR : (Fintype.card S + 1 : ℝ) ≤ ((D : ℝ) + 2) * (t : ℝ) ^ 8 := by
    have hh : S.card + 1 ≤ (D + 2) * t ^ 8 := by
      dsimp [R] at hScard
      have hm := Nat.mul_le_mul_left D h78
      nlinarith
    simpa only [Fintype.card_coe, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
      using (Nat.cast_le (α := ℝ)).mpr hh
  have hkernel : (Fintype.card S + 1 : ℝ) * kernelCost q c ^ 2 ≤
      sevenEighthBoundConstant * (t : ℝ) ^ 22 * kernelEnergy q c := by
    calc
      _ ≤ (((D : ℝ) + 2) * (t : ℝ) ^ 8) * kernelCost q c ^ 2 :=
        mul_le_mul_of_nonneg_right hScardR (sq_nonneg _)
      _ ≤ (((D : ℝ) + 2) * (t : ℝ) ^ 8) *
          (1024 * exp 4 * (R : ℝ) ^ 2 * kernelEnergy q c) :=
        mul_le_mul_of_nonneg_left hcostenergy (by positivity)
      _ = _ := by
        dsimp [sevenEighthBoundConstant, R, D]
        push_cast
        ring
  obtain ⟨j, hj, havoid⟩ := survivor_of_kernelEnergy q (fun i => (prime_marginals p hp i).1.ne') c m
    (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hinj r m)
    (hkernel.trans_lt (mul_lt_mul_of_pos_right hm henergypos))
  refine ⟨j, hj, ?_⟩
  intro a ha
  have hh := havoid ⟨a, mem_union_left _ ha⟩
  simpa only [p, decide_eq_false_iff_not] using hh

#print axioms prime_survivor_seven_eighths
end Erdos970.FiniteSelberg
