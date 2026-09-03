import Submission.SelbergQuadraticCost
import Submission.ThirteenSixteenthTail

/-! A prime-class survivor bound at cardinality t^16 and length O(t^42).
This gives exponent 21/8, not the conjectured exponent two. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def thirteenSixteenthCutoffScale : ℕ :=
  65536 + ⌈exp (512 * quadraticEnergyError + 131072 * (WeightedMertens.boundConstant + 1) + 1)⌉₊

lemma thirteenSixteenthCutoffScale_ge : 65536 ≤ thirteenSixteenthCutoffScale := by unfold thirteenSixteenthCutoffScale; omega

lemma thirteenSixteenthCutoffScale_log : 512 * quadraticEnergyError + 131072 * (WeightedMertens.boundConstant + 1) + 1 ≤ log (thirteenSixteenthCutoffScale : ℝ) := by
  have he := Nat.le_ceil (exp (512 * quadraticEnergyError + 131072 * (WeightedMertens.boundConstant + 1) + 1))
  have hd : exp (512 * quadraticEnergyError + 131072 * (WeightedMertens.boundConstant + 1) + 1) ≤ (thirteenSixteenthCutoffScale : ℝ) := by
    unfold thirteenSixteenthCutoffScale
    push_cast
    linarith
  have hh := log_le_log (exp_pos _) hd
  simpa only [log_exp] using hh

noncomputable def thirteenSixteenthBoundConstant : ℝ :=
  512 * exp 4 * (thirteenSixteenthCutoffScale : ℝ) ^ 2 * (thirteenSixteenthCutoffScale + 2)

lemma thirteenSixteenthBoundConstant_pos : 0 < thirteenSixteenthBoundConstant := by
  unfold thirteenSixteenthBoundConstant
  have hh : (0 : ℝ) < thirteenSixteenthCutoffScale := by exact_mod_cast (show 0 < thirteenSixteenthCutoffScale by have := thirteenSixteenthCutoffScale_ge; omega)
  positivity

/-- Every configuration of at most t^16 prime classes has a survivor in
intervals longer than one absolute constant times t^42. -/
theorem prime_survivor_thirteen_sixteenths (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℕ) (ht : 0 < t) (hcard : P.card ≤ t ^ 16) (r : ℕ → ℕ) (m : ℕ)
    (hm : thirteenSixteenthBoundConstant * (t : ℝ) ^ 42 < m) :
    ∃ j < m, ∀ p ∈ P, ¬j ≡ r p [MOD p] := by
  classical
  let D := thirteenSixteenthCutoffScale
  let R := D * t ^ 13
  let S := P ∪ (R + 1).primesBelow
  let p : S → ℕ := Subtype.val
  let L := log (R : ℝ)
  let q : S → ℝ := fun i => 1 / (p i : ℝ)
  let c : Finset S → ℝ := fun Q => weight q Q * primeQuadraticProfile p L Q
  have hD65536 : 65536 ≤ D := thirteenSixteenthCutoffScale_ge
  have hDpos : 0 < D := by omega
  have ht13 : 1 ≤ t ^ 13 := one_le_pow₀ ht
  have ht16 : 1 ≤ t ^ 16 := one_le_pow₀ ht
  have h1316 : t ^ 13 ≤ t ^ 16 := pow_le_pow_right₀ ht (by omega)
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
  have hlog : 512 * quadraticEnergyError + 131072 * (WeightedMertens.boundConstant + 1) + 1 ≤ L := by
    have hd0 : (0 : ℝ) < D := by exact_mod_cast hDpos
    exact thirteenSixteenthCutoffScale_log.trans (log_le_log hd0 (by exact_mod_cast hDR))
  have hL : 1 ≤ L := by linarith [quadraticEnergyError_pos, WeightedMertens.boundConstant_pos]
  have hlarge : 512 * quadraticEnergyError ≤ L := by linarith [WeightedMertens.boundConstant_pos]
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
  have htail : (∑ i ∈ (univ : Finset S).filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 5 / 24 := by
    have he : (∑ i ∈ (univ : Finset S).filter (fun i => R < p i), 1 / (p i : ℝ)) =
        ∑ a ∈ P.filter (fun a => R < a), 1 / (a : ℝ) := by
      rw [← htailset]
      simp only [sum_filter]
      exact sum_coe_sort S (fun a : ℕ => if R < a then 1 / (a : ℝ) else 0)
    rw [he]
    have hlogD : 131072 * (WeightedMertens.boundConstant + 1) ≤ log (D : ℝ) := by
      have hh := thirteenSixteenthCutoffScale_log
      change 512 * quadraticEnergyError + 131072 * (WeightedMertens.boundConstant + 1) + 1 ≤ log (D : ℝ) at hh
      linarith [quadraticEnergyError_pos]
    exact WeightedMertens.tail_thirteen_sixteenths P hP t D ht hD65536 hlogD hcard
  have henergy : L ^ 5 / 512 ≤ kernelEnergy q c :=
    prime_quadratic_energy p hp hinj R hRpos hfull hL hlarge htail
  have henergypos : 0 < kernelEnergy q c :=
    lt_of_lt_of_le (by
      have : 0 < L := by linarith
      positivity) henergy
  have hcost : kernelCost q c ≤ L ^ 2 * exp 2 * (R : ℝ) :=
    prime_quadratic_cost_le p hp hinj R hRpos
  have hcost0 : 0 ≤ kernelCost q c := sum_nonneg (fun _ _ => abs_nonneg _)
  have hcostsq : kernelCost q c ^ 2 ≤ exp 4 * (R : ℝ) ^ 2 * L ^ 4 := by
    have hh := (sq_le_sq₀ hcost0 (by positivity : 0 ≤ L ^ 2 * exp 2 * (R : ℝ))).mpr hcost
    have he : (L ^ 2 * exp 2 * (R : ℝ)) ^ 2 = exp 4 * (R : ℝ) ^ 2 * L ^ 4 := by
      rw [mul_pow, mul_pow, ← exp_nat_mul]
      norm_num
      ring
    exact hh.trans_eq he
  have hcostenergy : kernelCost q c ^ 2 ≤ 512 * exp 4 * (R : ℝ) ^ 2 * kernelEnergy q c := by
    have hLpow : L ^ 4 ≤ L ^ 5 := by
      have hh := mul_le_mul_of_nonneg_right hL (pow_nonneg (show 0 ≤ L by linarith) 4)
      nlinarith only [hh]
    have h1 := mul_le_mul_of_nonneg_left hLpow (show 0 ≤ exp 4 * (R : ℝ) ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 512 * exp 4 * (R : ℝ) ^ 2 by positivity)
    nlinarith only [hcostsq, h1, h2]
  have hsmallcard : (R + 1).primesBelow.card ≤ R := by
    have hsub : (R + 1).primesBelow ⊆ Icc 1 R := by
      intro a ha
      obtain ⟨hap, haR⟩ := WeightedMertens.mem_primes.mp ha
      exact mem_Icc.mpr ⟨hap.pos, haR⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  have hScard : S.card ≤ t ^ 16 + R :=
    (card_union_le P (R + 1).primesBelow).trans (Nat.add_le_add hcard hsmallcard)
  have hScardR : (Fintype.card S + 1 : ℝ) ≤ ((D : ℝ) + 2) * (t : ℝ) ^ 16 := by
    have hh : S.card + 1 ≤ (D + 2) * t ^ 16 := by
      dsimp [R] at hScard
      have hm := Nat.mul_le_mul_left D h1316
      nlinarith
    simpa only [Fintype.card_coe, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
      using (Nat.cast_le (α := ℝ)).mpr hh
  have hkernel : (Fintype.card S + 1 : ℝ) * kernelCost q c ^ 2 ≤
      thirteenSixteenthBoundConstant * (t : ℝ) ^ 42 * kernelEnergy q c := by
    calc
      _ ≤ (((D : ℝ) + 2) * (t : ℝ) ^ 16) * kernelCost q c ^ 2 :=
        mul_le_mul_of_nonneg_right hScardR (sq_nonneg _)
      _ ≤ (((D : ℝ) + 2) * (t : ℝ) ^ 16) *
          (512 * exp 4 * (R : ℝ) ^ 2 * kernelEnergy q c) :=
        mul_le_mul_of_nonneg_left hcostenergy (by positivity)
      _ = _ := by
        dsimp [thirteenSixteenthBoundConstant, R, D]
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

#print axioms prime_survivor_thirteen_sixteenths
end Erdos970.FiniteSelberg
