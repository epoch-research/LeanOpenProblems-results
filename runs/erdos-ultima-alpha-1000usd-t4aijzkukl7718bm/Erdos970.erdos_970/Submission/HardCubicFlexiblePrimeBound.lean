import Submission.HardCubicPrimeBound
import Submission.HardCubicFlexibleTail

/-! A flexible power-cutoff version of the logarithmically improved hard-cubic
sieve bound. The reciprocal-ratio hypothesis remains explicit. -/
namespace Erdos970.FiniteSelberg
open Finset Real

theorem prime_survivor_power_ratio_log (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (e f : ℕ) (hE : 0 < e) (hEF : e ≤ f)
    (hRatio : log ((f : ℝ) / e) ≤ 287697 / 1000000)
    (t : ℕ) (ht : 0 < t) (hcard : P.card ≤ t ^ f) (r : ℕ → ℕ) (m : ℕ)
    (hm : hardCubicBoundConstant * (t : ℝ) ^ (f + 2 * e) <
      (m : ℝ) * log ((hardCubicCutoffScale * t ^ e : ℕ) : ℝ)) :
    ∃ j < m, ∀ p ∈ P, ¬j ≡ r p [MOD p] := by
  classical
  let D := hardCubicCutoffScale
  let R := D * t ^ e
  let S := P ∪ (R + 1).primesBelow
  let p : S → ℕ := Subtype.val
  let L := log (R : ℝ)
  let q : S → ℝ := fun i => 1 / (p i : ℝ)
  let c : Finset S → ℝ := fun Q => weight q Q * primeHardCubicProfile p L Q
  have hD1000000 : 1000000 ≤ D := hardCubicCutoffScale_ge
  have hDpos : 0 < D := by omega
  have ht13 : 1 ≤ t ^ e := one_le_pow₀ ht
  have ht16 : 1 ≤ t ^ f := one_le_pow₀ ht
  have h1316 : t ^ e ≤ t ^ f := pow_le_pow_right₀ ht (by omega)
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
  have hlog : hardCubicEnergyThreshold + 2000000 * (WeightedMertens.boundConstant + 1) + 1 ≤ L := by
    have hd0 : (0 : ℝ) < D := by exact_mod_cast hDpos
    exact hardCubicCutoffScale_log.trans (log_le_log hd0 (by exact_mod_cast hDR))
  have hL : 1 ≤ L := by linarith [hardCubicEnergyThreshold_pos, WeightedMertens.boundConstant_pos]
  have hlarge : hardCubicEnergyThreshold ≤ L := by linarith [WeightedMertens.boundConstant_pos]
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
  have htail : (∑ i ∈ (univ : Finset S).filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 2877 / 10000 := by
    have he : (∑ i ∈ (univ : Finset S).filter (fun i => R < p i), 1 / (p i : ℝ)) =
        ∑ a ∈ P.filter (fun a => R < a), 1 / (a : ℝ) := by
      rw [← htailset]
      simp only [sum_filter]
      exact sum_coe_sort S (fun a : ℕ => if R < a then 1 / (a : ℝ) else 0)
    rw [he]
    have hlogD : 2000000 * (WeightedMertens.boundConstant + 1) ≤ log (D : ℝ) := by
      have hh := hardCubicCutoffScale_log
      change hardCubicEnergyThreshold + 2000000 * (WeightedMertens.boundConstant + 1) + 1 ≤ log (D : ℝ) at hh
      linarith [hardCubicEnergyThreshold_pos]
    exact WeightedMertens.tail_power_ratio P hP e f t D hE hEF ht hD1000000 hlogD hRatio hcard
  have henergy : L ^ 7 ≤ kernelEnergy q c :=
    prime_hardCubic_energy p hp hinj R hRpos hfull hlarge htail
  have henergypos : 0 < kernelEnergy q c :=
    lt_of_lt_of_le (by
      have : 0 < L := by linarith
      positivity) henergy
  have hcost : kernelCost q c ≤ 10000 * L ^ 3 * exp 2 * (R : ℝ) :=
    prime_hardCubic_cost_le p hp hinj R hRpos
  have hcost0 : 0 ≤ kernelCost q c := sum_nonneg (fun _ _ => abs_nonneg _)
  have hcostsq : kernelCost q c ^ 2 ≤ 100000000 * exp 4 * (R : ℝ) ^ 2 * L ^ 6 := by
    have hh := (sq_le_sq₀ hcost0 (by positivity : 0 ≤ 10000 * L ^ 3 * exp 2 * (R : ℝ))).mpr hcost
    have he : (10000 * L ^ 3 * exp 2 * (R : ℝ)) ^ 2 =
        100000000 * exp 4 * (R : ℝ) ^ 2 * L ^ 6 := by
      have hex : (exp (2 : ℝ)) ^ 2 = exp 4 := by rw [← exp_nat_mul]; norm_num
      calc
        _ = 100000000 * (exp 2) ^ 2 * (R : ℝ) ^ 2 * L ^ 6 := by ring
        _ = _ := by rw [hex]
    exact hh.trans_eq he
  have hLpos : 0 < L := by linarith only [hL]
  have hcostenergy : L * kernelCost q c ^ 2 ≤
      100000000 * exp 4 * (R : ℝ) ^ 2 * kernelEnergy q c := by
    have h1 := mul_le_mul_of_nonneg_left hcostsq hLpos.le
    have h2 := mul_le_mul_of_nonneg_left henergy
      (show 0 ≤ 100000000 * exp 4 * (R : ℝ) ^ 2 by positivity)
    nlinarith only [h1, h2]
  have hsmallcard : (R + 1).primesBelow.card ≤ R := by
    have hsub : (R + 1).primesBelow ⊆ Icc 1 R := by
      intro a ha
      obtain ⟨hap, haR⟩ := WeightedMertens.mem_primes.mp ha
      exact mem_Icc.mpr ⟨hap.pos, haR⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  have hScard : S.card ≤ t ^ f + R :=
    (card_union_le P (R + 1).primesBelow).trans (Nat.add_le_add hcard hsmallcard)
  have hScardR : (Fintype.card S + 1 : ℝ) ≤ ((D : ℝ) + 2) * (t : ℝ) ^ f := by
    have hh : S.card + 1 ≤ (D + 2) * t ^ f := by
      dsimp [R] at hScard
      have hm := Nat.mul_le_mul_left D h1316
      nlinarith
    simpa only [Fintype.card_coe, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
      using (Nat.cast_le (α := ℝ)).mpr hh
  have hkernel : L * ((Fintype.card S + 1 : ℝ) * kernelCost q c ^ 2) ≤
      hardCubicBoundConstant * (t : ℝ) ^ (f + 2 * e) * kernelEnergy q c := by
    calc
      _ = (Fintype.card S + 1 : ℝ) * (L * kernelCost q c ^ 2) := by ring
      _ ≤ (((D : ℝ) + 2) * (t : ℝ) ^ f) * (L * kernelCost q c ^ 2) :=
        mul_le_mul_of_nonneg_right hScardR (mul_nonneg hLpos.le (sq_nonneg _))
      _ ≤ (((D : ℝ) + 2) * (t : ℝ) ^ f) *
          (100000000 * exp 4 * (R : ℝ) ^ 2 * kernelEnergy q c) :=
        mul_le_mul_of_nonneg_left hcostenergy (by positivity)
      _ = _ := by
        dsimp [hardCubicBoundConstant, R, D]
        push_cast
        have hepow : (t : ℝ) ^ (f + 2 * e) = (t : ℝ) ^ f * ((t : ℝ) ^ e) ^ 2 := by
          rw [pow_add, Nat.mul_comm 2 e, pow_mul]
        rw [hepow]
        ring
  have hmain : (Fintype.card S + 1 : ℝ) * kernelCost q c ^ 2 <
      (m : ℝ) * kernelEnergy q c := by
    have hh := hkernel.trans_lt (mul_lt_mul_of_pos_right hm henergypos)
    change L * ((Fintype.card S + 1 : ℝ) * kernelCost q c ^ 2) <
      ((m : ℝ) * L) * kernelEnergy q c at hh
    have he : ((m : ℝ) * L) * kernelEnergy q c = L * ((m : ℝ) * kernelEnergy q c) := by ring
    rw [he] at hh
    exact (mul_lt_mul_iff_right₀ hLpos).mp hh
  obtain ⟨j, hj, havoid⟩ := survivor_of_kernelEnergy q (fun i => (prime_marginals p hp i).1.ne') c m
    (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hinj r m)
    hmain
  refine ⟨j, hj, ?_⟩
  intro a ha
  have hh := havoid ⟨a, mem_union_left _ ha⟩
  simpa only [p, decide_eq_false_iff_not] using hh


#print axioms prime_survivor_power_ratio_log
end Erdos970.FiniteSelberg
