import Submission.HardCubicPrimeBound
import Submission.HardCubicCountKernel
import Submission.LowCountCylinder

/-! A quantitative survivor-count version of the unconditional 5/2 bound.
Above its fixed 5/2 scale, every phase has a positive proportion of m/log k
survivors. The quadratic conjecture is not asserted. -/
namespace Erdos970.FiniteSelberg
open Finset Real

/-- Uniform lower count above the hard-cubic cardinality envelope. -/
theorem prime_count_three_quarters (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℕ) (ht : 0 < t) (hcard : P.card ≤ t ^ 4) (r : ℕ → ℕ) (m : ℕ)
    (hm : 2 * hardCubicBoundConstant * (t : ℝ) ^ 10 ≤ m) :
    (m : ℝ) ≤ 800000000 * log ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ) *
      (((range m).filter (fun j => ∀ p ∈ P, ¬j ≡ r p [MOD p])).card : ℝ) := by
  classical
  let D := hardCubicCutoffScale
  let R := D * t ^ 3
  let S := P ∪ (R + 1).primesBelow
  let p : S → ℕ := Subtype.val
  let L := log (R : ℝ)
  have hD1000000 : 1000000 ≤ D := hardCubicCutoffScale_ge
  have hDpos : 0 < D := by omega
  have ht13 : 1 ≤ t ^ 3 := one_le_pow₀ ht
  have ht16 : 1 ≤ t ^ 4 := one_le_pow₀ ht
  have h1316 : t ^ 3 ≤ t ^ 4 := pow_le_pow_right₀ ht (by omega)
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
    exact WeightedMertens.tail_three_quarters P hP t D ht hD1000000 hlogD hcard
  have hsmallcard : (R + 1).primesBelow.card ≤ R := by
    have hsub : (R + 1).primesBelow ⊆ Icc 1 R := by
      intro a ha
      obtain ⟨hap, haR⟩ := WeightedMertens.mem_primes.mp ha
      exact mem_Icc.mpr ⟨hap.pos, haR⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  have hScard : S.card ≤ t ^ 4 + R :=
    (card_union_le P (R + 1).primesBelow).trans (Nat.add_le_add hcard hsmallcard)
  have hScardR : (Fintype.card S + 1 : ℝ) ≤ ((D : ℝ) + 2) * (t : ℝ) ^ 4 := by
    have hh : S.card + 1 ≤ (D + 2) * t ^ 4 := by
      dsimp [R] at hScard
      have hm := Nat.mul_le_mul_left D h1316
      nlinarith
    simpa only [Fintype.card_coe, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
      using (Nat.cast_le (α := ℝ)).mpr hh
  have hbudget : 2 * 100000000 * exp 4 * (Fintype.card S + 1 : ℝ) * (R : ℝ) ^ 2 ≤
      (m : ℝ) * log R := by
    calc
      _ ≤ 2 * 100000000 * exp 4 * (((D : ℝ) + 2) * (t : ℝ) ^ 4) * (R : ℝ) ^ 2 := by
        gcongr
      _ = 2 * hardCubicBoundConstant * (t : ℝ) ^ 10 := by
        dsimp [hardCubicBoundConstant, R, D]
        push_cast
        ring
      _ ≤ m := hm
      _ ≤ (m : ℝ) * log R := by
        have hh := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg m)
        simpa only [mul_one] using hh
  have hlo := prime_hardCubic_count p hp hinj R hRpos hfull hlarge htail r m hbudget
  have hsub : (range m).filter (fun j => ∀ i : S, ¬j ≡ r (p i) [MOD p i]) ⊆
      (range m).filter (fun j => ∀ a ∈ P, ¬j ≡ r a [MOD a]) := by
    intro j hj
    obtain ⟨hjm, havoid⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨hjm, fun a ha => havoid ⟨a, mem_union_left _ ha⟩⟩
  have hc : (((range m).filter (fun j => ∀ i : S, ¬j ≡ r (p i) [MOD p i])).card : ℝ) ≤
      (((range m).filter (fun j => ∀ a ∈ P, ¬j ≡ r a [MOD a])).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hlo.trans (mul_le_mul_of_nonneg_left hc (by have := log_natCast_nonneg R; positivity))

end Erdos970.FiniteSelberg
namespace Erdos970.GapAverages
open Finset Real FiniteSelberg

lemma phase_count_card (P : Finset ℕ) (m : ℕ) (r : Phase P) :
    (((range m).filter (fun j => ∀ p ∈ P, ¬j ≡ phaseResidues P r p [MOD p])).card : ℝ) =
      intervalCount P m r := by
  rw [← CoverFibers.phaseSurvivors_card]
  congr 2
  ext j
  simp only [mem_filter, CoverFibers.phaseSurvivors]
  have he : (∀ p ∈ P, ¬j ≡ phaseResidues P r p [MOD p]) ↔
      ∀ p : P, j % p.val ≠ (r p).val := by
    constructor
    · intro h p hp
      apply h p.val p.property
      change j % p.val = phaseResidues P r p.val % p.val
      rw [phaseResidues_mem, Nat.mod_eq_of_lt (r p).isLt]
      exact hp
    · intro h p hp he
      let p' : P := ⟨p, hp⟩
      apply h p'
      change j % p = phaseResidues P r p % p at he
      have hr : phaseResidues P r p = (r p').val := phaseResidues_mem P r p'
      have hlt : (r p').val < p := (r p').isLt
      simpa only [hr, Nat.mod_eq_of_lt hlt] using he
  simp only [mem_filter, he]

/-- Phase form of the same unconditional large-scale lower count. -/
theorem phase_count_three_quarters (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℕ) (ht : 0 < t) (hcard : P.card ≤ t ^ 4) (m : ℕ)
    (hm : 2 * hardCubicBoundConstant * (t : ℝ) ^ 10 ≤ m) (r : Phase P) :
    (m : ℝ) ≤ 800000000 * log ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ) * intervalCount P m r := by
  have hh := prime_count_three_quarters P hP t ht hcard (phaseResidues P r) m hm
  rwa [phase_count_card] at hh

#print axioms phase_count_three_quarters
end Erdos970.GapAverages
