import Submission.PrimeRowResidueInjection

/-! The prime-row residue injection, restricted to unit cofactor residues.
These are upper bounds only; the prime-pair conjecture remains open here. -/
namespace Erdos972PrimeRowUnitInjection

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972SelbergLowerTest
open Erdos972PrimeOutputGcdDeterminant Erdos972PrimeRowResidueInjection
set_option autoImplicit false
set_option maxHeartbeats 1500000

lemma cofactorResidue_isUnit {α : ℝ} {d M p : ℕ}
    (hp : p.Prime) (hM : 0 < M) (hMp : M < p)
    (hcop : (floorMul α p / d).Coprime M) :
    IsUnit (cofactorResidue α d M p) := by
  have hpunit : IsUnit (p : ZMod M) := ZMod.isUnit_prime_of_not_dvd hp (by
    intro h
    exact (not_le_of_gt hMp) (Nat.le_of_dvd hM h))
  have hpinv : IsUnit ((p : ZMod M)⁻¹) :=
    IsUnit.of_mul_eq_one (p : ZMod M) (ZMod.inv_mul_of_unit _ hpunit)
  exact ((ZMod.isUnit_iff_coprime _ _).mpr hcop).mul hpinv

/-- Restricting the cofactor to integers coprime to the modulus reduces the
row multiplicity bound from M to Euler's totient of M. -/
theorem coprime_cofactor_row_card_le_totient {α : ℝ} (hα : 1 ≤ α) {N d M : ℕ}
    (hd : α < (d : ℝ)) (hM : 0 < M) (hN : N ≤ d*M) :
    ((Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p ∧
      (floorMul α p / d).Coprime M)).card ≤ M.totient := by
  classical
  letI : NeZero M := ⟨hM.ne'⟩
  let S := (Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p ∧
    (floorMul α p / d).Coprime M)
  have hunit (p : S) : IsUnit (cofactorResidue α d M p) := by
    have hp : (p : ℕ) ∈ (Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p ∧
      (floorMul α p / d).Coprime M) := p.property
    obtain ⟨hpI, hpp, hdp, hcop⟩ := mem_filter.mp hp
    exact cofactorResidue_isUnit hpp hM (mem_Ioc.mp hpI).1 hcop
  let f : S → (ZMod M)ˣ := fun p => (hunit p).unit
  have hinj : Function.Injective f := by
    intro p q he
    have hp : (p : ℕ) ∈ (Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p ∧
      (floorMul α p / d).Coprime M) := p.property
    have hq : (q : ℕ) ∈ (Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p ∧
      (floorMul α p / d).Coprime M) := q.property
    obtain ⟨hpI, hpp, hdp, hcopP⟩ := mem_filter.mp hp
    obtain ⟨hqI, hqp, hdq, hcopQ⟩ := mem_filter.mp hq
    have hr : cofactorResidue α d M p = cofactorResidue α d M q := by
      have hh := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) he
      simpa only [f, IsUnit.unit_spec] using hh
    apply Subtype.ext
    exact cofactorResidue_injective hα hd hM hN hpp hqp
      (mem_Ioc.mp hpI).1 (mem_Ioc.mp hqI).1
      (mem_Ioc.mp hpI).2 (mem_Ioc.mp hqI).2 hdp hdq hr
  have hh := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, ZMod.card_units_eq_totient] using hh

/-- In particular, outputs coprime to M satisfy the totient bound. -/
theorem coprime_output_row_card_le_totient {α : ℝ} (hα : 1 ≤ α) {N d M : ℕ}
    (hd : α < (d : ℝ)) (hM : 0 < M) (hN : N ≤ d*M) :
    ((Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p ∧
      (floorMul α p).Coprime M)).card ≤ M.totient := by
  classical
  apply (card_le_card ?_).trans (coprime_cofactor_row_card_le_totient hα hd hM hN)
  intro p hp
  obtain ⟨hpI, hpp, hdp, hcop⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpI, hpp, hdp, Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hdp) hcop⟩

/-- For odd prime inputs and odd outputs, the large-divisor row contains at
most one input already at the threshold 2d≥N. -/
theorem odd_output_row_card_le_one {α : ℝ} (hα : 1 ≤ α) {N d : ℕ}
    (hd : α < (d : ℝ)) (hN : N ≤ 2*d) :
    ((Ioc 2 N).filter (fun p => p.Prime ∧ d ∣ floorMul α p ∧
      Odd (floorMul α p))).card ≤ 1 := by
  have hh := coprime_output_row_card_le_totient hα hd (M := 2) (by decide)
    (by simpa [mul_comm] using hN)
  simpa only [Nat.coprime_two_right, Nat.totient_two] using hh

/-- If two distinct odd prime inputs have odd outputs, any common output
divisor exceeding the slope is less than half the larger input. -/
theorem twice_common_odd_output_divisor_lt_max {α : ℝ} (hα : 1 ≤ α)
    {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : 2 < p) (hq2 : 2 < q)
    (hpq : p ≠ q) (hd : α < (d : ℝ))
    (hdp : d ∣ floorMul α p) (hdq : d ∣ floorMul α q)
    (hop : Odd (floorMul α p)) (hoq : Odd (floorMul α q)) :
    2*d < max p q := by
  classical
  by_contra hnot
  have hh := odd_output_row_card_le_one hα hd (le_of_not_gt hnot)
  have hs : ({p, q} : Finset ℕ) ⊆ (Ioc 2 (max p q)).filter
      (fun r => r.Prime ∧ d ∣ floorMul α r ∧ Odd (floorMul α r)) := by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp2, le_max_left _ _⟩, hp, hdp, hop⟩
    · have he := mem_singleton.mp hr
      subst r
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hq2, le_max_right _ _⟩, hq, hdq, hoq⟩
  have hc := (card_le_card hs).trans hh
  simp only [card_pair hpq] at hc
  omega

#print axioms coprime_cofactor_row_card_le_totient
#print axioms coprime_output_row_card_le_totient
#print axioms odd_output_row_card_le_one
#print axioms twice_common_odd_output_divisor_lt_max
end Erdos972PrimeRowUnitInjection
