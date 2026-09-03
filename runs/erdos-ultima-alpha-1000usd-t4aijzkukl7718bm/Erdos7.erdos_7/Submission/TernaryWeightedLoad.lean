import Submission.WeightedExceptionArithmetic

/-!
# Necessary weighted loads on every ternary fiber

A full odd covering supplies, on each ternary fiber, more than one half of
3-free exceptional weight over its unchanged distinct no-3 base. This is a
necessary condition, not a proof of nonexistence of an odd covering.
-/
namespace Erdos7TernaryWeightedLoad
open scoped BigOperators
open Erdos7WeightedExceptionArithmetic Erdos7Reduction
set_option maxHeartbeats 4000000

/-- Invert any ternary power modulo a modulus prime to3. -/
lemma affine_power_residue (m E : ℕ) (hm : ¬ 3 ∣ m) (a r : ℤ) :
    ∃ b : ℤ, ∀ x : ℤ,
      (m : ℤ) ∣ ((3^E : ℕ) : ℤ)*x+r-a ↔ (m : ℤ) ∣ x-b := by
  have hcp : IsCoprime ((3^E : ℕ) : ℤ) (m : ℤ) :=
    ((Nat.prime_three.coprime_iff_not_dvd.mpr hm).pow_left E).isCoprime
  obtain ⟨u,v,hu⟩ := hcp
  refine ⟨u*(a-r),fun x => ⟨?_,?_⟩⟩
  · rintro ⟨t,ht⟩
    refine ⟨u*t+v*x,?_⟩
    nlinarith [congrArg (fun z : ℤ => z*x) hu,
      congrArg (fun z : ℤ => u*z) ht]
  · rintro ⟨t,ht⟩
    refine ⟨((3^E : ℕ) : ℤ)*t-v*(a-r),?_⟩
    nlinarith [congrArg (fun z : ℤ => z*(a-r)) hu]

/-- Active exceptions on an entire ternary fiber have weight greater than
one half. Repeated exceptional cofactors are counted with multiplicity. -/
theorem fiber_weight_gt_half {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (e d : J → ℕ) (b : J → ℤ)
    (hd : ∀ j, 0 < d j ∧ Odd (d j)) (hd3 : ∀ j, ¬ 3 ∣ d j)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      ∃ j, ((3^(e j)*d j : ℕ) : ℤ) ∣ x-b j)
    (E : ℕ) (hE : ∀ j, e j ≤ E) (r : ℤ) :
    (1/2 : ℚ) < ∑ j : {j // ((3^(e j) : ℕ) : ℤ) ∣ r-b j}, weight (d j) := by
  classical
  by_contra hsmall
  have hs : (∑ j : {j // ((3^(e j) : ℕ) : ℤ) ∣ r-b j}, weight (d j)) ≤ (1/2 : ℚ) :=
    le_of_not_gt hsmall
  let K := {j : J // ((3^(e j) : ℕ) : ℤ) ∣ r-b j}
  choose a' ha' using fun i => affine_power_residue (m i) E (h3 i) (a i) r
  choose b' hb' using fun j : K => affine_power_residue (d j) E (hd3 j) (b j) r
  apply not_cover_with_weighted_exceptions m a' hinj hm h3
    (fun j : K => d j) b' (fun j => hd j) (fun j => hd3 j) hs
  intro x
  rcases hcover (((3^E : ℕ) : ℤ)*x+r) with ⟨i,hi⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨i,(ha' i x).mp hi⟩
  · have hpow : ((3^(e j) : ℕ) : ℤ) ∣ ((3^E : ℕ) : ℤ)*x :=
      (Int.natCast_dvd_natCast.mpr (pow_dvd_pow 3 (hE j))).trans (dvd_mul_right _ x)
    have hpj : ((3^(e j) : ℕ) : ℤ) ∣ ((3^E : ℕ) : ℤ)*x+r-b j :=
      (Int.natCast_dvd_natCast.mpr (dvd_mul_right (3^(e j)) (d j))).trans hj
    have hactive : ((3^(e j) : ℕ) : ℤ) ∣ r-b j := by
      convert dvd_sub hpj hpow using 1 <;> ring
    have hdj : (d j : ℤ) ∣ ((3^E : ℕ) : ℤ)*x+r-b j :=
      (Int.natCast_dvd_natCast.mpr (dvd_mul_left (d j) (3^(e j)))).trans hj
    exact Or.inr ⟨⟨j,hactive⟩,(hb' ⟨j,hactive⟩ x).mp hdj⟩

/-- The actual 3-free part of a positive odd modulus is positive and odd. -/
lemma cofactor_properties (m : ℕ) (hm : 0 < m) (ho : Odd m) :
    0 < ordCompl[3] m ∧ Odd (ordCompl[3] m) ∧ ¬ 3 ∣ ordCompl[3] m := by
  have he := Nat.ordProj_mul_ordCompl_eq_self m 3
  have hd : ordCompl[3] m ∣ m := by
    calc
      ordCompl[3] m ∣ ordProj[3] m * ordCompl[3] m := dvd_mul_left _ _
      _ = m := he
  refine ⟨?_,ho.of_dvd_nat hd,Nat.not_dvd_ordCompl Nat.prime_three hm.ne'⟩
  exact Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hm.ne' hd)

/-- Every hypothetical strict odd cover obeys the branch inequality at every
integer residue, for any cap on its ternary exponents. -/
theorem arithmetic_fiber_weight_gt_half {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (E : ℕ) (hE : ∀ i, (m i).factorization 3 ≤ E) (r : ℤ) :
    (1/2 : ℚ) < ∑ j : {j // 3 ∣ m j ∧
      ((3^((m j).factorization 3) : ℕ) : ℤ) ∣ r-a j}, weight (ordCompl[3] (m j)) := by
  classical
  let K := {i : I // ¬ 3 ∣ m i}
  let J := {j : I // 3 ∣ m j}
  let e (j : J) := (m j).factorization 3
  let d (j : J) := ordCompl[3] (m j)
  have hd (j : J) : 0 < d j ∧ Odd (d j) ∧ ¬ 3 ∣ d j :=
    cofactor_properties (m j) (by have := (hc.2.1 j).1; omega) (hc.2.1 j).2
  have hcover : ∀ x : ℤ, (∃ i : K, (m i : ℤ) ∣ x-a i) ∨
      ∃ j : J, ((3^(e j)*d j : ℕ) : ℤ) ∣ x-a j := by
    intro x
    obtain ⟨j,hj⟩ := hc.2.2 x
    by_cases h3 : 3 ∣ m j
    · right
      refine ⟨⟨j,h3⟩,?_⟩
      simpa only [e,d,Nat.ordProj_mul_ordCompl_eq_self] using hj
    · exact Or.inl ⟨⟨j,h3⟩,hj⟩
  have hh := fiber_weight_gt_half (fun i : K => m i) (fun i => a i)
    (hc.1.comp Subtype.val_injective) (fun i => hc.2.1 i) (fun i => i.property)
    e d (fun j => a j) (fun j => ⟨(hd j).1,(hd j).2.1⟩) (fun j => (hd j).2.2)
    hcover E (fun j => hE j) r
  convert hh using 1
  apply Finset.sum_bij (fun j _ => ⟨⟨j.val,j.property.1⟩,j.property.2⟩)
  · intro j _; exact Finset.mem_univ _
  · intro j _ k _ hjk
    apply Subtype.ext
    exact congrArg (fun z => z.val.val) hjk
  · intro j _
    exact ⟨⟨j.val.val,j.val.property,j.property⟩,Finset.mem_univ _,rfl⟩
  · intro j _; rfl

#print axioms fiber_weight_gt_half
#print axioms arithmetic_fiber_weight_gt_half
end Erdos7TernaryWeightedLoad
