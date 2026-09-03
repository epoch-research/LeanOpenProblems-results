import Submission.DensePolynomialCocycle

/-! Integration of normalized circle cocycles on a finite cyclic group.
The periodicity obstruction is removed by taking an exact pth root in Circle;
no closeness assertion about that root is used. -/
namespace Erdos3PolynomialCocycleIntegration
open Finset Erdos3DensePolynomialCocycle Erdos3PolynomialDerivativeConsistency
  Erdos3HigherPolynomialSeparation Erdos3HigherPhaseRepresentation
  Erdos3HigherLocalPolynomialProgressions Erdos3HigherPhaseDifferences
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

noncomputable def normalizedDerivative {G : Type*} [AddCommGroup G]
    (q : G → Additive Circle) (h : G) : G → Additive Circle := Erdos3PolynomialDerivativeConsistency.normalize (fwdDiff h q)

lemma normalizedDerivative_cocycle {G : Type*} [AddCommGroup G]
    (q : G → Additive Circle) (h k x : G) :
    normalizedDerivative q (h+k) x = normalizedDerivative q h x+
      normalizedDerivative q k (x+h)-normalizedDerivative q k h := by
  simp only [normalizedDerivative,Erdos3PolynomialDerivativeConsistency.normalize,fwdDiff,zero_add,add_assoc]
  abel

/-- Every normalized circle 2-cocycle on Z/p has a potential. This uses cyclicity,
not an unjustified symmetry or general integration principle. -/
theorem cyclic_cocycle_integrates (p : ℕ) [NeZero p]
    (C : ZMod p → ZMod p → Additive Circle)
    (hzero : ∀ h, C h 0 = 0)
    (hcocycle : ∀ h k x, C (h+k) x = C h x+C k (x+h)-C k h) :
    ∃ q : ZMod p → Additive Circle, q 0 = 0 ∧ ∀ h, normalizedDerivative q h = C h := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨z,hz⟩ := circle_nsmul_surjective hp (-∑ i ∈ range p, C 1 (i : ZMod p))
  let a : ℕ → Additive Circle := fun i ↦ C 1 (i : ZMod p)+z
  let Q : ℕ → Additive Circle := fun n ↦ ∑ i ∈ range n, a i
  have htotal : Q p = 0 := by
    dsimp only [Q,a]
    rw [sum_add_distrib,sum_const,card_range,hz,add_neg_cancel]
  have ha (i : ℕ) : a (p+i) = a i := by
    dsimp only [a]
    rw [Nat.cast_add,ZMod.natCast_self,zero_add]
  have hperiod : Function.Periodic Q p := by
    intro n
    dsimp only [Q]
    rw [Nat.add_comm n p,sum_range_add]
    change Q p+(∑ i ∈ range n, a (p+i)) = Q n
    rw [htotal,zero_add]
    simp only [ha,Q]
  let q : ZMod p → Additive Circle := fun x ↦ Q x.val
  have hqcast (n : ℕ) : q (n : ZMod p) = Q n := by
    dsimp only [q]
    rw [ZMod.val_natCast]
    exact hperiod.map_mod_nat n
  have hQstep (n : ℕ) : Q (n+1)-Q n = a n := by
    dsimp only [Q]
    rw [sum_range_succ,add_sub_cancel_left]
  have hstep (x : ZMod p) : fwdDiff 1 q x = C 1 x+z := by
    have hh : fwdDiff 1 q (x.val : ZMod p) = C 1 (x.val : ZMod p)+z := by
      change q ((x.val : ZMod p)+1)-q (x.val : ZMod p) = _
      rw [← Nat.cast_one,← Nat.cast_add,hqcast,hqcast,hQstep]
      simp only [a,Nat.cast_one]
    simpa only [ZMod.natCast_zmod_val] using hh
  have hqzero : q 0 = 0 := by
    change Q (ZMod.val (0 : ZMod p)) = 0
    simp only [ZMod.val_zero,Q,range_zero,sum_empty]
  have hOne (x : ZMod p) : normalizedDerivative q 1 x = C 1 x := by
    dsimp only [normalizedDerivative,Erdos3PolynomialDerivativeConsistency.normalize]
    rw [hstep,hstep,hzero,zero_add,add_sub_cancel_right]
  have hCzero (x : ZMod p) : C 0 x = 0 := by
    have hh := hcocycle 0 0 x
    simp only [zero_add,add_zero,hzero,sub_zero] at hh
    exact add_eq_left.mp hh.symm
  have hNat (n : ℕ) : ∀ x : ZMod p, normalizedDerivative q (n : ZMod p) x = C (n : ZMod p) x := by
    induction n with
    | zero =>
      intro x
      rw [Nat.cast_zero,hCzero]
      simp only [normalizedDerivative,Erdos3PolynomialDerivativeConsistency.normalize,fwdDiff,add_zero,sub_self]
    | succ n ih =>
      intro x
      rw [Nat.cast_succ,normalizedDerivative_cocycle,hcocycle,ih,hOne,hOne]
  refine ⟨q,hqzero,?_⟩
  intro h
  funext x
  simpa only [ZMod.natCast_zmod_val] using hNat h.val x

/-- A polynomial cocycle integrates to a polynomial phase of one higher degree. -/
theorem cyclic_polynomial_cocycle_integrates (p n : ℕ) [NeZero p]
    (C : ZMod p → ZMod p → Additive Circle)
    (hzero : ∀ h, C h 0 = 0)
    (hpoly : ∀ h, IsLocallyPolynomial Set.univ n (C h))
    (hcocycle : ∀ h k x, C (h+k) x = C h x+C k (x+h)-C k h) :
    ∃ q : ZMod p → Additive Circle, q 0 = 0 ∧
      (∀ h, normalizedDerivative q h = C h) ∧ IsLocallyPolynomial Set.univ (n+1) q := by
  obtain ⟨q,hq0,hq⟩ := cyclic_cocycle_integrates p C hzero hcocycle
  refine ⟨q,hq0,hq,?_⟩
  intro x h _
  change cubeDifference (n+1) (fwdDiff (h 0) q) (fun i ↦ h i.succ) x = 0
  have he : fwdDiff (h 0) q = fun y ↦ C (h 0) y+fwdDiff (h 0) q 0 := by
    funext y
    have hh := congr_fun (hq (h 0)) y
    exact sub_eq_iff_eq_add.mp hh
  rw [he]
  exact global_polynomial_add n _ _ (hpoly (h 0))
    (global_polynomial_const n (fwdDiff (h 0) q 0)) x (fun i ↦ h i.succ)
      (fun _ ↦ Set.mem_univ _)

#print axioms cyclic_cocycle_integrates
#print axioms cyclic_polynomial_cocycle_integrates
end Erdos3PolynomialCocycleIntegration
