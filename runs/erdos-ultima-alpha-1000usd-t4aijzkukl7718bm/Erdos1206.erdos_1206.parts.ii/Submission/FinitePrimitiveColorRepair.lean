import Submission.RelativePrimitiveMaxima
import Submission.ColoringReduction
import Submission.StrictCubeCollision

/-!
A finite refinement repairs all monochromatic cubic collisions whose
normalized primitive maxima are bounded. The required bound on a coloring's
bad primitive maxima is not constructed here.
-/
namespace Erdos1206.FinitePrimitiveColorRepair
open RelativePrimitiveMaxima

/-- A finite vector of valuations, reduced modulo a fixed positive modulus. -/
def valuationColor (H n : ℕ) : Fin (H+1) → ZMod (H+1) :=
  fun p => n.factorization p

/-- Equal valuation colors separate all nontrivial ratios with numerator and
denominator at most H. The roots themselves need not be bounded. -/
theorem ratio_separation {H x y r s : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) (hrH : r ≤ H)
    (hs : 0 < s) (hsH : s ≤ H) (he : r*x=s*y)
    (hc : valuationColor H x=valuationColor H y) : x=y := by
  have hrs : r=s := by
    apply Nat.eq_of_factorization_eq hr.ne' hs.ne'
    intro p
    by_cases hp : p ≤ H
    · have hxy : (x.factorization p : ZMod (H+1)) = y.factorization p :=
        congrFun hc ⟨p,by omega⟩
      have hv := congrArg (fun n : ℕ => n.factorization p) he
      dsimp only at hv
      rw [Nat.factorization_mul hr.ne' hx.ne',
        Nat.factorization_mul hs.ne' hy.ne',Finsupp.add_apply,Finsupp.add_apply] at hv
      have hv' := congrArg (fun n : ℕ => (n : ZMod (H+1))) hv
      simp only [Nat.cast_add] at hv'
      rw [hxy] at hv'
      have hemod := (ZMod.natCast_eq_natCast_iff _ _ (H+1)).mp
        (add_right_cancel hv')
      exact hemod.eq_of_lt_of_lt ((Nat.factorization_lt p hr.ne').trans_le (by omega))
        ((Nat.factorization_lt p hs.ne').trans_le (by omega))
    · rw [Nat.factorization_eq_zero_of_lt (by omega : r < p),
        Nat.factorization_eq_zero_of_lt (by omega : s < p)]
  rw [←hrs] at he
  exact Nat.eq_of_mul_eq_mul_left hr he

/-- A hypothesis only about the primitive maxima of monochromatic collisions,
not about the absolute size of their common dilations. -/
def BoundedBadMaxima {ι : Type*} (H : ℕ) (c : ℕ → ι) : Prop :=
  ∀ a b d e : ℕ, 0<a → a<b → b<d → d<e → a^3+e^3=b^3+d^3 →
    c a=c b → c a=c d → c a=c e → primitiveMax a b d e ≤ H

/-- Repair a coloring with bounded bad primitive maxima by adding a finite
valuation vector. This asserts a refinement, not the existence of the input. -/
theorem repaired_coloring {ι : Type*} {H : ℕ} {c : ℕ → ι}
    (hc : BoundedBadMaxima H c) :
    GoodCubeColoring (fun n => (c n,valuationColor H n)) := by
  intro i
  apply (cubeSidon_iff_no_strict_positive _).mpr
  intro a ha b hb d hd e he ha0 hab hbd hde heq
  have haC : (c a,valuationColor H a)=i := ha.2
  have hbC : (c b,valuationColor H b)=i := hb.2
  have hdC : (c d,valuationColor H d)=i := hd.2
  have heC : (c e,valuationColor H e)=i := he.2
  have hH := hc a b d e ha0 hab hbd hde heq
    (congrArg Prod.fst (haC.trans hbC.symm))
    (congrArg Prod.fst (haC.trans hdC.symm))
    (congrArg Prod.fst (haC.trans heC.symm))
  have hga : commonGcd a b d e ∣ a :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hge : commonGcd a b d e ∣ e :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨_,r,hr,s,hs,hrs⟩ := ratio_of_common_divisor ha0
    (hab.trans (hbd.trans hde)).le hga hge
  have hae := ratio_separation ha0 (ha0.trans (hab.trans (hbd.trans hde)))
    hr.1 (hr.2.trans hH) hs.1 (hs.2.trans hH) hrs
    (congrArg Prod.snd (haC.trans heC.symm))
  omega

/-- A finite coloring with only bounded bad primitive maxima would suffice for
the original positive-lower-density conclusion. -/
theorem bounded_bad_primitive_maxima_suffice {ι : Type*} [Fintype ι]
    {H : ℕ} {c : ℕ → ι} (hc : BoundedBadMaxima H c) :
    ∃ A : Set ℕ, A.Infinite ∧ 0<A.lowerDensity ∧
      IsSidon ((fun n : ℕ => n^3) '' A) := by
  classical
  let K := ι × (Fin (H+1) → ZMod (H+1))
  let e := Fintype.equivFin K
  let d : ℕ → K := fun n => (c n,valuationColor H n)
  apply finite_cube_coloring_suffices (fun n => e (d n))
  intro i
  have hset : {n : ℕ | 0<n ∧ e (d n)=i} =
      {n : ℕ | 0<n ∧ d n=e.symm i} := by
    ext n
    simp only [Set.mem_setOf_eq,e.apply_eq_iff_eq_symm_apply]
  rw [hset]
  exact repaired_coloring hc (e.symm i)

#print axioms ratio_separation
#print axioms repaired_coloring
#print axioms bounded_bad_primitive_maxima_suffice
end Erdos1206.FinitePrimitiveColorRepair
