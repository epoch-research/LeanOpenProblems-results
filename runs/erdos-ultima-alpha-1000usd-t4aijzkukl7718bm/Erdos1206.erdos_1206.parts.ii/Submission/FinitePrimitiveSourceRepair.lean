import Submission.FinitePrimitiveColorRepair
import Submission.SquarefreeColoringReduction

/-!
Finite primitive-exception repair on a source, including the squarefree
source. No coloring with the finite-exception property is constructed.
-/
namespace Erdos1206.FinitePrimitiveSourceRepair
open RelativePrimitiveMaxima FinitePrimitiveColorRepair

/-- Primitive maxima occurring in monochromatic strict collisions on S. -/
def badMaximaOn {ι : Type*} (S : Set ℕ) (c : ℕ → ι) : Set ℕ :=
  {q | ∃ a∈S, ∃ b∈S, ∃ d∈S, ∃ e∈S,
    0<a ∧ a<b ∧ b<d ∧ d<e ∧ a^3+e^3=b^3+d^3 ∧
    c a=c b ∧ c a=c d ∧ c a=c e ∧ q=primitiveMax a b d e}

/-- Repair is source-preserving: no point of S has to be deleted. -/
theorem bounded_exception_refinement {ι : Type*} {S : Set ℕ} {c : ℕ → ι}
    {H : ℕ} (hH : ∀ q∈badMaximaOn S c, q≤H) :
    ∀ i, IsSidon ((fun n : ℕ => n^3) ''
      {n | n∈S ∧ (c n,valuationColor H n)=i}) := by
  intro i
  apply (cubeSidon_iff_no_strict_positive _).mpr
  intro a ha b hb d hd e he ha0 hab hbd hde heq
  have haC : (c a,valuationColor H a)=i := ha.2
  have hbC : (c b,valuationColor H b)=i := hb.2
  have hdC : (c d,valuationColor H d)=i := hd.2
  have heC : (c e,valuationColor H e)=i := he.2
  have hmax := hH (primitiveMax a b d e)
    ⟨a,ha.1,b,hb.1,d,hd.1,e,he.1,ha0,hab,hbd,hde,heq,
      congrArg Prod.fst (haC.trans hbC.symm),
      congrArg Prod.fst (haC.trans hdC.symm),
      congrArg Prod.fst (haC.trans heC.symm),rfl⟩
  have hga : commonGcd a b d e ∣ a :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hge : commonGcd a b d e ∣ e :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨_,r,hr,s,hs,hrs⟩ := ratio_of_common_divisor ha0
    (hab.trans (hbd.trans hde)).le hga hge
  have hae := ratio_separation ha0 (ha0.trans (hab.trans (hbd.trans hde)))
    hr.1 (hr.2.trans hmax) hs.1 (hs.2.trans hmax) hrs
    (congrArg Prod.snd (haC.trans heC.symm))
  omega

/-- Finitely many distinct bad primitive maxima suffice for a finite refinement
on any source. The hypothesis permits infinitely many absolute bad
quadruples, because a primitive pattern may have arbitrarily large dilations. -/
theorem finite_exception_refinement {ι : Type*} [Fintype ι]
    {S : Set ℕ} {c : ℕ → ι} (hc : (badMaximaOn S c).Finite) :
    ∃ k : ℕ, ∃ d : ℕ → Fin k,
      ∀ i, IsSidon ((fun n : ℕ => n^3) '' {n | n∈S ∧ d n=i}) := by
  classical
  obtain ⟨H,hH⟩ := hc.bddAbove
  let K := ι × (Fin (H+1) → ZMod (H+1))
  let e := Fintype.equivFin K
  let d : ℕ → K := fun n => (c n,valuationColor H n)
  refine ⟨Fintype.card K,fun n => e (d n),?_⟩
  intro i
  have hset : {n : ℕ | n∈S ∧ e (d n)=i} =
      {n : ℕ | n∈S ∧ d n=e.symm i} := by
    ext n
    simp only [Set.mem_setOf_eq,e.apply_eq_iff_eq_symm_apply]
  rw [hset]
  exact bounded_exception_refinement hH (e.symm i)

/-- The finite-exception condition on a squarefree coloring would settle the
original conjecture, after valuation refinement and density extraction. -/
theorem finite_squarefree_exceptions_suffice {ι : Type*} [Fintype ι]
    {c : ℕ → ι} (hc : (badMaximaOn {n | Squarefree n} c).Finite) :
    ∃ A : Set ℕ, A.Infinite ∧ 0<A.lowerDensity ∧
      IsSidon ((fun n : ℕ => n^3) '' A) := by
  obtain ⟨k,d,hd⟩ := finite_exception_refinement hc
  exact finite_squarefree_cube_coloring_suffices d hd

#print axioms bounded_exception_refinement
#print axioms finite_exception_refinement
#print axioms finite_squarefree_exceptions_suffice
end Erdos1206.FinitePrimitiveSourceRepair
