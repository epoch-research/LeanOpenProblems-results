import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

/-! Algebraic groundwork for a rational-function chord rigidity argument.
The final declarations specify exactly which symbolic square conditions are
used; this file does not assert the Erdős conjecture or its negation. -/
namespace Erdos213.RationalChordPencil

open Polynomial
noncomputable section
set_option maxHeartbeats 2000000

abbrev bar (f : ℂ[X]) : ℂ[X] := f.map (starRingEnd ℂ)
abbrev pencil (a b : ℂ[X]) (u : ℂ) : ℂ[X] := a-C u*b

lemma pencil_wronskian (a b : ℂ[X]) (u : ℂ) :
    wronskian (pencil a b u) b = wronskian a b := by
  simp only [pencil, wronskian, derivative_sub, derivative_mul, derivative_C,
    zero_mul, zero_add]
  ring

lemma pencil_ne_zero {a b : ℂ[X]} (hW : wronskian a b≠0) (u : ℂ) :
    pencil a b u≠0 := by
  intro he
  have h := pencil_wronskian a b u
  rw [he, wronskian_zero_left] at h
  exact hW h.symm

lemma denominator_at_pencil_root {a b : ℂ[X]} (hab : IsCoprime a b) {u r : ℂ}
    (hr : (pencil a b u).eval r=0) : b.eval r≠0 := by
  intro hb
  have ha : a.eval r=0 := by simpa [pencil, hb] using hr
  obtain ⟨s,t,hst⟩ := hab
  have hh := congrArg (fun f : ℂ[X] => f.eval r) hst
  simp [ha,hb] at hh

lemma pencil_root_value {a b : ℂ[X]} (hab : IsCoprime a b) {u r : ℂ}
    (hr : (pencil a b u).eval r=0) : u=a.eval r/b.eval r := by
  have hb := denominator_at_pencil_root hab hr
  apply (eq_div_iff hb).mpr
  simp only [pencil, eval_sub, eval_mul, eval_C] at hr
  exact (sub_eq_zero.mp hr).symm

/-- Outside the images of finitely many critical points and denominator roots,
the numerator of the shifted rational function is separable and does not
cancel against either denominator. -/
lemma good_pencil {a b d : ℂ[X]} (hab : IsCoprime a b) (u : ℂ)
    (hgood : ∀ r : ℂ, (wronskian a b*d).eval r=0 → u≠a.eval r/b.eval r) :
    (pencil a b u).Separable ∧ IsCoprime (pencil a b u) (b*d) := by
  constructor
  · rw [separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ (K := ℂ)]
    intro r
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id]
    by_cases hr : (pencil a b u).eval r=0
    · right
      intro hdr
      apply hgood r ?_ (pencil_root_value hab hr)
      have he : (wronskian a b).eval r=0 := by
        rw [← pencil_wronskian a b u]
        simp only [wronskian, eval_sub, eval_mul, hr, hdr, zero_mul, sub_self]
      simp [he]
    · exact Or.inl hr
  · rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ (K := ℂ)]
    intro r
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id]
    by_cases hr : (pencil a b u).eval r=0
    · right
      intro hbd
      have hb := denominator_at_pencil_root hab hr
      have hd : d.eval r=0 := by
        rw [eval_mul] at hbd
        exact (mul_eq_zero.mp hbd).resolve_left hb
      exact hgood r (by simp [hd]) (pencil_root_value hab hr)
    · exact Or.inl hr

lemma finite_bad_values {a b d : ℂ[X]} (hW : wronskian a b≠0) (hd : d≠0) :
    Set.Finite ((fun r : ℂ => a.eval r/b.eval r) ''
      {r : ℂ | (wronskian a b*d).eval r=0}) := by
  exact (finite_setOf_isRoot (mul_ne_zero hW hd)).image _

lemma squarefree_dvd_other {f g : ℂ[X]} (hf : f≠0) (hs : Squarefree f)
    (hsq : IsSquare (f*g)) : f ∣ g := by
  obtain ⟨p,hp⟩ := hsq
  have hd : f ∣ p^2 := ⟨g,by simpa only [pow_two] using hp.symm⟩
  obtain ⟨q,hq⟩ := (hs.dvd_pow_iff_dvd (by decide : (2 : ℕ)≠0)).mp hd
  refine ⟨q^2,?_⟩
  apply mul_left_cancel₀ hf
  rw [hp,hq]
  ring

lemma conjugate_proportional {f b : ℂ[X]} (hf : f≠0) (hs : f.Separable)
    (hb : IsCoprime f (b*bar b))
    (hN : IsSquare (f*bar f*b*bar b)) :
    ∃ k : ℂ, k≠0 ∧ bar f=C k*f := by
  have hmul : IsSquare (f*(bar f*(b*bar b))) := by convert hN using 1; ring
  have hdiv : f ∣ bar f := hb.dvd_of_dvd_mul_right
    (squarefree_dvd_other hf hs.squarefree hmul)
  obtain ⟨q,hq⟩ := hdiv
  have hbf : bar f≠0 := map_ne_zero hf
  have hq0 : q≠0 := by intro he; simp [he] at hq; exact hf hq
  have hdeg := congrArg natDegree hq
  rw [natDegree_map, natDegree_mul hf hq0] at hdeg
  have hqdeg : q.natDegree=0 := by omega
  have heq := eq_C_of_natDegree_eq_zero hqdeg
  refine ⟨q.coeff 0,?_,?_⟩
  · intro hz
    apply hq0
    rw [heq,hz,C_0]
  · calc
      bar f=f*q := hq
      _=f*C (q.coeff 0) := congrArg (fun z => f*z) heq
      _=C (q.coeff 0)*f := mul_comm _ _

/-- Every good symbolic square anchor yields a conjugation-invariant numerator
up to a nonzero complex scalar. -/
lemma good_square_anchor {a b : ℂ[X]} (hab : IsCoprime a b)
    (hW : wronskian a b≠0) (u : ℂ)
    (hgood : ∀ r : ℂ, (wronskian a b*bar b).eval r=0 → u≠a.eval r/b.eval r)
    (hsq : IsSquare (pencil a b u*bar (pencil a b u)*b*bar b)) :
    ∃ k : ℂ, k≠0 ∧ bar (pencil a b u)=C k*pencil a b u := by
  obtain ⟨hs,hcop⟩ := good_pencil hab u hgood
  exact conjugate_proportional (pencil_ne_zero hW u) hs hcop hsq

/-- An infinite collection of symbolic square anchors contains two distinct
good anchors. The finite exceptional set is removed explicitly. -/
theorem two_good_anchors {a b : ℂ[X]} (hab : IsCoprime a b) (hb : b≠0)
    (hW : wronskian a b≠0) (U : Set ℂ) (hU : U.Infinite)
    (hsq : ∀ u∈U, IsSquare (pencil a b u*bar (pencil a b u)*b*bar b)) :
    ∃ u∈U, ∃ v∈U, u≠v ∧ ∃ k l : ℂ, k≠0 ∧ l≠0 ∧
      bar (pencil a b u)=C k*pencil a b u ∧
      bar (pencil a b v)=C l*pencil a b v := by
  let B : Set ℂ := (fun r : ℂ => a.eval r/b.eval r) ''
    {r : ℂ | (wronskian a b*bar b).eval r=0}
  have hB : B.Finite := finite_bad_values hW (map_ne_zero hb)
  have hUB : (U\B).Infinite := hU.diff hB
  obtain ⟨u,hu,v,hv,huv⟩ := hUB.nontrivial
  have good (z : ℂ) (hz : z∈U\B) :
      ∃ k : ℂ, k≠0 ∧ bar (pencil a b z)=C k*pencil a b z := by
    apply good_square_anchor hab hW z ?_ (hsq z hz.1)
    intro r hr he
    exact hz.2 ⟨r,hr,he.symm⟩
  obtain ⟨k,hk,he⟩ := good u hu
  obtain ⟨l,hl,hf⟩ := good v hv
  exact ⟨u,hu.1,v,hv.1,huv,k,l,hk,hl,he,hf⟩

#print axioms good_pencil
#print axioms conjugate_proportional
#print axioms two_good_anchors
end
end Erdos213.RationalChordPencil
