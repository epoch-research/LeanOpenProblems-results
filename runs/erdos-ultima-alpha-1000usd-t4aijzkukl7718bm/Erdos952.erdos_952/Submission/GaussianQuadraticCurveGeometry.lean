import Submission.PiecewiseModularObstruction

/-! Exact geometry of real plane quadratic curves under bounded Gaussian
translations. A nonzero translation forces a common zero onto a finite
family of real affine lines, including the translation-invariant case. -/
namespace Erdos952Investigation.GaussianQuadraticCurveGeometry
open Polynomial
open scoped Classical
set_option maxHeartbeats 0
noncomputable section

structure Quad where
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  E : ℝ
  F : ℝ

def Quad.Nonzero (q : Quad) : Prop :=
  ¬ (q.A = 0 ∧ q.B = 0 ∧ q.C = 0 ∧ q.D = 0 ∧ q.E = 0 ∧ q.F = 0)

def Quad.eval (q : Quad) (z : GaussianInt) : ℝ :=
  q.A*(z.re : ℝ)^2+q.B*(z.re : ℝ)*(z.im : ℝ)+q.C*(z.im : ℝ)^2+
    q.D*(z.re : ℝ)+q.E*(z.im : ℝ)+q.F

/-- Translate the input plane without changing the quadratic part. -/
def Quad.shift (q : Quad) (d : GaussianInt) : Quad where
  A := q.A
  B := q.B
  C := q.C
  D := q.D+2*q.A*(d.re : ℝ)+q.B*(d.im : ℝ)
  E := q.E+q.B*(d.re : ℝ)+2*q.C*(d.im : ℝ)
  F := q.F+q.A*(d.re : ℝ)^2+q.B*(d.re : ℝ)*(d.im : ℝ)+q.C*(d.im : ℝ)^2+
    q.D*(d.re : ℝ)+q.E*(d.im : ℝ)

lemma Quad.eval_shift (q : Quad) (d z : GaussianInt) :
    (q.shift d).eval z = q.eval (z+d) := by
  simp only [Quad.shift,Quad.eval,Zsqrtd.re_add,Zsqrtd.im_add,Int.cast_add]
  ring

lemma Quad.shift_nonzero (q : Quad) (hq : q.Nonzero) (d : GaussianInt) :
    (q.shift d).Nonzero := by
  rintro ⟨ha,hb,hc,hd,he,hf⟩
  change q.A = 0 at ha
  change q.B = 0 at hb
  change q.C = 0 at hc
  dsimp only [Quad.shift] at hd he hf
  simp only [ha,hb,hc,zero_mul,mul_zero,add_zero] at hd he
  simp only [ha,hb,hc,hd,he,zero_mul,add_zero] at hf
  exact hq ⟨ha,hb,hc,hd,he,hf⟩

abbrev Line := ℝ × (ℝ × ℝ)
def Line.Valid (l : Line) : Prop := l.1 ≠ 0 ∨ l.2.1 ≠ 0
def Line.eval (l : Line) (z : GaussianInt) : ℝ :=
  l.1*(z.re : ℝ)+l.2.1*(z.im : ℝ)+l.2.2

def differenceLine (q : Quad) (d : GaussianInt) : Line :=
  (2*q.A*(d.re : ℝ)+q.B*(d.im : ℝ),
   q.B*(d.re : ℝ)+2*q.C*(d.im : ℝ),
   q.A*(d.re : ℝ)^2+q.B*(d.re : ℝ)*(d.im : ℝ)+q.C*(d.im : ℝ)^2+
     q.D*(d.re : ℝ)+q.E*(d.im : ℝ))

lemma eval_add_difference (q : Quad) (d z : GaussianInt) :
    q.eval (z+d)-q.eval z = (differenceLine q d).eval z := by
  simp only [Quad.eval,Line.eval,differenceLine,Zsqrtd.re_add,Zsqrtd.im_add,Int.cast_add]
  ring

def quadPoly (a b c : ℝ) : Polynomial ℝ := C a*X^2+C b*X+C c

lemma quadPoly_eval (a b c t : ℝ) : (quadPoly a b c).eval t = a*t^2+b*t+c := by
  simp [quadPoly]

lemma quadPoly_eq_zero_iff (a b c : ℝ) : quadPoly a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro he
    have h2 := congrArg (fun P : Polynomial ℝ => P.coeff 2) he
    have h1 := congrArg (fun P : Polynomial ℝ => P.coeff 1) he
    have h0 := congrArg (fun P : Polynomial ℝ => P.coeff 0) he
    norm_num [quadPoly,Polynomial.coeff_C_mul_X_pow] at h2 h1 h0
    exact ⟨h2,h1,h0⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp [quadPoly]

/-- A nontrivial quadratic invariant under a nonzero translation is a
nonzero univariate polynomial in a nonzero linear projection. -/
lemma invariant_projection (q : Quad) (hq : q.Nonzero) (d : GaussianInt) (hd : d ≠ 0)
    (hA : (differenceLine q d).1 = 0) (hB : (differenceLine q d).2.1 = 0)
    (hC : (differenceLine q d).2.2 = 0) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∃ P : Polynomial ℝ, P ≠ 0 ∧
      ∀ z : GaussianInt, q.eval z = 0 → P.eval (a*(z.re : ℝ)+b*(z.im : ℝ)) = 0 := by
  let u : ℝ := d.re
  let v : ℝ := d.im
  have hgrad1 : 2*q.A*u+q.B*v = 0 := hA
  have hgrad2 : q.B*u+2*q.C*v = 0 := hB
  have hconst : q.A*u^2+q.B*u*v+q.C*v^2+q.D*u+q.E*v = 0 := hC
  have hlinear : q.D*u+q.E*v = 0 := by
    linear_combination hconst-(u/2)*hgrad1-(v/2)*hgrad2
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      intro hv
      apply hd
      apply Zsqrtd.ext
      · change d.re = 0
        exact_mod_cast (show (d.re : ℝ) = 0 from hu)
      · change d.im = 0
        exact_mod_cast (show (d.im : ℝ) = 0 from hv)
    have hqB : q.B = 0 := (mul_eq_zero.mp (by simpa [hu] using hgrad1)).resolve_right hv
    have hqC : q.C = 0 := by
      have hh : q.C*v = 0 := by nlinarith [hgrad2]
      exact (mul_eq_zero.mp hh).resolve_right hv
    have hqE : q.E = 0 := (mul_eq_zero.mp (by simpa [hu] using hlinear)).resolve_right hv
    refine ⟨1,0,Or.inl one_ne_zero,quadPoly q.A q.D q.F,?_,?_⟩
    · intro he
      obtain ⟨ha,hd',hf⟩ := (quadPoly_eq_zero_iff _ _ _).mp he
      exact hq ⟨ha,hqB,hqC,hd',hqE,hf⟩
    · intro z hz
      simpa only [quadPoly_eval,one_mul,zero_mul,add_zero,Quad.eval,hqB,hqC,hqE,
        zero_add] using hz
  · have huu : u^2 ≠ 0 := pow_ne_zero 2 hu
    have hquad : q.A*u^2-q.C*v^2 = 0 := by
      linear_combination (u/2)*hgrad1-(v/2)*hgrad2
    refine ⟨-v,u,Or.inr hu,quadPoly q.C (q.E*u) (q.F*u^2),?_,?_⟩
    · intro he
      obtain ⟨hc,he',hf'⟩ := (quadPoly_eq_zero_iff _ _ _).mp he
      have he : q.E = 0 := (mul_eq_zero.mp he').resolve_right hu
      have hf : q.F = 0 := (mul_eq_zero.mp hf').resolve_right huu
      have hb : q.B = 0 := (mul_eq_zero.mp (by simpa [hc] using hgrad2)).resolve_right hu
      have ha : q.A = 0 := by
        have hg : 2*q.A*u = 0 := by simpa only [hb,zero_mul,add_zero] using hgrad1
        have hh : q.A*u = 0 := by nlinarith [hg]
        exact (mul_eq_zero.mp hh).resolve_right hu
      have hd' : q.D = 0 := (mul_eq_zero.mp (by simpa [he] using hlinear)).resolve_right hu
      exact hq ⟨ha,hb,hc,hd',he,hf⟩
    · intro z hz
      rw [quadPoly_eval]
      dsimp only [Quad.eval] at hz
      linear_combination u^2*hz-(z.re : ℝ)^2*hquad-
        (u*(z.re : ℝ)*(z.im : ℝ))*hgrad2-(u*(z.re : ℝ))*hlinear

/-- A polynomial condition on a linear projection is a finite affine-line
cover. Roots, rather than a guessed quadratic formula, handle every degeneracy. -/
lemma projection_line_cover (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (P : Polynomial ℝ) (hP : P ≠ 0) :
    ∃ S : Finset Line, (∀ l ∈ S, l.Valid) ∧ ∀ z : GaussianInt,
      P.eval (a*(z.re : ℝ)+b*(z.im : ℝ)) = 0 → ∃ l ∈ S, l.eval z = 0 := by
  let S := P.roots.toFinset.image (fun t => (a,b,-t))
  refine ⟨S,?_,?_⟩
  · intro l hl
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hl
    exact hab
  · intro z hz
    refine ⟨(a,b,-(a*(z.re : ℝ)+b*(z.im : ℝ))),?_,?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨a*(z.re : ℝ)+b*(z.im : ℝ),?_,rfl⟩
      rw [Multiset.mem_toFinset,Polynomial.mem_roots hP]
      exact hz
    · dsimp only [Line.eval]
      ring

/-- Every fixed nonzero translation of a nonzero real quadratic has its
common-zero locus covered by finitely many proper affine lines. -/
theorem translated_intersection_line_cover (q : Quad) (hq : q.Nonzero)
    (d : GaussianInt) (hd : d ≠ 0) :
    ∃ S : Finset Line, (∀ l ∈ S, l.Valid) ∧ ∀ z : GaussianInt,
      q.eval z = 0 → q.eval (z+d) = 0 → ∃ l ∈ S, l.eval z = 0 := by
  let l := differenceLine q d
  by_cases hl : l.Valid
  · refine ⟨{l},?_,?_⟩
    · intro r hr
      simpa only [Finset.mem_singleton.mp hr] using hl
    · intro z hz hzd
      refine ⟨l,Finset.mem_singleton_self l,?_⟩
      rw [← eval_add_difference,hzd,hz,sub_self]
  · have hA : l.1 = 0 := by simpa only [Line.Valid,not_or,not_not] using (not_or.mp hl).1
    have hB : l.2.1 = 0 := by simpa only [Line.Valid,not_or,not_not] using (not_or.mp hl).2
    by_cases hC : l.2.2 = 0
    · obtain ⟨a,b,hab,P,hP,hproj⟩ := invariant_projection q hq d hd hA hB hC
      obtain ⟨S,hS,hcover⟩ := projection_line_cover a b hab P hP
      exact ⟨S,hS,fun z hz _ => hcover z (hproj z hz)⟩
    · refine ⟨∅,by simp,?_⟩
      intro z hz hzd
      have he := eval_add_difference q d z
      change q.eval (z+d)-q.eval z = l.eval z at he
      simp only [Line.eval,hA,hB,zero_mul,zero_add,hz,hzd,sub_self] at he
      exact False.elim (hC he.symm)

#print axioms invariant_projection
#print axioms translated_intersection_line_cover
end
end Erdos952Investigation.GaussianQuadraticCurveGeometry
