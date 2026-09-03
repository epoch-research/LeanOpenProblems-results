import Submission.CentralReflection

/-! Rational distances in the OUTPUT of the central quadratic construction
force its normalized parameters to have degree at most two. The source norm
hypotheses are not needed. -/
namespace Erdos213.CentralOutputField
noncomputable section
set_option maxHeartbeats 4000000

def gram (z w : ℂ) : ℝ := z.re*w.re+z.im*w.im

def GramRat (z w : ℂ) : Prop := gram z w∈Set.range ((↑) : ℚ → ℝ)

lemma gram_self (z : ℂ) : gram z z=Complex.normSq z := rfl

lemma gram_sub (z w : ℂ) :
    Complex.normSq (z-w)=Complex.normSq z+Complex.normSq w-2*gram z w := by
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,gram]
  ring

lemma gram_from_distances (z w : ℂ)
    (hz : dist z 0∈Set.range ((↑) : ℚ → ℝ))
    (hw : dist w 0∈Set.range ((↑) : ℚ → ℝ))
    (hd : dist z w∈Set.range ((↑) : ℚ → ℝ)) : GramRat z w := by
  obtain ⟨a,ha⟩ := hz
  obtain ⟨b,hb⟩ := hw
  obtain ⟨d,hd⟩ := hd
  refine ⟨(a^2+b^2-d^2)/2,?_⟩
  have he := gram_sub z w
  simp only [Complex.normSq_eq_norm_sq,← dist_eq_norm] at he
  simp only [dist_zero_right] at ha hb
  rw [← ha,← hb,← hd] at he
  push_cast
  linarith

lemma GramRat.add_left {a b c : ℂ} (ha : GramRat a c) (hb : GramRat b c) :
    GramRat (a+b) c := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  refine ⟨x+y,?_⟩
  simp only [Rat.cast_add,gram,Complex.add_re,Complex.add_im] at hx hy ⊢
  linear_combination hx+hy

lemma GramRat.sub_left {a b c : ℂ} (ha : GramRat a c) (hb : GramRat b c) :
    GramRat (a-b) c := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  refine ⟨x-y,?_⟩
  simp only [Rat.cast_sub,gram,Complex.sub_re,Complex.sub_im] at hx hy ⊢
  linear_combination hx-hy

lemma GramRat.symm {a b : ℂ} (h : GramRat a b) : GramRat b a := by
  obtain ⟨q,hq⟩ := h
  refine ⟨q,?_⟩
  dsimp [gram] at hq ⊢
  linear_combination hq

lemma GramRat.add_right {a b c : ℂ} (hb : GramRat a b) (hc : GramRat a c) :
    GramRat a (b+c) := (hb.symm.add_left hc.symm).symm

lemma GramRat.sub_right {a b c : ℂ} (hb : GramRat a b) (hc : GramRat a c) :
    GramRat a (b-c) := (hb.symm.sub_left hc.symm).symm

lemma gram_identity (x y : ℂ) :
    (gram x x : ℂ)*y^2-2*(gram y x : ℂ)*y*x+(gram y y : ℂ)*x^2=0 := by
  apply Complex.ext <;> simp [gram,pow_two] <;> ring

lemma gram_self_ne_zero {x : ℂ} (hx : x≠0) : gram x x≠0 := by
  intro hh
  apply hx
  apply Complex.ext
  · change x.re=0
    dsimp [gram] at hh
    nlinarith [sq_nonneg x.re,sq_nonneg x.im]
  · change x.im=0
    dsimp [gram] at hh
    nlinarith [sq_nonneg x.re,sq_nonneg x.im]

/-- A nonzero reference vector and rational Gram data give a rational monic
quadratic equation for the complex ratio. -/
theorem quadratic_from_gram (x y : ℂ) (hx : x≠0)
    (hxx : GramRat x x) (hyx : GramRat y x) (hyy : GramRat y y) :
    ∃ u v : ℚ, (y/x)^2-(u : ℂ)*(y/x)+(v : ℂ)=0 := by
  obtain ⟨a,ha⟩ := hxx
  obtain ⟨b,hb⟩ := hyx
  obtain ⟨c,hc⟩ := hyy
  have ha0 : a≠0 := by
    intro hh
    apply gram_self_ne_zero hx
    simpa [hh] using ha.symm
  have haC : (a : ℂ)≠0 := by exact_mod_cast ha0
  have ha' := congrArg Complex.ofReal ha
  have hb' := congrArg Complex.ofReal hb
  have hc' := congrArg Complex.ofReal hc
  simp only [Complex.ofReal_ratCast] at ha' hb' hc'
  have he : (a : ℂ)*y^2-2*(b : ℂ)*y*x+(c : ℂ)*x^2=0 := by
    rw [ha',hb',hc']
    exact gram_identity x y
  refine ⟨2*b/a,c/a,?_⟩
  push_cast
  field_simp
  linear_combination he

def sumCorners (t w : ℂ) : ℂ :=
  CentralReflection.points t w 3+CentralReflection.points t w 4+
  (CentralReflection.points t w 5+CentralReflection.points t w 6)

def differenceCorners (t w : ℂ) : ℂ :=
  CentralReflection.points t w 3+CentralReflection.points t w 4-
  (CentralReflection.points t w 5+CentralReflection.points t w 6)

lemma corner_identities (t w : ℂ) : sumCorners t w=4 ∧ differenceCorners t w=4*t := by
  constructor
  · change (1+t)*(1+w)+(1+t)*(1-w)+((1-t)*(1+w)+(1-t)*(1-w))=4
    ring
  · change (1+t)*(1+w)+(1+t)*(1-w)-((1-t)*(1+w)+(1-t)*(1-w))=4*t
    ring

/-- This statement allows an arbitrary nonzero common complex scale. -/
theorem quadratic_of_scaled_output_distances (t w l : ℂ) (hl : l≠0)
    (hd : ∀ i j : Fin 7,
      dist (l*CentralReflection.points t w i) (l*CentralReflection.points t w j)
        ∈Set.range ((↑) : ℚ → ℝ)) :
    ∃ u v : ℚ, t^2-(u : ℂ)*t+(v : ℂ)=0 := by
  let p := fun i : Fin 7 => l*CentralReflection.points t w i
  have hp0 : p 0=0 := by dsimp [p,CentralReflection.points]; simp
  have hg (i j : Fin 7) : GramRat (p i) (p j) := by
    apply gram_from_distances _ _
    · simpa only [hp0] using (show dist (p i) (p 0)∈Set.range ((↑) : ℚ → ℝ) from hd i 0)
    · simpa only [hp0] using (show dist (p j) (p 0)∈Set.range ((↑) : ℚ → ℝ) from hd j 0)
    · exact hd i j
  let x := p 3+p 4+(p 5+p 6)
  let y := p 3+p 4-(p 5+p 6)
  have hxg (i : Fin 7) : GramRat (p i) x :=
    ((hg i 3).add_right (hg i 4)).add_right ((hg i 5).add_right (hg i 6))
  have hyg (i : Fin 7) : GramRat (p i) y :=
    ((hg i 3).add_right (hg i 4)).sub_right ((hg i 5).add_right (hg i 6))
  have hxx : GramRat x x := ((hxg 3).add_left (hxg 4)).add_left ((hxg 5).add_left (hxg 6))
  have hyx : GramRat y x := ((hxg 3).add_left (hxg 4)).sub_left ((hxg 5).add_left (hxg 6))
  have hyy : GramRat y y := ((hyg 3).add_left (hyg 4)).sub_left ((hyg 5).add_left (hyg 6))
  have hx : x=4*l := by
    have he := congrArg (fun z : ℂ => l*z) (corner_identities t w).1
    dsimp [x,p]
    dsimp only [sumCorners] at he
    linear_combination he
  have hy : y=4*l*t := by
    have he := congrArg (fun z : ℂ => l*z) (corner_identities t w).2
    dsimp [y,p]
    dsimp only [differenceCorners] at he
    linear_combination he
  have hx0 : x≠0 := by rw [hx]; exact mul_ne_zero (by norm_num) hl
  have he : y/x=t := by rw [hx,hy]; field_simp
  obtain ⟨u,v,hq⟩ := quadratic_from_gram x y hx0 hxx hyx hyy
  exact ⟨u,v,by simpa only [he] using hq⟩

#print axioms gram_from_distances
#print axioms quadratic_from_gram
#print axioms corner_identities
#print axioms quadratic_of_scaled_output_distances
end
end Erdos213.CentralOutputField
