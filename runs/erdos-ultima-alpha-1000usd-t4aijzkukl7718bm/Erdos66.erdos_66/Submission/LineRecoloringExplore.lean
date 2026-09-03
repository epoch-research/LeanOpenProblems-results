import Submission.GraphRowAssemblyExplore

/-! A concrete recoloring of finite line lifts. Joint old mixed caps are
regenerated with a factor of two; no asymptotic iteration is claimed. -/
namespace Erdos66LineRecoloring
open Erdos66GraphRowAssembly Erdos66OriginRepair Erdos66AffineLineAssembly
open scoped Classical
set_option maxHeartbeats 2500000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- After assigning new label v=u+alpha*x, the old label is v-alpha*x. -/
def recolorGraph (τ α v x : F) : F :=
  (v-α*x)*x+τ*(v-α*x)^2

lemma quadratic_zero_card (a b c : F) (ha : a≠0) :
    (Finset.univ.filter (fun x : F ↦ a*x^2+b*x+c=0)).card≤2 := by
  by_contra hh
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp (by omega :
    2<(Finset.univ.filter (fun x : F ↦ a*x^2+b*x+c=0)).card)
  have hx := (Finset.mem_filter.mp hx).2
  have hy := (Finset.mem_filter.mp hy).2
  have hz := (Finset.mem_filter.mp hz).2
  have hexy : (x-y)*(a*(x+y)+b)=0 := by linear_combination hx-hy
  have hexz : (x-z)*(a*(x+z)+b)=0 := by linear_combination hx-hz
  have hy' := (mul_eq_zero.mp hexy).resolve_left (sub_ne_zero.mpr hxy)
  have hz' := (mul_eq_zero.mp hexz).resolve_left (sub_ne_zero.mpr hxz)
  apply hyz
  apply mul_left_cancel₀ ha
  linear_combination hy'-hz'

/-- This works for equal as well as distinct NEW colors. The nondegeneracy
condition is alpha*(tau*alpha-1) != 0. -/
theorem recolor_mixed_fiber_two (h2 : (2:F)≠0) (τ α : F)
    (hα : α≠0) (hτ : τ*α≠1) (v w s t : F) :
    (Finset.univ.filter (fun x : F ↦ recolorGraph τ α v x+recolorGraph τ α w (s-x)=t)).card≤2 := by
  let a := 2*α*(τ*α-1)
  let b := (1-2*τ*α)*(v-w)-2*α*(τ*α-1)*s
  let c := τ*v^2+τ*(w-α*s)^2+(w-α*s)*s-t
  have he (x : F) : recolorGraph τ α v x+recolorGraph τ α w (s-x)-t=a*x^2+b*x+c := by
    dsimp only [recolorGraph,a,b,c]
    ring
  have hf : Finset.univ.filter (fun x : F ↦ recolorGraph τ α v x+recolorGraph τ α w (s-x)=t)=
      Finset.univ.filter (fun x : F ↦ a*x^2+b*x+c=0) := by
    apply Finset.filter_congr
    intro x hx
    rw [←he,sub_eq_zero]
  rw [hf]
  exact quadratic_zero_card a b c (mul_ne_zero (mul_ne_zero h2 hα) (sub_ne_zero.mpr hτ))

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def recolored (A : F → Finset G) (τ α v : F) : Finset (G×(F×F)) :=
  rowAssembly (fun x ↦ A (v-α*x)) (recolorGraph τ α v)

omit [AddCommGroup G] in
lemma mem_recolored (A : F → Finset G) (τ α v x y : F) (a : G) :
    (a,(x,y))∈recolored A τ α v ↔ a∈A (v-α*x) ∧ y=recolorGraph τ α v x :=
  mem_rowAssembly _ _ _ _ _

/-- Exact new mixed count, with the two old color labels visible. -/
theorem recolored_mixed_count (A : F → Finset G) (τ α v w s t : F) (z : G) :
    pairCount (recolored A τ α v) (recolored A τ α w) (z,(s,t))=
      ∑ x : F, if recolorGraph τ α v x+recolorGraph τ α w (s-x)=t then
        pairCount (A (v-α*x)) (A (w-α*(s-x))) z else 0 :=
  rowAssembly_mixed_pairCount _ _ _ _ _ _ _

/-- A genuine regenerated cap for ALL pairs of new colors. It requires
old MIXED caps, not merely same-color caps. -/
theorem recolored_joint_cap (h2 : (2:F)≠0) (A : F → Finset G) (τ α : F)
    (hα : α≠0) (hτ : τ*α≠1) (g : ℕ)
    (hcap : ∀ u v z, pairCount (A u) (A v) z≤g) :
    ∀ v w z, pairCount (recolored A τ α v) (recolored A τ α w) z≤2*g := by
  rintro v w ⟨z,s,t⟩
  apply rowAssembly_mixed_cap _ _ _ _ z s t g 2
  · intro x y
    exact hcap _ _ _
  · exact recolor_mixed_fiber_two h2 τ α hα hτ v w s t

omit [AddCommGroup G] in
lemma recolored_disjoint (A : F → Finset G)
    (hA : Pairwise (fun u v ↦ Disjoint (A u) (A v))) (τ α : F) :
    Pairwise (fun v w ↦ Disjoint (recolored A τ α v) (recolored A τ α w)) := by
  intro v w hvw
  apply Finset.disjoint_left.mpr
  rintro ⟨a,x,y⟩ ha hb
  have ha := (mem_recolored A τ α v x y a).mp ha
  have hb := (mem_recolored A τ α w x y a).mp hb
  have hne : v-α*x≠w-α*x := fun he ↦ hvw (sub_left_inj.mp he)
  exact Finset.disjoint_left.mp (hA hne) ha.1 hb.1

omit [AddCommGroup G] in
lemma recolored_card (A : F → Finset G) (τ α v : F) (hα : α≠0) :
    (recolored A τ α v).card=∑ u : F, (A u).card := by
  rw [recolored,rowAssembly_card]
  apply Finset.sum_bij (fun x _ ↦ v-α*x) (fun x _ ↦ Finset.mem_univ _)
  · intro x hx y hy he
    apply mul_left_cancel₀ hα
    exact sub_right_inj.mp he
  · intro u hu
    refine ⟨(v-u)/α,Finset.mem_univ _,?_⟩
    field_simp
    ring
  · intro x hx
    rfl

omit [AddCommGroup G] in
/-- Every old color is retained on the zero slice by the through-origin
version. This concerns a finite product group, not natural carries. -/
theorem origin_color_preserved (A : F → Finset G) (α v : F) (a : G) :
    (a,((0:F),0))∈recolored A 0 α v ↔ a∈A v := by
  simp [mem_recolored,recolorGraph]

omit [AddCommGroup G] in
/-- The union of new colors is the original tau-line assembly, independent
of alpha. The label change does not silently change the underlying set. -/
theorem union_recolored_membership (A : F → Finset G) (τ α x y : F) (a : G) :
    (a,(x,y))∈Finset.univ.biUnion (recolored A τ α) ↔
      ∃ u : F, a∈A u ∧ y=u*x+τ*u^2 := by
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,mem_recolored,recolorGraph]
  constructor
  · rintro ⟨v,hv,hy⟩
    exact ⟨v-α*x,hv,hy⟩
  · rintro ⟨u,hu,hy⟩
    refine ⟨u+α*x,?_,?_⟩ <;> simpa only [add_sub_cancel_right] using (by assumption)

/-- Cardinality is multiplied by the field size, as in the uncolored lift. -/
theorem union_recolored_card (A : F → Finset G)
    (hA : Pairwise (fun u v ↦ Disjoint (A u) (A v))) (τ α : F) (hα : α≠0) :
    (Finset.univ.biUnion (recolored A τ α)).card=
      Fintype.card F*(oldSet A).card := by
  rw [Finset.card_biUnion (fun v _ w _ hvw ↦ recolored_disjoint A hA τ α hvw)]
  simp_rw [recolored_card A τ α _ hα]
  rw [←oldSet_card A hA]
  simp

end Erdos66LineRecoloring
