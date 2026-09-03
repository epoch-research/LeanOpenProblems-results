import Submission.MixedDisjointAssemblyExplore

/-! A unit-mean finite lift by affine lines. Only same-color pairs cause
error. No infinite compatible coloring or natural-number witness is asserted. -/
namespace Erdos66AffineLineKernel
open Erdos66OriginRepair Erdos66DisjointPaletteAssembly Erdos66ParabolaRepair
open scoped Classical
set_option maxHeartbeats 2200000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def line (u : F) : Finset (F×F) :=
  Finset.univ.image (fun x : F ↦ (x,u*x+u^2))

lemma mem_line (u : F) (z : F×F) : z∈line u ↔ z.2=u*z.1+u^2 := by
  simp only [line,Finset.mem_image,Finset.mem_univ,true_and,Prod.ext_iff]
  constructor
  · rintro ⟨x,rfl,he⟩
    exact he.symm
  · intro h
    exact ⟨z.1,rfl,h.symm⟩

lemma line_card (u : F) : (line u).card=Fintype.card F := by
  rw [line,Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h)]
  simp

lemma line_pair_filter (u v x y : F) :
    pairCount (line u) (line v) (x,y)=
      (Finset.univ.filter (fun z : F ↦ (u-v)*z=y-v*x-u^2-v^2)).card := by
  unfold pairCount
  rw [show line u=Finset.univ.image (fun z : F ↦ (z,u*z+u^2)) by rfl,
    Finset.filter_image,Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h)]
  congr 1
  apply Finset.filter_congr
  intro z hz
  rw [mem_line]
  dsimp
  constructor <;> intro h <;> linear_combination -h

lemma line_pair_different (u v x y : F) (huv : u≠v) :
    pairCount (line u) (line v) (x,y)=1 := by
  rw [line_pair_filter]
  have hne : u-v≠0 := sub_ne_zero.mpr huv
  have hf : Finset.univ.filter (fun z : F ↦ (u-v)*z=y-v*x-u^2-v^2)=
      {(y-v*x-u^2-v^2)/(u-v)} := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    rw [eq_div_iff hne]
    constructor <;> intro h <;> simpa only [mul_comm] using h
  rw [hf,Finset.card_singleton]

lemma line_pair_same (u x y : F) :
    pairCount (line u) (line u) (x,y)=
      if y=u*x+2*u^2 then Fintype.card F else 0 := by
  rw [line_pair_filter]
  have he : (0:F)=y-u*x-u^2-u^2 ↔ y=u*x+2*u^2 := by
    constructor <;> intro h <;> linear_combination -h
  simp only [sub_self,zero_mul,he]
  split_ifs with h <;> simp [h]

lemma concurrent_card (htwo : (2:F)≠0) (x y : F) :
    (Finset.univ.filter (fun u : F ↦ y=u*x+2*u^2)).card≤2 := by
  by_contra h
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp (by omega :
    2<(Finset.univ.filter (fun u : F ↦ y=u*x+2*u^2)).card)
  have ha := (Finset.mem_filter.mp ha).2
  have hb := (Finset.mem_filter.mp hb).2
  have hc := (Finset.mem_filter.mp hc).2
  have hab' : (a-b)*(x+2*(a+b))=0 := by linear_combination hb-ha
  have hac' : (a-c)*(x+2*(a+c))=0 := by linear_combination hc-ha
  have hb' := (mul_eq_zero.mp hab').resolve_left (sub_ne_zero.mpr hab)
  have hc' := (mul_eq_zero.mp hac').resolve_left (sub_ne_zero.mpr hac)
  apply hbc
  apply mul_left_cancel₀ htwo
  linear_combination hb'-hc'

noncomputable def weightedCount (K : F → F → ℝ) (x y : F) : ℝ :=
  ∑ u : F, ∑ v : F, K u v*(pairCount (line u) (line v) (x,y):ℝ)

lemma weighted_identity (K : F → F → ℝ) (x y : F) :
    weightedCount K x y-(∑ u : F, ∑ v : F, K u v)=
      (Fintype.card F:ℝ)*(∑ u : F, if y=u*x+2*u^2 then K u u else 0)-
        ∑ u : F, K u u := by
  unfold weightedCount
  rw [←Finset.sum_sub_distrib]
  have he (u : F) :
      (∑ v : F, K u v*(pairCount (line u) (line v) (x,y):ℝ))-
        (∑ v : F, K u v)=
        (Fintype.card F:ℝ)*(if y=u*x+2*u^2 then K u u else 0)-K u u := by
    rw [←Finset.sum_sub_distrib]
    calc
      _ = ∑ v : F, if u=v then
          (Fintype.card F:ℝ)*(if y=u*x+2*u^2 then K u u else 0)-K u u else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases huv : u=v
        · subst v
          rw [if_pos rfl,line_pair_same]
          split_ifs <;> push_cast <;> ring
        · rw [if_neg huv,line_pair_different u v x y huv]
          norm_num
      _ = _ := by simp
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]

/-- Only the diagonal color bounds enter the error. Off-diagonal mixed
counts of the old color classes need not be bounded. -/
theorem weighted_error (htwo : (2:F)≠0) (K : F → F → ℝ) (g : ℝ)
    (hg : 0≤g) (hK : ∀ u, 0≤K u u ∧ K u u≤g) (x y : F) :
    |weightedCount K x y-(∑ u : F, ∑ v : F, K u v)|≤2*Fintype.card F*g := by
  rw [weighted_identity]
  have h₀ : 0≤∑ u : F, K u u := Finset.sum_nonneg (fun u _ ↦ (hK u).1)
  have h₁ : (∑ u : F, K u u)≤Fintype.card F*g := by
    calc
      _ ≤ ∑ _u : F, g := Finset.sum_le_sum (fun u _ ↦ (hK u).2)
      _ = _ := by simp
  have h₂ : 0≤∑ u : F, if y=u*x+2*u^2 then K u u else 0 := by
    apply Finset.sum_nonneg
    intro u hu
    split_ifs
    · exact (hK u).1
    · rfl
  have h₃ : (∑ u : F, if y=u*x+2*u^2 then K u u else 0)≤2*g := by
    rw [←Finset.sum_filter]
    calc
      _ ≤ ∑ _u∈Finset.univ.filter (fun u : F ↦ y=u*x+2*u^2), g :=
        Finset.sum_le_sum (fun u _ ↦ (hK u).2)
      _ ≤ 2*g := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ hg
        exact_mod_cast concurrent_card htwo x y
  have hp : (0:ℝ)≤Fintype.card F := by positivity
  rw [abs_le]
  constructor <;> nlinarith

end Erdos66AffineLineKernel
