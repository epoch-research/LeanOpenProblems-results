import FormalConjecturesUtil
import Submission.ReciprocalStar

/-! A norm-preserving change of parameters in the product octad.
It has period two up to similarity, so it is not by itself a growth rule. -/
namespace Erdos213.ProductCayley
open ReciprocalStar
set_option maxHeartbeats 2000000

noncomputable def cayley (b : ℂ) : ℂ := (b-1)/(b+1)

structure Input (b c : ℂ) : Prop where
  rb : RationalNorm b
  rc : RationalNorm c
  b1 : Compatible b 1
  c1 : Compatible c 1
  bc : Compatible b c
  product : Compatible (b*c) 1

lemma cayley_sub_one (b : ℂ) (hb : b+1 ≠ 0) : cayley b-1 = -2/(b+1) := by
  unfold cayley
  field_simp
  ring

lemma cayley_add_one (b : ℂ) (hb : b+1 ≠ 0) : cayley b+1 = 2*b/(b+1) := by
  unfold cayley
  field_simp
  ring

lemma cross_sub (b c : ℂ) (hb : b+1 ≠ 0) (hc : c+1 ≠ 0) :
    cayley b-cayley c = 2*(b-c)/((b+1)*(c+1)) := by
  unfold cayley
  field_simp
  ring

lemma cross_add (b c : ℂ) (hb : b+1 ≠ 0) (hc : c+1 ≠ 0) :
    cayley b+cayley c = 2*(b*c-1)/((b+1)*(c+1)) := by
  unfold cayley
  field_simp
  ring

lemma product_sub (b c : ℂ) (hb : b+1 ≠ 0) (hc : c+1 ≠ 0) :
    cayley b*cayley c-1 = -2*(b+c)/((b+1)*(c+1)) := by
  unfold cayley
  field_simp
  ring

lemma product_add (b c : ℂ) (hb : b+1 ≠ 0) (hc : c+1 ≠ 0) :
    cayley b*cayley c+1 = 2*(b*c+1)/((b+1)*(c+1)) := by
  unfold cayley
  field_simp
  ring

/-- All ten factor-norm requirements are preserved. This is not an assertion
that parameters satisfying them exist in general position. -/
theorem preserves_input {b c : ℂ} (h : Input b c) (hb : b+1 ≠ 0) (hc : c+1 ≠ 0) :
    Input (cayley b) (cayley c) := by
  have h2 : RationalNorm (2 : ℂ) := ⟨2,by norm_num⟩
  have hn2 : RationalNorm (-2 : ℂ) := ⟨2,by norm_num⟩
  have hden : RationalNorm ((b+1)*(c+1)) := h.b1.2.mul h.c1.2
  refine ⟨h.b1.1.div h.b1.2,h.c1.1.div h.c1.2,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · rw [cayley_sub_one b hb]; exact hn2.div h.b1.2
  · rw [cayley_add_one b hb]; exact (h2.mul h.rb).div h.b1.2
  · rw [cayley_sub_one c hc]; exact hn2.div h.c1.2
  · rw [cayley_add_one c hc]; exact (h2.mul h.rc).div h.c1.2
  · rw [cross_sub b c hb hc]; exact (h2.mul h.bc.1).div hden
  · rw [cross_add b c hb hc]; exact (h2.mul h.product.1).div hden
  · rw [product_sub b c hb hc]; exact (hn2.mul h.bc.2).div hden
  · rw [product_add b c hb hc]; exact (h2.mul h.product.2).div hden

lemma cayley_twice (b : ℂ) (hb : b+1 ≠ 0) (hb0 : b ≠ 0) :
    cayley (cayley b) = -1/b := by
  change (cayley b-1)/(cayley b+1) = -1/b
  rw [cayley_sub_one b hb,cayley_add_one b hb]
  field_simp [hb,hb0]

noncomputable def point (b c : ℂ) : Fin 8 → ℂ := ![1,-1,b,-b,c,-c,b*c,-b*c]
def twiceIndex : Fin 8 → Fin 8 := ![6,7,5,4,3,2,0,1]

lemma twiceIndex_involution : Function.Involutive twiceIndex := by
  change ∀ i : Fin 8, twiceIndex (twiceIndex i)=i
  decide

/-- After two simultaneous parameter changes, the octad is a uniformly
rescaled and relabelled copy of the original one. -/
theorem point_two_steps (b c : ℂ) (hb : b+1 ≠ 0) (hc : c+1 ≠ 0)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0) (i : Fin 8) :
    point (cayley (cayley b)) (cayley (cayley c)) i =
      point b c (twiceIndex i)/(b*c) := by
  rw [cayley_twice b hb hb0,cayley_twice c hc hc0]
  fin_cases i <;> dsimp [point,twiceIndex]
  all_goals field_simp

lemma distance_two_steps (b c : ℂ) (hb : b+1 ≠ 0) (hc : c+1 ≠ 0)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0) (i j : Fin 8) :
    dist (point (cayley (cayley b)) (cayley (cayley c)) i)
      (point (cayley (cayley b)) (cayley (cayley c)) j) =
    dist (point b c (twiceIndex i)) (point b c (twiceIndex j))/‖b*c‖ := by
  rw [point_two_steps b c hb hc hb0 hc0,point_two_steps b c hb hc hb0 hc0]
  simp only [dist_eq_norm,← sub_div,norm_div]

#print axioms preserves_input
#print axioms cayley_twice
#print axioms point_two_steps
#print axioms distance_two_steps
end Erdos213.ProductCayley
