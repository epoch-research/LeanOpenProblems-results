import Submission.PrefixFaithfulParabolaLiftExplore
import Submission.IntegerBlockExplore

/-! Exact row and natural carry formulas for row-dependent faithful lifts.
No estimate of the restricted root sums is assumed. -/
namespace Erdos66TaperedFaithfulLift
open Erdos66PrefixFaithfulParabolaLift Erdos66ShearedParabolaPrefix
  Erdos66InheritedOriginLift Erdos66IntegerBlock AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1600000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def row (U : Finset F) (a y : F) : Finset F :=
  Finset.univ.filter (fun x ↦ (x,y) ∈ faithfulLift U a)

lemma mem_faithfulLift (U : Finset F) (a x y : F)
    (hU : ∀ u∈U, a+u ≠ 0) :
    (x,y)∈faithfulLift U a ↔
      x+a ≠ 0 ∧ ∃ u∈U, (x+a)^2=(y+x+a)*(a+u) := by
  unfold faithfulLift
  rw [Finset.mem_erase, mem_shiftSet]
  have he : (x,y)-(-a,0)=(x+a,y) := by ext <;> simp
  rw [he, mem_sheared]
  constructor
  · rintro ⟨hneq,v,hv,hvEq⟩
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    have hmul := (eq_div_iff (hU u hu)).mp hvEq
    have hx : x+a ≠ 0 := by
      intro hx
      have hy : y=0 := by
        rw [hx, zero_pow (by norm_num : (2:ℕ)≠0), zero_div, add_zero] at hvEq
        exact hvEq
      apply hneq
      exact Prod.ext (by linear_combination hx) hy
    refine ⟨hx,u,hu,?_⟩
    linear_combination -hmul
  · rintro ⟨hx,u,hu,heq⟩
    refine ⟨?_,a+u,Finset.mem_image.mpr ⟨u,hu,rfl⟩,?_⟩
    · intro hz
      have hz' := congrArg Prod.fst hz
      apply hx
      dsimp only at hz'
      linear_combination hz'
    · apply (eq_div_iff (hU u hu)).mpr
      linear_combination -heq

noncomputable def label (a x y : F) : F := (x+a)^2/(y+x+a)-a

lemma mem_row_label (U : Finset F) (a x y : F)
    (hU : ∀ u∈U, a+u ≠ 0) :
    x∈row U a y ↔ x+a ≠ 0 ∧ y+x+a ≠ 0 ∧ label a x y∈U := by
  simp only [row,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [mem_faithfulLift U a x y hU]
  constructor
  · rintro ⟨hx,u,hu,he⟩
    have hd : y+x+a ≠ 0 := by
      intro hz
      rw [hz,zero_mul] at he
      exact (pow_ne_zero 2 hx) he
    have hl : label a x y=u := by
      unfold label
      rw [he,mul_div_cancel_left₀ _ hd]
      ring
    exact ⟨hx,hd,hl ▸ hu⟩
  · rintro ⟨hx,hd,hu⟩
    refine ⟨hx,label a x y,hu,?_⟩
    unfold label
    field_simp
    <;> ring

lemma row_zero (U : Finset F) (a : F) (hU : ∀ u∈U, a+u ≠ 0) :
    row U a 0=U := by
  ext x
  rw [mem_row_label U a x 0 hU]
  simp only [zero_add]
  constructor
  · rintro ⟨hx,_,hu⟩
    have hl : label a x 0=x := by
      unfold label
      simp only [zero_add]
      rw [pow_two,mul_div_cancel_right₀ _ hx]
      ring
    simpa only [hl] using hu
  · intro hx
    have hxa : x+a ≠ 0 := by simpa only [add_comm] using hU x hx
    refine ⟨hxa,hxa,?_⟩
    have hl : label a x 0=x := by
      unfold label
      simp only [zero_add]
      rw [pow_two,mul_div_cancel_right₀ _ hxa]
      ring
    simpa only [hl] using hx

noncomputable def tapered (U : F → Finset F) (a : F) : Finset (F × F) :=
  Finset.univ.filter (fun z ↦ z.1∈row (U z.2) a z.2)

lemma tapered_first_row (U : F → Finset F) (a x : F)
    (hU : ∀ u∈U 0, a+u ≠ 0) :
    (x,0)∈tapered U a ↔ x∈U 0 := by
  simp only [tapered,Finset.mem_filter,Finset.mem_univ,true_and,row_zero _ a hU]

section Natural
variable {p : ℕ} [Fact p.Prime]

noncomputable def naturalRows (U : ZMod p → Finset (ZMod p)) (a : ZMod p)
    (k : ℕ) : Finset (ZMod p) :=
  if k<p then row (U (k:ZMod p)) a (k:ZMod p) else ∅

lemma encode_tapered_eq_blocks (U : ZMod p → Finset (ZMod p)) (a : ZMod p) :
    (encodePlane p (tapered U a):Set ℕ)=blockSet p (naturalRows U a) := by
  ext n
  change n∈encodePlane p (tapered U a) ↔ (n:ZMod p)∈naturalRows U a (n/p)
  constructor
  · rintro hn
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
    have hdiv : (z.1.val+p*z.2.val)/p=z.2.val := by
      rw [Nat.add_mul_div_left _ _ (NeZero.pos p), Nat.div_eq_of_lt z.1.val_lt, zero_add]
    have hcast : ((z.1.val+p*z.2.val:ℕ):ZMod p)=z.1 := by simp
    rw [hdiv,hcast,naturalRows,if_pos z.2.val_lt,ZMod.natCast_zmod_val]
    exact (Finset.mem_filter.mp hz).2
  · intro hn
    by_cases hk : n/p<p
    · rw [naturalRows,if_pos hk] at hn
      refine Finset.mem_image.mpr ⟨((n:ZMod p),(n/p:ℕ)),?_,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
      · simp only [ZMod.val_natCast,ZMod.val_natCast_of_lt hk]
        exact Nat.mod_add_div n p
    · simp only [naturalRows,if_neg hk,Finset.notMem_empty] at hn

/-- Both natural carry terms survive the row-dependent taper. -/
theorem tapered_natural_formula (U : ZMod p → Finset (ZMod p)) (a : ZMod p)
    (q t : ℕ) (ht : t<p) :
    sumRep (encodePlane p (tapered U a):Set ℕ) (q*p+t)=
      (∑ k∈Finset.range (q+1),
        lower p (naturalRows U a k) (naturalRows U a (q-k)) t)+
      ∑ k∈Finset.range q,
        upper p (naturalRows U a k) (naturalRows U a (q-k-1)) t := by
  rw [encode_tapered_eq_blocks]
  exact block_formula p _ q t ht

lemma tapered_encoded_prefix (U : ZMod p → Finset (ZMod p)) (a : ZMod p)
    (hU : ∀ u∈U 0, a+u ≠ 0) (n : ℕ) (hn : n<p) :
    n∈encodePlane p (tapered U a) ↔ (n:ZMod p)∈U 0 := by
  rw [encodePlane_prefix p _ n hn,tapered_first_row U a _ hU]

end Natural
end Erdos66TaperedFaithfulLift
