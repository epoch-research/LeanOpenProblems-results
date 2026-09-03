import Submission.StoppingPreimage

/-! Private points in a predictable digit restriction. Active shortened
classes cannot disappear when a projected subcover is made irredundant.
This is a structural lemma, not a solution of the odd covering problem. -/
namespace Erdos7StoppingPrivatePoints
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7AllDigits
open Erdos7StoppingDigitRestriction Erdos7StoppingPreimage
set_option autoImplicit false
set_option maxHeartbeats 3000000

lemma agree_delete {α : Type*} {n : ℕ} (t : Fin n) (d : α) (y : Fin n → α) :
    Agree t.val y (deleteDigit t d y) := by
  intro j hj
  simp [deleteDigit,hj]

lemma insert_delete {α : Type*} {n : ℕ} (t : Fin n) (d : α) (y : Fin n → α) :
    insertDigit t (y t) (deleteDigit t d y) = y := by
  funext j
  by_cases hj : j.val < t.val
  · simp [insertDigit,deleteDigit,hj]
  · by_cases hje : j=t
    · subst j; simp
    · have htj : t.val < j.val := by
        have hne : j.val ≠ t.val := fun h => hje (Fin.ext h)
        omega
      let u : Fin n := ⟨j.val-1,by have := j.isLt; omega⟩
      have hu : ¬ u.val < t.val := by dsimp [u]; omega
      have hun : u.val+1 < n := by dsimp [u]; have := j.isLt; omega
      have hui : (⟨u.val+1,hun⟩ : Fin n)=j := Fin.ext (by dsimp [u]; omega)
      change (if j.val < t.val then _ else if j=t then _ else deleteDigit t d y u)=y j
      rw [if_neg hj,if_neg hje]
      simp only [deleteDigit,if_neg hu,dif_pos hun,hui]

/-- Exact inverse-image description of an individual prefix cylinder. -/
theorem prefix_preimage_iff {α : Type*} {n e : ℕ}
    (T : (Fin n → α) → Fin n) (V : (Fin n → α) → α)
    (hT : Predictable T) (hV : PredictableValue T V)
    (d : α) (he : e ≤ n) (x a : Fin n → α) :
    Agree e (insertDigit (T x) (V x) x) a ↔
      (e ≤ (T a).val ∨ a (T a)=V a) ∧
        Agree (eraseLevel (T a).val e) x (deleteDigit (T a) d a) := by
  constructor
  · intro hmatch
    have hTY : T (insertDigit (T x) (V x) x)=T x := predictable_insert T hT x (V x)
    have hcases : T a=T x ∨ (e ≤ (T a).val ∧ e ≤ (T x).val) := by
      simpa only [hTY] using predictable_agree T hT a _ hmatch.symm
    constructor
    · by_cases hlow : e ≤ (T a).val
      · exact Or.inl hlow
      · have ht : T a=T x := hcases.resolve_right (fun h => hlow h.1)
        have hte : (T x).val < e := by omega
        have hpref : Agree (T x).val x a := by
          intro j hj
          have hh := hmatch j (hj.trans hte)
          simpa only [insertDigit,if_pos hj] using hh
        have hv := hmatch (T x) hte
        rw [insertDigit_self] at hv
        right
        rw [ht]
        exact hv.symm.trans (hV x a hpref).symm
    · rcases hcases with ht | ⟨hta,htx⟩
      · rw [ht]
        exact prefix_agreement_after_deletion (T x) (V x) d x a e he hmatch
      · intro j hj
        have hje : j.val < e := hj.trans_le (eraseLevel_le _ _)
        have hja := hje.trans_le hta
        have hjx := hje.trans_le htx
        have hh := hmatch j hje
        simpa only [insertDigit,deleteDigit,if_pos hja,if_pos hjx] using hh
  · rintro ⟨ha,hh⟩
    exact stopping_agreement_lift T V hT hV d x a e he ha hh

/-- Deletion and insertion are inverse at every retained word. -/
theorem retained_reconstruction {α : Type*} {n : ℕ}
    (T : (Fin n → α) → Fin n) (V : (Fin n → α) → α)
    (hT : Predictable T) (hV : PredictableValue T V)
    (d : α) (y : Fin n → α) (hy : y (T y)=V y) :
    insertDigit (T (deleteDigit (T y) d y)) (V (deleteDigit (T y) d y))
      (deleteDigit (T y) d y)=y := by
  rw [hT y _ (agree_delete _ _ _),hV y _ (agree_delete _ _ _),←hy]
  exact insert_delete (T y) d y

/-- Every point of an active shortened class lies in the retained section. -/
theorem shortened_retained {α : Type*} {n e : ℕ}
    (T : (Fin n → α) → Fin n) (V : (Fin n → α) → α)
    (hT : Predictable T) (hV : PredictableValue T V)
    (a y : Fin n → α) (ht : (T a).val < e)
    (ha : a (T a)=V a) (hy : Agree e y a) : y (T y)=V y := by
  have hpre : Agree (T a).val a y := hy.symm.mono ht.le
  rw [hT a y hpre,hV a y hpre,hy (T a) ht]
  exact ha

section Product
variable {ι κ : Type*} [DecidableEq ι] {A : ι → Type*} {E : ι → ℕ}
    (i₀ : ι) (T : (Fin (E i₀) → A i₀) → Fin (E i₀))
    (V : (Fin (E i₀) → A i₀) → A i₀)
    (e : κ → ι → ℕ) (a : κ → (i : ι) → Fin (E i) → A i)

/-- Original prefix boxes in a product of digit spaces. -/
def Hit (k : κ) (y : (i : ι) → Fin (E i) → A i) : Prop :=
  ∀ i, Agree (e k i) (y i) (a k i)

/-- The active projected boxes, with a separate decision for each residue. -/
def ProjectedHit (d : A i₀) (k : κ) (x : (i : ι) → Fin (E i) → A i) : Prop :=
  (e k i₀ ≤ (T (a k i₀)).val ∨ a k i₀ (T (a k i₀))=V (a k i₀)) ∧
    ∀ i, Agree (eraseExponent i₀ (T (a k i₀)).val (e k) i) (x i)
      ((Function.update (a k) i₀ (deleteDigit (T (a k i₀)) d (a k i₀))) i)

/-- Simultaneous exact preimage identity; coverage is not assumed. -/
theorem hit_preimage_iff (hT : Predictable T) (hV : PredictableValue T V)
    (he : ∀ k i, e k i ≤ E i) (d : A i₀)
    (x : (i : ι) → Fin (E i) → A i) (k : κ) :
    Hit e a k (Function.update x i₀ (insertDigit (T (x i₀)) (V (x i₀)) (x i₀))) ↔
      ProjectedHit i₀ T V e a d k x := by
  constructor
  · intro hh
    have hroot := (prefix_preimage_iff T V hT hV d (he k i₀) (x i₀) (a k i₀)).mp
      (by simpa only [Hit,Function.update_self] using hh i₀)
    refine ⟨hroot.1,fun i => ?_⟩
    by_cases hi : i=i₀
    · subst i
      simpa only [eraseExponent_self,Function.update_self] using hroot.2
    · simpa only [eraseExponent_of_ne _ _ _ hi,Function.update_of_ne hi] using hh i
  · rintro ⟨ha,hh⟩ i
    by_cases hi : i=i₀
    · subst i
      simp only [Function.update_self]
      apply (prefix_preimage_iff T V hT hV d (he k i₀) (x i₀) (a k i₀)).mpr
      exact ⟨ha,by simpa only [eraseExponent_self,Function.update_self] using hh i₀⟩
    · simpa only [eraseExponent_of_ne _ _ _ hi,Function.update_of_ne hi] using hh i

/-- A retained private point projects to a private point. This also covers
unshortened classes whenever a particular private point is retained. -/
theorem retained_private_point (hT : Predictable T) (hV : PredictableValue T V)
    (he : ∀ k i, e k i ≤ E i) (d : A i₀)
    (k : κ) (y : (i : ι) → Fin (E i) → A i)
    (hpriv : ∀ l, Hit e a l y ↔ l=k) (hy : y i₀ (T (y i₀))=V (y i₀)) :
    ∃ x : (i : ι) → Fin (E i) → A i, ∀ l, ProjectedHit i₀ T V e a d l x ↔ l=k := by
  let x := Function.update y i₀ (deleteDigit (T (y i₀)) d (y i₀))
  have hinsert : Function.update x i₀ (insertDigit (T (x i₀)) (V (x i₀)) (x i₀))=y := by
    funext i
    by_cases hi : i=i₀
    · subst i
      simp only [x,Function.update_self]
      exact retained_reconstruction T V hT hV d (y i₀) hy
    · simp [x,hi]
  refine ⟨x,fun l => ?_⟩
  rw [←hit_preimage_iff i₀ T V e a hT hV he d x l,hinsert]
  exact hpriv l

/-- Every active shortened class in an irredundant family has a private
point in the projected family. No global coverage assumption is needed. -/
theorem shortened_private_point (hT : Predictable T) (hV : PredictableValue T V)
    (he : ∀ k i, e k i ≤ E i) (d : A i₀)
    (k : κ) (hpriv : ∃ y, ∀ l, Hit e a l y ↔ l=k)
    (ht : (T (a k i₀)).val < e k i₀)
    (ha : a k i₀ (T (a k i₀))=V (a k i₀)) :
    ∃ x : (i : ι) → Fin (E i) → A i, ∀ l, ProjectedHit i₀ T V e a d l x ↔ l=k := by
  obtain ⟨y,hy⟩ := hpriv
  have hky := (hy k).mpr rfl
  apply retained_private_point i₀ T V e a hT hV he d k y hy
  exact shortened_retained T V hT hV (a k i₀) (y i₀) ht ha (hky i₀)

/-- Any subfamily preserving the projected union must retain all active
shortened classes which had original private points. -/
theorem shortened_mem_subcover (hT : Predictable T) (hV : PredictableValue T V)
    (he : ∀ k i, e k i ≤ E i) (d : A i₀) (S : κ → Prop)
    (hS : ∀ x, (∃ l, ProjectedHit i₀ T V e a d l x) →
      ∃ l, S l ∧ ProjectedHit i₀ T V e a d l x)
    (k : κ) (hpriv : ∃ y, ∀ l, Hit e a l y ↔ l=k)
    (ht : (T (a k i₀)).val < e k i₀)
    (ha : a k i₀ (T (a k i₀))=V (a k i₀)) : S k := by
  obtain ⟨x,hx⟩ := shortened_private_point i₀ T V e a hT hV he d k hpriv ht ha
  obtain ⟨l,hl,hhit⟩ := hS x ⟨k,(hx k).mpr rfl⟩
  exact (hx l).mp hhit ▸ hl
end Product

#print axioms shortened_mem_subcover
#print axioms shortened_private_point
#print axioms hit_preimage_iff
end Erdos7StoppingPrivatePoints
