import Submission.CompleteFamilyCompression

/-! Full finite exponent rectangles, slices, and current-coordinate bad sets. -/
namespace Erdos7CompleteFamilyModel
open scoped BigOperators
open Erdos7KilledSieve
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {n : ℕ}
abbrev Pattern (E : Fin n → ℕ) := ∀ i, Fin (E i+1)
def exponent (E : Fin n → ℕ) (k : Pattern E) (i : Fin n) : ℕ := (k i).val
lemma exponent_bound (E : Fin n → ℕ) (k : Pattern E) (i : Fin n) :
    exponent E k i ≤ E i := by exact Nat.le_of_lt_succ (k i).isLt

lemma exponent_injective (E : Fin n → ℕ) : Function.Injective (exponent E) := by
  intro k l h
  funext i
  exact Fin.ext (congrFun h i)

/-- The unprocessed exponents are fixed, while every prefix exponent occurs. -/
noncomputable def sliceFamily (E : Fin n → ℕ) (t : ℕ) (v : Pattern E) :
    Family E (exponent E) t := by
  classical
  refine ⟨Finset.univ.filter (fun k => ∀ j, t ≤ j.val → k j = v j),1,by omega,?_⟩
  intro f hf
  let k : Pattern E := fun j => if j.val < t then ⟨f j,by have := hf.1 j; omega⟩ else v j
  have hk : ∀ j, t ≤ j.val → k j = v j := by intro j hj; simp [k,not_lt.mpr hj]
  have hproj : project t (exponent E k) = f := by
    funext j
    by_cases hj : j.val < t
    · simp [project,exponent,k,hj]
    · simp [project,hj,hf.2 j (Nat.le_of_not_gt hj)]
  have heq : (Finset.univ.filter (fun k : Pattern E => ∀ j, t ≤ j.val → k j = v j)).filter
      (fun k => project t (exponent E k) = f) = {k} := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · rintro ⟨hl,he⟩
      funext j
      by_cases hj : j.val < t
      · apply Fin.ext
        have hh := congrFun he j
        simpa [project,exponent,k,hj] using hh
      · rw [hl j (Nat.le_of_not_gt hj)]
        simp [k,hj]
    · rintro rfl
      exact ⟨hk,hproj⟩
  rw [heq,Finset.card_singleton]

lemma sliceFamily_labels (E : Fin n → ℕ) (t : ℕ) (v k : Pattern E) :
    k ∈ (sliceFamily E t v).labels ↔ ∀ j, t ≤ j.val → k j = v j := by
  classical
  simp [sliceFamily]

lemma sliceFamily_multiplicity (E : Fin n → ℕ) (t : ℕ) (v : Pattern E) :
    (sliceFamily E t v).multiplicity = 1 := rfl

instance family_nonempty (E : Fin n → ℕ) (t : ℕ) : Nonempty (Family E (exponent E) t) :=
  ⟨sliceFamily E t (fun _ => 0)⟩

noncomputable def currentFamily (E : Fin n → ℕ) (t : ℕ) (ht : t < n)
    (a : Fin (E ⟨t,ht⟩)) : Family E (exponent E) t :=
  sliceFamily E t (Function.update (fun _ => 0) ⟨t,ht⟩ ⟨a.val+1,by omega⟩)

lemma currentFamily_labels (E : Fin n → ℕ) (t : ℕ) (ht : t < n)
    (a : Fin (E ⟨t,ht⟩)) (k : Pattern E) :
    k ∈ (currentFamily E t ht a).labels ↔
      exponent E k ⟨t,ht⟩ = a.val+1 ∧
      ∀ j, t+1 ≤ j.val → exponent E k j = 0 := by
  rw [currentFamily,sliceFamily_labels]
  constructor
  · intro hk
    constructor
    · have hh := congrArg Fin.val (hk ⟨t,ht⟩ le_rfl)
      simpa only [Function.update_self,exponent] using hh
    · intro j hj
      have hji : j ≠ ⟨t,ht⟩ := by intro h; subst j; simp only at hj; omega
      have hh := congrArg Fin.val (hk j (by omega))
      simpa only [Function.update_of_ne hji,Fin.val_zero,exponent] using hh
  · rintro ⟨ha,hzero⟩ j hj
    by_cases hji : j = ⟨t,ht⟩
    · subst j; rw [Function.update_self]; exact Fin.ext ha
    · have hjv : j.val ≠ t := fun h => hji (Fin.ext h)
      rw [Function.update_of_ne hji]
      exact Fin.ext (hzero j (by omega))

section Bad
variable (A : Fin n → Type) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
  [∀ i, DecidableEq (A i)]
variable (E : Fin n → ℕ) (X : Pattern E → ∀ i, Finset (A i))

/-- The current coordinate's newly active boxes, written with actual slices. -/
def currentBad (t : ℕ) (ht : t < n) (x : ∀ i,A i) (y : A ⟨t,ht⟩) : Prop :=
  ∃ a : Fin (E ⟨t,ht⟩), ∃ k ∈ (currentFamily E t ht a).labels,
    indicator A t (exponent E k) (X k) x = 1 ∧ y ∈ X k ⟨t,ht⟩

lemma indicator_eq_zero_or_one (t : ℕ) (e : Fin n → ℕ)
    (X : ∀ i,Finset (A i)) (x : ∀ i,A i) :
    indicator A t e X x = 0 ∨ indicator A t e X x = 1 := by
  dsimp only [indicator,Erdos7Distortion.boxIndicator]
  split_ifs <;> simp

/-- A finite, positively weighted union bound, with an actual indicator weight. -/
lemma weighted_event_union_bound {I B : Type} [Fintype I] [Fintype B]
    (ρ : B → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (w r : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hit : I → B → Prop) [∀ i y, Decidable (hit i y)]
    (bad : B → Prop) [DecidablePred bad]
    (hbad : ∀ y, bad y → ∃ i, w i = 1 ∧ hit i y)
    (hd : ∀ i, (∑ y, if hit i y then ρ y else 0) ≤ r i) :
    (∑ y, if bad y then ρ y else 0) ≤ ∑ i,w i*r i := by
  classical
  calc
    _ ≤ ∑ y, ∑ i, w i*(if hit i y then ρ y else 0) := by
      apply Finset.sum_le_sum
      intro y _
      have hnonneg (i : I) : 0 ≤ w i*(if hit i y then ρ y else 0) := by
        apply mul_nonneg (hw i)
        split_ifs <;> [exact hρ y; exact le_rfl]
      by_cases hb : bad y
      · obtain ⟨i,hi,hh⟩ := hbad y hb
        rw [if_pos hb]
        have hl := Finset.single_le_sum (s := Finset.univ) (fun j _ => hnonneg j) (Finset.mem_univ i)
        simpa only [hi,if_pos hh,one_mul] using hl
      · rw [if_neg hb]
        exact Finset.sum_nonneg (fun i _ => hnonneg i)
    _ = ∑ i,w i*(∑ y,if hit i y then ρ y else 0) := by
      rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (hw i))

attribute [local instance] Classical.propDecidable

lemma currentBad_density (t : ℕ) (ht : t < n) (x : ∀ i,A i)
    (ρ : A ⟨t,ht⟩ → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (r : ℕ → ℝ)
    (hd : ∀ k : Pattern E, exponent E k ⟨t,ht⟩ ≠ 0 →
      (∑ y,if y ∈ X k ⟨t,ht⟩ then ρ y else 0) ≤ r (exponent E k ⟨t,ht⟩-1)) :
    (∑ y,if currentBad A E X t ht x y then ρ y else 0) ≤
      ∑ a : Fin (E ⟨t,ht⟩), r a.val * count A X (currentFamily E t ht a) x := by
  classical
  let I := (a : Fin (E ⟨t,ht⟩)) × ↥(currentFamily E t ht a).labels
  have hh := weighted_event_union_bound ρ hρ
    (fun z : I => indicator A t (exponent E z.2.val) (X z.2.val) x)
    (fun z : I => r z.1.val)
    (fun z => indicator_nonneg A t (exponent E z.2.val) (X z.2.val) x)
    (fun z y => y ∈ X z.2.val ⟨t,ht⟩) (currentBad A E X t ht x) ?_ ?_
  · apply hh.trans_eq
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro a _
    simp only [count,currentFamily,sliceFamily_multiplicity,Nat.cast_one,div_one]
    change (∑ k : ↥(currentFamily E t ht a).labels,
      indicator A t (exponent E k.val) (X k.val) x * r a.val) = _
    rw [Finset.mul_sum]
    have hs := Finset.sum_coe_sort (currentFamily E t ht a).labels
      (fun k => indicator A t (exponent E k) (X k) x * r a.val)
    apply hs.trans
    apply Finset.sum_congr rfl
    intro k _; ring
  · intro y hy
    obtain ⟨a,k,hk,hind,hhit⟩ := hy
    exact ⟨⟨a,⟨k,hk⟩⟩,hind,hhit⟩
  · intro z
    have hz := (currentFamily_labels E t ht z.1 z.2.val).mp z.2.property
    have hd' := hd z.2.val (by rw [hz.1]; omega)
    simpa only [hz.1,Nat.add_sub_cancel] using hd'

end Bad
#print axioms currentBad_density
#print axioms sliceFamily
end Erdos7CompleteFamilyModel
