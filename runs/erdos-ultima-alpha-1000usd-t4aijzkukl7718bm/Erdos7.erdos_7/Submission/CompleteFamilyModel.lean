import Submission.ArithmeticReduction
import Submission.KernelFamilyCompression

/-! Normalized complete exponent-pattern families on a fixed finite product.
This is an arithmetic-model component, not a solution of the odd covering problem. -/
namespace Erdos7CompleteFamilyModel
open scoped BigOperators
open Erdos7KilledSieve Erdos7CompressionSieve Erdos7Distortion
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {n : ℕ}

def project (t : ℕ) (e : Fin n → ℕ) (i : Fin n) : ℕ :=
  if i.val < t then e i else 0

lemma project_prefix (E e : Fin n → ℕ) (he : ∀ i, e i  ≤  E i) (t : ℕ) :
    PrefixPattern E t (project t e) := by
  constructor
  · intro i; dsimp only [project]; split_ifs
    · exact he i
    · exact Nat.zero_le _
  · intro i hi; simp only [project, if_neg (by omega : ¬i.val < t)]

lemma project_zero (e : Fin n → ℕ) : project 0 e = fun _ => 0 := by
  funext i; simp [project]

lemma project_erase (e : Fin n → ℕ) (t : ℕ) (ht : t < n) :
    Function.update (project (t+1) e) ⟨t,ht⟩ 0 = project t e := by
  funext j
  by_cases hj : j = ⟨t,ht⟩
  · subst j; simp [project]
  · have hjv : j.val≠t := fun h => hj (Fin.ext h)
    simp only [Function.update_of_ne hj, project]
    split_ifs  <;> omega

lemma project_current (e : Fin n → ℕ) (t : ℕ) (ht : t < n) :
    project (t+1) e ⟨t,ht⟩ = e ⟨t,ht⟩ := by simp [project]

/-- Pattern capacity of the first t coordinates. -/
def capacity (E : Fin n → ℕ) : ℕ → ℕ
  | 0 => 1
  | t+1 => if h:t < n then (E ⟨t,h⟩+1)*capacity E t else capacity E t

lemma capacity_pos (E : Fin n → ℕ) (t : ℕ) : 0 < capacity E t := by
  induction t with
  | zero => simp [capacity]
  | succ t ih => simp only [capacity]; split_ifs  <;> positivity

lemma capacity_succ (E : Fin n → ℕ) (t : ℕ) (ht : t < n) :
    capacity E (t+1) = (E ⟨t,ht⟩+1)*capacity E t := by simp [capacity,ht]

variable {κ : Type} [DecidableEq κ]

/-- All residue sections stay fixed; only the selected labels and their
normalization change when a coordinate is projected away. -/
structure Family (E : Fin n → ℕ) (e : κ → Fin n → ℕ) (t : ℕ) where
  labels : Finset κ
  multiplicity : ℕ
  positive : 0 < multiplicity
  complete : CompletePatterns E t labels (fun k => project t (e k)) multiplicity

namespace Family
variable {E : Fin n → ℕ} {e : κ → Fin n → ℕ} {t : ℕ}

noncomputable def truncate (b : Family E e (t+1)) (ht : t < n) (a : ℕ)
    (ha : a  ≤  E ⟨t,ht⟩) : Family E e t where
  labels := b.labels.filter (fun k => e k ⟨t,ht⟩  ≤  a)
  multiplicity := (a+1)*b.multiplicity
  positive := Nat.mul_pos (by omega) b.positive
  complete := by
    have hh := completePatterns_erase E t ht b.labels (fun k => project (t+1) (e k))
      b.multiplicity b.complete a ha
    simpa only [project_current,project_erase] using hh

lemma labels_card (he : ∀ k i, e k i  ≤  E i) (b : Family E e t) (ht : t ≤ n) :
    b.labels.card = capacity E t*b.multiplicity := by
  induction t with
  | zero =>
    have hh := b.complete _ (prefixPattern_zero E 0)
    simpa only [project_zero, Finset.filter_true,capacity,one_mul] using hh
  | succ t ih =>
    have htn : t < n := by omega
    let b' := b.truncate htn (E ⟨t,htn⟩) le_rfl
    have hlabels : b'.labels = b.labels := by
      dsimp only [b',truncate]
      exact Finset.filter_true_of_mem (fun k _ => he k _)
    have hh := ih b' (by omega)
    rw [hlabels] at hh
    rw [capacity_succ E t htn]
    dsimp only [b',truncate] at hh
    nlinarith [hh]

end Family

section Counts
variable (A : Fin n → Type) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
  [∀ i, DecidableEq (A i)]
variable (X : κ → ∀ i, Finset (A i))

noncomputable def indicator (t : ℕ) (e : Fin n → ℕ) (X : ∀ i, Finset (A i))
    (x : ∀ i,A i) : ℝ := (boxIndicator A (expSupport (project t e)) X x:ℚ)

lemma indicator_nonneg (t : ℕ) (e : Fin n → ℕ) (X : ∀ i, Finset (A i))
    (x : ∀ i,A i) : 0  ≤  indicator A t e X x := by
  dsimp only [indicator]
  exact_mod_cast boxIndicator_nonneg A (expSupport (project t e)) X x

lemma indicator_le_one (t : ℕ) (e : Fin n → ℕ) (X : ∀ i, Finset (A i))
    (x : ∀ i,A i) : indicator A t e X x  ≤  1 := by
  dsimp only [indicator,boxIndicator]
  split_ifs  <;> norm_num

lemma indicator_zero (e : Fin n → ℕ) (X : ∀ i, Finset (A i)) (x : ∀ i,A i) :
    indicator A 0 e X x = 1 := by
  simp [indicator,project_zero,expSupport,boxIndicator_empty]

lemma indicator_update (t : ℕ) (e : Fin n → ℕ) (X : ∀ i, Finset (A i))
    (i : Fin n) (hi : t ≤ i.val) (x : ∀ i,A i) (y : A i) :
    indicator A t e X (Function.update x i y) = indicator A t e X x := by
  apply congrArg (fun z : ℚ => (z:ℝ))
  apply boxIndicator_update
  simp only [mem_expSupport,project,if_neg (by omega : ¬i.val < t),ne_eq,not_not]

lemma indicator_step (t : ℕ) (ht : t < n) (e : Fin n → ℕ)
    (X : ∀ i, Finset (A i)) (x : ∀ i,A i) (y : A ⟨t,ht⟩) :
    indicator A (t+1) e X (Function.update x ⟨t,ht⟩ y)  = 
      if e ⟨t,ht⟩ = 0 ∨ y∈X ⟨t,ht⟩ then indicator A t e X x else 0 := by
  classical
  let i : Fin n := ⟨t,ht⟩
  have herase : (expSupport (project (t+1) e)).erase i  =  expSupport (project t e) := by
    rw [← expSupport_update_zero,project_erase]
  by_cases he : e i = 0
  · have hi : i∉expSupport (project (t+1) e) := by simp [mem_expSupport,project_current,i,he]
    have heq : expSupport (project (t+1) e) = expSupport (project t e) := by
      rw [← herase,Finset.erase_eq_of_notMem hi]
    simp only [indicator,heq]
    rw [boxIndicator_update A _ X i (by simpa only [← heq] using hi)]
    simp only [show e ⟨t,ht⟩ = 0 from he,true_or,if_true]
  · have hi : i∈expSupport (project (t+1) e) := by simpa only [mem_expSupport,project_current,i] using he
    rw [indicator,boxIndicator_erase A _ X i hi,herase]
    simp only [i,Function.update_self]
    rw [boxIndicator_update A _ X i (by simp [mem_expSupport,project,i])]
    simp only [show ¬e ⟨t,ht⟩ = 0 from he,false_or,indicator]
    split_ifs  <;> simp

noncomputable def count {E : Fin n → ℕ} {e : κ → Fin n → ℕ} {t : ℕ}
    (b : Family E e t) (x : ∀ i,A i) : ℝ :=
  (∑ k∈b.labels,indicator A t (e k) (X k) x)/(b.multiplicity:ℝ)

lemma count_lower {E : Fin n → ℕ} {e : κ → Fin n → ℕ} {t : ℕ}
    (b : Family E e t) (x : ∀ i,A i) : 1  ≤  count A X b x := by
  have hpos : (0:ℝ) < b.multiplicity := by exact_mod_cast b.positive
  apply (le_div_iff₀ hpos).mpr
  rw [one_mul]
  have hh := completePatterns_boxCount_lower A E t b.labels (fun k => project t (e k))
    b.multiplicity b.complete X x
  dsimp only [indicator]
  exact_mod_cast hh

lemma count_upper {E : Fin n → ℕ} {e : κ → Fin n → ℕ} {t : ℕ}
    (he : ∀ k i,e k i  ≤  E i) (b : Family E e t) (ht : t ≤ n) (x : ∀ i,A i) :
    count A X b x  ≤  capacity E t := by
  have hpos : (0:ℝ) < b.multiplicity := by exact_mod_cast b.positive
  apply (div_le_iff₀ hpos).mpr
  calc
    _  ≤  ∑ _k∈b.labels,(1:ℝ) := Finset.sum_le_sum (fun k _ => indicator_le_one A t (e k) (X k) x)
    _  =  _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one]; exact_mod_cast b.labels_card he ht

lemma count_initial {E : Fin n → ℕ} {e : κ → Fin n → ℕ}
    (b : Family E e 0) (x : ∀ i,A i) : count A X b x = 1 := by
  have hc : b.labels.card = b.multiplicity := by
    have hh := b.complete _ (prefixPattern_zero E 0)
    simpa only [project_zero,Finset.filter_true] using hh
  simp [count,indicator_zero,hc,ne_of_gt b.positive]

lemma count_update {E : Fin n → ℕ} {e : κ → Fin n → ℕ} {t : ℕ}
    (b : Family E e t) (i : Fin n) (hi : t ≤ i.val) (x : ∀ i,A i) (y : A i) :
    count A X b (Function.update x i y) = count A X b x := by
  simp only [count,indicator_update A t _ _ i hi]

end Counts
end Erdos7CompleteFamilyModel
