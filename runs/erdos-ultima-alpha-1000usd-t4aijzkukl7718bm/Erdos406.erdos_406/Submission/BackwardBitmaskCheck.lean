import Submission.BackwardNFAStrided

/-! Bitmask checks for strided simulations. This file supplies no missing-class witness. -/
namespace Erdos406BackwardBitmask
open Erdos406BackwardStandalone Erdos406BackwardStrided

def maskSet (N m : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun q => m.testBit q.val)

@[simp] lemma mem_maskSet {N m : ℕ} {q : Fin N} :
    q ∈ maskSet N m ↔ m.testBit q.val = true := by
  simp [maskSet]

lemma land_nonempty {N a b : ℕ} (ha : a < 2 ^ N) (hab : a &&& b ≠ 0) :
    (maskSet N a ∩ maskSet N b).Nonempty := by
  by_contra h
  apply hab
  apply Nat.zero_of_testBit_eq_false
  intro i
  by_cases hi : i < N
  · have hn : ¬ ((a &&& b).testBit i = true) := by
      intro ht
      rw [Nat.testBit_land, Bool.and_eq_true] at ht
      apply h
      exact ⟨⟨i, hi⟩, Finset.mem_inter.mpr ⟨mem_maskSet.mpr ht.1, mem_maskSet.mpr ht.2⟩⟩
    exact Bool.eq_false_iff.mpr hn
  · have hai : a < 2 ^ i := ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [Nat.testBit_eq_false_of_lt hai]

def allBelow (n : ℕ) (f : ℕ → Bool) : Bool := (List.range n).all f

lemma allBelow_spec {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true)
    {i : ℕ} (hi : i < n) : f i = true := by
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

lemma allBelow_of_forall {n : ℕ} {f : ℕ → Bool}
    (h : ∀ i, i < n → f i = true) : allBelow n f = true := by
  exact List.all_eq_true.mpr (fun i hi => h i (List.mem_range.mp hi))

lemma allBelow_succ_intro {n : ℕ} {f : ℕ → Bool}
    (h : allBelow n f = true) (hn : f n = true) : allBelow (n + 1) f = true := by
  simp only [allBelow, List.range_succ, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true]
  change (allBelow n f && f n) = true
  rw [h, hn]
  rfl

def rawStepCell (N K : ℕ) (T R : ℕ → ℕ → ℕ) (p d c' : ℕ) : Bool :=
  decide (R p ((K * d + c') / 3) = 0) ||
    allBelow N fun r => !(T p ((K * d + c') % 3)).testBit r ||
      allBelow N fun q => !(R p ((K * d + c') / 3)).testBit q ||
        decide (T q d &&& R r c' ≠ 0)

def rawStepRow (N K : ℕ) (T R : ℕ → ℕ → ℕ) (p : ℕ) : Bool :=
  allBelow 3 fun d => allBelow K fun c' => rawStepCell N K T R p d c'

lemma rawStepRow_of_cells {N K : ℕ} {T R : ℕ → ℕ → ℕ} {p : ℕ}
    (h : ∀ d, d < 3 → ∀ c', c' < K → rawStepCell N K T R p d c' = true) :
    rawStepRow N K T R p = true := by
  exact allBelow_of_forall (fun d hd => allBelow_of_forall (h d hd))

lemma rawStepRow_sound {N K : ℕ} {T R : ℕ → ℕ → ℕ}
    (hbound : ∀ q d, q < N → d < 3 → T q d < 2 ^ N)
    {p : Fin N} (h : rawStepRow N K T R p = true)
    (d : ℕ) (hd : d < 3) (c' : ℕ) (hc' : c' < K)
    (r : Fin N) (hr : r ∈ maskSet N (T p ((K * d + c') % 3)))
    (q : Fin N) (hq : q ∈ maskSet N (R p ((K * d + c') / 3))) :
    (maskSet N (T q d) ∩ maskSet N (R r c')).Nonempty := by
  have hh := allBelow_spec (allBelow_spec h hd) hc'
  unfold rawStepCell at hh
  have hR : R p ((K * d + c') / 3) ≠ 0 := by
    intro hz
    have hb := mem_maskSet.mp hq
    simp [hz] at hb
  have hh' : allBelow N (fun r => !(T p ((K * d + c') % 3)).testBit r ||
      allBelow N (fun q => !(R p ((K * d + c') / 3)).testBit q ||
        decide (T q d &&& R r c' ≠ 0))) = true := by
    simpa only [decide_eq_false hR, Bool.false_or] using hh
  have h₁ := allBelow_spec hh' r.isLt
  have h₂ : allBelow N (fun q => !(R p ((K * d + c') / 3)).testBit q ||
      decide (T q d &&& R r c' ≠ 0)) = true := by
    simpa only [mem_maskSet.mp hr, Bool.not_true, Bool.false_or] using h₁
  have h₃ := allBelow_spec h₂ q.isLt
  have hne : T q d &&& R r c' ≠ 0 := by
    simpa only [mem_maskSet.mp hq, Bool.not_true, Bool.false_or, decide_eq_true_eq] using h₃
  exact land_nonempty (hbound q d q.isLt hd) hne


def stepMaskList (T : ℕ → ℕ → ℕ) (U d : ℕ) (l : List ℕ) : ℕ :=
  l.foldr (fun q V => if U.testBit q then T q d ||| V else V) 0

lemma stepMaskList_spec (T : ℕ → ℕ → ℕ) (U d r : ℕ) (l : List ℕ) :
    (stepMaskList T U d l).testBit r = true ↔
      ∃ q ∈ l, U.testBit q = true ∧ (T q d).testBit r = true := by
  induction l with
  | nil => simp [stepMaskList]
  | cons a l ih =>
    simp only [stepMaskList, List.foldr_cons]
    split <;> rename_i h
    · simp only [Nat.testBit_lor, Bool.or_eq_true]
      change ((T a d).testBit r = true ∨ (stepMaskList T U d l).testBit r = true) ↔ _
      rw [ih]
      simp [h]
    · change (stepMaskList T U d l).testBit r = true ↔ _
      rw [ih]
      simp [h]

def stepMask (N : ℕ) (T : ℕ → ℕ → ℕ) (U d : ℕ) : ℕ :=
  stepMaskList T U d (List.range N)

def fromMasks (N : ℕ) (T R : ℕ → ℕ → ℕ) (S A : ℕ) : Data (Fin N) where
  step p d := maskSet N (T p d)
  start := maskSet N S
  accept := maskSet N A
  relation p c := maskSet N (R p c)

lemma stepStates_maskSet (N : ℕ) (T R : ℕ → ℕ → ℕ) (S A U d : ℕ) :
    (fromMasks N T R S A).stepStates (maskSet N U) d =
      maskSet N (stepMask N T U d) := by
  ext r
  simp only [Data.stepStates, Finset.mem_biUnion, mem_maskSet,
    fromMasks, stepMask, stepMaskList_spec, List.mem_range]
  constructor
  · rintro ⟨q, hq, hr⟩
    exact ⟨q.val, q.isLt, hq, hr⟩
  · rintro ⟨q, hq, hu, ht⟩
    exact ⟨⟨q, hq⟩, hu, ht⟩

def evalMask (N : ℕ) (T : ℕ → ℕ → ℕ) (S n : ℕ) : ℕ :=
  (Nat.digits 3 n).reverse.foldl (stepMask N T) S

lemma foldl_maskSet (N : ℕ) (T R : ℕ → ℕ → ℕ) (S A U : ℕ) (w : List ℕ) :
    w.foldl (fromMasks N T R S A).stepStates (maskSet N U) =
      maskSet N (w.foldl (stepMask N T) U) := by
  induction w generalizing U with
  | nil => rfl
  | cons d w ih =>
    simp only [List.foldl_cons, stepStates_maskSet, ih]

lemma evalStates_maskSet (N : ℕ) (T R : ℕ → ℕ → ℕ) (S A n : ℕ) :
    (fromMasks N T R S A).evalStates n = maskSet N (evalMask N T S n) := by
  exact foldl_maskSet N T R S A S (Nat.digits 3 n).reverse

def rawInitRow (N : ℕ) (T R : ℕ → ℕ → ℕ) (S c : ℕ) : Bool :=
  allBelow N fun p => !(evalMask N T S c).testBit p || decide (S &&& R p c ≠ 0)

lemma rawInitRow_sound {N : ℕ} {T R : ℕ → ℕ → ℕ} {S A c : ℕ}
    (hS : S < 2 ^ N) (h : rawInitRow N T R S c = true) :
    ∀ p ∈ (fromMasks N T R S A).evalStates c,
      ((fromMasks N T R S A).start ∩ (fromMasks N T R S A).relation p c).Nonempty := by
  intro p hp
  rw [evalStates_maskSet, mem_maskSet] at hp
  have hh := allBelow_spec h p.isLt
  have hne : S &&& R p c ≠ 0 := by
    simpa only [hp, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hh
  exact land_nonempty hS hne

lemma land_disjoint {N a b : ℕ} (h : a &&& b = 0) :
    Disjoint (maskSet N a) (maskSet N b) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hx : (a &&& b).testBit p = true := by
    rw [Nat.testBit_land, mem_maskSet.mp hp, mem_maskSet.mp hq]
    rfl
  simp [h] at hx

lemma ldiff_subset {N a b : ℕ} (h : Nat.ldiff a b = 0) :
    maskSet N a ⊆ maskSet N b := by
  intro q hq
  have ht := congrArg (fun n => Nat.testBit n q.val) h
  have ha := mem_maskSet.mp hq
  simp [Nat.testBit_ldiff, ha] at ht
  exact mem_maskSet.mpr ht

def rawFinishRow (A : ℕ) (R : ℕ → ℕ → ℕ) (p : ℕ) : Bool :=
  !A.testBit p || decide (Nat.ldiff (R p 0) A = 0)

lemma rawFinishRow_sound {N A : ℕ} {R : ℕ → ℕ → ℕ} {p : Fin N}
    (h : rawFinishRow A R p = true) (hp : p ∈ maskSet N A) :
    maskSet N (R p 0) ⊆ maskSet N A := by
  have hh : Nat.ldiff (R p 0) A = 0 := by
    simpa only [rawFinishRow, mem_maskSet.mp hp, Bool.not_true, Bool.false_or,
      decide_eq_true_eq] using h
  exact ldiff_subset hh

#print axioms rawStepRow_sound
#print axioms rawInitRow_sound
#print axioms rawFinishRow_sound
#print axioms evalStates_maskSet
end Erdos406BackwardBitmask
