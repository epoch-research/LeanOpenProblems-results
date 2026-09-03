import Submission.CriticalTightVertices

/-! A kernel-checked linear-time disjointness certificate for sorted lists. -/
namespace Erdos184
namespace SortedDisjointCertificate

def check : ℕ → List ℕ → List ℕ → Bool
  | _, [], _ => true
  | _, _, [] => true
  | 0, _ :: _, _ :: _ => false
  | n+1, a :: as, b :: bs =>
    if a < b then check n as (b :: bs)
    else if b < a then check n (a :: as) bs
    else false

lemma check_sound (n : ℕ) (as bs : List ℕ)
    (ha : as.Pairwise (· ≤ ·)) (hb : bs.Pairwise (· ≤ ·))
    (h : check n as bs = true) : as.Disjoint bs := by
  induction n generalizing as bs with
  | zero =>
    cases as <;> cases bs <;> simp_all [check]
  | succ n ih =>
    cases as with
    | nil => simp
    | cons a as =>
      cases bs with
      | nil => simp
      | cons b bs =>
        have ha' := List.pairwise_cons.mp ha
        have hb' := List.pairwise_cons.mp hb
        simp only [check] at h
        split_ifs at h with hab hba
        · have hd := ih as (b :: bs) ha'.2 hb h
          intro x hx hy
          rcases List.mem_cons.mp hx with rfl | hx
          · rcases List.mem_cons.mp hy with h | hy
            · omega
            · have := hb'.1 x hy
              omega
          · exact hd hx hy
        · have hd := ih (a :: as) bs ha hb'.2 h
          intro x hx hy
          rcases List.mem_cons.mp hy with rfl | hy
          · rcases List.mem_cons.mp hx with h | hx
            · omega
            · have := ha'.1 x hx
              omega
          · exact hd hx hy

def mergeSteps : ℕ → List ℕ → List ℕ → List ℕ
  | _, [], bs => bs
  | _, as, [] => as
  | 0, as, bs => as ++ bs
  | n+1, a :: as, b :: bs =>
    if a ≤ b then a :: mergeSteps n as (b :: bs)
    else b :: mergeSteps n (a :: as) bs

lemma mergeSteps_eq (n : ℕ) (as bs : List ℕ) (hn : as.length + bs.length ≤ n) :
    mergeSteps n as bs = as.merge bs (fun a b => decide (a ≤ b)) := by
  induction n generalizing as bs with
  | zero =>
    have ha : as = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hb : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [ha,hb,mergeSteps]
  | succ n ih =>
    cases as with
    | nil => simp [mergeSteps]
    | cons a as =>
      cases bs with
      | nil => simp [mergeSteps]
      | cons b bs =>
        simp only [List.length_cons] at hn
        simp only [mergeSteps,List.merge,decide_eq_true_eq]
        split_ifs with hab
        · rw [ih as (b :: bs) (by simp only [List.length_cons]; omega)]
        · rw [ih (a :: as) bs (by simp only [List.length_cons]; omega)]

def merge (as bs : List ℕ) := mergeSteps (as.length + bs.length) as bs

lemma merge_eq (as bs : List ℕ) :
    merge as bs = as.merge bs (fun a b => decide (a ≤ b)) := mergeSteps_eq _ _ _ le_rfl

def sort : ℕ → List ℕ → List ℕ
  | 0, xs => xs.insertionSort (· ≤ ·)
  | _+1, [] => []
  | _+1, [a] => [a]
  | n+1, a :: b :: xs =>
    let ys := a :: b :: xs
    let k := ys.length / 2
    merge (sort n (ys.take k)) (sort n (ys.drop k))

lemma sort_perm (n : ℕ) (xs : List ℕ) : (sort n xs).Perm xs := by
  induction n generalizing xs with
  | zero => exact List.perm_insertionSort (· ≤ ·) xs
  | succ n ih =>
    cases xs with
    | nil => simp [sort]
    | cons a xs =>
      cases xs with
      | nil => simp [sort]
      | cons b xs =>
        simp only [sort,merge_eq]
        refine (List.merge_perm_append (fun a b : ℕ => decide (a ≤ b))).trans ?_
        simpa only [List.take_append_drop] using
          (ih ((a :: b :: xs).take ((a :: b :: xs).length / 2))).append
            (ih ((a :: b :: xs).drop ((a :: b :: xs).length / 2)))

lemma sort_pairwise (n : ℕ) (xs : List ℕ) : (sort n xs).Pairwise (· ≤ ·) := by
  induction n generalizing xs with
  | zero => exact List.pairwise_insertionSort (· ≤ ·) xs
  | succ n ih =>
    cases xs with
    | nil => simp [sort]
    | cons a xs =>
      cases xs with
      | nil => simp [sort]
      | cons b xs =>
        simp only [sort,merge_eq]
        have h := List.pairwise_merge
          (le := fun a b : ℕ => decide (a ≤ b))
          (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
          (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega)
          (sort n ((a :: b :: xs).take ((a :: b :: xs).length / 2)))
          (sort n ((a :: b :: xs).drop ((a :: b :: xs).length / 2)))
          (by simpa only [decide_eq_true_eq] using ih _) (by
            simpa only [decide_eq_true_eq] using ih _)
        simpa only [decide_eq_true_eq] using h

def sorted (xs : List ℕ) : List ℕ := sort 16 xs

lemma sorted_pairwise (xs : List ℕ) : (sorted xs).Pairwise (· ≤ ·) := sort_pairwise 16 xs

@[simp] lemma mem_sorted (x : ℕ) (xs : List ℕ) : x ∈ sorted xs ↔ x ∈ xs :=
  (sort_perm 16 xs).mem_iff

end SortedDisjointCertificate
end Erdos184
