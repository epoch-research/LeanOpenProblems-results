import Submission.CubicBlockRigidity

/-! Canonical balanced ternary for nonnegative integers. These representation
lemmas do not assert finiteness of the powers in Erdős 406. -/
namespace Erdos406Balanced
open Erdos406Work

/-- The indices 0,1,2 denote the trits -1,0,1. -/
def value : List ℕ → ℤ
  | [] => 0
  | d :: w => (d : ℤ) - 1 + 3 * value w

/-- Canonical nonnegative balanced ternary, least significant trit first. -/
def digits (n : ℕ) : List ℕ :=
  if hn : n = 0 then [] else (n+1)%3 :: digits ((n+1)/3)
termination_by n
decreasing_by omega

@[simp] lemma digits_zero : digits 0 = [] := by rw [digits]; simp

lemma digits_pos {n : ℕ} (hn : 0 < n) :
    digits n = (n+1)%3 :: digits ((n+1)/3) := by
  rw [digits, dif_neg (by omega)]

lemma digits_ne_nil {n : ℕ} (hn : 0 < n) : digits n ≠ [] := by
  rw [digits_pos hn]
  simp

lemma value_digits (n : ℕ) : value (digits n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz, value]
    · rw [digits_pos (by omega), value, ih ((n+1)/3) (by omega)]
      omega

lemma digits_lt_three (n d : ℕ) (hd : d ∈ digits n) : d < 3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz] at hd
    · rw [digits_pos (by omega), List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Nat.mod_lt _ (by decide)
      · exact ih ((n+1)/3) (by omega) hd

lemma digits_last (n : ℕ) (hn : 0 < n) : (digits n).getLast? = some 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [digits_pos hn]
    by_cases hq : (n+1)/3 = 0
    · have he : n = 1 := by omega
      simp [he, digits_zero]
    · have hh := ih ((n+1)/3) (by omega) (by omega)
      simp only [List.getLast?_cons, hh, Option.getD_some]

/-- Ordinary good words need no balanced carries: add one to each digit index. -/
lemma digits_eq_map_of_good {n : ℕ} (hg : Nat.digits 3 n ⊆ [0, 1]) :
    digits n = (Nat.digits 3 n).map (fun d => d+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz]
    · have hn : 0 < n := by omega
      have hd := ternary_digit_bound hg 0
      norm_num only [pow_zero, Nat.div_one] at hd
      have hq : (n+1)/3 = n/3 := by omega
      have hr : (n+1)%3 = n%3+1 := by omega
      have ht : Nat.digits 3 (n/3) ⊆ [0, 1] := by
        simpa using good_div_three_pow hg 1
      rw [digits_pos hn, hq, hr, ih (n/3) (by omega) ht,
        Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn, List.map_cons]

/-- Empty words representzero; nonempty canonical words end in index2. -/
def Canonical (w : List ℕ) : Prop := w = [] ∨ w.getLast? = some 2

def Valid (w : List ℕ) : Prop := ∀ d ∈ w, d < 3

lemma canonical_tail {d : ℕ} {w : List ℕ} (h : Canonical (d::w)) : Canonical w := by
  cases w with
  | nil => exact Or.inl rfl
  | cons e w =>
    right
    rcases h with h | h
    · simp at h
    · simpa only [List.getLast?_cons_cons] using h

lemma valid_tail {d : ℕ} {w : List ℕ} (h : Valid (d::w)) : Valid w :=
  fun e he => h e (List.mem_cons_of_mem d he)

lemma value_pos_of_canonical {w : List ℕ} (hw : Valid w)
    (hc : w.getLast? = some 2) : 0 < value w := by
  induction w with
  | nil => simp at hc
  | cons d w ih =>
    cases w with
    | nil =>
      have hd : d = 2 := by simpa using hc
      simp [hd, value]
    | cons e w =>
      have ht : (e::w).getLast? = some 2 := by
        simpa only [List.getLast?_cons_cons] using hc
      have hp := ih (valid_tail hw) ht
      simp only [value]
      change 0 < (d : ℤ) - 1 + 3 * value (e::w)
      omega

lemma value_nonneg_of_canonical {w : List ℕ} (hw : Valid w) (hc : Canonical w) :
    0 ≤ value w := by
  rcases hc with rfl | hc
  · simp [value]
  · exact (value_pos_of_canonical hw hc).le

lemma value_injective {w v : List ℕ} (hw : Valid w) (hv : Valid v)
    (hcw : Canonical w) (hcv : Canonical v) (he : value w = value v) : w = v := by
  induction w generalizing v with
  | nil =>
    rcases hcv with rfl | hcv
    · rfl
    · have hp := value_pos_of_canonical hv hcv
      simp only [value] at he
      omega
  | cons d w ih =>
    cases v with
    | nil =>
      have hc : (d::w).getLast? = some 2 := by simpa [Canonical] using hcw
      have hp := value_pos_of_canonical hw hc
      change value (d::w) = 0 at he
      omega
    | cons e v =>
      have hd := hw d (by simp)
      have he' := hv e (by simp)
      have hde : d = e := by
        simp only [value] at he
        omega
      subst e
      have ht : value w = value v := by simp only [value] at he; omega
      exact congrArg (List.cons d) (ih (valid_tail hw) (valid_tail hv)
        (canonical_tail hcw) (canonical_tail hcv) ht)

lemma canonical_digits (n : ℕ) : Canonical (digits n) := by
  by_cases hn : n = 0
  · left; simp [hn]
  · right; exact digits_last n (by omega)

lemma digits_unique {w : List ℕ} (n : ℕ) (hw : Valid w)
    (hc : Canonical w) (he : value w = n) : w = digits n :=
  value_injective hw (digits_lt_three n) hc (canonical_digits n)
    (he.trans (value_digits n).symm)

lemma value_append (u v : List ℕ) :
    value (u++v) = value u + (3 : ℤ)^u.length * value v := by
  induction u with
  | nil => simp [value]
  | cons d u ih => simp only [List.cons_append, value, List.length_cons, pow_succ, ih]; ring

lemma good_iff (n : ℕ) : digits n ⊆ [1,2] ↔ Nat.digits 3 n ⊆ [0,1] := by
  constructor
  · intro hb
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · simp [hn]
      · have hnpos : 0 < n := by omega
        have hh : (n+1)%3 = 1 ∨ (n+1)%3 = 2 := by
          have hh := hb (by rw [digits_pos hnpos]; simp : (n+1)%3 ∈ digits n)
          simpa using hh
        have hq : (n+1)/3 = n/3 := by omega
        have hm : n%3 = 0 ∨ n%3 = 1 := by omega
        have ht : digits (n/3) ⊆ [1,2] := by
          intro d hd
          apply hb
          rw [digits_pos hnpos,hq]
          exact List.mem_cons_of_mem _ hd
        have hi := ih (n/3) (by omega) ht
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hnpos]
        exact List.cons_subset.mpr ⟨by simpa using hm,hi⟩
  · intro hg
    rw [digits_eq_map_of_good hg]
    intro d hd
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
    have hh := hg he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh ⊢
    omega

@[simp] lemma digits_one : digits 1 = [2] := by norm_num [digits]
@[simp] lemma digits_two : digits 2 = [0,2] := by norm_num [digits]

#print axioms good_iff

#print axioms value_injective
#print axioms digits_unique

#print axioms value_digits
#print axioms digits_last
#print axioms digits_eq_map_of_good
end Erdos406Balanced
