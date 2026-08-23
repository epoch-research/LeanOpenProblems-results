import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option linter.unusedVariables false

def T (z : ℕ) : ℕ := z * (z + 1) / 2

def primeCond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

def A264010 (n : ℕ) : ℕ :=
  let B := 2 * n + 2
  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ primeCond y ∧ primeCond z then 1 else 0

lemma x_lt_bound {n x y z : ℕ} (h : x * x + y * (y + 1) + T z = n) :
    x < 2 * n + 2 := by
  have : x * x ≤ n := by
    have := Nat.le_add_right (x * x) (y * (y + 1) + T z)
    simpa [← add_assoc, h] using this
  match x with
  | 0 => omega
  | 1 => omega
  | x + 2 =>
    have : (x + 2) * (x + 2) ≤ n := this
    nlinarith

lemma y_lt_bound {n x y z : ℕ} (h : x * x + y * (y + 1) + T z = n) :
    y < 2 * n + 2 := by
  have : y * (y + 1) ≤ n := by omega
  match y with
  | 0 => omega
  | 1 => omega
  | y + 2 =>
    have : (y + 2) * (y + 3) ≤ n := this
    nlinarith

lemma z_lt_bound {n x y z : ℕ} (h : x * x + y * (y + 1) + T z = n) :
    z < 2 * n + 2 := by
  have hz : T z ≤ n := by
    simp only [T] at *
    omega
  match z with
  | 0 => omega
  | 1 => omega
  | z + 2 =>
    have hdiv : (z + 2) * (z + 3) / 2 ≤ n := hz
    have : (z + 2) * (z + 3) ≤ 2 * n + 1 := by
      have := (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)).mp hdiv
      omega
    nlinarith

lemma one_le_of_rep {n x y z : ℕ} (heq : x * x + y * (y + 1) + T z = n)
    (hy : primeCond y) (hz : primeCond z) : 1 ≤ A264010 n := by
  have hxB := x_lt_bound heq
  have hyB := y_lt_bound heq
  have hzB := z_lt_bound heq
  simp only [A264010]
  have hxR : x ∈ range (2 * n + 2) := by simpa using hxB
  have hyR : y ∈ range (2 * n + 2) := by simpa using hyB
  have hzR : z ∈ range (2 * n + 2) := by simpa using hzB
  refine (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxR).trans' ?_
  refine (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyR).trans' ?_
  refine (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hzR).trans' ?_
  simp [heq, hy, hz]

-- Test
theorem a3_ge1 : 1 ≤ A264010 3 :=
  one_le_of_rep (x := 0) (y := 1) (z := 1) (by decide) (Or.inr (by decide)) (Or.inr (by decide))

theorem a4_ge1 : 1 ≤ A264010 4 :=
  one_le_of_rep (x := 1) (y := 1) (z := 1) (by decide) (Or.inr (by decide)) (Or.inr (by decide))
