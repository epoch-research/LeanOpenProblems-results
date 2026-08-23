import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option linter.unusedVariables false

def T (z : ℕ) : ℕ := z * (z + 1) / 2

def primeCond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

instance : DecidablePred primeCond := fun k =>
  inferInstanceAs (Decidable (k.Prime ∨ (k + 1).Prime))

def good (n x y z : ℕ) : Prop :=
  x * x + y * (y + 1) + T z = n ∧ primeCond y ∧ primeCond z

instance (n x y z : ℕ) : Decidable (good n x y z) := by
  dsimp [good]; infer_instance

def A264010 (n : ℕ) : ℕ :=
  let B := 2 * n + 2
  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if good n x y z then 1 else 0

lemma x_lt_bound {n x y z : ℕ} (h : x * x + y * (y + 1) + T z = n) :
    x < 2 * n + 2 := by
  have : x * x ≤ n := by omega
  match x with
  | 0 => omega
  | 1 => omega
  | x + 2 => nlinarith

lemma y_lt_bound {n x y z : ℕ} (h : x * x + y * (y + 1) + T z = n) :
    y < 2 * n + 2 := by
  have : y * (y + 1) ≤ n := by omega
  match y with
  | 0 => omega
  | 1 => omega
  | y + 2 => nlinarith

lemma z_lt_bound {n x y z : ℕ} (h : x * x + y * (y + 1) + T z = n) :
    z < 2 * n + 2 := by
  have hz : T z ≤ n := by simp only [T] at *; omega
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
  have hg : good n x y z := ⟨heq, hy, hz⟩
  refine (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxR).trans' ?_
  refine (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyR).trans' ?_
  refine (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hzR).trans' ?_
  simp [hg]

lemma two_le_of_two_reps {n x1 y1 z1 x2 y2 z2 : ℕ}
    (e1 : x1 * x1 + y1 * (y1 + 1) + T z1 = n)
    (e2 : x2 * x2 + y2 * (y2 + 1) + T z2 = n)
    (p1 : primeCond y1) (q1 : primeCond z1)
    (p2 : primeCond y2) (q2 : primeCond z2)
    (hne : ¬ (x1 = x2 ∧ y1 = y2 ∧ z1 = z2)) :
    2 ≤ A264010 n := by
  have hx1 := x_lt_bound e1
  have hy1 := y_lt_bound e1
  have hz1 := z_lt_bound e1
  have hx2 := x_lt_bound e2
  have hy2 := y_lt_bound e2
  have hz2 := z_lt_bound e2
  let B := 2 * n + 2
  let f : ℕ → ℕ → ℕ → ℕ := fun x y z => if good n x y z then 1 else 0
  have hA : A264010 n = (range B).sum fun x => (range B).sum fun y => (range B).sum fun z => f x y z := by
    simp [A264010, f, B]
  rw [hA]
  have f1 : f x1 y1 z1 = 1 := by simp [f, good, e1, p1, q1]
  have f2 : f x2 y2 z2 = 1 := by simp [f, good, e2, p2, q2]
  have hx1R : x1 ∈ range B := by simp [B]; exact hx1
  have hy1R : y1 ∈ range B := by simp [B]; exact hy1
  have hz1R : z1 ∈ range B := by simp [B]; exact hz1
  have hx2R : x2 ∈ range B := by simp [B]; exact hx2
  have hy2R : y2 ∈ range B := by simp [B]; exact hy2
  have hz2R : z2 ∈ range B := by simp [B]; exact hz2
  by_cases hxeq : x1 = x2
  · subst hxeq
    by_cases hyeq : y1 = y2
    · subst hyeq
      have hzne : z1 ≠ z2 := fun h => hne ⟨rfl, rfl, h⟩
      have : 2 ≤ (range B).sum (fun z => f x1 y1 z) := by
        rw [← sum_erase_add (range B) (fun z => f x1 y1 z) hz1R]
        have : z2 ∈ (range B).erase z1 := mem_erase.mpr ⟨Ne.symm hzne, hz2R⟩
        rw [← sum_erase_add _ _ this]
        omega
      refine le_trans this ?_
      have i1 : (range B).sum (fun z => f x1 y1 z) ≤
          (range B).sum (fun y => (range B).sum (fun z => f x1 y z)) :=
        single_le_sum (f := fun y => (range B).sum (fun z => f x1 y z))
          (fun _ _ => Nat.zero_le _) hy1R
      have i2 : (range B).sum (fun y => (range B).sum (fun z => f x1 y z)) ≤
          (range B).sum (fun x => (range B).sum (fun y => (range B).sum (fun z => f x y z))) :=
        single_le_sum (f := fun x => (range B).sum (fun y => (range B).sum (fun z => f x y z)))
          (fun _ _ => Nat.zero_le _) hx1R
      exact le_trans i1 i2
    · have : 2 ≤ (range B).sum (fun y => (range B).sum (fun z => f x1 y z)) := by
        rw [← sum_erase_add (range B) (fun y => (range B).sum (fun z => f x1 y z)) hy1R]
        have : y2 ∈ (range B).erase y1 := mem_erase.mpr ⟨fun h => hyeq h.symm, hy2R⟩
        rw [← sum_erase_add _ _ this]
        have g1 : 1 ≤ (range B).sum (fun z => f x1 y1 z) :=
          le_trans (f1 ▸ le_rfl)
            (single_le_sum (f := fun z => f x1 y1 z) (fun _ _ => Nat.zero_le _) hz1R)
        have g2 : 1 ≤ (range B).sum (fun z => f x1 y2 z) :=
          le_trans (f2 ▸ le_rfl)
            (single_le_sum (f := fun z => f x1 y2 z) (fun _ _ => Nat.zero_le _) hz2R)
        omega
      have i : (range B).sum (fun y => (range B).sum (fun z => f x1 y z)) ≤
          (range B).sum (fun x => (range B).sum (fun y => (range B).sum (fun z => f x y z))) :=
        single_le_sum (f := fun x => (range B).sum (fun y => (range B).sum (fun z => f x y z)))
          (fun _ _ => Nat.zero_le _) hx1R
      exact le_trans this i
  · have : 2 ≤ (range B).sum (fun x => (range B).sum (fun y => (range B).sum (fun z => f x y z))) := by
      rw [← sum_erase_add (range B) _ hx1R]
      have : x2 ∈ (range B).erase x1 := mem_erase.mpr ⟨fun h => hxeq h.symm, hx2R⟩
      rw [← sum_erase_add _ _ this]
      have g1 : 1 ≤ (range B).sum (fun y => (range B).sum (fun z => f x1 y z)) := by
        have i : 1 ≤ (range B).sum (fun z => f x1 y1 z) :=
          le_trans (f1 ▸ le_rfl)
            (single_le_sum (f := fun z => f x1 y1 z) (fun _ _ => Nat.zero_le _) hz1R)
        exact le_trans i
          (single_le_sum (f := fun y => (range B).sum (fun z => f x1 y z))
            (fun _ _ => Nat.zero_le _) hy1R)
      have g2 : 1 ≤ (range B).sum (fun y => (range B).sum (fun z => f x2 y z)) := by
        have i : 1 ≤ (range B).sum (fun z => f x2 y2 z) :=
          le_trans (f2 ▸ le_rfl)
            (single_le_sum (f := fun z => f x2 y2 z) (fun _ _ => Nat.zero_le _) hz2R)
        exact le_trans i
          (single_le_sum (f := fun y => (range B).sum (fun z => f x2 y z))
            (fun _ _ => Nat.zero_le _) hy2R)
      omega
    exact this

theorem a3 : 1 ≤ A264010 3 :=
  one_le_of_rep (x := 0) (y := 1) (z := 1) (by decide) (Or.inr (by decide)) (Or.inr (by decide))

theorem a7 : 2 ≤ A264010 7 :=
  two_le_of_two_reps (x1 := 2) (y1 := 1) (z1 := 1) (x2 := 0) (y2 := 2) (z2 := 1)
    (by decide) (by decide)
    (Or.inr (by decide)) (Or.inr (by decide))
    (Or.inl (by decide)) (Or.inr (by decide))
    (by decide)
