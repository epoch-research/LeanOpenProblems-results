import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option linter.unusedVariables false

def T (z : ℕ) : ℕ := z * (z + 1) / 2

def primeCond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

instance decidable_primeCond : DecidablePred primeCond := fun k =>
  inferInstanceAs (Decidable (k.Prime ∨ (k + 1).Prime))

def A264010 (n : ℕ) : ℕ :=
  let B := 2 * n + 2
  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ primeCond y ∧ primeCond z then 1 else 0

def good (n x y z : ℕ) : Prop :=
  x * x + y * (y + 1) + T z = n ∧ primeCond y ∧ primeCond z

instance : Decidable (good n x y z) := inferInstance

def A' (n : ℕ) : ℕ :=
  let B := 2 * n + 2
  (range B ×ˢ range B ×ˢ range B).sum fun p =>
    if good n p.1 p.2.1 p.2.2 then 1 else 0

lemma sum_sum_sum_eq_sum_product {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (t : Finset β) (u : Finset γ) (f : α → β → γ → ℕ) :
    s.sum (fun a => t.sum (fun b => u.sum (fun c => f a b c))) =
      (s ×ˢ t ×ˢ u).sum (fun p => f p.1 p.2.1 p.2.2) := by
  rw [sum_product, sum_congr rfl]
  intro a ha
  rw [sum_product]

lemma A_eq_A' (n : ℕ) : A264010 n = A' n := by
  simp only [A264010, A', good]
  convert (sum_sum_sum_eq_sum_product (range (2 * n + 2)) (range (2 * n + 2))
    (range (2 * n + 2)) (fun x y z =>
      if x * x + y * (y + 1) + T z = n ∧ primeCond y ∧ primeCond z then 1 else 0)).symm
  ext x y z
  split_ifs <;> rfl

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

lemma mem_product3 {B x y z : ℕ} (hx : x < B) (hy : y < B) (hz : z < B) :
    (x, y, z) ∈ range B ×ˢ range B ×ˢ range B := by
  simp [hx, hy, hz]

lemma one_le_of_rep {n x y z : ℕ} (heq : x * x + y * (y + 1) + T z = n)
    (hy : primeCond y) (hz : primeCond z) : 1 ≤ A264010 n := by
  rw [A_eq_A']
  have hxB := x_lt_bound heq
  have hyB := y_lt_bound heq
  have hzB := z_lt_bound heq
  have hp : (x, y, z) ∈ range (2 * n + 2) ×ˢ range (2 * n + 2) ×ˢ range (2 * n + 2) :=
    mem_product3 hxB hyB hzB
  have hg : good n x y z := ⟨heq, hy, hz⟩
  simp only [A']
  have := Finset.single_le_sum (s := range (2 * n + 2) ×ˢ range (2 * n + 2) ×ˢ range (2 * n + 2))
    (f := fun p => if good n p.1 p.2.1 p.2.2 then 1 else 0)
    (fun _ _ => Nat.zero_le _) hp
  simpa [hg] using this

lemma two_le_of_two_reps {n x1 y1 z1 x2 y2 z2 : ℕ}
    (e1 : x1 * x1 + y1 * (y1 + 1) + T z1 = n)
    (e2 : x2 * x2 + y2 * (y2 + 1) + T z2 = n)
    (p1 : primeCond y1) (q1 : primeCond z1)
    (p2 : primeCond y2) (q2 : primeCond z2)
    (hne : (x1, y1, z1) ≠ (x2, y2, z2)) :
    2 ≤ A264010 n := by
  rw [A_eq_A']
  let B := 2 * n + 2
  let s := range B ×ˢ range B ×ˢ range B
  let f : ℕ × ℕ × ℕ → ℕ := fun p => if good n p.1 p.2.1 p.2.2 then 1 else 0
  have h1 : (x1, y1, z1) ∈ s :=
    mem_product3 (x_lt_bound e1) (y_lt_bound e1) (z_lt_bound e1)
  have h2 : (x2, y2, z2) ∈ s :=
    mem_product3 (x_lt_bound e2) (y_lt_bound e2) (z_lt_bound e2)
  have f1 : f (x1, y1, z1) = 1 := by simp [f, good, e1, p1, q1]
  have f2 : f (x2, y2, z2) = 1 := by simp [f, good, e2, p2, q2]
  have hnn : ∀ p ∈ s, 0 ≤ f p := fun _ _ => Nat.zero_le _
  -- sum ≥ f t1 + f t2 = 2
  have : f (x1, y1, z1) + f (x2, y2, z2) ≤ s.sum f := by
    rw [← Finset.sum_add_sum_compl (s := { (x1, y1, z1), (x2, y2, z2) }) (t := s)]
    · have hsub : {(x1, y1, z1), (x2, y2, z2)} ⊆ s := by
        intro p hp; simp at hp; rcases hp with rfl | rfl <;> assumption
      rw [sum_pair hne]
      omega
    · exact fun p hp => hnn p (by
        have : {(x1, y1, z1), (x2, y2, z2)} ⊆ s := by
          intro q hq; simp at hq; rcases hq with rfl | rfl <;> assumption
        exact this hp)
  simp only [A']
  omega

theorem a3 : 1 ≤ A264010 3 :=
  one_le_of_rep (x := 0) (y := 1) (z := 1) (by decide) (Or.inr (by decide)) (Or.inr (by decide))

theorem a7 : 2 ≤ A264010 7 :=
  two_le_of_two_reps (x1 := 2) (y1 := 1) (z1 := 1) (x2 := 0) (y2 := 2) (z2 := 1)
    (by decide) (by decide)
    (Or.inr (by decide)) (Or.inr (by decide))
    (Or.inl (by decide)) (Or.inr (by decide))
    (by decide)
