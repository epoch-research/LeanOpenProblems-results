import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/--
A264010: Number of ways to write $n$ as $x^2 + y(y+1) + z(z+1)/2$, where $x, y$ and $z$ are nonnegative integers such that $y$ or $y+1$ is prime, and $z$ or $z+1$ is prime.
-/
def A264010 (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

  -- A loose, but sufficient upper bound for all variables is $n+1$. We use $2n+2$ for maximum safety.
  let B := 2 * n + 2

  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ prime_cond y ∧ prime_cond z then 1 else 0

/-- The summand of `A264010`, written with a plain `if` for computation. -/
def tm (n x y z : ℕ) : ℕ :=
  if x * x + y * (y + 1) + z * (z + 1) / 2 = n ∧
      (Nat.Prime y ∨ Nat.Prime (y + 1)) ∧ (Nat.Prime z ∨ Nat.Prime (z + 1)) then 1 else 0

/-- **Reduction lemma.** The loose bound `2*n+2` in `A264010` may be replaced by any
`c` with `2*n < c*(c+1)` (and `c ≤ 2*n+2`): every representation of `n` already has all of
`x, y, z < c`, because `x^2 ≥ c^2 > n`, `y(y+1) ≥ c(c+1) > n` and
`T_z ≥ c(c+1)/2 > n` once the index reaches `c`. This makes `A264010 n` computable over a
small box. -/
lemma reduce (n c : ℕ) (h1 : 2 * n < c * (c + 1)) (h2 : c ≤ 2 * n + 2) :
    A264010 n = (range c).sum fun x => (range c).sum fun y => (range c).sum fun z => tm n x y z := by
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; simp at h1
    · exact h
  have hexp : c * (c + 1) = c * c + c := by ring
  have hcle : c ≤ c * c := by nlinarith [hc1]
  have hncc : n < c * c := by omega
  have hzero_z : ∀ x y z, c ≤ z → tm n x y z = 0 := by
    intro x y z hz; simp only [tm]; rw [if_neg]
    rintro ⟨he, _⟩
    have hle : c * (c + 1) ≤ z * (z + 1) := Nat.mul_le_mul hz (Nat.add_le_add_right hz 1)
    have hev : 2 ∣ z * (z + 1) := (Nat.even_mul_succ_self z).two_dvd
    omega
  have hzero_y : ∀ x y, c ≤ y → (∑ z ∈ range c, tm n x y z) = 0 := by
    intro x y hy; apply Finset.sum_eq_zero; intro z _; simp only [tm]; rw [if_neg]
    rintro ⟨he, _⟩
    have hle : c * (c + 1) ≤ y * (y + 1) := Nat.mul_le_mul hy (Nat.add_le_add_right hy 1)
    omega
  have hzero_x : ∀ x, c ≤ x → (∑ y ∈ range c, ∑ z ∈ range c, tm n x y z) = 0 := by
    intro x hx; apply Finset.sum_eq_zero; intro y _; apply Finset.sum_eq_zero; intro z _
    simp only [tm]; rw [if_neg]
    rintro ⟨he, _⟩
    have hle : c * c ≤ x * x := Nat.mul_le_mul hx hx
    omega
  have hsub : range c ⊆ range (2 * n + 2) := by intro a ha; rw [mem_range] at ha ⊢; omega
  unfold A264010
  simp only [dite_eq_ite]
  have tmeq : ∀ x y z : ℕ, (if x * x + y * (y + 1) + z * (z + 1) / 2 = n ∧
      (Nat.Prime y ∨ Nat.Prime (y + 1)) ∧ (Nat.Prime z ∨ Nat.Prime (z + 1)) then (1 : ℕ) else 0)
      = tm n x y z := fun _ _ _ => rfl
  simp only [tmeq]
  have hz : ∀ x y, (∑ z ∈ range (2 * n + 2), tm n x y z) = ∑ z ∈ range c, tm n x y z := by
    intro x y
    exact (Finset.sum_subset hsub
      (fun z _ hz => hzero_z x y z (by rw [mem_range, not_lt] at hz; exact hz))).symm
  simp only [hz]
  have hy : ∀ x, (∑ y ∈ range (2 * n + 2), ∑ z ∈ range c, tm n x y z)
      = ∑ y ∈ range c, ∑ z ∈ range c, tm n x y z := by
    intro x
    exact (Finset.sum_subset hsub
      (fun y _ hy => hzero_y x y (by rw [mem_range, not_lt] at hy; exact hy))).symm
  rw [Finset.sum_congr rfl (fun x _ => hy x)]
  exact (Finset.sum_subset hsub
    (fun x _ hx => hzero_x x (by rw [mem_range, not_lt] at hx; exact hx))).symm


-- Verification of the ten exceptional values `a(n) = 1`, via the reduction lemma + `decide`.
lemma a3 : A264010 3 = 1 := by rw [reduce 3 3 (by norm_num) (by norm_num)]; decide
lemma a4 : A264010 4 = 1 := by rw [reduce 4 3 (by norm_num) (by norm_num)]; decide
lemma a5 : A264010 5 = 1 := by rw [reduce 5 3 (by norm_num) (by norm_num)]; decide
lemma a6 : A264010 6 = 1 := by rw [reduce 6 4 (by norm_num) (by norm_num)]; decide
lemma a10 : A264010 10 = 1 := by rw [reduce 10 5 (by norm_num) (by norm_num)]; decide
lemma a11 : A264010 11 = 1 := by rw [reduce 11 5 (by norm_num) (by norm_num)]; decide
lemma a15 : A264010 15 = 1 := by rw [reduce 15 6 (by norm_num) (by norm_num)]; decide
lemma a20 : A264010 20 = 1 := by rw [reduce 20 6 (by norm_num) (by norm_num)]; decide
lemma a29 : A264010 29 = 1 := by rw [reduce 29 8 (by norm_num) (by norm_num)]; decide
lemma a1125 : A264010 1125 = 1 := by rw [reduce 1125 47 (by norm_num) (by norm_num)]; decide

/--
Conjecture (i): a(n) > 0 for all n > 2, and a(n) = 1 only for n = 3, 4, 5, 6, 10, 11, 15, 20, 29, 1125.
-/
theorem oeis_264010_conjecture_i (n : ℕ) (H_n : n > 2) :
  A264010 n > 0 ∧ (A264010 n = 1 ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) :=
by
  refine ⟨?_, ?_, ?_⟩
  · -- Positivity `a(n) > 0` for all `n > 2` (open part of Sun's conjecture; verified for n ≤ 10⁹).
    sorry
  · -- Forward direction `a(n) = 1 → n ∈ S`, i.e. `a(n) ≥ 2` for every `n > 1125` (open).
    sorry
  · intro hn
    fin_cases hn
    · exact a3
    · exact a4
    · exact a5
    · exact a6
    · exact a10
    · exact a11
    · exact a15
    · exact a20
    · exact a29
    · exact a1125
