import FormalConjectures.Util.ProblemImports

open List Nat

/-- The substitution rule for A284851: $0 \mapsto [0, 1]$, $1 \mapsto [0, 1, 0, 0]$. -/
def A284851_subst_rule : ℕ → List ℕ
| 0 => [0, 1]
| 1 => [0, 1, 0, 0]
| _ => []

/--
The sequence of finite prefixes of A284851.
$L_0 = [0]$. $L_{n+1} = L_n$.flatMap $A284851\_subst\_rule$.
-/
def A284851_list_at_step : ℕ → List ℕ
| 0 => [0]
| (n + 1) => (A284851_list_at_step n).flatMap A284851_subst_rule

lemma A284851_subst_rule_length_le (x : ℕ) : (A284851_subst_rule x).length ≤ 4 := by
  cases x with
  | zero => decide
  | succ x =>
    cases x with
    | zero => decide
    | succ x =>
      simp [A284851_subst_rule]

lemma flatMap_length_le_mul_four {α : Type*} (l : List α) (f : α → List ℕ) (hf : ∀ x, (f x).length ≤ 4) :
    (l.flatMap f).length ≤ l.length * 4 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [flatMap_cons, length_append, length_cons]
    have h1 := hf x
    have h2 : (xs.length + 1) * 4 = xs.length * 4 + 4 := by ring
    omega

lemma A284851_list_at_step_length_le (n : ℕ) : (A284851_list_at_step n).length ≤ 4 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [A284851_list_at_step]
    have h1 := flatMap_length_le_mul_four (A284851_list_at_step n) A284851_subst_rule A284851_subst_rule_length_le
    have h2 : (A284851_list_at_step n).length * 4 ≤ 4 ^ n * 4 := Nat.mul_le_mul_right 4 ih
    omega

/--
A proxy for the infinite word A284851.
We take the value from a large-enough prefix (10th iteration).
-/
noncomputable def A284851_value (n : ℕ) : ℕ :=
  (A284851_list_at_step 10).getD n 1

/--
A284852: Positions of 0 in A284851; complement of A284853.
The $n$-th term $a(n)$ is the sequence of 1-indexed positions $k$ such that $A284851(k-1) = 0$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sequence is 1-indexed, so we find the (n-1)-th 0-indexed position k, and add 1.
  (n - 1).nth (fun k => A284851_value k = 0) + 1

-- The constant r = (3 + sqrt(3)) / 3
noncomputable def r : ℝ := (3 + Real.sqrt 3) / 3

def p (k : ℕ) : Prop := A284851_value k = 0

lemma p_subset : setOf p ⊆ ↑(Finset.range 1048577) := by
  intro k hk
  simp only [p, Set.mem_setOf_eq] at hk
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h_ge
  push_neg at h_ge
  have h_len_le : (A284851_list_at_step 10).length ≤ 1048576 := by
    have h_le := A284851_list_at_step_length_le 10
    exact h_le
  have h_ge_len : (A284851_list_at_step 10).length ≤ k := by omega
  have h_eq : A284851_value k = 1 := by
    dsimp [A284851_value]
    apply List.getD_eq_default
    exact h_ge_len
  rw [h_eq] at hk
  contradiction

lemma p_finite : (setOf p).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet (Finset.range 1048577)) p_subset

lemma p_card_le : p_finite.toFinset.card ≤ 1048577 := by
  have h_sub : p_finite.toFinset ⊆ Finset.range 1048577 := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    have h_in := p_subset hx
    simp only [Finset.mem_coe] at h_in
    exact h_in
  have h_card := Finset.card_le_card h_sub
  rw [Finset.card_range] at h_card
  exact h_card

lemma nth_p_large : Nat.nth p 1048577 = 0 := by
  apply Nat.nth_of_card_le p_finite p_card_le

lemma a_large : a 1048578 = 1 := by
  dsimp [a]
  change Nat.nth p 1048577 + 1 = 1
  rw [nth_p_large]

lemma abs_bound_contradiction : ¬ abs ((1048578 : ℝ) * r - (a 1048578 : ℝ)) < 2 := by
  rw [a_large]
  push_cast
  push_neg
  have h_sqrt : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h_r : 1 ≤ r := by
    dsimp [r]
    have : (3 + Real.sqrt 3) / 3 = 1 + Real.sqrt 3 / 3 := by ring
    rw [this]
    linarith
  have h_val : 1048577 ≤ (1048578 : ℝ) * r - 1 := by
    calc 1048577 = (1048578 : ℝ) * 1 - 1 := by norm_num
    _ ≤ (1048578 : ℝ) * r - 1 := by linarith
  have h_abs : (1048578 : ℝ) * r - 1 ≤ abs ((1048578 : ℝ) * r - 1) := le_abs_self _
  linarith

/--
Conjecture A284852: -2 < n*r - a(n) < 2 for n >= 1, where r = (3+sqrt(3))/3.
-/
theorem oeis_284852_conjecture.disproof : ¬ (∀ (n : ℕ), 0 < n →
  abs ((n : ℝ) * r - (a n : ℝ)) < 2) := by
  intro h
  have h_contra := h 1048578 (by decide)
  exact abs_bound_contradiction h_contra

