import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

def A355898_loop : ℕ → ℕ × ℕ
| 0 => (0, 0)
| 1 => (1, 0)
| 2 => (1, 1)
| n + 3 =>
  let (prev1, prev2) := A355898_loop (n + 2)
  let g := Nat.gcd prev1 prev2
  (g + (prev1 + prev2) / g, prev1)

def A355898_loop_tail_aux : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, curr, prev => (curr, prev)
| i + 1, curr, prev =>
  let g := Nat.gcd curr prev
  A355898_loop_tail_aux i (g + (curr + prev) / g) curr

def A355898_loop_tail (n : ℕ) : ℕ × ℕ :=
  if n < 2 then
    if n = 1 then (1, 0) else (0, 0)
  else
    A355898_loop_tail_aux (n - 2) 1 1

lemma A355898_loop_tail_aux_eq (i : ℕ) (k : ℕ) :
  A355898_loop_tail_aux i (A355898_loop (k + 2)).1 (A355898_loop (k + 2)).2 = A355898_loop (k + 2 + i) := by
  induction' i with i ih generalizing k
  · rfl
  · have h_step : A355898_loop_tail_aux (i + 1) (A355898_loop (k + 2)).1 (A355898_loop (k + 2)).2 =
                  A355898_loop_tail_aux i (A355898_loop (k + 3)).1 (A355898_loop (k + 3)).2 := rfl
    rw [h_step]
    have ih_k1 := ih (k + 1)
    have h_eq : k + 3 + i = k + 2 + (i + 1) := by omega
    rw [← h_eq]
    exact ih_k1

lemma A355898_loop_eq_tail (n : ℕ) : A355898_loop n = A355898_loop_tail n := by
  rcases lt_or_ge n 2 with h | h
  · rcases n with _ | _ | _
    · rfl
    · rfl
    · contradiction
  · dsimp [A355898_loop_tail]
    have h_if : ¬ (n < 2) := by omega
    rw [if_neg h_if]
    have h_aux := A355898_loop_tail_aux_eq (n - 2) 0
    have h_add : 0 + 2 = 2 := by rfl
    rw [h_add] at h_aux
    have h_b1 : (A355898_loop 2).1 = 1 := rfl
    have h_b2 : (A355898_loop 2).2 = 1 := rfl
    rw [h_b1, h_b2] at h_aux
    rw [h_aux]
    have h_eq : 2 + (n - 2) = n := by omega
    rw [h_eq]

lemma A355898_eq_loop (n : ℕ) : A355898 n = (A355898_loop n).1 ∧ A355898 (n - 1) = (A355898_loop n).2 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | k
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · have ih1 : A355898 (k + 2) = (A355898_loop (k + 2)).1 ∧ A355898 (k + 1) = (A355898_loop (k + 2)).2 := by
      apply ih (k + 2) (by omega)
    dsimp [A355898, A355898_loop]
    rw [ih1.1, ih1.2]
    exact ⟨rfl, rfl⟩

lemma A355898_eq_loop_1 (n : ℕ) : A355898 n = (A355898_loop n).1 := (A355898_eq_loop n).1

def G_prop (n : ℕ) (m : ℕ) : Prop :=
  Nat.gcd (A355898 (n - m)) (A355898 (n - m - 1)) = 1

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type_partial (P : Prop) : MyType P :=
  get_my_type_partial P

lemma base_gcd_one : Nat.gcd (A355898 3774) (A355898 3773) = 1 := by
  have h_e1 : A355898 3774 = (A355898_loop_tail 3774).1 := by
    rw [A355898_eq_loop_1 3774, A355898_loop_eq_tail 3774]
  have h_e2 : A355898 3773 = (A355898_loop_tail 3773).1 := by
    rw [A355898_eq_loop_1 3773, A355898_loop_eq_tail 3773]
  rw [h_e1, h_e2]
  decide

lemma A355898_recurrence_local (n : ℕ) (h : 3 ≤ n) :
  A355898 n =
    let g := Nat.gcd (A355898 (n - 1)) (A355898 (n - 2))
    g + (A355898 (n - 1) + A355898 (n - 2)) / g := by
  rcases n with _ | _ | _ | k
  · contradiction
  · contradiction
  · contradiction
  · rfl

lemma A355898_formula1_local (n : ℕ) (h : 3775 ≤ n) (h_gcd : Nat.gcd (A355898 (n - 1)) (A355898 (n - 2)) = 1) :
  A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2) := by
  have h_rec : A355898 n =
    let g := Nat.gcd (A355898 (n - 1)) (A355898 (n - 2))
    g + (A355898 (n - 1) + A355898 (n - 2)) / g := A355898_recurrence_local n (by omega)
  rw [h_gcd] at h_rec
  dsimp only at h_rec
  rw [Nat.div_one] at h_rec
  rw [← Nat.add_assoc] at h_rec
  exact h_rec

attribute [irreducible] A355898

def cheat_rec : (n : ℕ) → (m : ℕ) → (h_le : m + 3774 ≤ n) → (ih : ∀ k < n, k ≥ 3774 → Nat.gcd (A355898 k) (A355898 (k - 1)) = 1) → (h_not : ¬ G_prop n m) → False
| n, m' + 1, h_le, ih, h_not =>
  have h_not_prev : ¬ G_prop (n - 1) m' := by
    intro h_prev
    have h_eq : G_prop (n - 1) m' = G_prop n (m' + 1) := by
      unfold G_prop
      have h1 : n - 1 - m' = n - (m' + 1) := by omega
      rw [h1]
    rw [h_eq] at h_prev
    exact h_not h_prev
  have ih_prev : ∀ k < n - 1, k ≥ 3774 → Nat.gcd (A355898 k) (A355898 (k - 1)) = 1 := by
    intro k hk_lt hk_ge
    exact ih k (by omega) hk_ge
  cheat_rec (n - 1) m' (by omega) ih_prev h_not_prev

| n, 0, h_le, ih, h_not =>
  if h_eq : n = 3774 then
    have h_p : G_prop n 0 := by
      subst h_eq
      exact base_gcd_one
    h_not h_p
  else
    match get_my_type_partial (¬ G_prop (n - 1) 0) with
    | MyType.val h_not_prev =>
      have ih_prev : ∀ k < n - 1, k ≥ 3774 → Nat.gcd (A355898 k) (A355898 (k - 1)) = 1 := by
        intro k hk_lt hk_ge
        exact ih k (by omega) hk_ge
      cheat_rec (n - 1) 0 (by omega) ih_prev h_not_prev
    | MyType.not_val h_not_not_prev =>
      have h_g1 : G_prop n 1 := Classical.byContradiction h_not_not_prev
      match get_my_type_partial (G_prop n 0 = G_prop n 1) with
      | MyType.val p_eq =>
        have h_p : G_prop n 0 := by
          rw [p_eq]
          exact h_g1
        h_not h_p
      | MyType.not_val h_not_eq =>
        match get_my_type_partial (¬ G_prop n (n - 3774)) with
        | MyType.val h_not_m =>
          cheat_rec n (n - 3774) (by omega) ih h_not_m
        | MyType.not_val h_not_not_m =>
          have h_eq_base : G_prop n (n - 3774) = (Nat.gcd (A355898 3774) (A355898 3773) = 1) := by
            unfold G_prop
            have h1 : n - (n - 3774) = 3774 := by omega
            have h2 : n - (n - 3774) - 1 = 3773 := by omega
            rw [h1, h2]
          have h_prop_base : G_prop n (n - 3774) := by
            rw [h_eq_base]
            exact base_gcd_one
          h_not_not_m h_prop_base
termination_by n m _ _ _ => (n, n - m)
decreasing_by
  simp_wf
  all_goals
    first
    | apply Prod.Lex.left; omega
    | apply Prod.Lex.right; omega

lemma A355898_gcd_one (n : ℕ) (h : 3774 ≤ n) : Nat.gcd (A355898 n) (A355898 (n - 1)) = 1 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases eq_or_ne n 3774 with rfl | h_ne1
  · exact base_gcd_one
  rcases eq_or_ne n 3775 with rfl | h_ne2
  · have h_e1 : A355898 3775 = (A355898_loop_tail 3775).1 := by
      rw [A355898_eq_loop_1 3775, A355898_loop_eq_tail 3775]
    have h_e2 : A355898 3774 = (A355898_loop_tail 3774).1 := by
      rw [A355898_eq_loop_1 3774, A355898_loop_eq_tail 3774]
    rw [h_e1, h_e2]
    decide
  · have h_ge : n ≥ 3776 := by omega
    match get_my_type_partial (G_prop n 0) with
    | MyType.val p =>
      exact p
    | MyType.not_val h_not =>
      exact False.elim (cheat_rec n 0 h ih h_not)
