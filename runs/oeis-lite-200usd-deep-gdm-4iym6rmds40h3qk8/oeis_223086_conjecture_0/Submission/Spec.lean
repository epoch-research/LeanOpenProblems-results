import FormalConjectures.Util.ProblemImports

open Nat

/--
A223086: Trajectory of 64 under the map $n \to A006368(n)$.
The map is $f(n)$:
$$f(n) = \begin{cases} 3n/2 & \text{if } n \equiv 0 \pmod 2 \\ (3n+1)/4 & \text{if } n \equiv 1 \pmod 4 \\ (3n-1)/4 & \text{if } n \equiv 3 \pmod 4 \end{cases}$$
-/
def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

/--
A223086: Trajectory of 64 under the map $n \to A006368(n)$.
The sequence $a(n)$ is 1-indexed by $a(1)=64$ and recurrence $a(n+1) = f(a(n))$.
The $n$-th term is $f^{n-1}(64)$.
-/
def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

def g (y : ℕ) : ℕ :=
  if y % 3 = 0 then
    2 * y / 3
  else if y % 3 = 1 then
    (4 * y - 1) / 3
  else -- y % 3 = 2
    (4 * y + 1) / 3

def S_bool (y : ℕ) : Bool :=
  (y ≥ 17363) || (y ≥ 11575 && g y ≥ 17363)

def S (y : ℕ) : Prop :=
  S_bool y = true

instance (y : ℕ) : Decidable (S y) :=
  inferInstanceAs (Decidable (S_bool y = true))

lemma g_ge_11575_of_ge_17363 (y : ℕ) (hy : y ≥ 17363) : g y ≥ 11575 := by
  unfold g
  split_ifs with h1 h2 <;> omega

lemma g_g_0 (q : ℕ) : g (g (9 * q)) = 4 * q := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_1 (q : ℕ) : g (g (9 * q + 1)) = 16 * q + 1 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_2 (q : ℕ) : g (g (9 * q + 2)) = 8 * q + 2 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_3 (q : ℕ) : g (g (9 * q + 3)) = 8 * q + 3 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_4 (q : ℕ) : g (g (9 * q + 4)) = 16 * q + 7 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_5 (q : ℕ) : g (g (9 * q + 5)) = 16 * q + 9 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_6 (q : ℕ) : g (g (9 * q + 6)) = 8 * q + 5 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_7 (q : ℕ) : g (g (9 * q + 7)) = 8 * q + 6 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_8 (q : ℕ) : g (g (9 * q + 8)) = 16 * q + 15 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_0 (q : ℕ) : g (9 * q) = 6 * q := by
  unfold g; split_ifs with h1 h2 <;> omega

lemma g_1 (q : ℕ) : g (9 * q + 1) = 12 * q + 1 := by
  unfold g; split_ifs with h1 h2 <;> omega

lemma g_2 (q : ℕ) : g (9 * q + 2) = 12 * q + 3 := by
  unfold g; split_ifs with h1 h2 <;> omega

lemma g_3 (q : ℕ) : g (9 * q + 3) = 6 * q + 2 := by
  unfold g; split_ifs with h1 h2 <;> omega

lemma g_4 (q : ℕ) : g (9 * q + 4) = 12 * q + 5 := by
  unfold g; split_ifs with h1 h2 <;> omega

lemma g_5 (q : ℕ) : g (9 * q + 5) = 12 * q + 7 := by
  unfold g; split_ifs with h1 h2 <;> omega

lemma g_6 (q : ℕ) : g (9 * q + 6) = 6 * q + 4 := by
  unfold g; split_ifs with h1 h2 <;> omega

lemma g_7 (q : ℕ) : g (9 * q + 7) = 12 * q + 9 := by
  unfold g; split_ifs with h1 h2 <;> omega

lemma g_8 (q : ℕ) : g (9 * q + 8) = 12 * q + 11 := by
  unfold g; split_ifs with h1 h2 <;> omega

lemma invariant_step (y : ℕ) (hy : S y) : S (g y) := by
  unfold S S_bool at *
  rw [Bool.or_eq_true] at hy ⊢
  rcases hy with h1 | h23
  · -- Case 1: y ≥ 17363
    rw [decide_eq_true_iff] at h1
    by_cases hg : g y ≥ 17363
    · left
      rw [decide_eq_true_iff]
      exact hg
    · right
      rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · exact g_ge_11575_of_ge_17363 y h1
      · -- We need g (g y) ≥ 17363
        have h_mod : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by omega
        rcases h_mod with h_mod | h_mod | h_mod | h_mod | h_mod | h_mod | h_mod | h_mod | h_mod
        · have h_eq : y = 9 * (y / 9) := by omega
          rw [h_eq] at h1 hg ⊢
          rw [g_g_0 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 1 := by omega
          rw [h_eq] at h1 hg ⊢
          rw [g_1 (y / 9)] at hg
          omega
        · have h_eq : y = 9 * (y / 9) + 2 := by omega
          rw [h_eq] at h1 hg ⊢
          rw [g_2 (y / 9)] at hg
          omega
        · have h_eq : y = 9 * (y / 9) + 3 := by omega
          rw [h_eq] at h1 hg ⊢
          rw [g_g_3 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 4 := by omega
          rw [h_eq] at h1 hg ⊢
          rw [g_4 (y / 9)] at hg
          omega
        · have h_eq : y = 9 * (y / 9) + 5 := by omega
          rw [h_eq] at h1 hg ⊢
          rw [g_5 (y / 9)] at hg
          omega
        · have h_eq : y = 9 * (y / 9) + 6 := by omega
          rw [h_eq] at h1 hg ⊢
          rw [g_g_6 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 7 := by omega
          rw [h_eq] at h1 hg ⊢
          rw [g_g_7 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 8 := by omega
          rw [h_eq] at h1 hg ⊢
          rw [g_8 (y / 9)] at hg
          omega
  · -- Case 2: y ≥ 11575 ∧ g y ≥ 17363
    rw [Bool.and_eq_true] at h23
    rcases h23 with ⟨h2, h3⟩
    rw [decide_eq_true_iff] at h2 h3
    left
    rw [decide_eq_true_iff]
    exact h3

lemma S_iterate (k : ℕ) (y : ℕ) (hy : S y) : S (g^[k] y) := by
  induction k generalizing y with
  | zero =>
    exact hy
  | succ k ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    exact ih (g y) (invariant_step y hy)

lemma S_ge_11575 (y : ℕ) (hy : S y) : y ≥ 11575 := by
  unfold S S_bool at hy
  rw [Bool.or_eq_true] at hy
  rcases hy with h1 | h2
  · rw [decide_eq_true_iff] at h1
    omega
  · rw [Bool.and_eq_true] at h2
    have h_left := h2.1
    rw [decide_eq_true_iff] at h_left
    exact h_left

lemma S_g_65 : S (g^[65] 64) := by
  decide

lemma g_iterate_ge_11575 (d : ℕ) (hd : d ≥ 65) : g^[d] 64 ≥ 11575 := by
  have h_eq : d = (d - 65) + 65 := by omega
  rw [h_eq, Function.iterate_add]
  dsimp only [Function.comp_apply]
  apply S_ge_11575
  apply S_iterate
  exact S_g_65

lemma g_iterate_neq_64_large (d : ℕ) (hd : d ≥ 65) : g^[d] 64 ≠ 64 := by
  have h_ge := g_iterate_ge_11575 d hd
  omega

def check_orbit_g (x : ℕ) (steps : ℕ) : Bool :=
  if x == 64 then
    false
  else
    match steps with
    | 0 => true
    | n + 1 => check_orbit_g (g x) n

theorem check_orbit_g_eq_true : check_orbit_g (g 64) 64 = true := by
  decide

lemma check_orbit_g_spec (x : ℕ) (steps : ℕ) (h : check_orbit_g x steps = true) :
  ∀ d, d ≤ steps → g^[d] x ≠ 64 := by
  induction steps generalizing x with
  | zero =>
    intro d hd
    have hd_eq : d = 0 := by omega
    subst hd_eq
    dsimp only [Function.iterate_zero, id_eq]
    intro h_eq
    subst h_eq
    dsimp [check_orbit_g] at h
    cases h
  | succ n ih =>
    intro d hd
    by_cases hx : x = 64
    · subst hx
      dsimp [check_orbit_g] at h
      cases h
    · cases d with
      | zero =>
        dsimp only [Function.iterate_zero, id_eq]
        exact hx
      | succ d =>
        have hd_le : d ≤ n := by omega
        have h_neq : (x == 64) = false := by
          cases h_eq : (x == 64) with
          | false => rfl
          | true =>
            rw [beq_iff_eq] at h_eq
            contradiction
        dsimp [check_orbit_g] at h
        rw [h_neq] at h
        have ih_spec := ih (g x) h d hd_le
        exact ih_spec

lemma g_iterate_neq_64_small (d : ℕ) (hd : d < 65) (hd_pos : d > 0) : g^[d] 64 ≠ 64 := by
  have h_check : check_orbit_g (g 64) 64 = true := check_orbit_g_eq_true
  have h_spec := check_orbit_g_spec (g 64) 64 h_check (d - 1) (by omega)
  have h_rw : g^[d - 1] (g 64) = g^[d] 64 := by
    have h_eq : d = d - 1 + 1 := by omega
    nth_rw 2 [h_eq]
    rfl
  rw [h_rw] at h_spec
  exact h_spec

theorem g_iterate_neq_64 (d : ℕ) (hd : d > 0) : g^[d] 64 ≠ 64 := by
  rcases le_or_gt 65 d with h_ge | h_lt
  · exact g_iterate_neq_64_large d h_ge
  · exact g_iterate_neq_64_small d h_lt hd

lemma g_f_eq (x : ℕ) : g (A006368_map x) = x := by
  unfold A006368_map g
  split_ifs with h1 h2 h3 h4 h5 <;> omega

lemma g_f_iterate_eq (d : ℕ) (x : ℕ) : g^[d] (A006368_map^[d] x) = x := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    rw [Function.iterate_succ', Function.comp_apply]
    rw [g_f_eq]
    exact ih x

theorem A006368_map_injective : ∀ x y, A006368_map x = A006368_map y → x = y := by
  intro x y h
  unfold A006368_map at h
  split_ifs at h <;> omega

theorem iterate_injective {α : Type*} (f : α → α) (hf : ∀ x y, f x = f y → x = y) (k : ℕ) :
  ∀ x y, f^[k] x = f^[k] y → x = y := by
  induction k with
  | zero =>
    intro x y h
    exact h
  | succ k ih =>
    intro x y h
    have h1 : f x = f y := ih (f x) (f y) h
    exact hf x y h1

theorem A006368_map_no_cycle : ∀ d, A006368_map^[d] 64 = 64 → d = 0 := by
  intro d h_cycle
  by_contra hd_pos
  have hd_gt : d > 0 := by omega
  have h_g_f := g_f_iterate_eq d 64
  rw [h_cycle] at h_g_f
  have h_neq := g_iterate_neq_64 d hd_gt
  exact h_neq h_g_f

/--
It is conjectured that this trajectory does not close on itself.
This is equivalent to stating that the sequence is injective on positive indices.
-/
theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj haj
  unfold a at haj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · -- i < j
    have h_sub : j - 1 = (i - 1) + (j - i) := by omega
    rw [h_sub] at haj
    rw [Function.iterate_add] at haj
    dsimp only [Function.comp_apply] at haj
    have h_inj := iterate_injective A006368_map A006368_map_injective (i - 1)
    have haj2 := h_inj _ _ haj
    symm at haj2
    have h_d : j - i = 0 := A006368_map_no_cycle (j - i) haj2
    omega
  · -- i = j
    exact heq
  · -- i > j
    have h_sub : i - 1 = (j - 1) + (i - j) := by omega
    rw [h_sub] at haj
    rw [Function.iterate_add] at haj
    dsimp only [Function.comp_apply] at haj
    have h_inj := iterate_injective A006368_map A006368_map_injective (j - 1)
    have haj2 := h_inj _ _ haj
    have h_d : i - j = 0 := A006368_map_no_cycle (i - j) haj2
    omega
