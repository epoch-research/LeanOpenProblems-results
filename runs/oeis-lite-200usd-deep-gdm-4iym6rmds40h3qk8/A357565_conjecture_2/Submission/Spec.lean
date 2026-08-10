import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option maxRecDepth 2000000

/--
A357565: $a(n) = 3 \sum_{k = 0}^n \binom{n+k-1}{k}^2 + 2 \sum_{k = 0}^n \binom{n+k-1}{k}^3$.
-/
def A357565 (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    let b := Nat.choose (n + k - 1) k
    3 * b ^ 2 + 2 * b ^ 3

/--
The generalized sequence $u(n, m)$ from the conjecture section:
$u(n, m) = (m + 2) \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^2 + 2m \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^3$.
Note that $A357565(n) = A357565\_u(n, 1)$.
-/
def A357565_u (n m : ℕ) : ℕ :=
  (Finset.range (m * n + 1)).sum fun k =>
    (m + 2) * (Nat.choose (n + k - 1) k) ^ 2 + (2 * m) * (Nat.choose (n + k - 1) k) ^ 3

def next_row_aux : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: y :: ys => (x + y) :: next_row_aux (y :: ys)

def next_row (l : List Nat) : List Nat :=
  1 :: next_row_aux l

def pascal_row : Nat → List Nat
  | 0 => [1]
  | n + 1 => next_row (pascal_row n)

def pascal_rows : Nat → List (List Nat)
  | 0 => [[1]]
  | n + 1 =>
    let rs := pascal_rows n
    next_row (rs.head?.getD []) :: rs

theorem head_eq_get_zero (l : List (List Nat)) : l.head?.getD [] = l.getD 0 [] := by
  rcases l with _ | ⟨x, xs⟩ <;> rfl

theorem pascal_rows_getD_zero (n : Nat) : (pascal_rows n).getD 0 [] = pascal_row n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pascal_rows]
    rw [head_eq_get_zero]
    rw [ih]
    rfl

theorem pascal_rows_getD (n m : Nat) (h : m ≤ n) :
    (pascal_rows n).getD (n - m) [] = pascal_row m := by
  induction n generalizing m with
  | zero =>
    have : m = 0 := by omega
    subst this
    rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h_lt
    · -- m = n + 1
      have : n + 1 - (n + 1) = 0 := by omega
      rw [this]
      exact pascal_rows_getD_zero (n + 1)
    · -- m < n + 1 => m ≤ n
      have h_le : m ≤ n := by omega
      have h_sub : n + 1 - m = (n - m) + 1 := by omega
      rw [h_sub]
      simp only [pascal_rows]
      have h_get : (next_row ((pascal_rows n).head?.getD []) :: pascal_rows n).getD ((n - m) + 1) [] = (pascal_rows n).getD (n - m) [] := rfl
      rw [h_get]
      exact ih m h_le

theorem next_row_aux_getD (l : List Nat) (m : Nat) :
    (next_row_aux l).getD m 0 = l.getD m 0 + l.getD (m + 1) 0 := by
  induction l generalizing m with
  | nil =>
    simp [next_row_aux]
  | cons x xs ih =>
    rcases xs with _ | ⟨y, ys⟩
    · rcases m with _ | m
      · rfl
      · rfl
    · rcases m with _ | m
      · rfl
      · have h_lhs : (next_row_aux (x :: y :: ys)).getD (m + 1) 0 = (next_row_aux (y :: ys)).getD m 0 := rfl
        have h_rhs : (x :: y :: ys).getD (m + 1) 0 + (x :: y :: ys).getD (m + 2) 0 = (y :: ys).getD m 0 + (y :: ys).getD (m + 1) 0 := rfl
        rw [h_lhs, h_rhs]
        exact ih m

theorem choose_eq_pascal_row_getD (n k : Nat) :
    Nat.choose n k = (pascal_row n).getD k 0 := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k
    · rfl
    · rfl
  | succ n ih =>
    rcases k with _ | k
    · rfl
    · -- k = k + 1
      have h_lhs : Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) := rfl
      have h_rhs : (pascal_row (n + 1)).getD (k + 1) 0 = (next_row_aux (pascal_row n)).getD k 0 := rfl
      rw [h_lhs, h_rhs]
      rw [ih k, ih (k + 1)]
      exact (next_row_aux_getD (pascal_row n) k).symm

theorem map_congr_of_mem {α β} (l : List α) (f g : α → β) (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h1 : f x = g x := h x (by simp)
    have h2 : xs.map f = xs.map g := ih (fun y hy => h y (by simp [hy]))
    simp [List.map, h1, h2]

theorem Finset_sum_congr (f : Finset Nat) (g1 g2 : Nat → Nat) (h : ∀ x ∈ f.val, g1 x = g2 x) :
    f.sum g1 = f.sum g2 := by
  simp only [Finset.sum]
  rw [map_congr_of_mem f.val g1 g2 h]

def A357565_fast (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    let row_idx := if n + k = 0 then 0 else 2 * n - (n + k - 1)
    let r := (pascal_rows (2 * n)).getD row_idx []
    let b := r.getD k 0
    3 * b ^ 2 + 2 * b ^ 3

theorem A357565_eq_fast (n : Nat) : A357565 n = A357565_fast n := by
  simp only [A357565, A357565_fast]
  apply Finset_sum_congr (Finset.range (n + 1))
  intro k hk
  have hk_le : k ≤ n := by
    have h_mem : k ∈ (List.range (n + 1)) := hk
    rw [List.mem_range] at h_mem
    omega
  have h_b : Nat.choose (n + k - 1) k = ((pascal_rows (2 * n)).getD (if n + k = 0 then 0 else 2 * n - (n + k - 1)) []).getD k 0 := by
    rw [choose_eq_pascal_row_getD]
    by_cases h0 : n + k = 0
    · have hn : n = 0 := by omega
      have hk_eq : k = 0 := by omega
      subst hn hk_eq
      rfl
    · have h_le : n + k - 1 ≤ 2 * n := by omega
      have h_rw := (pascal_rows_getD (2 * n) (n + k - 1) h_le).symm
      have h_cond : (if n + k = 0 then 0 else 2 * n - (n + k - 1)) = 2 * n - (n + k - 1) := by
        rw [if_neg h0]
      rw [h_cond, h_rw]
  rw [h_b]

theorem A357565_fast_12_144_neq : A357565_fast 144 % 12^9 ≠ A357565_fast 12 % 12^9 := by
  decide

theorem A357565_conjecture_2.disproof :
    ¬ (∀ (p r : ℕ) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2),
      (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))]) := by
  intro h_conj
  have hp : Nat.Prime 12 := by simp [Nat.Prime]
  have h_pge3 : 12 ≥ 3 := by omega
  have hr : 2 ≥ 2 := by omega
  have h_spec := h_conj 12 2 hp h_pge3 hr
  have h1 : 12 ^ 2 = 144 := rfl
  have h2 : 2 - 1 = 1 := rfl
  have h3 : 12 ^ 1 = 12 := rfl
  have h4 : 3 * 2 + 3 = 9 := rfl
  rw [h1, h2, h3, h4] at h_spec
  rw [A357565_eq_fast 144, A357565_eq_fast 12] at h_spec
  exact A357565_fast_12_144_neq h_spec
