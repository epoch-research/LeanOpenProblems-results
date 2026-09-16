import FormalConjectures.Util.ProblemImports

open Int Nat List

/--
Helper function for A382590, computing the pair $(a(n), b(n))$ such that:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$
$b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
-/
def A382590_pair : ℕ → ℤ × ℤ
| 0 => (1, 1)
| 1 => (2, 1)
| n + 2 =>
  let (a_n_plus_1, b_n_plus_1) := A382590_pair (n + 1)
  let (a_n, b_n) := A382590_pair n
  (a_n_plus_1 * b_n + a_n * b_n_plus_1, a_n_plus_1 * b_n - a_n * b_n_plus_1)

/--
A382590: $a(n)$ is the sequence defined by the mutual recurrence relations:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$ and $b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
starting with $a(0) = b(0) = b(1) = 1$ and a(1) = 2.
The terms are in $\mathbb{Z}$ due to negative values.
-/
def A382590 (n : ℕ) : ℤ := (A382590_pair n).fst

/--
The k-th prime factor of an integer n (where k>=1), counted with multiplicity.
This is defined as the k-th element (0-indexed k-1) of `Nat.primeFactorsList n.natAbs`.
Returns 1 if n has fewer than k prime factors or if n is 0, 1, or -1, following the informal convention.
-/
def kth_prime_factor (k : ℕ) (n : ℤ) : ℕ :=
  if h₀ : k = 0 then 1 else
  let n_abs := Int.natAbs n
  let L := primeFactorsList n_abs
  -- prime factors list length is L.length. We look for k-th element, index k-1.
  if h_len : k - 1 ≥ L.length then 1 else
  L[k - 1]

def a (n : ℕ) : ℤ := (A382590_pair n).fst
def b (n : ℕ) : ℤ := (A382590_pair n).snd

lemma a_b_step' (n : ℕ) :
  a (n + 2) = a (n + 1) * b n + a n * b (n + 1) ∧
  b (n + 2) = a (n + 1) * b n - a n * b (n + 1) := by
  exact ⟨rfl, rfl⟩

def M : ℕ → ℕ
| 0 => 0
| 1 => 0
| 2 => 0
| 3 => 0
| 4 => 1
| 5 => 1
| n + 6 => M (n + 5) + M (n + 4)

lemma div_step (n : ℕ) (h1a : (2:ℤ)^(M (n + 1)) ∣ a (n + 1)) (h1b : (2:ℤ)^(M (n + 1)) ∣ b (n + 1))
    (h2a : (2:ℤ)^(M n) ∣ a n) (h2b : (2:ℤ)^(M n) ∣ b n)
    (h_eq : M (n + 2) ≤ M (n + 1) + M n) :
    (2:ℤ)^(M (n + 2)) ∣ a (n + 2) ∧ (2:ℤ)^(M (n + 2)) ∣ b (n + 2) := by
  have step := a_b_step' n
  rcases h1a with ⟨k1a, hk1a⟩
  rcases h1b with ⟨k1b, hk1b⟩
  rcases h2a with ⟨k2a, hk2a⟩
  rcases h2b with ⟨k2b, hk2b⟩
  have h_add2 : M (n + 2) + (M (n + 1) + M n - M (n + 2)) = M (n + 1) + M n := by omega
  have h_pow : (2:ℤ)^(M (n + 1) + M n) = (2:ℤ)^(M (n + 2)) * (2:ℤ)^(M (n + 1) + M n - M (n + 2)) := by
    calc (2:ℤ)^(M (n + 1) + M n) = (2:ℤ)^(M (n + 2) + (M (n + 1) + M n - M (n + 2))) := by rw [h_add2]
      _ = (2:ℤ)^(M (n + 2)) * (2:ℤ)^(M (n + 1) + M n - M (n + 2)) := by exact pow_add 2 (M (n + 2)) (M (n + 1) + M n - M (n + 2))
  have h_ap2 : a (n + 2) = (2:ℤ)^(M (n + 2)) * ((2:ℤ)^(M (n + 1) + M n - M (n + 2)) * (k1a * k2b + k2a * k1b)) := by
    calc a (n + 2) = a (n + 1) * b n + a n * b (n + 1) := step.1
      _ = (2:ℤ)^(M (n + 1)) * k1a * ((2:ℤ)^(M n) * k2b) + (2:ℤ)^(M n) * k2a * ((2:ℤ)^(M (n + 1)) * k1b) := by rw [hk1a, hk2b, hk2a, hk1b]
      _ = (2:ℤ)^(M (n + 1)) * (2:ℤ)^(M n) * (k1a * k2b + k2a * k1b) := by ring
      _ = (2:ℤ)^(M (n + 1) + M n) * (k1a * k2b + k2a * k1b) := by exact congrArg (fun x => x * (k1a * k2b + k2a * k1b)) (pow_add 2 (M (n + 1)) (M n)).symm
      _ = (2:ℤ)^(M (n + 2)) * (2:ℤ)^(M (n + 1) + M n - M (n + 2)) * (k1a * k2b + k2a * k1b) := by rw [h_pow]
      _ = (2:ℤ)^(M (n + 2)) * ((2:ℤ)^(M (n + 1) + M n - M (n + 2)) * (k1a * k2b + k2a * k1b)) := by ring
  have h_bp2 : b (n + 2) = (2:ℤ)^(M (n + 2)) * ((2:ℤ)^(M (n + 1) + M n - M (n + 2)) * (k1a * k2b - k2a * k1b)) := by
    calc b (n + 2) = a (n + 1) * b n - a n * b (n + 1) := step.2
      _ = (2:ℤ)^(M (n + 1)) * k1a * ((2:ℤ)^(M n) * k2b) - (2:ℤ)^(M n) * k2a * ((2:ℤ)^(M (n + 1)) * k1b) := by rw [hk1a, hk2b, hk2a, hk1b]
      _ = (2:ℤ)^(M (n + 1)) * (2:ℤ)^(M n) * (k1a * k2b - k2a * k1b) := by ring
      _ = (2:ℤ)^(M (n + 1) + M n) * (k1a * k2b - k2a * k1b) := by exact congrArg (fun x => x * (k1a * k2b - k2a * k1b)) (pow_add 2 (M (n + 1)) (M n)).symm
      _ = (2:ℤ)^(M (n + 2)) * (2:ℤ)^(M (n + 1) + M n - M (n + 2)) * (k1a * k2b - k2a * k1b) := by rw [h_pow]
      _ = (2:ℤ)^(M (n + 2)) * ((2:ℤ)^(M (n + 1) + M n - M (n + 2)) * (k1a * k2b - k2a * k1b)) := by ring
  exact ⟨⟨_, h_ap2⟩, ⟨_, h_bp2⟩⟩

lemma M_div (n : ℕ) : (2:ℤ)^(M n) ∣ a n ∧ (2:ℤ)^(M n) ∣ b n := by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero => exact ⟨⟨a 0, by decide⟩, ⟨b 0, by decide⟩⟩
  | succ n =>
    cases n with
    | zero => exact ⟨⟨a 1, by decide⟩, ⟨b 1, by decide⟩⟩
    | succ n =>
      cases n with
      | zero => exact ⟨⟨a 2, by decide⟩, ⟨b 2, by decide⟩⟩
      | succ n =>
        cases n with
        | zero => exact ⟨⟨a 3, by decide⟩, ⟨b 3, by decide⟩⟩
        | succ n =>
          cases n with
          | zero => exact ⟨⟨a 4 / 2, by decide⟩, ⟨b 4 / 2, by decide⟩⟩
          | succ n =>
            cases n with
            | zero => exact ⟨⟨a 5 / 2, by decide⟩, ⟨b 5 / 2, by decide⟩⟩
            | succ n =>
              have h1 := ih (n + 5) (by omega)
              have h2 := ih (n + 4) (by omega)
              have heq : M (n + 6) ≤ M (n + 5) + M (n + 4) := by
                have h_def : M (n + 6) = M (n + 5) + M (n + 4) := rfl
                omega
              exact div_step (n + 4) h1.1 h1.2 h2.1 h2.2 heq

lemma M_grow (n : ℕ) : 2 * M (n + 6) ≥ n + 1 := by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      have h1 := ih (n + 1) (by omega)
      have h2 := ih n (by omega)
      have heq : M (n + 8) = M (n + 7) + M (n + 6) := rfl
      have eq1 : n + 2 + 6 = n + 8 := by omega
      have eq2 : n + 1 + 6 = n + 7 := by omega
      rw [eq1]
      rw [eq2] at h1
      omega

lemma mem_cons_self_lem (x : ℕ) (xs : List ℕ) : x ∈ x :: xs := by simp
lemma mem_cons_of_mem_lem {x y : ℕ} {xs : List ℕ} (h : y ∈ xs) : y ∈ x :: xs := by simp [h]

lemma count_zero_of_gt {L : List ℕ} (h : ∀ y ∈ L, y > 2) : L.count 2 = 0 := by
  induction' L with x xs ih
  · rfl
  · have hx : x > 2 := h x (mem_cons_self_lem x xs)
    have h_neq : x ≠ 2 := by omega
    have h_xs : ∀ y ∈ xs, y > 2 := fun y hy => h y (mem_cons_of_mem_lem hy)
    have ih_xs := ih h_xs
    rw [List.count_cons]
    simp [h_neq, ih_xs]

lemma sorted_2_count (L : List ℕ) (h_sorted : L.Pairwise (· ≤ ·))
    (h_min : ∀ x ∈ L, 2 ≤ x) (k : ℕ) (hk : k ≤ L.count 2) (i : ℕ) (hi : i < k) (h_len : i < L.length) :
    L.get ⟨i, h_len⟩ = 2 := by
  induction' L with x xs ih generalizing k i
  · exfalso
    have hk_zero : List.count 2 [] = 0 := rfl
    omega
  · have hx_min := h_min x (mem_cons_self_lem x xs)
    by_cases hx : x = 2
    · have h_count_x : (x :: xs).count 2 = 1 + xs.count 2 := by
        rw [List.count_cons]
        simp [hx]
        omega
      cases i
      · exact hx
      · rename_i i'
        have h_sorted_xs : xs.Pairwise (· ≤ ·) := List.Pairwise.of_cons h_sorted
        have h_min_xs : ∀ y ∈ xs, 2 ≤ y := fun y hy => h_min y (mem_cons_of_mem_lem hy)
        have hk_xs : k - 1 ≤ xs.count 2 := by
          rw [h_count_x] at hk
          omega
        have hi_xs : i' < k - 1 := by omega
        have h_len_xs : i' < xs.length := by
          dsimp at h_len
          omega
        exact ih h_sorted_xs h_min_xs (k - 1) hk_xs i' hi_xs h_len_xs
    · have h_count_x : (x :: xs).count 2 = xs.count 2 := by
        rw [List.count_cons]
        simp [hx]
      have hx_gt : x > 2 := by omega
      have h_all : ∀ y ∈ xs, y > 2 := by
        intro y hy
        have h_le := List.rel_of_pairwise_cons h_sorted hy
        omega
      have h_no_2 : xs.count 2 = 0 := count_zero_of_gt h_all
      exfalso
      rw [h_count_x, h_no_2] at hk
      omega

def x3 (n : ℕ) : ZMod 3 := a n
def y3 (n : ℕ) : ZMod 3 := b n

lemma x3_y3_step (n : ℕ) :
  x3 (n + 2) = x3 (n + 1) * y3 n + x3 n * y3 (n + 1) ∧
  y3 (n + 2) = x3 (n + 1) * y3 n - x3 n * y3 (n + 1) := by
  dsimp [x3, y3]
  have h := a_b_step' n
  exact ⟨by rw [h.1]; push_cast; rfl, by rw [h.2]; push_cast; rfl⟩

def step_state3 (s : ℕ × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) : ℕ × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 :=
  let n3 := s.1
  let x1 := s.2.1
  let y1 := s.2.2.1
  let x2 := s.2.2.2.1
  let y2 := s.2.2.2.2
  ((n3 + 1) % 3, x2, y2, x2 * y1 + x1 * y2, x2 * y1 - x1 * y2)

def valid_states3_n3 : List (Nat × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) := [
  (0, 1, 1, 2, 1),
  (1, 2, 1, 0, 1),
  (2, 0, 1, 2, 1),
  (0, 2, 1, 2, 2),
  (1, 2, 2, 0, 1)
]

lemma step_valid3 (s : ℕ × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) (h : s ∈ valid_states3_n3) :
  step_state3 s ∈ valid_states3_n3 := by
  revert s h
  decide

lemma valid_n3 (n : ℕ) : (n % 3, x3 n, y3 n, x3 (n + 1), y3 (n + 1)) ∈ valid_states3_n3 := by
  induction' n with n ih
  · decide
  · have h_step := x3_y3_step n
    have h_valid := step_valid3 _ ih
    have h_n_mod : (n + 1) % 3 = (n % 3 + 1) % 3 := by omega
    dsimp [step_state3] at h_valid
    rw [h_n_mod]
    rw [h_step.1, h_step.2]
    exact h_valid

lemma mod3_zero_implies_n_mod_3_eq_2 (n : ℕ) (h : x3 n = 0) : n % 3 = 2 := by
  have h_val := valid_n3 n
  have h_prop : ∀ s : ℕ × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3, s ∈ valid_states3_n3 → s.2.1 = 0 → s.1 = 2 := by decide
  exact h_prop (n % 3, x3 n, y3 n, x3 (n + 1), y3 (n + 1)) h_val h

def x7 (n : ℕ) : ZMod 7 := a n
def y7 (n : ℕ) : ZMod 7 := b n

lemma x7_y7_step (n : ℕ) :
  x7 (n + 2) = x7 (n + 1) * y7 n + x7 n * y7 (n + 1) ∧
  y7 (n + 2) = x7 (n + 1) * y7 n - x7 n * y7 (n + 1) := by
  dsimp [x7, y7]
  have h := a_b_step' n
  exact ⟨by rw [h.1]; push_cast; rfl, by rw [h.2]; push_cast; rfl⟩

def step_state7 (s : ℕ × ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7) : ℕ × ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7 :=
  let n3 := s.1
  let x1 := s.2.1
  let y1 := s.2.2.1
  let x2 := s.2.2.2.1
  let y2 := s.2.2.2.2
  ((n3 + 1) % 3, x2, y2, x2 * y1 + x1 * y2, x2 * y1 - x1 * y2)

def valid_states7_n3 : List (Nat × ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7) := [
  (0, 1, 1, 2, 1), (1, 2, 1, 3, 1), (2, 3, 1, 5, 1), (0, 5, 1, 1, 2),
  (1, 1, 2, 4, 5), (2, 4, 5, 6, 3), (0, 6, 3, 0, 4), (1, 0, 4, 3, 4),
  (2, 3, 4, 5, 5), (0, 5, 5, 0, 5), (1, 0, 5, 4, 3), (2, 4, 3, 6, 6),
  (0, 6, 6, 0, 1), (1, 0, 1, 6, 1), (2, 6, 1, 6, 6), (0, 6, 6, 0, 5),
  (1, 0, 5, 2, 5), (2, 2, 5, 3, 3), (0, 3, 3, 0, 2), (1, 0, 2, 6, 1),
  (2, 6, 1, 5, 5), (0, 5, 5, 0, 3), (1, 0, 3, 1, 6), (2, 1, 6, 3, 3),
  (0, 3, 3, 0, 1), (1, 0, 1, 3, 4), (2, 3, 4, 3, 3), (0, 3, 3, 0, 3),
  (1, 0, 3, 2, 5), (2, 2, 5, 6, 6), (0, 6, 6, 0, 4)
]

lemma step_valid7 (s : ℕ × ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7) (h : s ∈ valid_states7_n3) :
  step_state7 s ∈ valid_states7_n3 := by
  revert s h
  decide

lemma valid_n7 (n : ℕ) : (n % 3, x7 n, y7 n, x7 (n + 1), y7 (n + 1)) ∈ valid_states7_n3 := by
  induction' n with n ih
  · decide
  · have h_step := x7_y7_step n
    have h_valid := step_valid7 _ ih
    have h_n_mod : (n + 1) % 3 = (n % 3 + 1) % 3 := by omega
    dsimp [step_state7] at h_valid
    rw [h_n_mod]
    rw [h_step.1, h_step.2]
    exact h_valid

lemma mod7_zero_implies_n_mod_3_eq_1 (n : ℕ) (h : x7 n = 0) : n % 3 = 1 := by
  have h_val := valid_n7 n
  have h_prop : ∀ s : ℕ × ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7, s ∈ valid_states7_n3 → s.2.1 = 0 → s.1 = 1 := by decide
  exact h_prop (n % 3, x7 n, y7 n, x7 (n + 1), y7 (n + 1)) h_val h

lemma a_not_zero (n : ℕ) : a n ≠ 0 := by
  intro h
  have h3 : x3 n = 0 := by dsimp [x3]; rw [h]; rfl
  have h7 : x7 n = 0 := by dsimp [x7]; rw [h]; rfl
  have h_n3 := mod3_zero_implies_n_mod_3_eq_2 n h3
  have h_n7 := mod7_zero_implies_n_mod_3_eq_1 n h7
  omega

lemma k_le_M (k : ℕ) (n : ℕ) (hn : n ≥ 2 * k + 6) : k ≤ M n := by
  have h_grow := M_grow (n - 6)
  have h_eq : n - 6 + 6 = n := by omega
  rw [h_eq] at h_grow
  have : 2 * M n ≥ 2 * k + 1 := by omega
  omega

lemma int_dvd_natAbs {k : ℕ} {x : ℤ} (h : (2:ℤ)^k ∣ x) : 2^k ∣ x.natAbs := by
  have : (2:ℤ)^k = ((2^k : ℕ) : ℤ) := by push_cast; rfl
  rw [this] at h
  rcases h with ⟨c, hc⟩
  use c.natAbs
  calc x.natAbs = ((2^k : ℕ) : ℤ).natAbs * c.natAbs := by
        rw [hc, natAbs_mul]
    _ = 2^k * c.natAbs := by rfl

lemma sortedLE_to_pairwise (L : List ℕ) (h : L.SortedLE) : L.Pairwise (· ≤ ·) := by
  apply List.pairwise_iff_get.mpr
  intro i j hij
  apply h
  exact le_of_lt hij

lemma kth_eq_2 (x : ℤ) (hx : x ≠ 0) (k : ℕ) (hk0 : k ≠ 0) (hk2 : 2^k ∣ x.natAbs) :
    kth_prime_factor k x = 2 := by
  have n_abs_ne : x.natAbs ≠ 0 := by exact fun h => hx (Int.natAbs_eq_zero.mp h)
  have h_count : k ≤ List.count 2 (primeFactorsList x.natAbs) := by
    rw [Nat.primeFactorsList_count_eq]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two n_abs_ne).mp hk2
  have h_len : k ≤ (primeFactorsList x.natAbs).length := by
    calc k ≤ List.count 2 (primeFactorsList x.natAbs) := h_count
      _ ≤ (primeFactorsList x.natAbs).length := List.count_le_length
  have h_len2 : ¬ (k - 1 ≥ (primeFactorsList x.natAbs).length) := by omega
  unfold kth_prime_factor
  rw [dif_neg hk0, dif_neg h_len2]
  have h_sorted : (primeFactorsList x.natAbs).Pairwise (· ≤ ·) := sortedLE_to_pairwise _ (Nat.primeFactorsList_sorted x.natAbs)
  have h_min : ∀ p ∈ primeFactorsList x.natAbs, 2 ≤ p := by
    intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactorsList hp
    exact Nat.Prime.two_le hp_prime
  have h_k_min : k - 1 < k := by omega
  have h_len_minus : k - 1 < (primeFactorsList x.natAbs).length := by omega
  exact sorted_2_count (primeFactorsList x.natAbs) h_sorted h_min k h_count (k - 1) h_k_min h_len_minus

theorem A382590_conjecture_kth_prime_factor_is_eventually_periodic :
  ∀ k : ℕ, k ≥ 2 →
    ∃ N₀ p : ℕ, p > 0 ∧ ∀ n : ℕ, n ≥ N₀ →
      kth_prime_factor k (A382590 (n + p)) = kth_prime_factor k (A382590 n) := by
  intro k hk
  use 2 * k + 6, 1
  constructor
  · decide
  · intro n hn
    have hn_p : n + 1 ≥ 2 * k + 6 := by omega
    have hk_ne_0 : k ≠ 0 := by omega
    have h_a_n : a n ≠ 0 := a_not_zero n
    have h_a_n_p : a (n + 1) ≠ 0 := a_not_zero (n + 1)
    have hk_M_n : k ≤ M n := k_le_M k n hn
    have hdvd_n : 2^k ∣ (a n).natAbs := by
      have hdvd1 := (M_div n).1
      have hk_le : (2:ℤ)^k ∣ (2:ℤ)^(M n) := by
        use (2:ℤ)^(M n - k)
        have : k + (M n - k) = M n := Nat.add_sub_of_le hk_M_n
        calc (2:ℤ)^(M n) = (2:ℤ)^(k + (M n - k)) := by rw [this]
          _ = (2:ℤ)^k * (2:ℤ)^(M n - k) := by exact pow_add 2 k (M n - k)
      have hdvd2 : (2:ℤ)^k ∣ a n := dvd_trans hk_le hdvd1
      exact int_dvd_natAbs hdvd2
    have hk_M_n_p : k ≤ M (n + 1) := k_le_M k (n + 1) hn_p
    have hdvd_n_p : 2^k ∣ (a (n + 1)).natAbs := by
      have hdvd1 := (M_div (n + 1)).1
      have hk_le : (2:ℤ)^k ∣ (2:ℤ)^(M (n + 1)) := by
        use (2:ℤ)^(M (n + 1) - k)
        have : k + (M (n + 1) - k) = M (n + 1) := Nat.add_sub_of_le hk_M_n_p
        calc (2:ℤ)^(M (n + 1)) = (2:ℤ)^(k + (M (n + 1) - k)) := by rw [this]
          _ = (2:ℤ)^k * (2:ℤ)^(M (n + 1) - k) := by exact pow_add 2 k (M (n + 1) - k)
      have hdvd2 : (2:ℤ)^k ∣ a (n + 1) := dvd_trans hk_le hdvd1
      exact int_dvd_natAbs hdvd2
    have h_a_n_eq : A382590 n = a n := rfl
    have h_a_n_p_eq : A382590 (n + 1) = a (n + 1) := rfl
    rw [h_a_n_eq, h_a_n_p_eq]
    have heq_n : kth_prime_factor k (a n) = 2 := kth_eq_2 (a n) h_a_n k hk_ne_0 hdvd_n
    have heq_n_p : kth_prime_factor k (a (n + 1)) = 2 := kth_eq_2 (a (n + 1)) h_a_n_p k hk_ne_0 hdvd_n_p
    rw [heq_n_p, heq_n]

theorem A382590_conjecture_kth_prime_factor_is_eventually_periodic.disproof : ¬ (type_of% @A382590_conjecture_kth_prime_factor_is_eventually_periodic) := sorry

