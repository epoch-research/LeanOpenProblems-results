import FormalConjectures.Util.ProblemImports

open Int
open Nat

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
  if h_len : k - 1 ≥ L.length then 1 else
  L[k - 1]

def f : ℕ → ℕ
| 0 => 0
| 1 => 0
| 2 => 0
| 3 => 0
| 4 => 1
| 5 => 1
| n + 6 => f (n + 5) + f (n + 4)

def P (n : ℕ) : Prop :=
  (2 : ℤ) ^ (f n) ∣ (A382590_pair n).1 ∧ (2 : ℤ) ^ (f n) ∣ (A382590_pair n).2

theorem P_all (n : ℕ) : P n := by
  induction n using f.induct
  case case1 => simp [P, f, A382590_pair]
  case case2 => simp [P, f, A382590_pair]
  case case3 => simp [P, f, A382590_pair]
  case case4 => simp [P, f, A382590_pair]
  case case5 => simp [P, f, A382590_pair]
  case case6 => simp [P, f, A382590_pair]
  case case7 n ih1 ih2 =>
    rw [P] at *
    obtain ⟨da1, db1⟩ := ih1
    obtain ⟨da2, db2⟩ := ih2
    rcases h1 : A382590_pair (n + 5) with ⟨a1, b1⟩
    rcases h2 : A382590_pair (n + 4) with ⟨a2, b2⟩
    have h_step : A382590_pair (n + 6) = (a1 * b2 + a2 * b1, a1 * b2 - a2 * b1) := by
      have h_def : A382590_pair (n + 6) =
        let (a_n_plus_5, b_n_plus_5) := A382590_pair (n + 5)
        let (a_n_plus_4, b_n_plus_4) := A382590_pair (n + 4)
        (a_n_plus_5 * b_n_plus_4 + a_n_plus_4 * b_n_plus_5, a_n_plus_5 * b_n_plus_4 - a_n_plus_4 * b_n_plus_5) := by rfl
      rw [h_def, h1, h2]
    rw [h_step]
    have h_f : f (n + 6) = f (n + 5) + f (n + 4) := rfl
    rw [h_f, pow_add]
    rw [h1] at da1 db1
    rw [h2] at da2 db2
    have h_term1 : (2 : ℤ) ^ f (n + 5) * (2 : ℤ) ^ f (n + 4) ∣ a1 * b2 := mul_dvd_mul da1 db2
    have h_term2_orig : (2 : ℤ) ^ f (n + 4) * (2 : ℤ) ^ f (n + 5) ∣ a2 * b1 := mul_dvd_mul da2 db1
    have h_comm : (2 : ℤ) ^ f (n + 4) * (2 : ℤ) ^ f (n + 5) = (2 : ℤ) ^ f (n + 5) * (2 : ℤ) ^ f (n + 4) := mul_comm _ _
    have h_term2 : (2 : ℤ) ^ f (n + 5) * (2 : ℤ) ^ f (n + 4) ∣ a2 * b1 := h_comm ▸ h_term2_orig
    exact ⟨dvd_add h_term1 h_term2, dvd_sub h_term1 h_term2⟩

def pair_mod15 (n : ℕ) : ZMod 15 × ZMod 15 :=
  match n with
  | 0 => (1, 1)
  | 1 => (2, 1)
  | n + 2 =>
    if n + 2 = 2 then (3, 1)
    else
      match (n + 2 - 3) % 12 with
      | 0 => (5, 1)
      | 1 => (8, 2)
      | 2 => (3, 13)
      | 3 => (5, 7)
      | 4 => (11, 14)
      | 5 => (12, 7)
      | 6 => (5, 1)
      | 7 => (2, 8)
      | 8 => (12, 7)
      | 9 => (5, 7)
      | 10 => (14, 11)
      | _ => (3, 13)

lemma pair_mod15_val (m : ℕ) (h : m ≥ 3) :
    pair_mod15 m =
      match (m - 3) % 12 with
      | 0 => (5, 1)
      | 1 => (8, 2)
      | 2 => (3, 13)
      | 3 => (5, 7)
      | 4 => (11, 14)
      | 5 => (12, 7)
      | 6 => (5, 1)
      | 7 => (2, 8)
      | 8 => (12, 7)
      | 9 => (5, 7)
      | 10 => (14, 11)
      | _ => (3, 13) := by
  rcases m with _ | _ | _ | m3
  . contradiction
  . contradiction
  . contradiction
  . rfl

theorem A382590_pair_mod15 (n : ℕ) :
    ((A382590_pair n).1 : ZMod 15) = (pair_mod15 n).1 ∧ ((A382590_pair n).2 : ZMod 15) = (pair_mod15 n).2 := by
  induction n using f.induct
  case case1 => decide
  case case2 => decide
  case case3 => decide
  case case4 => decide
  case case5 => decide
  case case6 => decide
  case case7 n ih1 ih2 =>
    obtain ⟨da1, db1⟩ := ih1
    obtain ⟨da2, db2⟩ := ih2
    rcases h1 : A382590_pair (n + 5) with ⟨a1, b1⟩
    rcases h2 : A382590_pair (n + 4) with ⟨a2, b2⟩
    have h_step : A382590_pair (n + 6) = (a1 * b2 + a2 * b1, a1 * b2 - a2 * b1) := by
      have h_def : A382590_pair (n + 6) =
        let (a_n_plus_5, b_n_plus_5) := A382590_pair (n + 5)
        let (a_n_plus_4, b_n_plus_4) := A382590_pair (n + 4)
        (a_n_plus_5 * b_n_plus_4 + a_n_plus_4 * b_n_plus_5, a_n_plus_5 * b_n_plus_4 - a_n_plus_4 * b_n_plus_5) := by rfl
      rw [h_def, h1, h2]
    rw [h_step]
    rw [h1] at da1 db1
    rw [h2] at da2 db2
    simp only [Prod.fst, Prod.snd] at *
    have h6 : n + 6 ≥ 3 := by omega
    have h5 : n + 5 ≥ 3 := by omega
    have h4 : n + 4 ≥ 3 := by omega
    rw [pair_mod15_val (n + 6) h6]
    rw [pair_mod15_val (n + 5) h5] at da1 db1
    rw [pair_mod15_val (n + 4) h4] at da2 db2
    simp only [Int.cast_add, Int.cast_mul, Int.cast_sub]
    have h_mod : n % 12 = 0
      ∨ n % 12 = 1
      ∨ n % 12 = 2
      ∨ n % 12 = 3
      ∨ n % 12 = 4
      ∨ n % 12 = 5
      ∨ n % 12 = 6
      ∨ n % 12 = 7
      ∨ n % 12 = 8
      ∨ n % 12 = 9
      ∨ n % 12 = 10
      ∨ n % 12 = 11
    := by omega
    rcases h_mod with hm0 | hm1 | hm2 | hm3 | hm4 | hm5 | hm6 | hm7 | hm8 | hm9 | hm10 | hm11
    · have m6 : (n + 6 - 3) % 12 = 3 := by omega
      have m5 : (n + 5 - 3) % 12 = 2 := by omega
      have m4 : (n + 4 - 3) % 12 = 1 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 4 := by omega
      have m5 : (n + 5 - 3) % 12 = 3 := by omega
      have m4 : (n + 4 - 3) % 12 = 2 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 5 := by omega
      have m5 : (n + 5 - 3) % 12 = 4 := by omega
      have m4 : (n + 4 - 3) % 12 = 3 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 6 := by omega
      have m5 : (n + 5 - 3) % 12 = 5 := by omega
      have m4 : (n + 4 - 3) % 12 = 4 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 7 := by omega
      have m5 : (n + 5 - 3) % 12 = 6 := by omega
      have m4 : (n + 4 - 3) % 12 = 5 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 8 := by omega
      have m5 : (n + 5 - 3) % 12 = 7 := by omega
      have m4 : (n + 4 - 3) % 12 = 6 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 9 := by omega
      have m5 : (n + 5 - 3) % 12 = 8 := by omega
      have m4 : (n + 4 - 3) % 12 = 7 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 10 := by omega
      have m5 : (n + 5 - 3) % 12 = 9 := by omega
      have m4 : (n + 4 - 3) % 12 = 8 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 11 := by omega
      have m5 : (n + 5 - 3) % 12 = 10 := by omega
      have m4 : (n + 4 - 3) % 12 = 9 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 0 := by omega
      have m5 : (n + 5 - 3) % 12 = 11 := by omega
      have m4 : (n + 4 - 3) % 12 = 10 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 1 := by omega
      have m5 : (n + 5 - 3) % 12 = 0 := by omega
      have m4 : (n + 4 - 3) % 12 = 11 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide
    · have m6 : (n + 6 - 3) % 12 = 2 := by omega
      have m5 : (n + 5 - 3) % 12 = 1 := by omega
      have m4 : (n + 4 - 3) % 12 = 0 := by omega
      rw [m6]
      rw [m5] at da1 db1
      rw [m4] at da2 db2
      simp only [if_true, if_false, Prod.fst, Prod.snd] at *
      rw [da1, db1, da2, db2]
      decide

lemma a_nonzero (n : ℕ) : (A382590_pair n).1 ≠ 0 := by
  intro h_zero
  have h_mod15 := (A382590_pair_mod15 n).1
  rw [h_zero] at h_mod15
  rcases n with _ | _ | _ | m
  · revert h_mod15; decide
  · revert h_mod15; decide
  · revert h_mod15; decide
  · have h3 : m + 3 ≥ 3 := by omega
    rw [pair_mod15_val (m + 3) h3] at h_mod15
    have h_sub : m + 3 - 3 = m := by omega
    rw [h_sub] at h_mod15
    have h_mod : m % 12 = 0
      ∨ m % 12 = 1
      ∨ m % 12 = 2
      ∨ m % 12 = 3
      ∨ m % 12 = 4
      ∨ m % 12 = 5
      ∨ m % 12 = 6
      ∨ m % 12 = 7
      ∨ m % 12 = 8
      ∨ m % 12 = 9
      ∨ m % 12 = 10
      ∨ m % 12 = 11
    := by omega
    rcases h_mod with hm0 | hm1 | hm2 | hm3 | hm4 | hm5 | hm6 | hm7 | hm8 | hm9 | hm10 | hm11
    · rw [hm0] at h_mod15; revert h_mod15; decide
    · rw [hm1] at h_mod15; revert h_mod15; decide
    · rw [hm2] at h_mod15; revert h_mod15; decide
    · rw [hm3] at h_mod15; revert h_mod15; decide
    · rw [hm4] at h_mod15; revert h_mod15; decide
    · rw [hm5] at h_mod15; revert h_mod15; decide
    · rw [hm6] at h_mod15; revert h_mod15; decide
    · rw [hm7] at h_mod15; revert h_mod15; decide
    · rw [hm8] at h_mod15; revert h_mod15; decide
    · rw [hm9] at h_mod15; revert h_mod15; decide
    · rw [hm10] at h_mod15; revert h_mod15; decide
    · rw [hm11] at h_mod15; revert h_mod15; decide

lemma count_eq_two_head {L : List ℕ} (h_sorted : L.Pairwise (· ≤ ·))
    (h_ge : ∀ x ∈ L, 2 ≤ x) (h_count : L.count 2 = C) {i : ℕ} (hi : i < C) :
    L.get ⟨i, by
      have : C ≤ L.length := by
        rw [← h_count]
        exact List.count_le_length
      omega⟩ = 2 := by
  induction L generalizing C i with
  | nil =>
    simp at h_count
    rw [← h_count] at hi
    contradiction
  | cons x xs ih =>
    simp [List.count_cons] at h_count
    have h_ge_xs : ∀ y ∈ xs, 2 ≤ y := fun y hy => h_ge y (List.mem_cons_of_mem _ hy)
    have h_sorted_xs : xs.Pairwise (· ≤ ·) := List.Pairwise.of_cons h_sorted
    split_ifs at h_count with hx
    · subst hx
      rcases i with _ | i_1
      · rfl
      · simp only [List.get_cons_succ]
        have hi_xs : i_1 < xs.count 2 := by omega
        exact ih h_sorted_xs h_ge_xs rfl hi_xs
    · have hx_ne : x ≠ 2 := hx
      have hx_gt : 2 < x := by
        have : 2 ≤ x := h_ge x (by simp)
        omega
      have h_xs_ne_two : 2 ∉ xs := by
        intro h_mem
        have h_le : x ≤ 2 := List.rel_of_pairwise_cons h_sorted h_mem
        omega
      have h_count_xs : xs.count 2 = 0 := by
        rwa [List.count_eq_zero]
      omega

lemma kth_prime_factor_eq_two_of_fn_ge (k : ℕ) (hk : k ≥ 2) (n : ℕ) (h_fn : f n ≥ k) :
    kth_prime_factor k (A382590 n) = 2 := by
  have ha : A382590 n ≠ 0 := by
    exact a_nonzero n
  have ha_abs : (A382590 n).natAbs ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr ha
  rw [kth_prime_factor]
  have hk0 : k ≠ 0 := by omega
  simp only [hk0, ↓reduceDIte]
  have h_dvd : (2 : ℤ) ^ (f n) ∣ A382590 n := (P_all n).1
  have h_dvd_abs : 2 ^ f n ∣ (A382590 n).natAbs := by
    have h_cast := Int.natAbs_dvd_natAbs.mpr h_dvd
    simp at h_cast
    exact h_cast
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have h_sub : (List.replicate (f n) 2).Subperm ((A382590 n).natAbs.primeFactorsList) := by
    rw [Nat.replicate_subperm_primeFactorsList_iff hp2 ha_abs]
    exact h_dvd_abs
  have h_len_L : (A382590 n).natAbs.primeFactorsList.length ≥ f n := by
    have h_len_sub := List.Subperm.length_le h_sub
    rw [List.length_replicate] at h_len_sub
    exact h_len_sub
  have h_k_len : k - 1 < (A382590 n).natAbs.primeFactorsList.length := by omega
  have h_not_ge : ¬ (k - 1 ≥ (A382590 n).natAbs.primeFactorsList.length) := by omega
  simp only [h_not_ge, ↓reduceDIte]
  have h_sorted : (A382590 n).natAbs.primeFactorsList.Pairwise (· ≤ ·) := 
    List.sortedLE_iff_pairwise.mp (Nat.primeFactorsList_sorted _)
  have h_ge : ∀ x ∈ (A382590 n).natAbs.primeFactorsList, 2 ≤ x := by
    intro x hx
    have hp : Nat.Prime x := Nat.prime_of_mem_primeFactorsList hx
    exact hp.two_le
  have h_count_replicate : (List.replicate (f n) 2).count 2 = f n := by
    simp
  have h_count_L : (A382590 n).natAbs.primeFactorsList.count 2 ≥ f n := by
    have h_c_le := List.Subperm.count_le h_sub 2
    rw [h_count_replicate] at h_c_le
    exact h_c_le
  have hi_count : k - 1 < (A382590 n).natAbs.primeFactorsList.count 2 := by omega
  have h_get_eq := count_eq_two_head h_sorted h_ge rfl hi_count
  exact h_get_eq

lemma f_ge_one (n : ℕ) (hn : n ≥ 4) : f n ≥ 1 := by
  induction n using f.induct
  case case1 => contradiction
  case case2 => contradiction
  case case3 => contradiction
  case case4 => contradiction
  case case5 => decide
  case case6 => decide
  case case7 m ih1 ih2 =>
    have h_f : f (m + 6) = f (m + 5) + f (m + 4) := rfl
    rw [h_f]
    omega

lemma f_ge_k (k : ℕ) : ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → f n ≥ k := by
  induction k with
  | zero =>
    use 0
    intro n hn
    omega
  | succ k ih =>
    obtain ⟨N0, hN0⟩ := ih
    use N0 + 6
    intro n hn
    rcases n with _ | _ | _ | _ | _ | _ | m
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · have h_f : f (m + 6) = f (m + 5) + f (m + 4) := rfl
      rw [h_f]
      have h5 : m + 5 ≥ N0 := by omega
      have h4 : m + 4 ≥ 4 := by omega
      have v1 := hN0 (m + 5) h5
      have v2 := f_ge_one (m + 4) h4
      omega

/--
A382590 This sequence appears to have a very peculiar (conjectured) property.
For any k > 1, if you take the k-th prime factor of each term, you get an eventually periodic sequence.
This seems to hold even when we change a(1) as long as it is an integer > 1.
-/
theorem A382590_conjecture_kth_prime_factor_is_eventually_periodic :
  ∀ k : ℕ, k ≥ 2 →
    ∃ N₀ p : ℕ, p > 0 ∧ ∀ n : ℕ, n ≥ N₀ →
      kth_prime_factor k (A382590 (n + p)) = kth_prime_factor k (A382590 n) := by
  intro k hk
  obtain ⟨N0, hN0⟩ := f_ge_k k
  use N0, 1
  refine ⟨by decide, ?_⟩
  intro n hn
  have h_fn : f n ≥ k := hN0 n hn
  have h_fn1 : f (n + 1) ≥ k := hN0 (n + 1) (by omega)
  have h1 := kth_prime_factor_eq_two_of_fn_ge k hk n h_fn
  have h2 := kth_prime_factor_eq_two_of_fn_ge k hk (n + 1) h_fn1
  rw [h1, h2]
