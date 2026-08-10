import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Nat Finset

def choose (m k : ℕ) : ℕ :=
  if k ≥ 12 then 0
  else
    match m % 12 with
    | 0 => match k with | 0 => 1 | _ => 0
    | 1 => match k with | 0 => 1 | 1 => 1 | _ => 0
    | 2 => match k with | 0 => 1 | 1 => 2 | 2 => 1 | _ => 0
    | 3 => match k with | 0 => 1 | 1 => 3 | 2 => 3 | 3 => 1 | _ => 0
    | 4 => match k with | 0 => 1 | 1 => 4 | 2 => 6 | 3 => 4 | 4 => 1 | _ => 0
    | 5 => match k with | 0 => 1 | 5 => 1 | _ => 0
    | 6 => match k with | 0 => 1 | 5 => 1 | 6 => 1 | _ => 0
    | 7 => match k with | 0 => 1 | 7 => 1 | _ => 0
    | 8 => match k with | 0 => 1 | 5 => 3 | 7 => 11 | 8 => 7 | _ => 0
    | 9 => match k with | 0 => 1 | 7 => 3 | 8 => 3 | 9 => 1 | _ => 0
    | 10 => match k with | 0 => 1 | 9 => 2 | 10 => 1 | _ => 0
    | 11 => match k with | 0 => 1 | 11 => 1 | _ => 0
    | _ => 0

local macro_rules
  | `(choose $m $k) => `(_root_.choose $m $k)

def A141057 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun n₁ =>
    Finset.sum (Finset.range (n - n₁ + 1)) fun n₂ =>
      (choose n n₁ * choose (n - n₁) n₂) ^ 3


lemma sum_reduction_helper (f : ℕ → ℕ) (hf : ∀ x, x ≥ 12 → f x = 0) (n : ℕ) (hn : 11 ≤ n) :
    Finset.sum (Finset.range (n + 1)) f = Finset.sum (Finset.range 12) f := by
  induction' n, hn using Nat.le_induction with n' hn' ih
  · rfl
  · rw [Finset.sum_range_succ]
    have h1 : n' + 1 ≥ 12 := by omega
    rw [hf (n' + 1) h1, add_zero]
    exact ih


lemma choose_eq_zero_of_ge_12 (m k : ℕ) (hk : k ≥ 12) : _root_.choose m k = 0 := by
  unfold _root_.choose
  split
  · rfl
  · omega

lemma choose_eq_zero_of_gt (m k : ℕ) (hk : k > m) : _root_.choose m k = 0 := by
  unfold _root_.choose
  split
  · rfl
  · rename_i h1
    have hm : m < 12 := by omega
    have hk1 : k < 12 := by omega
    interval_cases m <;> interval_cases k <;> (first | rfl | omega)


lemma sum_range_eq_sum_range_12_of_eq_zero (m : ℕ) (g : ℕ → ℕ) (hg1 : ∀ x, x ≥ 12 → g x = 0) (hg2 : ∀ x, x > m → g x = 0) :
    Finset.sum (Finset.range (m + 1)) g = Finset.sum (Finset.range 12) g := by
  by_cases h : 11 ≤ m
  · exact sum_reduction_helper g hg1 m h
  · have h_lt : m < 11 := by omega
    have h_split : Finset.range 12 = Finset.range (m + 1) ∪ Finset.filter (· ≥ m + 1) (Finset.range 12) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_filter]
      omega
    have h_disj : Disjoint (Finset.range (m + 1)) (Finset.filter (· ≥ m + 1) (Finset.range 12)) := by
      rw [Finset.disjoint_left]
      intro x hx hx1
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_filter] at hx1
      omega
    rw [h_split, Finset.sum_union h_disj]
    have h_zero : Finset.sum (Finset.filter (· ≥ m + 1) (Finset.range 12)) g = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      apply hg2
      omega
    rw [h_zero, add_zero]


lemma A_eq_sum_12 (n : ℕ) (hn : 11 ≤ n) :
    A141057 n = Finset.sum (Finset.range 12) fun n₁ => Finset.sum (Finset.range 12) fun n₂ => (_root_.choose n n₁ * _root_.choose (n - n₁) n₂) ^ 3 := by
  unfold A141057
  rw [sum_reduction_helper (fun n_1 => Finset.sum (Finset.range (n - n_1 + 1)) fun n₂ => (_root_.choose n n_1 * _root_.choose (n - n_1) n₂) ^ 3) _ n hn]
  · apply Finset.sum_congr rfl
    intro n_1 hn_1
    have hn1 : n_1 < 12 := Finset.mem_range.mp hn_1
    apply sum_range_eq_sum_range_12_of_eq_zero (n - n_1)
    · intro x hx
      have h1 : _root_.choose (n - n_1) x = 0 := choose_eq_zero_of_ge_12 (n - n_1) x hx
      simp [h1]
    · intro x hx
      have h1 : _root_.choose (n - n_1) x = 0 := choose_eq_zero_of_gt (n - n_1) x hx
      simp [h1]
  · intro x hx
    have h1 : _root_.choose n x = 0 := choose_eq_zero_of_ge_12 n x hx
    simp [h1]


lemma mod_sub_helper (n n_1 : ℕ) (hn : 11 ≤ n) (hn1 : n_1 < 12) :
    (n - n_1) % 12 = (n % 12 + 12 - n_1) % 12 := by
  omega


lemma choose_mod_12 (m k : ℕ) : _root_.choose m k = _root_.choose (m % 12) k := by
  unfold _root_.choose
  split
  · rfl
  · have h : (m % 12) % 12 = m % 12 := Nat.mod_mod m 12
    rw [h]


lemma A_eq_periodic (n : ℕ) :
    A141057 n = match n % 12 with
    | 1 => 3
    | 2 => 27
    | 3 => 381
    | 4 => 6219
    | 5 => 3
    | 6 => 6
    | 7 => 3
    | 8 => 6219
    | 9 => 381
    | 10 => 27
    | 11 => 3
    | 0 => 1
    | _ => 0 := by
  by_cases hn : 11 ≤ n
  · rw [A_eq_sum_12 n hn]
    have h_mod : n % 12 < 12 := Nat.mod_lt n (by decide)
    generalize hr : n % 12 = r
    have hr_lt : r < 12 := by omega
    have h_sum : (Finset.sum (Finset.range 12) fun n₁ => Finset.sum (Finset.range 12) fun n₂ => (_root_.choose n n₁ * _root_.choose (n - n₁) n₂) ^ 3) =
                 (Finset.sum (Finset.range 12) fun n₁ => Finset.sum (Finset.range 12) fun n₂ => (_root_.choose r n₁ * _root_.choose ((r + 12 - n₁) % 12) n₂) ^ 3) := by
      apply Finset.sum_congr rfl
      intro n_1 hn_1
      have hn1 : n_1 < 12 := Finset.mem_range.mp hn_1
      apply Finset.sum_congr rfl
      intro n_2 hn_2
      rw [choose_mod_12 n n_1, hr]
      congr 1
      rw [choose_mod_12 (n - n_1) n_2]
      congr 1
      rw [mod_sub_helper n n_1 hn hn1, hr]
    rw [h_sum]
    interval_cases r <;> rfl
  · have hn_lt : n < 11 := by omega
    interval_cases n <;> rfl


lemma prime_ge_5_mod_12_coprime (p : ℕ) (hp : 5 ≤ p) (hp_prime : Nat.Prime p) :
    p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by
  have h_mod : p % 12 < 12 := Nat.mod_lt p (by decide)
  have h2 : ¬ 2 ∣ p := by
    intro h
    have : p = 2 := (Nat.Prime.eq_one_or_self_of_dvd hp_prime 2 h).resolve_left (by decide) |>.symm
    omega
  have h3 : ¬ 3 ∣ p := by
    intro h
    have : p = 3 := (Nat.Prime.eq_one_or_self_of_dvd hp_prime 3 h).resolve_left (by decide) |>.symm
    omega
  have h_div_12 : p = 12 * (p / 12) + p % 12 := (Nat.div_add_mod p 12).symm
  interval_cases r : p % 12
  · have : 2 ∣ p := by
      rw [h_div_12]
      omega
    contradiction
  · left; rfl
  · have : 2 ∣ p := by
      use 6 * (p / 12) + 1
      omega
    contradiction
  · have : 3 ∣ p := by
      use 4 * (p / 12) + 1
      omega
    contradiction
  · have : 2 ∣ p := by
      use 6 * (p / 12) + 2
      omega
    contradiction
  · right; left; rfl
  · have : 2 ∣ p := by
      use 6 * (p / 12) + 3
      omega
    contradiction
  · right; right; left; rfl
  · have : 2 ∣ p := by
      use 6 * (p / 12) + 4
      omega
    contradiction
  · have : 3 ∣ p := by
      use 4 * (p / 12) + 3
      omega
    contradiction
  · have : 2 ∣ p := by
      use 6 * (p / 12) + 5
      omega
    contradiction
  · right; right; right; rfl



lemma A_mul_prime_pow_eq (n p k : ℕ) (hp : 5 ≤ p) (hp_prime : Nat.Prime p) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    A141057 (n * p ^ k) = A141057 (n * p ^ (k - 1)) := by
  rw [A_eq_periodic (n * p ^ k)]
  rw [A_eq_periodic (n * p ^ (k - 1))]
  have hp_mod := prime_ge_5_mod_12_coprime p hp hp_prime
  have h_pk : p ^ k = p ^ (k - 1) * p := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have h_eq : n * p ^ k = (n * p ^ (k - 1)) * p := by
    rw [h_pk]
    ring
  rw [h_eq]
  generalize hx : n * p ^ (k - 1) = X
  have hX_mod : X % 12 < 12 := Nat.mod_lt X (by decide)
  rcases hp_mod with h_p1 | h_p5 | h_p7 | h_p11
  · have h_mul : (X * p) % 12 = X % 12 := by
      rw [Nat.mul_mod, h_p1]
      simp
    rw [h_mul]
  · have h_mul : (X * p) % 12 = (X % 12 * 5) % 12 := by
      rw [Nat.mul_mod, h_p5]
    rw [h_mul]
    interval_cases r : X % 12 <;> rfl
  · have h_mul : (X * p) % 12 = (X % 12 * 7) % 12 := by
      rw [Nat.mul_mod, h_p7]
    rw [h_mul]
    interval_cases r : X % 12 <;> rfl
  · have h_mul : (X * p) % 12 = (X % 12 * 11) % 12 := by
      rw [Nat.mul_mod, h_p11]
    rw [h_mul]
    interval_cases r : X % 12 <;> rfl


theorem oeis_a141057_supercongruence_conjecture (p k n : ℕ)
    (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (h_n_pos : 1 ≤ n) :
    (A141057 (n * p ^ k) : ℤ) ≡ A141057 (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k))] := by
  have h_eq : A141057 (n * p ^ k) = A141057 (n * p ^ (k - 1)) := A_mul_prime_pow_eq n p k h_p_ge_5 hp h_k_pos h_n_pos
  rw [h_eq]

