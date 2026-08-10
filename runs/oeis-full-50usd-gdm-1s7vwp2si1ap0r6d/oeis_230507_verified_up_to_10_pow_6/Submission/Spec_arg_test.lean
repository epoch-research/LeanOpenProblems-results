
import FormalConjectures.Util.ProblemImports
open Nat Finset

namespace OeisA230507

namespace OeisA230507

/-- The condition $2m + 1$ and $2m^3 + 1$ are both prime, for $m \in \mathbb{N}$. -/
def S_condition (m : ℕ) : Prop :=
  Nat.Prime (2 * m + 1) ∧ Nat.Prime (2 * m ^ 3 + 1)

instance (m : ℕ) : Decidable (S_condition m) :=
  instDecidableAnd

/--
A230507: Number of ways to write $n = a + b + c$ with $a \le b \le c$, where $a, b, c$ are among those numbers $m$ (terms of A230506) with $2m + 1$ and $2m^3 + 1$ both prime.
We rely on the bounds $1 \le a$ to ensure the summands are positive.
-/
def A230507 (n : ℕ) : ℕ :=
  -- Iterate over 'a' satisfying 1 <= a <= n/3.
  Finset.sum (Finset.Icc 1 (n / 3)) fun a ↦
    -- Iterate over 'b' satisfying a <= b <= (n-a)/2.
    Finset.sum (Finset.Icc a ((n - a) / 2)) fun b ↦
      let c := n - a - b
      -- Count 1 if a, b, and c all satisfy the special prime condition.
      if S_condition a ∧ S_condition b ∧ S_condition c
      then 1
      else 0

section ConjectureDefs

/-- Condition for $x$ and $y$ in Conjecture (ii): $x > 0$ and $2x+1$ and $2x^4-1$ are both prime. -/
def P2_condition (m : ℕ) : Prop :=
  m > 0 ∧ Nat.Prime (2 * m + 1) ∧ Nat.Prime (2 * m ^ 4 - 1)

/-- Condition for $z$ in Conjecture (ii): $z > 0$ and $2z-1$ and $2z^4-1$ are both prime. Note: $2z-1$ requires $2z \ge 1$, which is true for $z>0$. -/
def Z_condition (m : ℕ) : Prop :=
  m > 0 ∧ Nat.Prime (2 * m - 1) ∧ Nat.Prime (2 * m ^ 4 - 1)

end ConjectureDefs

set_option maxRecDepth 10000

def pow_fast_aux (x : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | _, 0, _ => 1
  | fuel + 1, n, m =>
    if n = 1 then x % m
    else if n % 2 == 0 then
      let y := pow_fast_aux x fuel (n / 2) m
      (y * y) % m
    else
      let y := pow_fast_aux x fuel (n / 2) m
      (y * y * x) % m

def pow_fast (x : ℕ) (n : ℕ) (m : ℕ) : ℕ :=
  pow_fast_aux x n n m

theorem pow_fast_aux_eq (x fuel n m : ℕ) (hm : 1 < m) (h_fuel : n ≤ fuel) :
    pow_fast_aux x fuel n m = (x ^ n) % m := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    simp [pow_fast_aux]
    exact (Nat.mod_eq_of_lt hm).symm
  | succ fuel ih =>
    cases n with
    | zero =>
      simp [pow_fast_aux]
      exact (Nat.mod_eq_of_lt hm).symm
    | succ n =>
      by_cases hn1 : n = 0
      · subst hn1
        simp [pow_fast_aux]
      · have hn_not_zero : n ≠ 0 := hn1
        have h_cond : n + 1 ≠ 1 := by omega
        simp only [pow_fast_aux, h_cond, ↓reduceIte]
        by_cases heven : (n + 1) % 2 = 0
        · have heven' : ((n + 1) % 2 == 0) = true := by simp [heven]
          simp [heven']
          have h_div : (n + 1) / 2 ≤ fuel := by omega
          rw [ih _ h_div]
          rw [← Nat.mul_mod]
          congr 1
          rw [← Nat.pow_add]
          congr 1
          omega
        · have heven' : ((n + 1) % 2 == 0) = false := by simp [heven]
          simp [heven']
          have h_div : (n + 1) / 2 ≤ fuel := by omega
          rw [ih _ h_div]
          rw [Nat.mul_mod, ← Nat.mul_mod (x ^ ((n + 1) / 2)) (x ^ ((n + 1) / 2)), ← Nat.mul_mod]
          congr 1
          rw [← Nat.pow_add, ← Nat.pow_succ]
          congr 1
          omega

theorem pow_fast_eq (x n m : ℕ) (hm : 1 < m) :
    pow_fast x n m = (x ^ n) % m := by
  apply pow_fast_aux_eq x n n m hm (by rfl)

theorem zmod_pow_eq_pow_fast (p : ℕ) (hp : 1 < p) (a n : ℕ) :
    (a : ZMod p) ^ n = (pow_fast a n p : ZMod p) := by
  have : NeZero p := ⟨by omega⟩
  rw [pow_fast_eq a n p hp]
  rw [ZMod.natCast_mod]
  push_cast
  rfl

theorem dvd_prime_of_dvd_prod (q : ℕ) (hq : q.Prime) (l : List ℕ) (hl : ∀ x ∈ l, x.Prime) (h_div : q ∣ l.prod) :
    ∃ x ∈ l, q = x := by
  induction l with
  | nil =>
    simp at h_div
    exact (hq.ne_one h_div).elim
  | cons x xs ih =>
    have h_prim_x : x.Prime := hl x (by simp)
    have h_prim_xs : ∀ y ∈ xs, y.Prime := fun y hy => hl y (by simp [hy])
    simp only [List.prod_cons] at h_div
    have h_dvd : q ∣ x ∨ q ∣ xs.prod := (Nat.Prime.dvd_mul hq).mp h_div
    cases h_dvd with
    | inl h1 =>
      use x
      simp only [List.mem_cons, true_or, true_and]
      exact Nat.Prime.eq_one_or_self_of_dvd h_prim_x q h1 |>.resolve_left hq.ne_one
    | inr h2 =>
      obtain ⟨y, hy, h_eq⟩ := ih h_prim_xs h2
      use y
      simp [hy, h_eq]

theorem lucas_primality_helper (p : ℕ) (a : ℕ) (l : List ℕ)
    (hp : 1 < p)
    (hl : ∀ x ∈ l, x.Prime)
    (h_prod : l.prod = p - 1)
    (ha : pow_fast a (p - 1) p = 1)
    (hd : ∀ q ∈ l, pow_fast a ((p - 1) / q) p ≠ 1) :
    Nat.Prime p := by
  have ha_zmod : (a : ZMod p) ^ (p - 1) = 1 := by
    change ((a : ℕ) : ZMod p) ^ (p - 1) = 1
    rw [zmod_pow_eq_pow_fast p hp a (p - 1)]
    rw [ha]
    push_cast
    rfl
  have hd_zmod : ∀ q : ℕ, q.Prime → q ∣ p - 1 → (a : ZMod p) ^ ((p - 1) / q) ≠ 1 := by
    intro q hq hq_div
    have h_q_div : q ∣ l.prod := by rwa [h_prod]
    have h_mem : ∃ x ∈ l, q = x := dvd_prime_of_dvd_prod q hq l hl h_q_div
    rcases h_mem with ⟨x, hx_in, rfl⟩
    have h_hd : pow_fast a ((p - 1) / q) p ≠ 1 := hd q hx_in
    change ((a : ℕ) : ZMod p) ^ ((p - 1) / q) ≠ 1
    rw [zmod_pow_eq_pow_fast p hp a ((p - 1) / q)]
    intro hc
    have h_val := congr_arg ZMod.val hc
    rw [ZMod.val_natCast] at h_val
    haveI : Fact (1 < p) := ⟨hp⟩
    rw [ZMod.val_one p] at h_val
    have h_lt : pow_fast a ((p - 1) / q) p < p := by
      rw [pow_fast_eq a ((p - 1) / q) p hp]
      exact Nat.mod_lt _ (by omega)
    rw [Nat.mod_eq_of_lt h_lt] at h_val
    exact h_hd h_val
  exact lucas_primality p a ha_zmod hd_zmod

def check_range (f : ℕ → Bool) (start len : ℕ) : Bool :=
  match len with
  | 0 => true
  | l + 1 => f start && check_range f (start + 1) l

theorem check_range_iff (f : ℕ → Bool) (start len : ℕ) :
    check_range f start len = true ↔ ∀ i, start ≤ i ∧ i < start + len → f i = true := by
  induction len generalizing start with
  | zero =>
    simp [check_range]
  | succ len ih =>
    simp only [check_range, Bool.and_eq_true]
    rw [ih]
    constructor
    · intro ⟨h_start, h_rest⟩ i hi
      rcases hi with ⟨hi1, hi2⟩
      by_cases h_eq : i = start
      · subst h_eq; exact h_start
      · have : start + 1 ≤ i := by omega
        exact h_rest i ⟨by omega, by omega⟩
    · intro h
      constructor
      · exact h start ⟨by omega, by omega⟩
      · intro i hi
        exact h i ⟨by omega, by omega⟩

def check_range_2d (f : ℕ → Bool) (start num_blocks block_size : ℕ) : Bool :=
  match num_blocks with
  | 0 => true
  | b + 1 => check_range f start block_size && check_range_2d f (start + block_size) b block_size

theorem check_range_2d_iff (f : ℕ → Bool) (start num_blocks block_size : ℕ) :
    check_range_2d f start num_blocks block_size = true ↔ ∀ i, start ≤ i ∧ i < start + num_blocks * block_size → f i = true := by
  induction num_blocks generalizing start with
  | zero =>
    simp [check_range_2d]

theorem prime_S_p2_6134 : Nat.Prime 461595228209 :=
  lucas_primality_helper 461595228209 3 [2, 2, 2, 2, 3067, 3067, 3067] (by decide) (by decide) (by decide) (by decide) sorry

end OeisA230507
