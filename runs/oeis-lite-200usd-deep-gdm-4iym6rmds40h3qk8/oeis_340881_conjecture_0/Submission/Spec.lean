import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
Row sums of A340880.
$$a(n) = \sum_{k = 0}^{n-1} 2^{k(k+1)/2} \cdot \left( \prod_{j = k+1}^{n-1} (2^j - 1) \right)$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k ↦
    (2 ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ (2 ^ j - 1))

lemma zmod_two_two_eq_zero : (2 : ZMod 2) = 0 := by
  have : (2 : ZMod 2) = ((2 : ℕ) : ZMod 2) := rfl
  rw [this, ZMod.natCast_self]

lemma zmod_two_two_pow_eq_zero {x : ℕ} (hx : x ≥ 1) : (2 : ZMod 2) ^ x = 0 := by
  have : x ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero this with ⟨y, rfl⟩
  rw [zmod_two_two_eq_zero, zero_pow]
  exact Nat.succ_ne_zero y

lemma two_ne_zero_of_odd_prime {p : ℕ} (hp : Nat.Prime p) (h_odd : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  change ((2 : ℕ) : ZMod p) = 0 at h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h
  have : p ∣ 2 := h
  have : p ≤ 2 := Nat.le_of_dvd (by decide) this
  have : p ≥ 2 := hp.two_le
  have : p = 2 := by omega
  contradiction

lemma two_pow_T_eq_one {p : ℕ} (hp : Nat.Prime p) (h_odd : p ≠ 2) : (2 : ZMod p) ^ (2 * (p - 1)) = 1 := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_of_odd_prime hp h_odd
  have h_fermat := ZMod.pow_card_sub_one_eq_one h2ne
  rw [mul_comm, pow_mul, h_fermat, one_pow]

lemma two_mul_choose_two (x : ℕ) : 2 * Nat.choose x 2 = x * (x - 1) := by
  induction x with
  | zero => rfl
  | succ x ih =>
    induction x with
    | zero => rfl
    | succ x ih2 =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have ih_succ : 2 * Nat.choose (x + 1) 2 = (x + 1) * x := ih
      have hsub1 : x + 2 - 1 = x + 1 := by omega
      rw [hsub1]
      rw [mul_add, mul_add, ih_succ]
      ring

lemma choose_pos_of_pos {k : ℕ} (hk : k > 0) : Nat.choose (k + 1) 2 ≥ 1 := by
  have h_eq := two_mul_choose_two (k + 1)
  have h_sub : k + 1 - 1 = k := by omega
  rw [h_sub] at h_eq
  have hk_ne : k ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero hk_ne with ⟨m, rfl⟩
  have h_ring : (m + 1 + 1) * (m + 1) = m * m + 3 * m + 2 := by ring
  rw [h_ring] at h_eq
  omega

lemma choose_T_add_succ_two (p i : ℕ) :
  Nat.choose (2 * (p - 1) + i + 1) 2 = Nat.choose (i + 1) 2 + (p - 1) * (2 * (p - 1) + 2 * i + 1) := by
  have h_eq : 2 * Nat.choose (2 * (p - 1) + i + 1) 2 = 2 * (Nat.choose (i + 1) 2 + (p - 1) * (2 * (p - 1) + 2 * i + 1)) := by
    rw [mul_add]
    rw [two_mul_choose_two, two_mul_choose_two]
    have hsub1 : 2 * (p - 1) + i + 1 - 1 = 2 * (p - 1) + i := by omega
    have hsub2 : i + 1 - 1 = i := by omega
    rw [hsub1, hsub2]
    ring
  omega

lemma two_pow_choose_eq {p : ℕ} (hp : Nat.Prime p) (h_odd : p ≠ 2) (i : ℕ) :
  (2 : ZMod p) ^ Nat.choose (2 * (p - 1) + i + 1) 2 = (2 : ZMod p) ^ Nat.choose (i + 1) 2 := by
  have h_eq := choose_T_add_succ_two p i
  rw [h_eq]
  rw [pow_add]
  rw [pow_mul]
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_of_odd_prime hp h_odd
  have h_fermat := ZMod.pow_card_sub_one_eq_one h2ne
  rw [h_fermat, one_pow, mul_one]

lemma prod_T_add_eq {p n i : ℕ} (hp : Nat.Prime p) (h_odd : p ≠ 2) :
  ∏ j ∈ Ico (2 * (p - 1) + i + 1) (2 * (p - 1) + n), ((2 : ZMod p) ^ j - 1) =
  ∏ m ∈ Ico (i + 1) n, ((2 : ZMod p) ^ m - 1) := by
  set T := 2 * (p - 1)
  have h_map := map_add_left_Ico (i + 1) n T
  have h_eq_ico : Ico (T + i + 1) (T + n) = map (addLeftEmbedding T) (Ico (i + 1) n) := by
    have : T + i + 1 = T + (i + 1) := by omega
    rw [this, h_map]
  rw [h_eq_ico, prod_map]
  apply prod_congr rfl
  intro x hx
  dsimp [addLeftEmbedding]
  rw [pow_add, two_pow_T_eq_one hp h_odd, one_mul]

lemma term_lt_T_eq_zero {p n k : ℕ} (hp : Nat.Prime p) (h_odd : p ≠ 2) (hn : n ≥ 1) (hk : k < 2 * (p - 1)) :
  (2 : ZMod p) ^ Nat.choose (k + 1) 2 * ∏ j ∈ Ico (k + 1) (2 * (p - 1) + n), ((2 : ZMod p) ^ j - 1) = 0 := by
  set T := 2 * (p - 1)
  have hT : T = 2 * (p - 1) := rfl
  have h_mem : T ∈ Ico (k + 1) (T + n) := by
    rw [mem_Ico]
    constructor
    · omega
    · omega
  have h_zero : (2 : ZMod p) ^ T - 1 = 0 := by
    rw [two_pow_T_eq_one hp h_odd, sub_self]
  have h_prod_zero : ∏ j ∈ Ico (k + 1) (T + n), ((2 : ZMod p) ^ j - 1) = 0 := by
    exact Finset.prod_eq_zero h_mem h_zero
  rw [h_prod_zero, mul_zero]

lemma a_cast_eq (n p : ℕ) :
  (a n : ZMod p) = ∑ k ∈ range n, (2 : ZMod p) ^ Nat.choose (k + 1) 2 * ∏ j ∈ Ico (k + 1) n, ((2 : ZMod p) ^ j - 1) := by
  simp [a]

lemma mod_eq_of_zmod_eq {a b p : ℕ} (h : (a : ZMod p) = (b : ZMod p)) : a % p = b % p := by
  have h2 := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast] at h2
  exact h2

lemma a_two_eq_one (n : ℕ) (hn : n ≥ 1) : (a n : ZMod 2) = 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
  rw [a_cast_eq]
  rw [sum_range_succ']
  have h_sum_zero : ∑ k ∈ range m, ((2 : ZMod 2) ^ Nat.choose (k + 1 + 1) 2 * ∏ j ∈ Ico (k + 1 + 1) (m + 1), ((2 : ZMod 2) ^ j - 1)) = 0 := by
    apply sum_eq_zero
    intro k hk
    have hk_pos : k + 1 > 0 := by omega
    have h_pos := choose_pos_of_pos hk_pos
    rw [zmod_two_two_pow_eq_zero h_pos, zero_mul]
  rw [h_sum_zero, zero_add]
  dsimp
  have h_choose : Nat.choose 1 2 = 0 := rfl
  rw [h_choose, pow_zero, one_mul]
  have h_prod : ∏ j ∈ Ico 1 (m + 1), ((2 : ZMod 2) ^ j - 1) = 1 := by
    apply prod_eq_one
    intro j hj
    rw [mem_Ico] at hj
    have hj_pos : j ≥ 1 := hj.1
    rw [zmod_two_two_pow_eq_zero hj_pos]
    have : (-1 : ZMod 2) = 1 := rfl
    exact this
  rw [h_prod]

lemma oeis_340881_conjecture_odd_prime {p : ℕ} (hp : Nat.Prime p) (h_odd : p ≠ 2) (n : ℕ) (hn : n ≥ 1) :
  a (n + 2 * (p - 1)) % p = a n % p := by
  apply mod_eq_of_zmod_eq
  have h_comm : n + 2 * (p - 1) = 2 * (p - 1) + n := by omega
  rw [h_comm]
  rw [a_cast_eq, a_cast_eq]
  set T := 2 * (p - 1)
  rw [sum_range_add]
  have h_sum1_zero : ∑ x ∈ range T, ((2 : ZMod p) ^ Nat.choose (x + 1) 2 * ∏ j ∈ Ico (x + 1) (T + n), ((2 : ZMod p) ^ j - 1)) = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_range] at hx
    exact term_lt_T_eq_zero hp h_odd hn hx
  rw [h_sum1_zero, zero_add]
  apply sum_congr rfl
  intro x hx
  dsimp
  rw [two_pow_choose_eq hp h_odd x]
  rw [prod_T_add_eq hp h_odd]

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  rcases eq_or_ne p 2 with rfl | h_odd
  · -- Case p = 2
    have h_sub : 2 * (2 - 1) = 2 := rfl
    rw [h_sub]
    apply mod_eq_of_zmod_eq
    have h1 : (a (n + 2) : ZMod 2) = 1 := a_two_eq_one (n + 2) (by omega)
    have h2 : (a n : ZMod 2) = 1 := a_two_eq_one n hn
    rw [h1, h2]
  · -- Case p ≠ 2
    exact oeis_340881_conjecture_odd_prime hp h_odd n hn




