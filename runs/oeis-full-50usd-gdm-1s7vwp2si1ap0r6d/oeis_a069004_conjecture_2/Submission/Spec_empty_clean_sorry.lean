import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Nat Finset

def no_divisors (p : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | k + 1 => if (k + 1) ∣ p then false else no_divisors p k

lemma no_divisors_spec (p : ℕ) (k : ℕ) :
    no_divisors p k = true ↔ ∀ m, 2 ≤ m → m ≤ k → ¬ m ∣ p := by
  induction k with
  | zero =>
    simp [no_divisors]
    intro m hm h_le
    omega
  | succ k ih =>
    rcases k with _ | k
    · simp [no_divisors]
      intro m hm h_le
      omega
    · -- k >= 1, so k + 2
      have h_step : no_divisors p (k + 2) = if (k + 2) ∣ p then false else no_divisors p (k + 1) := rfl
      rw [h_step]
      split_ifs with h_dvd
      · simp
        use k + 2
        refine ⟨by omega, le_rfl, h_dvd⟩
      · rw [ih]
        constructor
        · intro h m hm h_le mdvd
          rcases eq_or_lt_of_le h_le with rfl | h_lt
          · exact h_dvd mdvd
          · exact h m hm (Nat.le_of_lt_succ h_lt) mdvd
        · intro h m hm h_le
          exact h m hm (Nat.le_succ_of_le h_le)

lemma prime_fast_iff (p : ℕ) :
    p.Prime ↔ 2 ≤ p ∧ no_divisors p (sqrt p) = true := by
  rw [prime_def_le_sqrt, no_divisors_spec]

theorem count_eq_ico_sum (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    count p n = (Ico 0 n).sum (fun i => if p i then 1 else 0) := by
  induction n with
  | zero =>
    rw [count_zero]
    rfl
  | succ n ih =>
    rw [count_succ]
    rw [ih]
    rw [sum_Ico_succ_top (by omega)]

theorem sub_div_two_le (x : ℕ) : x - x / 2 ≤ (x + 1) / 2 := by
  omega

def sum_tree_fuel (p : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, L, R => if L = R then (if p L then 1 else 0) else 0
  | depth + 1, L, R =>
    if R < L then 0
    else if R = L then (if p L then 1 else 0)
    else
      let M := L + (R - L) / 2
      sum_tree_fuel p depth L M + sum_tree_fuel p depth (M + 1) R

theorem sum_tree_fuel_eq (p : ℕ → Bool) (depth : ℕ) (L R : ℕ) (h_range : R - L < 2^depth) :
    sum_tree_fuel p depth L R = (Ico L (R + 1)).sum (fun i => if p i then 1 else 0) := by
  induction depth generalizing L R with
  | zero =>
    simp at h_range
    dsimp [sum_tree_fuel]
    by_cases h_eq : L = R
    · subst h_eq
      rw [Ico_succ_singleton, sum_singleton]
      simp
    · have h_le : R ≤ L := Nat.le_of_sub_eq_zero h_range
      have h_lt : R < L := Nat.lt_of_le_of_ne h_le (Ne.symm h_eq)
      have : R + 1 ≤ L := h_lt
      rw [if_neg h_eq]
      rw [Ico_eq_empty_of_le this, sum_empty]
  | succ depth ih =>
    dsimp [sum_tree_fuel]
    by_cases h_lt : R < L
    · -- R < L
      rw [if_pos h_lt]
      have : R + 1 ≤ L := h_lt
      rw [Ico_eq_empty_of_le this, sum_empty]
    · -- L ≤ R
      rw [if_neg h_lt]
      by_cases h_eq : R = L
      · -- R = L
        rw [if_pos h_eq]
        subst h_eq
        rw [Ico_succ_singleton, sum_singleton]
      · -- L < R
        rw [if_neg h_eq]
        have h_lt_LR : L < R := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h_lt) (Ne.symm h_eq)
        have h_pow : 2^(depth + 1) = 2^depth * 2 := by ring
        rw [h_pow] at h_range
        have h_L_le_M : L ≤ L + (R - L) / 2 := Nat.le_add_right L ((R - L) / 2)
        have h_sub : 0 < R - L := Nat.sub_pos_of_lt h_lt_LR
        have h_div_lt : (R - L) / 2 < R - L := Nat.div_lt_self h_sub (by decide)
        have h_M_lt_R : L + (R - L) / 2 < R := by
          have : L + (R - L) / 2 < L + (R - L) := Nat.add_lt_add_left h_div_lt L
          rwa [Nat.add_sub_of_le (Nat.le_of_lt h_lt_LR)] at this
        have h_range1 : L + (R - L) / 2 - L < 2^depth := by
          rw [Nat.add_sub_cancel_left]
          rwa [Nat.div_lt_iff_lt_mul (by decide)]
        have h_range2 : R - (L + (R - L) / 2 + 1) < 2^depth := by
          have h_eq2 : R - (L + (R - L) / 2 + 1) = (R - L) - (R - L) / 2 - 1 := by omega
          rw [h_eq2]
          have h_le3 := sub_div_two_le (R - L)
          have h_div_le : (R - L + 1) / 2 ≤ 2^depth := by omega
          omega
        rw [ih L (L + (R - L) / 2) h_range1, ih (L + (R - L) / 2 + 1) R h_range2]
        have h_split1 : L ≤ L + (R - L) / 2 + 1 := by omega
        have h_split2 : L + (R - L) / 2 + 1 ≤ R + 1 := by omega
        rw [sum_Ico_consecutive _ h_split1 h_split2]


def get_chunk (i : ℕ) : String := ""

def get_chunk_a (i : ℕ) : String := ""
def get_char_at_loop (s : String) (pos : String.Pos) : ℕ → Char
  | 0 => s.get pos
  | offset + 1 => get_char_at_loop s (s.next pos) offset

def decode_val (c_val : ℕ) : ℕ :=
  if c_val < 1000 then 0
  else if c_val < 55296 then c_val - 1000
  else c_val - 1000 - 2048

def get_table_val (x : ℕ) : ℕ :=
  let chunk_idx := x / 50000
  let offset := x % 50000
  let s := get_chunk chunk_idx
  decode_val (get_char_at_loop s 0 offset).toNat

def fast_prime_bool (p : ℕ) : Bool :=
  if p < 2 then false
  else if 512720 < p then
    no_divisors p (sqrt p)
  else
    let v := get_table_val p
    if v == 0 then
      no_divisors p (sqrt p)
    else
      let d := v
      if 1 < d ∧ d < p ∧ d ∣ p then
        false
      else
        no_divisors p (sqrt p)

theorem fast_prime_bool_eq (p : ℕ) :
    fast_prime_bool p = true ↔ p.Prime := by
  dsimp [fast_prime_bool]
  by_cases h_lt2 : p < 2
  · rw [if_pos h_lt2]
    simp
    intro hp
    have := hp.two_le
    omega
  · rw [if_neg h_lt2]
    by_cases h_gt : 512720 < p
    · rw [if_pos h_gt]
      rw [prime_fast_iff p]
      have : 2 ≤ p := by omega
      simp [this]
    · rw [if_neg h_gt]
      split_ifs with h_v h_dvd
      · rw [prime_fast_iff p]
        have : 2 ≤ p := by omega
        simp [this]
      · simp
        intro hp
        rcases h_dvd with ⟨hd1, hd2, hd3⟩
        have h_contra := hp.eq_one_or_self_of_dvd _ hd3
        rcases h_contra with h1_eq | h2_eq
        · rw [h1_eq] at hd1; omega
        · rw [h2_eq] at hd2; omega
      · rw [prime_fast_iff p]
        have : 2 ≤ p := by omega
        simp [this]

theorem primeCounting_512720_eq : Nat.primeCounting 512720 = sum_tree_fuel fast_prime_bool 20 0 512720 := by
  change count Nat.Prime 512721 = sum_tree_fuel fast_prime_bool 20 0 512720
  rw [count_eq_ico_sum]
  rw [sum_tree_fuel_eq _ 20 0 512720 (by decide)]
  refine sum_congr rfl (fun x hx => ?_)
  rw [mem_Ico] at hx
  have h_fast := fast_prime_bool_eq x
  by_cases hp : x.Prime
  · rw [if_pos hp]
    have hf : fast_prime_bool x = true := h_fast.mpr hp
    rw [if_pos hf]
  · rw [if_neg hp]
    have hf : fast_prime_bool x = false := by
      by_contra h_contra
      have h_true : fast_prime_bool x = true := by rwa [Bool.not_eq_false] at h_contra
      have : x.Prime := h_fast.mp h_true
      contradiction
    have h_not : ¬ (fast_prime_bool x = true) := by rw [hf]; decide
    rw [if_neg h_not]

def get_table_val_a (s : ℕ) : ℕ :=
  let chunk_idx := s / 50000
  let offset := s % 50000
  let s_str := get_chunk_a chunk_idx
  decode_val (get_char_at_loop s_str 0 offset).toNat

def fast_prime_bool_a (s : ℕ) : Bool :=
  if s < 1 ∨ 512720 ≤ s then false
  else
    let p := 262881798400 + s^2
    let v := get_table_val_a s
    if v == 0 then
      no_divisors p (sqrt p)
    else
      let d := v
      if 1 < d ∧ d < p ∧ d ∣ p then
        false
      else
        no_divisors p (sqrt p)

theorem fast_prime_bool_a_eq (s : ℕ) (h1 : 1 ≤ s) (h2 : s < 512720) :
    fast_prime_bool_a s = true ↔ (262881798400 + s^2).Prime := by
  dsimp [fast_prime_bool_a]
  have h_s_bounds : ¬ (s < 1 ∨ 512720 ≤ s) := by omega
  rw [if_neg h_s_bounds]
  generalize h_p : 262881798400 + s^2 = p
  have h_p_ge_2 : 2 ≤ p := by
    rw [← h_p]
    omega
  split_ifs with h_v h_dvd
  · rw [prime_fast_iff p, iff_and_self]
    intro _
    exact h_p_ge_2
  · simp
    intro hp
    rcases h_dvd with ⟨hd1, hd2, hd3⟩
    have h_contra := hp.eq_one_or_self_of_dvd _ hd3
    rcases h_contra with h1_eq | h2_eq
    · rw [h1_eq] at hd1; omega
    · rw [h2_eq] at hd2; omega
  · rw [prime_fast_iff p, iff_and_self]
    intro _
    exact h_p_ge_2

def a (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun s => if Nat.Prime (n^2 + s^2) then 1 else 0

theorem a_512720_eq : a 512720 = sum_tree_fuel fast_prime_bool_a 20 1 512719 := by
  dsimp [a]
  rw [sum_tree_fuel_eq _ 20 1 512719 (by decide)]
  refine sum_congr rfl (fun s hs => ?_)
  rw [mem_Ico] at hs
  have h_fast := fast_prime_bool_a_eq s hs.1 hs.2
  by_cases hp : (262881798400 + s^2).Prime
  · rw [if_pos hp]
    have hf : fast_prime_bool_a s = true := h_fast.mpr hp
    rw [if_pos hf]
  · rw [if_neg hp]
    have hf : fast_prime_bool_a s = false := by
      by_contra h_contra
      have h_true : fast_prime_bool_a s = true := by rwa [Bool.not_eq_false] at h_contra
      have : (262881798400 + s^2).Prime := h_fast.mp h_true
      contradiction
    have h_not : ¬ (fast_prime_bool_a s = true) := by rw [hf]; decide
    rw [if_neg h_not]

@[default_instance 10000]
instance (priority := 10000) (p : ℕ) : Decidable (Nat.Prime p) :=
  if h : fast_prime_bool p = true then
    isTrue (by rwa [fast_prime_bool_eq] at h)
  else
    isFalse (by rwa [fast_prime_bool_eq] at h)

open scoped Nat.Prime

theorem oeis_a069004_conjecture_2.disproof :
  ¬ ((∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ a n) ∧
  (∀ n : ℕ, 1 < n → 5 * a n ≥ Nat.primeCounting n) ∧
  (Nat.primeCounting 2 = a 2) ∧
  (Nat.primeCounting 10 = a 10) ∧
  (5 * a 12 = Nat.primeCounting 12)) := by
  intro h
  have h1 := h.1
  have h_512720 := h1 512720 (by decide)
  have h_false : Nat.primeCounting 512720 < a 512720 := by
    rw [primeCounting_512720_eq]
    rw [a_512720_eq]
    sorry
  omega
