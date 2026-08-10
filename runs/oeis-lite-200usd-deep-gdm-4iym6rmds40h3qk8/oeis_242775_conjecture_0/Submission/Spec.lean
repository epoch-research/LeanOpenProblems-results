import FormalConjectures.Util.ProblemImports

open Nat Set

/-- The number $b_k$, consisting of $k$ threes. $b_k = (10^k - 1)/3$. -/
def rep_threes (k : ℕ) : ℕ := (10 ^ k - 1) / 3

/-- The number of decimal digits of $p$. -/
def num_digits (p : ℕ) : ℕ := (Nat.digits 10 p).length

/-- Concatenation of $b_k$ and $p$. -/
def concatenate (k p : ℕ) : ℕ :=
  rep_threes k * (10 ^ (num_digits p)) + p

/-- The $n$-th prime (1-indexed). -/
noncomputable def prime_of_index (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/--
A242775: Let $b_k=3\dots3$ consist of $k\ge 1$ 3's. Then $a(n)$ is the smallest $k$ such that the concatenation $b_k$ and $\operatorname{prime}(n)$ is prime, or $a(n)=0$ if there is no such prime.
-/
noncomputable def A242775 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P_n := prime_of_index n

    -- The set S of all k >= 1 such that the concatenated number is prime.
    let S : Set ℕ := { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k P_n) }

    -- Nat.sInf S is the minimum element of S. If S is empty, Nat.sInf S = 0 is the convention for ℕ.
    sInf S

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

def primeFastRec (n d f : ℕ) : Bool :=
  match f with
  | 0 => true
  | f + 1 =>
    if d * d > n then true
    else if n % d = 0 then false
    else primeFastRec n (d + 1) f

lemma primeFastRec_iff (n d f : ℕ) (h_fuel : d + f ≥ Nat.sqrt n + 1) :
  primeFastRec n d f = true ↔ ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  induction f generalizing d with
  | zero =>
    simp [primeFastRec]
    intro m hm1 hm2 hm3
    have h_d_sq : d * d > n := Nat.sqrt_lt.1 h_fuel
    have h_sq : m * m ≥ d * d := Nat.mul_self_le_mul_self hm1
    omega
  | succ f ih =>
    simp [primeFastRec]
    have h_fuel_succ : (d + 1) + f ≥ Nat.sqrt n + 1 := by omega
    rw [ih (d + 1) h_fuel_succ]
    constructor
    · rintro (h1 | ⟨h2, h3⟩) m hm1 hm2 hm3
      · have : m * m ≥ d * d := Nat.mul_self_le_mul_self hm1
        omega
      · rcases Nat.eq_or_lt_of_le hm1 with rfl | h_lt
        · have hdvd : d ∣ n := hm3
          have hmod : n % d = 0 := Nat.mod_eq_zero_of_dvd hdvd
          contradiction
        · exact h3 m h_lt hm2 hm3
    · intro h
      by_cases hd : d * d > n
      · left; exact hd
      · right
        have hd_le : d * d ≤ n := by omega
        have h_nd : ¬ d ∣ n := h d le_rfl hd_le
        constructor
        · intro h_mod
          have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h_mod
          contradiction
        · intro m hm1 hm2 hm3
          exact h m (by omega) hm2 hm3

def primeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else primeFastRec n 2 n

lemma primeFast_iff (n : ℕ) : primeFast n = true ↔ Nat.Prime n := by
  unfold primeFast
  split_ifs with h
  · simp
    intro hn
    have := hn.two_le
    omega
  · have h_le : 2 ≤ n := by omega
    rw [Nat.prime_def_le_sqrt]
    simp [h_le]
    have h_fuel : 2 + n ≥ Nat.sqrt n + 1 := by
      have : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega)
      omega
    rw [primeFastRec_iff n 2 n h_fuel]
    simp_rw [Nat.le_sqrt]

def countFastRec (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => countFastRec n + (if primeFast n then 1 else 0)

lemma countFastRec_eq_count (n : ℕ) : countFastRec n = Nat.count Nat.Prime n := by
  induction n with
  | zero =>
    simp [countFastRec]
  | succ n ih =>
    simp [countFastRec, Nat.count_succ]
    rw [ih]
    congr 1
    split_ifs with h1 h2 h2
    · rfl
    · have := (primeFast_iff n).1 h1
      contradiction
    · have := (primeFast_iff n).2 h2
      simp [this] at h1
    · rfl

theorem count_prime_2593 : Nat.count Nat.Prime 2593 = 377 := by
  rw [← countFastRec_eq_count]
  decide

theorem prime_2593 : Nat.Prime 2593 := by
  apply Nat.prime_def_le_sqrt.2
  constructor
  · decide
  · intro m hm1 hm2
    have h_sqrt : Nat.sqrt 2593 = 50 := by
      have h : 50 = Nat.sqrt 2593 := by
        apply Nat.eq_sqrt.2
        constructor <;> decide
      exact h.symm
    rw [h_sqrt] at hm2
    have h_all : ∀ m, 2 ≤ m → m ≤ 50 → ¬m ∣ 2593 := by decide
    exact h_all m hm1 hm2

theorem prime_of_index_378 : prime_of_index 378 = 2593 := by
  unfold prime_of_index
  have h1 : Nat.count Nat.Prime 2593 = 377 := count_prime_2593
  have h2 : Nat.nth Nat.Prime (Nat.count Nat.Prime 2593) = 2593 := by
    exact Nat.nth_count prime_2593
  rw [h1] at h2
  exact h2


lemma three_mul_rep_threes (k : ℕ) : 3 * rep_threes k = 10 ^ k - 1 := by
  unfold rep_threes
  have hdvd : 3 ∣ 10 ^ k - 1 := by
    induction k with
    | zero => decide
    | succ k ih =>
      have h_pow1 : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
      have h1 : 10 ^ (k + 1) - 1 = 10 * (10 ^ k - 1) + 9 := by
        rw [h_pow1]
        have h_pos : 10 * 10 ^ k ≥ 10 := by
          have : 10 ^ k ≥ 1 := Nat.one_le_pow k 10 (by decide)
          omega
        omega
      rw [h1]
      apply dvd_add
      · apply dvd_mul_of_dvd_right ih
      · decide
  exact Nat.mul_div_cancel' hdvd

lemma rep_threes_step (k : ℕ) : rep_threes (k + 2) = 100 * rep_threes k + 33 := by
  apply Nat.eq_of_mul_eq_mul_left (by decide : 3 > 0)
  rw [Nat.mul_add]
  rw [three_mul_rep_threes (k + 2)]
  have h_assoc : 3 * (100 * rep_threes k) = 100 * (3 * rep_threes k) := by
    ring
  rw [h_assoc, three_mul_rep_threes k]
  have h_pow2 : 10 ^ (k + 2) = 100 * 10 ^ k := by ring
  rw [h_pow2]
  have h_pos : 100 * 10 ^ k ≥ 100 := by
    have : 10 ^ k ≥ 1 := Nat.one_le_pow k 10 (by decide)
    omega
  omega

lemma concatenate_step (m : ℕ) :
  concatenate (2 * m + 3) 2593 = 100 * concatenate (2 * m + 1) 2593 + 73293 := by
  unfold concatenate
  have h_digits : num_digits 2593 = 4 := by
    unfold num_digits
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10 / 10)]
    rw [Nat.digits_zero]
    rfl
  rw [h_digits]
  have h_add : 2 * m + 3 = (2 * m + 1) + 2 := by omega
  rw [h_add, rep_threes_step (2 * m + 1)]
  ring

lemma div_eleven_of_odd (m : ℕ) : 11 ∣ concatenate (2 * m + 1) 2593 := by
  induction m with
  | zero =>
    have h_val : concatenate 1 2593 = 32593 := by
      unfold concatenate
      have h_digits : num_digits 2593 = 4 := by
        unfold num_digits
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10 / 10)]
        rw [Nat.digits_zero]
        rfl
      rw [h_digits]
      unfold rep_threes
      decide
    rw [h_val]
    decide
  | succ m ih =>
    have h_step : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
    rw [h_step, concatenate_step m]
    apply dvd_add
    · apply dvd_mul_of_dvd_right ih
    · decide

lemma rep_threes_step6 (k : ℕ) : rep_threes (k + 6) = 1000000 * rep_threes k + 333333 := by
  apply Nat.eq_of_mul_eq_mul_left (by decide : 3 > 0)
  rw [Nat.mul_add]
  rw [three_mul_rep_threes (k + 6)]
  have h_assoc : 3 * (1000000 * rep_threes k) = 1000000 * (3 * rep_threes k) := by
    ring
  rw [h_assoc, three_mul_rep_threes k]
  have h_pow6 : 10 ^ (k + 6) = 1000000 * 10 ^ k := by ring
  rw [h_pow6]
  have h_pos : 1000000 * 10 ^ k ≥ 1000000 := by
    have : 10 ^ k ≥ 1 := Nat.one_le_pow k 10 (by decide)
    omega
  omega

lemma concatenate_step6 (k : ℕ) :
  concatenate (k + 6) 2593 = 1000000 * concatenate k 2593 + 740332593 := by
  unfold concatenate
  have h_digits : num_digits 2593 = 4 := by
    unfold num_digits
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10 / 10)]
    rw [Nat.digits_zero]
    rfl
  rw [h_digits]
  rw [rep_threes_step6 k]
  ring

lemma div_seven_of_four_mod_six (m : ℕ) : 7 ∣ concatenate (6 * m + 4) 2593 := by
  induction m with
  | zero =>
    have h_val : concatenate 4 2593 = 33332593 := by
      unfold concatenate
      have h_digits : num_digits 2593 = 4 := by
        unfold num_digits
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10 / 10)]
        rw [Nat.digits_zero]
        rfl
      rw [h_digits]
      unfold rep_threes
      decide
    rw [h_val]
    decide
  | succ m ih =>
    have h_step : 6 * (m + 1) + 4 = (6 * m + 4) + 6 := by omega
    rw [h_step, concatenate_step6]
    apply dvd_add
    · apply dvd_mul_of_dvd_right ih
    · decide

lemma div_thirty_seven_of_two_mod_six (m : ℕ) : 37 ∣ concatenate (6 * m + 2) 2593 := by
  induction m with
  | zero =>
    have h_val : concatenate 2 2593 = 332593 := by
      unfold concatenate
      have h_digits : num_digits 2593 = 4 := by
        unfold num_digits
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10 / 10)]
        rw [Nat.digits_zero]
        rfl
      rw [h_digits]
      unfold rep_threes
      decide
    rw [h_val]
    decide
  | succ m ih =>
    have h_step : 6 * (m + 1) + 2 = (6 * m + 2) + 6 := by omega
    rw [h_step, concatenate_step6]
    apply dvd_add
    · apply dvd_mul_of_dvd_right ih
    · decide

lemma rep_threes_step12 (k : ℕ) : rep_threes (k + 12) = 1000000000000 * rep_threes k + 333333333333 := by
  apply Nat.eq_of_mul_eq_mul_left (by decide : 3 > 0)
  rw [Nat.mul_add]
  rw [three_mul_rep_threes (k + 12)]
  have h_assoc : 3 * (1000000000000 * rep_threes k) = 1000000000000 * (3 * rep_threes k) := by
    ring
  rw [h_assoc, three_mul_rep_threes k]
  have h_pow12 : 10 ^ (k + 12) = 1000000000000 * 10 ^ k := by ring
  rw [h_pow12]
  have h_pos : 1000000000000 * 10 ^ k ≥ 1000000000000 := by
    have : 10 ^ k ≥ 1 := Nat.one_le_pow k 10 (by decide)
    omega
  omega

lemma concatenate_step12 (k : ℕ) :
  concatenate (k + 12) 2593 = 1000000000000 * concatenate k 2593 + 740333333332593 := by
  unfold concatenate
  have h_digits : num_digits 2593 = 4 := by
    unfold num_digits
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10 / 10)]
    rw [Nat.digits_zero]
    rfl
  rw [h_digits]
  rw [rep_threes_step12 k]
  ring

lemma div_one_hundred_and_one_of_six_mod_twelve (m : ℕ) : 101 ∣ concatenate (12 * m + 6) 2593 := by
  induction m with
  | zero =>
    have h_val : concatenate 6 2593 = 3333332593 := by
      unfold concatenate
      have h_digits : num_digits 2593 = 4 := by
        unfold num_digits
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10)]
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10 / 10)]
        rw [Nat.digits_zero]
        rfl
      rw [h_digits]
      unfold rep_threes
      decide
    rw [h_val]
    decide
  | succ m ih =>
    have h_step : 12 * (m + 1) + 6 = (12 * m + 6) + 12 := by omega
    rw [h_step, concatenate_step12]
    apply dvd_add
    · apply dvd_mul_of_dvd_right ih
    · decide


def powMod_fuel (fuel : ℕ) (base exp modulus : ℕ) : ℕ :=
  match fuel with
  | 0 => 1 % modulus
  | fuel' + 1 =>
    if exp = 0 then
      1 % modulus
    else
      let half := powMod_fuel fuel' base (exp / 2) modulus
      let half_sq := (half * half) % modulus
      if exp % 2 = 1 then
        (half_sq * base) % modulus
      else
        half_sq

lemma test_mod_left (a b n : ℕ) : (a % n * b) % n = (a * b) % n := by
  rw [Nat.mul_mod (a % n) b n]
  rw [Nat.mod_mod]
  rw [← Nat.mul_mod a b n]

lemma powMod_fuel_eq (fuel : ℕ) (base exp modulus : ℕ) (h_fuel : exp < 2 ^ fuel) :
    powMod_fuel fuel base exp modulus = (base ^ exp) % modulus := by
  induction fuel generalizing exp with
  | zero =>
    have h_exp : exp = 0 := by omega
    subst h_exp
    rfl
  | succ fuel ih =>
    rw [powMod_fuel]
    by_cases h_exp : exp = 0
    · rw [if_pos h_exp]
      subst h_exp
      rfl
    · rw [if_neg h_exp]
      dsimp only
      have h_fuel_div : exp / 2 < 2 ^ fuel := by
        have h_pow : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := by rw [Nat.pow_succ]
        omega
      have h_ih := ih (exp / 2) h_fuel_div
      rw [h_ih]
      rw [← Nat.mul_mod]
      rw [← Nat.pow_add]
      have h_double : exp / 2 + exp / 2 = 2 * (exp / 2) := by omega
      rw [h_double]
      by_cases h_odd : exp % 2 = 1
      · rw [if_pos h_odd]
        rw [test_mod_left (base ^ (2 * (exp / 2))) base modulus]
        have h_pow : base ^ (2 * (exp / 2)) * base = base ^ (2 * (exp / 2) + 1) := by
          rw [Nat.pow_succ]
        rw [h_pow]
        have h_exp_eq : 2 * (exp / 2) + 1 = exp := by
          have h_div := Nat.div_add_mod exp 2
          omega
        rw [h_exp_eq]
      · rw [if_neg h_odd]
        have h_exp_eq : 2 * (exp / 2) = exp := by
          rw [Nat.mul_comm]
          have h_div := Nat.div_add_mod exp 2
          omega
        rw [h_exp_eq]

lemma not_prime_of_fermat_witness (n base : ℕ) (h_n : n > 1) (h_coprime : Nat.Coprime base n) (h_witness : powMod_fuel n base (n - 1) n ≠ 1) : ¬ Nat.Prime n := by
  intro hp
  have h_fermat := Nat.ModEq.pow_card_sub_one_eq_one hp h_coprime
  unfold Nat.ModEq at h_fermat
  have h_one : 1 % n = 1 := Nat.mod_eq_of_lt h_n
  rw [h_one] at h_fermat
  have h_eq : powMod_fuel n base (n - 1) n = (base ^ (n - 1)) % n := by
    apply powMod_fuel_eq
    have h_lt : n - 1 < n := by omega
    have h_n_lt_pow : n < 2 ^ n := Nat.lt_pow_self (by decide)
    omega
  rw [h_eq] at h_witness
  exact h_witness h_fermat

lemma not_prime_of_fermat_witness_fuel (n base fuel : ℕ) (h_n : n > 1) (h_coprime : Nat.Coprime base n) (h_exp : n - 1 < 2 ^ fuel) (h_witness : powMod_fuel fuel base (n - 1) n ≠ 1) : ¬ Nat.Prime n := by
  intro hp
  have h_fermat := Nat.ModEq.pow_card_sub_one_eq_one hp h_coprime
  unfold Nat.ModEq at h_fermat
  have h_one : 1 % n = 1 := Nat.mod_eq_of_lt h_n
  rw [h_one] at h_fermat
  have h_eq : powMod_fuel fuel base (n - 1) n = (base ^ (n - 1)) % n := by
    apply powMod_fuel_eq
    exact h_exp
  rw [h_eq] at h_witness
  exact h_witness h_fermat


lemma three_mul_concatenate (k : ℕ) : 3 * concatenate k 2593 + 2221 = 10000 * 10 ^ k := by
  unfold concatenate
  rw [Nat.mul_add]
  have h_digits : num_digits 2593 = 4 := by
    unfold num_digits
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10 / 10)]
    rw [Nat.digits_zero]
    rfl
  rw [h_digits]
  have h1 : 3 * (rep_threes k * 10 ^ 4) = (10 ^ 4) * (3 * rep_threes k) := by ring
  rw [h1, three_mul_rep_threes]
  have h2 : 10000 * (10 ^ k - 1) + 3 * 2593 + 2221 = 10000 * 10 ^ k := by
    have h_pow : 10 ^ k ≥ 1 := Nat.one_le_pow k 10 (by decide)
    omega
  rw [Nat.add_assoc]
  exact h2

lemma pow_ten_mod_nine (res : ℕ) : (10000 * 10 ^ res) % 9 = 1 := by
  induction res with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ]
    have : 10000 * (10 ^ r * 10) = (10000 * 10 ^ r) * 10 := by ring
    rw [this, Nat.mul_mod, ih]

lemma coprime_three_of_dvd_concatenate (q res : ℕ) (h_div : q ∣ concatenate res 2593) : Nat.Coprime 3 q := by
  have h_3_mul : 3 * concatenate res 2593 + 2221 = 10000 * 10 ^ res := three_mul_concatenate res
  have h_not_dvd : ¬ 3 ∣ q := by
    intro h_dvd_q
    have h_dvd_concat : 3 ∣ concatenate res 2593 := Nat.dvd_trans h_dvd_q h_div
    rcases h_dvd_concat with ⟨A, h_eq_concat⟩
    have h_eq : 3 * (3 * A) + 2221 = 10000 * 10 ^ res := by
      rw [← h_eq_concat]
      exact h_3_mul
    have h_9_mul : 9 * A + 2221 = 10000 * 10 ^ res := by
      have h_ring : 3 * (3 * A) = 9 * A := by ring
      rw [← h_ring]
      exact h_eq
    have h_mod : (9 * A + 2221) % 9 = (10000 * 10 ^ res) % 9 := by rw [h_9_mul]
    have h_mod_left : (9 * A + 2221) % 9 = 7 := by
      have h_add_mod : (9 * A + 2221) % 9 = ((9 * A) % 9 + 2221 % 9) % 9 := Nat.add_mod (9 * A) 2221 9
      have h_mul_mod : (9 * A) % 9 = 0 := Nat.mul_mod_right 9 A
      rw [h_add_mod, h_mul_mod]
    have h_mod_right : (10000 * 10 ^ res) % 9 = 1 := pow_ten_mod_nine res
    rw [h_mod_left] at h_mod
    rw [h_mod_right] at h_mod
    contradiction
  exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).2 h_not_dvd

lemma pow_mod_step (q mod res : ℕ) (h_mod : 10 ^ mod % q = 1 % q) (j : ℕ) :
    10 ^ (mod * j + res) % q = 10 ^ res % q := by
  rw [Nat.pow_add, Nat.pow_mul]
  have h_pow_j : (10 ^ mod) ^ j % q = 1 % q := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Nat.pow_succ]
      rw [Nat.mul_mod]
      rw [ih, h_mod]
      rw [← Nat.mul_mod]
  rw [Nat.mul_mod]
  rw [h_pow_j]
  rw [← Nat.mul_mod]
  rw [Nat.one_mul]

lemma three_mul_concatenate_modeq (q mod res : ℕ) (h_mod : 10 ^ mod ≡ 1 [MOD q]) (j : ℕ) :
    3 * concatenate (mod * j + res) 2593 ≡ 3 * concatenate res 2593 [MOD q] := by
  have h_eq1 : 3 * concatenate (mod * j + res) 2593 + 2221 = 10000 * 10 ^ (mod * j + res) := three_mul_concatenate (mod * j + res)
  have h_eq2 : 3 * concatenate res 2593 + 2221 = 10000 * 10 ^ res := three_mul_concatenate res
  have h_pow : 10 ^ (mod * j + res) % q = 10 ^ res % q := pow_mod_step q mod res h_mod j
  have h_mul : (10000 * 10 ^ (mod * j + res)) % q = (10000 * 10 ^ res) % q := by
    rw [Nat.mul_mod, h_pow, ← Nat.mul_mod]
  have h_add : 3 * concatenate (mod * j + res) 2593 + 2221 ≡ 3 * concatenate res 2593 + 2221 [MOD q] := by
    unfold Nat.ModEq
    rw [h_eq1, h_eq2, h_mul]
  exact Nat.ModEq.add_right_cancel' 2221 h_add

lemma div_of_step_simple (q mod res : ℕ) (h_div : q ∣ concatenate res 2593) (h_mod : 10 ^ mod ≡ 1 [MOD q]) (j : ℕ) :
    q ∣ concatenate (mod * j + res) 2593 := by
  have h_coprime : Nat.Coprime 3 q := coprime_three_of_dvd_concatenate q res h_div
  have h_dvd_mul_res : q ∣ 3 * concatenate res 2593 := dvd_mul_of_dvd_right h_div 3
  have h_modeq : 3 * concatenate (mod * j + res) 2593 ≡ 3 * concatenate res 2593 [MOD q] := three_mul_concatenate_modeq q mod res h_mod j
  have h_dvd_mul : q ∣ 3 * concatenate (mod * j + res) 2593 := by
    unfold Nat.ModEq at h_modeq
    have h_mod_zero : (3 * concatenate res 2593) % q = 0 := Nat.mod_eq_zero_of_dvd h_dvd_mul_res
    rw [h_mod_zero] at h_modeq
    exact Nat.dvd_of_mod_eq_zero h_modeq
  exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm h_coprime) h_dvd_mul


lemma not_prime_of_dvd {p n : ℕ} (hp : Nat.Prime p) (h_dvd : p ∣ n) (h_gt : p < n) : ¬ Nat.Prime n := by
  intro hn
  have h_eq : p = n := by
    apply hn.eq_one_or_self_of_dvd at h_dvd
    rcases h_dvd with h1 | h2
    · rw [h1] at hp
      exact (Nat.not_prime_one hp).elim
    · exact h2
  omega

lemma not_prime_of_exists_divisor {n : ℕ} (h_exists : ∃ d, 1 < d ∧ d < n ∧ d ∣ n) : ¬ Nat.Prime n := by
  intro hn_prime
  rcases h_exists with ⟨d, hd1, hd2, hd_dvd⟩
  have h_eq : d = 1 ∨ d = n := hn_prime.eq_one_or_self_of_dvd d hd_dvd
  omega



lemma rep_threes_add (a b : ℕ) : rep_threes (a + b) = rep_threes a * 10 ^ b + rep_threes b := by
  apply Nat.eq_of_mul_eq_mul_left (by decide : 3 > 0)
  rw [Nat.mul_add, ← Nat.mul_assoc, three_mul_rep_threes, three_mul_rep_threes, three_mul_rep_threes]
  have h_pow : 10 ^ (a + b) = 10 ^ a * 10 ^ b := Nat.pow_add 10 a b
  rw [h_pow]
  have h_mul : (10 ^ a - 1) * 10 ^ b = 10 ^ a * 10 ^ b - 10 ^ b := by
    rw [Nat.sub_mul, Nat.one_mul]
  rw [h_mul]
  have h_sub : 10 ^ a * 10 ^ b - 10 ^ b + (10 ^ b - 1) = 10 ^ a * 10 ^ b - 1 := by
    have h_le1 : 10 ^ b ≥ 1 := Nat.one_le_pow b 10 (by decide)
    have h_le2 : 10 ^ a * 10 ^ b ≥ 10 ^ b := by
      have : 10 ^ a ≥ 1 := Nat.one_le_pow a 10 (by decide)
      have : 10 ^ a * 10 ^ b ≥ 1 * 10 ^ b := Nat.mul_le_mul_right (10 ^ b) this
      omega
    omega
  rw [h_sub]

lemma rep_threes_ge (a b : ℕ) : rep_threes (a + b) ≥ rep_threes a := by
  rw [rep_threes_add]
  have h_pow : 10 ^ b ≥ 1 := Nat.one_le_pow b 10 (by decide)
  have h_mul : rep_threes a * 10 ^ b ≥ rep_threes a * 1 := Nat.mul_le_mul_left (rep_threes a) h_pow
  omega

lemma concatenate_ge_r (m : ℕ) (r : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = r) :
    concatenate (12 * m) 2593 ≥ rep_threes (12 * (if r > 0 then r else 216)) * 10000 + 2593 := by
  have h_eq_r : m = 216 * (m / 216) + r := by
    have h_div := Nat.div_add_mod m 216
    omega
  have h_r_gt : (if r > 0 then r else 216) ≤ m := by
    split_ifs with hr
    · omega
    · have hr0 : r = 0 := by omega
      subst hr0
      have hm_div : m / 216 ≥ 1 := by
        by_contra h_lt
        have : m / 216 = 0 := by omega
        have : m = 0 := by omega
        omega
      omega
  have h_k_ge : 12 * m = 12 * (if r > 0 then r else 216) + 12 * (m - (if r > 0 then r else 216)) := by omega
  unfold concatenate
  rw [h_k_ge]
  have h_rep_ge := rep_threes_ge (12 * (if r > 0 then r else 216)) (12 * (m - (if r > 0 then r else 216)))
  have h_digits : num_digits 2593 = 4 := by
    unfold num_digits
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10)]
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10 / 10)]
    rw [Nat.digits_zero]
    rfl
  rw [h_digits]
  omega


lemma h_digits : num_digits 2593 = 4 := by
  unfold num_digits
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593)]
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10)]
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10)]
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (by decide : 0 < 2593 / 10 / 10 / 10)]
  rw [Nat.digits_zero]
  rfl


-- Pre-verified Fermat witness lemmas
lemma not_prime_r18 : ¬ Nat.Prime (concatenate (12 * 18) 2593) := by
  have h_eq : concatenate (12 * 18) 2593 = rep_threes (12 * 18) * 10000 + 2593 := by
    unfold concatenate; rw [h_digits]; rfl
  rw [h_eq]
  apply not_prime_of_fermat_witness_fuel (rep_threes (12 * 18) * 10000 + 2593) 2 8000
  · unfold rep_threes; decide
  · decide
  · decide
  · decide

lemma not_prime_r53 : ¬ Nat.Prime (concatenate (12 * 53) 2593) := by
  have h_eq : concatenate (12 * 53) 2593 = rep_threes (12 * 53) * 10000 + 2593 := by
    unfold concatenate; rw [h_digits]; rfl
  rw [h_eq]
  apply not_prime_of_fermat_witness_fuel (rep_threes (12 * 53) * 10000 + 2593) 2 8000
  · unfold rep_threes; decide
  · decide
  · decide
  · decide

lemma not_prime_r76 : ¬ Nat.Prime (concatenate (12 * 76) 2593) := by
  have h_eq : concatenate (12 * 76) 2593 = rep_threes (12 * 76) * 10000 + 2593 := by
    unfold concatenate; rw [h_digits]; rfl
  rw [h_eq]
  apply not_prime_of_fermat_witness_fuel (rep_threes (12 * 76) * 10000 + 2593) 2 8000
  · unfold rep_threes; decide
  · decide
  · decide
  · decide

lemma not_prime_r136 : ¬ Nat.Prime (concatenate (12 * 136) 2593) := by
  have h_eq : concatenate (12 * 136) 2593 = rep_threes (12 * 136) * 10000 + 2593 := by
    unfold concatenate; rw [h_digits]; rfl
  rw [h_eq]
  apply not_prime_of_fermat_witness_fuel (rep_threes (12 * 136) * 10000 + 2593) 2 8000
  · unfold rep_threes; decide
  · decide
  · decide
  · decide

lemma not_prime_r161 : ¬ Nat.Prime (concatenate (12 * 161) 2593) := by
  have h_eq : concatenate (12 * 161) 2593 = rep_threes (12 * 161) * 10000 + 2593 := by
    unfold concatenate; rw [h_digits]; rfl
  rw [h_eq]
  apply not_prime_of_fermat_witness_fuel (rep_threes (12 * 161) * 10000 + 2593) 2 8000
  · unfold rep_threes; decide
  · decide
  · decide
  · decide

lemma not_prime_r198 : ¬ Nat.Prime (concatenate (12 * 198) 2593) := by
  have h_eq : concatenate (12 * 198) 2593 = rep_threes (12 * 198) * 10000 + 2593 := by
    unfold concatenate; rw [h_digits]; rfl
  rw [h_eq]
  apply not_prime_of_fermat_witness_fuel (rep_threes (12 * 198) * 10000 + 2593) 2 8000
  · unfold rep_threes; decide
  · decide
  · decide
  · decide


lemma div_of_twelve_m_chunk_0 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 0 ∨ m % 216 = 1 ∨ m % 216 = 2 ∨ m % 216 = 3 ∨ m % 216 = 4 ∨ m % 216 = 5 ∨ m % 216 = 6 ∨ m % 216 = 7 ∨ m % 216 = 8 ∨ m % 216 = 9 ∨ m % 216 = 10 ∨ m % 216 = 11 ∨ m % 216 = 12 ∨ m % 216 = 13 ∨ m % 216 = 14 ∨ m % 216 = 15 ∨ m % 216 = 16 ∨ m % 216 = 17) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 0
    have h_mod_mod : m % 216 = 0 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 0 := by omega
    have h_div : 2593 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 2593 2592 0 (by decide)
      · have h1 : powMod_fuel 20 10 2592 2593 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 2593 = (10 ^ 2592) % 2593 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 216 hm
    have h_q_lt : 2593 < concatenate (12 * m) 2593 := by
      have h_base_gt : 2593 < rep_threes 2592 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 1
    have h_mod_mod : m % 41 = 1 := by omega
    have h_eq : 12 * m = 492 * (m / 41) + 12 := by omega
    have h_div : 739 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 739 492 12 (by decide)
      · have h1 : powMod_fuel 20 10 492 739 = 1 := by decide
        have h2 : powMod_fuel 20 10 492 739 = (10 ^ 492) % 739 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 1 hm
    have h_q_lt : 739 < concatenate (12 * m) 2593 := by
      have h_base_gt : 739 < rep_threes 12 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 2
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 2 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 24 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 3
    have h_mod_mod : m % 235 = 3 := by omega
    have h_eq : 12 * m = 2820 * (m / 235) + 36 := by omega
    have h_div : 941 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 941 2820 36 (by decide)
      · have h1 : powMod_fuel 20 10 2820 941 = 1 := by decide
        have h2 : powMod_fuel 20 10 2820 941 = (10 ^ 2820) % 941 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 3 hm
    have h_q_lt : 941 < concatenate (12 * m) 2593 := by
      have h_base_gt : 941 < rep_threes 36 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 4
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 4 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 48 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 5
    have h_mod_mod : m % 41 = 5 := by omega
    have h_eq : 12 * m = 492 * (m / 41) + 60 := by omega
    have h_div : 83 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 83 492 60 (by decide)
      · have h1 : powMod_fuel 20 10 492 83 = 1 := by decide
        have h2 : powMod_fuel 20 10 492 83 = (10 ^ 492) % 83 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 5 hm
    have h_q_lt : 83 < concatenate (12 * m) 2593 := by
      have h_base_gt : 83 < rep_threes 60 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 6
    have h_mod_mod : m % 77051 = 6 := by omega
    have h_eq : 12 * m = 924612 * (m / 77051) + 72 := by omega
    have h_div : 10170733 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 10170733 924612 72 (by decide)
      · have h1 : powMod_fuel 20 10 924612 10170733 = 1 := by decide
        have h2 : powMod_fuel 20 10 924612 10170733 = (10 ^ 924612) % 10170733 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 6 hm
    have h_q_lt : 10170733 < concatenate (12 * m) 2593 := by
      have h_base_gt : 10170733 < rep_threes 72 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 7
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 7 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 84 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 8
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 8 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 96 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 9
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 9 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 108 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 10
    have h_mod_mod : m % 23 = 10 := by omega
    have h_eq : 12 * m = 276 * (m / 23) + 120 := by omega
    have h_div : 47 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 47 276 120 (by decide)
      · have h1 : powMod_fuel 20 10 276 47 = 1 := by decide
        have h2 : powMod_fuel 20 10 276 47 = (10 ^ 276) % 47 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 10 hm
    have h_q_lt : 47 < concatenate (12 * m) 2593 := by
      have h_base_gt : 47 < rep_threes 120 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 11
    have h_mod_mod : m % 216 = 11 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 132 := by omega
    have h_div : 427988326919 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 427988326919 2592 132 (by decide)
      · have h1 : powMod_fuel 20 10 2592 427988326919 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 427988326919 = (10 ^ 2592) % 427988326919 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 11 hm
    have h_q_lt : 427988326919 < concatenate (12 * m) 2593 := by
      have h_base_gt : 427988326919 < rep_threes 132 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 12
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 12 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 144 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 13
    have h_mod_mod : m % 713 = 13 := by omega
    have h_eq : 12 * m = 8556 * (m / 713) + 156 := by omega
    have h_div : 1427 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1427 8556 156 (by decide)
      · have h1 : powMod_fuel 20 10 8556 1427 = 1 := by decide
        have h2 : powMod_fuel 20 10 8556 1427 = (10 ^ 8556) % 1427 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 13 hm
    have h_q_lt : 1427 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1427 < rep_threes 156 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 14
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 14 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 168 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 15
    have h_mod_mod : m % 216 = 15 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 180 := by omega
    have h_div : 4781738003228663940809 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 4781738003228663940809 2592 180 (by decide)
      · have h1 : powMod_fuel 20 10 2592 4781738003228663940809 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 4781738003228663940809 = (10 ^ 2592) % 4781738003228663940809 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 15 hm
    have h_q_lt : 4781738003228663940809 < concatenate (12 * m) 2593 := by
      have h_base_gt : 4781738003228663940809 < rep_threes 180 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 16
    have h_mod_mod : m % 216 = 16 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 192 := by omega
    have h_div : 238244869 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 238244869 2592 192 (by decide)
      · have h1 : powMod_fuel 20 10 2592 238244869 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 238244869 = (10 ^ 2592) % 238244869 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 16 hm
    have h_q_lt : 238244869 < concatenate (12 * m) 2593 := by
      have h_base_gt : 238244869 < rep_threes 192 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 17
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 17 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 204 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_1 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 18 ∨ m % 216 = 19 ∨ m % 216 = 20 ∨ m % 216 = 21 ∨ m % 216 = 22 ∨ m % 216 = 23 ∨ m % 216 = 24 ∨ m % 216 = 25 ∨ m % 216 = 26 ∨ m % 216 = 27 ∨ m % 216 = 28 ∨ m % 216 = 29 ∨ m % 216 = 30 ∨ m % 216 = 31 ∨ m % 216 = 32 ∨ m % 216 = 33 ∨ m % 216 = 34 ∨ m % 216 = 35) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 18
    by_cases h_eq_m : m = 18
    · subst h_eq_m
      exact not_prime_r18
    · have h_mod_mod : m % 216 = 18 := by omega
      have h_eq : 12 * m = 2592 * (m / 216) + 216 := by omega
      have h_div : 2593 ∣ concatenate (12 * m) 2593 := by
        rw [h_eq]
        apply div_of_step_simple 2593 2592 216 (by decide) (by decide)
      have h_concat_gt := concatenate_ge_r m 216 hm
      have h_q_lt : 2593 < concatenate (12 * m) 2593 := by
        have h_base_gt : 2593 < rep_threes 2592 * 10000 + 2593 := by decide
        omega
      exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 19
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 19 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 228 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 20
    have h_mod_mod : m % 63 = 20 := by omega
    have h_eq : 12 * m = 756 * (m / 63) + 240 := by omega
    have h_div : 379 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 379 756 240 (by decide)
      · have h1 : powMod_fuel 20 10 756 379 = 1 := by decide
        have h2 : powMod_fuel 20 10 756 379 = (10 ^ 756) % 379 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 20 hm
    have h_q_lt : 379 < concatenate (12 * m) 2593 := by
      have h_base_gt : 379 < rep_threes 240 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 21
    have h_mod_mod : m % 38 = 21 := by omega
    have h_eq : 12 * m = 456 * (m / 38) + 252 := by omega
    have h_div : 457 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 457 456 252 (by decide)
      · have h1 : powMod_fuel 20 10 456 457 = 1 := by decide
        have h2 : powMod_fuel 20 10 456 457 = (10 ^ 456) % 457 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 21 hm
    have h_q_lt : 457 < concatenate (12 * m) 2593 := by
      have h_base_gt : 457 < rep_threes 252 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 22
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 22 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 264 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 23
    have h_mod_mod : m % 1409 = 23 := by omega
    have h_eq : 12 * m = 16908 * (m / 1409) + 276 := by omega
    have h_div : 2819 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 2819 16908 276 (by decide)
      · have h1 : powMod_fuel 20 10 16908 2819 = 1 := by decide
        have h2 : powMod_fuel 20 10 16908 2819 = (10 ^ 16908) % 2819 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 23 hm
    have h_q_lt : 2819 < concatenate (12 * m) 2593 := by
      have h_base_gt : 2819 < rep_threes 276 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 24
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 24 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 288 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 25
    have h_mod_mod : m % 131 = 25 := by omega
    have h_eq : 12 * m = 1572 * (m / 131) + 300 := by omega
    have h_div : 263 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 263 1572 300 (by decide)
      · have h1 : powMod_fuel 20 10 1572 263 = 1 := by decide
        have h2 : powMod_fuel 20 10 1572 263 = (10 ^ 1572) % 263 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 25 hm
    have h_q_lt : 263 < concatenate (12 * m) 2593 := by
      have h_base_gt : 263 < rep_threes 300 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 26
    have h_mod_mod : m % 298 = 26 := by omega
    have h_eq : 12 * m = 3576 * (m / 298) + 312 := by omega
    have h_div : 1193 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1193 3576 312 (by decide)
      · have h1 : powMod_fuel 20 10 3576 1193 = 1 := by decide
        have h2 : powMod_fuel 20 10 3576 1193 = (10 ^ 3576) % 1193 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 26 hm
    have h_q_lt : 1193 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1193 < rep_threes 312 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 27
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 27 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 324 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 28
    have h_mod_mod : m % 216 = 28 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 336 := by omega
    have h_div : 9343981 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 9343981 2592 336 (by decide)
      · have h1 : powMod_fuel 20 10 2592 9343981 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 9343981 = (10 ^ 2592) % 9343981 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 28 hm
    have h_q_lt : 9343981 < concatenate (12 * m) 2593 := by
      have h_base_gt : 9343981 < rep_threes 336 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 29
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 29 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 348 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 30
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 30 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 360 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 31
    have h_mod_mod : m % 216 = 31 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 372 := by omega
    have h_div : 519283 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 519283 2592 372 (by decide)
      · have h1 : powMod_fuel 20 10 2592 519283 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 519283 = (10 ^ 2592) % 519283 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 31 hm
    have h_q_lt : 519283 < concatenate (12 * m) 2593 := by
      have h_base_gt : 519283 < rep_threes 372 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 32
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 32 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 384 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 33
    have h_mod_mod : m % 23 = 10 := by omega
    have h_eq : 12 * m = 276 * (m / 23) + 120 := by omega
    have h_div : 47 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 47 276 120 (by decide)
      · have h1 : powMod_fuel 20 10 276 47 = 1 := by decide
        have h2 : powMod_fuel 20 10 276 47 = (10 ^ 276) % 47 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 33 hm
    have h_q_lt : 47 < concatenate (12 * m) 2593 := by
      have h_base_gt : 47 < rep_threes 396 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 34
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 34 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 408 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 35
    have h_mod_mod : m % 356 = 35 := by omega
    have h_eq : 12 * m = 4272 * (m / 356) + 420 := by omega
    have h_div : 4273 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 4273 4272 420 (by decide)
      · have h1 : powMod_fuel 20 10 4272 4273 = 1 := by decide
        have h2 : powMod_fuel 20 10 4272 4273 = (10 ^ 4272) % 4273 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 35 hm
    have h_q_lt : 4273 < concatenate (12 * m) 2593 := by
      have h_base_gt : 4273 < rep_threes 420 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_2 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 36 ∨ m % 216 = 37 ∨ m % 216 = 38 ∨ m % 216 = 39 ∨ m % 216 = 40 ∨ m % 216 = 41 ∨ m % 216 = 42 ∨ m % 216 = 43 ∨ m % 216 = 44 ∨ m % 216 = 45 ∨ m % 216 = 46 ∨ m % 216 = 47 ∨ m % 216 = 48 ∨ m % 216 = 49 ∨ m % 216 = 50 ∨ m % 216 = 51 ∨ m % 216 = 52 ∨ m % 216 = 53) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 36
    have h_mod_mod : m % 189 = 36 := by omega
    have h_eq : 12 * m = 2268 * (m / 189) + 432 := by omega
    have h_div : 15877 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 15877 2268 432 (by decide)
      · have h1 : powMod_fuel 20 10 2268 15877 = 1 := by decide
        have h2 : powMod_fuel 20 10 2268 15877 = (10 ^ 2268) % 15877 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 36 hm
    have h_q_lt : 15877 < concatenate (12 * m) 2593 := by
      have h_base_gt : 15877 < rep_threes 432 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 37
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 37 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 444 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 38
    have h_mod_mod : m % 13 = 12 := by omega
    have h_eq : 12 * m = 156 * (m / 13) + 144 := by omega
    have h_div : 859 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 859 156 144 (by decide)
      · have h1 : powMod_fuel 20 10 156 859 = 1 := by decide
        have h2 : powMod_fuel 20 10 156 859 = (10 ^ 156) % 859 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 38 hm
    have h_q_lt : 859 < concatenate (12 * m) 2593 := by
      have h_base_gt : 859 < rep_threes 456 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 39
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 39 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 468 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 40
    have h_mod_mod : m % 2063 = 40 := by omega
    have h_eq : 12 * m = 24756 * (m / 2063) + 480 := by omega
    have h_div : 4127 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 4127 24756 480 (by decide)
      · have h1 : powMod_fuel 20 10 24756 4127 = 1 := by decide
        have h2 : powMod_fuel 20 10 24756 4127 = (10 ^ 24756) % 4127 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 40 hm
    have h_q_lt : 4127 < concatenate (12 * m) 2593 := by
      have h_base_gt : 4127 < rep_threes 480 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 41
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 41 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 492 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 42
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 42 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 504 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 43
    have h_mod_mod : m % 35 = 8 := by omega
    have h_eq : 12 * m = 420 * (m / 35) + 96 := by omega
    have h_div : 71 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 71 420 96 (by decide)
      · have h1 : powMod_fuel 20 10 420 71 = 1 := by decide
        have h2 : powMod_fuel 20 10 420 71 = (10 ^ 420) % 71 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 43 hm
    have h_q_lt : 71 < concatenate (12 * m) 2593 := by
      have h_base_gt : 71 < rep_threes 516 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 44
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 44 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 528 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 45
    have h_mod_mod : m % 265 = 45 := by omega
    have h_eq : 12 * m = 3180 * (m / 265) + 540 := by omega
    have h_div : 89041 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 89041 3180 540 (by decide)
      · have h1 : powMod_fuel 20 10 3180 89041 = 1 := by decide
        have h2 : powMod_fuel 20 10 3180 89041 = (10 ^ 3180) % 89041 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 45 hm
    have h_q_lt : 89041 < concatenate (12 * m) 2593 := by
      have h_base_gt : 89041 < rep_threes 540 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 46
    have h_mod_mod : m % 41 = 5 := by omega
    have h_eq : 12 * m = 492 * (m / 41) + 60 := by omega
    have h_div : 83 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 83 492 60 (by decide)
      · have h1 : powMod_fuel 20 10 492 83 = 1 := by decide
        have h2 : powMod_fuel 20 10 492 83 = (10 ^ 492) % 83 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 46 hm
    have h_q_lt : 83 < concatenate (12 * m) 2593 := by
      have h_base_gt : 83 < rep_threes 552 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 47
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 47 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 564 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 48
    have h_mod_mod : m % 53 = 48 := by omega
    have h_eq : 12 * m = 636 * (m / 53) + 576 := by omega
    have h_div : 107 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 107 636 576 (by decide)
      · have h1 : powMod_fuel 20 10 636 107 = 1 := by decide
        have h2 : powMod_fuel 20 10 636 107 = (10 ^ 636) % 107 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 48 hm
    have h_q_lt : 107 < concatenate (12 * m) 2593 := by
      have h_base_gt : 107 < rep_threes 576 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 49
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 49 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 588 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 50
    have h_mod_mod : m % 216 = 50 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 600 := by omega
    have h_div : 4013574263 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 4013574263 2592 600 (by decide)
      · have h1 : powMod_fuel 20 10 2592 4013574263 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 4013574263 = (10 ^ 2592) % 4013574263 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 50 hm
    have h_q_lt : 4013574263 < concatenate (12 * m) 2593 := by
      have h_base_gt : 4013574263 < rep_threes 600 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 51
    have h_mod_mod : m % 13 = 12 := by omega
    have h_eq : 12 * m = 156 * (m / 13) + 144 := by omega
    have h_div : 859 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 859 156 144 (by decide)
      · have h1 : powMod_fuel 20 10 156 859 = 1 := by decide
        have h2 : powMod_fuel 20 10 156 859 = (10 ^ 156) % 859 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 51 hm
    have h_q_lt : 859 < concatenate (12 * m) 2593 := by
      have h_base_gt : 859 < rep_threes 612 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 52
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 52 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 624 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 53
    by_cases h_eq_m : m = 53
    · subst h_eq_m
      exact not_prime_r53
    · have h_mod_mod : m % 216 = 53 := by omega
      have h_eq : 12 * m = 2592 * (m / 216) + 636 := by omega
      have h_div : 2593 ∣ concatenate (12 * m) 2593 := by
        rw [h_eq]
        apply div_of_step_simple 2593 2592 636 (by decide) (by decide)
      have h_concat_gt := concatenate_ge_r m 216 hm
      have h_q_lt : 2593 < concatenate (12 * m) 2593 := by
        have h_base_gt : 2593 < rep_threes 2592 * 10000 + 2593 := by decide
        omega
      exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_3 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 54 ∨ m % 216 = 55 ∨ m % 216 = 56 ∨ m % 216 = 57 ∨ m % 216 = 58 ∨ m % 216 = 59 ∨ m % 216 = 60 ∨ m % 216 = 61 ∨ m % 216 = 62 ∨ m % 216 = 63 ∨ m % 216 = 64 ∨ m % 216 = 65 ∨ m % 216 = 66 ∨ m % 216 = 67 ∨ m % 216 = 68 ∨ m % 216 = 69 ∨ m % 216 = 70 ∨ m % 216 = 71) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 54
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 54 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 648 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 55
    have h_mod_mod : m % 65 = 55 := by omega
    have h_eq : 12 * m = 780 * (m / 65) + 660 := by omega
    have h_div : 131 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 131 780 660 (by decide)
      · have h1 : powMod_fuel 20 10 780 131 = 1 := by decide
        have h2 : powMod_fuel 20 10 780 131 = (10 ^ 780) % 131 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 55 hm
    have h_q_lt : 131 < concatenate (12 * m) 2593 := by
      have h_base_gt : 131 < rep_threes 660 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 56
    have h_mod_mod : m % 23 = 10 := by omega
    have h_eq : 12 * m = 276 * (m / 23) + 120 := by omega
    have h_div : 47 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 47 276 120 (by decide)
      · have h1 : powMod_fuel 20 10 276 47 = 1 := by decide
        have h2 : powMod_fuel 20 10 276 47 = (10 ^ 276) % 47 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 56 hm
    have h_q_lt : 47 < concatenate (12 * m) 2593 := by
      have h_base_gt : 47 < rep_threes 672 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 57
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 57 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 684 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 58
    have h_mod_mod : m % 453 = 58 := by omega
    have h_eq : 12 * m = 5436 * (m / 453) + 696 := by omega
    have h_div : 5437 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 5437 5436 696 (by decide)
      · have h1 : powMod_fuel 20 10 5436 5437 = 1 := by decide
        have h2 : powMod_fuel 20 10 5436 5437 = (10 ^ 5436) % 5437 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 58 hm
    have h_q_lt : 5437 < concatenate (12 * m) 2593 := by
      have h_base_gt : 5437 < rep_threes 696 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 59
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 59 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 708 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 60
    have h_mod_mod : m % 1001 = 60 := by omega
    have h_eq : 12 * m = 12012 * (m / 1001) + 720 := by omega
    have h_div : 2003 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 2003 12012 720 (by decide)
      · have h1 : powMod_fuel 20 10 12012 2003 = 1 := by decide
        have h2 : powMod_fuel 20 10 12012 2003 = (10 ^ 12012) % 2003 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 60 hm
    have h_q_lt : 2003 < concatenate (12 * m) 2593 := by
      have h_base_gt : 2003 < rep_threes 720 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 61
    have h_mod_mod : m % 4693 = 61 := by omega
    have h_eq : 12 * m = 56316 * (m / 4693) + 732 := by omega
    have h_div : 18773 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 18773 56316 732 (by decide)
      · have h1 : powMod_fuel 20 10 56316 18773 = 1 := by decide
        have h2 : powMod_fuel 20 10 56316 18773 = (10 ^ 56316) % 18773 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 61 hm
    have h_q_lt : 18773 < concatenate (12 * m) 2593 := by
      have h_base_gt : 18773 < rep_threes 732 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 62
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 62 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 744 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 63
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 63 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 756 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 64
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 64 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 768 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 65
    have h_mod_mod : m % 55 = 10 := by omega
    have h_eq : 12 * m = 660 * (m / 55) + 120 := by omega
    have h_div : 1321 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1321 660 120 (by decide)
      · have h1 : powMod_fuel 20 10 660 1321 = 1 := by decide
        have h2 : powMod_fuel 20 10 660 1321 = (10 ^ 660) % 1321 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 65 hm
    have h_q_lt : 1321 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1321 < rep_threes 780 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 66
    have h_mod_mod : m % 216 = 66 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 792 := by omega
    have h_div : 18602533384691813 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 18602533384691813 2592 792 (by decide)
      · have h1 : powMod_fuel 20 10 2592 18602533384691813 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 18602533384691813 = (10 ^ 2592) % 18602533384691813 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 66 hm
    have h_q_lt : 18602533384691813 < concatenate (12 * m) 2593 := by
      have h_base_gt : 18602533384691813 < rep_threes 792 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 67
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 67 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 804 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 68
    have h_mod_mod : m % 216 = 68 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 816 := by omega
    have h_div : 751184697019 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 751184697019 2592 816 (by decide)
      · have h1 : powMod_fuel 20 10 2592 751184697019 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 751184697019 = (10 ^ 2592) % 751184697019 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 68 hm
    have h_q_lt : 751184697019 < concatenate (12 * m) 2593 := by
      have h_base_gt : 751184697019 < rep_threes 816 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 69
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 69 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 828 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 70
    have h_mod_mod : m % 96 = 70 := by omega
    have h_eq : 12 * m = 1152 * (m / 96) + 840 := by omega
    have h_div : 1153 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1153 1152 840 (by decide)
      · have h1 : powMod_fuel 20 10 1152 1153 = 1 := by decide
        have h2 : powMod_fuel 20 10 1152 1153 = (10 ^ 1152) % 1153 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 70 hm
    have h_q_lt : 1153 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1153 < rep_threes 840 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 71
    have h_mod_mod : m % 103 = 71 := by omega
    have h_eq : 12 * m = 1236 * (m / 103) + 852 := by omega
    have h_div : 1031 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1031 1236 852 (by decide)
      · have h1 : powMod_fuel 20 10 1236 1031 = 1 := by decide
        have h2 : powMod_fuel 20 10 1236 1031 = (10 ^ 1236) % 1031 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 71 hm
    have h_q_lt : 1031 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1031 < rep_threes 852 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_4 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 72 ∨ m % 216 = 73 ∨ m % 216 = 74 ∨ m % 216 = 75 ∨ m % 216 = 76 ∨ m % 216 = 77 ∨ m % 216 = 78 ∨ m % 216 = 79 ∨ m % 216 = 80 ∨ m % 216 = 81 ∨ m % 216 = 82 ∨ m % 216 = 83 ∨ m % 216 = 84 ∨ m % 216 = 85 ∨ m % 216 = 86 ∨ m % 216 = 87 ∨ m % 216 = 88 ∨ m % 216 = 89) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 72
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 72 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 864 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 73
    have h_mod_mod : m % 217 = 73 := by omega
    have h_eq : 12 * m = 2604 * (m / 217) + 876 := by omega
    have h_div : 1303 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1303 2604 876 (by decide)
      · have h1 : powMod_fuel 20 10 2604 1303 = 1 := by decide
        have h2 : powMod_fuel 20 10 2604 1303 = (10 ^ 2604) % 1303 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 73 hm
    have h_q_lt : 1303 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1303 < rep_threes 876 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 74
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 74 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 888 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 75
    have h_mod_mod : m % 216 = 75 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 900 := by omega
    have h_div : 26191349 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 26191349 2592 900 (by decide)
      · have h1 : powMod_fuel 20 10 2592 26191349 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 26191349 = (10 ^ 2592) % 26191349 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 75 hm
    have h_q_lt : 26191349 < concatenate (12 * m) 2593 := by
      have h_base_gt : 26191349 < rep_threes 900 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 76
    by_cases h_eq_m : m = 76
    · subst h_eq_m
      exact not_prime_r76
    · have h_mod_mod : m % 216 = 76 := by omega
      have h_eq : 12 * m = 2592 * (m / 216) + 912 := by omega
      have h_div : 2593 ∣ concatenate (12 * m) 2593 := by
        rw [h_eq]
        apply div_of_step_simple 2593 2592 912 (by decide) (by decide)
      have h_concat_gt := concatenate_ge_r m 216 hm
      have h_q_lt : 2593 < concatenate (12 * m) 2593 := by
        have h_base_gt : 2593 < rep_threes 2592 * 10000 + 2593 := by decide
        omega
      exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 77
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 77 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 924 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 78
    have h_mod_mod : m % 35 = 8 := by omega
    have h_eq : 12 * m = 420 * (m / 35) + 96 := by omega
    have h_div : 71 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 71 420 96 (by decide)
      · have h1 : powMod_fuel 20 10 420 71 = 1 := by decide
        have h2 : powMod_fuel 20 10 420 71 = (10 ^ 420) % 71 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 78 hm
    have h_q_lt : 71 < concatenate (12 * m) 2593 := by
      have h_base_gt : 71 < rep_threes 936 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 79
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 79 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 948 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 80
    have h_mod_mod : m % 216 = 80 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 960 := by omega
    have h_div : 40043135857 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 40043135857 2592 960 (by decide)
      · have h1 : powMod_fuel 20 10 2592 40043135857 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 40043135857 = (10 ^ 2592) % 40043135857 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 80 hm
    have h_q_lt : 40043135857 < concatenate (12 * m) 2593 := by
      have h_base_gt : 40043135857 < rep_threes 960 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 81
    have h_mod_mod : m % 216 = 81 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 972 := by omega
    have h_div : 2622124339 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 2622124339 2592 972 (by decide)
      · have h1 : powMod_fuel 20 10 2592 2622124339 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 2622124339 = (10 ^ 2592) % 2622124339 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 81 hm
    have h_q_lt : 2622124339 < concatenate (12 * m) 2593 := by
      have h_base_gt : 2622124339 < rep_threes 972 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 82
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 82 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 984 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 83
    have h_mod_mod : m % 63 = 20 := by omega
    have h_eq : 12 * m = 756 * (m / 63) + 240 := by omega
    have h_div : 379 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 379 756 240 (by decide)
      · have h1 : powMod_fuel 20 10 756 379 = 1 := by decide
        have h2 : powMod_fuel 20 10 756 379 = (10 ^ 756) % 379 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 83 hm
    have h_q_lt : 379 < concatenate (12 * m) 2593 := by
      have h_base_gt : 379 < rep_threes 996 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 84
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 84 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1008 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 85
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 85 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 1020 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 86
    have h_mod_mod : m % 216 = 86 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1032 := by omega
    have h_div : 7290289 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 7290289 2592 1032 (by decide)
      · have h1 : powMod_fuel 20 10 2592 7290289 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 7290289 = (10 ^ 2592) % 7290289 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 86 hm
    have h_q_lt : 7290289 < concatenate (12 * m) 2593 := by
      have h_base_gt : 7290289 < rep_threes 1032 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 87
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 87 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1044 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 88
    have h_mod_mod : m % 20417 = 88 := by omega
    have h_eq : 12 * m = 245004 * (m / 20417) + 1056 := by omega
    have h_div : 1388357 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1388357 245004 1056 (by decide)
      · have h1 : powMod_fuel 20 10 245004 1388357 = 1 := by decide
        have h2 : powMod_fuel 20 10 245004 1388357 = (10 ^ 245004) % 1388357 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 88 hm
    have h_q_lt : 1388357 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1388357 < rep_threes 1056 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 89
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 89 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1068 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_5 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 90 ∨ m % 216 = 91 ∨ m % 216 = 92 ∨ m % 216 = 93 ∨ m % 216 = 94 ∨ m % 216 = 95 ∨ m % 216 = 96 ∨ m % 216 = 97 ∨ m % 216 = 98 ∨ m % 216 = 99 ∨ m % 216 = 100 ∨ m % 216 = 101 ∨ m % 216 = 102 ∨ m % 216 = 103 ∨ m % 216 = 104 ∨ m % 216 = 105 ∨ m % 216 = 106 ∨ m % 216 = 107) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 90
    have h_mod_mod : m % 13 = 12 := by omega
    have h_eq : 12 * m = 156 * (m / 13) + 144 := by omega
    have h_div : 859 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 859 156 144 (by decide)
      · have h1 : powMod_fuel 20 10 156 859 = 1 := by decide
        have h2 : powMod_fuel 20 10 156 859 = (10 ^ 156) % 859 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 90 hm
    have h_q_lt : 859 < concatenate (12 * m) 2593 := by
      have h_base_gt : 859 < rep_threes 1080 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 91
    have h_mod_mod : m % 61 = 30 := by omega
    have h_eq : 12 * m = 732 * (m / 61) + 360 := by omega
    have h_div : 733 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 733 732 360 (by decide)
      · have h1 : powMod_fuel 20 10 732 733 = 1 := by decide
        have h2 : powMod_fuel 20 10 732 733 = (10 ^ 732) % 733 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 91 hm
    have h_q_lt : 733 < concatenate (12 * m) 2593 := by
      have h_base_gt : 733 < rep_threes 1092 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 92
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 92 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1104 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 93
    have h_mod_mod : m % 3950 = 93 := by omega
    have h_eq : 12 * m = 47400 * (m / 3950) + 1116 := by omega
    have h_div : 31601 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31601 47400 1116 (by decide)
      · have h1 : powMod_fuel 20 10 47400 31601 = 1 := by decide
        have h2 : powMod_fuel 20 10 47400 31601 = (10 ^ 47400) % 31601 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 93 hm
    have h_q_lt : 31601 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31601 < rep_threes 1116 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 94
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 94 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1128 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 95
    have h_mod_mod : m % 216 = 95 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1140 := by omega
    have h_div : 1549428417935147 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1549428417935147 2592 1140 (by decide)
      · have h1 : powMod_fuel 20 10 2592 1549428417935147 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 1549428417935147 = (10 ^ 2592) % 1549428417935147 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 95 hm
    have h_q_lt : 1549428417935147 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1549428417935147 < rep_threes 1140 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 96
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 96 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 1152 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 97
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 97 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1164 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 98
    have h_mod_mod : m % 216 = 98 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1176 := by omega
    have h_div : 8430278711131247 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 8430278711131247 2592 1176 (by decide)
      · have h1 : powMod_fuel 20 10 2592 8430278711131247 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 8430278711131247 = (10 ^ 2592) % 8430278711131247 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 98 hm
    have h_q_lt : 8430278711131247 < concatenate (12 * m) 2593 := by
      have h_base_gt : 8430278711131247 < rep_threes 1176 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 99
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 99 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1188 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 100
    have h_mod_mod : m % 3943 = 100 := by omega
    have h_eq : 12 * m = 47316 * (m / 3943) + 1200 := by omega
    have h_div : 15773 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 15773 47316 1200 (by decide)
      · have h1 : powMod_fuel 20 10 47316 15773 = 1 := by decide
        have h2 : powMod_fuel 20 10 47316 15773 = (10 ^ 47316) % 15773 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 100 hm
    have h_q_lt : 15773 < concatenate (12 * m) 2593 := by
      have h_base_gt : 15773 < rep_threes 1200 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 101
    have h_mod_mod : m % 53 = 48 := by omega
    have h_eq : 12 * m = 636 * (m / 53) + 576 := by omega
    have h_div : 107 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 107 636 576 (by decide)
      · have h1 : powMod_fuel 20 10 636 107 = 1 := by decide
        have h2 : powMod_fuel 20 10 636 107 = (10 ^ 636) % 107 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 101 hm
    have h_q_lt : 107 < concatenate (12 * m) 2593 := by
      have h_base_gt : 107 < rep_threes 1212 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 102
    have h_mod_mod : m % 23 = 10 := by omega
    have h_eq : 12 * m = 276 * (m / 23) + 120 := by omega
    have h_div : 47 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 47 276 120 (by decide)
      · have h1 : powMod_fuel 20 10 276 47 = 1 := by decide
        have h2 : powMod_fuel 20 10 276 47 = (10 ^ 276) % 47 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 102 hm
    have h_q_lt : 47 < concatenate (12 * m) 2593 := by
      have h_base_gt : 47 < rep_threes 1224 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 103
    have h_mod_mod : m % 13 = 12 := by omega
    have h_eq : 12 * m = 156 * (m / 13) + 144 := by omega
    have h_div : 859 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 859 156 144 (by decide)
      · have h1 : powMod_fuel 20 10 156 859 = 1 := by decide
        have h2 : powMod_fuel 20 10 156 859 = (10 ^ 156) % 859 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 103 hm
    have h_q_lt : 859 < concatenate (12 * m) 2593 := by
      have h_base_gt : 859 < rep_threes 1236 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 104
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 104 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1248 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 105
    have h_mod_mod : m % 2795 = 105 := by omega
    have h_eq : 12 * m = 33540 * (m / 2795) + 1260 := by omega
    have h_div : 5591 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 5591 33540 1260 (by decide)
      · have h1 : powMod_fuel 20 10 33540 5591 = 1 := by decide
        have h2 : powMod_fuel 20 10 33540 5591 = (10 ^ 33540) % 5591 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 105 hm
    have h_q_lt : 5591 < concatenate (12 * m) 2593 := by
      have h_base_gt : 5591 < rep_threes 1260 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 106
    have h_mod_mod : m % 127 = 106 := by omega
    have h_eq : 12 * m = 1524 * (m / 127) + 1272 := by omega
    have h_div : 509 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 509 1524 1272 (by decide)
      · have h1 : powMod_fuel 20 10 1524 509 = 1 := by decide
        have h2 : powMod_fuel 20 10 1524 509 = (10 ^ 1524) % 509 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 106 hm
    have h_q_lt : 509 < concatenate (12 * m) 2593 := by
      have h_base_gt : 509 < rep_threes 1272 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 107
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 107 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 1284 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_6 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 108 ∨ m % 216 = 109 ∨ m % 216 = 110 ∨ m % 216 = 111 ∨ m % 216 = 112 ∨ m % 216 = 113 ∨ m % 216 = 114 ∨ m % 216 = 115 ∨ m % 216 = 116 ∨ m % 216 = 117 ∨ m % 216 = 118 ∨ m % 216 = 119 ∨ m % 216 = 120 ∨ m % 216 = 121 ∨ m % 216 = 122 ∨ m % 216 = 123 ∨ m % 216 = 124 ∨ m % 216 = 125) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 108
    have h_mod_mod : m % 216 = 108 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1296 := by omega
    have h_div : 279468246479 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 279468246479 2592 1296 (by decide)
      · have h1 : powMod_fuel 20 10 2592 279468246479 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 279468246479 = (10 ^ 2592) % 279468246479 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 108 hm
    have h_q_lt : 279468246479 < concatenate (12 * m) 2593 := by
      have h_base_gt : 279468246479 < rep_threes 1296 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 109
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 109 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1308 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 110
    have h_mod_mod : m % 216 = 110 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1320 := by omega
    have h_div : 2459038900957 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 2459038900957 2592 1320 (by decide)
      · have h1 : powMod_fuel 20 10 2592 2459038900957 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 2459038900957 = (10 ^ 2592) % 2459038900957 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 110 hm
    have h_q_lt : 2459038900957 < concatenate (12 * m) 2593 := by
      have h_base_gt : 2459038900957 < rep_threes 1320 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 111
    have h_mod_mod : m % 216 = 111 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1332 := by omega
    have h_div : 24574085035463998506719297 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 24574085035463998506719297 2592 1332 (by decide)
      · have h1 : powMod_fuel 20 10 2592 24574085035463998506719297 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 24574085035463998506719297 = (10 ^ 2592) % 24574085035463998506719297 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 111 hm
    have h_q_lt : 24574085035463998506719297 < concatenate (12 * m) 2593 := by
      have h_base_gt : 24574085035463998506719297 < rep_threes 1332 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 112
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 112 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1344 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 113
    have h_mod_mod : m % 35 = 8 := by omega
    have h_eq : 12 * m = 420 * (m / 35) + 96 := by omega
    have h_div : 71 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 71 420 96 (by decide)
      · have h1 : powMod_fuel 20 10 420 71 = 1 := by decide
        have h2 : powMod_fuel 20 10 420 71 = (10 ^ 420) % 71 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 113 hm
    have h_q_lt : 71 < concatenate (12 * m) 2593 := by
      have h_base_gt : 71 < rep_threes 1356 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 114
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 114 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1368 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 115
    have h_mod_mod : m % 1161 = 115 := by omega
    have h_eq : 12 * m = 13932 * (m / 1161) + 1380 := by omega
    have h_div : 13933 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 13933 13932 1380 (by decide)
      · have h1 : powMod_fuel 20 10 13932 13933 = 1 := by decide
        have h2 : powMod_fuel 20 10 13932 13933 = (10 ^ 13932) % 13933 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 115 hm
    have h_q_lt : 13933 < concatenate (12 * m) 2593 := by
      have h_base_gt : 13933 < rep_threes 1380 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 116
    have h_mod_mod : m % 13 = 12 := by omega
    have h_eq : 12 * m = 156 * (m / 13) + 144 := by omega
    have h_div : 859 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 859 156 144 (by decide)
      · have h1 : powMod_fuel 20 10 156 859 = 1 := by decide
        have h2 : powMod_fuel 20 10 156 859 = (10 ^ 156) % 859 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 116 hm
    have h_q_lt : 859 < concatenate (12 * m) 2593 := by
      have h_base_gt : 859 < rep_threes 1392 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 117
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 117 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1404 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 118
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 118 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 1416 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 119
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 119 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1428 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 120
    have h_mod_mod : m % 65 = 55 := by omega
    have h_eq : 12 * m = 780 * (m / 65) + 660 := by omega
    have h_div : 131 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 131 780 660 (by decide)
      · have h1 : powMod_fuel 20 10 780 131 = 1 := by decide
        have h2 : powMod_fuel 20 10 780 131 = (10 ^ 780) % 131 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 120 hm
    have h_q_lt : 131 < concatenate (12 * m) 2593 := by
      have h_base_gt : 131 < rep_threes 1440 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 121
    have h_mod_mod : m % 233 = 121 := by omega
    have h_eq : 12 * m = 2796 * (m / 233) + 1452 := by omega
    have h_div : 2797 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 2797 2796 1452 (by decide)
      · have h1 : powMod_fuel 20 10 2796 2797 = 1 := by decide
        have h2 : powMod_fuel 20 10 2796 2797 = (10 ^ 2796) % 2797 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 121 hm
    have h_q_lt : 2797 < concatenate (12 * m) 2593 := by
      have h_base_gt : 2797 < rep_threes 1452 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 122
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 122 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1464 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 123
    have h_mod_mod : m % 216 = 123 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1476 := by omega
    have h_div : 167618939 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 167618939 2592 1476 (by decide)
      · have h1 : powMod_fuel 20 10 2592 167618939 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 167618939 = (10 ^ 2592) % 167618939 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 123 hm
    have h_q_lt : 167618939 < concatenate (12 * m) 2593 := by
      have h_base_gt : 167618939 < rep_threes 1476 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 124
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 124 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1488 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 125
    have h_mod_mod : m % 23 = 10 := by omega
    have h_eq : 12 * m = 276 * (m / 23) + 120 := by omega
    have h_div : 47 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 47 276 120 (by decide)
      · have h1 : powMod_fuel 20 10 276 47 = 1 := by decide
        have h2 : powMod_fuel 20 10 276 47 = (10 ^ 276) % 47 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 125 hm
    have h_q_lt : 47 < concatenate (12 * m) 2593 := by
      have h_base_gt : 47 < rep_threes 1500 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_7 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 126 ∨ m % 216 = 127 ∨ m % 216 = 128 ∨ m % 216 = 129 ∨ m % 216 = 130 ∨ m % 216 = 131 ∨ m % 216 = 132 ∨ m % 216 = 133 ∨ m % 216 = 134 ∨ m % 216 = 135 ∨ m % 216 = 136 ∨ m % 216 = 137 ∨ m % 216 = 138 ∨ m % 216 = 139 ∨ m % 216 = 140 ∨ m % 216 = 141 ∨ m % 216 = 142 ∨ m % 216 = 143) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 126
    have h_mod_mod : m % 4517 = 126 := by omega
    have h_eq : 12 * m = 54204 * (m / 4517) + 1512 := by omega
    have h_div : 81307 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 81307 54204 1512 (by decide)
      · have h1 : powMod_fuel 20 10 54204 81307 = 1 := by decide
        have h2 : powMod_fuel 20 10 54204 81307 = (10 ^ 54204) % 81307 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 126 hm
    have h_q_lt : 81307 < concatenate (12 * m) 2593 := by
      have h_base_gt : 81307 < rep_threes 1512 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 127
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 127 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1524 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 128
    have h_mod_mod : m % 41 = 5 := by omega
    have h_eq : 12 * m = 492 * (m / 41) + 60 := by omega
    have h_div : 83 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 83 492 60 (by decide)
      · have h1 : powMod_fuel 20 10 492 83 = 1 := by decide
        have h2 : powMod_fuel 20 10 492 83 = (10 ^ 492) % 83 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 128 hm
    have h_q_lt : 83 < concatenate (12 * m) 2593 := by
      have h_base_gt : 83 < rep_threes 1536 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 129
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 129 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 1548 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 130
    have h_mod_mod : m % 216 = 130 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1560 := by omega
    have h_div : 13730542393751 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 13730542393751 2592 1560 (by decide)
      · have h1 : powMod_fuel 20 10 2592 13730542393751 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 13730542393751 = (10 ^ 2592) % 13730542393751 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 130 hm
    have h_q_lt : 13730542393751 < concatenate (12 * m) 2593 := by
      have h_base_gt : 13730542393751 < rep_threes 1560 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 131
    have h_mod_mod : m % 83 = 48 := by omega
    have h_eq : 12 * m = 996 * (m / 83) + 576 := by omega
    have h_div : 167 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 167 996 576 (by decide)
      · have h1 : powMod_fuel 20 10 996 167 = 1 := by decide
        have h2 : powMod_fuel 20 10 996 167 = (10 ^ 996) % 167 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 131 hm
    have h_q_lt : 167 < concatenate (12 * m) 2593 := by
      have h_base_gt : 167 < rep_threes 1572 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 132
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 132 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1584 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 133
    have h_mod_mod : m % 216 = 133 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1596 := by omega
    have h_div : 759959 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 759959 2592 1596 (by decide)
      · have h1 : powMod_fuel 20 10 2592 759959 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 759959 = (10 ^ 2592) % 759959 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 133 hm
    have h_q_lt : 759959 < concatenate (12 * m) 2593 := by
      have h_base_gt : 759959 < rep_threes 1596 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 134
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 134 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1608 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 135
    have h_mod_mod : m % 38 = 21 := by omega
    have h_eq : 12 * m = 456 * (m / 38) + 252 := by omega
    have h_div : 457 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 457 456 252 (by decide)
      · have h1 : powMod_fuel 20 10 456 457 = 1 := by decide
        have h2 : powMod_fuel 20 10 456 457 = (10 ^ 456) % 457 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 135 hm
    have h_q_lt : 457 < concatenate (12 * m) 2593 := by
      have h_base_gt : 457 < rep_threes 1620 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 136
    by_cases h_eq_m : m = 136
    · subst h_eq_m
      exact not_prime_r136
    · have h_mod_mod : m % 216 = 136 := by omega
      have h_eq : 12 * m = 2592 * (m / 216) + 1632 := by omega
      have h_div : 2593 ∣ concatenate (12 * m) 2593 := by
        rw [h_eq]
        apply div_of_step_simple 2593 2592 1632 (by decide) (by decide)
      have h_concat_gt := concatenate_ge_r m 216 hm
      have h_q_lt : 2593 < concatenate (12 * m) 2593 := by
        have h_base_gt : 2593 < rep_threes 2592 * 10000 + 2593 := by decide
        omega
      exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 137
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 137 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1644 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 138
    have h_mod_mod : m % 91 = 47 := by omega
    have h_eq : 12 * m = 1092 * (m / 91) + 564 := by omega
    have h_div : 17837 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 17837 1092 564 (by decide)
      · have h1 : powMod_fuel 20 10 1092 17837 = 1 := by decide
        have h2 : powMod_fuel 20 10 1092 17837 = (10 ^ 1092) % 17837 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 138 hm
    have h_q_lt : 17837 < concatenate (12 * m) 2593 := by
      have h_base_gt : 17837 < rep_threes 1656 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 139
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 139 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1668 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 140
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 140 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 1680 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 141
    have h_mod_mod : m % 49 = 43 := by omega
    have h_eq : 12 * m = 588 * (m / 49) + 516 := by omega
    have h_div : 197 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 197 588 516 (by decide)
      · have h1 : powMod_fuel 20 10 588 197 = 1 := by decide
        have h2 : powMod_fuel 20 10 588 197 = (10 ^ 588) % 197 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 141 hm
    have h_q_lt : 197 < concatenate (12 * m) 2593 := by
      have h_base_gt : 197 < rep_threes 1692 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 142
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 142 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1704 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 143
    have h_mod_mod : m % 216 = 143 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1716 := by omega
    have h_div : 27580265477 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 27580265477 2592 1716 (by decide)
      · have h1 : powMod_fuel 20 10 2592 27580265477 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 27580265477 = (10 ^ 2592) % 27580265477 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 143 hm
    have h_q_lt : 27580265477 < concatenate (12 * m) 2593 := by
      have h_base_gt : 27580265477 < rep_threes 1716 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_8 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 144 ∨ m % 216 = 145 ∨ m % 216 = 146 ∨ m % 216 = 147 ∨ m % 216 = 148 ∨ m % 216 = 149 ∨ m % 216 = 150 ∨ m % 216 = 151 ∨ m % 216 = 152 ∨ m % 216 = 153 ∨ m % 216 = 154 ∨ m % 216 = 155 ∨ m % 216 = 156 ∨ m % 216 = 157 ∨ m % 216 = 158 ∨ m % 216 = 159 ∨ m % 216 = 160 ∨ m % 216 = 161) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 144
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 144 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1728 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 145
    have h_mod_mod : m % 216 = 145 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1740 := by omega
    have h_div : 27232433 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 27232433 2592 1740 (by decide)
      · have h1 : powMod_fuel 20 10 2592 27232433 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 27232433 = (10 ^ 2592) % 27232433 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 145 hm
    have h_q_lt : 27232433 < concatenate (12 * m) 2593 := by
      have h_base_gt : 27232433 < rep_threes 1740 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 146
    have h_mod_mod : m % 63 = 20 := by omega
    have h_eq : 12 * m = 756 * (m / 63) + 240 := by omega
    have h_div : 379 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 379 756 240 (by decide)
      · have h1 : powMod_fuel 20 10 756 379 = 1 := by decide
        have h2 : powMod_fuel 20 10 756 379 = (10 ^ 756) % 379 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 146 hm
    have h_q_lt : 379 < concatenate (12 * m) 2593 := by
      have h_base_gt : 379 < rep_threes 1752 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 147
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 147 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1764 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 148
    have h_mod_mod : m % 23 = 10 := by omega
    have h_eq : 12 * m = 276 * (m / 23) + 120 := by omega
    have h_div : 47 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 47 276 120 (by decide)
      · have h1 : powMod_fuel 20 10 276 47 = 1 := by decide
        have h2 : powMod_fuel 20 10 276 47 = (10 ^ 276) % 47 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 148 hm
    have h_q_lt : 47 < concatenate (12 * m) 2593 := by
      have h_base_gt : 47 < rep_threes 1776 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 149
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 149 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1788 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 150
    have h_mod_mod : m % 216 = 150 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1800 := by omega
    have h_div : 108731301884472907 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 108731301884472907 2592 1800 (by decide)
      · have h1 : powMod_fuel 20 10 2592 108731301884472907 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 108731301884472907 = (10 ^ 2592) % 108731301884472907 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 150 hm
    have h_q_lt : 108731301884472907 < concatenate (12 * m) 2593 := by
      have h_base_gt : 108731301884472907 < rep_threes 1800 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 151
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 151 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 1812 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 152
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 152 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1824 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 153
    have h_mod_mod : m % 2464 = 153 := by omega
    have h_eq : 12 * m = 29568 * (m / 2464) + 1836 := by omega
    have h_div : 9857 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 9857 29568 1836 (by decide)
      · have h1 : powMod_fuel 20 10 29568 9857 = 1 := by decide
        have h2 : powMod_fuel 20 10 29568 9857 = (10 ^ 29568) % 9857 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 153 hm
    have h_q_lt : 9857 < concatenate (12 * m) 2593 := by
      have h_base_gt : 9857 < rep_threes 1836 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 154
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 154 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1848 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 155
    have h_mod_mod : m % 13 = 12 := by omega
    have h_eq : 12 * m = 156 * (m / 13) + 144 := by omega
    have h_div : 859 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 859 156 144 (by decide)
      · have h1 : powMod_fuel 20 10 156 859 = 1 := by decide
        have h2 : powMod_fuel 20 10 156 859 = (10 ^ 156) % 859 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 155 hm
    have h_q_lt : 859 < concatenate (12 * m) 2593 := by
      have h_base_gt : 859 < rep_threes 1860 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 156
    have h_mod_mod : m % 131 = 25 := by omega
    have h_eq : 12 * m = 1572 * (m / 131) + 300 := by omega
    have h_div : 263 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 263 1572 300 (by decide)
      · have h1 : powMod_fuel 20 10 1572 263 = 1 := by decide
        have h2 : powMod_fuel 20 10 1572 263 = (10 ^ 1572) % 263 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 156 hm
    have h_q_lt : 263 < concatenate (12 * m) 2593 := by
      have h_base_gt : 263 < rep_threes 1872 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 157
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 157 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 1884 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 158
    have h_mod_mod : m % 3593 = 158 := by omega
    have h_eq : 12 * m = 43116 * (m / 3593) + 1896 := by omega
    have h_div : 7187 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 7187 43116 1896 (by decide)
      · have h1 : powMod_fuel 20 10 43116 7187 = 1 := by decide
        have h2 : powMod_fuel 20 10 43116 7187 = (10 ^ 43116) % 7187 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 158 hm
    have h_q_lt : 7187 < concatenate (12 * m) 2593 := by
      have h_base_gt : 7187 < rep_threes 1896 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 159
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 159 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1908 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 160
    have h_mod_mod : m % 216 = 160 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 1920 := by omega
    have h_div : 32935669302833836474379 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 32935669302833836474379 2592 1920 (by decide)
      · have h1 : powMod_fuel 20 10 2592 32935669302833836474379 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 32935669302833836474379 = (10 ^ 2592) % 32935669302833836474379 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 160 hm
    have h_q_lt : 32935669302833836474379 < concatenate (12 * m) 2593 := by
      have h_base_gt : 32935669302833836474379 < rep_threes 1920 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 161
    by_cases h_eq_m : m = 161
    · subst h_eq_m
      exact not_prime_r161
    · have h_mod_mod : m % 216 = 161 := by omega
      have h_eq : 12 * m = 2592 * (m / 216) + 1932 := by omega
      have h_div : 2593 ∣ concatenate (12 * m) 2593 := by
        rw [h_eq]
        apply div_of_step_simple 2593 2592 1932 (by decide) (by decide)
      have h_concat_gt := concatenate_ge_r m 216 hm
      have h_q_lt : 2593 < concatenate (12 * m) 2593 := by
        have h_base_gt : 2593 < rep_threes 2592 * 10000 + 2593 := by decide
        omega
      exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_9 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 162 ∨ m % 216 = 163 ∨ m % 216 = 164 ∨ m % 216 = 165 ∨ m % 216 = 166 ∨ m % 216 = 167 ∨ m % 216 = 168 ∨ m % 216 = 169 ∨ m % 216 = 170 ∨ m % 216 = 171 ∨ m % 216 = 172 ∨ m % 216 = 173 ∨ m % 216 = 174 ∨ m % 216 = 175 ∨ m % 216 = 176 ∨ m % 216 = 177 ∨ m % 216 = 178 ∨ m % 216 = 179) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 162
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 162 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 1944 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 163
    have h_mod_mod : m % 1019 = 163 := by omega
    have h_eq : 12 * m = 12228 * (m / 1019) + 1956 := by omega
    have h_div : 2039 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 2039 12228 1956 (by decide)
      · have h1 : powMod_fuel 20 10 12228 2039 = 1 := by decide
        have h2 : powMod_fuel 20 10 12228 2039 = (10 ^ 12228) % 2039 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 163 hm
    have h_q_lt : 2039 < concatenate (12 * m) 2593 := by
      have h_base_gt : 2039 < rep_threes 1956 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 164
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 164 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 1968 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 165
    have h_mod_mod : m % 299 = 165 := by omega
    have h_eq : 12 * m = 3588 * (m / 299) + 1980 := by omega
    have h_div : 599 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 599 3588 1980 (by decide)
      · have h1 : powMod_fuel 20 10 3588 599 = 1 := by decide
        have h2 : powMod_fuel 20 10 3588 599 = (10 ^ 3588) % 599 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 165 hm
    have h_q_lt : 599 < concatenate (12 * m) 2593 := by
      have h_base_gt : 599 < rep_threes 1980 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 166
    have h_mod_mod : m % 96 = 70 := by omega
    have h_eq : 12 * m = 1152 * (m / 96) + 840 := by omega
    have h_div : 1153 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1153 1152 840 (by decide)
      · have h1 : powMod_fuel 20 10 1152 1153 = 1 := by decide
        have h2 : powMod_fuel 20 10 1152 1153 = (10 ^ 1152) % 1153 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 166 hm
    have h_q_lt : 1153 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1153 < rep_threes 1992 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 167
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 167 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 2004 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 168
    have h_mod_mod : m % 13 = 12 := by omega
    have h_eq : 12 * m = 156 * (m / 13) + 144 := by omega
    have h_div : 859 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 859 156 144 (by decide)
      · have h1 : powMod_fuel 20 10 156 859 = 1 := by decide
        have h2 : powMod_fuel 20 10 156 859 = (10 ^ 156) % 859 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 168 hm
    have h_q_lt : 859 < concatenate (12 * m) 2593 := by
      have h_base_gt : 859 < rep_threes 2016 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 169
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 169 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 2028 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 170
    have h_mod_mod : m % 386 = 170 := by omega
    have h_eq : 12 * m = 4632 * (m / 386) + 2040 := by omega
    have h_div : 3089 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 3089 4632 2040 (by decide)
      · have h1 : powMod_fuel 20 10 4632 3089 = 1 := by decide
        have h2 : powMod_fuel 20 10 4632 3089 = (10 ^ 4632) % 3089 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 170 hm
    have h_q_lt : 3089 < concatenate (12 * m) 2593 := by
      have h_base_gt : 3089 < rep_threes 2040 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 171
    have h_mod_mod : m % 23 = 10 := by omega
    have h_eq : 12 * m = 276 * (m / 23) + 120 := by omega
    have h_div : 47 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 47 276 120 (by decide)
      · have h1 : powMod_fuel 20 10 276 47 = 1 := by decide
        have h2 : powMod_fuel 20 10 276 47 = (10 ^ 276) % 47 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 171 hm
    have h_q_lt : 47 < concatenate (12 * m) 2593 := by
      have h_base_gt : 47 < rep_threes 2052 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 172
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 172 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 2064 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 173
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 173 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 2076 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 174
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 174 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 2088 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 175
    have h_mod_mod : m % 55 = 10 := by omega
    have h_eq : 12 * m = 660 * (m / 55) + 120 := by omega
    have h_div : 1321 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1321 660 120 (by decide)
      · have h1 : powMod_fuel 20 10 660 1321 = 1 := by decide
        have h2 : powMod_fuel 20 10 660 1321 = (10 ^ 660) % 1321 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 175 hm
    have h_q_lt : 1321 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1321 < rep_threes 2100 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 176
    have h_mod_mod : m % 216 = 176 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 2112 := by omega
    have h_div : 6331265839 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 6331265839 2592 2112 (by decide)
      · have h1 : powMod_fuel 20 10 2592 6331265839 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 6331265839 = (10 ^ 2592) % 6331265839 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 176 hm
    have h_q_lt : 6331265839 < concatenate (12 * m) 2593 := by
      have h_base_gt : 6331265839 < rep_threes 2112 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 177
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 177 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 2124 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 178
    have h_mod_mod : m % 1463 = 178 := by omega
    have h_eq : 12 * m = 17556 * (m / 1463) + 2136 := by omega
    have h_div : 2927 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 2927 17556 2136 (by decide)
      · have h1 : powMod_fuel 20 10 17556 2927 = 1 := by decide
        have h2 : powMod_fuel 20 10 17556 2927 = (10 ^ 17556) % 2927 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 178 hm
    have h_q_lt : 2927 < concatenate (12 * m) 2593 := by
      have h_base_gt : 2927 < rep_threes 2136 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 179
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 179 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 2148 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_10 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 180 ∨ m % 216 = 181 ∨ m % 216 = 182 ∨ m % 216 = 183 ∨ m % 216 = 184 ∨ m % 216 = 185 ∨ m % 216 = 186 ∨ m % 216 = 187 ∨ m % 216 = 188 ∨ m % 216 = 189 ∨ m % 216 = 190 ∨ m % 216 = 191 ∨ m % 216 = 192 ∨ m % 216 = 193 ∨ m % 216 = 194 ∨ m % 216 = 195 ∨ m % 216 = 196 ∨ m % 216 = 197) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 180
    have h_mod_mod : m % 257 = 180 := by omega
    have h_eq : 12 * m = 3084 * (m / 257) + 2160 := by omega
    have h_div : 1543 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 1543 3084 2160 (by decide)
      · have h1 : powMod_fuel 20 10 3084 1543 = 1 := by decide
        have h2 : powMod_fuel 20 10 3084 1543 = (10 ^ 3084) % 1543 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 180 hm
    have h_q_lt : 1543 < concatenate (12 * m) 2593 := by
      have h_base_gt : 1543 < rep_threes 2160 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 181
    have h_mod_mod : m % 13 = 12 := by omega
    have h_eq : 12 * m = 156 * (m / 13) + 144 := by omega
    have h_div : 859 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 859 156 144 (by decide)
      · have h1 : powMod_fuel 20 10 156 859 = 1 := by decide
        have h2 : powMod_fuel 20 10 156 859 = (10 ^ 156) % 859 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 181 hm
    have h_q_lt : 859 < concatenate (12 * m) 2593 := by
      have h_base_gt : 859 < rep_threes 2172 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 182
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 182 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 2184 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 183
    have h_mod_mod : m % 35 = 8 := by omega
    have h_eq : 12 * m = 420 * (m / 35) + 96 := by omega
    have h_div : 71 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 71 420 96 (by decide)
      · have h1 : powMod_fuel 20 10 420 71 = 1 := by decide
        have h2 : powMod_fuel 20 10 420 71 = (10 ^ 420) % 71 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 183 hm
    have h_q_lt : 71 < concatenate (12 * m) 2593 := by
      have h_base_gt : 71 < rep_threes 2196 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 184
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 184 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 2208 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 185
    have h_mod_mod : m % 65 = 55 := by omega
    have h_eq : 12 * m = 780 * (m / 65) + 660 := by omega
    have h_div : 131 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 131 780 660 (by decide)
      · have h1 : powMod_fuel 20 10 780 131 = 1 := by decide
        have h2 : powMod_fuel 20 10 780 131 = (10 ^ 780) % 131 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 185 hm
    have h_q_lt : 131 < concatenate (12 * m) 2593 := by
      have h_base_gt : 131 < rep_threes 2220 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 186
    have h_mod_mod : m % 431 = 186 := by omega
    have h_eq : 12 * m = 5172 * (m / 431) + 2232 := by omega
    have h_div : 863 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 863 5172 2232 (by decide)
      · have h1 : powMod_fuel 20 10 5172 863 = 1 := by decide
        have h2 : powMod_fuel 20 10 5172 863 = (10 ^ 5172) % 863 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 186 hm
    have h_q_lt : 863 < concatenate (12 * m) 2593 := by
      have h_base_gt : 863 < rep_threes 2232 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 187
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 187 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 2244 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 188
    have h_mod_mod : m % 10225 = 188 := by omega
    have h_eq : 12 * m = 122700 * (m / 10225) + 2256 := by omega
    have h_div : 122701 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 122701 122700 2256 (by decide)
      · have h1 : powMod_fuel 20 10 122700 122701 = 1 := by decide
        have h2 : powMod_fuel 20 10 122700 122701 = (10 ^ 122700) % 122701 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 188 hm
    have h_q_lt : 122701 < concatenate (12 * m) 2593 := by
      have h_base_gt : 122701 < rep_threes 2256 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 189
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 189 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 2268 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 190
    have h_mod_mod : m % 49 = 43 := by omega
    have h_eq : 12 * m = 588 * (m / 49) + 516 := by omega
    have h_div : 197 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 197 588 516 (by decide)
      · have h1 : powMod_fuel 20 10 588 197 = 1 := by decide
        have h2 : powMod_fuel 20 10 588 197 = (10 ^ 588) % 197 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 190 hm
    have h_q_lt : 197 < concatenate (12 * m) 2593 := by
      have h_base_gt : 197 < rep_threes 2280 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 191
    have h_mod_mod : m % 216 = 191 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 2292 := by omega
    have h_div : 7595587 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 7595587 2592 2292 (by decide)
      · have h1 : powMod_fuel 20 10 2592 7595587 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 7595587 = (10 ^ 2592) % 7595587 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 191 hm
    have h_q_lt : 7595587 < concatenate (12 * m) 2593 := by
      have h_base_gt : 7595587 < rep_threes 2292 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 192
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 192 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 2304 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 193
    have h_mod_mod : m % 3911 = 193 := by omega
    have h_eq : 12 * m = 46932 * (m / 3911) + 2316 := by omega
    have h_div : 7823 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 7823 46932 2316 (by decide)
      · have h1 : powMod_fuel 20 10 46932 7823 = 1 := by decide
        have h2 : powMod_fuel 20 10 46932 7823 = (10 ^ 46932) % 7823 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 193 hm
    have h_q_lt : 7823 < concatenate (12 * m) 2593 := by
      have h_base_gt : 7823 < rep_threes 2316 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 194
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 194 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 2328 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 195
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 195 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 2340 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 196
    have h_mod_mod : m % 216 = 196 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 2352 := by omega
    have h_div : 32422861 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 32422861 2592 2352 (by decide)
      · have h1 : powMod_fuel 20 10 2592 32422861 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 32422861 = (10 ^ 2592) % 32422861 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 196 hm
    have h_q_lt : 32422861 < concatenate (12 * m) 2593 := by
      have h_base_gt : 32422861 < rep_threes 2352 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 197
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 197 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 2364 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m_chunk_11 (m : ℕ) (hm : m ≥ 1) (h_mod : m % 216 = 198 ∨ m % 216 = 199 ∨ m % 216 = 200 ∨ m % 216 = 201 ∨ m % 216 = 202 ∨ m % 216 = 203 ∨ m % 216 = 204 ∨ m % 216 = 205 ∨ m % 216 = 206 ∨ m % 216 = 207 ∨ m % 216 = 208 ∨ m % 216 = 209 ∨ m % 216 = 210 ∨ m % 216 = 211 ∨ m % 216 = 212 ∨ m % 216 = 213 ∨ m % 216 = 214 ∨ m % 216 = 215) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  rcases h_mod with hc_0 | hc_1 | hc_2 | hc_3 | hc_4 | hc_5 | hc_6 | hc_7 | hc_8 | hc_9 | hc_10 | hc_11 | hc_12 | hc_13 | hc_14 | hc_15 | hc_16 | hc_17
  · -- Case 198
    by_cases h_eq_m : m = 198
    · subst h_eq_m
      exact not_prime_r198
    · have h_mod_mod : m % 216 = 198 := by omega
      have h_eq : 12 * m = 2592 * (m / 216) + 2376 := by omega
      have h_div : 2593 ∣ concatenate (12 * m) 2593 := by
        rw [h_eq]
        apply div_of_step_simple 2593 2592 2376 (by decide) (by decide)
      have h_concat_gt := concatenate_ge_r m 216 hm
      have h_q_lt : 2593 < concatenate (12 * m) 2593 := by
        have h_base_gt : 2593 < rep_threes 2592 * 10000 + 2593 := by decide
        omega
      exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 199
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 199 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 2388 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 200
    have h_mod_mod : m % 216 = 200 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 2400 := by omega
    have h_div : 24415832681 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 24415832681 2592 2400 (by decide)
      · have h1 : powMod_fuel 20 10 2592 24415832681 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 24415832681 = (10 ^ 2592) % 24415832681 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 200 hm
    have h_q_lt : 24415832681 < concatenate (12 * m) 2593 := by
      have h_base_gt : 24415832681 < rep_threes 2400 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 201
    have h_mod_mod : m % 2065 = 201 := by omega
    have h_eq : 12 * m = 24780 * (m / 2065) + 2412 := by omega
    have h_div : 12391 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 12391 24780 2412 (by decide)
      · have h1 : powMod_fuel 20 10 24780 12391 = 1 := by decide
        have h2 : powMod_fuel 20 10 24780 12391 = (10 ^ 24780) % 12391 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 201 hm
    have h_q_lt : 12391 < concatenate (12 * m) 2593 := by
      have h_base_gt : 12391 < rep_threes 2412 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 202
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 202 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 2424 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 203
    have h_mod_mod : m % 688 = 203 := by omega
    have h_eq : 12 * m = 8256 * (m / 688) + 2436 := by omega
    have h_div : 2753 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 2753 8256 2436 (by decide)
      · have h1 : powMod_fuel 20 10 8256 2753 = 1 := by decide
        have h2 : powMod_fuel 20 10 8256 2753 = (10 ^ 8256) % 2753 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 203 hm
    have h_q_lt : 2753 < concatenate (12 * m) 2593 := by
      have h_base_gt : 2753 < rep_threes 2436 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 204
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 204 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 2448 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 205
    have h_mod_mod : m % 216 = 205 := by omega
    have h_eq : 12 * m = 2592 * (m / 216) + 2460 := by omega
    have h_div : 35623561 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 35623561 2592 2460 (by decide)
      · have h1 : powMod_fuel 20 10 2592 35623561 = 1 := by decide
        have h2 : powMod_fuel 20 10 2592 35623561 = (10 ^ 2592) % 35623561 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 205 hm
    have h_q_lt : 35623561 < concatenate (12 * m) 2593 := by
      have h_base_gt : 35623561 < rep_threes 2460 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 206
    have h_mod_mod : m % 11 = 8 := by omega
    have h_eq : 12 * m = 132 * (m / 11) + 96 := by omega
    have h_div : 23 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 23 132 96 (by decide)
      · have h1 : powMod_fuel 20 10 132 23 = 1 := by decide
        have h2 : powMod_fuel 20 10 132 23 = (10 ^ 132) % 23 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 206 hm
    have h_q_lt : 23 < concatenate (12 * m) 2593 := by
      have h_base_gt : 23 < rep_threes 2472 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 207
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 207 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 2484 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 208
    have h_mod_mod : m % 753 = 208 := by omega
    have h_eq : 12 * m = 9036 * (m / 753) + 2496 := by omega
    have h_div : 27109 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 27109 9036 2496 (by decide)
      · have h1 : powMod_fuel 20 10 9036 27109 = 1 := by decide
        have h2 : powMod_fuel 20 10 9036 27109 = (10 ^ 9036) % 27109 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 208 hm
    have h_q_lt : 27109 < concatenate (12 * m) 2593 := by
      have h_base_gt : 27109 < rep_threes 2496 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 209
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 209 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 2508 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 210
    have h_mod_mod : m % 41 = 5 := by omega
    have h_eq : 12 * m = 492 * (m / 41) + 60 := by omega
    have h_div : 83 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 83 492 60 (by decide)
      · have h1 : powMod_fuel 20 10 492 83 = 1 := by decide
        have h2 : powMod_fuel 20 10 492 83 = (10 ^ 492) % 83 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 210 hm
    have h_q_lt : 83 < concatenate (12 * m) 2593 := by
      have h_base_gt : 83 < rep_threes 2520 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 211
    have h_mod_mod : m % 38 = 21 := by omega
    have h_eq : 12 * m = 456 * (m / 38) + 252 := by omega
    have h_div : 457 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 457 456 252 (by decide)
      · have h1 : powMod_fuel 20 10 456 457 = 1 := by decide
        have h2 : powMod_fuel 20 10 456 457 = (10 ^ 456) % 457 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 211 hm
    have h_q_lt : 457 < concatenate (12 * m) 2593 := by
      have h_base_gt : 457 < rep_threes 2532 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 212
    have h_mod_mod : m % 5 = 2 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 24 := by omega
    have h_div : 61 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 61 60 24 (by decide)
      · have h1 : powMod_fuel 20 10 60 61 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 61 = (10 ^ 60) % 61 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 212 hm
    have h_q_lt : 61 < concatenate (12 * m) 2593 := by
      have h_base_gt : 61 < rep_threes 2544 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 213
    have h_mod_mod : m % 61 = 30 := by omega
    have h_eq : 12 * m = 732 * (m / 61) + 360 := by omega
    have h_div : 733 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 733 732 360 (by decide)
      · have h1 : powMod_fuel 20 10 732 733 = 1 := by decide
        have h2 : powMod_fuel 20 10 732 733 = (10 ^ 732) % 733 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 213 hm
    have h_q_lt : 733 < concatenate (12 * m) 2593 := by
      have h_base_gt : 733 < rep_threes 2556 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 214
    have h_mod_mod : m % 5 = 4 := by omega
    have h_eq : 12 * m = 60 * (m / 5) + 48 := by omega
    have h_div : 31 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 31 60 48 (by decide)
      · have h1 : powMod_fuel 20 10 60 31 = 1 := by decide
        have h2 : powMod_fuel 20 10 60 31 = (10 ^ 60) % 31 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 214 hm
    have h_q_lt : 31 < concatenate (12 * m) 2593 := by
      have h_base_gt : 31 < rep_threes 2568 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt
  · -- Case 215
    have h_mod_mod : m % 1105 = 215 := by omega
    have h_eq : 12 * m = 13260 * (m / 1105) + 2580 := by omega
    have h_div : 4421 ∣ concatenate (12 * m) 2593 := by
      rw [h_eq]
      apply div_of_step_simple 4421 13260 2580 (by decide)
      · have h1 : powMod_fuel 20 10 13260 4421 = 1 := by decide
        have h2 : powMod_fuel 20 10 13260 4421 = (10 ^ 13260) % 4421 := by apply powMod_fuel_eq; decide
        unfold Nat.ModEq
        rw [← h2, h1]
        decide
    have h_concat_gt := concatenate_ge_r m 215 hm
    have h_q_lt : 4421 < concatenate (12 * m) 2593 := by
      have h_base_gt : 4421 < rep_threes 2580 * 10000 + 2593 := by decide
      omega
    exact not_prime_of_dvd (by decide) h_div h_q_lt


lemma div_of_twelve_m (m : ℕ) (hm : m ≥ 1) : ¬ Nat.Prime (concatenate (12 * m) 2593) := by
  have h_div : (m % 216 ≥ 0 ∧ m % 216 < 18) ∨ (m % 216 ≥ 18 ∧ m % 216 < 36) ∨ (m % 216 ≥ 36 ∧ m % 216 < 54) ∨ (m % 216 ≥ 54 ∧ m % 216 < 72) ∨ (m % 216 ≥ 72 ∧ m % 216 < 90) ∨ (m % 216 ≥ 90 ∧ m % 216 < 108) ∨ (m % 216 ≥ 108 ∧ m % 216 < 126) ∨ (m % 216 ≥ 126 ∧ m % 216 < 144) ∨ (m % 216 ≥ 144 ∧ m % 216 < 162) ∨ (m % 216 ≥ 162 ∧ m % 216 < 180) ∨ (m % 216 ≥ 180 ∧ m % 216 < 198) ∨ m % 216 ≥ 198 := by omega
  rcases h_div with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · apply div_of_twelve_m_chunk_0 m hm
    have h_or : m % 216 = 0 ∨ m % 216 = 1 ∨ m % 216 = 2 ∨ m % 216 = 3 ∨ m % 216 = 4 ∨ m % 216 = 5 ∨ m % 216 = 6 ∨ m % 216 = 7 ∨ m % 216 = 8 ∨ m % 216 = 9 ∨ m % 216 = 10 ∨ m % 216 = 11 ∨ m % 216 = 12 ∨ m % 216 = 13 ∨ m % 216 = 14 ∨ m % 216 = 15 ∨ m % 216 = 16 ∨ m % 216 = 17 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_1 m hm
    have h_or : m % 216 = 18 ∨ m % 216 = 19 ∨ m % 216 = 20 ∨ m % 216 = 21 ∨ m % 216 = 22 ∨ m % 216 = 23 ∨ m % 216 = 24 ∨ m % 216 = 25 ∨ m % 216 = 26 ∨ m % 216 = 27 ∨ m % 216 = 28 ∨ m % 216 = 29 ∨ m % 216 = 30 ∨ m % 216 = 31 ∨ m % 216 = 32 ∨ m % 216 = 33 ∨ m % 216 = 34 ∨ m % 216 = 35 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_2 m hm
    have h_or : m % 216 = 36 ∨ m % 216 = 37 ∨ m % 216 = 38 ∨ m % 216 = 39 ∨ m % 216 = 40 ∨ m % 216 = 41 ∨ m % 216 = 42 ∨ m % 216 = 43 ∨ m % 216 = 44 ∨ m % 216 = 45 ∨ m % 216 = 46 ∨ m % 216 = 47 ∨ m % 216 = 48 ∨ m % 216 = 49 ∨ m % 216 = 50 ∨ m % 216 = 51 ∨ m % 216 = 52 ∨ m % 216 = 53 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_3 m hm
    have h_or : m % 216 = 54 ∨ m % 216 = 55 ∨ m % 216 = 56 ∨ m % 216 = 57 ∨ m % 216 = 58 ∨ m % 216 = 59 ∨ m % 216 = 60 ∨ m % 216 = 61 ∨ m % 216 = 62 ∨ m % 216 = 63 ∨ m % 216 = 64 ∨ m % 216 = 65 ∨ m % 216 = 66 ∨ m % 216 = 67 ∨ m % 216 = 68 ∨ m % 216 = 69 ∨ m % 216 = 70 ∨ m % 216 = 71 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_4 m hm
    have h_or : m % 216 = 72 ∨ m % 216 = 73 ∨ m % 216 = 74 ∨ m % 216 = 75 ∨ m % 216 = 76 ∨ m % 216 = 77 ∨ m % 216 = 78 ∨ m % 216 = 79 ∨ m % 216 = 80 ∨ m % 216 = 81 ∨ m % 216 = 82 ∨ m % 216 = 83 ∨ m % 216 = 84 ∨ m % 216 = 85 ∨ m % 216 = 86 ∨ m % 216 = 87 ∨ m % 216 = 88 ∨ m % 216 = 89 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_5 m hm
    have h_or : m % 216 = 90 ∨ m % 216 = 91 ∨ m % 216 = 92 ∨ m % 216 = 93 ∨ m % 216 = 94 ∨ m % 216 = 95 ∨ m % 216 = 96 ∨ m % 216 = 97 ∨ m % 216 = 98 ∨ m % 216 = 99 ∨ m % 216 = 100 ∨ m % 216 = 101 ∨ m % 216 = 102 ∨ m % 216 = 103 ∨ m % 216 = 104 ∨ m % 216 = 105 ∨ m % 216 = 106 ∨ m % 216 = 107 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_6 m hm
    have h_or : m % 216 = 108 ∨ m % 216 = 109 ∨ m % 216 = 110 ∨ m % 216 = 111 ∨ m % 216 = 112 ∨ m % 216 = 113 ∨ m % 216 = 114 ∨ m % 216 = 115 ∨ m % 216 = 116 ∨ m % 216 = 117 ∨ m % 216 = 118 ∨ m % 216 = 119 ∨ m % 216 = 120 ∨ m % 216 = 121 ∨ m % 216 = 122 ∨ m % 216 = 123 ∨ m % 216 = 124 ∨ m % 216 = 125 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_7 m hm
    have h_or : m % 216 = 126 ∨ m % 216 = 127 ∨ m % 216 = 128 ∨ m % 216 = 129 ∨ m % 216 = 130 ∨ m % 216 = 131 ∨ m % 216 = 132 ∨ m % 216 = 133 ∨ m % 216 = 134 ∨ m % 216 = 135 ∨ m % 216 = 136 ∨ m % 216 = 137 ∨ m % 216 = 138 ∨ m % 216 = 139 ∨ m % 216 = 140 ∨ m % 216 = 141 ∨ m % 216 = 142 ∨ m % 216 = 143 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_8 m hm
    have h_or : m % 216 = 144 ∨ m % 216 = 145 ∨ m % 216 = 146 ∨ m % 216 = 147 ∨ m % 216 = 148 ∨ m % 216 = 149 ∨ m % 216 = 150 ∨ m % 216 = 151 ∨ m % 216 = 152 ∨ m % 216 = 153 ∨ m % 216 = 154 ∨ m % 216 = 155 ∨ m % 216 = 156 ∨ m % 216 = 157 ∨ m % 216 = 158 ∨ m % 216 = 159 ∨ m % 216 = 160 ∨ m % 216 = 161 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_9 m hm
    have h_or : m % 216 = 162 ∨ m % 216 = 163 ∨ m % 216 = 164 ∨ m % 216 = 165 ∨ m % 216 = 166 ∨ m % 216 = 167 ∨ m % 216 = 168 ∨ m % 216 = 169 ∨ m % 216 = 170 ∨ m % 216 = 171 ∨ m % 216 = 172 ∨ m % 216 = 173 ∨ m % 216 = 174 ∨ m % 216 = 175 ∨ m % 216 = 176 ∨ m % 216 = 177 ∨ m % 216 = 178 ∨ m % 216 = 179 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_10 m hm
    have h_or : m % 216 = 180 ∨ m % 216 = 181 ∨ m % 216 = 182 ∨ m % 216 = 183 ∨ m % 216 = 184 ∨ m % 216 = 185 ∨ m % 216 = 186 ∨ m % 216 = 187 ∨ m % 216 = 188 ∨ m % 216 = 189 ∨ m % 216 = 190 ∨ m % 216 = 191 ∨ m % 216 = 192 ∨ m % 216 = 193 ∨ m % 216 = 194 ∨ m % 216 = 195 ∨ m % 216 = 196 ∨ m % 216 = 197 := by omega
    exact h_or
  · apply div_of_twelve_m_chunk_11 m hm
    have h_or : m % 216 = 198 ∨ m % 216 = 199 ∨ m % 216 = 200 ∨ m % 216 = 201 ∨ m % 216 = 202 ∨ m % 216 = 203 ∨ m % 216 = 204 ∨ m % 216 = 205 ∨ m % 216 = 206 ∨ m % 216 = 207 ∨ m % 216 = 208 ∨ m % 216 = 209 ∨ m % 216 = 210 ∨ m % 216 = 211 ∨ m % 216 = 212 ∨ m % 216 = 213 ∨ m % 216 = 214 ∨ m % 216 = 215 := by omega
    exact h_or


theorem A242775_378_eq_zero : A242775 378 = 0 := by
  unfold A242775
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rw [prime_of_index_378]
  apply Nat.sInf_eq_zero.2
  right
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hk
  by_cases h_odd : k % 2 = 1
  · have h_eq : k = 2 * (k / 2) + 1 := by omega
    have h_div := div_eleven_of_odd (k / 2)
    rw [← h_eq] at h_div
    have h_gt : 11 < concatenate k 2593 := by
      unfold concatenate
      omega
    exact not_prime_of_dvd (by decide) h_div h_gt
  · have h_even : k % 2 = 0 := by omega
    by_cases h6_4 : k % 6 = 4
    · have h_eq : k = 6 * (k / 6) + 4 := by omega
      have h_div := div_seven_of_four_mod_six (k / 6)
      rw [← h_eq] at h_div
      have h_gt : 7 < concatenate k 2593 := by
        unfold concatenate
        omega
      exact not_prime_of_dvd (by decide) h_div h_gt
    · by_cases h6_2 : k % 6 = 2
      · have h_eq : k = 6 * (k / 6) + 2 := by omega
        have h_div := div_thirty_seven_of_two_mod_six (k / 6)
        rw [← h_eq] at h_div
        have h_gt : 37 < concatenate k 2593 := by
          unfold concatenate
          omega
        exact not_prime_of_dvd (by decide) h_div h_gt
      · have h6_0 : k % 6 = 0 := by omega
        by_cases h12_6 : k % 12 = 6
        · have h_eq : k = 12 * (k / 12) + 6 := by omega
          have h_div := div_one_hundred_and_one_of_six_mod_twelve (k / 12)
          rw [← h_eq] at h_div
          have h_gt : 101 < concatenate k 2593 := by
            unfold concatenate
            omega
          exact not_prime_of_dvd (by decide) h_div h_gt
        · have h12_0 : k % 12 = 0 := by omega
          have hm : k / 12 ≥ 1 := by omega
          have h_not_prime : ¬ Nat.Prime (concatenate k 2593) := by
            have h_eq : 12 * (k / 12) = k := by omega
            have h_not_prime_12m := div_of_twelve_m (k / 12) hm
            rw [h_eq] at h_not_prime_12m
            exact h_not_prime_12m
          exact h_not_prime

/-- OEIS A242775 Conjecture disproof -/
theorem oeis_242775_conjecture_0.disproof : ¬ (∀ n, 4 ≤ n → A242775 n > 0) := by
  intro h
  have h4 : 4 ≤ 378 := by decide
  have h_pos := h 378 h4
  have h_zero : A242775 378 = 0 := A242775_378_eq_zero
  omega
