import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

primes = [q for q in range(2, 284) if is_prime(q)]

def lcm(a, b):
    if a == 0 or b == 0: return 0
    return abs(a * b) // math.gcd(a, b)

x = [0, 1]
for n in range(2, 283 * 283):
    x.append(2 * x[-1] + lcm(x[-1], n))

multipliers = {}
for q in primes:
    for k in range(1, len(x)):
        if x[k] % q == 0:
            multipliers[q] = k
            break

print(f"Found {len(primes)} primes up to 283.")

# Generate Lean code for q_dvd_x_seq_q_sq_small
lean_cases = []
for q in range(2, 284):
    if is_prime(q):
        kq = multipliers[q]
        lean_cases.append(f"  · -- q = {q}\n    have h_dvd : {q} ∣ x_seq_tr {kq} := by decide\n    have h_eq : x_seq_tr {kq} = x_seq {kq} := x_seq_tr_eq {kq}\n    have h_dvd' : {q} ∣ x_seq {kq} := by\n      rw [← h_eq]\n      exact h_dvd\n    exact Nat.dvd_trans h_dvd' (x_seq_dvd_x_seq_of_le (by decide) (by decide))")
    else:
        lean_cases.append("  · contradiction")

cases_str = "\n".join(lean_cases)

spec_template = f'''import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Nat

/--
The auxiliary sequence $x(n)$, where $x(1)=1$ and $x(n) = 2 \\cdot x(n-1) + \\mathrm{{lcm}}(x(n-1), n)$ for $n > 1$.
`x_seq n` corresponds to the OEIS term $x(n)$.
This definition is set up for `n : ℕ` where $n=0$ and $n=1$ are base cases for $x(0)$ and $x(1)$.
Note: Mathlib's `lcm` is `Nat.lcm`.
-/
def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

/--
A135508: $a(n) = x(n+1)/x(n) - 2$ where $x(1)=1$ and $x(n) = 2*x(n-1) + \\operatorname{{lcm}}(x(n-1),n)$.
-/
def A135508 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n
    (x_n_plus_1 / x_n) - 2

lemma x_seq_pos (n : ℕ) (h : n > 0) : x_seq n > 0 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      decide
    | succ n =>
      simp [x_seq]
      have : n + 1 > 0 := Nat.succ_pos n
      have ih' := ih this
      omega

lemma lcm_div_self_eq (a b : ℕ) (ha : a > 0) :
    Nat.lcm a b / a = b / Nat.gcd a b := by
  have h_dvd : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
  have h_cancel : b = Nat.gcd a b * (b / Nat.gcd a b) := (Nat.mul_div_cancel' h_dvd).symm
  have h_lcm : Nat.lcm a b = a * (b / Nat.gcd a b) := by
    have h_gcd : Nat.gcd a b > 0 := by
      exact Nat.gcd_pos_of_pos_left b ha
    have h_prod : a * b = a * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [← h_cancel]
    have h_mul_lcm : Nat.lcm a b * Nat.gcd a b = a * b := by
      rw [Nat.mul_comm]
      exact Nat.gcd_mul_lcm a b
    have h_eq : Nat.lcm a b * Nat.gcd a b = a * (b / Nat.gcd a b) * Nat.gcd a b := by
      rw [h_mul_lcm]
      rw [h_prod]
      ring
    exact Nat.eq_of_mul_eq_mul_right h_gcd h_eq
  rw [h_lcm]
  rw [Nat.mul_div_cancel_left _ ha]

lemma x_seq_p_eq (p : ℕ) (hp : Nat.Prime p) :
    x_seq p = 2 * x_seq (p - 1) + Nat.lcm (x_seq (p - 1)) p := by
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have h_cancel : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have h_def : x_seq (p - 1 + 1) = 2 * x_seq (p - 1) + Nat.lcm (x_seq (p - 1)) (p - 1 + 1) := by
    cases h : p - 1 with
    | zero =>
      omega
    | succ n =>
      rfl
  rw [← h_cancel]
  exact h_def

lemma A135508_eq (p : ℕ) (hp : Nat.Prime p) :
    A135508 (p - 1) = (x_seq p / x_seq (p - 1)) - 2 := by
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have h_ne : p - 1 ≠ 0 := by omega
  unfold A135508
  split_ifs with h
  · contradiction
  · have h_cancel : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    rw [h_cancel]

lemma A135508_p_eq (p : ℕ) (hp : Nat.Prime p) :
    A135508 (p - 1) = Nat.lcm (x_seq (p - 1)) p / x_seq (p - 1) := by
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have h_pos : x_seq (p - 1) > 0 := x_seq_pos (p - 1) (by omega)
  have h_dvd : x_seq (p - 1) ∣ Nat.lcm (x_seq (p - 1)) p := Nat.dvd_lcm_left (x_seq (p - 1)) p
  rw [A135508_eq p hp]
  rw [x_seq_p_eq p hp]
  have h_div : (2 * x_seq (p - 1) + Nat.lcm (x_seq (p - 1)) p) / x_seq (p - 1) =
    2 + Nat.lcm (x_seq (p - 1)) p / x_seq (p - 1) := by
    have h_factor : 2 * x_seq (p - 1) + Nat.lcm (x_seq (p - 1)) p =
      x_seq (p - 1) * (2 + Nat.lcm (x_seq (p - 1)) p / x_seq (p - 1)) := by
      generalize hK : Nat.lcm (x_seq (p - 1)) p / x_seq (p - 1) = K
      have h_lcm : Nat.lcm (x_seq (p - 1)) p = x_seq (p - 1) * K := by
        rw [← hK]
        exact (Nat.mul_div_cancel' h_dvd).symm
      rw [h_lcm]
      ring
    rw [h_factor]
    rw [Nat.mul_div_cancel_left _ h_pos]
  rw [h_div]
  rw [Nat.add_sub_cancel_left]

lemma x_seq_dvd_x_seq_succ (n : ℕ) (h : n > 0) : x_seq n ∣ x_seq (n + 1) := by
  cases n with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero =>
      decide
    | succ n =>
      have : x_seq (n + 3) = 2 * x_seq (n + 2) + Nat.lcm (x_seq (n + 2)) (n + 3) := rfl
      rw [this]
      apply Nat.dvd_add
      · simp
      · apply Nat.dvd_lcm_left

lemma x_seq_dvd_x_seq_add (n k : ℕ) (hn : n > 0) : x_seq n ∣ x_seq (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_succ : x_seq (n + k) ∣ x_seq (n + k + 1) := x_seq_dvd_x_seq_succ (n + k) (by omega)
    exact Nat.dvd_trans ih h_succ

lemma x_seq_dvd_x_seq_of_le {{n m : ℕ}} (hn : n > 0) (h : n ≤ m) : x_seq n ∣ x_seq m := by
  have : m = n + (m - n) := by omega
  rw [this]
  exact x_seq_dvd_x_seq_add n (m - n) hn

lemma factor_lemma (m : ℕ) (hm : m ≥ 1) :
    x_seq (m + 1) = x_seq m * (2 + (m + 1) / Nat.gcd (x_seq m) (m + 1)) := by
  have h_pos : x_seq m > 0 := x_seq_pos m (by omega)
  have h_dvd_lcm : x_seq m ∣ Nat.lcm (x_seq m) (m + 1) := Nat.dvd_lcm_left (x_seq m) (m + 1)
  have h_lcm_div : Nat.lcm (x_seq m) (m + 1) / x_seq m = (m + 1) / Nat.gcd (x_seq m) (m + 1) :=
    lcm_div_self_eq (x_seq m) (m + 1) h_pos
  have h_def : x_seq (m + 1) = 2 * x_seq m + Nat.lcm (x_seq m) (m + 1) := by
    cases m with
    | zero => contradiction
    | succ m => rfl
  rw [h_def]
  generalize hD : (m + 1) / Nat.gcd (x_seq m) (m + 1) = D
  have h_lcm_eq : Nat.lcm (x_seq m) (m + 1) = x_seq m * D := by
    rw [← hD]
    rw [← h_lcm_div]
    exact (Nat.mul_div_cancel' h_dvd_lcm).symm
  rw [h_lcm_eq]
  ring

lemma minfac_sq_le_of_composite (M : ℕ) (hM : M > 0) (h_comp : ¬ Nat.Prime M) :
    Nat.minFac M * Nat.minFac M ≤ M := by
  have h_le := Nat.minFac_le_div hM h_comp
  have h_dvd := Nat.minFac_dvd M
  have h_cancel := Nat.mul_div_cancel' h_dvd
  have h_mul_le : Nat.minFac M * Nat.minFac M ≤ Nat.minFac M * (M / Nat.minFac M) := by
    exact Nat.mul_le_mul_left (Nat.minFac M) h_le
  rw [h_cancel] at h_mul_le
  exact h_mul_le

lemma prime_of_smallest_prime_factor (M : ℕ) (hM : M ≥ 2)
    (h : Nat.minFac M = M) : Nat.Prime M := by
  have h_ne : M ≠ 1 := by omega
  have h_prime := Nat.minFac_prime h_ne
  rw [h] at h_prime
  exact h_prime

lemma prime_triplet_contradiction (q : ℕ) (hq : Nat.Prime q) (hq2 : Nat.Prime (q - 2)) (hq4 : Nat.Prime (q - 4)) (hq_ge : q ≥ 13) : False := by
  have h_mod3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h_mod3 with h0 | h1 | h2
  · have h_dvd : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
    have h_eq : q = 3 := by
      cases Nat.Prime.eq_one_or_self_of_dvd hq 3 h_dvd with
      | inl h_one => contradiction
      | inr h_self => exact h_self.symm
    omega
  · have h_dvd : 3 ∣ q - 4 := by
      have : (q - 4) % 3 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have h_eq : q - 4 = 3 := by
      cases Nat.Prime.eq_one_or_self_of_dvd hq4 3 h_dvd with
      | inl h_one => contradiction
      | inr h_self => exact h_self.symm
    omega
  · have h_dvd : 3 ∣ q - 2 := by
      have : (q - 2) % 3 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have h_eq : q - 2 = 3 := by
      cases Nat.Prime.eq_one_or_self_of_dvd hq2 3 h_dvd with
      | inl h_one => contradiction
      | inr h_self => exact h_self.symm
    omega

def x_seq_loop : ℕ → ℕ → ℕ → ℕ
| 0, _, x => x
| n + 1, i, x => x_seq_loop n (i + 1) (2 * x + Nat.lcm x i)

def x_seq_tr (n : ℕ) : ℕ :=
  if n = 0 then 0
  else x_seq_loop (n - 1) 2 1

lemma x_seq_step (n : ℕ) (hn : n ≥ 1) :
    x_seq (n + 1) = 2 * x_seq n + Nat.lcm (x_seq n) (n + 1) := by
  cases n with
  | zero => contradiction
  | succ n => rfl

lemma x_seq_loop_eq (k n : ℕ) (hn : n ≥ 1) :
    x_seq_loop k (n + 1) (x_seq n) = x_seq (n + k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp [x_seq_loop]
    rw [← x_seq_step n hn]
    have ih' := ih (n + 1) (by omega)
    rw [ih']
    have : n + 1 + k = n + (k + 1) := by omega
    rw [this]

lemma x_seq_tr_eq (n : ℕ) : x_seq_tr n = x_seq n := by
  unfold x_seq_tr
  split_ifs with h
  · rw [h]; rfl
  · have hn : n ≥ 1 := by omega
    have h_loop := x_seq_loop_eq (n - 1) 1 (by decide)
    simp at h_loop
    have h_eq : x_seq_loop (n - 1) 2 1 = x_seq_loop (n - 1) 2 (x_seq 1) := rfl
    rw [h_eq]
    rw [h_loop]
    have : 1 + (n - 1) = n := by omega
    rw [this]

lemma q_dvd_x_seq_q_sq_small (q : ℕ) (hq : Nat.Prime q) (hq_le : q ≤ 283) : q ∣ x_seq (q * q - 1) := by
  interval_cases q
{cases_str}

lemma q_dvd_x_seq_q_sq (q : ℕ) (hq : Nat.Prime q) : q ∣ x_seq (q * q - 1) := by
  by_cases h : q ≤ 283
  · exact q_dvd_x_seq_q_sq_small q hq h
  · sorry

lemma prime_of_prime_factor (p : ℕ) (hp : Nat.Prime p) (h_div : p ∣ x_seq (p - 1)) : Nat.Prime (p - 2) := by
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have hp5 : p ≥ 5 := by
    by_contra h_lt
    have : p < 5 := by omega
    interval_cases p
    · have h_f : ¬ (2 ∣ x_seq 1) := by decide
      contradiction
    · have h_f : ¬ (3 ∣ x_seq 2) := by decide
      contradiction
    · have : ¬ Nat.Prime 4 := by decide
      contradiction
  have hp1 : p - 1 > 0 := by omega
  have h_ex : ∃ k, k > 0 ∧ p ∣ x_seq k := ⟨p - 1, hp1, h_div⟩
  let k := Nat.find h_ex
  have hk_pos : k > 0 := (Nat.find_spec h_ex).1
  have hk_dvd : p ∣ x_seq k := (Nat.find_spec h_ex).2
  have hk_min : ∀ m < k, m > 0 → ¬ (p ∣ x_seq m) := by
    intro m hm hm_pos h_m_dvd
    have : m > 0 ∧ p ∣ x_seq m := ⟨hm_pos, h_m_dvd⟩
    have : k ≤ m := Nat.find_le this
    omega
  have hk_ge_2 : k ≥ 2 := by
    by_contra h_lt
    have hk_eq : k = 1 := by omega
    have : x_seq 1 = 1 := rfl
    rw [hk_eq] at hk_dvd
    rw [this] at hk_dvd
    have : p ≤ 1 := Nat.le_of_dvd (by decide) hk_dvd
    omega
  let m := k - 1
  have hm_eq : k = m + 1 := (Nat.sub_add_cancel (by omega)).symm
  have hm_ge_1 : m ≥ 1 := by omega
  have h_not_dvd_m : ¬ (p ∣ x_seq m) := by
    apply hk_min m (by omega) (by omega)
  have h_dvd_m1 : p ∣ x_seq (m + 1) := by
    rw [← hm_eq]
    exact hk_dvd
  have h_fac := factor_lemma m hm_ge_1
  have h_dvd_factor : p ∣ 2 + (m + 1) / Nat.gcd (x_seq m) (m + 1) := by
    rw [h_fac] at h_dvd_m1
    exact (Nat.Prime.dvd_mul hp).mp h_dvd_m1 |>.resolve_left h_not_dvd_m
  generalize hd : (m + 1) / Nat.gcd (x_seq m) (m + 1) = d
  rw [hd] at h_dvd_factor
  have hd_pos : 2 + d > 0 := by omega
  have hp_le : p ≤ 2 + d := Nat.le_of_dvd hd_pos h_dvd_factor
  have hk_le : k ≤ p - 1 := by
    have : p - 1 > 0 ∧ p ∣ x_seq (p - 1) := ⟨hp1, h_div⟩
    exact Nat.find_le this
  have hm_le : m ≤ p - 2 := by clear hd hd_pos hp_le h_dvd_factor; omega
  have hd_le : d ≤ m + 1 := by
    rw [← hd]
    exact Nat.div_le_self (m + 1) (Nat.gcd (x_seq m) (m + 1))
  have h_bound : 2 + d ≤ p + 1 := by clear hd hd_pos hp_le h_dvd_factor; omega
  have hd_eq : 2 + d = p := by
    have h_dvd_eq : ∃ c, 2 + d = p * c := h_dvd_factor
    rcases h_dvd_eq with ⟨c, hc⟩
    have hc_cases : c = 0 ∨ c = 1 ∨ c ≥ 2 := by clear hd hd_pos hp_le h_dvd_factor; omega
    rcases hc_cases with rfl | rfl | hc2
    · simp [mul_zero] at hc
    · simp [mul_one] at hc
      exact hc
    · have h_mul_le : p * 2 ≤ p * c := Nat.mul_le_mul_left p hc2
      rw [← hc] at h_mul_le
      have : p * 2 = p + p := by ring
      rw [this] at h_mul_le
      clear hd hd_pos hp_le h_dvd_factor; omega
  have hd_val : d = p - 2 := by
    revert hd_eq
    clear hd h_fac h_dvd_factor h_dvd_m1 h_not_dvd_m hm_ge_1 hm_eq m hk_ge_2 hk_min hk_dvd hk_pos k h_ex hm_le hd_le hk_le h_bound
    intro hd_eq_d
    omega
  have h_gcd_dvd : Nat.gcd (x_seq m) (m + 1) ∣ m + 1 := Nat.gcd_dvd_right (x_seq m) (m + 1)
  have hm1_eq : m + 1 = Nat.gcd (x_seq m) (m + 1) * d := by
    rw [← hd]
    exact (Nat.mul_div_cancel' h_gcd_dvd).symm
  have h_gcd_eq_1 : Nat.gcd (x_seq m) (m + 1) = 1 := by
    by_contra h_ne_1
    have h_gcd_ge_2 : Nat.gcd (x_seq m) (m + 1) ≥ 2 := by
      have : Nat.gcd (x_seq m) (m + 1) > 0 := Nat.gcd_pos_of_pos_right (x_seq m) (by omega)
      omega
    have : m + 1 ≥ 2 * (p - 2) := by
      rw [hm1_eq]
      rw [hd_val]
      have : p - 2 > 0 := by omega
      nlinarith
    omega
  have h_gcd_final : Nat.gcd (x_seq (p - 3)) (p - 2) = 1 := by
    have hm_val : m = p - 3 := by
      rw [h_gcd_eq_1] at hm1_eq
      rw [Nat.one_mul] at hm1_eq
      rw [hd_val] at hm1_eq
      omega
    have h_cancel2 : p - 3 + 1 = p - 2 := by omega
    rw [hm_val] at h_gcd_eq_1
    rw [h_cancel2] at h_gcd_eq_1
    exact h_gcd_eq_1
  have h_M_ge_2 : p - 2 ≥ 2 := by omega
  apply prime_of_smallest_prime_factor (p - 2) h_M_ge_2
  by_contra h_ne
  have h_comp : ¬ Nat.Prime (p - 2) := by
    intro h_pr
    have : Nat.minFac (p - 2) = p - 2 := (prime_def_minFac.1 h_pr).2
    exact h_ne this
  generalize hq : Nat.minFac (p - 2) = q
  have h_comp' : ¬ Nat.Prime (p - 2) := h_comp
  have h_pos_M : p - 2 > 0 := by omega
  have h_le_M := minfac_sq_le_of_composite (p - 2) h_pos_M h_comp'
  rw [hq] at h_le_M
  have hq_prime : Nat.Prime q := by
    rw [← hq]
    exact Nat.minFac_prime (by omega)
  have h_dvd_q_sq := q_dvd_x_seq_q_sq q hq_prime
  generalize hX : q * q = X
  rw [hX] at h_le_M
  have h_le_p3 : X - 1 ≤ p - 3 := by omega
  have hq_pos : q > 0 := Nat.Prime.pos hq_prime
  have h_dvd_x_seq_p3 : q ∣ x_seq (p - 3) := by
    have h_q_sq : q * q ≥ 4 := by
      have : q ≥ 2 := Nat.Prime.two_le hq_prime
      nlinarith
    have h_le_pos : q * q - 1 > 0 := by omega
    have h_le : q * q - 1 ≤ p - 3 := by
      rw [hX]
      exact h_le_p3
    have h_dvd_le := x_seq_dvd_x_seq_of_le h_le_pos h_le
    exact Nat.dvd_trans h_dvd_q_sq h_dvd_le
  have h_dvd_M : q ∣ p - 2 := by
    rw [← hq]
    exact Nat.minFac_dvd (p - 2)
  have h_dvd_gcd : q ∣ Nat.gcd (x_seq (p - 3)) (p - 2) := Nat.dvd_gcd h_dvd_x_seq_p3 h_dvd_M
  rw [h_gcd_final] at h_dvd_gcd
  have : q ≤ 1 := Nat.le_of_dvd (by decide) h_dvd_gcd
  have : q ≥ 2 := Nat.Prime.two_le hq_prime
  omega

theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  intro p hp h_np2
  rw [A135508_p_eq p hp]
  rw [lcm_div_self_eq (x_seq (p - 1)) p (x_seq_pos (p - 1) (by
    have : p ≥ 2 := Nat.Prime.two_le hp
    omega))]
  have h_gcd : Nat.gcd (x_seq (p - 1)) p = 1 := by
    have h_dvd : Nat.gcd (x_seq (p - 1)) p ∣ p := Nat.gcd_dvd_right (x_seq (p - 1)) p
    have h_divs : Nat.gcd (x_seq (p - 1)) p = 1 ∨ Nat.gcd (x_seq (p - 1)) p = p := by
      exact Nat.Prime.eq_one_or_self_of_dvd hp _ h_dvd
    rcases h_divs with h1 | hp1
    · exact h1
    · have h_div_p : p ∣ x_seq (p - 1) := by
        have : Nat.gcd (x_seq (p - 1)) p ∣ x_seq (p - 1) := Nat.gcd_dvd_left (x_seq (p - 1)) p
        rw [hp1] at this
        exact this
      have h_prime_p2 : Nat.Prime (p - 2) := prime_of_prime_factor p hp h_div_p
      contradiction
  rw [h_gcd]
  exact Nat.div_one p
'''

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(spec_template)
print("Wrote Spec.lean")
