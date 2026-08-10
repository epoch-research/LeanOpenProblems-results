import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

/--
A228304: The sequence $a(n)$ is defined by the alternating sum of fourth powers of binomial coefficients.
$$a(n) = \sum_{k=0}^n \binom{n}{k}^4 (-1)^k$$
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

/--
A228304 c(n) sequence:
$$c(n) = \sum_{k=0}^n (-1)^k \binom{n}{k}^2 \binom{2k}{k} \binom{2(n-k)}{n-k}$$
-/
def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

/--
Proof of the congruence of binomial coefficients modulo $p$.
For primes $p$, if $p \le n < 2p$ and $k \le n$, we show that $\binom{n}{k} \equiv \binom{n \pmod p}{k \pmod p} \pmod p$.
-/
lemma choose_congr_mod (p n k : ℕ) [Fact p.Prime] (hpn : p ≤ n) (hn2p : n < 2 * p) (hkn : k ≤ n) :
    choose n k ≡ choose (n % p) (k % p) [ZMOD p] := by
  have hp_prime : p.Prime := Fact.out
  have hp_pos : p > 0 := hp_prime.pos
  have h1 : choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [ZMOD p] :=
    Choose.choose_modEq_choose_mod_mul_choose_div
  have h_div : n / p = 1 := by
    have h_eq := (Nat.div_add_mod' n p).symm
    have h_mod := Nat.mod_lt n hp_pos
    rcases h_div_cases : n / p with _ | _ | k
    · rw [h_div_cases] at h_eq; omega
    · rfl
    · rw [h_div_cases] at h_eq
      have h_ineq : (k + 1 + 1) * p ≥ 2 * p := by rw [add_mul, add_mul, one_mul]; omega
      omega
  have h_k : k / p = 0 ∨ k / p = 1 := by
    have h_eq := (Nat.div_add_mod' k p).symm
    have h_mod := Nat.mod_lt k hp_pos
    rcases h_div_cases : k / p with _ | _ | j
    · left; rfl
    · right; rfl
    · rw [h_div_cases] at h_eq
      have h_ineq : (j + 1 + 1) * p ≥ 2 * p := by rw [add_mul, add_mul, one_mul]; omega
      omega
  have h_choose : choose (n / p) (k / p) = 1 := by
    rw [h_div]
    rcases h_k with hk | hk
    · rw [hk, choose_zero_right]
    · rw [hk, choose_self]
  have h2 : ((choose (n % p) (k % p) * choose (n / p) (k / p) : ℕ) : ℤ) = (choose (n % p) (k % p) : ℤ) := by
    rw [h_choose, mul_one]
  rw [show (choose (n % p) (k % p) * choose (n / p) (k / p) : ℤ) = ((choose (n % p) (k % p) * choose (n / p) (k / p) : ℕ) : ℤ) by rfl] at h1
  rw [h2] at h1
  exact h1

lemma choose_pow_congr_mod (p n k : ℕ) [Fact p.Prime] (hpn : p ≤ n) (hn2p : n < 2 * p) (hkn : k ≤ n) :
    (choose n k : ℤ)^4 ≡ (choose (n % p) (k % p) : ℤ)^4 [ZMOD p] :=
  Int.ModEq.pow 4 (choose_congr_mod p n k hpn hn2p hkn)

lemma choose_cast_congr (p n k : ℕ) [Fact p.Prime] (hpn : p ≤ n) (hn2p : n < 2 * p) (hkn : k ≤ n) :
    (choose n k : ZMod p) = (choose (n % p) (k % p) : ZMod p) := by
  have h := choose_congr_mod p n k hpn hn2p hkn
  have h_eq := (ZMod.intCast_eq_intCast_iff (choose n k) (choose (n % p) (k % p)) p).mpr h
  exact_mod_cast h_eq

lemma a_cast_eq (p n : ℕ) :
    ((a n : ℤ) : ZMod p) = ∑ k ∈ range (n + 1), (-1 : ZMod p)^k * (choose n k : ZMod p)^4 := by
  simp [a]

lemma a_eq_zero_of_range (p n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpn : p ≤ n) (hn2p : n < 2 * p) :
    ((a n : ℤ) : ZMod p) = 0 := by
  have hp : p.Prime := Fact.out
  have hp_pos : p > 0 := hp.pos
  have h_r : n - p < p := by omega
  let r := n - p
  have h_n_eq : n = p + r := by omega
  have h_sum := a_cast_eq p n
  rw [h_sum]
  have h_split : n + 1 = p + (r + 1) := by omega
  rw [h_split, sum_range_add]
  have h_r1 : r + 1 ≤ p := by omega
  have h_sub : range (r + 1) ⊆ range p := range_subset_range.mpr h_r1
  have h_sum_sdiff : ∑ x ∈ range p, ((-1 : ZMod p) ^ x * (choose n x : ZMod p) ^ 4) =
      ∑ x ∈ range (r + 1), ((-1 : ZMod p) ^ x * (choose n x : ZMod p) ^ 4) +
      ∑ x ∈ (range p \ range (r + 1)), ((-1 : ZMod p) ^ x * (choose n x : ZMod p) ^ 4) := by
    rw [← sum_sdiff h_sub, add_comm]
  have h_sum_sdiff_zero : ∑ x ∈ (range p \ range (r + 1)), ((-1 : ZMod p) ^ x * (choose n x : ZMod p) ^ 4) = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_sdiff, mem_range, mem_range] at hx
    have h_x_le_n : x ≤ n := by omega
    have h_choose_cast : (choose n x : ZMod p) = (choose (n % p) (x % p) : ZMod p) :=
      choose_cast_congr p n x hpn hn2p h_x_le_n
    have h_mod_n : n % p = r := by
      rw [h_n_eq, Nat.add_comm]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt h_r
    have h_mod_x : x % p = x := Nat.mod_eq_of_lt (by omega)
    rw [h_mod_n, h_mod_x] at h_choose_cast
    have h_choose_zero : choose r x = 0 := choose_eq_zero_of_lt (by omega)
    rw [h_choose_zero, Nat.cast_zero] at h_choose_cast
    rw [h_choose_cast]
    ring
  rw [h_sum_sdiff_zero, add_zero] at h_sum_sdiff
  have h_sum1_eq : ∑ x ∈ range (r + 1), ((-1 : ZMod p) ^ x * (choose n x : ZMod p) ^ 4) =
      ∑ x ∈ range (r + 1), ((-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 4) := by
    apply sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    have h_x_le_n : x ≤ n := by omega
    have h_choose_cast : (choose n x : ZMod p) = (choose (n % p) (x % p) : ZMod p) :=
      choose_cast_congr p n x hpn hn2p h_x_le_n
    have h_mod_n : n % p = r := by
      rw [h_n_eq, Nat.add_comm]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt h_r
    have h_mod_x : x % p = x := Nat.mod_eq_of_lt (by omega)
    rw [h_mod_n, h_mod_x] at h_choose_cast
    rw [h_choose_cast]
  rw [h_sum_sdiff, h_sum1_eq]
  have h_sum2_eq : ∑ x ∈ range (r + 1), ((-1 : ZMod p) ^ (p + x) * (choose n (p + x) : ZMod p) ^ 4) =
      ∑ x ∈ range (r + 1), -((-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 4) := by
    apply sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    have h_x_le_n : p + x ≤ n := by omega
    have h_choose_cast : (choose n (p + x) : ZMod p) = (choose (n % p) ((p + x) % p) : ZMod p) :=
      choose_cast_congr p n (p + x) hpn hn2p h_x_le_n
    have h_mod_n : n % p = r := by
      rw [h_n_eq, Nat.add_comm]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt h_r
    have h_mod_x : (p + x) % p = x := by
      rw [Nat.add_comm]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_mod_n, h_mod_x] at h_choose_cast
    have h_pow : (-1 : ZMod p) ^ (p + x) = - (-1 : ZMod p) ^ x := by
      rw [pow_add, Odd.neg_one_pow (Nat.Prime.odd_of_ne_two hp hp2)]
      ring
    rw [h_choose_cast, h_pow]
    ring
  rw [h_sum2_eq, ← sum_add_distrib]
  apply sum_eq_zero
  intro x _
  ring

lemma choose_two_p_add (p y : ℕ) [Fact p.Prime] (hy : y < p) :
    (choose (2 * (p + y)) (p + y) : ZMod p) = ((choose (2 * y) y * (2 + 2 * y / p) : ℕ) : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hp_pos : p > 0 := hp.pos
  have h_div : (2 * (p + y)) / p = 2 * y / p + 2 := by
    have h1 : 2 * (p + y) = 2 * y + 2 * p := by ring
    rw [h1, Nat.add_mul_div_right (2 * y) 2 hp_pos]
  have h_mod : (2 * (p + y)) % p = (2 * y) % p := by
    have h1 : 2 * (p + y) = 2 * y + p * 2 := by ring
    rw [h1, Nat.add_mul_mod_self_left (2 * y) p 2]
  have h_B_div : (p + y) / p = 1 := by
    have h1 : p + y = y + 1 * p := by ring
    rw [h1, Nat.add_mul_div_right y 1 hp_pos]
    have h2 : y / p = 0 := Nat.div_eq_of_lt hy
    rw [h2, zero_add]
  have h_B_mod : (p + y) % p = y := by
    have h1 : p + y = y + p * 1 := by ring
    rw [h1, Nat.add_mul_mod_self_left y p 1]
    exact Nat.mod_eq_of_lt hy
  have h_lucas := Choose.choose_modEq_choose_mod_mul_choose_div (p := p) (n := 2 * (p + y)) (k := p + y)
  have h_cast : (choose (2 * (p + y)) (p + y) : ZMod p) = (choose ((2 * (p + y)) % p) ((p + y) % p) : ZMod p) * (choose ((2 * (p + y)) / p) ((p + y) / p) : ZMod p) := by
    have h_eq := (ZMod.intCast_eq_intCast_iff (choose (2 * (p + y)) (p + y)) (choose ((2 * (p + y)) % p) ((p + y) % p) * choose ((2 * (p + y)) / p) ((p + y) / p)) p).mpr h_lucas
    exact_mod_cast h_eq
  rw [h_mod, h_B_mod, h_div, h_B_div] at h_cast
  rw [h_cast]
  have h_choose_1 : choose (2 * y / p + 2) 1 = 2 * y / p + 2 := choose_one_right (2 * y / p + 2)
  have h_lucas_2 := Choose.choose_modEq_choose_mod_mul_choose_div (p := p) (n := 2 * y) (k := y)
  have h_cast_2 : (choose (2 * y) y : ZMod p) = (choose ((2 * y) % p) (y % p) : ZMod p) * (choose ((2 * y) / p) (y / p) : ZMod p) := by
    have h_eq := (ZMod.intCast_eq_intCast_iff (choose (2 * y) y) (choose ((2 * y) % p) (y % p) * choose ((2 * y) / p) (y / p)) p).mpr h_lucas_2
    exact_mod_cast h_eq
  have h_y_mod : y % p = y := Nat.mod_eq_of_lt hy
  have h_y_div : y / p = 0 := Nat.div_eq_of_lt hy
  rw [h_y_mod, h_y_div, choose_zero_right, Nat.cast_one, mul_one] at h_cast_2
  rw [h_choose_1]
  rw [show ((2 * y / p + 2 : ℕ) : ZMod p) = ((2 + 2 * y / p : ℕ) : ZMod p) by rw [add_comm]]
  rw [show ((choose (2 * y) y * (2 + 2 * y / p) : ℕ) : ZMod p) = (choose (2 * y) y : ZMod p) * ((2 + 2 * y / p : ℕ) : ZMod p) by push_cast; rfl]
  rw [h_cast_2]

lemma choose_mul_symmetric (p x y : ℕ) [Fact p.Prime] (hx : x < p) (hy : y < p) (hxy : x + y < p) :
    (choose (2 * x) x : ZMod p) * choose (2 * (p + y)) (p + y) = choose (2 * (p + x)) (p + x) * choose (2 * y) y := by
  have hp : p.Prime := Fact.out
  have hp_pos : p > 0 := hp.pos
  rw [choose_two_p_add p y hy]
  rw [choose_two_p_add p x hx]
  rw [show ((choose (2 * y) y * (2 + 2 * y / p) : ℕ) : ZMod p) = (choose (2 * y) y : ZMod p) * ((2 + 2 * y / p : ℕ) : ZMod p) by push_cast; rfl]
  rw [show ((choose (2 * x) x * (2 + 2 * x / p) : ℕ) : ZMod p) = (choose (2 * x) x : ZMod p) * ((2 + 2 * x / p : ℕ) : ZMod p) by push_cast; rfl]
  have h_cases : 2 * x < p ∨ 2 * y < p := by omega
  rcases h_cases with h_x | h_y
  · have h_x_div : 2 * x / p = 0 := Nat.div_eq_of_lt h_x
    by_cases h_y : 2 * y < p
    · have h_y_div : 2 * y / p = 0 := Nat.div_eq_of_lt h_y
      rw [h_x_div, h_y_div]
      ring
    · have h_choose : (choose (2 * y) y : ZMod p) = 0 := by
        have h_lucas := Choose.choose_modEq_choose_mod_mul_choose_div (p := p) (n := 2 * y) (k := y)
        have h_cast : (choose (2 * y) y : ZMod p) = (choose ((2 * y) % p) (y % p) : ZMod p) * (choose ((2 * y) / p) (y / p) : ZMod p) := by
          have h_eq := (ZMod.intCast_eq_intCast_iff (choose (2 * y) y) (choose ((2 * y) % p) (y % p) * choose ((2 * y) / p) (y / p)) p).mpr h_lucas
          exact_mod_cast h_eq
        have h_y_mod : y % p = y := Nat.mod_eq_of_lt hy
        have h_y_div : y / p = 0 := Nat.div_eq_of_lt hy
        rw [h_y_mod, h_y_div, choose_zero_right, Nat.cast_one, mul_one] at h_cast
        have h_mod_lt : (2 * y) % p < y := by
          have h_eq := (Nat.div_add_mod (2 * y) p).symm
          have h_mod_lt_p := Nat.mod_lt (2 * y) hp_pos
          rcases h_div : (2 * y) / p with _ | _ | k
          · rw [h_div] at h_eq; omega
          · rw [h_div] at h_eq; omega
          · rw [h_div] at h_eq
            have h_ineq : p * (k + 1 + 1) ≥ 2 * p := by
              have h_k : k + 1 + 1 ≥ 2 := by omega
              rw [mul_comm 2 p]
              exact Nat.mul_le_mul_left p h_k
            omega
        have h_choose_zero : choose ((2 * y) % p) y = 0 := choose_eq_zero_of_lt h_mod_lt
        rw [h_choose_zero, Nat.cast_zero] at h_cast
        exact h_cast
      rw [h_choose]
      ring
  · have h_y_div : 2 * y / p = 0 := Nat.div_eq_of_lt h_y
    by_cases h_x : 2 * x < p
    · have h_x_div : 2 * x / p = 0 := Nat.div_eq_of_lt h_x
      rw [h_x_div, h_y_div]
      ring
    · have h_choose : (choose (2 * x) x : ZMod p) = 0 := by
        have h_lucas := Choose.choose_modEq_choose_mod_mul_choose_div (p := p) (n := 2 * x) (k := x)
        have h_cast : (choose (2 * x) x : ZMod p) = (choose ((2 * x) % p) (x % p) : ZMod p) * (choose ((2 * x) / p) (x / p) : ZMod p) := by
          have h_eq := (ZMod.intCast_eq_intCast_iff (choose (2 * x) x) (choose ((2 * x) % p) (x % p) * choose ((2 * x) / p) (x / p)) p).mpr h_lucas
          exact_mod_cast h_eq
        have h_x_mod : x % p = x := Nat.mod_eq_of_lt hx
        have h_x_div : x / p = 0 := Nat.div_eq_of_lt hx
        rw [h_x_mod, h_x_div, choose_zero_right, Nat.cast_one, mul_one] at h_cast
        have h_mod_lt : (2 * x) % p < x := by
          have h_eq := (Nat.div_add_mod (2 * x) p).symm
          have h_mod_lt_p := Nat.mod_lt (2 * x) hp_pos
          rcases h_div : (2 * x) / p with _ | _ | k
          · rw [h_div] at h_eq; omega
          · rw [h_div] at h_eq; omega
          · rw [h_div] at h_eq
            have h_ineq : p * (k + 1 + 1) ≥ 2 * p := by
              have h_k : k + 1 + 1 ≥ 2 := by omega
              rw [mul_comm 2 p]
              exact Nat.mul_le_mul_left p h_k
            omega
        have h_choose_zero : choose ((2 * x) % p) x = 0 := choose_eq_zero_of_lt h_mod_lt
        rw [h_choose_zero, Nat.cast_zero] at h_cast
        exact h_cast
      rw [h_choose]
      ring

lemma c_cast_eq (p n : ℕ) :
    ((c n : ℤ) : ZMod p) = ∑ k ∈ range (n + 1), (-1 : ZMod p)^k * (choose n k : ZMod p)^2 * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p) := by
  simp [c]

lemma c_eq_zero_of_range (p n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpn : p ≤ n) (hn2p : n < 2 * p) :
    ((c n : ℤ) : ZMod p) = 0 := by
  have hp : p.Prime := Fact.out
  have hp_pos : p > 0 := hp.pos
  have h_r : n - p < p := by omega
  let r := n - p
  have h_n_eq : n = p + r := by omega
  have h_sum := c_cast_eq p n
  rw [h_sum]
  have h_split : n + 1 = p + (r + 1) := by omega
  rw [h_split, sum_range_add]
  have h_r1 : r + 1 ≤ p := by omega
  have h_sub : range (r + 1) ⊆ range p := range_subset_range.mpr h_r1
  have h_sum_sdiff : ∑ x ∈ range p, ((-1 : ZMod p) ^ x * (choose n x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (n - x)) (n - x) : ZMod p)) =
      ∑ x ∈ range (r + 1), ((-1 : ZMod p) ^ x * (choose n x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (n - x)) (n - x) : ZMod p)) +
      ∑ x ∈ (range p \ range (r + 1)), ((-1 : ZMod p) ^ x * (choose n x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (n - x)) (n - x) : ZMod p)) := by
    rw [← sum_sdiff h_sub, add_comm]
  have h_sum_sdiff_zero : ∑ x ∈ (range p \ range (r + 1)), ((-1 : ZMod p) ^ x * (choose n x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (n - x)) (n - x) : ZMod p)) = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_sdiff, mem_range, mem_range] at hx
    have h_x_le_n : x ≤ n := by omega
    have h_choose_cast : (choose n x : ZMod p) = (choose (n % p) (x % p) : ZMod p) :=
      choose_cast_congr p n x hpn hn2p h_x_le_n
    have h_mod_n : n % p = r := by
      rw [h_n_eq, add_comm]
      have h1 : (r + p) % p = (r + p * 1) % p := by ring_nf
      rw [h1, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt h_r
    have h_mod_x : x % p = x := Nat.mod_eq_of_lt hx.1
    rw [h_mod_n, h_mod_x] at h_choose_cast
    have h_choose_zero : choose r x = 0 := choose_eq_zero_of_lt (by omega)
    rw [h_choose_zero, Nat.cast_zero] at h_choose_cast
    rw [h_choose_cast]
    ring
  rw [h_sum_sdiff_zero, add_zero] at h_sum_sdiff
  have h_sum1_eq : ∑ x ∈ range (r + 1), ((-1 : ZMod p) ^ x * (choose n x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (n - x)) (n - x) : ZMod p)) =
      ∑ x ∈ range (r + 1), ((-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (n - x)) (n - x) : ZMod p)) := by
    apply sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    have h_x_le_n : x ≤ n := by omega
    have h_choose_cast : (choose n x : ZMod p) = (choose (n % p) (x % p) : ZMod p) :=
      choose_cast_congr p n x hpn hn2p h_x_le_n
    have h_mod_n : n % p = r := by
      rw [h_n_eq, add_comm]
      have h1 : (r + p) % p = (r + p * 1) % p := by ring_nf
      rw [h1, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt h_r
    have h_mod_x : x % p = x := Nat.mod_eq_of_lt (by omega)
    rw [h_mod_n, h_mod_x] at h_choose_cast
    rw [h_choose_cast]
  rw [h_sum_sdiff, h_sum1_eq]
  have h_sum2_eq : ∑ x ∈ range (r + 1), ((-1 : ZMod p) ^ (p + x) * (choose n (p + x) : ZMod p) ^ 2 * (choose (2 * (p + x)) (p + x) : ZMod p) * (choose (2 * (n - (p + x))) (n - (p + x)) : ZMod p)) =
      ∑ x ∈ range (r + 1), -((-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (n - x)) (n - x) : ZMod p)) := by
    apply sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    have h_x_le_n : p + x ≤ n := by omega
    have h_choose_cast : (choose n (p + x) : ZMod p) = (choose (n % p) ((p + x) % p) : ZMod p) :=
      choose_cast_congr p n (p + x) hpn hn2p h_x_le_n
    have h_mod_n : n % p = r := by
      rw [h_n_eq, add_comm]
      have h1 : (r + p) % p = (r + p * 1) % p := by ring_nf
      rw [h1, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt h_r
    have h_mod_x : (p + x) % p = x := by
      rw [add_comm]
      have h1 : (x + p) % p = (x + p * 1) % p := by ring_nf
      rw [h1, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_mod_n, h_mod_x] at h_choose_cast
    have h_pow : (-1 : ZMod p) ^ (p + x) = - (-1 : ZMod p) ^ x := by
      rw [pow_add, Odd.neg_one_pow (Nat.Prime.odd_of_ne_two hp hp2)]
      ring
    have h_sub_eq : n - (p + x) = r - x := by omega
    have h_n_sub_x : n - x = p + (r - x) := by omega
    have h_symm := choose_mul_symmetric p x (r - x) (by omega) (by omega) (by omega)
    rw [h_sub_eq]
    rw [← h_n_sub_x] at h_symm
    rw [h_pow, h_choose_cast]
    have h_lhs : -(-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 2 * (choose (2 * (p + x)) (p + x) : ZMod p) * (choose (2 * (r - x)) (r - x) : ZMod p) =
        - ( (-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 2 * ((choose (2 * (p + x)) (p + x) : ZMod p) * (choose (2 * (r - x)) (r - x) : ZMod p)) ) := by ring
    rw [h_lhs, ← h_symm]
    ring
  rw [h_sum2_eq, ← sum_add_distrib]
  apply sum_eq_zero
  intro x _
  ring

lemma choose_p_minus_one_cast (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    (choose (p - 1) k : ZMod p) = (-1)^k := by
  induction' k with k ih
  · rw [choose_zero_right, pow_zero, Nat.cast_one]
  · have h_succ : k < p := by omega
    have h_succ_2 : k + 1 < p := hk
    have h_ih := ih h_succ
    have h_eq := Nat.choose_succ_right_eq (p - 1) k
    have h_cast : ((choose (p - 1) (k + 1) : ZMod p)) * ((k + 1 : ℕ) : ZMod p) = ((choose (p - 1) k : ZMod p)) * (((p - 1 - k : ℕ) : ZMod p)) := by
      have h_eq' : (((choose (p - 1) (k + 1) * (k + 1) : ℕ) : ZMod p)) = (((choose (p - 1) k * (p - 1 - k) : ℕ) : ZMod p)) := by rw [h_eq]
      exact_mod_cast h_eq'
    have h_sub : ((p - 1 - k : ℕ) : ZMod p) = - ((k + 1 : ℕ) : ZMod p) := by
      have h_eq2 : p - 1 - k = p - (k + 1) := by omega
      rw [h_eq2]
      have h_add : ((p - (k + 1) : ℕ) : ZMod p) + ((k + 1 : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
        exact ZMod.natCast_self p
      exact add_eq_zero_iff_eq_neg.mp h_add
    rw [h_sub] at h_cast
    have h_cast2 : ((choose (p - 1) (k + 1) : ZMod p)) * ((k + 1 : ℕ) : ZMod p) = - ((choose (p - 1) k : ZMod p)) * ((k + 1 : ℕ) : ZMod p) := by
      rw [h_cast]
      ring
    have h_nz : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      have h_le := Nat.le_of_dvd (by omega) h
      omega
    have h_eq_final := mul_right_cancel₀ h_nz h_cast2
    rw [h_eq_final, h_ih, pow_succ]
    ring

lemma sum_neg_one_pow_two_mul (m : ℕ) (R : Type*) [CommRing R] :
    ∑ k ∈ range (2 * m), (-1 : R)^k = 0 := by
  induction' m with m ih
  · rw [mul_zero, range_zero, sum_empty]
  · have h_step : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [h_step, sum_range_add, ih, zero_add]
    have h_two : range 2 = {0, 1} := by decide
    rw [h_two, sum_insert (by decide), sum_singleton]
    ring

lemma sum_neg_one_pow_odd (p : ℕ) (R : Type*) [CommRing R] (hp : Odd p) :
    ∑ k ∈ range p, (-1 : R)^k = 1 := by
  rcases hp with ⟨m, rfl⟩
  have h_split : 2 * m + 1 = 2 * m + 1 := rfl
  rw [h_split, sum_range_succ, sum_neg_one_pow_two_mul]
  rw [show (-1 : R)^(2 * m) = ((-1 : R)^2)^m by rw [pow_mul]]
  ring

lemma choose_two_k_k_zero (p k : ℕ) [Fact p.Prime] (hk1 : k < p) (hk2 : 2 * k ≥ p) :
    (choose (2 * k) k : ZMod p) = 0 := by
  have hp : p.Prime := Fact.out
  have hp_pos : p > 0 := hp.pos
  have h_lucas := Choose.choose_modEq_choose_mod_mul_choose_div (p := p) (n := 2 * k) (k := k)
  have h_cast : (choose (2 * k) k : ZMod p) = (choose ((2 * k) % p) (k % p) : ZMod p) * (choose ((2 * k) / p) (k / p) : ZMod p) := by
    have h_eq := (ZMod.intCast_eq_intCast_iff (choose (2 * k) k) (choose ((2 * k) % p) (k % p) * choose ((2 * k) / p) (k / p)) p).mpr h_lucas
    exact_mod_cast h_eq
  have h_k_mod : k % p = k := Nat.mod_eq_of_lt hk1
  have h_k_div : k / p = 0 := Nat.div_eq_of_lt hk1
  rw [h_k_mod, h_k_div, choose_zero_right, Nat.cast_one, mul_one] at h_cast
  have h_mod_lt : (2 * k) % p < k := by
    have h_eq := (Nat.div_add_mod (2 * k) p).symm
    have h_mod_lt_p := Nat.mod_lt (2 * k) hp_pos
    rcases h_div : (2 * k) / p with _ | _ | j
    · rw [h_div] at h_eq; omega
    · rw [h_div] at h_eq; omega
    · rw [h_div] at h_eq
      have h_ineq : p * (j + 1 + 1) ≥ 2 * p := by
        have h_j : j + 1 + 1 ≥ 2 := by omega
        rw [mul_comm 2 p]
        exact Nat.mul_le_mul_left p h_j
      omega
  have h_choose_zero : choose ((2 * k) % p) k = 0 := choose_eq_zero_of_lt h_mod_lt
  rw [h_choose_zero, Nat.cast_zero] at h_cast
  exact h_cast

lemma a_p_minus_1_eq_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((a (p - 1) : ℤ) : ZMod p) = 1 := by
  have hp : p.Prime := Fact.out
  have hp_pos : p > 0 := hp.pos
  have h_sum := a_cast_eq p (p - 1)
  rw [h_sum]
  have h_split : p - 1 + 1 = p := by omega
  rw [h_split]
  have h_eq : ∑ k ∈ range p, (-1 : ZMod p)^k * (choose (p - 1) k : ZMod p)^4 =
      ∑ k ∈ range p, (-1 : ZMod p)^k := by
    apply sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    rw [choose_p_minus_one_cast p x hx]
    have h_pow_4 : ((-1 : ZMod p)^x)^4 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      have h1 : (-1 : ZMod p)^4 = 1 := by ring
      rw [h1, one_pow]
    rw [h_pow_4, mul_one]
  rw [h_eq]
  exact sum_neg_one_pow_odd p (ZMod p) (Nat.Prime.odd_of_ne_two hp hp2)

lemma c_p_minus_1_eq_sign (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((c (p - 1) : ℤ) : ZMod p) = (-1)^((p - 1) / 2) := by
  have hp : p.Prime := Fact.out
  have hp_pos : p > 0 := hp.pos
  have h_sum := c_cast_eq p (p - 1)
  rw [h_sum]
  have h_split : p - 1 + 1 = p := by omega
  rw [h_split]
  let k0 := (p - 1) / 2
  have hk0_lt : k0 < p := by omega
  have hp_odd : p = 2 * k0 + 1 := by
    have h_odd := Nat.Prime.odd_of_ne_two hp hp2
    rcases h_odd with ⟨k, hk⟩
    have hk0_eq : k0 = k := by
      dsimp [k0]
      rw [hk]
      omega
    rw [hk0_eq, hk]
  have h_sub : range k0 ⊆ range p := range_subset_range.mpr (by omega)
  have h_sum_split : ∑ x ∈ range p, ((-1 : ZMod p) ^ x * (choose (p - 1) x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (p - 1 - x)) (p - 1 - x) : ZMod p)) =
      ∑ x ∈ range k0, ((-1 : ZMod p) ^ x * (choose (p - 1) x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (p - 1 - x)) (p - 1 - x) : ZMod p)) +
      ∑ x ∈ (range p \ range k0), ((-1 : ZMod p) ^ x * (choose (p - 1) x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (p - 1 - x)) (p - 1 - x) : ZMod p)) := by
    rw [← sum_sdiff h_sub, add_comm]
  have h_mem : k0 ∈ range p \ range k0 := by
    rw [mem_sdiff, mem_range, mem_range]
    omega
  have h_sum_split_2 := add_sum_erase (range p \ range k0) (fun x ↦ (-1 : ZMod p) ^ x * (choose (p - 1) x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (p - 1 - x)) (p - 1 - x) : ZMod p)) h_mem
  have h_sum_split_2' : ∑ x ∈ (range p \ range k0), ((-1 : ZMod p) ^ x * (choose (p - 1) x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (p - 1 - x)) (p - 1 - x) : ZMod p)) =
      ((-1 : ZMod p) ^ k0 * (choose (p - 1) k0 : ZMod p) ^ 2 * (choose (2 * k0) k0 : ZMod p) * (choose (2 * (p - 1 - k0)) (p - 1 - k0) : ZMod p)) +
      ∑ x ∈ (range p \ range k0).erase k0, ((-1 : ZMod p) ^ x * (choose (p - 1) x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (p - 1 - x)) (p - 1 - x) : ZMod p)) := by
    rw [← h_sum_split_2, add_comm]
  rw [h_sum_split_2'] at h_sum_split
  have h_sum1_zero : ∑ x ∈ range k0, ((-1 : ZMod p) ^ x * (choose (p - 1) x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (p - 1 - x)) (p - 1 - x) : ZMod p)) = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_range] at hx
    have h_zero : (choose (2 * (p - 1 - x)) (p - 1 - x) : ZMod p) = 0 := by
      apply choose_two_k_k_zero p (p - 1 - x)
      · omega
      · omega
    rw [h_zero, mul_zero]
  have h_sum3_zero : ∑ x ∈ (range p \ range k0).erase k0, ((-1 : ZMod p) ^ x * (choose (p - 1) x : ZMod p) ^ 2 * (choose (2 * x) x : ZMod p) * (choose (2 * (p - 1 - x)) (p - 1 - x) : ZMod p)) = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_erase, mem_sdiff, mem_range, mem_range] at hx
    have h_zero : (choose (2 * x) x : ZMod p) = 0 := by
      apply choose_two_k_k_zero p x
      · omega
      · omega
    rw [h_zero, mul_zero, zero_mul]
  rw [h_sum1_zero, h_sum3_zero, zero_add, add_zero] at h_sum_split
  rw [h_sum_split]
  have hk0_eq : p - 1 - k0 = k0 := by omega
  rw [hk0_eq]
  have h_choose1 : (choose (p - 1) k0 : ZMod p) = (-1)^k0 := choose_p_minus_one_cast p k0 hk0_lt
  have h_choose2 : (choose (2 * k0) k0 : ZMod p) = (choose (p - 1) k0 : ZMod p) := by
    have h_2k0 : 2 * k0 = p - 1 := by omega
    rw [h_2k0]
  rw [h_choose2, h_choose1]
  have h_pow_sq : ((-1 : ZMod p) ^ k0) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have h1 : (-1 : ZMod p)^2 = 1 := by ring
    rw [h1, one_pow]
  rw [h_pow_sq]
  have h_pow_3 : (-1 : ZMod p)^(k0 * 3) = (-1 : ZMod p)^k0 := by
    rw [show k0 * 3 = 2 * k0 + k0 by omega]
    rw [pow_add]
    have h_pow_2k0 : (-1 : ZMod p)^(2 * k0) = 1 := by
      rw [show (-1 : ZMod p)^(2 * k0) = ((-1 : ZMod p)^2)^k0 by rw [pow_mul]]
      ring
    rw [h_pow_2k0, one_mul]
  have h_lhs_eq : (-1 : ZMod p) ^ k0 * 1 * (-1 : ZMod p) ^ k0 * (-1 : ZMod p) ^ k0 = (-1 : ZMod p)^(k0 * 3) := by ring
  rw [h_lhs_eq, h_pow_3]

def anti_diag_perm (p : ℕ) : Equiv.Perm (Fin p) where
  toFun i := ⟨p - 1 - i.val, Nat.lt_of_le_of_lt (Nat.sub_le (p - 1) i.val) (Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) Nat.one_pos)⟩
  invFun i := ⟨p - 1 - i.val, Nat.lt_of_le_of_lt (Nat.sub_le (p - 1) i.val) (Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) Nat.one_pos)⟩
  left_inv i := by
    ext
    dsimp
    omega
  right_inv i := by
    ext
    dsimp
    omega

def prod_swaps (k : ℕ) (p : ℕ) : Equiv.Perm (Fin p) :=
  match k with
  | 0 => 1
  | k + 1 =>
    if h : k < p ∧ p - 1 - k < p then
      prod_swaps k p * Equiv.swap ⟨k, h.1⟩ ⟨p - 1 - k, h.2⟩
    else
      prod_swaps k p

lemma sign_prod_swaps (k p : ℕ) (hk : k ≤ (p - 1) / 2) (hp_odd : p % 2 = 1) :
    (Equiv.Perm.sign (prod_swaps k p) : ℤ) = (-1 : ℤ)^k := by
  induction' k with k ih
  · simp [prod_swaps]
  · have hk' : k ≤ (p - 1) / 2 := by omega
    have h_lt : k < p ∧ p - 1 - k < p := by omega
    dsimp [prod_swaps]
    rw [dif_pos h_lt]
    rw [map_mul]
    simp only [Units.val_mul]
    rw [ih hk']
    have h_ne : (⟨k, h_lt.1⟩ : Fin p) ≠ ⟨p - 1 - k, h_lt.2⟩ := by
      intro hc
      have hc' : k = p - 1 - k := by injection hc
      omega
    rw [Equiv.Perm.sign_swap h_ne]
    simp only [Units.val_neg, Units.val_one]
    ring

lemma prod_swaps_apply (k p : ℕ) (hk : k ≤ (p - 1) / 2) (i : Fin p) :
    prod_swaps k p i = if i.val < k then ⟨p - 1 - i.val, Nat.lt_of_le_of_lt (Nat.sub_le (p - 1) i.val) (Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) Nat.one_pos)⟩
                      else if i.val ≥ p - k then ⟨p - 1 - i.val, Nat.lt_of_le_of_lt (Nat.sub_le (p - 1) i.val) (Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) Nat.one_pos)⟩
                      else i := by
  induction' k with k ih generalizing i
  · simp [prod_swaps]
  · have h_le_half : 2 * k + 2 ≤ p - 1 := by
      have h1 := (Nat.le_div_iff_mul_le (by decide)).mp hk
      omega
    have hk' : k ≤ (p - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by decide)]
      omega
    have ih' := ih hk'
    clear hk hk' ih
    have h_lt : k < p ∧ p - 1 - k < p := by omega
    dsimp [prod_swaps]
    rw [dif_pos h_lt]
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    by_cases h_c1 : i = ⟨k, h_lt.1⟩
    · rw [if_pos h_c1]
      rw [ih' ⟨p - 1 - k, h_lt.2⟩]
      split_ifs <;> (try ext) <;> (try subst_vars) <;> simp only [Fin.ext_iff] at * <;> simp at * <;> omega
    · rw [if_neg h_c1]
      by_cases h_c2 : i = ⟨p - 1 - k, h_lt.2⟩
      · rw [if_pos h_c2]
        rw [ih' ⟨k, h_lt.1⟩]
        split_ifs <;> (try ext) <;> (try subst_vars) <;> simp only [Fin.ext_iff] at * <;> simp at * <;> omega
      · rw [if_neg h_c2]
        rw [ih' i]
        split_ifs <;> (try ext) <;> (try subst_vars) <;> simp only [Fin.ext_iff] at * <;> simp at * <;> omega

lemma anti_diag_perm_eq_prod_swaps (p : ℕ) (hp2 : p ≠ 2) (hp_odd : p % 2 = 1) :
    anti_diag_perm p = prod_swaps ((p - 1) / 2) p := by
  ext i
  have hk0 : (p - 1) / 2 ≤ (p - 1) / 2 := by omega
  rw [prod_swaps_apply ((p - 1) / 2) p hk0 i]
  let k0 := (p - 1) / 2
  have hp_eq : p = 2 * k0 + 1 := by omega
  split_ifs <;> (try ext) <;> dsimp [anti_diag_perm] <;> omega

lemma sign_anti_diag_perm (p : ℕ) (hp2 : p ≠ 2) (hp_odd : p % 2 = 1) :
    (Equiv.Perm.sign (anti_diag_perm p) : ℤ) = (-1 : ℤ)^((p - 1) / 2) := by
  rw [anti_diag_perm_eq_prod_swaps p hp2 hp_odd]
  exact sign_prod_swaps ((p - 1) / 2) p (by omega) hp_odd

lemma sum_eq_card_mul_of_le {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℕ} {c : ℕ}
    (h : ∀ x ∈ s, f x ≤ c) (hsum : ∑ x ∈ s, f x = s.card * c) : ∀ x ∈ s, f x = c := by
  intro x hx
  by_contra h_lt
  have h_lt : f x < c := lt_of_le_of_ne (h x hx) h_lt
  have h_split : ∑ y ∈ s, f y = f x + ∑ y ∈ s.erase x, f y := (add_sum_erase s f hx).symm
  have h_card_pos : s.card > 0 := card_pos.mpr ⟨x, hx⟩
  have h_le : ∑ y ∈ s.erase x, f y ≤ (s.card - 1) * c := by
    have h_card : (s.erase x).card = s.card - 1 := card_erase_of_mem hx
    have h_le' := Finset.sum_le_card_nsmul (s.erase x) f c (fun y hy ↦ h y (mem_of_mem_erase hy))
    rwa [h_card] at h_le'
  have h_mul : s.card * c = (s.card - 1) * c + c := by
    have h_eq : s.card = (s.card - 1) + 1 := (Nat.sub_add_cancel h_card_pos).symm
    nth_rw 1 [h_eq]
    rw [add_mul, one_mul, add_comm]
  have h_strict : ∑ y ∈ s, f y < s.card * c := by
    rw [h_split, h_mul]
    omega
  omega

lemma sum_val_eq_sum_range (p : ℕ) :
    (∑ i : Fin p, i.val) = ∑ i ∈ range p, i := by
  exact Fin.sum_univ_eq_sum_range (fun i ↦ i) p

lemma sum_val_perm (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    (∑ i : Fin p, (σ i).val) = ∑ i : Fin p, i.val := by
  exact Equiv.sum_comp σ (fun i ↦ i.val)

lemma sum_add_val_perm (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    (∑ i : Fin p, (i.val + (σ i).val)) = p * (p - 1) := by
  rw [sum_add_distrib, sum_val_perm, ← two_mul, sum_val_eq_sum_range, mul_comm, sum_range_id_mul_two]

lemma val_add_perm_eq_pred_of_le (p : ℕ) (σ : Equiv.Perm (Fin p))
    (hle : ∀ i : Fin p, i.val + (σ i).val ≤ p - 1) : ∀ i : Fin p, i.val + (σ i).val = p - 1 := by
  intro i
  have h_univ : i ∈ (Finset.univ : Finset (Fin p)) := Finset.mem_univ i
  refine sum_eq_card_mul_of_le (s := Finset.univ) (f := fun i ↦ i.val + (σ i).val) (c := p - 1) ?_ ?_ i h_univ
  · intro x _
    exact hle x
  · rw [Finset.card_univ, Fintype.card_fin]
    exact sum_add_val_perm p σ

lemma det_collapse (p : ℕ) (M : Matrix (Fin p) (Fin p) (ZMod p))
    (h_zero : ∀ i j : Fin p, i.val + j.val ≥ p → M i j = 0) :
    M.det = (Equiv.Perm.sign (anti_diag_perm p)) • ∏ i : Fin p, M (anti_diag_perm p i) i := by
  rw [Matrix.det_apply]
  apply sum_eq_single (anti_diag_perm p)
  · intro σ _ h_ne
    have h_exists : ∃ i : Fin p, (σ i).val + i.val ≥ p := by
      by_contra hc
      push_neg at hc
      have h_le : ∀ i : Fin p, i.val + (σ i).val ≤ p - 1 := by
        intro i
        have h1 := hc i
        omega
      have h_eq := val_add_perm_eq_pred_of_le p σ h_le
      have h_eq_σ : σ = anti_diag_perm p := by
        ext i
        have h2 := h_eq i
        dsimp [anti_diag_perm]
        omega
      exact h_ne h_eq_σ
    rcases h_exists with ⟨i, hi⟩
    have h_term_zero : M (σ i) i = 0 := h_zero (σ i) i hi
    have h_prod_zero : ∏ j : Fin p, M (σ j) j = 0 := by
      exact prod_eq_zero (mem_univ i) h_term_zero
    rw [h_prod_zero, smul_zero]
  · intro h_not_mem
    exact False.elim (h_not_mem (mem_univ _))

/--
A228304 Conjecture: Let p be any odd prime, and let A(p) be the p X p determinant with (i,j)-entry equal to a(i+j) for all i,j = 0,...,p-1. Then A(p) == (-1)^{(p-1)/2} (mod p). Similarly, if c(n) = sum_{k=0}^n (-1)^k*C(n,k)^2*C(2k,k)*C(2(n-k),n-k) and C(p) is the p X p determinant with (i,j)-entry equal to c(i+j) for all i,j = 0,...,p-1, then we have C(p) == 1 (mod p).
-/
theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    -- A(p) is the p x p matrix with entries a(i+j)
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    -- C(p) is the p x p matrix with entries c(i+j)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  intro N half_minus_one A C
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr h_odd
  constructor
  · have h_det_A : ((Matrix.det A : ℤ) : ZMod p) = Matrix.det (fun i j : Fin p ↦ ((A i j : ℤ) : ZMod p)) := by
      exact RingHom.map_det (Int.castRingHom (ZMod p)) A
    have h_A_mod : (fun i j : Fin p ↦ ((A i j : ℤ) : ZMod p)) = (fun i j : Fin p ↦ ((a (i.val + j.val) : ℤ) : ZMod p)) := rfl
    rw [h_A_mod] at h_det_A
    have h_zero : ∀ i j : Fin p, i.val + j.val ≥ p → ((a (i.val + j.val) : ℤ) : ZMod p) = 0 := by
      intro i j hij
      have hij2 : i.val + j.val < 2 * p := by omega
      exact a_eq_zero_of_range p (i.val + j.val) h_odd hij hij2
    have h_collapse := det_collapse p (fun i j : Fin p ↦ ((a (i.val + j.val) : ℤ) : ZMod p)) h_zero
    rw [h_collapse] at h_det_A
    have h_prod_eq : (∏ i : Fin p, ((a ((anti_diag_perm p i).val + i.val) : ℤ) : ZMod p)) = 1 := by
      have h1 : ∀ i : Fin p, ((a ((anti_diag_perm p i).val + i.val) : ℤ) : ZMod p) = 1 := by
        intro i
        have h_index : (anti_diag_perm p i).val + i.val = p - 1 := by
          dsimp [anti_diag_perm]
          omega
        rw [h_index]
        exact a_p_minus_1_eq_one p h_odd
      rw [prod_congr rfl (fun i _ ↦ h1 i), prod_const, one_pow]
    rw [h_prod_eq] at h_det_A
    have h_sign := sign_anti_diag_perm p h_odd hp_odd
    have h_sign_cast : (((Equiv.Perm.sign (anti_diag_perm p) : ℤ) : ZMod p)) = ((-1 : ℤ)^((p-1)/2) : ZMod p) := by
      rw [h_sign]
      push_cast
      rfl
    have h_smul : (Equiv.Perm.sign (anti_diag_perm p)) • (1 : ZMod p) = (((Equiv.Perm.sign (anti_diag_perm p) : ℤ) : ZMod p)) := by
      rw [Units.smul_def, zsmul_eq_mul, mul_one]
    rw [h_smul] at h_det_A
    rw [← h_det_A] at h_sign_cast
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast at h_sign_cast
    push_cast
    exact h_sign_cast

  · have h_det_C : ((Matrix.det C : ℤ) : ZMod p) = Matrix.det (fun i j : Fin p ↦ ((C i j : ℤ) : ZMod p)) := by
      exact RingHom.map_det (Int.castRingHom (ZMod p)) C
    have h_C_mod : (fun i j : Fin p ↦ ((C i j : ℤ) : ZMod p)) = (fun i j : Fin p ↦ ((c (i.val + j.val) : ℤ) : ZMod p)) := rfl
    rw [h_C_mod] at h_det_C
    have h_zero : ∀ i j : Fin p, i.val + j.val ≥ p → ((c (i.val + j.val) : ℤ) : ZMod p) = 0 := by
      intro i j hij
      have hij2 : i.val + j.val < 2 * p := by omega
      exact c_eq_zero_of_range p (i.val + j.val) h_odd hij hij2
    have h_collapse := det_collapse p (fun i j : Fin p ↦ ((c (i.val + j.val) : ℤ) : ZMod p)) h_zero
    rw [h_collapse] at h_det_C
    have h_prod_eq : (∏ i : Fin p, ((c ((anti_diag_perm p i).val + i.val) : ℤ) : ZMod p)) = (-1)^((p-1)/2) := by
      have h1 : ∀ i : Fin p, ((c ((anti_diag_perm p i).val + i.val) : ℤ) : ZMod p) = (-1)^((p-1)/2) := by
        intro i
        have h_index : (anti_diag_perm p i).val + i.val = p - 1 := by
          dsimp [anti_diag_perm]
          omega
        rw [h_index]
        exact c_p_minus_1_eq_sign p h_odd
      rw [prod_congr rfl (fun i _ ↦ h1 i), prod_const]
      rw [Finset.card_univ, Fintype.card_fin]
      exact ZMod.pow_card _
    rw [h_prod_eq] at h_det_C
    have h_sign := sign_anti_diag_perm p h_odd hp_odd
    have h_smul : (Equiv.Perm.sign (anti_diag_perm p)) • ((-1 : ZMod p)^((p-1)/2)) = (((Equiv.Perm.sign (anti_diag_perm p) : ℤ) : ZMod p)) * (-1 : ZMod p)^((p-1)/2) := by
      rw [Units.smul_def, zsmul_eq_mul]
    rw [h_smul] at h_det_C
    have h_sign_cast : (((Equiv.Perm.sign (anti_diag_perm p) : ℤ) : ZMod p)) = ((-1 : ℤ)^((p-1)/2) : ZMod p) := by
      rw [h_sign]
      push_cast
      rfl
    rw [h_sign_cast] at h_det_C
    push_cast at h_det_C
    have h_one : (-1 : ZMod p)^((p-1)/2) * (-1 : ZMod p)^((p-1)/2) = 1 := by
      rw [← sq]
      rw [← pow_mul, mul_comm, pow_mul]
      have h1 : (-1 : ZMod p)^2 = 1 := by ring
      rw [h1, one_pow]
    rw [h_one] at h_det_C
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact h_det_C
