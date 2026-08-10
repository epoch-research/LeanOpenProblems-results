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


lemma choose_p_minus_one_mod_p (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k < p) :
    (Nat.choose (p - 1) k : ZMod p) = (-1 : ZMod p) ^ k := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hk_lt : k < p := by omega
    have ih_val := ih hk_lt
    have h_eq_nat := Nat.choose_succ_right_eq (p - 1) k
    have h_zmod : ((Nat.choose (p - 1) (k + 1) * (k + 1) : ℕ) : ZMod p) =
                  ((Nat.choose (p - 1) k * (p - 1 - k) : ℕ) : ZMod p) :=
      congrArg (fun x : ℕ => (x : ZMod p)) h_eq_nat
    -- we can push cast on h_zmod:
    have h_zmod' : (Nat.choose (p - 1) (k + 1) : ZMod p) * (k + 1 : ZMod p) =
                   (Nat.choose (p - 1) k : ZMod p) * ((p - 1 - k : ℕ) : ZMod p) := by
      push_cast at h_zmod
      exact h_zmod
    have h_sub : ((p - 1 - k : ℕ) : ZMod p) = - (k + 1 : ZMod p) := by
      have h1 : p - 1 - k = p - (k + 1) := by omega
      rw [h1]
      have h2 : k + 1 ≤ p := by omega
      have h3 : ((p - (k + 1) : ℕ) : ZMod p) = (p : ZMod p) - (k + 1 : ZMod p) := by
        exact_mod_cast Nat.cast_sub h2
      rw [h3]
      have hp_zero : (p : ZMod p) = 0 := by simp
      rw [hp_zero]
      ring
    haveI : Fact p.Prime := ⟨hp⟩
    have hk1_nz : (k + 1 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((k + 1 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have h_lt : k + 1 < p := hk
      have h_pos : 0 < k + 1 := by omega
      have : p ≤ k + 1 := Nat.le_of_dvd h_pos h'
      omega
    have h_rhs : (-1 : ZMod p) ^ k * - (k + 1 : ZMod p) = (-1 : ZMod p) ^ (k + 1) * (k + 1 : ZMod p) := by
      rw [pow_succ]
      ring
    rw [h_sub] at h_zmod'
    rw [ih_val] at h_zmod'
    rw [h_rhs] at h_zmod'
    exact mul_right_cancel₀ hk1_nz h_zmod'


lemma sum_neg_one_pow_odd (p : ℕ) (m : ℕ) :
    (Finset.sum (range (2 * m + 1)) fun k => (-1 : ZMod p) ^ k) = 1 := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have h_split : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by omega
    rw [h_split, sum_range_succ, sum_range_succ]
    rw [ih]
    have h_even : (-1 : ZMod p) ^ (2 * m) = 1 := by
      rw [pow_mul]
      have : (-1 : ZMod p) ^ 2 = 1 := by ring
      rw [this, one_pow]
    have h_odd : (-1 : ZMod p) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, h_even, one_mul]
    have h_even' : (-1 : ZMod p) ^ (2 * m + 2) = 1 := by
      rw [pow_succ, h_odd]
      ring
    rw [h_odd, h_even']
    ring




lemma choose_two_n_n_mod_p (p : ℕ) (hp : Nat.Prime p) (n : ℕ) (hn_lt : n < p) (hn_ge : p ≤ 2 * n) :
    (Nat.choose (2 * n) n : ZMod p) = 0 := by
  have hd : p ∣ Nat.choose (2 * n) n := by
    have h_sub : 2 * n - n = n := by omega
    have h_hab : 2 * n - n < p := by
      rw [h_sub]
      exact hn_lt
    exact Nat.Prime.dvd_choose hp hn_lt h_hab hn_ge
  rw [ZMod.natCast_eq_zero_iff]
  exact hd


lemma c_term_zero_of_ne (p : ℕ) (hp : Nat.Prime p) (m : ℕ) (hm : p = 2 * m + 1) (k : ℕ) (hk : k < p) (hne : k ≠ m) :
    ((Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p)) = 0 := by
  by_cases h_lt : k < m
  · have h1 : p - 1 - k < p := by omega
    have h2 : p ≤ 2 * (p - 1 - k) := by omega
    have h_zero : (Nat.choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) = 0 :=
      choose_two_n_n_mod_p p hp (p - 1 - k) h1 h2
    rw [h_zero, mul_zero]
  · have h_gt : k > m := by omega
    have h1 : k < p := hk
    have h2 : p ≤ 2 * k := by omega
    have h_zero : (Nat.choose (2 * k) k : ZMod p) = 0 :=
      choose_two_n_n_mod_p p hp k h1 h2
    rw [h_zero, zero_mul]


lemma c_p_minus_one_mod_p (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    (c (p - 1) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hp_odd : Odd p := hp.odd_of_ne_two h_odd
  rcases hp_odd with ⟨m, hm⟩
  have h_range : p - 1 + 1 = p := by omega
  have hc : (c (p - 1) : ZMod p) = (((Finset.sum (range p) fun k => ((-1 : ℤ) ^ k) * ((Nat.choose (p - 1) k : ℤ) ^ 2) * (Nat.choose (2 * k) k : ℤ) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ℤ) : ℤ) : ZMod p)) := by
    unfold c
    rw [h_range]
  rw [hc]
  push_cast
  have h_sum : (Finset.sum (range p) fun k => (-1 : ZMod p) ^ k * (Nat.choose (p - 1) k : ZMod p) ^ 2 * (Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p)) =
               (-1 : ZMod p) ^ m * (Nat.choose (p - 1) m : ZMod p) ^ 2 * (Nat.choose (2 * m) m : ZMod p) * (Nat.choose (2 * (p - 1 - m)) (p - 1 - m) : ZMod p) := by
    apply Finset.sum_eq_single m
    · intro k hk hk_ne
      rw [Finset.mem_range] at hk
      have h_zero : ((Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p)) = 0 :=
        c_term_zero_of_ne p hp m hm k hk hk_ne
      have h_assoc : (-1 : ZMod p) ^ k * (Nat.choose (p - 1) k : ZMod p) ^ 2 * (Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) =
                     (-1 : ZMod p) ^ k * (Nat.choose (p - 1) k : ZMod p) ^ 2 * ((Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p)) := by ring
      rw [h_assoc, h_zero, mul_zero]
    · intro h_not_mem
      have h_mem : m ∈ range p := by
        rw [Finset.mem_range]
        omega
      exact False.elim (h_not_mem h_mem)
  rw [h_sum]
  have h_sub_m : p - 1 - m = m := by omega
  rw [h_sub_m]
  have h_2m : 2 * m = p - 1 := by omega
  rw [h_2m]
  have h_choose_m : (Nat.choose (p - 1) m : ZMod p) = (-1 : ZMod p) ^ m := by
    apply choose_p_minus_one_mod_p p hp m
    omega
  rw [h_choose_m]
  have h_sq : ((-1 : ZMod p) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have : (-1 : ZMod p) ^ 2 = 1 := by ring
    rw [this, one_pow]
  have h_mul_sq : (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m = 1 := by
    have : (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m = ((-1 : ZMod p) ^ m) ^ 2 := by ring
    rw [this, h_sq]
  rw [h_sq]
  have h_goal : (-1 : ZMod p) ^ m * 1 * (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m = (-1 : ZMod p) ^ m := by
    calc (-1 : ZMod p) ^ m * 1 * (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m
      _ = (-1 : ZMod p) ^ m * ((-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m) := by ring
      _ = (-1 : ZMod p) ^ m * 1 := by rw [h_mul_sq]
      _ = (-1 : ZMod p) ^ m := by ring
  rw [h_goal]
  have h_div : (p - 1) / 2 = m := by omega
  rw [h_div]

lemma a_p_minus_one_mod_p (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    (a (p - 1) : ZMod p) = 1 := by
  have hp_odd : Odd p := hp.odd_of_ne_two h_odd
  rcases hp_odd with ⟨m, hm⟩
  have h_range : p - 1 + 1 = p := by omega
  have ha : (a (p - 1) : ZMod p) = (((Finset.sum (range p) fun k => ((-1 : ℤ) ^ k) * ((Nat.choose (p - 1) k : ℤ) ^ 4) : ℤ) : ZMod p)) := by
    unfold a
    rw [h_range]
  rw [ha]
  push_cast
  have h_sum : (Finset.sum (range p) fun k => (-1 : ZMod p) ^ k * (Nat.choose (p - 1) k : ZMod p) ^ 4) =
               (Finset.sum (range p) fun k => (-1 : ZMod p) ^ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk_lt : k < p := by
      rw [Finset.mem_range] at hk
      exact hk
    rw [choose_p_minus_one_mod_p p hp k hk_lt]
    have h_term : (-1 : ZMod p) ^ k * ((-1 : ZMod p) ^ k) ^ 4 = (-1 : ZMod p) ^ k := by
      rw [← pow_mul, mul_comm k 4, pow_mul]
      have : (-1 : ZMod p) ^ 4 = 1 := by ring
      rw [this, one_pow, mul_one]
    exact h_term
  rw [h_sum]
  rw [hm]
  exact sum_neg_one_pow_odd (2 * m + 1) m



lemma choose_lucas_one (p : ℕ) [hp : Fact p.Prime] (n k : ℕ) :
    (Nat.choose n k : ZMod p) = (Nat.choose (n % p) (k % p) : ZMod p) * (Nat.choose (n / p) (k / p) : ZMod p) := by
  have h_eq := @Choose.choose_modEq_choose_mod_mul_choose_div n k p hp
  rw [← ZMod.intCast_eq_intCast_iff] at h_eq
  push_cast at h_eq
  exact h_eq


lemma choose_p_add_d_k_zero (p : ℕ) [hp : Fact p.Prime] (d k : ℕ) (hd : d < p) (hk_gt : d < k) (hk_lt : k < p) :
    (Nat.choose (p + d) k : ZMod p) = 0 := by
  have h_lucas := choose_lucas_one p (p + d) k
  rw [h_lucas]
  have h1 : (p + d) % p = d := by
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hd
  have h2 : k % p = k := Nat.mod_eq_of_lt hk_lt
  rw [h1, h2]
  have h3 : Nat.choose d k = 0 := Nat.choose_eq_zero_of_lt hk_gt
  have h3' : (Nat.choose d k : ZMod p) = 0 := by simp [h3]
  rw [h3', zero_mul]

lemma choose_p_add_d_p_add_j (p : ℕ) [hp : Fact p.Prime] (d j : ℕ) (hd : d < p) (hj : j < p) :
    (Nat.choose (p + d) (p + j) : ZMod p) = (Nat.choose d j : ZMod p) := by
  have h_lucas := choose_lucas_one p (p + d) (p + j)
  rw [h_lucas]
  have h1 : (p + d) % p = d := by
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hd
  have h2 : (p + j) % p = j := by
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hj
  have h3 : (p + d) / p = 1 := by
    have h_div := Nat.add_div_of_dvd_right (Nat.dvd_refl p) (b := d)
    rw [h_div]
    have h_self : p / p = 1 := Nat.div_self hp.out.pos
    have h_lt : d / p = 0 := Nat.div_eq_of_lt hd
    rw [h_self, h_lt]
  have h4 : (p + j) / p = 1 := by
    have h_div := Nat.add_div_of_dvd_right (Nat.dvd_refl p) (b := j)
    rw [h_div]
    have h_self : p / p = 1 := Nat.div_self hp.out.pos
    have h_lt : j / p = 0 := Nat.div_eq_of_lt hj
    rw [h_self, h_lt]
  rw [h1, h2, h3, h4]
  simp



lemma choose_two_p_add_two_k_p_add_k (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (hk : k < p) :
    (Nat.choose (2 * p + 2 * k) (p + k) : ZMod p) = 2 * (Nat.choose (2 * k) k : ZMod p) := by
  have h_pos : p > 0 := hp.out.pos
  by_cases h_lt : 2 * k < p
  · have h_lucas := choose_lucas_one p (2 * p + 2 * k) (p + k)
    rw [h_lucas]
    have h_mod1 : (2 * p + 2 * k) % p = 2 * k := by
      rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt h_lt
    have h_mod2 : (p + k) % p = k := by
      rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt hk
    have h_div1 : (2 * p + 2 * k) / p = 2 := by
      have : 2 * p + 2 * k = 2 * k + 2 * p := by ring
      rw [this]
      rw [Nat.add_mul_div_right _ _ h_pos]
      have : 2 * k / p = 0 := Nat.div_eq_of_lt h_lt
      omega
    have h_div2 : (p + k) / p = 1 := by
      have : p + k = k + 1 * p := by ring
      rw [this]
      rw [Nat.add_mul_div_right _ _ h_pos]
      have : k / p = 0 := Nat.div_eq_of_lt hk
      omega
    rw [h_mod1, h_mod2, h_div1, h_div2]
    have : (Nat.choose 2 1 : ZMod p) = 2 := rfl
    rw [this]
    ring
  · have h_zero1 : (Nat.choose (2 * k) k : ZMod p) = 0 :=
      choose_two_n_n_mod_p p hp.out k hk (by omega)
    have h_zero2 : (Nat.choose (2 * p + 2 * k) (p + k) : ZMod p) = 0 := by
      have h_lucas := choose_lucas_one p (2 * p + 2 * k) (p + k)
      rw [h_lucas]
      have h_mod1 : (2 * p + 2 * k) % p = 2 * k - p := by
        rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
        have h_eq : 2 * k = p + (2 * k - p) := by omega
        rw [h_eq]
        rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
        have h_lt_p : 2 * k - p < p := by omega
        rw [Nat.mod_eq_of_lt h_lt_p]
        omega
      have h_mod2 : (p + k) % p = k := by
        rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt hk
      rw [h_mod1, h_mod2]
      have h_lt2 : 2 * k - p < k := by omega
      have h_choose_zero : Nat.choose (2 * k - p) k = 0 := Nat.choose_eq_zero_of_lt h_lt2
      simp [h_choose_zero]
    rw [h_zero1, h_zero2]
    ring


lemma a_p_add_d_mod_p (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) (d : ℕ) (hd : d < p - 1) :
    (a (p + d) : ZMod p) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_odd : Odd p := hp.odd_of_ne_two h_odd
  rcases hp_odd with ⟨m, hm⟩
  have h_pos : p > 0 := by omega
  have h_split1 : p ≤ p + d + 1 := by omega
  have h_sum1 := Finset.sum_range_add_sum_Ico (fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 4) h_split1
  have ha : (a (p + d) : ZMod p) = (Finset.sum (range (p + d + 1)) fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 4) := by
    unfold a
    push_cast
    rfl
  rw [ha, ← h_sum1]
  have h_split2 : d + 1 ≤ p := by omega
  have h_sum2 := Finset.sum_range_add_sum_Ico (fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 4) h_split2
  rw [← h_sum2]
  have h_middle_zero : (Finset.sum (Ico (d + 1) p) fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 4) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hd_lt_p : d < p := by omega
    have hk_gt : d < k := hk.left
    have hk_lt : k < p := hk.right
    rw [choose_p_add_d_k_zero p d k hd_lt_p hk_gt hk_lt]
    ring
  rw [h_middle_zero, add_zero]
  have h_shift := Finset.sum_Ico_add (fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 4) 0 (d + 1) p
  simp only [zero_add] at h_shift
  have h_add_comm : p + d + 1 = d + 1 + p := by omega
  rw [h_add_comm]
  rw [← h_shift]
  rw [Ico_zero_eq_range]
  have h_cancel : (Finset.sum (range (d + 1)) fun k => (-1 : ZMod p) ^ (p + k) * (Nat.choose (p + d) (p + k) : ZMod p) ^ 4) =
                  - (Finset.sum (range (d + 1)) fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 4) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have h_choose1 : (Nat.choose (p + d) (p + k) : ZMod p) = (Nat.choose d k : ZMod p) := by
      apply choose_p_add_d_p_add_j p d k (by omega) (by omega)
    have h_choose2 : (Nat.choose (p + d) k : ZMod p) = (Nat.choose d k : ZMod p) := by
      have h_lucas := choose_lucas_one p (p + d) k
      rw [h_lucas]
      have h_mod : (p + d) % p = d := by
        rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (by omega)
      have h_div : (p + d) / p = 1 := by
        have h_div_add := Nat.add_div_of_dvd_right (Nat.dvd_refl p) (b := d)
        rw [h_div_add]
        have h_self : p / p = 1 := Nat.div_self h_pos
        have h_lt : d / p = 0 := Nat.div_eq_of_lt (by omega)
        rw [h_self, h_lt]
      have h_k_mod : k % p = k := Nat.mod_eq_of_lt (by omega)
      have h_k_div : k / p = 0 := Nat.div_eq_of_lt (by omega)
      rw [h_mod, h_k_mod, h_div, h_k_div]
      simp
    rw [h_choose1, h_choose2]
    have h_pow : (-1 : ZMod p) ^ (p + k) = (-1 : ZMod p) ^ p * (-1 : ZMod p) ^ k := pow_add (-1 : ZMod p) p k
    have h_p_odd : (-1 : ZMod p) ^ p = -1 := by
      have h_pow_odd : (-1 : ZMod p) ^ (2 * m + 1) = -1 := by
        have h_even : (-1 : ZMod p) ^ (2 * m) = 1 := by
          rw [pow_mul]
          have : (-1 : ZMod p) ^ 2 = 1 := by ring
          rw [this, one_pow]
        rw [pow_succ, h_even, one_mul]
      have h_congr := congrArg (fun x => (-1 : ZMod p) ^ x) hm
      have h_congr' : (-1 : ZMod p) ^ p = (-1 : ZMod p) ^ (2 * m + 1) := h_congr
      rw [h_congr']
      exact h_pow_odd
    rw [h_pow, h_p_odd]
    ring
  rw [h_cancel]
  ring



lemma c_p_add_d_mod_p (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) (d : ℕ) (hd : d < p - 1) :
    (c (p + d) : ZMod p) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_odd : Odd p := hp.odd_of_ne_two h_odd
  rcases hp_odd with ⟨m, hm⟩
  have h_pos : p > 0 := by omega
  have h_split1 : p ≤ p + d + 1 := by omega
  have h_sum1 := Finset.sum_range_add_sum_Ico (fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 2 * (Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p + d - k)) (p + d - k) : ZMod p)) h_split1
  have hc : (c (p + d) : ZMod p) = (Finset.sum (range (p + d + 1)) fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 2 * (Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p + d - k)) (p + d - k) : ZMod p)) := by
    unfold c
    push_cast
    rfl
  rw [hc, ← h_sum1]
  have h_split2 : d + 1 ≤ p := by omega
  have h_sum2 := Finset.sum_range_add_sum_Ico (fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 2 * (Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p + d - k)) (p + d - k) : ZMod p)) h_split2
  rw [← h_sum2]
  have h_middle_zero : (Finset.sum (Ico (d + 1) p) fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 2 * (Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p + d - k)) (p + d - k) : ZMod p)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hd_lt_p : d < p := by omega
    have hk_gt : d < k := hk.left
    have hk_lt : k < p := hk.right
    rw [choose_p_add_d_k_zero p d k hd_lt_p hk_gt hk_lt]
    ring
  rw [h_middle_zero, add_zero]
  have h_shift := Finset.sum_Ico_add (fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 2 * (Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p + d - k)) (p + d - k) : ZMod p)) 0 (d + 1) p
  simp only [zero_add] at h_shift
  have h_add_comm : p + d + 1 = d + 1 + p := by omega
  rw [h_add_comm]
  rw [← h_shift]
  rw [Ico_zero_eq_range]
  have h_cancel : (Finset.sum (range (d + 1)) fun k => (-1 : ZMod p) ^ (p + k) * (Nat.choose (p + d) (p + k) : ZMod p) ^ 2 * (Nat.choose (2 * (p + k)) (p + k) : ZMod p) * (Nat.choose (2 * (p + d - (p + k))) (p + d - (p + k)) : ZMod p)) =
                  - (Finset.sum (range (d + 1)) fun k => (-1 : ZMod p) ^ k * (Nat.choose (p + d) k : ZMod p) ^ 2 * (Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p + d - k)) (p + d - k) : ZMod p)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have h_choose1 : (Nat.choose (p + d) (p + k) : ZMod p) = (Nat.choose d k : ZMod p) := by
      apply choose_p_add_d_p_add_j p d k (by omega) (by omega)
    have h_choose2 : (Nat.choose (p + d) k : ZMod p) = (Nat.choose d k : ZMod p) := by
      have h_lucas := choose_lucas_one p (p + d) k
      rw [h_lucas]
      have h_mod : (p + d) % p = d := by
        rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (by omega)
      have h_div : (p + d) / p = 1 := by
        have h_div_add := Nat.add_div_of_dvd_right (Nat.dvd_refl p) (b := d)
        rw [h_div_add]
        have h_self : p / p = 1 := Nat.div_self h_pos
        have h_lt : d / p = 0 := Nat.div_eq_of_lt (by omega)
        rw [h_self, h_lt]
      have h_k_mod : k % p = k := Nat.mod_eq_of_lt (by omega)
      have h_k_div : k / p = 0 := Nat.div_eq_of_lt (by omega)
      rw [h_mod, h_k_mod, h_div, h_k_div]
      simp
    have h_double_p : 2 * (p + k) = 2 * p + 2 * k := by ring
    have h_choose_double1 : (Nat.choose (2 * (p + k)) (p + k) : ZMod p) = 2 * (Nat.choose (2 * k) k : ZMod p) := by
      rw [h_double_p]
      apply choose_two_p_add_two_k_p_add_k p k (by omega)
    have h_sub_eq : p + d - (p + k) = d - k := by omega
    rw [h_sub_eq]
    have h_choose_double2 : (Nat.choose (2 * (p + d - k)) (p + d - k) : ZMod p) = 2 * (Nat.choose (2 * (d - k)) (d - k) : ZMod p) := by
      have h_eq' : p + d - k = p + (d - k) := by omega
      have h_double' : 2 * (p + d - k) = 2 * p + 2 * (d - k) := by omega
      rw [h_double', h_eq']
      apply choose_two_p_add_two_k_p_add_k p (d - k) (by omega)
    rw [h_choose_double2]
    have h_pow : (-1 : ZMod p) ^ (p + k) = (-1 : ZMod p) ^ p * (-1 : ZMod p) ^ k := pow_add (-1 : ZMod p) p k
    have h_p_odd : (-1 : ZMod p) ^ p = -1 := by
      have h_pow_odd : (-1 : ZMod p) ^ (2 * m + 1) = -1 := by
        have h_even : (-1 : ZMod p) ^ (2 * m) = 1 := by
          rw [pow_mul]
          have : (-1 : ZMod p) ^ 2 = 1 := by ring
          rw [this, one_pow]
        rw [pow_succ, h_even, one_mul]
      have h_congr := congrArg (fun x => (-1 : ZMod p) ^ x) hm
      have h_congr' : (-1 : ZMod p) ^ p = (-1 : ZMod p) ^ (2 * m + 1) := h_congr
      rw [h_congr']
      exact h_pow_odd
    rw [h_pow, h_p_odd]
    rw [h_choose1, h_choose2]
    rw [h_choose_double1]
    ring
  rw [h_cancel]
  ring



lemma a_entry_zero (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) (i j : Fin p) (h_ge : p ≤ i.val + j.val) :
    (a (i.val + j.val) : ZMod p) = 0 := by
  have hd : i.val + j.val - p < p - 1 := by
    have h1 : i.val < p := i.isLt
    have h2 : j.val < p := j.isLt
    omega
  have h_eq : i.val + j.val = p + (i.val + j.val - p) := by omega
  rw [h_eq]
  exact a_p_add_d_mod_p p hp h_odd (i.val + j.val - p) hd

lemma c_entry_zero (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) (i j : Fin p) (h_ge : p ≤ i.val + j.val) :
    (c (i.val + j.val) : ZMod p) = 0 := by
  have hd : i.val + j.val - p < p - 1 := by
    have h1 : i.val < p := i.isLt
    have h2 : j.val < p := j.isLt
    omega
  have h_eq : i.val + j.val = p + (i.val + j.val - p) := by omega
  rw [h_eq]
  exact c_p_add_d_mod_p p hp h_odd (i.val + j.val - p) hd

def sigma_rev (p : ℕ) : Equiv.Perm (Fin p) where
  toFun i := ⟨p - 1 - i.val, by omega⟩
  invFun i := ⟨p - 1 - i.val, by omega⟩
  left_inv i := by
    ext
    simp
    omega
  right_inv i := by
    ext
    simp
    omega


lemma sum_val_tau_eq (p : ℕ) (tau : Equiv.Perm (Fin p)) :
    (∑ i : Fin p, (tau i).val) = ∑ i : Fin p, i.val := by
  exact Equiv.sum_comp tau (fun x => x.val)


lemma sum_val_rev_eq (p : ℕ) :
    (∑ i : Fin p, (p - 1 - i.val)) = ∑ i : Fin p, i.val := by
  have h_eq : (∑ i : Fin p, (p - 1 - i.val)) = ∑ i : Fin p, (sigma_rev p i).val := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [h_eq]
  exact Equiv.sum_comp (sigma_rev p) (fun x => x.val)


lemma eq_sigma_rev_of_le (p : ℕ) (tau : Equiv.Perm (Fin p))
    (hle : ∀ i : Fin p, (tau i).val ≤ p - 1 - i.val) :
    tau = sigma_rev p := by
  ext i
  have h_eq_all : ∀ j : Fin p, (tau j).val = p - 1 - j.val := by
    by_contra! h_exists
    rcases h_exists with ⟨j, hj⟩
    have h_lt : (tau j).val < p - 1 - j.val := lt_of_le_of_ne (hle j) hj
    have h_sum_lt : (∑ i : Fin p, (tau i).val) < ∑ i : Fin p, (p - 1 - i.val) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact hle i
      · use j
        simp
        exact h_lt
    rw [sum_val_tau_eq p tau, sum_val_rev_eq p] at h_sum_lt
    omega
  exact h_eq_all i



lemma det_anti_triangular_mod_p {p : ℕ} (M : Matrix (Fin p) (Fin p) (ZMod p))
    (h_zero : ∀ i j : Fin p, p ≤ i.val + j.val → M i j = 0) :
    M.det = (Equiv.Perm.sign (sigma_rev p) : ZMod p) * ∏ i : Fin p, M (sigma_rev p i) i := by
  rw [Matrix.det_apply']
  apply Finset.sum_eq_single (sigma_rev p)
  · intro tau h_mem h_ne
    have h_not_le : ¬ (∀ i : Fin p, (tau i).val ≤ p - 1 - i.val) := by
      intro h
      have h_eq := eq_sigma_rev_of_le p tau h
      exact h_ne h_eq
    push_neg at h_not_le
    rcases h_not_le with ⟨i, hi_gt⟩
    have h_sum_ge : p ≤ (tau i).val + i.val := by omega
    have h_entry_zero : M (tau i) i = 0 := h_zero (tau i) i h_sum_ge
    have h_prod_zero : (∏ j : Fin p, M (tau j) j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact h_entry_zero
    rw [h_prod_zero, mul_zero]
  · intro h_not_mem
    have h_mem : sigma_rev p ∈ Finset.univ := Finset.mem_univ _
    exact False.elim (h_not_mem h_mem)


lemma sign_sigma_rev (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    (Equiv.Perm.sign (sigma_rev p) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hp_odd : Odd p := hp.odd_of_ne_two h_odd
  rcases hp_odd with ⟨m, hm⟩
  have h_sign := Equiv.Perm.sign_eq_prod_prod_Ioi (sigma_rev p)
  have h_sign_zmod : (Equiv.Perm.sign (sigma_rev p) : ZMod p) = (((Equiv.Perm.sign (sigma_rev p) : ℤ) : ZMod p)) := rfl
  rw [h_sign_zmod]
  rw [h_sign]
  push_cast
  have h_simp : (∏ x : Fin p, ∏ i ∈ Finset.Ioi x, ↑↑(if (sigma_rev p) x < (sigma_rev p) i then (1 : ℤˣ) else -1)) =
                ∏ x : Fin p, ∏ i ∈ Finset.Ioi x, (if (sigma_rev p) x < (sigma_rev p) i then (1 : ZMod p) else -1) := by
    apply Finset.prod_congr rfl
    intro x _
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  rw [h_simp]
  have h_cond : ∀ i : Fin p, ∀ j ∈ Finset.Ioi i, (if sigma_rev p i < sigma_rev p j then (1 : ZMod p) else -1) = -1 := by
    intro i j hj
    rw [Finset.mem_Ioi] at hj
    have h_lt : ¬ (sigma_rev p i < sigma_rev p j) := by
      intro h
      have h' : p - 1 - i.val < p - 1 - j.val := h
      omega
    rw [if_neg h_lt]
  have h_inner : ∀ i : Fin p, (∏ j ∈ Finset.Ioi i, (if sigma_rev p i < sigma_rev p j then (1 : ZMod p) else -1)) = (-1 : ZMod p) ^ (p - 1 - i.val) := by
    intro i
    rw [Finset.prod_congr rfl (h_cond i)]
    rw [Finset.prod_const]
    rw [Fin.card_Ioi i]
  have h_prod : (∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (if sigma_rev p i < sigma_rev p j then (1 : ZMod p) else -1)) =
                ∏ i : Fin p, (-1 : ZMod p) ^ (p - 1 - i.val) := by
    apply Finset.prod_congr rfl
    intro i _
    exact h_inner i
  rw [h_prod]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [sum_val_rev_eq p]
  have h_sum_range : (∑ i : Fin p, i.val) = ∑ i ∈ Finset.range p, i := Fin.sum_univ_eq_sum_range (fun x => x) p
  rw [h_sum_range]
  rw [sum_range_id]
  have h_val : p * (p - 1) / 2 = 2 * m ^ 2 + m := by
    subst p
    have h1 : 2 * m + 1 - 1 = 2 * m := by omega
    have h2 : (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m) := by ring
    have : (2 * m + 1) * (2 * m + 1 - 1) / 2 = 2 * m ^ 2 + m := by
      rw [h1, h2]
      rw [Nat.mul_div_cancel_left _ (by decide)]
      ring
    exact this
  rw [h_val]
  have h_split_pow : (-1 : ZMod p) ^ (2 * m ^ 2 + m) = ((-1 : ZMod p) ^ 2) ^ (m ^ 2) * (-1 : ZMod p) ^ m := by
    rw [← pow_mul, ← pow_add]
  rw [h_split_pow]
  have : (-1 : ZMod p) ^ 2 = 1 := by ring
  rw [this, one_pow, one_mul]
  have h_div : (p - 1) / 2 = m := by omega
  rw [h_div]


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
  let f := Int.castRingHom (ZMod p)
  have h_det_A : ((Matrix.det A : ℤ) : ZMod p) = (A.map f).det := by
    have h1 : ((Matrix.det A : ℤ) : ZMod p) = (Int.castRingHom (ZMod p)) (Matrix.det A) := rfl
    rw [h1, RingHom.map_det, RingHom.mapMatrix_apply]
  have h_zero_A : ∀ i j : Fin p, p ≤ i.val + j.val → (A.map f) i j = 0 := by
    intro i j h_ge
    rw [Matrix.map_apply]
    change f (a (i.val + j.val)) = 0
    have : f (a (i.val + j.val)) = (a (i.val + j.val) : ZMod p) := rfl
    rw [this]
    exact a_entry_zero p hp h_odd i j h_ge
  have h_det_A_eq := det_anti_triangular_mod_p (A.map f) h_zero_A
  have h_diag_A : ∀ i : Fin p, (A.map f) (sigma_rev p i) i = 1 := by
    intro i
    rw [Matrix.map_apply]
    change ((a ((sigma_rev p i).val + i.val) : ℤ) : ZMod p) = 1
    have h_val : (sigma_rev p i).val = p - 1 - i.val := rfl
    have h_sum : (sigma_rev p i).val + i.val = p - 1 := by omega
    rw [h_sum]
    exact a_p_minus_one_mod_p p hp h_odd
  have h_prod_A : (∏ i : Fin p, (A.map f) (sigma_rev p i) i) = 1 := by
    rw [Finset.prod_congr rfl (fun i _ => h_diag_A i)]
    simp
  rw [h_prod_A, mul_one] at h_det_A_eq
  rw [sign_sigma_rev p hp h_odd] at h_det_A_eq
  have h_A_mod : ((Matrix.det A : ℤ) : ZMod p) = (((-1 : ℤ) ^ half_minus_one : ℤ) : ZMod p) := by
    rw [h_det_A, h_det_A_eq]
    push_cast
    rfl
  rw [ZMod.intCast_eq_intCast_iff] at h_A_mod

  have h_det_C : ((Matrix.det C : ℤ) : ZMod p) = (C.map f).det := by
    have h1 : ((Matrix.det C : ℤ) : ZMod p) = (Int.castRingHom (ZMod p)) (Matrix.det C) := rfl
    rw [h1, RingHom.map_det, RingHom.mapMatrix_apply]
  have h_zero_C : ∀ i j : Fin p, p ≤ i.val + j.val → (C.map f) i j = 0 := by
    intro i j h_ge
    rw [Matrix.map_apply]
    change f (c (i.val + j.val)) = 0
    have : f (c (i.val + j.val)) = (c (i.val + j.val) : ZMod p) := rfl
    rw [this]
    exact c_entry_zero p hp h_odd i j h_ge
  have h_det_C_eq := det_anti_triangular_mod_p (C.map f) h_zero_C
  have h_diag_C : ∀ i : Fin p, (C.map f) (sigma_rev p i) i = (-1 : ZMod p) ^ half_minus_one := by
    intro i
    rw [Matrix.map_apply]
    change ((c ((sigma_rev p i).val + i.val) : ℤ) : ZMod p) = (-1 : ZMod p) ^ half_minus_one
    have h_val : (sigma_rev p i).val = p - 1 - i.val := rfl
    have h_sum : (sigma_rev p i).val + i.val = p - 1 := by omega
    rw [h_sum]
    exact c_p_minus_one_mod_p p hp h_odd
  have h_prod_C : (∏ i : Fin p, (C.map f) (sigma_rev p i) i) = ((-1 : ZMod p) ^ half_minus_one) ^ p := by
    rw [Finset.prod_congr rfl (fun i _ => h_diag_C i)]
    simp
  rw [h_prod_C] at h_det_C_eq
  rw [sign_sigma_rev p hp h_odd] at h_det_C_eq
  have h_C_rhs : (-1 : ZMod p) ^ half_minus_one * ((-1 : ZMod p) ^ half_minus_one) ^ p =
                 (-1 : ZMod p) ^ (half_minus_one * (p + 1)) := by
    rw [← pow_mul]
    rw [← pow_add]
    have h_arith : half_minus_one + half_minus_one * p = half_minus_one * (p + 1) := by ring
    rw [h_arith]
  have hp_odd : Odd p := hp.odd_of_ne_two h_odd
  rcases hp_odd with ⟨m, hm⟩
  have h_div_m : half_minus_one = m := by
    change (p - 1) / 2 = m
    omega
  have h_p_plus_1 : p + 1 = 2 * m + 2 := by omega
  have h_arith2 : half_minus_one * (p + 1) = 2 * (m * (m + 1)) := by
    rw [h_div_m, h_p_plus_1]
    ring
  have h_C_rhs2 : (-1 : ZMod p) ^ (half_minus_one * (p + 1)) = 1 := by
    rw [h_arith2]
    rw [pow_mul]
    have h_neg_one_sq : (-1 : ZMod p) ^ 2 = 1 := by ring
    rw [h_neg_one_sq, one_pow]
  rw [h_C_rhs, h_C_rhs2] at h_det_C_eq
  have h_C_mod : ((Matrix.det C : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) := by
    rw [h_det_C, h_det_C_eq]
    push_cast
    rfl
  rw [ZMod.intCast_eq_intCast_iff] at h_C_mod

  exact ⟨h_A_mod, h_C_mod⟩


lemma test_lemma (p : ℕ) (hp : Nat.Prime p) : p > 1 := hp.one_lt
