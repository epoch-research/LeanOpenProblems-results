import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix Equiv Perm Choose

def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

lemma odd_p {p : ℕ} (hp : Nat.Prime p) (hp_odd : p ≠ 2) : Odd p := by
  have := hp.eq_two_or_odd
  rcases this with rfl | h
  · contradiction
  · exact Nat.odd_iff.mpr h

lemma choose_p_minus_one (p k : ℕ) [hp : Fact p.Prime] (hk : k < p) :
  (choose (p - 1) k : ZMod p) = (-1 : ZMod p) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk_p : k < p := by omega
    have h_eq : choose (p - 1) (k + 1) * (k + 1) = choose (p - 1) k * (p - 1 - k) := by
      exact choose_succ_right_eq (p - 1) k
    have h_zmod : (choose (p - 1) (k + 1) : ZMod p) * (k + 1 : ZMod p) = (choose (p - 1) k : ZMod p) * ((p - 1 - k : ℕ) : ZMod p) := by
      have : ((choose (p - 1) (k + 1) * (k + 1) : ℕ) : ZMod p) = ((choose (p - 1) k * (p - 1 - k) : ℕ) : ZMod p) := by
        rw [h_eq]
      push_cast at this ⊢; exact this
    rw [ih hk_p] at h_zmod
    have h_p : ((p - 1 - k : ℕ) : ZMod p) = - (k + 1 : ZMod p) := by
      have : ((p - 1 - k : ℕ) : ZMod p) + (k + 1 : ZMod p) = 0 := by
        have h_sum : p - 1 - k + (k + 1) = p := by omega
        have h_cast : (((p - 1 - k + (k + 1) : ℕ) : ZMod p)) = ((p : ℕ) : ZMod p) := by rw [h_sum]
        push_cast at h_cast
        rw [CharP.cast_eq_zero (ZMod p) p] at h_cast
        exact h_cast
      exact eq_neg_of_add_eq_zero_left this
    rw [h_p] at h_zmod
    have h_mul : (-1 : ZMod p) ^ k * - (k + 1 : ZMod p) = (-1 : ZMod p) ^ (k + 1) * (k + 1 : ZMod p) := by
      rw [pow_add, pow_one]; ring
    rw [h_mul] at h_zmod
    have hk1 : (k + 1 : ZMod p) ≠ 0 := by
      intro hc
      have hc2 : ((k + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact hc
      have : p ∣ (k + 1) := (CharP.cast_eq_zero_iff (ZMod p) p (k + 1)).mp hc2
      have h_mod : (k + 1) % p = k + 1 := Nat.mod_eq_of_lt hk
      have : (k + 1) % p = 0 := Nat.mod_eq_zero_of_dvd this
      rw [h_mod] at this
      omega
    exact mul_right_cancel₀ hk1 h_zmod

lemma sum_neg_one_pow_m {p : ℕ} [Fact p.Prime] (m : ℕ) :
  ∑ k ∈ range (2 * m + 1), (-1 : ZMod p) ^ k = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have : 2 * (m + 1) + 1 = 2 * m + 1 + 2 := by ring
    rw [this, sum_range_add, ih]
    have h_sum2 : ∑ x ∈ range 2, (-1 : ZMod p) ^ (2 * m + 1 + x) = 0 := by
      rw [sum_range_succ, sum_range_one]
      have h_pow_2m : (-1 : ZMod p) ^ (2 * m) = 1 := by
        have : (-1 : ZMod p) ^ (2 * m) = ((-1 : ZMod p) ^ 2) ^ m := by exact pow_mul (-1 : ZMod p) 2 m
        rw [this]
        have h1 : (-1 : ZMod p) ^ 2 = 1 := by ring
        rw [h1, one_pow]
      have : (-1 : ZMod p) ^ (2 * m + 1 + 0) = -1 := by
        have h_add : 2 * m + 1 + 0 = 2 * m + 1 := by ring
        rw [h_add, pow_add, h_pow_2m, pow_one, one_mul]
      rw [this]
      have : (-1 : ZMod p) ^ (2 * m + 1 + 1) = 1 := by
        have h_add : 2 * m + 1 + 1 = 2 * m + 2 := by ring
        rw [h_add, pow_add, h_pow_2m]
        have h2 : (-1 : ZMod p) ^ 2 = 1 := by ring
        rw [h2, mul_one]
      rw [this]; ring
    rw [h_sum2]; ring

lemma a_p_minus_one (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) :
  (a (p - 1) : ZMod p) = 1 := by
  unfold a
  push_cast
  have h_eq : p - 1 + 1 = p := by
    have hp_pos : p ≥ 1 := Nat.Prime.pos hp.out
    omega
  have h_sum : ∑ k ∈ range (p - 1 + 1), (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 4 =
               ∑ k ∈ range p, (-1 : ZMod p) ^ k := by
    rw [h_eq]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have h_mod := choose_p_minus_one p k hk
    rw [h_mod]
    have : (-1 : ZMod p) ^ k * ((-1 : ZMod p) ^ k) ^ 4 = (-1 : ZMod p) ^ k := by
      have : ((-1 : ZMod p) ^ k) ^ 4 = (-1 : ZMod p) ^ (k * 4) := by exact (pow_mul (-1 : ZMod p) k 4).symm
      rw [this]
      have : (-1 : ZMod p) ^ (k * 4) = ((-1 : ZMod p) ^ 2) ^ (k * 2) := by
        have h4 : k * 4 = 2 * (k * 2) := by ring
        rw [h4, pow_mul]
      rw [this]
      have h_one : (-1 : ZMod p) ^ 2 = 1 := by ring
      rw [h_one, one_pow, mul_one]
    exact this
  rw [h_sum]
  have hp_odd2 : Odd p := odd_p hp.out hp_odd
  rcases hp_odd2 with ⟨m, hm⟩
  have h_sum_m := sum_neg_one_pow_m (p := p) m
  have h_eq2 : range p = range (2 * m + 1) := by rw [hm]
  rw [h_eq2]
  exact h_sum_m

lemma choose_mod_p {p m k : ℕ} [hp : Fact p.Prime] (hm : m < p) (hk1 : m < k) (hk2 : k < p) :
  (choose (p + m) k : ZMod p) = 0 := by
  have h := choose_modEq_choose_mod_mul_choose_div (n := p + m) (k := k) (p := p)
  have h_zmod : (choose (p + m) k : ZMod p) = (choose ((p + m) % p) (k % p) : ZMod p) * (choose ((p + m) / p) (k / p) : ZMod p) := by
    rw [← ZMod.intCast_eq_intCast_iff] at h
    push_cast at h ⊢; exact h
  have h1 : (p + m) % p = m := by rw [add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
  have h2 : k % p = k := Nat.mod_eq_of_lt hk2
  have h4 : k / p = 0 := Nat.div_eq_of_lt hk2
  rw [h1, h2, h4] at h_zmod
  have h5 : choose m k = 0 := choose_eq_zero_of_lt hk1
  rw [h5] at h_zmod
  push_cast at h_zmod
  simp at h_zmod
  exact h_zmod

lemma choose_mod_p_ge {p m j : ℕ} [hp : Fact p.Prime] (hm : m < p) (hj : j < p) :
  (choose (p + m) (p + j) : ZMod p) = (choose m j : ZMod p) := by
  have h := choose_modEq_choose_mod_mul_choose_div (n := p + m) (k := p + j) (p := p)
  have h_zmod : (choose (p + m) (p + j) : ZMod p) = (choose ((p + m) % p) ((p + j) % p) : ZMod p) * (choose ((p + m) / p) ((p + j) / p) : ZMod p) := by
    rw [← ZMod.intCast_eq_intCast_iff] at h
    push_cast at h ⊢; exact h
  have h1 : (p + m) % p = m := by rw [add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
  have h2 : (p + j) % p = j := by rw [add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  have h3 : (p + m) / p = 1 := by
    rw [add_comm, Nat.add_div_right _ (Nat.Prime.pos hp.out)]
    have : m / p = 0 := Nat.div_eq_of_lt hm
    rw [this, zero_add]
  have h4 : (p + j) / p = 1 := by
    rw [add_comm, Nat.add_div_right _ (Nat.Prime.pos hp.out)]
    have : j / p = 0 := Nat.div_eq_of_lt hj
    rw [this, zero_add]
  rw [h1, h2, h3, h4] at h_zmod
  have h5 : choose 1 1 = 1 := rfl
  rw [h5] at h_zmod
  push_cast at h_zmod; simp at h_zmod; exact h_zmod

lemma sum_split_test (p m : ℕ) (f : ℕ → ZMod p) :
  ∑ k ∈ range (p + m + 1), f k = (∑ k ∈ range p, f k) + (∑ j ∈ range (m + 1), f (p + j)) := by
  have : p ≤ p + m + 1 := by omega
  rw [← sum_range_add_sum_Ico f this]
  congr 1
  rw [sum_Ico_eq_sum_range]
  congr
  omega

lemma sum_split_range_p (p m : ℕ) (hm : m < p) (f : ℕ → ZMod p) :
  ∑ k ∈ range p, f k = (∑ k ∈ range (m + 1), f k) + (∑ j ∈ Ico (m + 1) p, f j) := by
  have : m + 1 ≤ p := hm
  rw [← sum_range_add_sum_Ico f this]

lemma a_p_add_m (p m : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hm : m < p - 1) :
  (a (p + m) : ZMod p) = 0 := by
  have hm2 : m < p := by omega
  unfold a
  push_cast
  have h_split := sum_split_test p m (fun k => (-1 : ZMod p) ^ k * (choose (p + m) k : ZMod p) ^ 4)
  rw [h_split]
  have h_split2 := sum_split_range_p p m hm2 (fun k => (-1 : ZMod p) ^ k * (choose (p + m) k : ZMod p) ^ 4)
  rw [h_split2]
  have h_zero : ∑ j ∈ Ico (m + 1) p, (-1 : ZMod p) ^ j * (choose (p + m) j : ZMod p) ^ 4 = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [mem_Ico] at hj
    have h_mod := choose_mod_p hm2 hj.1 hj.2
    rw [h_mod]
    ring
  rw [h_zero, add_zero]
  have h_second : ∑ j ∈ range (m + 1), (-1 : ZMod p) ^ (p + j) * (choose (p + m) (p + j) : ZMod p) ^ 4 = 
                  ∑ j ∈ range (m + 1), - ((-1 : ZMod p) ^ j * (choose m j : ZMod p) ^ 4) := by
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    have hj_p : j < p := by omega
    have h_mod := choose_mod_p_ge hm2 hj_p
    rw [h_mod]
    have h_sign : (-1 : ZMod p) ^ (p + j) = - (-1 : ZMod p) ^ j := by
      rw [pow_add]
      have hp_odd2 : Odd p := odd_p hp.out hp_odd
      rcases hp_odd2 with ⟨k, hk⟩
      have h_neg1 : (-1 : ZMod p) ^ p = -1 := by
        have : (-1 : ZMod p) ^ p = (-1 : ZMod p) ^ (2 * k + 1) := by congr 1
        rw [this, pow_add, pow_mul]
        have : (-1 : ZMod p) ^ 2 = 1 := by ring
        rw [this, one_pow, one_mul, pow_one]
      rw [h_neg1]
      ring
    rw [h_sign]
    ring
  rw [h_second]
  have h_first : ∑ k ∈ range (m + 1), (-1 : ZMod p) ^ k * (choose (p + m) k : ZMod p) ^ 4 =
                 ∑ k ∈ range (m + 1), (-1 : ZMod p) ^ k * (choose m k : ZMod p) ^ 4 := by
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have hk_p : k < p := by omega
    have h_mod := choose_modEq_choose_mod_mul_choose_div (n := p + m) (k := k) (p := p)
    have h_zmod : (choose (p + m) k : ZMod p) = (choose ((p + m) % p) (k % p) : ZMod p) * (choose ((p + m) / p) (k / p) : ZMod p) := by
      rw [← ZMod.intCast_eq_intCast_iff] at h_mod
      push_cast at h_mod ⊢; exact h_mod
    have h1 : (p + m) % p = m := by rw [add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hm2]
    have h2 : k % p = k := Nat.mod_eq_of_lt hk_p
    have h4 : k / p = 0 := Nat.div_eq_of_lt hk_p
    rw [h1, h2, h4] at h_zmod
    have h5 : choose ((p + m) / p) 0 = 1 := Nat.choose_zero_right _
    rw [h5] at h_zmod
    push_cast at h_zmod
    rw [h_zmod]
    ring
  rw [h_first, ← sum_add_distrib]
  apply sum_eq_zero
  intro x _
  ring

lemma choose_two_mul_mod_p {p u : ℕ} [hp : Fact p.Prime] (hu : u < p) :
  (choose (2 * p + 2 * u) (p + u) : ZMod p) = 2 * (choose (2 * u) u : ZMod p) := by
  by_cases h2u : p ≤ 2 * u
  · have hu_2p : 2 * u < 2 * p := Nat.mul_lt_mul_of_pos_left hu (by decide)
    have hu_mod : (2 * u) % p = 2 * u - p := by rw [Nat.mod_eq_sub_mod h2u, Nat.mod_eq_of_lt (by omega)]
    have hu2 : (choose (2 * u) u : ZMod p) = 0 := by
      have h := choose_modEq_choose_mod_mul_choose_div (n := 2 * u) (k := u) (p := p)
      have h_zmod : (choose (2 * u) u : ZMod p) = (choose ((2 * u) % p) (u % p) : ZMod p) * (choose ((2 * u) / p) (u / p) : ZMod p) := by
        rw [← ZMod.intCast_eq_intCast_iff] at h
        push_cast at h ⊢; exact h
      have h1 : u % p = u := Nat.mod_eq_of_lt hu
      rw [h1] at h_zmod
      have : choose ((2 * u) % p) u = 0 := by apply choose_eq_zero_of_lt; rw [hu_mod]; omega
      rw [this] at h_zmod
      push_cast at h_zmod; simp at h_zmod; exact h_zmod
    have hu3 : (choose (2 * p + 2 * u) (p + u) : ZMod p) = 0 := by
      have h := choose_modEq_choose_mod_mul_choose_div (n := 2 * p + 2 * u) (k := p + u) (p := p)
      have h_zmod : (choose (2 * p + 2 * u) (p + u) : ZMod p) = (choose ((2 * p + 2 * u) % p) ((p + u) % p) : ZMod p) * (choose ((2 * p + 2 * u) / p) ((p + u) / p) : ZMod p) := by
        rw [← ZMod.intCast_eq_intCast_iff] at h
        push_cast at h ⊢; exact h
      have h1 : (p + u) % p = u := by rw [add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hu]
      have h2 : (2 * p + 2 * u) % p = (2 * u) % p := by
        have : 2 * p = p * 2 := mul_comm _ _
        rw [this, add_comm, Nat.add_mul_mod_self_left]
      rw [h1, h2] at h_zmod
      have : choose ((2 * u) % p) u = 0 := by apply choose_eq_zero_of_lt; rw [hu_mod]; omega
      rw [this] at h_zmod
      push_cast at h_zmod; simp at h_zmod; exact h_zmod
    rw [hu2, hu3]
    ring
  · push_neg at h2u
    have h2u_lt : 2 * u < p := h2u
    have h := choose_modEq_choose_mod_mul_choose_div (n := 2 * p + 2 * u) (k := p + u) (p := p)
    have h_zmod : (choose (2 * p + 2 * u) (p + u) : ZMod p) = (choose ((2 * p + 2 * u) % p) ((p + u) % p) : ZMod p) * (choose ((2 * p + 2 * u) / p) ((p + u) / p) : ZMod p) := by
      rw [← ZMod.intCast_eq_intCast_iff] at h
      push_cast at h ⊢; exact h
    have h1 : (2 * p + 2 * u) % p = 2 * u := by
      have : 2 * p = p * 2 := mul_comm _ _
      rw [this, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2u_lt]
    have h2 : (p + u) % p = u := by rw [add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hu]
    have h3 : (2 * p + 2 * u) / p = 2 := by
      have : 2 * p = p * 2 := mul_comm _ _
      rw [this, add_comm, Nat.add_mul_div_left _ _ (Nat.Prime.pos hp.out)]
      have : 2 * u / p = 0 := Nat.div_eq_of_lt h2u_lt
      rw [this, zero_add]
    have h4 : (p + u) / p = 1 := by
      rw [add_comm, Nat.add_div_right _ (Nat.Prime.pos hp.out)]
      have : u / p = 0 := Nat.div_eq_of_lt hu
      rw [this, zero_add]
    rw [h1, h2, h3, h4] at h_zmod
    have h5 : choose 2 1 = 2 := rfl
    rw [h5] at h_zmod
    push_cast at h_zmod; rw [h_zmod]; ring

lemma c_p_add_m (p m : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hm : m < p - 1) :
  (c (p + m) : ZMod p) = 0 := by
  have hm2 : m < p := by omega
  unfold c
  push_cast
  have h_split := sum_split_test p m (fun k => (-1 : ZMod p) ^ k * (choose (p + m) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p + m - k)) (p + m - k) : ZMod p))
  rw [h_split]
  have h_split2 := sum_split_range_p p m hm2 (fun k => (-1 : ZMod p) ^ k * (choose (p + m) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p + m - k)) (p + m - k) : ZMod p))
  rw [h_split2]
  have h_zero : ∑ j ∈ Ico (m + 1) p, (-1 : ZMod p) ^ j * (choose (p + m) j : ZMod p) ^ 2 * (choose (2 * j) j : ZMod p) * (choose (2 * (p + m - j)) (p + m - j) : ZMod p) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [mem_Ico] at hj
    have h_mod := choose_mod_p hm2 hj.1 hj.2
    rw [h_mod]
    ring
  rw [h_zero, add_zero]
  have h_second : ∑ j ∈ range (m + 1), (-1 : ZMod p) ^ (p + j) * (choose (p + m) (p + j) : ZMod p) ^ 2 * (choose (2 * (p + j)) (p + j) : ZMod p) * (choose (2 * (p + m - (p + j))) (p + m - (p + j)) : ZMod p) =
                  ∑ j ∈ range (m + 1), - ((-1 : ZMod p) ^ j * (choose m j : ZMod p) ^ 2 * 2 * (choose (2 * j) j : ZMod p) * (choose (2 * (m - j)) (m - j) : ZMod p)) := by
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    have hj_p : j < p := by omega
    have h_mod := choose_mod_p_ge hm2 hj_p
    rw [h_mod]
    have h_sign : (-1 : ZMod p) ^ (p + j) = - (-1 : ZMod p) ^ j := by
      rw [pow_add]
      have hp_odd2 : Odd p := odd_p hp.out hp_odd
      rcases hp_odd2 with ⟨k, hk⟩
      have h_neg1 : (-1 : ZMod p) ^ p = -1 := by
        have : (-1 : ZMod p) ^ p = (-1 : ZMod p) ^ (2 * k + 1) := by congr 1
        rw [this, pow_add, pow_mul]
        have : (-1 : ZMod p) ^ 2 = 1 := by ring
        rw [this, one_pow, one_mul, pow_one]
      rw [h_neg1]
      ring
    rw [h_sign]
    have h_sub : p + m - (p + j) = m - j := by omega
    rw [h_sub]
    have h_mul : 2 * (p + j) = 2 * p + 2 * j := by ring
    rw [h_mul]
    have h_two := choose_two_mul_mod_p hj_p
    rw [h_two]
    ring
  rw [h_second]
  have h_first : ∑ k ∈ range (m + 1), (-1 : ZMod p) ^ k * (choose (p + m) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p + m - k)) (p + m - k) : ZMod p) =
                 ∑ k ∈ range (m + 1), (-1 : ZMod p) ^ k * (choose m k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * 2 * (choose (2 * (m - k)) (m - k) : ZMod p) := by
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have hk_p : k < p := by omega
    have h_mod := choose_modEq_choose_mod_mul_choose_div (n := p + m) (k := k) (p := p)
    have h_zmod : (choose (p + m) k : ZMod p) = (choose ((p + m) % p) (k % p) : ZMod p) * (choose ((p + m) / p) (k / p) : ZMod p) := by
      rw [← ZMod.intCast_eq_intCast_iff] at h_mod
      push_cast at h_mod ⊢; exact h_mod
    have h1 : (p + m) % p = m := by rw [add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hm2]
    have h2 : k % p = k := Nat.mod_eq_of_lt hk_p
    have h4 : k / p = 0 := Nat.div_eq_of_lt hk_p
    rw [h1, h2, h4] at h_zmod
    have h5 : choose ((p + m) / p) 0 = 1 := Nat.choose_zero_right _
    rw [h5] at h_zmod
    push_cast at h_zmod
    rw [h_zmod]
    have h_sub2 : p + m - k = p + (m - k) := by omega
    have h_mul2 : 2 * (p + (m - k)) = 2 * p + 2 * (m - k) := by ring
    rw [h_sub2, h_mul2]
    have hmk_lt : m - k < p := by omega
    have h_two2 := choose_two_mul_mod_p hmk_lt
    rw [h_two2]
    ring
  rw [h_first, ← sum_add_distrib]
  apply sum_eq_zero
  intro x _
  ring

lemma choose_two_k_zero (p m k : ℕ) [hp : Fact p.Prime] (hm : p = 2 * m + 1) (hk1 : m < k) (hk2 : k < p) :
  (choose (2 * k) k : ZMod p) = 0 := by
  have h := choose_modEq_choose_mod_mul_choose_div (n := 2 * k) (k := k) (p := p)
  have h_zmod : (choose (2 * k) k : ZMod p) = (choose ((2 * k) % p) (k % p) : ZMod p) * (choose ((2 * k) / p) (k / p) : ZMod p) := by
    rw [← ZMod.intCast_eq_intCast_iff] at h
    push_cast at h ⊢; exact h
  have h_k_mod : k % p = k := Nat.mod_eq_of_lt hk2
  have h_k_div : k / p = 0 := Nat.div_eq_of_lt hk2
  have h_2k_lt : 2 * k < 2 * p := Nat.mul_lt_mul_of_pos_left hk2 (by decide)
  have h_2k_ge : 2 * k ≥ p := by omega
  have h_2k_mod : (2 * k) % p = 2 * k - p := by rw [Nat.mod_eq_sub_mod h_2k_ge, Nat.mod_eq_of_lt (by omega)]
  rw [h_k_mod, h_k_div] at h_zmod
  have h_zero : choose ((2 * k) % p) k = 0 := by apply choose_eq_zero_of_lt; rw [h_2k_mod]; omega
  rw [h_zero] at h_zmod
  push_cast at h_zmod; simp at h_zmod; exact h_zmod

lemma c_p_minus_one (p m : ℕ) [hp : Fact p.Prime] (hm : p = 2 * m + 1) :
  (c (p - 1) : ZMod p) = (-1 : ZMod p) ^ m := by
  unfold c
  push_cast
  have h_eq : p - 1 + 1 = p := by omega
  have h_sum : ∑ k ∈ range (p - 1 + 1), (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) =
               ∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) := by
    rw [h_eq]
  rw [h_sum]
  have h_split : ∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) =
                 ∑ k ∈ {m}, (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) := by
    symm
    apply sum_subset
    · intro x hx
      rw [mem_singleton] at hx
      rw [hx, mem_range]
      omega
    · intro k hk h_neq
      rw [mem_range] at hk
      rw [mem_singleton] at h_neq
      by_cases hk_lt : k < m
      · have h1 : p - 1 - k > m := by omega
        have h2 : p - 1 - k < p := by omega
        have h_zero := choose_two_k_zero p m (p - 1 - k) hm h1 h2
        rw [h_zero]
        ring
      · have h1 : k > m := by omega
        have h_zero := choose_two_k_zero p m k hm h1 hk
        rw [h_zero]
        ring
  rw [h_split, sum_singleton]
  have h_m : p - 1 - m = m := by omega
  rw [h_m]
  have hm_lt : m < p := by omega
  have h_mod := choose_p_minus_one p m hm_lt
  have h_2m : 2 * m = p - 1 := by omega
  have h_choose_2m : (choose (2 * m) m : ZMod p) = (choose (p - 1) m : ZMod p) := by rw [h_2m]
  rw [h_choose_2m, h_mod]
  have h_pow_2m : (-1 : ZMod p) ^ (2 * m) = 1 := by
    have : (-1 : ZMod p) ^ (2 * m) = ((-1 : ZMod p) ^ 2) ^ m := by exact pow_mul (-1 : ZMod p) 2 m
    rw [this]
    have h1 : (-1 : ZMod p) ^ 2 = 1 := by ring
    rw [h1, one_pow]
  have h_pow_mul : (-1 : ZMod p) ^ m * ((-1 : ZMod p) ^ m) ^ 2 * (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m = (-1 : ZMod p) ^ m := by
    have h1 : ((-1 : ZMod p) ^ m) ^ 2 = (-1 : ZMod p) ^ (2 * m) := by
      have h_symm : m * 2 = 2 * m := by ring
      rw [← pow_mul, h_symm]
    rw [h1, h_pow_2m]
    calc (-1 : ZMod p) ^ m * 1 * (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m
      _ = ((-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m) * (-1 : ZMod p) ^ m := by ring
      _ = (-1 : ZMod p) ^ (2 * m) * (-1 : ZMod p) ^ m := by
        have : (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m = (-1 : ZMod p) ^ (2 * m) := by
          rw [← pow_add]
          have : m + m = 2 * m := by ring
          rw [this]
        rw [this]
      _ = 1 * (-1 : ZMod p) ^ m := by rw [h_pow_2m]
      _ = (-1 : ZMod p) ^ m := by ring
  exact h_pow_mul

lemma sum_val_fin (p : ℕ) : ∑ i : Fin p, i.val = p * (p - 1) / 2 := by
  have h := sum_range_id p
  have h2 : ∑ i ∈ range p, i = ∑ i : Fin p, i.val := by
    exact (Fin.sum_univ_eq_sum_range (fun i => i) p).symm
  rw [← h2]
  exact h

lemma mul_sub_two (p : ℕ) : p * (p - 1) = p * (p - 1) / 2 * 2 := by
  have h2 : 2 ∣ p * (p - 1) := by
    by_cases hp : p = 0
    · rw [hp]; simp
    · have hp2 : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.pos_of_ne_zero hp)
      have := Nat.even_mul_succ_self (p - 1)
      rw [hp2] at this
      have : 2 ∣ (p - 1) * p := even_iff_two_dvd.mp this
      rw [mul_comm] at this
      exact this
  exact (Nat.div_mul_cancel h2).symm

lemma perm_eq_rev (p : ℕ) (σ : Perm (Fin p)) (h : ∀ i : Fin p, (σ i).val + i.val ≤ p - 1) :
  ∀ i : Fin p, (σ i).val + i.val = p - 1 := by
  have h_sum1 : ∑ i : Fin p, ((σ i).val + i.val) = p * (p - 1) := by
    rw [sum_add_distrib]
    have h_bij : ∑ i : Fin p, (σ i).val = ∑ i : Fin p, i.val := by
      exact Fintype.sum_bijective σ σ.bijective _ _ (fun _ => rfl)
    rw [h_bij, sum_val_fin]
    have h3 : p * (p - 1) / 2 + p * (p - 1) / 2 = p * (p - 1) / 2 * 2 := by ring
    rw [h3]
    exact (mul_sub_two p).symm
  have h_sum2 : ∑ i : Fin p, (p - 1) = p * (p - 1) := by simp
  have h_sum_eq : ∑ i : Fin p, ((σ i).val + i.val) = ∑ i : Fin p, (p - 1) := by rw [h_sum1, h_sum2]
  have h_all := sum_eq_sum_iff_of_le (fun i _ => h i) |>.mp h_sum_eq
  intro i
  exact h_all i (mem_univ i)

def revPerm (p : ℕ) (hp : 0 < p) : Perm (Fin p) :=
  { toFun := fun i => ⟨p - 1 - i.val, by omega⟩
    invFun := fun i => ⟨p - 1 - i.val, by omega⟩
    left_inv := by intro i; ext; simp; omega
    right_inv := by intro i; ext; simp; omega }

lemma det_anti_triangular_zmod (p : ℕ) [Fact p.Prime] (hp : 0 < p) (M : Matrix (Fin p) (Fin p) (ZMod p))
  (h_zero : ∀ i j : Fin p, i.val + j.val ≥ p → M i j = 0) :
  M.det = ((sign (revPerm p hp) : ℤ) : ZMod p) * ∏ i : Fin p, M (revPerm p hp i) i := by
  rw [det_apply]
  have h_eq : ∑ σ : Perm (Fin p), ((sign σ : ℤ) : ZMod p) * ∏ i, M (σ i) i =
              ∑ σ ∈ ({revPerm p hp} : Finset (Perm (Fin p))), ((sign σ : ℤ) : ZMod p) * ∏ i, M (σ i) i := by
    symm
    apply sum_subset
    · intro _ _; exact mem_univ _
    · intro σ _ h_neq
      have h_not_rev : ¬ ∀ i, (σ i).val + i.val = p - 1 := by
        intro hc
        have : σ = revPerm p hp := by
          ext i
          have hci := hc i
          have : (σ i).val = p - 1 - i.val := by omega
          exact this
        rw [mem_singleton] at h_neq
        exact h_neq this
      have h_not_le : ¬ ∀ i, (σ i).val + i.val ≤ p - 1 := fun hc => h_not_rev (perm_eq_rev p σ hc)
      push_neg at h_not_le
      rcases h_not_le with ⟨i, hi⟩
      have hi2 : (σ i).val + i.val ≥ p := by omega
      have h_zero2 : M (σ i) i = 0 := h_zero _ _ hi2
      have h_prod_zero : ∏ i : Fin p, M (σ i) i = 0 := prod_eq_zero (mem_univ i) h_zero2
      rw [h_prod_zero, mul_zero]
  have h_smul : ∑ σ : Perm (Fin p), sign σ • ∏ i, M (σ i) i = ∑ σ : Perm (Fin p), ((sign σ : ℤ) : ZMod p) * ∏ i, M (σ i) i := by
    apply sum_congr rfl
    intro σ _
    rw [Units.smul_def]
    exact zsmul_eq_mul (∏ i : Fin p, M (σ i) i) (↑(sign σ) : ℤ)
  rw [h_smul, h_eq]
  simp

def JMat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i.val + j.val = n - 1 then 1 else 0

lemma div_two (n : ℕ) : (n + 1) * n / 2 = n + n * (n - 1) / 2 := by
  by_cases h : n = 0
  · simp [h]
  · have h1 : 1 ≤ n := Nat.pos_of_ne_zero h
    have h2 : (n + 1) * n = 2 * n + n * (n - 1) := by zify [h1]; ring
    rw [h2]
    have h3 : (2 * n + n * (n - 1)) / 2 = n + n * (n - 1) / 2 := by
      have h4 : (n * (n - 1) + 2 * n) / 2 = n * (n - 1) / 2 + n := Nat.add_mul_div_left (n * (n - 1)) n (by decide : 0 < 2)
      have h5 : 2 * n + n * (n - 1) = n * (n - 1) + 2 * n := by ring
      rw [h5, h4, add_comm]
    exact h3

lemma det_JMat (n : ℕ) : (JMat n).det = (-1 : ℤ) ^ (n * (n - 1) / 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [det_succ_row_zero]
    have h_sum : ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val * JMat (n + 1) 0 j * (submatrix (JMat (n + 1)) Fin.succ j.succAbove).det =
                 (-1 : ℤ) ^ n * 1 * (submatrix (JMat (n + 1)) Fin.succ (Fin.last n).succAbove).det := by
      have : ∑ j ∈ ({Fin.last n} : Finset (Fin (n+1))), (-1 : ℤ) ^ j.val * JMat (n + 1) 0 j * (submatrix (JMat (n + 1)) Fin.succ j.succAbove).det =
             ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val * JMat (n + 1) 0 j * (submatrix (JMat (n + 1)) Fin.succ j.succAbove).det := by
        apply sum_subset
        · intro _ _; exact mem_univ _
        · intro j _ hj
          rw [mem_singleton] at hj
          have : j.val ≠ n := fun hc => hj (Fin.ext hc)
          have : JMat (n + 1) 0 j = 0 := by
            unfold JMat
            have h_if : ¬ ((0 : Fin (n+1)).val + j.val = n + 1 - 1) := by
              have : (0 : Fin (n+1)).val = 0 := rfl
              omega
            rw [if_neg h_if]
          rw [this, mul_zero, zero_mul]
      rw [← this, sum_singleton]
      congr 1
      have h_val : JMat (n + 1) 0 (Fin.last n) = 1 := by
        unfold JMat
        have h_if : (0 : Fin (n+1)).val + (Fin.last n).val = n + 1 - 1 := by
          have : (0 : Fin (n+1)).val = 0 := rfl
          have : (Fin.last n).val = n := rfl
          omega
        rw [if_pos h_if]
      rw [h_val]
      have : (Fin.last n).val = n := rfl
      rw [this]
    rw [h_sum]
    have h_submatrix : submatrix (JMat (n + 1)) Fin.succ (Fin.last n).succAbove = JMat n := by
      ext i j
      unfold JMat submatrix
      simp
      by_cases h : i.val + j.val = n - 1
      · have h_pos : i.val + 1 + j.val = n := by omega
        rw [if_pos h_pos, if_pos h]
      · have h_neg : ¬ (i.val + 1 + j.val = n) := by omega
        rw [if_neg h_neg, if_neg h]
    rw [h_submatrix, ih]
    have : (-1 : ℤ) ^ n * 1 * (-1 : ℤ) ^ (n * (n - 1) / 2) = (-1 : ℤ) ^ ((n + 1) * n / 2) := by
      rw [mul_one, ← pow_add]
      congr 1
      have : n + n * (n - 1) / 2 = (n + 1) * n / 2 := (div_two n).symm
      exact this
    exact this

lemma det_anti_triangular (p : ℕ) (hp : 0 < p) (M : Matrix (Fin p) (Fin p) ℤ)
  (h_zero : ∀ i j : Fin p, i.val + j.val ≥ p → M i j = 0) :
  M.det = (sign (revPerm p hp) : ℤ) * ∏ i : Fin p, M (revPerm p hp i) i := by
  rw [det_apply]
  have h_eq : ∑ σ : Perm (Fin p), (sign σ : ℤ) * ∏ i, M (σ i) i =
              ∑ σ ∈ ({revPerm p hp} : Finset (Perm (Fin p))), (sign σ : ℤ) * ∏ i, M (σ i) i := by
    symm
    apply sum_subset
    · intro _ _; exact mem_univ _
    · intro σ _ h_neq
      have h_not_rev : ¬ ∀ i, (σ i).val + i.val = p - 1 := by
        intro hc
        have : σ = revPerm p hp := by
          ext i
          have hci := hc i
          have : (σ i).val = p - 1 - i.val := by omega
          exact this
        rw [mem_singleton] at h_neq
        exact h_neq this
      have h_not_le : ¬ ∀ i, (σ i).val + i.val ≤ p - 1 := fun hc => h_not_rev (perm_eq_rev p σ hc)
      push_neg at h_not_le
      rcases h_not_le with ⟨i, hi⟩
      have hi2 : (σ i).val + i.val ≥ p := by omega
      have h_zero2 : M (σ i) i = 0 := h_zero _ _ hi2
      have h_prod_zero : ∏ i : Fin p, M (σ i) i = 0 := prod_eq_zero (mem_univ i) h_zero2
      rw [h_prod_zero, mul_zero]
  have h_smul : ∑ σ : Perm (Fin p), sign σ • ∏ i, M (σ i) i = ∑ σ : Perm (Fin p), (sign σ : ℤ) * ∏ i, M (σ i) i := by
    apply sum_congr rfl
    intro σ _
    exact Units.smul_def _ _
  rw [h_smul, h_eq]
  simp

lemma sign_revPerm (p : ℕ) (hp : 0 < p) : (sign (revPerm p hp) : ℤ) = (-1 : ℤ) ^ (p * (p - 1) / 2) := by
  have h_anti := det_anti_triangular p hp (JMat p) (by
    intro i j hij
    unfold JMat
    have : i.val + j.val ≠ p - 1 := by omega
    rw [if_neg this]
  )
  have h_det := det_JMat p
  rw [h_det] at h_anti
  have h_prod : ∏ i : Fin p, JMat p (revPerm p hp i) i = 1 := by
    apply prod_eq_one
    intro i _
    unfold JMat
    have : (revPerm p hp i).val + i.val = p - 1 := by
      have : (revPerm p hp i).val = p - 1 - i.val := rfl
      omega
    rw [if_pos this]
  rw [h_prod, mul_one] at h_anti
  exact h_anti.symm

lemma neg_one_pow_p_mul_m (p m : ℕ) (hm : p = 2 * m + 1) [Fact p.Prime] :
  (-1 : ZMod p) ^ (p * m) = (-1 : ZMod p) ^ m := by
  have : (-1 : ZMod p) ^ (p * m) = ((-1 : ZMod p) ^ p) ^ m := by
    exact pow_mul (-1 : ZMod p) p m
  rw [this]
  have hp_pow : (-1 : ZMod p) ^ p = -1 := by
    have h_p : (-1 : ZMod p) ^ p = (-1 : ZMod p) ^ (2 * m + 1) := by congr 1
    rw [h_p]
    have : (-1 : ZMod p) ^ (2 * m + 1) = ((-1 : ZMod p) ^ 2) ^ m * (-1 : ZMod p) := by
      rw [pow_add, pow_mul (-1 : ZMod p) 2 m, pow_one]
    rw [this]
    have h2 : (-1 : ZMod p) ^ 2 = 1 := by ring
    rw [h2, one_pow, one_mul]
  rw [hp_pow]

theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  intro N half_minus_one A C
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have hp_pos : 0 < p := Nat.Prime.pos hp
  have hA_mod : (A.det : ZMod p) = (-1 : ZMod p) ^ half_minus_one := by
    let A_zmod : Matrix N N (ZMod p) := fun i j => (A i j : ZMod p)
    have h_detA : (A.det : ZMod p) = A_zmod.det := by
      exact RingHom.map_det (Int.castRingHom (ZMod p)) A
    rw [h_detA]
    have h_anti := det_anti_triangular_zmod p hp_pos A_zmod (by
      intro i j hij
      have h_m : i.val + j.val - p < p - 1 := by omega
      have h_eq : i.val + j.val = p + (i.val + j.val - p) := by omega
      have h_a := a_p_add_m p (i.val + j.val - p) h_odd h_m
      have : A_zmod i j = (a (i.val + j.val) : ZMod p) := rfl
      rw [this, h_eq, h_a]
    )
    rw [h_anti]
    have h_prod : ∏ i : Fin p, A_zmod (revPerm p hp_pos i) i = 1 := by
      have : ∀ i ∈ univ, A_zmod (revPerm p hp_pos i) i = 1 := by
        intro i _
        have h_sum : (revPerm p hp_pos i).val + i.val = p - 1 := by
          have : (revPerm p hp_pos i).val = p - 1 - i.val := rfl
          omega
        have : A_zmod (revPerm p hp_pos i) i = (a (p - 1) : ZMod p) := by
          have : A_zmod (revPerm p hp_pos i) i = (a ((revPerm p hp_pos i).val + i.val) : ZMod p) := rfl
          rw [this, h_sum]
        rw [this]
        exact a_p_minus_one p h_odd
      rw [prod_congr rfl this, prod_const, one_pow]
    rw [h_prod, mul_one]
    have h_sign := sign_revPerm p hp_pos
    have h_sign_zmod : ((sign (revPerm p hp_pos) : ℤ) : ZMod p) = ((-1 : ZMod p) ^ (p * (p - 1) / 2)) := by
      rw [h_sign]
      push_cast
      rfl
    rw [h_sign_zmod]
    have hp_odd2 : Odd p := odd_p hp h_odd
    rcases hp_odd2 with ⟨m, hm⟩
    have h1 : p * (p - 1) / 2 = p * m := by
      have h_pm1 : p - 1 = 2 * m := by omega
      rw [h_pm1]
      have h_mul : p * (2 * m) = 2 * (p * m) := by ring
      rw [h_mul]
      exact Nat.mul_div_cancel_left (p * m) (by decide)
    have h2 : (p - 1) / 2 = m := by omega
    change (-1 : ZMod p) ^ (p * (p - 1) / 2) = (-1 : ZMod p) ^ ((p - 1) / 2)
    rw [h1, h2]
    exact neg_one_pow_p_mul_m p m hm
  have hC_mod : (C.det : ZMod p) = 1 := by
    let C_zmod : Matrix N N (ZMod p) := fun i j => (C i j : ZMod p)
    have h_detC : (C.det : ZMod p) = C_zmod.det := by
      exact RingHom.map_det (Int.castRingHom (ZMod p)) C
    rw [h_detC]
    have h_anti := det_anti_triangular_zmod p hp_pos C_zmod (by
      intro i j hij
      have h_m : i.val + j.val - p < p - 1 := by omega
      have h_eq : i.val + j.val = p + (i.val + j.val - p) := by omega
      have h_c := c_p_add_m p (i.val + j.val - p) h_odd h_m
      have : C_zmod i j = (c (i.val + j.val) : ZMod p) := rfl
      rw [this, h_eq, h_c]
    )
    rw [h_anti]
    have hp_odd2 : Odd p := odd_p hp h_odd
    rcases hp_odd2 with ⟨m, hm⟩
    have h_prod : ∏ i : Fin p, C_zmod (revPerm p hp_pos i) i = ((-1 : ZMod p) ^ m) ^ p := by
      have h_const : ∀ i ∈ univ, C_zmod (revPerm p hp_pos i) i = (-1 : ZMod p) ^ m := by
        intro i _
        have h_sum : (revPerm p hp_pos i).val + i.val = p - 1 := by
          have : (revPerm p hp_pos i).val = p - 1 - i.val := rfl
          omega
        have : C_zmod (revPerm p hp_pos i) i = (c (p - 1) : ZMod p) := by
          have : C_zmod (revPerm p hp_pos i) i = (c ((revPerm p hp_pos i).val + i.val) : ZMod p) := rfl
          rw [this, h_sum]
        rw [this]
        exact c_p_minus_one p m hm
      have : (∏ i : Fin p, C_zmod (revPerm p hp_pos i) i) = ∏ i : Fin p, ((-1 : ZMod p) ^ m) := by
        apply prod_congr rfl h_const
      rw [this, prod_const]
      have h_card : (Finset.univ : Finset (Fin p)).card = p := by simp
      rw [h_card]
    rw [h_prod]
    have h_sign := sign_revPerm p hp_pos
    have h_sign_zmod : ((sign (revPerm p hp_pos) : ℤ) : ZMod p) = ((-1 : ZMod p) ^ (p * (p - 1) / 2)) := by
      rw [h_sign]
      push_cast
      rfl
    rw [h_sign_zmod]
    have h1 : p * (p - 1) / 2 = p * m := by
      have h_pm1 : p - 1 = 2 * m := by omega
      rw [h_pm1]
      have h_mul : p * (2 * m) = 2 * (p * m) := by ring
      rw [h_mul]
      exact Nat.mul_div_cancel_left (p * m) (by decide)
    rw [h1]
    have h_pow_pm : (-1 : ZMod p) ^ (p * m) = (-1 : ZMod p) ^ m := neg_one_pow_p_mul_m p m hm
    rw [h_pow_pm]
    have h_m_p : ((-1 : ZMod p) ^ m) ^ p = (-1 : ZMod p) ^ (m * p) := by
      exact (pow_mul (-1 : ZMod p) m p).symm
    rw [h_m_p]
    have h_mp : m * p = p * m := by ring
    rw [h_mp]
    rw [h_pow_pm]
    have h_final : (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m = 1 := by
      rw [← pow_add]
      have : m + m = 2 * m := by ring
      rw [this]
      have : (-1 : ZMod p) ^ (2 * m) = ((-1 : ZMod p) ^ 2) ^ m := by exact pow_mul (-1 : ZMod p) 2 m
      rw [this]
      have h1 : (-1 : ZMod p) ^ 2 = 1 := by ring
      rw [h1, one_pow]
    exact h_final
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    have : (((-1 : ℤ) ^ half_minus_one : ℤ) : ZMod p) = (-1 : ZMod p) ^ half_minus_one := by push_cast; rfl
    rw [this]
    exact hA_mod
  · rw [← ZMod.intCast_eq_intCast_iff]
    have : ((1 : ℤ) : ZMod p) = 1 := by push_cast; rfl
    rw [this]
    exact hC_mod

theorem oeis_228304_conjecture_0.disproof : ¬ (type_of% @oeis_228304_conjecture_0) := sorry
