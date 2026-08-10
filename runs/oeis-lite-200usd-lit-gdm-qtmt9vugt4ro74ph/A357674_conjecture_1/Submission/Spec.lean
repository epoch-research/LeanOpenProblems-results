import FormalConjectures.Util.ProblemImports

set_option warn.sorry false


open Nat Finset BigOperators

/--
A357674: $a(n) = \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k} \right)^4 \cdot \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k}^2 \right)^3$.

The terms $\sum_{k = 0}^{2n} \binom{n+k-1}{k}$ and $\sum_{k = 0}^{2n} \binom{n+k-1}{k}^2$ are the summations required.
For $n \ge 1$, the first sum is equal to $\binom{3n}{n}$. We keep the summation structure for fidelity to the OEIS definition, using Finset.sum and Nat.choose.
-/
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

/--
The general sequence $u(n, m)$ from conjecture 3.
$u(n, m) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k} \right)^{2m} \cdot \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Note that `A357674 n = u_A357674 n 2`.
-/
def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)

lemma choose_symm_helper (n k : ℕ) (hn : n ≥ 1) : (n + k - 1).choose k = (k + (n - 1)).choose (n - 1) := by
  have : k ≤ n + k - 1 := by omega
  have h_symm := choose_symm this
  have h_sub : n + k - 1 - k = n - 1 := by omega
  have h_add : n + k - 1 = k + (n - 1) := by omega
  rw [← h_symm]
  rw [h_sub, h_add]

lemma S1_eq (n : ℕ) (hn : n ≥ 1) :
    Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k) = (3 * n).choose n := by
  have h1 : (fun k => (n + k - 1).choose k) = (fun k => (k + (n - 1)).choose (n - 1)) := by
    funext k
    exact choose_symm_helper n k hn
  rw [h1]
  rw [sum_range_add_choose (2 * n) (n - 1)]
  congr 1
  · omega
  · omega

lemma prime_cases (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) : p = 3 ∨ p ≥ 5 := by
  have : p = 3 ∨ p ≥ 4 := by omega
  rcases this with rfl | h4
  · left; rfl
  · right
    by_contra h5
    have hp4 : p = 4 := by omega
    have h_not_prime : ¬ Nat.Prime 4 := by decide
    rw [hp4] at hp
    exact h_not_prime hp

/--
Conjecture 1: $a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/

lemma term_eq_helper (a y : ℕ) (f : ℕ → R) [CommRing R] (hne : y ≠ a) :
    ((if a < y then f a * f y else 0) + (if y < a then f a * f y else 0)) = f a * f y := by
  rcases lt_or_gt_of_ne hne.symm with h | h
  · have h1 : ¬ y < a := by omega
    simp [h, h1]
  · have h1 : ¬ a < y := by omega
    simp [h, h1]

lemma prod_one_add_t_mul {R : Type*} [CommRing R]
    (t : R) (ht3 : t^3 = 0) (s : Finset ℕ) (f : ℕ → R) :
    ∏ x ∈ s, (1 + t * f x) = 1 + t * (∑ x ∈ s, f x) + t^2 * (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [prod_insert ha, ih, sum_insert ha]
    have h_double : ∑ x ∈ insert a s, ∑ y ∈ insert a s, (if x < y then f x * f y else 0) =
        (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) + f a * (∑ x ∈ s, f x) := by
      rw [sum_insert ha]
      simp only [sum_insert ha, lt_self_iff_false, if_false, zero_add]
      rw [sum_add_distrib]
      have h_term : ∑ y ∈ s, (if a < y then f a * f y else 0) + ∑ x ∈ s, (if x < a then f x * f a else 0) =
          f a * ∑ x ∈ s, f x := by
        rw [← sum_add_distrib]
        rw [mul_sum]
        apply sum_congr rfl
        intro x hx
        have hne : x ≠ a := by
          intro h_eq
          subst h_eq
          exact ha hx
        have h_comm : f x * f a = f a * f x := mul_comm (f x) (f a)
        rw [h_comm]
        exact term_eq_helper a x f hne
      calc ∑ y ∈ s, (if a < y then f a * f y else 0) + ((∑ x ∈ s, if x < a then f x * f a else 0) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0)
        _ = (∑ y ∈ s, (if a < y then f a * f y else 0) + ∑ x ∈ s, if x < a then f x * f a else 0) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0 := by ring
        _ = f a * (∑ x ∈ s, f x) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0 := by rw [h_term]
        _ = (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) + f a * (∑ x ∈ s, f x) := by ring
    rw [h_double]
    set sum_s := ∑ x ∈ s, f x
    set sum_pair := ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0
    have h_ring : (1 + t * f a) * (1 + t * sum_s + t^2 * sum_pair) =
        1 + t * (f a + sum_s) + t^2 * (sum_pair + f a * sum_s) + t^3 * (f a * sum_pair) := by ring
    rw [h_ring, ht3]
    ring

lemma algebra_step {R : Type*} [CommRing R] (S1 S2 X : R)
    (hX : S1 = 3 + X) (hX2 : X^2 = 0) (hS2 : 3 * S2 = 9 - 4 * X) :
    27 * (S1^4 * S2^3) = 27 * 2187 := by
  have h1 : 27 * (S1^4 * S2^3) = (S1^4 * (3 * S2)^3) := by ring
  have h2 : (S1^4 * (3 * S2)^3) = 59049 + X^2 * (-30618 - 2268 * X + 5481 * X^2 + 756 * X^3 - 336 * X^4 - 64 * X^5) := by
    rw [hX, hS2]
    ring
  rw [h1, h2, hX2]
  ring

lemma S1_eq_mul_choose (p : ℕ) (hp : p.Prime) :
    (3 * p).choose p = 3 * (3 * p - 1).choose (p - 1) := by
  have hp_pos : p > 0 := hp.pos
  have h1 : 3 * p * (3 * p - 1).choose (p - 1) = (3 * p).choose p * p := by
    have h_succ : 3 * p = (3 * p - 1) + 1 := by omega
    have hk_succ : p = (p - 1) + 1 := by omega
    rw [h_succ, hk_succ]
    exact add_one_mul_choose_eq _ _
  have h2 : p * (3 * p).choose p = p * (3 * (3 * p - 1).choose (p - 1)) := by
    calc p * (3 * p).choose p
      _ = (3 * p).choose p * p := by ring
      _ = 3 * p * (3 * p - 1).choose (p - 1) := h1.symm
      _ = p * (3 * (3 * p - 1).choose (p - 1)) := by ring
  exact mul_left_cancel₀ hp_pos.ne' h2

lemma choose_mod_p (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    (3 * p - 1).choose (p - 1) ≡ 1 [MOD p] := by
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (3 * p - 1) (p - 1) p hp_fact
  have h_mod1 : (3 * p - 1) % p = p - 1 := by
    have h_eq : 3 * p - 1 = p - 1 + 2 * p := by omega
    rw [h_eq]
    have h_comm : 2 * p = p * 2 := by ring
    rw [h_comm]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have h_div1 : (3 * p - 1) / p = 2 := by
    have h_eq : 3 * p - 1 = p - 1 + p * 2 := by omega
    rw [h_eq]
    rw [Nat.add_mul_div_left _ _ (hp.pos)]
    have h_lt : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [h_lt]
  have h_mod2 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  have h_div2 : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [h_mod1, h_mod2, h_div1, h_div2] at h
  have hc1 : (p - 1).choose (p - 1) = 1 := choose_self (p - 1)
  have hc2 : (2).choose 0 = 1 := rfl
  rw [hc1, hc2] at h
  simp only [mul_one] at h
  exact h


lemma sum_range_zmod_zero (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ∑ i ∈ range p, (i : ZMod p) = 0 := by
  have h_sum : ∑ i ∈ range p, i = p * (p - 1) / 2 := sum_range_id p
  have h_cast : (∑ i ∈ range p, (i : ZMod p)) = ((∑ i ∈ range p, i : ℕ) : ZMod p) := by
    simp only [Nat.cast_sum]
  rw [h_cast, h_sum]
  have h_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have h_dvd : 2 ∣ p - 1 := by omega
  rw [Nat.mul_div_assoc p h_dvd]
  push_cast
  rw [ZMod.natCast_self p]
  ring

lemma sum_range_sq_nat (n : ℕ) : 6 * (∑ k ∈ range n, k ^ 2) = n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases n with rfl | n
    · simp
    · have h_sub1 : succ (succ n) - 1 = succ n := rfl
      have h_sub2 : 2 * succ (succ n) - 1 = 2 * n + 3 := by omega
      have h_sub3 : succ n - 1 = n := rfl
      have h_sub4 : 2 * succ n - 1 = 2 * n + 1 := by omega
      rw [h_sub1, h_sub2]
      rw [h_sub3, h_sub4] at ih
      rw [sum_range_succ]
      rw [mul_add]
      rw [ih]
      simp only [succ_eq_add_one]
      ring

lemma sum_squares_eq_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ∑ i ∈ range p, ((i : ZMod p) ^ 2) = 0 := by
  have h_fact : Fact p.Prime := ⟨hp⟩
  have h_eq : (6 : ZMod p) * (∑ i ∈ range p, ((i : ZMod p) ^ 2)) = 0 := by
    have h_nat := sum_range_sq_nat p
    have h_cast : ((6 * (∑ k ∈ range p, k ^ 2) : ℕ) : ZMod p) = ((p * (p - 1) * (2 * p - 1) : ℕ) : ZMod p) := by
      rw [h_nat]
    push_cast at h_cast
    rw [ZMod.natCast_self p] at h_cast
    simp only [zero_mul] at h_cast
    exact h_cast
  have h_six : (6 : ZMod p) ≠ 0 := by
    change ¬ (((6 : ℕ) : ZMod p) = 0)
    rw [ZMod.natCast_eq_zero_iff]
    intro h_dvd'
    have h_dvd_factors : p = 2 ∨ p = 3 := by
      have h6 : 6 = 2 * 3 := by decide
      rw [h6] at h_dvd'
      rcases hp.dvd_mul.mp h_dvd' with h2 | h3
      · left
        exact ((Nat.Prime.dvd_iff_eq (by decide) hp.ne_one).mp h2).symm
      · right
        exact ((Nat.Prime.dvd_iff_eq (by decide) hp.ne_one).mp h3).symm
    rcases h_dvd_factors with rfl | rfl
    · omega
    · omega
  exact (mul_eq_zero.mp h_eq).resolve_left h_six

lemma sum_inv_squares_eq_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) = 0 := by
  have h_fact : Fact p.Prime := ⟨hp⟩
  have h_sum : ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) = ∑ j ∈ Ico 1 p, ((j : ZMod p) ^ 2) := by
    apply Finset.sum_nbij' (fun (j : ℕ) => ((j : ZMod p)⁻¹).val) (fun (j : ℕ) => ((j : ZMod p)⁻¹).val)
    · intro a ha
      rw [mem_Ico] at ha ⊢
      have ha_nz : (a : ZMod p) ≠ 0 := by
        change ¬ (((a : ℕ) : ZMod p) = 0)
        rw [ZMod.natCast_eq_zero_iff]
        intro hdvd
        have : p ≤ a := Nat.le_of_dvd (by omega) hdvd
        omega
      have h_inv_nz : (a : ZMod p)⁻¹ ≠ 0 := inv_ne_zero ha_nz
      have h_val_nz : ((a : ZMod p)⁻¹).val ≠ 0 := by
        intro h_zero
        apply h_inv_nz
        have h_val : (((a : ZMod p)⁻¹).val : ZMod p) = 0 := by
          rw [h_zero, Nat.cast_zero]
        rw [ZMod.natCast_zmod_val] at h_val
        exact h_val
      constructor
      · omega
      · exact ZMod.val_lt ((a : ZMod p)⁻¹)
    · intro a ha
      rw [mem_Ico] at ha ⊢
      have ha_nz : (a : ZMod p) ≠ 0 := by
        change ¬ (((a : ℕ) : ZMod p) = 0)
        rw [ZMod.natCast_eq_zero_iff]
        intro hdvd
        have : p ≤ a := Nat.le_of_dvd (by omega) hdvd
        omega
      have h_inv_nz : (a : ZMod p)⁻¹ ≠ 0 := inv_ne_zero ha_nz
      have h_val_nz : ((a : ZMod p)⁻¹).val ≠ 0 := by
        intro h_zero
        apply h_inv_nz
        have h_val : (((a : ZMod p)⁻¹).val : ZMod p) = 0 := by
          rw [h_zero, Nat.cast_zero]
        rw [ZMod.natCast_zmod_val] at h_val
        exact h_val
      constructor
      · omega
      · exact ZMod.val_lt ((a : ZMod p)⁻¹)
    · intro a ha
      rw [mem_Ico] at ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_zmod_val ((a : ZMod p)⁻¹)
      rw [this, inv_inv]
      exact ZMod.val_natCast_of_lt ha.2
    · intro a ha
      rw [mem_Ico] at ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_zmod_val ((a : ZMod p)⁻¹)
      rw [this, inv_inv]
      exact ZMod.val_natCast_of_lt ha.2
    · intro a ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_zmod_val ((a : ZMod p)⁻¹)
      rw [this]
  rw [h_sum]
  have h_split : ∑ j ∈ range p, ((j : ZMod p) ^ 2) = ∑ j ∈ Ico 1 p, ((j : ZMod p) ^ 2) := by
    rw [Finset.range_eq_Ico]
    have h_insert : Ico 0 p = insert 0 (Ico 1 p) := by
      symm
      apply Finset.insert_Ico_add_one_left_eq_Ico
      omega
    rw [h_insert]
    rw [Finset.sum_insert]
    · simp
    · simp
  rw [← h_split]
  exact sum_squares_eq_zero p hp hp5

lemma sum_inv_eq_zero (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹) = 0 := by
  have h_fact : Fact p.Prime := ⟨hp⟩
  have h_sum : ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹) = ∑ j ∈ Ico 1 p, ((j : ZMod p)) := by
    apply Finset.sum_nbij' (fun (j : ℕ) => ((j : ZMod p)⁻¹).val) (fun (j : ℕ) => ((j : ZMod p)⁻¹).val)
    · intro a ha
      rw [mem_Ico] at ha ⊢
      have ha_nz : (a : ZMod p) ≠ 0 := by
        change ¬ (((a : ℕ) : ZMod p) = 0)
        rw [ZMod.natCast_eq_zero_iff]
        intro hdvd
        have : p ≤ a := Nat.le_of_dvd (by omega) hdvd
        omega
      have h_inv_nz : (a : ZMod p)⁻¹ ≠ 0 := inv_ne_zero ha_nz
      have h_val_nz : ((a : ZMod p)⁻¹).val ≠ 0 := by
        intro h_zero
        apply h_inv_nz
        have h_val : (((a : ZMod p)⁻¹).val : ZMod p) = 0 := by
          rw [h_zero, Nat.cast_zero]
        rw [ZMod.natCast_zmod_val] at h_val
        exact h_val
      constructor
      · omega
      · exact ZMod.val_lt ((a : ZMod p)⁻¹)
    · intro a ha
      rw [mem_Ico] at ha ⊢
      have ha_nz : (a : ZMod p) ≠ 0 := by
        change ¬ (((a : ℕ) : ZMod p) = 0)
        rw [ZMod.natCast_eq_zero_iff]
        intro hdvd
        have : p ≤ a := Nat.le_of_dvd (by omega) hdvd
        omega
      have h_inv_nz : (a : ZMod p)⁻¹ ≠ 0 := inv_ne_zero ha_nz
      have h_val_nz : ((a : ZMod p)⁻¹).val ≠ 0 := by
        intro h_zero
        apply h_inv_nz
        have h_val : (((a : ZMod p)⁻¹).val : ZMod p) = 0 := by
          rw [h_zero, Nat.cast_zero]
        rw [ZMod.natCast_zmod_val] at h_val
        exact h_val
      constructor
      · omega
      · exact ZMod.val_lt ((a : ZMod p)⁻¹)
    · intro a ha
      rw [mem_Ico] at ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_zmod_val ((a : ZMod p)⁻¹)
      rw [this, inv_inv]
      exact ZMod.val_natCast_of_lt ha.2
    · intro a ha
      rw [mem_Ico] at ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_zmod_val ((a : ZMod p)⁻¹)
      rw [this, inv_inv]
      exact ZMod.val_natCast_of_lt ha.2
    · intro a ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_zmod_val ((a : ZMod p)⁻¹)
      rw [this]
  rw [h_sum]
  have h_split : ∑ j ∈ range p, ((j : ZMod p)) = ∑ j ∈ Ico 1 p, ((j : ZMod p)) := by
    rw [Finset.range_eq_Ico]
    have h_insert : Ico 0 p = insert 0 (Ico 1 p) := by
      symm
      apply Finset.insert_Ico_add_one_left_eq_Ico
      omega
    rw [h_insert]
    rw [Finset.sum_insert]
    · simp
    · simp
  rw [← h_split]
  exact sum_range_zmod_zero p hp hp3

lemma j_coprime_p_sq (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    Nat.Coprime j (p^2) := by
  have h1 : ¬ p ∣ j := by
    intro hdvd
    have : p ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega
  have h2 : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
  exact Nat.Coprime.pow_right 2 h2

lemma j_inv_mul (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    (j : ZMod (p^2)) * (j : ZMod (p^2))⁻¹ = 1 := by
  exact ZMod.coe_mul_inv_eq_one j (j_coprime_p_sq p hp j hj1 hjp)

lemma sum_inv_eq_sum_inv_p_sub (p : ℕ) :
    ∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹) = ∑ j ∈ Ico 1 p, (((p - j : ℕ) : ZMod (p^2))⁻¹) := by
  apply Finset.sum_nbij' (fun j => p - j) (fun j => p - j)
  · intro a ha
    rw [mem_Ico] at ha ⊢
    omega
  · intro a ha
    rw [mem_Ico] at ha ⊢
    omega
  · intro a ha
    rw [mem_Ico] at ha
    omega
  · intro a ha
    rw [mem_Ico] at ha
    omega
  · intro a ha
    rw [mem_Ico] at ha
    have : p - (p - a) = a := by omega
    rw [this]

lemma p_sub_j_inv (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    ((p - j : ℕ) : ZMod (p^2))⁻¹ = - (j : ZMod (p^2))⁻¹ - (p : ZMod (p^2)) * ((j : ZMod (p^2))⁻¹ ^ 2) := by
  set A : ZMod (p^2) := ((p - j : ℕ) : ZMod (p^2))
  set Y : ZMod (p^2) := (j : ZMod (p^2))⁻¹
  set p_cast : ZMod (p^2) := (p : ZMod (p^2))
  have h_cop : Nat.Coprime (p - j) (p^2) := by
    have h_pos : 1 ≤ p - j := by omega
    have h_lt : p - j < p := by omega
    exact j_coprime_p_sq p hp (p - j) h_pos h_lt
  have h_inv_mul := ZMod.coe_mul_inv_eq_one (p - j) h_cop
  have h_jY : (j : ZMod (p^2)) * Y = 1 := j_inv_mul p hp j hj1 hjp
  have h_p2 : p_cast^2 = 0 := by
    have : p_cast^2 = (((p^2 : ℕ) : ZMod (p^2))) := by push_cast; rfl
    rw [this]
    rw [ZMod.natCast_self]
  have h_A : A = p_cast - (j : ZMod (p^2)) := by
    have : p - j + j = p := by omega
    have h_eq : A + (j : ZMod (p^2)) = p_cast := by
      change ((p - j : ℕ) : ZMod (p^2)) + (j : ZMod (p^2)) = (p : ZMod (p^2))
      rw [← Nat.cast_add, this]
    rw [← h_eq]
    ring
  have h_mul : A * (- Y - p_cast * Y^2) = 1 := by
    rw [h_A]
    calc (p_cast - (j : ZMod (p^2))) * (- Y - p_cast * Y^2)
      _ = - (p_cast * Y) - p_cast^2 * Y^2 + (j : ZMod (p^2)) * Y + p_cast * ((j : ZMod (p^2)) * Y) * Y := by ring
      _ = - (p_cast * Y) - 0 * Y^2 + 1 + p_cast * 1 * Y := by rw [h_p2, h_jY]
      _ = 1 := by ring
  have h_cancel : A⁻¹ = - Y - p_cast * Y^2 := by
    calc A⁻¹
      _ = 1 * A⁻¹ := by ring
      _ = (A * (- Y - p_cast * Y^2)) * A⁻¹ := by rw [h_mul]
      _ = (A * A⁻¹) * (- Y - p_cast * Y^2) := by ring
      _ = 1 * (- Y - p_cast * Y^2) := by rw [h_inv_mul]
      _ = - Y - p_cast * Y^2 := by ring
  exact h_cancel

lemma p_mul_eq_zero_of_val_divisible (p : ℕ) (hp : p.Prime) (x : ZMod (p^2)) (h : (x.val : ZMod p) = 0) :
    (p : ZMod (p^2)) * x = 0 := by
  have h_p_pos : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  have hdvd : p ∣ x.val := by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact h
  obtain ⟨k, hk⟩ := hdvd
  have h_val : x = (x.val : ZMod (p^2)) := by rw [ZMod.natCast_zmod_val]
  rw [h_val, hk]
  have : p * (p * k) = p^2 * k := by ring
  have h_mul : (p : ZMod (p^2)) * ((p * k : ℕ) : ZMod (p^2)) = ((p * (p * k) : ℕ) : ZMod (p^2)) := by push_cast; rfl
  rw [h_mul, this]
  push_cast
  have h_p2 : (p : ZMod (p^2))^2 = 0 := by
    have h_eq : (p : ZMod (p^2))^2 = ((p^2 : ℕ) : ZMod (p^2)) := by push_cast; rfl
    rw [h_eq, ZMod.natCast_self]
  rw [h_p2, zero_mul]

lemma mod_p_sq_cast (p : ℕ) (n : ℕ) :
    ((n % p^2 : ℕ) : ZMod p) = (n : ZMod p) := by
  have h_eq : (n % p^2) + p^2 * (n / p^2) = n := Nat.mod_add_div n (p^2)
  have h_cast : (n : ZMod p) = ((n % p^2 : ℕ) : ZMod p) + ((p^2 * (n / p^2) : ℕ) : ZMod p) := by
    rw [← Nat.cast_add, h_eq]
  rw [h_cast]
  have h_zero : ((p^2 * (n / p^2) : ℕ) : ZMod p) = 0 := by
    push_cast
    have : (p : ZMod p) = 0 := ZMod.natCast_self p
    rw [this]
    ring
  rw [h_zero, add_zero]

lemma val_add_cast (p : ℕ) (hp : p.Prime) (A B : ZMod (p^2)) :
    (((A + B).val : ℕ) : ZMod p) = (A.val : ZMod p) + (B.val : ZMod p) := by
  have : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  have h_val := ZMod.val_add A B
  rw [h_val]
  rw [mod_p_sq_cast p]
  push_cast
  rfl

lemma sum_val_cast (p : ℕ) (hp : p.Prime) (s : Finset ℕ) (x : ℕ → ZMod (p^2)) :
    (((∑ i ∈ s, x i).val : ℕ) : ZMod p) = ∑ i ∈ s, (((x i).val : ZMod p)) := by
  have : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    rw [val_add_cast p hp]
    rw [ih]

lemma val_mul_cast (p : ℕ) (hp : p.Prime) (A B : ZMod (p^2)) :
    (((A * B).val : ℕ) : ZMod p) = (A.val : ZMod p) * (B.val : ZMod p) := by
  have : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  have h_val := ZMod.val_mul A B
  rw [h_val]
  rw [mod_p_sq_cast p]
  push_cast
  rfl

lemma inv_val_cast (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    (((j : ZMod (p^2))⁻¹).val : ZMod p) = (j : ZMod p)⁻¹ := by
  have : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  set X : ZMod p := (j : ZMod p)
  set Y : ZMod p := (((j : ZMod (p^2))⁻¹).val : ZMod p)
  set Z : ZMod p := (j : ZMod p)⁻¹
  have h_cop_p : Nat.Coprime j p := by
    have h1 : ¬ p ∣ j := by
      intro hdvd
      have : p ≤ j := Nat.le_of_dvd (by omega) hdvd
      omega
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
  have h_XZ : X * Z = 1 := ZMod.coe_mul_inv_eq_one j h_cop_p
  have h_j_inv : (j : ZMod (p^2)) * (j : ZMod (p^2))⁻¹ = 1 := j_inv_mul p hp j hj1 hjp
  have h_cast : (((j : ZMod (p^2)) * (j : ZMod (p^2))⁻¹).val : ZMod p) = 1 := by
    rw [h_j_inv]
    have hp2 : p ≥ 2 := hp.two_le
    haveI : Fact (1 < p^2) := ⟨by nlinarith⟩
    have : (1 : ZMod (p^2)).val = 1 := ZMod.val_one _
    rw [this]
    push_cast; rfl
  have h_mul_cast := val_mul_cast p hp (j : ZMod (p^2)) ((j : ZMod (p^2))⁻¹)
  rw [h_cast] at h_mul_cast
  have h_val_j : ((j : ZMod (p^2)).val : ZMod p) = X := by
    have h_lt : j < p^2 := by
      calc j < p := hjp
      _ ≤ p^2 := by nlinarith
    rw [ZMod.val_natCast_of_lt h_lt]
  rw [h_val_j] at h_mul_cast
  have h_XY : X * Y = 1 := h_mul_cast.symm
  calc Y
    _ = 1 * Y := by ring
    _ = (Z * X) * Y := by rw [mul_comm Z X, h_XZ]
    _ = Z * (X * Y) := by ring
    _ = Z * 1 := by rw [h_XY]
    _ = Z := by ring

lemma sum_inv_eq_zero_mod_p_sq (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹) = 0 := by
  have : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  set S : ZMod (p^2) := ∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹)
  have h_p_sub : S = ∑ j ∈ Ico 1 p, (((p - j : ℕ) : ZMod (p^2))⁻¹) := sum_inv_eq_sum_inv_p_sub p
  have h_congr : ∑ j ∈ Ico 1 p, (((p - j : ℕ) : ZMod (p^2))⁻¹) = ∑ j ∈ Ico 1 p, (- (j : ZMod (p^2))⁻¹ - (p : ZMod (p^2)) * ((j : ZMod (p^2))⁻¹ ^ 2)) := by
    apply sum_congr rfl
    intro j hj
    rw [mem_Ico] at hj
    exact p_sub_j_inv p hp j hj.1 hj.2
  rw [← h_p_sub] at h_congr
  have h_split : ∑ j ∈ Ico 1 p, (- (j : ZMod (p^2))⁻¹ - (p : ZMod (p^2)) * ((j : ZMod (p^2))⁻¹ ^ 2)) =
      - S - (p : ZMod (p^2)) * (∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹ ^ 2)) := by
    rw [sum_sub_distrib, sum_neg_distrib, ← mul_sum]
  rw [h_split] at h_congr
  have h_p_sum : (p : ZMod (p^2)) * (∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹ ^ 2)) = 0 := by
    apply p_mul_eq_zero_of_val_divisible p hp
    rw [sum_val_cast p hp]
    have h_pow_cast : ∀ j ∈ Ico 1 p, ((((j : ZMod (p^2))⁻¹ ^ 2).val : ℕ) : ZMod p) = (j : ZMod p)⁻¹ ^ 2 := by
      intro j hj
      rw [mem_Ico] at hj
      have h_sq : (j : ZMod (p^2))⁻¹ ^ 2 = (j : ZMod (p^2))⁻¹ * (j : ZMod (p^2))⁻¹ := by ring
      rw [h_sq]
      rw [val_mul_cast p hp]
      rw [inv_val_cast p hp j hj.1 hj.2]
      ring
    have h_congr2 : ∑ j ∈ Ico 1 p, ((((j : ZMod (p^2))⁻¹ ^ 2).val : ℕ) : ZMod p) = ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) := by
      apply sum_congr rfl
      intro j hj
      exact h_pow_cast j hj
    rw [h_congr2]
    rw [sum_inv_squares_eq_zero p hp hp5]
  have h_two_S : (2 : ZMod (p^2)) * S = 0 := by
    calc (2 : ZMod (p^2)) * S
      _ = S + S := by ring
      _ = S + (-S - (p : ZMod (p^2)) * (∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹ ^ 2))) := by nth_rw 2 [h_congr]
      _ = - ((p : ZMod (p^2)) * (∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹ ^ 2))) := by ring
      _ = - 0 := by rw [h_p_sum]
      _ = 0 := by ring
  have h_cop_two : Nat.Coprime 2 (p^2) := by
    have h1 : ¬ p ∣ 2 := by
      intro hdvd
      have : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
      omega
    have h2 : Nat.Coprime 2 p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
    exact Nat.Coprime.pow_right 2 h2
  have h_inv_two := ZMod.coe_mul_inv_eq_one 2 h_cop_two
  have h_one : (2 : ZMod (p^2))⁻¹ * 2 = 1 := by
    rw [mul_comm]
    exact h_inv_two
  calc S
    _ = 1 * S := by ring
    _ = ((2 : ZMod (p^2))⁻¹ * 2) * S := by rw [h_one]
    _ = (2 : ZMod (p^2))⁻¹ * (2 * S) := by ring
    _ = (2 : ZMod (p^2))⁻¹ * 0 := by rw [h_two_S]
    _ = 0 := by ring

lemma sum_pairs_identity {R : Type*} [CommRing R] (s : Finset ℕ) (f : ℕ → R) :
    2 * (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) = (∑ x ∈ s, f x)^2 - ∑ x ∈ s, (f x)^2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h_double : ∑ x ∈ insert a s, ∑ y ∈ insert a s, (if x < y then f x * f y else 0) =
        (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) + f a * (∑ x ∈ s, f x) := by
      rw [sum_insert ha]
      simp only [sum_insert ha, lt_self_iff_false, if_false, zero_add]
      rw [sum_add_distrib]
      have h_term : ∑ y ∈ s, (if a < y then f a * f y else 0) + ∑ x ∈ s, (if x < a then f x * f a else 0) =
          f a * ∑ x ∈ s, f x := by
        rw [← sum_add_distrib]
        rw [mul_sum]
        apply sum_congr rfl
        intro x hx
        have hne : x ≠ a := by
          intro h_eq
          subst h_eq
          exact ha hx
        have h_comm : f x * f a = f a * f x := mul_comm (f x) (f a)
        rw [h_comm]
        exact term_eq_helper a x f hne
      calc ∑ y ∈ s, (if a < y then f a * f y else 0) + ((∑ x ∈ s, if x < a then f x * f a else 0) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0)
        _ = (∑ y ∈ s, (if a < y then f a * f y else 0) + ∑ x ∈ s, if x < a then f x * f a else 0) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0 := by ring
        _ = f a * (∑ x ∈ s, f x) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0 := by rw [h_term]
        _ = (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) + f a * (∑ x ∈ s, f x) := by ring
    rw [h_double]
    rw [sum_insert ha, sum_insert ha]
    set sum_s := ∑ x ∈ s, f x
    set sum_pair := ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0
    set sum_sq := ∑ x ∈ s, (f x)^2
    calc 2 * (sum_pair + f a * sum_s)
      _ = 2 * sum_pair + 2 * f a * sum_s := by ring
      _ = (sum_s^2 - sum_sq) + 2 * f a * sum_s := by rw [ih]
      _ = (f a + sum_s)^2 - ((f a)^2 + sum_sq) := by ring

lemma prod_Ico_reflect {α : Type*} [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∏ j ∈ Ico 1 n, f (n - j) = ∏ j ∈ Ico 1 n, f j := by
  apply prod_nbij' (fun j => n - j) (fun j => n - j)
  · intro a ha
    rw [mem_Ico] at ha ⊢
    omega
  · intro a ha
    rw [mem_Ico] at ha ⊢
    omega
  · intro a ha
    rw [mem_Ico] at ha
    omega
  · intro a ha
    rw [mem_Ico] at ha
    omega
  · intro a ha
    rfl

lemma choose_mul_factorial_helper (n : ℕ) (hn : n ≥ 1) :
    (3 * n - 1).choose (n - 1) * (n - 1)! * (2 * n)! = (3 * n - 1)! := by
  have h_sub : (3 * n - 1) - (n - 1) = 2 * n := by omega
  have h_le : n - 1 ≤ 3 * n - 1 := by omega
  rw [← Nat.choose_mul_factorial_mul_factorial h_le, h_sub]


lemma prod_range_succ (n : ℕ) : ∏ j ∈ range n, (j + 1) = (n)! := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, mul_comm, Nat.factorial_succ]


lemma prod_Ico_id_eq_factorial (n : ℕ) (hn : n ≥ 1) :
    ∏ j ∈ Ico 1 n, j = (n - 1)! := by
  have h_eq : ∏ j ∈ Ico 1 n, j = ∏ j ∈ range (n - 1), (j + 1) := by
    apply prod_nbij' (fun j => j - 1) (fun j => j + 1)
    · intro a ha
      rw [mem_Ico] at ha
      rw [mem_range]
      omega
    · intro a ha
      rw [mem_range] at ha
      rw [mem_Ico]
      omega
    · intro a ha
      rw [mem_Ico] at ha
      omega
    · intro a ha
      rw [mem_range] at ha
      omega
    · intro a ha
      rw [mem_Ico] at ha
      omega
  rw [h_eq]
  exact prod_range_succ (n - 1)


lemma prod_add_eq_Ico (n : ℕ) :
    ∏ j ∈ Ico 1 n, (2 * n + j) = ∏ j ∈ Ico (2 * n + 1) (3 * n), j := by
  have h := Finset.prod_Ico_add (fun j => j) 1 n (2 * n)
  have h1 : 1 + 2 * n = 2 * n + 1 := by omega
  have h2 : n + 2 * n = 3 * n := by omega
  rw [h1, h2] at h
  exact h


lemma prod_add_mul_factorial (n : ℕ) (hn : n ≥ 1) :
    (2 * n)! * ∏ j ∈ Ico 1 n, (2 * n + j) = (3 * n - 1)! := by
  have h_shift := prod_add_eq_Ico n
  rw [h_shift]
  have h_fac1 := prod_Ico_id_eq_factorial (2 * n + 1) (by omega)
  have h_sub : 2 * n + 1 - 1 = 2 * n := by omega
  rw [h_sub] at h_fac1
  rw [← h_fac1]
  have h_consec := Finset.prod_Ico_consecutive (fun j => j) (by omega : 1 ≤ 2 * n + 1) (by omega : 2 * n + 1 ≤ 3 * n)
  rw [h_consec]
  have h_fac2 := prod_Ico_id_eq_factorial (3 * n) (by omega)
  rw [h_fac2]


lemma choose_mul_factorial_eq_prod (p : ℕ) (_hp : p.Prime) (hp5 : p ≥ 5) :
    (3 * p - 1).choose (p - 1) * (p - 1)! = ∏ j ∈ Ico 1 p, (2 * p + j) := by
  have h1 : (3 * p - 1).choose (p - 1) * (p - 1)! * (2 * p)! = (∏ j ∈ Ico 1 p, (2 * p + j)) * (2 * p)! := by
    rw [choose_mul_factorial_helper p (by omega)]
    rw [mul_comm (∏ j ∈ Ico 1 p, (2 * p + j))]
    exact (prod_add_mul_factorial p (by omega)).symm
  have h_pos : (2 * p)! > 0 := Nat.factorial_pos _
  exact Nat.eq_of_mul_eq_mul_right h_pos h1



lemma j_coprime_p_cub (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    Nat.Coprime j (p^3) := by
  have h1 : ¬ p ∣ j := by
    intro hdvd
    have : p ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega
  have h2 : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
  exact Nat.Coprime.pow_right 3 h2

lemma j_inv_mul_cub (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    (j : ZMod (p^3)) * (j : ZMod (p^3))⁻¹ = 1 := by
  exact ZMod.coe_mul_inv_eq_one j (j_coprime_p_cub p hp j hj1 hjp)


lemma element_factorization (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    ((2 * p + j : ℕ) : ZMod (p^3)) = (j : ZMod (p^3)) * (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹) := by
  have h_j_inv : (j : ZMod (p^3)) * (j : ZMod (p^3))⁻¹ = 1 := j_inv_mul_cub p hp j hj1 hjp
  calc ((2 * p + j : ℕ) : ZMod (p^3))
    _ = 2 * (p : ZMod (p^3)) + (j : ZMod (p^3)) := by push_cast; rfl
    _ = (j : ZMod (p^3)) * (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹) := by
      rw [mul_add, mul_one, ← mul_assoc, mul_comm (j : ZMod (p^3)), mul_assoc, h_j_inv]
      ring


lemma prod_factorization (p : ℕ) (hp : p.Prime) (_hp5 : p ≥ 5) :
    ∏ j ∈ Ico 1 p, ((2 * p + j : ℕ) : ZMod (p^3)) =
    (∏ j ∈ Ico 1 p, (j : ZMod (p^3))) * ∏ j ∈ Ico 1 p, (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹) := by
  have h_eq : ∏ j ∈ Ico 1 p, ((2 * p + j : ℕ) : ZMod (p^3)) =
      ∏ j ∈ Ico 1 p, ((j : ZMod (p^3)) * (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹)) := by
    apply prod_congr rfl
    intro j hj
    rw [mem_Ico] at hj
    exact element_factorization p hp j hj.1 hj.2
  rw [h_eq]
  exact prod_mul_distrib


lemma prod_id_zmod_cub (p : ℕ) (hp : p.Prime) :
    ∏ j ∈ Ico 1 p, (j : ZMod (p^3)) = ((p - 1)! : ZMod (p^3)) := by
  have h := prod_Ico_id_eq_factorial p (by have := hp.two_le; omega)
  have h_cast : ((∏ j ∈ Ico 1 p, j : ℕ) : ZMod (p^3)) = (((p - 1)! : ℕ) : ZMod (p^3)) := by rw [h]
  push_cast at h_cast
  exact h_cast



lemma coprime_factorial_p_cub (p : ℕ) (hp : p.Prime) :
    Nat.Coprime ((p - 1)!) (p^3) := by
  have h_pos : p > 0 := hp.pos
  have h_cop : Nat.Coprime p ((p - 1)!) := Nat.Prime.coprime_factorial_of_lt hp (by omega)
  have h_cop2 : Nat.Coprime ((p - 1)!) p := h_cop.symm
  exact Nat.Coprime.pow_right 3 h_cop2


lemma choose_mod_p_cubed (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ((3 * p - 1).choose (p - 1) : ZMod (p^3)) = ∏ j ∈ Ico 1 p, (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹) := by
  have h_cop := coprime_factorial_p_cub p hp
  have h_eq1 := choose_mul_factorial_eq_prod p hp hp5
  have h_cast : (((3 * p - 1).choose (p - 1) * (p - 1)! : ℕ) : ZMod (p^3)) = (((∏ j ∈ Ico 1 p, (2 * p + j) : ℕ) : ZMod (p^3))) := by rw [h_eq1]
  push_cast at h_cast
  have h_fac := prod_factorization p hp hp5
  push_cast at h_fac
  have h_id_zmod := prod_id_zmod_cub p hp
  rw [h_fac, h_id_zmod] at h_cast
  have h_inv := ZMod.coe_mul_inv_eq_one ((p - 1)!) h_cop
  set B : ZMod (p^3) := ((p - 1)! : ZMod (p^3))
  set A : ZMod (p^3) := ((3 * p - 1).choose (p - 1) : ZMod (p^3))
  set C : ZMod (p^3) := ∏ j ∈ Ico 1 p, (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹)
  change A * B = B * C at h_cast
  have h_comm : B * C = C * B := mul_comm B C
  rw [h_comm] at h_cast
  have h_cancel : A = C := by
    calc A
      _ = A * 1 := by ring
      _ = A * (B * B⁻¹) := by rw [h_inv]
      _ = (A * B) * B⁻¹ := by ring
      _ = (C * B) * B⁻¹ := by rw [h_cast]
      _ = C * (B * B⁻¹) := by ring
      _ = C * 1 := by rw [h_inv]
      _ = C := by ring
  exact h_cancel


lemma p_cub_eq_zero (p : ℕ) : ((p : ZMod (p^3)) ^ 3) = 0 := by
  have : (p : ZMod (p^3)) ^ 3 = (((p^3 : ℕ) : ZMod (p^3))) := by push_cast; rfl
  rw [this, ZMod.natCast_self]


lemma p_mul_eq_zero_of_val_divisible_cubed (p : ℕ) (hp : p.Prime) (x : ZMod (p^3)) (h : (x.val : ZMod (p^2)) = 0) :
    (p : ZMod (p^3)) * x = 0 := by
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  have hdvd : p^2 ∣ x.val := by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact h
  obtain ⟨k, hk⟩ := hdvd
  have h_val : x = (x.val : ZMod (p^3)) := by rw [ZMod.natCast_zmod_val]
  rw [h_val, hk]
  have h_eq : p * (p^2 * k) = p^3 * k := by ring
  have h_mul : (p : ZMod (p^3)) * ((p^2 * k : ℕ) : ZMod (p^3)) = ((p * (p^2 * k) : ℕ) : ZMod (p^3)) := by push_cast; rfl
  rw [h_mul, h_eq]
  push_cast
  rw [← Nat.cast_pow]
  have h_zero : ((p^3 : ℕ) : ZMod (p^3)) = 0 := ZMod.natCast_self (p^3)
  rw [h_zero, zero_mul]


lemma mod_p_cub_cast (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ((n % p^3 : ℕ) : ZMod (p^2)) = (n : ZMod (p^2)) := by
  have hp_pos := hp.pos; haveI : NeZero (p^2) := ⟨by nlinarith⟩
  have h_eq : (n % p^3) + p^3 * (n / p^3) = n := Nat.mod_add_div n (p^3)
  have h_cast : (n : ZMod (p^2)) = ((n % p^3 : ℕ) : ZMod (p^2)) + ((p^3 * (n / p^3) : ℕ) : ZMod (p^2)) := by
    rw [← Nat.cast_add, h_eq]
  rw [h_cast]
  have h_zero : ((p^3 * (n / p^3) : ℕ) : ZMod (p^2)) = 0 := by
    have h_eq2 : p^3 * (n / p^3) = p^2 * (p * (n / p^3)) := by ring
    rw [h_eq2]
    push_cast
    rw [← Nat.cast_pow]
    rw [ZMod.natCast_self (p^2)]
    ring
  rw [h_zero, add_zero]

lemma val_add_cast_cub (p : ℕ) (hp : p.Prime) (A B : ZMod (p^3)) :
    (((A + B).val : ℕ) : ZMod (p^2)) = (A.val : ZMod (p^2)) + (B.val : ZMod (p^2)) := by
  have hp_pos := hp.pos; haveI : NeZero (p^2) := ⟨by nlinarith⟩
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  have h_val := ZMod.val_add A B
  rw [h_val]
  rw [mod_p_cub_cast p hp]
  push_cast
  rfl

lemma sum_val_cast_cub (p : ℕ) (hp : p.Prime) (s : Finset ℕ) (x : ℕ → ZMod (p^3)) :
    (((∑ i ∈ s, x i).val : ℕ) : ZMod (p^2)) = ∑ i ∈ s, (((x i).val : ZMod (p^2))) := by
  have hp_pos := hp.pos; haveI : NeZero (p^2) := ⟨by nlinarith⟩
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    rw [val_add_cast_cub p hp]
    rw [ih]

lemma val_mul_cast_cub (p : ℕ) (hp : p.Prime) (A B : ZMod (p^3)) :
    (((A * B).val : ℕ) : ZMod (p^2)) = (A.val : ZMod (p^2)) * (B.val : ZMod (p^2)) := by
  have hp_pos := hp.pos; haveI : NeZero (p^2) := ⟨by nlinarith⟩
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  have h_val := ZMod.val_mul A B
  rw [h_val]
  rw [mod_p_cub_cast p hp]
  push_cast
  rfl

lemma inv_val_cast_cub (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    (((j : ZMod (p^3))⁻¹).val : ZMod (p^2)) = (j : ZMod (p^2))⁻¹ := by
  have hp_pos := hp.pos; haveI : NeZero (p^2) := ⟨by nlinarith⟩
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  set X : ZMod (p^2) := (j : ZMod (p^2))
  set Y : ZMod (p^2) := (((j : ZMod (p^3))⁻¹).val : ZMod (p^2))
  set Z : ZMod (p^2) := (j : ZMod (p^2))⁻¹
  have h_cop_p2 : Nat.Coprime j (p^2) := by
    have h1 : ¬ p ∣ j := by
      intro hdvd
      have : p ≤ j := Nat.le_of_dvd (by omega) hdvd
      omega
    have h2 : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
    exact Nat.Coprime.pow_right 2 h2
  have h_XZ : X * Z = 1 := ZMod.coe_mul_inv_eq_one j h_cop_p2
  have h_j_inv : (j : ZMod (p^3)) * (j : ZMod (p^3))⁻¹ = 1 := by
    exact ZMod.coe_mul_inv_eq_one j (j_coprime_p_cub p hp j hj1 hjp)
  have h_cast : (((j : ZMod (p^3)) * (j : ZMod (p^3))⁻¹).val : ZMod (p^2)) = 1 := by
    rw [h_j_inv]
    have hp2 := hp.two_le
    have h_le1 : p ≤ p * p := by nlinarith [hp2]
    have h_le2 : p * p ≤ p * p * p := by nlinarith [hp2]
    have h_le3 : p ≤ p * p * p := by omega
    have h_ring : p^3 = p * p * p := by ring
    have h_le4 : p ≤ p^3 := by rw [h_ring]; exact h_le3
    have h_p1 : 1 < p := by omega
    have h_p3_gt : 1 < p^3 := by omega
    haveI : Fact (1 < p^3) := ⟨h_p3_gt⟩
    have h_one : (1 : ZMod (p^3)).val = 1 := ZMod.val_one (p^3)
    rw [h_one]
    push_cast; rfl
  have h_mul_cast := val_mul_cast_cub p hp (j : ZMod (p^3)) ((j : ZMod (p^3))⁻¹)
  rw [h_cast] at h_mul_cast
  have h_val_j : ((j : ZMod (p^3)).val : ZMod (p^2)) = X := by
    have h_lt : j < p^3 := by
      have hp2 := hp.two_le
      have h_le1 : p ≤ p * p := by nlinarith [hp2]
      have h_le2 : p * p ≤ p * p * p := by nlinarith [hp2]
      have h_le3 : p ≤ p * p * p := by omega
      have h_ring : p^3 = p * p * p := by ring
      have h_le4 : p ≤ p^3 := by rw [h_ring]; exact h_le3
      omega
    rw [ZMod.val_natCast_of_lt h_lt]
  rw [h_val_j] at h_mul_cast
  have h_XY : X * Y = 1 := h_mul_cast.symm
  calc Y
    _ = 1 * Y := by ring
    _ = (Z * X) * Y := by rw [mul_comm Z X, h_XZ]
    _ = Z * (X * Y) := by ring
    _ = Z * 1 := by rw [h_XY]
    _ = Z := by ring


lemma prod_expansion (p : ℕ) (_hp : p.Prime) (_hp5 : p ≥ 5) :
    ∏ j ∈ Ico 1 p, (1 + (p : ZMod (p^3)) * (2 * (j : ZMod (p^3))⁻¹)) =
    1 + (p : ZMod (p^3)) * (∑ j ∈ Ico 1 p, 2 * (j : ZMod (p^3))⁻¹) +
    (p : ZMod (p^3))^2 * (∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (2 * (x : ZMod (p^3))⁻¹) * (2 * (y : ZMod (p^3))⁻¹) else 0) := by
  have ht3 : (p : ZMod (p^3))^3 = 0 := p_cub_eq_zero p
  exact prod_one_add_t_mul (p : ZMod (p^3)) ht3 (Ico 1 p) (fun j => 2 * (j : ZMod (p^3))⁻¹)






lemma p_sq_mul_eq_zero_of_val_divisible_cubed (p : ℕ) (hp : p.Prime) (x : ZMod (p^3)) (h : (x.val : ZMod p) = 0) :
    (p : ZMod (p^3))^2 * x = 0 := by
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  have hdvd : p ∣ x.val := by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact h
  obtain ⟨k, hk⟩ := hdvd
  have h_val : x = (x.val : ZMod (p^3)) := by rw [ZMod.natCast_zmod_val]
  rw [h_val, hk]
  have h_eq : p^2 * (p * k) = p^3 * k := by ring
  have h_mul : (p : ZMod (p^3))^2 * ((p * k : ℕ) : ZMod (p^3)) = ((p^2 * (p * k) : ℕ) : ZMod (p^3)) := by push_cast; rfl
  rw [h_mul, h_eq]
  push_cast
  rw [← Nat.cast_pow]
  have h_zero : ((p^3 : ℕ) : ZMod (p^3)) = 0 := ZMod.natCast_self (p^3)
  rw [h_zero, zero_mul]

lemma mod_p_cub_cast_to_p (p : ℕ) (_hp : p.Prime) (n : ℕ) :
    ((n % p^3 : ℕ) : ZMod p) = (n : ZMod p) := by
  have h_eq : (n % p^3) + p^3 * (n / p^3) = n := Nat.mod_add_div n (p^3)
  have h_cast : (n : ZMod p) = ((n % p^3 : ℕ) : ZMod p) + ((p^3 * (n / p^3) : ℕ) : ZMod p) := by
    rw [← Nat.cast_add, h_eq]
  rw [h_cast]
  have h_zero : ((p^3 * (n / p^3) : ℕ) : ZMod p) = 0 := by
    push_cast
    have : (p : ZMod p) = 0 := ZMod.natCast_self p
    rw [this]
    ring
  rw [h_zero, add_zero]

lemma val_add_cast_to_p (p : ℕ) (hp : p.Prime) (A B : ZMod (p^3)) :
    (((A + B).val : ℕ) : ZMod p) = (A.val : ZMod p) + (B.val : ZMod p) := by
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  have h_val := ZMod.val_add A B
  rw [h_val]
  rw [mod_p_cub_cast_to_p p hp]
  push_cast
  rfl

lemma sum_val_cast_to_p (p : ℕ) (hp : p.Prime) (s : Finset ℕ) (x : ℕ → ZMod (p^3)) :
    (((∑ i ∈ s, x i).val : ℕ) : ZMod p) = ∑ i ∈ s, (((x i).val : ZMod p)) := by
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    rw [val_add_cast_to_p p hp]
    rw [ih]

lemma val_mul_cast_to_p (p : ℕ) (hp : p.Prime) (A B : ZMod (p^3)) :
    (((A * B).val : ℕ) : ZMod p) = (A.val : ZMod p) * (B.val : ZMod p) := by
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  have h_val := ZMod.val_mul A B
  rw [h_val]
  rw [mod_p_cub_cast_to_p p hp]
  push_cast; rfl

lemma inv_val_cast_to_p (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    (((j : ZMod (p^3))⁻¹).val : ZMod p) = (j : ZMod p)⁻¹ := by
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  set X : ZMod p := (j : ZMod p)
  set Y : ZMod p := (((j : ZMod (p^3))⁻¹).val : ZMod p)
  set Z : ZMod p := (j : ZMod p)⁻¹
  have h_cop_p : Nat.Coprime j p := by
    have h1 : ¬ p ∣ j := by
      intro hdvd
      have : p ≤ j := Nat.le_of_dvd (by omega) hdvd
      omega
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
  have h_XZ : X * Z = 1 := ZMod.coe_mul_inv_eq_one j h_cop_p
  have h_j_inv : (j : ZMod (p^3)) * (j : ZMod (p^3))⁻¹ = 1 := by
    exact ZMod.coe_mul_inv_eq_one j (j_coprime_p_cub p hp j hj1 hjp)
  have h_cast : (((j : ZMod (p^3)) * (j : ZMod (p^3))⁻¹).val : ZMod p) = 1 := by
    rw [h_j_inv]
    have hp2 := hp.two_le
    have h_le1 : p ≤ p * p := by nlinarith [hp2]
    have h_le2 : p * p ≤ p * p * p := by nlinarith [hp2]
    have h_le3 : p ≤ p * p * p := by omega
    have h_ring : p^3 = p * p * p := by ring
    have h_le4 : p ≤ p^3 := by rw [h_ring]; exact h_le3
    have h_p1 : 1 < p := by omega
    have h_p3_gt : 1 < p^3 := by omega
    haveI : Fact (1 < p^3) := ⟨h_p3_gt⟩
    have h_one : (1 : ZMod (p^3)).val = 1 := ZMod.val_one (p^3)
    rw [h_one]
    push_cast; rfl
  have h_mul_cast := val_mul_cast_to_p p hp (j : ZMod (p^3)) ((j : ZMod (p^3))⁻¹)
  rw [h_cast] at h_mul_cast
  have h_val_j : ((j : ZMod (p^3)).val : ZMod p) = X := by
    have h_lt : j < p^3 := by
      have hp2 := hp.two_le
      have h_le1 : p ≤ p * p := by nlinarith [hp2]
      have h_le2 : p * p ≤ p * p * p := by nlinarith [hp2]
      have h_le3 : p ≤ p * p * p := by omega
      have h_ring : p^3 = p * p * p := by ring
      have h_le4 : p ≤ p^3 := by rw [h_ring]; exact h_le3
      omega
    rw [ZMod.val_natCast_of_lt h_lt]
  rw [h_val_j] at h_mul_cast
  have h_XY : X * Y = 1 := h_mul_cast.symm
  calc Y
    _ = 1 * Y := by ring
    _ = (Z * X) * Y := by rw [mul_comm Z X, h_XZ]
    _ = Z * (X * Y) := by ring
    _ = Z * 1 := by rw [h_XY]
    _ = Z := by ring

lemma S_pair_eq_zero_mod_p (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (((∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (x : ZMod (p^3))⁻¹ * (y : ZMod (p^3))⁻¹ else 0).val : ℕ) : ZMod p) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set S_pair := ∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (x : ZMod (p^3))⁻¹ * (y : ZMod (p^3))⁻¹ else 0
  have h_val : (S_pair.val : ZMod p) = ∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (x : ZMod p)⁻¹ * (y : ZMod p)⁻¹ else 0 := by
    rw [sum_val_cast_to_p p hp]
    apply sum_congr rfl
    intro x hx
    rw [sum_val_cast_to_p p hp]
    apply sum_congr rfl
    intro y hy
    rw [mem_Ico] at hx hy
    split_ifs with h_lt
    · rw [val_mul_cast_to_p p hp]
      rw [inv_val_cast_to_p p hp x hx.1 hx.2]
      rw [inv_val_cast_to_p p hp y hy.1 hy.2]
    · simp
  rw [h_val]
  have h_id := sum_pairs_identity (Ico 1 p) (fun (j : ℕ) => (j : ZMod p)⁻¹)
  have h_sum_inv : ∑ x ∈ Ico 1 p, (x : ZMod p)⁻¹ = 0 := sum_inv_eq_zero p hp (by omega)
  have h_sum_inv_sq : ∑ x ∈ Ico 1 p, ((x : ZMod p)⁻¹)^2 = 0 := sum_inv_squares_eq_zero p hp hp5
  have h_zero : ((∑ x ∈ Ico 1 p, (x : ZMod p)⁻¹) ^ 2 - ∑ x ∈ Ico 1 p, ((x : ZMod p)⁻¹ ^ 2)) = 0 := by
    rw [h_sum_inv, h_sum_inv_sq]
    ring
  rw [h_zero] at h_id
  have h_two : (2 : ZMod p) ≠ 0 := by
    intro h
    have : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by rfl
    rw [this] at h
    rw [ZMod.natCast_eq_zero_iff] at h
    have : p ∣ 2 := h
    have : p ≤ 2 := Nat.le_of_dvd (by decide) this
    omega
  exact mul_eq_zero.mp h_id |>.resolve_left h_two

theorem wolstenholme_2 (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ((3 * p - 1).choose (p - 1) : ZMod (p^3)) = 1 := by
  rw [choose_mod_p_cubed p hp hp5]
  have h_rw : ∏ j ∈ Ico 1 p, (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹) =
      ∏ j ∈ Ico 1 p, (1 + (p : ZMod (p^3)) * (2 * (j : ZMod (p^3))⁻¹)) := by
    apply prod_congr rfl
    intro j hj
    ring
  rw [h_rw]
  rw [prod_expansion p hp hp5]
  have h_term1 : (p : ZMod (p^3)) * (∑ j ∈ Ico 1 p, 2 * (j : ZMod (p^3))⁻¹) = 0 := by
    have h_eq : (∑ j ∈ Ico 1 p, 2 * (j : ZMod (p^3))⁻¹) = 2 * (∑ j ∈ Ico 1 p, (j : ZMod (p^3))⁻¹) := by
      rw [mul_sum]
    rw [h_eq]
    have h_zero : (p : ZMod (p^3)) * (∑ j ∈ Ico 1 p, (j : ZMod (p^3))⁻¹) = 0 := by
      apply p_mul_eq_zero_of_val_divisible_cubed p hp
      rw [sum_val_cast_cub p hp]
      have h_congr : ∑ j ∈ Ico 1 p, ((((j : ZMod (p^3))⁻¹).val : ℕ) : ZMod (p^2)) = ∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹) := by
        apply sum_congr rfl
        intro j hj
        rw [mem_Ico] at hj
        exact inv_val_cast_cub p hp j hj.1 hj.2
      rw [h_congr]
      exact sum_inv_eq_zero_mod_p_sq p hp hp5
    calc (p : ZMod (p^3)) * (2 * ∑ j ∈ Ico 1 p, (j : ZMod (p^3))⁻¹)
      _ = 2 * ((p : ZMod (p^3)) * ∑ j ∈ Ico 1 p, (j : ZMod (p^3))⁻¹) := by ring
      _ = 2 * 0 := by rw [h_zero]
      _ = 0 := by ring
  have h_term2 : (p : ZMod (p^3))^2 * (∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (2 * (x : ZMod (p^3))⁻¹) * (2 * (y : ZMod (p^3))⁻¹) else 0) = 0 := by
    have h_eq : (∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (2 * (x : ZMod (p^3))⁻¹) * (2 * (y : ZMod (p^3))⁻¹) else 0) =
        4 * (∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (x : ZMod (p^3))⁻¹ * (y : ZMod (p^3))⁻¹ else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [mul_sum]
      apply sum_congr rfl
      intro y hy
      split_ifs with h_lt
      · ring
      · ring
    rw [h_eq]
    have h_zero : (p : ZMod (p^3))^2 * (∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (x : ZMod (p^3))⁻¹ * (y : ZMod (p^3))⁻¹ else 0) = 0 := by
      apply p_sq_mul_eq_zero_of_val_divisible_cubed p hp
      exact S_pair_eq_zero_mod_p p hp hp5
    calc (p : ZMod (p^3))^2 * (4 * (∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (x : ZMod (p^3))⁻¹ * (y : ZMod (p^3))⁻¹ else 0))
      _ = 4 * ((p : ZMod (p^3))^2 * (∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (x : ZMod (p^3))⁻¹ * (y : ZMod (p^3))⁻¹ else 0)) := by ring
      _ = 4 * 0 := by rw [h_zero]
      _ = 0 := by ring
  rw [h_term1, h_term2]
  ring

lemma choose_mod_p_cubed_nat (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (3 * p - 1).choose (p - 1) ≡ 1 [MOD p^3] := by
  have h := wolstenholme_2 p hp hp5
  have h_cast : (((3 * p - 1).choose (p - 1) : ℕ) : ZMod (p^3)) = (((1 : ℕ) : ZMod (p^3))) := by
    rw [h]
    push_cast; rfl
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_cast

lemma dvd_sub_of_mod_eq_three {a m : ℕ} (h_mod : a % m = 3) (_h_gt : 3 < m) :
    m ∣ a - 3 := by
  have h_eq : a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
  rw [h_mod] at h_eq
  have h_sub : a - 3 = m * (a / m) := by omega
  exact ⟨a / m, h_sub⟩

lemma S1_mod_p_cub (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (3 * p).choose p ≡ 3 [MOD p^3] := by
  have h1 := S1_eq_mul_choose p hp
  have h2 := choose_mod_p_cubed_nat p hp hp5
  have h3 : 3 * (3 * p - 1).choose (p - 1) ≡ 3 * 1 [MOD p^3] := by
    exact Nat.ModEq.mul_left 3 h2
  rw [mul_one] at h3
  rw [← h1] at h3
  exact h3

lemma S1_minus_three_sq_mod_p_five (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ((3 * p).choose p - 3)^2 ≡ 0 [MOD p^5] := by
  have h_mod := S1_mod_p_cub p hp hp5
  have h_gt : 3 < p^3 := by
    have : p ≥ 5 := hp5
    have : p^3 ≥ 5^3 := Nat.pow_le_pow_left this 3
    omega
  have h_eq_mod : (3 * p).choose p % p^3 = 3 := by
    have h_mod3 : 3 % p^3 = 3 := Nat.mod_eq_of_lt h_gt
    rw [Nat.ModEq] at h_mod
    rw [h_mod, h_mod3]
  have hdvd := dvd_sub_of_mod_eq_three h_eq_mod h_gt
  rcases hdvd with ⟨k, hk⟩
  have h_sq : ((3 * p).choose p - 3)^2 = p^5 * (p * k^2) := by
    calc ((3 * p).choose p - 3)^2
      _ = (p^3 * k)^2 := by rw [hk]
      _ = p^6 * k^2 := by ring
      _ = p^5 * (p * k^2) := by ring
  rw [Nat.ModEq]
  rw [h_sq]
  simp


lemma coprime_27_p5 (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) : Nat.Coprime 27 (p^5) := by
  have h1 : p ≠ 3 := by omega
  have h2 : ¬ p ∣ 3 := by
    intro hdvd
    have : p ≤ 3 := Nat.le_of_dvd (by decide) hdvd
    omega
  have h3 : Nat.Coprime 3 p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h2).symm
  have h4 : Nat.Coprime 27 p := by
    have : 27 = 3^3 := by rfl
    rw [this]
    exact Nat.Coprime.pow_left 3 h3
  exact Nat.Coprime.pow_right 5 h4

lemma cancel_27 {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) (A B : ZMod (p^5)) (h : (27 : ZMod (p^5)) * A = (27 : ZMod (p^5)) * B) : A = B := by
  have h_cop := coprime_27_p5 p hp hp5
  have h_inv := ZMod.coe_mul_inv_eq_one 27 h_cop
  have h_inv2 : ((27 : ZMod (p^5)) * (27 : ZMod (p^5))⁻¹) = 1 := by
    have : (27 : ZMod (p^5)) = ((27 : ℕ) : ZMod (p^5)) := by rfl
    rw [this]
    exact h_inv
  calc A
    _ = 1 * A := by ring
    _ = ((27 : ZMod (p^5)) * (27 : ZMod (p^5))⁻¹) * A := by rw [h_inv2]
    _ = (27 : ZMod (p^5))⁻¹ * ((27 : ZMod (p^5)) * A) := by ring
    _ = (27 : ZMod (p^5))⁻¹ * ((27 : ZMod (p^5)) * B) := by rw [h]
    _ = ((27 : ZMod (p^5)) * (27 : ZMod (p^5))⁻¹) * B := by ring
    _ = 1 * B := by rw [h_inv2]
    _ = B := by ring


lemma S2_S1_relation (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    3 * (Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ZMod (p^5)) +
    4 * (Finset.sum (range (2 * p + 1)) (fun k => (p + k - 1).choose k) : ZMod (p^5)) = 21 := by
  have h_S1 : (Finset.sum (range (2 * p + 1)) (fun k => (p + k - 1).choose k) : ZMod (p^5)) = ((3 * p).choose p : ZMod (p^5)) := by
    have h_eq : Finset.sum (range (2 * p + 1)) (fun k => (p + k - 1).choose k) = (3 * p).choose p := S1_eq p (by omega)
    rw [← h_eq]
    push_cast
    rfl
  sorry

theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  rcases prime_cases p hp hp3 with rfl | hp5
  · decide
  · have h1 : (A357674 p : ZMod (p^5)) = (A357674 1 : ZMod (p^5)) := by
      set S1_z : ZMod (p^5) := ∑ k ∈ range (2 * p + 1), ↑((p + k - 1).choose k)
      set S2_z : ZMod (p^5) := ∑ k ∈ range (2 * p + 1), (↑((p + k - 1).choose k) : ZMod (p^5)) ^ 2
      set X : ZMod (p^5) := S1_z - 3
      have hX : S1_z = 3 + X := by ring
      have hX2 : X^2 = 0 := by
        have h_sq := S1_minus_three_sq_mod_p_five p hp hp5
        have h_le : 3 ≤ (3 * p).choose p := by
          have h_mod := S1_mod_p_cub p hp hp5
          have h_gt : 3 < p^3 := by
            have : p ≥ 5 := hp5
            have : p^3 ≥ 5^3 := Nat.pow_le_pow_left this 3
            omega
          have h_eq_mod : (3 * p).choose p % p^3 = 3 := by
            have h_mod3 : 3 % p^3 = 3 := Nat.mod_eq_of_lt h_gt
            rw [Nat.ModEq] at h_mod
            rw [h_mod, h_mod3]
          have h_div_add : (3 * p).choose p = p^3 * ((3 * p).choose p / p^3) + 3 := by
            have := Nat.div_add_mod ((3 * p).choose p) (p^3)
            omega
          omega
        have h_S1_cast : S1_z = ((3 * p).choose p : ZMod (p^5)) := by
          have h_eq : (3 * p).choose p = Finset.sum (range (2 * p + 1)) (fun k => (p + k - 1).choose k) := (S1_eq p (by omega)).symm
          rw [h_eq]
          push_cast
          rfl
        have h_sub_cast : (((((3 * p).choose p - 3)^2 : ℕ) : ZMod (p^5))) = (S1_z - 3)^2 := by
          have h_cast1 : ( ((((3 * p).choose p - 3)^2 : ℕ) : ZMod (p^5)) ) = ( ((((3 * p).choose p - 3 : ℕ) : ZMod (p^5)) ) )^2 := by push_cast; rfl
          have h_cast2 : ((((3 * p).choose p - 3 : ℕ) : ZMod (p^5))) = ((3 * p).choose p : ZMod (p^5)) - 3 := Nat.cast_sub h_le
          rw [h_cast1, h_cast2, ← h_S1_cast]
        rw [← h_sub_cast]
        rw [ZMod.natCast_eq_zero_iff]
        rw [Nat.ModEq] at h_sq
        have h_mod : ((3 * p).choose p - 3)^2 % p^5 = 0 := by
          rw [h_sq]
          rfl
        exact Nat.dvd_of_mod_eq_zero h_mod
      have hS2 : 3 * S2_z = 9 - 4 * X := by
        have h_rel := S2_S1_relation p hp hp5
        change 3 * S2_z + 4 * S1_z = 21 at h_rel
        calc 3 * S2_z
          _ = (3 * S2_z + 4 * S1_z) - 4 * S1_z := by ring
          _ = 21 - 4 * S1_z := by rw [h_rel]
          _ = 9 - 4 * X := by ring
      have h_alg := algebra_step S1_z S2_z X hX hX2 hS2
      have h_cancel := cancel_27 hp hp5 _ _ h_alg
      have h_A_p : (A357674 p : ZMod (p^5)) = S1_z^4 * S2_z^3 := by
        unfold A357674
        push_cast
        rfl
      have h_A_1 : (A357674 1 : ZMod (p^5)) = 2187 := by
        have : A357674 1 = 2187 := rfl
        rw [this]
        push_cast; rfl
      rw [h_A_p, h_cancel, h_A_1]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h1



