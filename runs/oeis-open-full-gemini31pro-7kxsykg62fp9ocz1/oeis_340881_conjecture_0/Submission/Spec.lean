import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k ↦
    (2 ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ (2 ^ j - 1))

def aR (R : Type*) [CommRing R] (n : ℕ) : R :=
  ∑ k ∈ range n, ((2:R) ^ Nat.choose (k + 1) 2) * ∏ j ∈ Ico (k + 1) n, ((2:R) ^ j - 1)

lemma a_cast {R : Type*} [CommRing R] (n : ℕ) : (a n : R) = aR R n := by
  dsimp [a, aR]
  push_cast
  apply sum_congr rfl
  intro k hk
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [mem_Ico] at hj
  have : 1 ≤ 2 ^ j := by apply Nat.one_le_two_pow
  rw [Nat.cast_sub this]
  push_cast
  rfl

lemma aR_succ {R : Type*} [CommRing R] (n : ℕ) :
    aR R (n + 1) = ((2:R) ^ n - 1) * aR R n + (2:R) ^ Nat.choose (n + 1) 2 := by
  dsimp [aR]
  rw [sum_range_succ]
  have H : ∀ k ∈ range n, ∏ j ∈ Ico (k + 1) (n + 1), ((2:R) ^ j - 1) =
      (∏ j ∈ Ico (k + 1) n, ((2:R) ^ j - 1)) * ((2:R) ^ n - 1) := by
    intro k hk
    rw [mem_range] at hk
    rw [prod_Ico_succ_top]
    omega
  have H2 : ∑ k ∈ range n, (2:R) ^ (k + 1).choose 2 * ∏ j ∈ Ico (k + 1) (n + 1), ((2:R) ^ j - 1) =
    ((2:R) ^ n - 1) * ∑ k ∈ range n, (2:R) ^ (k + 1).choose 2 * ∏ j ∈ Ico (k + 1) n, ((2:R) ^ j - 1) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [H k hk]
    ring
  rw [H2, Ico_self, prod_empty, mul_one, add_comm]

lemma two_ne_zero_zmod {p : ℕ} [hp : Fact p.Prime] (hp2 : p > 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : (p : ℤ) ∣ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact h
  have h3 : (p : ℤ) ≤ 2 := by apply Int.le_of_dvd (by decide) h2
  omega

lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  change (n + 1).choose (1 + 1) = _
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

lemma choose_add (p m : ℕ) (hp : p ≥ 1) :
    (p + m).choose 2 = p.choose 2 + (m + 1).choose 2 + m * (p - 1) := by
  induction m with
  | zero =>
    have : (1 : ℕ).choose 2 = 0 := rfl
    rw [this, zero_mul, add_zero, add_zero, add_zero]
  | succ m ih =>
    have h1 : p + (m + 1) = (p + m) + 1 := by omega
    rw [h1, choose_two_succ, ih]
    have h3 : (m + 1 + 1).choose 2 = (m + 1).choose 2 + (m + 1) := choose_two_succ (m + 1)
    rw [h3]
    have hp_cast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    zify
    rw [hp_cast]
    ring

lemma pow_choose_add (p m : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) :
    (2 : ZMod p) ^ (p + m).choose 2 = (2 : ZMod p) ^ p.choose 2 * (2 : ZMod p) ^ (m + 1).choose 2 := by
  have hp_pos : p ≥ 1 := by omega
  have h_add := choose_add p m hp_pos
  rw [h_add, pow_add, pow_add, mul_assoc]
  have H1 : (2 : ZMod p) ^ (m * (p - 1)) = 1 := by
    rw [mul_comm, pow_mul, ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp2), one_pow]
  rw [H1, mul_one]

lemma prod_shift (p m : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) :
    ∏ j ∈ Ico (p + m) (2 * p - 1), ((2:ZMod p) ^ j - 1) =
    ∏ i ∈ Ico (m + 1) p, ((2:ZMod p) ^ i - 1) := by
  have : Ico (p + m) (2 * p - 1) = (Ico (m + 1) p).map ⟨fun i => i + p - 1, fun x y (h : x + p - 1 = y + p - 1) => by omega⟩ := by
    ext a
    rw [mem_Ico, mem_map]
    simp only [mem_Ico, Function.Embedding.coeFn_mk]
    constructor
    · intro h
      refine ⟨a - (p - 1), ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [this, prod_map]
  apply prod_congr rfl
  intro x hx
  dsimp
  have H : x + p - 1 = x + (p - 1) := by omega
  rw [H, pow_add]
  have H2 : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp2)
  rw [H2, mul_one]

lemma aR_2p_minus_1_eq_sum (p : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) :
    aR (ZMod p) (2 * p - 1) = ∑ k ∈ Ico (p - 1) (2 * p - 1),
      ((2:ZMod p) ^ (k + 1).choose 2) * ∏ j ∈ Ico (k + 1) (2 * p - 1), ((2:ZMod p) ^ j - 1) := by
  dsimp [aR]
  have : ∑ k ∈ range (2 * p - 1), ((2:ZMod p) ^ (k + 1).choose 2) * ∏ j ∈ Ico (k + 1) (2 * p - 1), ((2:ZMod p) ^ j - 1) =
         ∑ k ∈ Ico (p - 1) (2 * p - 1), ((2:ZMod p) ^ (k + 1).choose 2) * ∏ j ∈ Ico (k + 1) (2 * p - 1), ((2:ZMod p) ^ j - 1) := by
    symm
    apply sum_subset
    · intro x hx
      rw [mem_Ico] at hx
      rw [mem_range]
      omega
    · intro x hx hx_not
      rw [mem_Ico] at hx_not
      rw [mem_range] at hx
      have hx_lt : x < p - 1 := by omega
      have H1 : p - 1 ∈ Ico (x + 1) (2 * p - 1) := by
        rw [mem_Ico]
        refine ⟨by omega, by omega⟩
      have H2 : (2 : ZMod p) ^ (p - 1) - 1 = 0 := by
        have h_Fermat := ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp2)
        rw [h_Fermat, sub_self]
      have H3 : ∏ j ∈ Ico (x + 1) (2 * p - 1), ((2:ZMod p) ^ j - 1) = 0 := by
        apply prod_eq_zero H1 H2
      rw [H3, mul_zero]
  exact this

lemma aR_2p_minus_1 (p : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) :
    aR (ZMod p) (2 * p - 1) = (2:ZMod p) ^ p.choose 2 * aR (ZMod p) p := by
  rw [aR_2p_minus_1_eq_sum p hp2]
  have h_map : Ico (p - 1) (2 * p - 1) = (range p).map ⟨fun m => m + p - 1, fun x y (h : x + p - 1 = y + p - 1) => by omega⟩ := by
    ext a
    rw [mem_Ico, mem_map]
    simp only [mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h
      refine ⟨a - (p - 1), ⟨by omega, by omega⟩⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [h_map, sum_map]
  dsimp [aR]
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [mem_range] at hm
  have H : m + p - 1 + 1 = p + m := by omega
  rw [H]
  rw [pow_choose_add p m hp2]
  rw [prod_shift p m hp2]
  ring

lemma aR_p (p : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) :
    aR (ZMod p) p = (2 : ZMod p) ^ p.choose 2 := by
  dsimp [aR]
  have : ∑ k ∈ range p, ((2:ZMod p) ^ (k + 1).choose 2) * ∏ j ∈ Ico (k + 1) p, ((2:ZMod p) ^ j - 1) =
         ∑ k ∈ {p - 1}, ((2:ZMod p) ^ (k + 1).choose 2) * ∏ j ∈ Ico (k + 1) p, ((2:ZMod p) ^ j - 1) := by
    symm
    apply sum_subset
    · intro x hx
      rw [mem_singleton] at hx
      rw [hx, mem_range]
      omega
    · intro x hx hx_not
      rw [mem_singleton] at hx_not
      rw [mem_range] at hx
      have H1 : p - 1 ∈ Ico (x + 1) p := by
        rw [mem_Ico]
        refine ⟨by omega, by omega⟩
      have H2 : (2 : ZMod p) ^ (p - 1) - 1 = 0 := by
        have h_Fermat := ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp2)
        rw [h_Fermat, sub_self]
      have H3 : ∏ j ∈ Ico (x + 1) p, ((2:ZMod p) ^ j - 1) = 0 := by
        apply prod_eq_zero H1 H2
      rw [H3, mul_zero]
  rw [this, sum_singleton]
  have H4 : p - 1 + 1 = p := by omega
  rw [H4, Ico_self, prod_empty, mul_one]

lemma choose_two_add (p : ℕ) : p.choose 2 + p.choose 2 = p * (p - 1) := by
  cases p with
  | zero => rfl
  | succ p =>
    induction p with
    | zero => rfl
    | succ p ih =>
      have H1 : (p + 2).choose 2 = (p + 1).choose 2 + (p + 1) := by
        change (p + 1 + 1).choose (1 + 1) = _
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      rw [H1]
      have H2 : (p + 1).choose 2 + (p + 1) + ((p + 1).choose 2 + (p + 1)) =
        ((p + 1).choose 2 + (p + 1).choose 2) + 2 * (p + 1) := by omega
      rw [H2, ih]
      have H4 : p + 1 - 1 = p := rfl
      rw [H4]
      have H5 : p + 1 + 1 - 1 = p + 1 := rfl
      rw [H5]
      ring

lemma aR_2p_minus_1_eq_one (p : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) :
    aR (ZMod p) (2 * p - 1) = 1 := by
  rw [aR_2p_minus_1 p hp2, aR_p p hp2, ← pow_add]
  rw [choose_two_add p, mul_comm, pow_mul]
  have H : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp2)
  rw [H, one_pow]

lemma choose_add_gen (x y : ℕ) : (x + y).choose 2 = x.choose 2 + y.choose 2 + x * y := by
  induction y with
  | zero =>
    have : (0 : ℕ).choose 2 = 0 := rfl
    rw [this, Nat.add_zero, add_zero, mul_zero, add_zero]
  | succ y ih =>
    have h1 : x + (y + 1) = (x + y) + 1 := by omega
    rw [h1, choose_two_succ, ih]
    have h2 : (y + 1).choose 2 = y.choose 2 + y := choose_two_succ y
    rw [h2]
    have h3 : x * (y + 1) = x * y + x := by ring
    rw [h3]
    omega

lemma choose_two_mul_two (p : ℕ) (hp : p > 2) : (2 * (p - 1)).choose 2 = (p - 1) * (2 * p - 3) := by
  have H := choose_add_gen (p - 1) (p - 1)
  have H2 : p - 1 + (p - 1) = 2 * (p - 1) := by omega
  rw [H2] at H
  rw [H]
  have H3 : (p - 1).choose 2 + (p - 1).choose 2 = (p - 1) * (p - 2) := by
    have : p - 2 = (p - 1) - 1 := by omega
    rw [this, choose_two_add]
  rw [H3]
  zify [show 2 ≤ p by omega, show 3 ≤ 2 * p by omega]
  have hp_cast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  rw [hp_cast]
  ring

lemma pow_choose_add_two (p k : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) :
    (2 : ZMod p) ^ (k + 1 + 2 * (p - 1)).choose 2 = (2 : ZMod p) ^ (k + 1).choose 2 := by
  rw [choose_add_gen, pow_add, pow_add]
  have H1 : (2 : ZMod p) ^ (2 * (p - 1)).choose 2 = 1 := by
    rw [choose_two_mul_two p hp2, pow_mul, ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp2), one_pow]
  rw [H1, mul_one]
  have h_comm2 : (k + 1) * (2 * (p - 1)) = (p - 1) * (2 * (k + 1)) := by ring
  have H2 : (2 : ZMod p) ^ ((k + 1) * (2 * (p - 1))) = 1 := by
    rw [h_comm2, pow_mul, ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp2), one_pow]
  rw [H2, mul_one]

lemma aR_mod_2 (n : ℕ) (hn : n ≥ 1) : aR (ZMod 2) n = 1 := by
  induction' n, hn using Nat.le_induction with k hk ih
  · rfl
  · rw [aR_succ, ih]
    have h1 : (2 : ZMod 2) = 0 := rfl
    rw [h1]
    have h2 : k > 0 := by omega
    have h3 : (0 : ZMod 2) ^ k = 0 := zero_pow h2.ne'
    have h4 : (k + 1).choose 2 > 0 := by
      cases k with
      | zero => contradiction
      | succ k =>
        change (k + 1 + 1).choose (1 + 1) > 0
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        omega
    have h5 : (0 : ZMod 2) ^ (k + 1).choose 2 = 0 := zero_pow h4.ne'
    rw [h3, h5]
    exact rfl

lemma aR_one (R : Type*) [CommRing R] :
    aR R 1 = 1 := by
  unfold aR
  rw [sum_range_one]
  have H : (0 + 1 : ℕ).choose 2 = 0 := rfl
  rw [H, pow_zero]
  have H2 : Ico (0 + 1) 1 = ∅ := Ico_self _
  rw [H2, prod_empty, mul_one]

lemma aR_periodic (p : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) (n : ℕ) (hn : n ≥ 1) :
    aR (ZMod p) (n + 2 * (p - 1)) = aR (ZMod p) n := by
  induction' n, hn using Nat.le_induction with k hk ih
  · have : 1 + 2 * (p - 1) = 2 * p - 1 := by omega
    rw [this, aR_2p_minus_1_eq_one p hp2]
    rw [aR_one (ZMod p)]
  · have h1 : k + 1 + 2 * (p - 1) = (k + 2 * (p - 1)) + 1 := by omega
    rw [h1, aR_succ, aR_succ, ih]
    have h2 : (2 : ZMod p) ^ (k + 2 * (p - 1)) = (2 : ZMod p) ^ k := by
      rw [pow_add]
      have H : (2 : ZMod p) ^ (2 * (p - 1)) = 1 := by
        rw [mul_comm, pow_mul, ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp2), one_pow]
      rw [H, mul_one]
    rw [h2]
    have h3 : (2 : ZMod p) ^ (k + 2 * (p - 1) + 1).choose 2 = (2 : ZMod p) ^ (k + 1).choose 2 := by
      have h4 : k + 2 * (p - 1) + 1 = k + 1 + 2 * (p - 1) := by omega
      rw [h4]
      exact pow_choose_add_two p k hp2
    rw [h3]

theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  have hp_fact : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p > 2
  · have h := aR_periodic p hp2 n hn
    have h_a : ((a (n + 2 * (p - 1)) : ZMod p)) = aR (ZMod p) (n + 2 * (p - 1)) := a_cast _
    have h_a2 : ((a n : ZMod p)) = aR (ZMod p) n := a_cast n
    have h_eq : (a (n + 2 * (p - 1)) : ZMod p) = (a n : ZMod p) := by
      rw [h_a, h_a2, h]
    have h_val : (a (n + 2 * (p - 1)) : ZMod p).val = (a n : ZMod p).val := by rw [h_eq]
    rw [ZMod.val_natCast, ZMod.val_natCast] at h_val
    exact h_val
  · have h_p_eq_2 : p = 2 := by
      have h_prime := hp.two_le
      omega
    subst h_p_eq_2
    have h1 := aR_mod_2 (n + 2 * (2 - 1)) (by omega)
    have h2 := aR_mod_2 n hn
    have h_a : (a (n + 2 * (2 - 1)) : ZMod 2) = aR (ZMod 2) (n + 2 * (2 - 1)) := a_cast _
    have h_a2 : (a n : ZMod 2) = aR (ZMod 2) n := a_cast n
    have h_eq : (a (n + 2 * (2 - 1)) : ZMod 2) = (a n : ZMod 2) := by
      rw [h_a, h_a2, h1, h2]
    have h_val : (a (n + 2 * (2 - 1)) : ZMod 2).val = (a n : ZMod 2).val := by rw [h_eq]
    rw [ZMod.val_natCast, ZMod.val_natCast] at h_val
    exact h_val

theorem oeis_340881_conjecture_0.disproof : ¬ (type_of% @oeis_340881_conjecture_0) := sorry
