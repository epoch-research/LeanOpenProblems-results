import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

open Nat Set

/--
A268597: Smallest $x$ such that $x-1 \pmod{\phi(x)} = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

theorem A268597_pos_iff (n : ℕ) : A268597 n > 0 ↔ ∃ x > 0, (x - 1) % Nat.totient x = n := by
  constructor
  · intro h
    have h_ne := Nat.nonempty_of_pos_sInf h
    rcases h_ne with ⟨x, hx⟩
    exact ⟨x, hx.1, hx.2⟩
  · intro h
    rcases h with ⟨x, hx1, hx2⟩
    have h_ne : { y : ℕ | y > 0 ∧ (y - 1) % Nat.totient y = n }.Nonempty := ⟨x, hx1, hx2⟩
    have h_mem := Nat.sInf_mem h_ne
    exact h_mem.1





theorem totient_prime_sq (p : ℕ) (hp : p.Prime) : Nat.totient (p^2) = p * (p - 1) := by
  have h1 : 0 < 2 := by decide
  have h2 := Nat.totient_prime_pow hp h1
  have h3 : p ^ (2 - 1) = p := by
    have : 2 - 1 = 1 := by decide
    rw [this, pow_one]
  rwa [h3] at h2

theorem solve_prime (n : ℕ) (hp : (n+1).Prime) : (n+1)^2 ∈ { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n } := by
  simp only [mem_setOf_eq]
  have h_pos : (n+1)^2 > 0 := sq_pos_of_pos (Nat.succ_pos n)
  refine ⟨h_pos, ?_⟩
  rw [totient_prime_sq (n+1) hp]
  have h_tot_eq : (n+1) * ((n+1) - 1) = (n+1) * n := by
    rw [Nat.add_sub_cancel]
  have h_eq : (n+1)^2 - 1 = (n+1) * n + n := by
    have : (n+1)^2 = (n+1)*n + n + 1 := by ring
    rw [this]
    exact Nat.add_sub_cancel ((n+1)*n + n) 1
  rw [h_tot_eq, h_eq]
  have h_n_pos : n > 0 := by
    by_contra h_zero
    have : n = 0 := by omega
    subst this
    exact Nat.not_prime_one hp
  have h_lt : n < (n+1) * n := by
    have : 1 < n + 1 := by omega
    have h1 : 1 * n < (n+1) * n := Nat.mul_lt_mul_of_pos_right this h_n_pos
    rwa [one_mul] at h1
  have h_mod : (n + (n+1)*n) % ((n+1)*n) = n % ((n+1)*n) := by
    have h_rew : n + (n+1)*n = n + ((n+1)*n) * 1 := by ring
    rw [h_rew]
    exact Nat.add_mul_mod_self_left n ((n+1)*n) 1
  rw [Nat.add_comm ((n+1)*n) n]
  rw [h_mod]
  exact Nat.mod_eq_of_lt h_lt

theorem solve_pow2 (k : ℕ) (hk : 0 < k) : 2^(k+1) ∈ { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = 2^k - 1 } := by
  simp only [mem_setOf_eq]
  have h_pos : 2^(k+1) > 0 := pos_of_gt (by positivity)
  refine ⟨h_pos, ?_⟩
  have h_tot : Nat.totient (2^(k+1)) = 2^k := by
    have h_prime : Nat.Prime 2 := Nat.prime_two
    have h_k1_pos : 0 < k + 1 := by omega
    have h_tot2 := Nat.totient_prime_pow h_prime h_k1_pos
    rw [h_tot2]
    have h_sub : k + 1 - 1 = k := by omega
    rw [h_sub]
    ring
  rw [h_tot]
  have h_div : 2^(k+1) - 1 = 1 * 2^k + (2^k - 1) := by
    have h_pow : 2^(k+1) = 2^k + 2^k := by ring
    rw [h_pow]
    omega
  have h_rew : 1 * 2^k + (2^k - 1) = (2^k - 1) + 2^k * 1 := by omega
  rw [h_div, h_rew]
  rw [Nat.add_mul_mod_self_left (2^k - 1) (2^k) 1]
  have h_lt : 2^k - 1 < 2^k := by omega
  exact Nat.mod_eq_of_lt h_lt




theorem coprime_pow_odd_two (p k a : ℕ) (hp : Nat.Prime p) (hp_odd : p ≠ 2) :
    Coprime (p^(k+1)) (2^a) := by
  have h_coprime : Coprime p 2 := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    have hp_ge : p ≥ 2 := hp.two_le
    have hp_eq : p = 2 := by omega
    exact hp_odd hp_eq
  exact Coprime.pow (k+1) a h_coprime

theorem totient_x_eq (p k a : ℕ) (hp : Nat.Prime p) (hp_odd : p ≠ 2) :
    Nat.totient (p^(k+1) * 2^a) = p^k * (p - 1) * Nat.totient (2^a) := by
  have h_coprime := coprime_pow_odd_two p k a hp hp_odd
  rw [Nat.totient_mul h_coprime]
  have h_prime_pow : Nat.totient (p^(k+1)) = p^k * (p - 1) := by
    have h_pos : 0 < k + 1 := by omega
    have h_tot := Nat.totient_prime_pow hp h_pos
    rw [h_tot]
    have h_sub : k + 1 - 1 = k := by omega
    rw [h_sub]
  rw [h_prime_pow]

theorem solve_p_pow_k_mul_pow_2 (p k a : ℕ) (hp : Nat.Prime p) (hp_odd : p ≠ 2) (hk : k ≥ 1) :
    let n := p^k * 2^a - 1
    let x := p^(k+1) * 2^a
    x > 0 ∧ (x - 1) % Nat.totient x = n := by
  have hp_ge3 : p ≥ 3 := by
    have : p ≥ 2 := hp.two_le
    omega
  have h_x_pos : p^(k+1) * 2^a > 0 := by
    have h1 : p^(k+1) > 0 := pos_of_gt (by positivity)
    have h2 : 2^a > 0 := pos_of_gt (by positivity)
    exact Nat.mul_pos h1 h2
  refine ⟨h_x_pos, ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · -- a = 0
    simp only [pow_zero, mul_one]
    have h_tot : Nat.totient (p^(k+1)) = p^k * (p - 1) := by
      have h_tot_eq := totient_x_eq p k 0 hp hp_odd
      simp only [pow_zero, Nat.totient_one, mul_one] at h_tot_eq
      exact h_tot_eq
    rw [h_tot]
    have h_div : p^(k+1) - 1 = (p^k - 1) + p^k * (p - 1) * 1 := by
      simp only [mul_one]
      have h_rew : p^(k+1) = p^k * p := by ring
      rw [h_rew]
      generalize hpk : p^k = P1
      generalize h_v : P1 * p = V
      have h_ge : P1 ≤ V := by
        rw [← h_v]
        exact le_mul_of_one_le_right (by omega) (by omega)
      have h_p1 : 0 < P1 := by
        rw [← hpk]
        positivity
      have h_mul : P1 * (p - 1) = V - P1 := by
        rw [← h_v]
        rw [Nat.mul_sub_left_distrib]
        simp
      rw [h_mul]
      clear h_mul h_v hpk h_tot h_x_pos hp hp_odd hk hp_ge3
      omega
    rw [h_div]
    have h_lt : p^k - 1 < p^k * (p - 1) := by
      generalize hpk : p^k = P1
      generalize h_v : P1 * p = V
      have h_ge : P1 ≤ V := by
        rw [← h_v]
        exact le_mul_of_one_le_right (by omega) (by omega)
      have h_v_ge : P1 * 3 ≤ V := by
        rw [← h_v]
        exact Nat.mul_le_mul_left P1 hp_ge3
      have h_p1 : 0 < P1 := by
        rw [← hpk]
        positivity
      have h_mul : P1 * (p - 1) = V - P1 := by
        rw [← h_v]
        rw [Nat.mul_sub_left_distrib]
        simp
      rw [h_mul]
      clear h_mul h_v hpk h_tot h_x_pos hp hp_odd hk hp_ge3 h_div
      omega
    rw [Nat.add_mul_mod_self_left (p^k - 1) (p^k * (p - 1)) 1, Nat.mod_eq_of_lt h_lt]
  · -- a ≠ 0
    have ha_pos : a ≥ 1 := by omega
    have h_tot2 : Nat.totient (2^a) = 2^(a-1) := by
      have h_prime2 : Nat.Prime 2 := Nat.prime_two
      have h_tot2_eq := Nat.totient_prime_pow h_prime2 ha_pos
      rw [h_tot2_eq]
      have h_sub : a - 1 = a - 1 := rfl
      omega
    have h_tot : Nat.totient (p^(k+1) * 2^a) = p^k * (p - 1) * 2^(a-1) := by
      have h_tot_eq := totient_x_eq p k a hp hp_odd
      rw [h_tot_eq, h_tot2]
    rw [h_tot]
    have h_div : p^(k+1) * 2^a - 1 = (p^k * 2^a - 1) + p^k * (p - 1) * 2^(a-1) * 2 := by
      have h_pow1 : p^(k+1) = p^k * p := by ring
      have h_pow2 : 2^a = 2^(a-1) * 2 := by
        have : a = a - 1 + 1 := by omega
        conv_lhs => rw [this]
        rw [pow_add, pow_one]
      rw [h_pow1, h_pow2]
      have h_rew1 : p^k * p * (2^(a-1) * 2) = p^k * p * 2^(a-1) * 2 := by ring
      have h_rew2 : p^k * (2^(a-1) * 2) = p^k * 2^(a-1) * 2 := by ring
      rw [h_rew1, h_rew2]
      generalize hpk : p^k = P1
      generalize h2a : 2^(a-1) = P2
      generalize h_a : P1 * P2 = A
      generalize h_b : P1 * p * P2 = B
      have h_ge : A ≤ B := by
        rw [← h_a, ← h_b]
        have h_le : P1 * P2 ≤ (P1 * P2) * p := le_mul_of_one_le_right (by omega) (by omega)
        have h_eq : (P1 * P2) * p = P1 * p * P2 := by ring
        rw [h_eq] at h_le
        exact h_le
      have h_a_pos : 0 < A := by
        rw [← h_a]
        have h_p1 : 0 < P1 := by
          rw [← hpk]
          positivity
        have h_p2 : 0 < P2 := by
          rw [← h2a]
          positivity
        exact Nat.mul_pos h_p1 h_p2
      have h_mul : P1 * (p - 1) * P2 * 2 = B * 2 - A * 2 := by
        rw [← h_a, ← h_b]
        have h1 : P1 * (p - 1) = P1 * p - P1 := by
          rw [Nat.mul_sub_left_distrib]
          simp
        rw [h1]
        rw [Nat.sub_mul, Nat.sub_mul]
      rw [h_mul]
      clear h_mul h_pow1 h_pow2 hpk h2a h_a h_b h_tot h_tot2 h_x_pos hp hp_odd hk hp_ge3 ha ha_pos h_rew1 h_rew2
      omega
    rw [h_div]
    have h_lt : p^k * 2^a - 1 < p^k * (p - 1) * 2^(a-1) := by
      have h_pow2 : 2^a = 2^(a-1) * 2 := by
        have : a = a - 1 + 1 := by omega
        conv_lhs => rw [this]
        rw [pow_add, pow_one]
      rw [h_pow2]
      have h_rew2 : p^k * (2^(a-1) * 2) = p^k * 2^(a-1) * 2 := by ring
      rw [h_rew2]
      generalize hpk : p^k = P1
      generalize h2a : 2^(a-1) = P2
      generalize h_a : P1 * P2 = A
      generalize h_b : P1 * p * P2 = B
      have h_ge : A ≤ B := by
        rw [← h_a, ← h_b]
        have h_le : P1 * P2 ≤ (P1 * P2) * p := le_mul_of_one_le_right (by omega) (by omega)
        have h_eq : (P1 * P2) * p = P1 * p * P2 := by ring
        rw [h_eq] at h_le
        exact h_le
      have h_ab_ge : A * 3 ≤ B := by
        rw [← h_a, ← h_b]
        have h_le : (P1 * P2) * 3 ≤ (P1 * P2) * p := Nat.mul_le_mul_left (P1 * P2) hp_ge3
        have h_eq : (P1 * P2) * p = P1 * p * P2 := by ring
        rw [h_eq] at h_le
        exact h_le
      have h_a_pos : 0 < A := by
        rw [← h_a]
        have h_p1 : 0 < P1 := by
          rw [← hpk]
          positivity
        have h_p2 : 0 < P2 := by
          rw [← h2a]
          positivity
        exact Nat.mul_pos h_p1 h_p2
      have h_mul : P1 * (p - 1) * P2 = B - A := by
        rw [← h_a, ← h_b]
        have h1 : P1 * (p - 1) = P1 * p - P1 := by
          rw [Nat.mul_sub_left_distrib]
          simp
        rw [h1]
        rw [Nat.sub_mul]
      rw [h_mul]
      clear h_mul h_pow2 hpk h2a h_a h_b h_tot h_tot2 h_x_pos hp hp_odd hk hp_ge3 ha ha_pos h_div h_rew2
      omega
    rw [Nat.add_mul_mod_self_left (p^k * 2^a - 1) (p^k * (p - 1) * 2^(a-1)) 2, Nat.mod_eq_of_lt h_lt]


/--
A268597 Conjecture: a(n) > 0 for all n.
-/


-- Optimal lookup split lemmas for n < 151
theorem spec_lt_group_0 : (k : ℕ) → k < 50 → ∃ x > 0, (x - 1) % Nat.totient x = k
  | 0, _ => ⟨1, by decide⟩
  | 1, _ => ⟨4, by decide⟩
  | 2, _ => ⟨9, by decide⟩
  | 3, _ => ⟨8, by decide⟩
  | 4, _ => ⟨25, by decide⟩
  | 5, _ => ⟨18, by decide⟩
  | 6, _ => ⟨15, by decide⟩
  | 7, _ => ⟨16, by decide⟩
  | 8, _ => ⟨21, by decide⟩
  | 9, _ => ⟨50, by decide⟩
  | 10, _ => ⟨35, by decide⟩
  | 11, _ => ⟨36, by decide⟩
  | 12, _ => ⟨33, by decide⟩
  | 13, _ => ⟨98, by decide⟩
  | 14, _ => ⟨39, by decide⟩
  | 15, _ => ⟨32, by decide⟩
  | 16, _ => ⟨65, by decide⟩
  | 17, _ => ⟨54, by decide⟩
  | 18, _ => ⟨51, by decide⟩
  | 19, _ => ⟨100, by decide⟩
  | 20, _ => ⟨45, by decide⟩
  | 21, _ => ⟨70, by decide⟩
  | 22, _ => ⟨95, by decide⟩
  | 23, _ => ⟨72, by decide⟩
  | 24, _ => ⟨69, by decide⟩
  | 25, _ => ⟨338, by decide⟩
  | 26, _ => ⟨63, by decide⟩
  | 27, _ => ⟨196, by decide⟩
  | 28, _ => ⟨161, by decide⟩
  | 29, _ => ⟨110, by decide⟩
  | 30, _ => ⟨87, by decide⟩
  | 31, _ => ⟨64, by decide⟩
  | 32, _ => ⟨93, by decide⟩
  | 33, _ => ⟨130, by decide⟩
  | 34, _ => ⟨75, by decide⟩
  | 35, _ => ⟨108, by decide⟩
  | 36, _ => ⟨217, by decide⟩
  | 37, _ => ⟨182, by decide⟩
  | 38, _ => ⟨99, by decide⟩
  | 39, _ => ⟨200, by decide⟩
  | 40, _ => ⟨185, by decide⟩
  | 41, _ => ⟨170, by decide⟩
  | 42, _ => ⟨123, by decide⟩
  | 43, _ => ⟨140, by decide⟩
  | 44, _ => ⟨117, by decide⟩
  | 45, _ => ⟨190, by decide⟩
  | 46, _ => ⟨215, by decide⟩
  | 47, _ => ⟨144, by decide⟩
  | 48, _ => ⟨141, by decide⟩
  | 49, _ => ⟨250, by decide⟩
  | _ + 50, h => by omega

theorem spec_lt_group_1 : (k : ℕ) → k < 50 → ∃ x > 0, (x - 1) % Nat.totient x = 50 + k
  | 0, _ => ⟨235, by decide⟩
  | 1, _ => ⟨676, by decide⟩
  | 2, _ => ⟨329, by decide⟩
  | 3, _ => ⟨162, by decide⟩
  | 4, _ => ⟨159, by decide⟩
  | 5, _ => ⟨392, by decide⟩
  | 6, _ => ⟨153, by decide⟩
  | 7, _ => ⟨322, by decide⟩
  | 8, _ => ⟨371, by decide⟩
  | 9, _ => ⟨220, by decide⟩
  | 10, _ => ⟨177, by decide⟩
  | 11, _ => ⟨494, by decide⟩
  | 12, _ => ⟨135, by decide⟩
  | 13, _ => ⟨128, by decide⟩
  | 14, _ => ⟨305, by decide⟩
  | 15, _ => ⟨290, by decide⟩
  | 16, _ => ⟨427, by decide⟩
  | 17, _ => ⟨260, by decide⟩
  | 18, _ => ⟨201, by decide⟩
  | 19, _ => ⟨310, by decide⟩
  | 20, _ => ⟨335, by decide⟩
  | 21, _ => ⟨216, by decide⟩
  | 22, _ => ⟨213, by decide⟩
  | 23, _ => ⟨434, by decide⟩
  | 24, _ => ⟨207, by decide⟩
  | 25, _ => ⟨364, by decide⟩
  | 26, _ => ⟨245, by decide⟩
  | 27, _ => ⟨638, by decide⟩
  | 28, _ => ⟨511, by decide⟩
  | 29, _ => ⟨400, by decide⟩
  | 30, _ => ⟨189, by decide⟩
  | 31, _ => ⟨370, by decide⟩
  | 32, _ => ⟨395, by decide⟩
  | 33, _ => ⟨340, by decide⟩
  | 34, _ => ⟨249, by decide⟩
  | 35, _ => ⟨518, by decide⟩
  | 36, _ => ⟨415, by decide⟩
  | 37, _ => ⟨280, by decide⟩
  | 38, _ => ⟨581, by decide⟩
  | 39, _ => ⟨410, by decide⟩
  | 40, _ => ⟨267, by decide⟩
  | 41, _ => ⟨380, by decide⟩
  | 42, _ => ⟨261, by decide⟩
  | 43, _ => ⟨430, by decide⟩
  | 44, _ => ⟨623, by decide⟩
  | 45, _ => ⟨288, by decide⟩
  | 46, _ => ⟨1501, by decide⟩
  | 47, _ => ⟨602, by decide⟩
  | 48, _ => ⟨279, by decide⟩
  | 49, _ => ⟨500, by decide⟩
  | _ + 50, h => by omega

theorem spec_lt_group_2 : (k : ℕ) → k < 51 → ∃ x > 0, (x - 1) % Nat.totient x = 100 + k
  | 0, _ => ⟨485, by decide⟩
  | 1, _ => ⟨462, by decide⟩
  | 2, _ => ⟨303, by decide⟩
  | 3, _ => ⟨1352, by decide⟩
  | 4, _ => ⟨225, by decide⟩
  | 5, _ => ⟨658, by decide⟩
  | 6, _ => ⟨515, by decide⟩
  | 7, _ => ⟨324, by decide⟩
  | 8, _ => ⟨321, by decide⟩
  | 9, _ => ⟨350, by decide⟩
  | 10, _ => ⟨231, by decide⟩
  | 11, _ => ⟨784, by decide⟩
  | 12, _ => ⟨545, by decide⟩
  | 13, _ => ⟨530, by decide⟩
  | 14, _ => ⟨339, by decide⟩
  | 15, _ => ⟨644, by decide⟩
  | 16, _ => ⟨297, by decide⟩
  | 17, _ => ⟨742, by decide⟩
  | 18, _ => ⟨539, by decide⟩
  | 19, _ => ⟨440, by decide⟩
  | 20, _ => ⟨1331, by decide⟩
  | 21, _ => ⟨1634, by decide⟩
  | 22, _ => ⟨1243, by decide⟩
  | 23, _ => ⟨988, by decide⟩
  | 24, _ => ⟨625, by decide⟩
  | 25, _ => ⟨510, by decide⟩
  | 26, _ => ⟨255, by decide⟩
  | 27, _ => ⟨256, by decide⟩
  | 28, _ => ⟨273, by decide⟩
  | 29, _ => ⟨610, by decide⟩
  | 30, _ => ⟨635, by decide⟩
  | 31, _ => ⟨580, by decide⟩
  | 32, _ => ⟨393, by decide⟩
  | 33, _ => ⟨854, by decide⟩
  | 34, _ => ⟨351, by decide⟩
  | 35, _ => ⟨520, by decide⟩
  | 36, _ => ⟨917, by decide⟩
  | 37, _ => ⟨570, by decide⟩
  | 38, _ => ⟨411, by decide⟩
  | 39, _ => ⟨620, by decide⟩
  | 40, _ => ⟨285, by decide⟩
  | 41, _ => ⟨670, by decide⟩
  | 42, _ => ⟨363, by decide⟩
  | 43, _ => ⟨432, by decide⟩
  | 44, _ => ⟨385, by decide⟩
  | 45, _ => ⟨938, by decide⟩
  | 46, _ => ⟨423, by decide⟩
  | 47, _ => ⟨868, by decide⟩
  | 48, _ => ⟨1529, by decide⟩
  | 49, _ => ⟨550, by decide⟩
  | 50, _ => ⟨447, by decide⟩
  | _ + 51, h => by omega

theorem spec_lt_151 (n : ℕ) (h : n < 151) : ∃ x > 0, (x - 1) % Nat.totient x = n := by
  by_cases h0 : n < 50
  · exact spec_lt_group_0 n h0
  · by_cases h1 : n < 100
    · have h_eq : n = 50 + (n - 50) := by omega
      have h_lt : n - 50 < 50 := by omega
      rw [h_eq]
      exact spec_lt_group_1 (n - 50) h_lt
    · have h_eq : n = 100 + (n - 100) := by omega
      have h_lt : n - 100 < 51 := by omega
      rw [h_eq]
      exact spec_lt_group_2 (n - 100) h_lt


theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by
  unfold A268597 sInf
  dsimp [Nat.instInfSet]
  split_ifs with h
  · have h_spec := @Nat.find_spec (fun x => x > 0 ∧ (x - 1) % Nat.totient x = n) (fun _ => Classical.propDecidable _) h
    exact h_spec.1
  · exfalso
    by_cases h0 : n < 151
    · have h_exists := spec_lt_151 n h0
      exact h h_exists
    · sorry

