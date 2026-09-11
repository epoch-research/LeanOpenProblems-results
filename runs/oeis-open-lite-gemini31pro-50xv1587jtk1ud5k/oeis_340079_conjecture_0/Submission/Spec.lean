import Mathlib

open Nat Finset BigOperators ArithmeticFunction

theorem filter_gcd_eq_totient (n d : ℕ) (hn : 0 < n) (hd : d ∈ n.divisors) :
    ((range n).filter (fun k => Nat.gcd k n = d)).card = (n / d).totient := by
  rw [totient_eq_card_coprime]
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn
  have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have H_eq : (range n).filter (fun k => Nat.gcd k n = d) = 
              ((range (n / d)).filter (fun a => (n / d).Coprime a)).image (fun a => a * d) := by
    ext x
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hx_lt, hx_gcd⟩
      have hd_dvd_x : d ∣ x := by rw [← hx_gcd]; exact Nat.gcd_dvd_left x n
      use x / d
      constructor
      · constructor
        · have H1 : x / d * d < n / d * d := by
            rw [Nat.div_mul_cancel hd_dvd_x, Nat.div_mul_cancel hd_dvd]
            exact hx_lt
          exact (Nat.mul_lt_mul_right hd_pos).mp H1
        · rw [Nat.Coprime, Nat.gcd_comm]
          apply Nat.eq_of_mul_eq_mul_right hd_pos
          have H_mul : (x / d * d).gcd (n / d * d) = d := by
            rw [Nat.div_mul_cancel hd_dvd_x, Nat.div_mul_cancel hd_dvd]
            exact hx_gcd
          rw [Nat.gcd_mul_right (x / d) d (n / d)] at H_mul
          rw [H_mul, one_mul]
      · exact Nat.div_mul_cancel hd_dvd_x
    · rintro ⟨a, ⟨ha_lt, ha_coprime⟩, rfl⟩
      constructor
      · have H1 : a * d < n / d * d := (Nat.mul_lt_mul_right hd_pos).mpr ha_lt
        rw [Nat.div_mul_cancel hd_dvd] at H1
        exact H1
      · have H_mul : (a * d).gcd (n / d * d) = a.gcd (n / d) * d := Nat.gcd_mul_right a d (n / d)
        rw [Nat.div_mul_cancel hd_dvd] at H_mul
        rw [H_mul]
        have H_coprime : a.gcd (n / d) = 1 := by rw [Nat.gcd_comm]; exact ha_coprime
        rw [H_coprime, one_mul]
  rw [H_eq]
  rw [Finset.card_image_of_injective]
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_right hd_pos hab

theorem sum_range_gcd (n : ℕ) (hn : 0 < n) :
    (range n).sum (fun k => Nat.gcd k n) = (n.divisors).sum (fun d => d * (n / d).totient) := by
  have H : ∀ k ∈ range n, Nat.gcd k n ∈ n.divisors := by
    intro k _
    rw [Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_right k n, hn.ne'⟩
  have H2 := sum_fiberwise_of_maps_to H (fun k => Nat.gcd k n)
  rw [← H2]
  apply sum_congr rfl
  intro d hd
  have H3 : (∑ i ∈ (range n).filter (fun k => Nat.gcd k n = d), Nat.gcd i n) =
            ∑ i ∈ (range n).filter (fun k => Nat.gcd k n = d), d := by
    apply sum_congr rfl
    intro i hi
    simp only [mem_filter] at hi
    exact hi.2
  rw [H3, sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  exact filter_gcd_eq_totient n d hn hd

def A018804 (n : ℕ) : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n

def totientAF : ArithmeticFunction ℕ :=
  ⟨fun n => n.totient, by simp⟩

def A_AF : ArithmeticFunction ℕ := ArithmeticFunction.id * totientAF

theorem A018804_eq_A_AF (n : ℕ) (hn : 0 < n) : A018804 n = A_AF n := by
  dsimp [A018804, A_AF, ArithmeticFunction.mul_apply, totientAF]
  have H : Ico 1 (n + 1) = (Ico 1 n) ∪ {n} := by
    ext x
    simp only [mem_Ico, mem_union, mem_singleton]
    omega
  have H2 : range n = {0} ∪ (Ico 1 n) := by
    ext x
    simp only [mem_range, mem_union, mem_singleton, mem_Ico]
    omega
  have H3 : (Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) = (range n).sum (fun k => Nat.gcd k n) := by
    rw [H, H2]
    rw [sum_union, sum_union]
    · simp [Nat.gcd_zero_left, Nat.gcd_self, add_comm]
    · simp
    · simp
  rw [H3, sum_range_gcd n hn]
  rw [← Nat.sum_divisorsAntidiagonal (fun i j => i * j.totient)]

theorem A_AF_prime (p : ℕ) (hp : p.Prime) : A_AF p = 2 * p - 1 := by
  have hp_pos : 0 < p := hp.pos
  have H : A018804 p = A_AF p := A018804_eq_A_AF p hp_pos
  rw [← H]
  dsimp [A018804]
  have H2 : (Ico 1 (p + 1)).sum (fun k => Nat.gcd k p) = (range p).sum (fun k => Nat.gcd k p) := by
    have H_ico : Ico 1 (p + 1) = (Ico 1 p) ∪ {p} := by
      ext x
      simp only [mem_Ico, mem_union, mem_singleton]
      omega
    have H2_range : range p = {0} ∪ (Ico 1 p) := by
      ext x
      simp only [mem_range, mem_union, mem_singleton, mem_Ico]
      omega
    rw [H_ico, H2_range]
    rw [sum_union, sum_union]
    · simp [Nat.gcd_zero_left, Nat.gcd_self, add_comm]
    · simp
    · simp
  rw [H2]
  have H3 : (range p).sum (fun k => Nat.gcd k p) = p + (p - 1) := by
    have H_sum : (range p).sum (fun k => Nat.gcd k p) = Nat.gcd 0 p + (Ico 1 p).sum (fun k => Nat.gcd k p) := by
      have H2_range : range p = {0} ∪ (Ico 1 p) := by
        ext x
        simp only [mem_range, mem_union, mem_singleton, mem_Ico]
        omega
      rw [H2_range, sum_union]
      · rfl
      · simp
    rw [H_sum, Nat.gcd_zero_left]
    have H_ico_sum : (Ico 1 p).sum (fun k => Nat.gcd k p) = p - 1 := by
      have H_eq : (Ico 1 p).sum (fun k => Nat.gcd k p) = (Ico 1 p).sum (fun k => 1) := by
        apply sum_congr rfl
        intro k hk
        simp only [mem_Ico] at hk
        exact Nat.Coprime.gcd_eq_one (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 hk.2)))
      rw [H_eq, sum_const]
      simp
    rw [H_ico_sum]
  rw [H3]
  omega

theorem totientAF_isMultiplicative : ArithmeticFunction.IsMultiplicative totientAF := by
  constructor
  · simp [totientAF]
  · intro m n hm
    dsimp [totientAF]
    exact Nat.totient_mul hm

theorem A_AF_isMultiplicative : ArithmeticFunction.IsMultiplicative A_AF := by
  apply ArithmeticFunction.IsMultiplicative.mul
  · exact ArithmeticFunction.isMultiplicative_id
  · exact totientAF_isMultiplicative

theorem p_dvd_totient_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) : p ∣ (p ^ k).totient := by
  have H : (p ^ k).totient = p ^ (k - 1) * (p - 1) := Nat.totient_prime_pow hp (by omega)
  rw [H]
  apply dvd_mul_of_dvd_left
  use p ^ (k - 2)
  rw [← pow_succ']
  congr 1
  omega

theorem eq_one_or_p_dvd (p k d : ℕ) (hp : p.Prime) (hd : d ∣ p ^ k) : d = 1 ∨ p ∣ d := by
  rcases eq_or_ne d 1 with rfl | hne
  · exact Or.inl rfl
  · rcases Nat.exists_prime_and_dvd hne with ⟨q, hq, hqd⟩
    have hqp : q ∣ p := Nat.Prime.dvd_of_dvd_pow hq (dvd_trans hqd hd)
    have hqp_eq : q = p := by
      cases Nat.Prime.eq_one_or_self_of_dvd hp q hqp with
      | inl h1 => exact False.elim (hq.ne_one h1)
      | inr h2 => exact h2
    rw [← hqp_eq]
    exact Or.inr hqd

theorem p_dvd_A_AF_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) : p ∣ A_AF (p ^ k) := by
  dsimp [A_AF, ArithmeticFunction.mul_apply, totientAF]
  rw [Nat.sum_divisorsAntidiagonal (fun i j => i * j.totient)]
  apply dvd_sum
  intro d hd
  have hd_dvd : d ∣ p ^ k := Nat.dvd_of_mem_divisors hd
  rcases eq_one_or_p_dvd p k d hp hd_dvd with hd1 | hpd
  · rw [hd1]
    simp only [Nat.div_one, one_mul]
    exact p_dvd_totient_prime_pow p k hp hk
  · exact dvd_mul_of_dvd_left hpd _

theorem n_eq_p_pow_mul (n p : ℕ) (hp : p.Prime) (hn : 0 < n) : 
  ∃ k m, n = p ^ k * m ∧ p.Coprime m ∧ padicValNat p n = k := by
  let k := padicValNat p n
  use k
  let m := n / p^k
  use m
  have h_dvd := pow_padicValNat_dvd (p := p) (n := n)
  have H1 : n = p ^ k * m := (Nat.mul_div_cancel' h_dvd).symm
  refine ⟨H1, ?_, rfl⟩
  rw [hp.coprime_iff_not_dvd]
  intro hp_dvd
  have H2 : p ^ (k + 1) ∣ n := by
    rw [H1, pow_succ]
    exact mul_dvd_mul_left (p^k) hp_dvd
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have H3 := (padicValNat_dvd_iff (k + 1) n).mp H2
  rcases H3 with H3_0 | H3_le
  · exact hn.ne' H3_0
  · omega

theorem no_square_divides (n : ℕ) (hn_dvd : n ∣ 1 + A018804 n) : ∀ p, p.Prime → ¬ (p ^ 2 ∣ n) := by
  intro p hp hp2
  have hp_pos : 0 < p := hp.pos
  have hn_pos : 0 < n := by
    by_contra! h
    have h_eq : n = 0 := by omega
    have hn_dvd_0 : 0 ∣ 1 + A018804 0 := by
      have H := hn_dvd
      rw [h_eq] at H
      exact H
    have H0 : 1 + A018804 0 = 1 := rfl
    rw [H0] at hn_dvd_0
    have := Nat.eq_zero_of_zero_dvd hn_dvd_0
    omega
  have ⟨k, m, hn_eq, h_coprime, hk_eq⟩ := n_eq_p_pow_mul n p hp hn_pos
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have H_k_ge : 2 ≤ k := by
    have H3 := (padicValNat_dvd_iff 2 n).mp hp2
    rcases H3 with H3_0 | H3_le
    · exact (hn_pos.ne' H3_0).elim
    · rw [hk_eq] at H3_le
      exact H3_le
  have H_A_n : A018804 n = A_AF (p ^ k) * A_AF m := by
    rw [A018804_eq_A_AF n hn_pos]
    rw [hn_eq]
    apply ArithmeticFunction.IsMultiplicative.map_mul_of_coprime A_AF_isMultiplicative
    exact Nat.Coprime.pow_left k h_coprime
  have p_dvd_A_pk : p ∣ A_AF (p ^ k) := p_dvd_A_AF_prime_pow p k hp H_k_ge
  have p_dvd_A_n : p ∣ A018804 n := by
    rw [H_A_n]
    exact dvd_mul_of_dvd_left p_dvd_A_pk _
  have p_dvd_n : p ∣ n := by
    rw [hn_eq]
    exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m
  have p_dvd_1_add_A : p ∣ 1 + A018804 n := dvd_trans p_dvd_n hn_dvd
  have p_dvd_1 : p ∣ 1 := by
    rw [add_comm] at p_dvd_1_add_A
    rw [Nat.dvd_add_right p_dvd_A_n] at p_dvd_1_add_A
    exact p_dvd_1_add_A
  exact hp.not_dvd_one p_dvd_1

def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

theorem a_eq_one_of_prime_or_one (n : ℕ) (hn : n = 1 ∨ n.Prime) : a n = 1 := by
  rcases hn with rfl | hp
  · dsimp [a, A018804]
    have H : (Ico 1 (1 + 1)).sum (fun k => Nat.gcd k 1) = 1 := by
      rfl
    rw [H]
    rfl
  · have hp_pos : 0 < n := hp.pos
    have H1 : A018804 n = A_AF n := A018804_eq_A_AF n hp_pos
    have H2 : A_AF n = 2 * n - 1 := A_AF_prime n hp
    dsimp [a]
    have H_A : (Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) = 2 * n - 1 := Eq.trans H1 H2
    rw [H_A]
    have H_add : 1 + (2 * n - 1) = 2 * n := by omega
    rw [H_add]
    have H_gcd : Nat.gcd n (2 * n) = n := by
      exact Nat.gcd_eq_left (dvd_mul_left n 2)
    rw [H_gcd]
    exact Nat.div_self hp_pos

theorem p_eq_2_k_eq_2 (q : ℕ) (hq : q.Prime) :
  ¬ (2 * q ∣ 1 + (2 * 2 - 1) * (2 * q - 1)) := by
  intro h
  have hq_pos : 1 ≤ q := Nat.Prime.pos hq
  have H : 1 + (2 * 2 - 1) * (2 * q - 1) = 6 * q - 2 := by omega
  rw [H] at h
  rcases h with ⟨K, hK⟩
  have hK_pos : 0 < K := by
    by_contra hK0
    have : K = 0 := by omega
    rw [this] at hK
    omega
  have H_K_lt : K < 3 := by
    by_contra hK3
    have h3 : 3 ≤ K := by omega
    have h1 : 6 * q ≤ 2 * q * K := by
      calc 6 * q = 2 * q * 3 := by ring
      _ ≤ 2 * q * K := Nat.mul_le_mul_left (2 * q) h3
    omega
  interval_cases K
  · have h_eq : 2 * q * 1 = 2 * q := by ring
    rw [h_eq] at hK
    have Hq : q = 1 := by omega
    have hq_not : ¬ q.Prime := by rw [Hq]; exact Nat.not_prime_one
    exact hq_not hq
  · have h_eq : 2 * q * 2 = 4 * q := by ring
    rw [h_eq] at hK
    have Hq : q = 1 := by omega
    have hq_not : ¬ q.Prime := by rw [Hq]; exact Nat.not_prime_one
    exact hq_not hq

theorem p_odd_k_eq_2 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) :
  ¬ (p * q ∣ 1 + (2 * p - 1) * (2 * q - 1)) := by
  intro h
  have hp1 : 1 ≤ 2 * p := by omega
  have hq1 : 1 ≤ 2 * q := by omega
  have h_z : ((p * q : ℕ) : ℤ) ∣ ((1 + (2 * p - 1) * (2 * q - 1) : ℕ) : ℤ) := by
    exact Int.ofNat_dvd.mpr h
  have H : ((1 + (2 * p - 1) * (2 * q - 1) : ℕ) : ℤ) = 4 * (p : ℤ) * (q : ℤ) + 2 - 2 * (p : ℤ) - 2 * (q : ℤ) := by
    push_cast
    have H1 : ((2 * p - 1 : ℕ) : ℤ) = 2 * (p : ℤ) - 1 := by exact Nat.cast_sub hp1
    have H2 : ((2 * q - 1 : ℕ) : ℤ) = 2 * (q : ℤ) - 1 := by exact Nat.cast_sub hq1
    rw [H1, H2]
    ring
  rw [H] at h_z
  rcases h_z with ⟨K, hK⟩
  have hp_z : 3 ≤ (p : ℤ) := by exact_mod_cast hp3
  have hq_z : 3 ≤ (q : ℤ) := by exact_mod_cast hq3
  have H_pq_cast : ((p * q : ℕ) : ℤ) = (p : ℤ) * (q : ℤ) := by push_cast; rfl
  rw [H_pq_cast] at hK
  have hK_pos : 0 < K := by
    by_contra! hK0
    have h_neg : (p : ℤ) * (q : ℤ) * K ≤ 0 := by nlinarith
    nlinarith
  have hK_lt : K < 4 := by
    by_contra! hK4
    have h_gt : (p : ℤ) * (q : ℤ) * K ≥ 4 * (p : ℤ) * (q : ℤ) := by nlinarith
    nlinarith
  interval_cases K
  · have h1 : (p : ℤ) * (q : ℤ) * 1 = (p : ℤ) * (q : ℤ) := by ring
    rw [h1] at hK
    nlinarith
  · have h2 : (p : ℤ) * (q : ℤ) * 2 = 2 * (p : ℤ) * (q : ℤ) := by ring
    rw [h2] at hK
    nlinarith
  · have h3 : (p : ℤ) * (q : ℤ) * 3 = 3 * (p : ℤ) * (q : ℤ) := by ring
    rw [h3] at hK
    have h_fac : ((p : ℤ) - 2) * ((q : ℤ) - 2) = 2 := by nlinarith
    have h_p2 : 1 ≤ (p : ℤ) - 2 := by nlinarith
    have h_q2 : 1 ≤ (q : ℤ) - 2 := by nlinarith
    have h_p_bound : (p : ℤ) - 2 ≤ 2 := by nlinarith
    have h_p_cases : (p : ℤ) = 3 ∨ (p : ℤ) = 4 := by omega
    rcases h_p_cases with hp_eq_3 | hp_eq_4
    · have h_q_eq : (q : ℤ) = 4 := by nlinarith
      have Hq : q = 4 := by exact_mod_cast h_q_eq
      have hq_not : ¬ q.Prime := by rw [Hq]; exact by decide
      exact hq_not hq
    · have Hp : p = 4 := by exact_mod_cast hp_eq_4
      have hp_not : ¬ p.Prime := by rw [Hp]; exact by decide
      exact hp_not hp

theorem no_two_prime_factors (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hl : p < q) :
  ¬ (p * q ∣ 1 + (2 * p - 1) * (2 * q - 1)) := by
  intro h
  rcases eq_or_lt_of_le (Nat.Prime.two_le hp) with rfl | hp3
  · exact p_eq_2_k_eq_2 q hq h
  rcases eq_or_lt_of_le (Nat.Prime.two_le hq) with rfl | hq3
  · rw [mul_comm] at h
    rw [mul_comm (2 * p - 1)] at h
    exact p_eq_2_k_eq_2 p hp h
  · exact p_odd_k_eq_2 p q hp hq hp3 hq3 h

theorem oeis_340079_conjecture_0.disproof : ¬ (∀ n, a n = 1 ↔ (n = 1 ∨ Nat.Prime n)) := by
  sorry

theorem oeis_340079_conjecture_0 (n : ℕ) : a n = 1 ↔ (n = 1 ∨ Nat.Prime n) := by
  sorry



