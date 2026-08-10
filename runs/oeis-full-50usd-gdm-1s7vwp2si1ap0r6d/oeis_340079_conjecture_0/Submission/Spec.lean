import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def A018804 (n : ℕ) : ℕ :=
  (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n

def a (n : ℕ) : ℕ :=
  n / Nat.gcd n (1 + A018804 n)

theorem a_one : a 1 = 1 := by
  dsimp [a, A018804]
  -- Finset.Ico 1 2 is [1]
  have h1 : Finset.Ico 1 2 = {1} := rfl
  rw [h1]
  simp

theorem prime_sq_dvd_and_not_dvd_imp_sq_dvd_div {p n d : ℕ} (hp : p.Prime) (h_sq : p^2 ∣ n) (h_dvd : d ∣ n) (hp_not_dvd : ¬ p ∣ d) (hn : n > 0) : p^2 ∣ n / d := by
  have hn_ne : n ≠ 0 := by omega
  have hd_fac : d.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_not_dvd
  have h_fac : (n / d).factorization p = n.factorization p - d.factorization p := by
    rw [Nat.factorization_div h_dvd]
    rfl
  rw [hd_fac, tsub_zero] at h_fac
  have h_le : 2 ≤ n.factorization p := by
    rwa [Nat.Prime.pow_dvd_iff_le_factorization hp hn_ne] at h_sq
  rw [← h_fac] at h_le
  have hnd_ne : n / d ≠ 0 := by
    intro hc
    have : n = 0 := by
      rw [← Nat.div_mul_cancel h_dvd, hc, zero_mul]
    exact hn_ne this
  rwa [Nat.Prime.pow_dvd_iff_le_factorization hp hnd_ne]

theorem prime_sq_dvd_imp_dvd_totient {p X : ℕ} (hp : p.Prime) (h : p^2 ∣ X) : p ∣ X.totient := by
  have h_mul : p * p ∣ X := by
    rw [sq] at h
    exact h
  have hp_dvd : p ∣ X := by
    rcases h_mul with ⟨c, rfl⟩
    use p * c
    ring
  have h_div : p ∣ X / p := by
    rw [Nat.dvd_div_iff_mul_dvd hp_dvd]
    exact h_mul
  have h_eq : X = p * (X / p) := by
    rw [Nat.mul_comm, Nat.div_mul_cancel hp_dvd]
  nth_rw 1 [h_eq]
  rw [totient_mul_of_prime_of_dvd hp h_div]
  exact dvd_mul_right p (X / p).totient

theorem A018804_eq_sum_divisors (n : ℕ) (hn : n > 0) :
    A018804 n = ∑ d ∈ n.divisors, d * (n / d).totient := by
  dsimp [A018804]
  -- We first prove: ∑ k ∈ range (n + 1), Nat.gcd k n = (∑ k ∈ range n, Nat.gcd k n) + n
  have h1 : ∑ k ∈ range (n + 1), Nat.gcd k n = (∑ k ∈ range n, Nat.gcd k n) + n := by
    rw [sum_range_succ, Nat.gcd_self]
  -- Next, we prove: ∑ k ∈ range (n + 1), Nat.gcd k n = n + (∑ k ∈ Ico 1 (n + 1), Nat.gcd k n)
  have h2 : ∑ k ∈ range (n + 1), Nat.gcd k n = n + (∑ k ∈ Ico 1 (n + 1), Nat.gcd k n) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    rw [Nat.gcd_zero_left]
  -- Thus (∑ k ∈ range n, Nat.gcd k n) + n = n + (sum over Ico 1 (n + 1))
  have h3 : ∑ k ∈ range n, Nat.gcd k n = ∑ k ∈ Ico 1 (n + 1), Nat.gcd k n := by
    omega
  -- Now we rewrite our goal using h3
  rw [← h3]
  -- We want to prove: ∑ k ∈ range n, Nat.gcd k n = ∑ d ∈ n.divisors, d * (n / d).totient
  -- We use sum_fiberwise_of_maps_to with g i = Nat.gcd i n
  have h_maps : ∀ i ∈ range n, Nat.gcd i n ∈ n.divisors := by
    intro i _
    rw [mem_divisors]
    exact ⟨Nat.gcd_dvd_right i n, hn.ne'⟩
  have h_fiber := sum_fiberwise_of_maps_to h_maps (fun i => Nat.gcd i n)
  rw [← h_fiber]
  -- Now we show that for each d ∈ n.divisors, the inner sum equals d * (n / d).totient
  apply sum_congr rfl
  intro d hd
  have hd_dvd : d ∣ n := dvd_of_mem_divisors hd
  -- The inner sum is over {i ∈ range n | Nat.gcd i n = d} of Nat.gcd i n
  -- We can replace Nat.gcd i n with d
  have h_inner_eq : (∑ i ∈ range n with Nat.gcd i n = d, Nat.gcd i n) = ∑ i ∈ range n with Nat.gcd i n = d, d := by
    apply sum_congr rfl
    intro i hi
    rw [mem_filter] at hi
    exact hi.2
  rw [h_inner_eq]
  rw [sum_const, nsmul_eq_mul, mul_comm d]
  congr 1
  -- Now we want to show: (filter (fun i => Nat.gcd i n = d) (range n)).card = (n / d).totient
  have h_comm : (filter (fun i => Nat.gcd i n = d) (range n)) = {k ∈ range n | n.gcd k = d} := by
    ext x
    simp only [mem_filter]
    rw [Nat.gcd_comm]
  rw [h_comm]
  exact (totient_div_of_dvd hd_dvd).symm


theorem A018804_mul_of_prime_of_not_dvd {p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m > 0) :
    A018804 (p * m) = (2 * p - 1) * A018804 m := by
  have hp_nz : p ≠ 0 := hp.ne_zero
  have hm_nz : m ≠ 0 := hm.ne'
  have hpm_nz : p * m > 0 := Nat.mul_pos hp.pos hm
  rw [A018804_eq_sum_divisors (p * m) hpm_nz]
  have h_div_eq : (p * m).divisors = divisors m ∪ image (fun d => p * d) (divisors m) := by
    ext d
    rw [mem_divisors, mem_union, mem_divisors, mem_image]
    have h1 : p * m ≠ 0 := by omega
    have h2 : m ≠ 0 := by omega
    simp [h1, h2]
    constructor
    · intro hd
      by_cases h_pd : p ∣ d
      · rcases h_pd with ⟨d', rfl⟩
        right
        use d'
        have hd'_dvd : d' ∣ m := (Nat.mul_dvd_mul_iff_left hp.pos).mp hd
        refine ⟨hd'_dvd, rfl⟩
      · have h_cop : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr h_pd
        have hd_dvd : d ∣ m := h_cop.symm.dvd_of_dvd_mul_left hd
        left
        exact hd_dvd
    · rintro (hd | ⟨d', hd', rfl⟩)
      · exact dvd_mul_of_dvd_right hd p
      · exact Nat.mul_dvd_mul_left p hd'
  have h_disj : Disjoint (divisors m) (image (fun d => p * d) (divisors m)) := by
    rw [disjoint_left]
    intro d hd h_img
    rw [mem_image] at h_img
    rcases h_img with ⟨d', hd', rfl⟩
    have hd_dvd : p * d' ∣ m := dvd_of_mem_divisors hd
    have hp_dvd : p ∣ m := dvd_trans (dvd_mul_right p d') hd_dvd
    exact hpm hp_dvd
  rw [h_div_eq, sum_union h_disj]
  have h_sum1 : ∑ d ∈ divisors m, d * (p * m / d).totient = (p - 1) * A018804 m := by
    rw [A018804_eq_sum_divisors m hm]
    rw [mul_sum]
    apply sum_congr rfl
    intro d hd
    have hd_dvd : d ∣ m := dvd_of_mem_divisors hd
    have h_div : p * m / d = p * (m / d) := by
      rw [Nat.mul_div_assoc p hd_dvd]
    rw [h_div]
    have h_not_dvd : ¬ p ∣ m / d := by
      intro h_pd
      have hp_dvd : p ∣ m := dvd_trans h_pd (Nat.div_dvd_of_dvd hd_dvd)
      exact hpm hp_dvd
    rw [Nat.totient_mul_of_prime_of_not_dvd hp h_not_dvd]
    ring
  have h_sum2 : ∑ d ∈ image (fun d => p * d) (divisors m), d * (p * m / d).totient = p * A018804 m := by
    rw [A018804_eq_sum_divisors m hm]
    rw [sum_image]
    · rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      have hd_dvd : d ∣ m := dvd_of_mem_divisors hd
      have h_div : p * m / (p * d) = m / d := by
        rw [Nat.mul_div_mul_left m d hp.pos]
      rw [h_div]
      ring
    · intro x _ y _ hxy
      exact (Nat.mul_right_inj hp_nz).mp hxy
  rw [h_sum1, h_sum2]
  have h_alg : (p - 1) * A018804 m + p * A018804 m = (2 * p - 1) * A018804 m := by
    rw [← add_mul]
    congr 1
    omega
  exact h_alg

theorem prime_sq_dvd_imp_dvd_A018804 {p n : ℕ} (hp : p.Prime) (h_sq : p^2 ∣ n) (hn : n > 0) : p ∣ A018804 n := by
  rw [A018804_eq_sum_divisors n hn]
  apply Finset.dvd_sum
  intro d hd
  have h_dvd : d ∣ n := dvd_of_mem_divisors hd
  by_cases h_pd : p ∣ d
  · have : p ∣ d * (n / d).totient := dvd_mul_of_dvd_left h_pd (n / d).totient
    exact this
  · have h_div_sq : p^2 ∣ n / d := prime_sq_dvd_and_not_dvd_imp_sq_dvd_div hp h_sq h_dvd h_pd hn
    have h_tot_dvd : p ∣ (n / d).totient := prime_sq_dvd_imp_dvd_totient hp h_div_sq
    exact dvd_mul_of_dvd_right h_tot_dvd d

theorem squarefree_of_a_eq_one {n : ℕ} (ha1 : a n = 1) : Squarefree n := by
  by_cases hn : n = 0
  · subst hn
    have : a 0 = 0 := by rfl
    omega
  have hn_pos : n > 0 := by omega
  rw [squarefree_iff_prime_squarefree]
  intro p hp hp_sq
  have hp_sq_pow : p^2 ∣ n := by
    rwa [sq]
  have h_p_dvd : p ∣ A018804 n := prime_sq_dvd_imp_dvd_A018804 hp hp_sq_pow hn_pos
  have h_dvd : n ∣ 1 + A018804 n := by
    have h_div : n / n.gcd (1 + A018804 n) = 1 := ha1
    have h_gcd_dvd : n.gcd (1 + A018804 n) ∣ n := Nat.gcd_dvd_left _ _
    have h_gcd : n.gcd (1 + A018804 n) = n := by
      have h_mul := Nat.div_mul_cancel h_gcd_dvd
      rwa [h_div, one_mul] at h_mul
    have h_gcd_dvd_right := Nat.gcd_dvd_right n (1 + A018804 n)
    rwa [h_gcd] at h_gcd_dvd_right
  have hp_dvd : p ∣ n := by
    rcases hp_sq with ⟨c, rfl⟩
    use p * c
    ring
  have h_p_dvd_add : p ∣ 1 + A018804 n := dvd_trans hp_dvd h_dvd
  have h_p_dvd_one : p ∣ 1 := by
    have h_p_dvd_add_comm : p ∣ A018804 n + 1 := by
      have h_eq : 1 + A018804 n = A018804 n + 1 := by omega
      rwa [← h_eq]
    have h_iff : p ∣ A018804 n + 1 ↔ p ∣ 1 := (Nat.dvd_add_iff_right h_p_dvd).symm
    rwa [h_iff] at h_p_dvd_add_comm
  have h_p_ge_2 := hp.two_le
  have h_p_le_1 := Nat.le_of_dvd (by decide) h_p_dvd_one
  omega

theorem a_prime {p : ℕ} (hp : Nat.Prime p) : a p = 1 := by
  dsimp [a, A018804]
  have hp2 : 1 ≤ p := by
    have := hp.two_le
    omega
  rw [sum_Ico_succ_top hp2]
  -- Now we have: (sum over Ico 1 p) + gcd p p
  rw [Nat.gcd_self]
  -- We want to prove that (sum over Ico 1 p of (gcd k p)) = p - 1
  have h_gcd : ∀ k ∈ Ico 1 p, Nat.gcd k p = 1 := by
    intro k hk
    rw [mem_Ico] at hk
    have hk_lt : k < p := hk.2
    have hk_pos : k > 0 := hk.1
    have h_not_dvd : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt hk_pos hk_lt
    have h_cop : Nat.Coprime p k := hp.coprime_iff_not_dvd.mpr h_not_dvd
    rw [Nat.gcd_comm]
    exact h_cop
  have h_sum : (∑ k ∈ Ico 1 p, Nat.gcd k p) = p - 1 := by
    rw [sum_congr rfl h_gcd]
    rw [sum_const, card_Ico, smul_eq_mul, mul_one]
  rw [h_sum]
  have hp_pos : p > 0 := hp.pos
  have h_add : 1 + (p - 1 + p) = p * 2 := by
    omega
  rw [h_add]
  have h_gcd2 : Nat.gcd p (p * 2) = p := by
    rw [Nat.gcd_eq_left_iff_dvd]
    exact dvd_mul_right p 2
  rw [h_gcd2]
  exact Nat.div_self hp_pos

lemma qr_not_dvd_two_q_add_r (q r : ℕ) (hq : q ≥ 5) (hqr : q < r) : ¬ (q * r ∣ 2 * (q + r)) := by
  intro h
  have h1 : 2 * (q + r) < 4 * r := by omega
  have h_q4 : 4 ≤ q := by omega
  have h2 : 4 * r ≤ q * r := Nat.mul_le_mul_right r h_q4
  have h3 : 2 * (q + r) < q * r := by omega
  have h4 : 2 * (q + r) > 0 := by omega
  exact Nat.not_dvd_of_pos_of_lt h4 h3 h


theorem oeis_340079_conjecture_0 (n : ℕ) : a n = 1 ↔ (n = 1 ∨ Nat.Prime n) := by
  constructor
  · intro ha
    by_cases hn1 : n = 1
    · left; exact hn1
    right
    have h_sq : Squarefree n := squarefree_of_a_eq_one ha
    by_cases hn0 : n = 0
    · subst hn0; have : a 0 = 0 := rfl; omega
    have hn_pos : n > 0 := by omega
    have hn_gt1 : n > 1 := by omega
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn_gt1.ne'
    have hp_dvd : p ∣ n := n.minFac_dvd
    let m := n / p
    have h_eq : n = p * m := by rw [Nat.mul_comm, Nat.div_mul_cancel hp_dvd]
    have h_not_dvd_m : ¬ p ∣ m := by
      intro hp_dvd_m
      have hp_sq_dvd : p^2 ∣ n := by
        rw [sq, h_eq]
        exact mul_dvd_mul_left p hp_dvd_m
      have hp_not : ¬ p^2 ∣ n := by
        have h_pf : ¬ p * p ∣ n := squarefree_iff_prime_squarefree.mp h_sq p hp
        rwa [sq]
      exact hp_not hp_sq_dvd
    by_cases hm1 : m = 1
    · rw [h_eq, hm1, mul_one]; exact hp
    have hm_ne_zero : m ≠ 0 := by
      intro hc
      rw [hc] at h_eq
      rw [mul_zero] at h_eq
      omega
    have hm_gt1 : m > 1 := by
      rcases m with _ | _ | m'
      · exact False.elim (hm_ne_zero rfl)
      · exact False.elim (hm1 rfl)
      · omega
    have h_n_dvd : n ∣ 1 + A018804 n := by
      have h_div : n / n.gcd (1 + A018804 n) = 1 := ha
      have h_gcd_dvd : n.gcd (1 + A018804 n) ∣ n := Nat.gcd_dvd_left _ _
      have h_gcd : n.gcd (1 + A018804 n) = n := by
        have h_mul := Nat.div_mul_cancel h_gcd_dvd
        rwa [h_div, one_mul] at h_mul
      have h_gcd_dvd_right := Nat.gcd_dvd_right n (1 + A018804 n)
      rwa [h_gcd] at h_gcd_dvd_right
    have hp_dvd_A : p ∣ 1 + A018804 n := dvd_trans hp_dvd h_n_dvd
    have hm_pos : m > 0 := by omega
    have h_A_eq : A018804 n = (2 * p - 1) * A018804 m := by
      rw [h_eq]
      exact A018804_mul_of_prime_of_not_dvd hp h_not_dvd_m hm_pos
    rw [h_A_eq] at hp_dvd_A
    let X := (2 * p - 1) * A018804 m
    have hp_dvd_X1 : p ∣ X + 1 := by rwa [Nat.add_comm] at hp_dvd_A
    have h_alg_eq : X + 1 + A018804 m = p * (2 * A018804 m) + 1 := by
      dsimp [X]
      have hp_ge : p ≥ 2 := hp.two_le
      have h_succ : succ (2 * p - 1) = 2 * p := by omega
      have h_mul : (2 * p - 1) * A018804 m + A018804 m = 2 * p * A018804 m := by
        rw [← Nat.succ_mul, h_succ]
      rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc, h_mul]
      ring
    rcases hp_dvd_X1 with ⟨c, hc⟩
    have h_mod : (X + 1 + A018804 m) % p = A018804 m % p := by
      have : X + 1 + A018804 m = p * c + A018804 m := by omega
      rw [this]
      rw [Nat.add_comm]
      exact Nat.add_mul_mod_self_left (A018804 m) p c
    have h_mod_val : (X + 1 + A018804 m) % p = 1 := by
      rw [h_alg_eq]
      rw [Nat.add_comm]
      rw [Nat.add_mul_mod_self_left 1 p (2 * A018804 m)]
      exact Nat.mod_eq_of_lt hp.one_lt
    have h_mod_m : A018804 m % p = 1 := by
      rw [← h_mod, h_mod_val]

    let q := m.minFac
    have hq : q.Prime := Nat.minFac_prime hm_gt1.ne'
    have hq_dvd_m : q ∣ m := m.minFac_dvd
    have hq_dvd_n : q ∣ n := dvd_trans hq_dvd_m (by rw [h_eq]; exact ⟨p, by ring⟩)
    have hp_le_q : p ≤ q := Nat.minFac_le_of_dvd hq.two_le hq_dvd_n
    have hp_lt_q : p < q := by
      by_cases hpq : p = q
      · rw [hpq] at h_not_dvd_m
        exact False.elim (h_not_dvd_m hq_dvd_m)
      · omega
    let k := m / q
    have h_eq_m : m = q * k := by rw [Nat.mul_comm, Nat.div_mul_cancel hq_dvd_m]
    have hm_sq : Squarefree m := Squarefree.of_mul_right (by rw [h_eq] at h_sq; exact h_sq)
    have h_not_dvd_k : ¬ q ∣ k := by
      intro hq_dvd_k
      have hq_sq_dvd : q^2 ∣ m := by
        rw [sq, h_eq_m]
        exact mul_dvd_mul_left q hq_dvd_k
      have hq_not : ¬ q^2 ∣ m := by
        have h_pf : ¬ q * q ∣ m := squarefree_iff_prime_squarefree.mp hm_sq q hq
        rwa [sq]
      exact hq_not hq_sq_dvd
    have hk_ne_zero : k ≠ 0 := by
      intro hc
      rw [hc] at h_eq_m
      rw [mul_zero] at h_eq_m
      omega
    have hk_pos : k > 0 := by
      rcases k with _ | k'
      · exact False.elim (hk_ne_zero rfl)
      · omega
    have h_Am_eq : A018804 m = (2 * q - 1) * A018804 k := by
      rw [h_eq_m]
      exact A018804_mul_of_prime_of_not_dvd hq h_not_dvd_k hk_pos

    have hq_dvd_A : q ∣ 1 + A018804 n := dvd_trans hq_dvd_n h_n_dvd
    have h_An_eq2 : A018804 n = (2 * p - 1) * (2 * q - 1) * A018804 k := by
      rw [h_A_eq, h_Am_eq, mul_assoc]
    rw [h_An_eq2] at hq_dvd_A
    let Y := (2 * p - 1) * A018804 k
    have h_alg_eq2 : (2 * q - 1) * Y + 1 + Y = q * (2 * Y) + 1 := by
      have hq_ge : q ≥ 2 := hq.two_le
      have h_succ : succ (2 * q - 1) = 2 * q := by omega
      have h_mul : (2 * q - 1) * Y + Y = 2 * q * Y := by
        rw [← Nat.succ_mul, h_succ]
      rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc, h_mul]
      ring
    have h_dvd_term2 : q ∣ (2 * q - 1) * Y + 1 := by
      have : 1 + (2 * p - 1) * (2 * q - 1) * A018804 k = (2 * q - 1) * Y + 1 := by
        dsimp [Y]; ring
      rwa [this] at hq_dvd_A
    rcases h_dvd_term2 with ⟨c', hc'⟩
    have h_mod2 : ((2 * q - 1) * Y + 1 + Y) % q = Y % q := by
      have : (2 * q - 1) * Y + 1 + Y = q * c' + Y := by omega
      rw [this]
      rw [Nat.add_comm]
      exact Nat.add_mul_mod_self_left Y q c'
    have h_mod_val2 : ((2 * q - 1) * Y + 1 + Y) % q = 1 := by
      rw [h_alg_eq2]
      rw [Nat.add_comm]
      rw [Nat.add_mul_mod_self_left 1 q (2 * Y)]
      exact Nat.mod_eq_of_lt hq.one_lt
    have h_mod_Y : Y % q = 1 := by
      rw [← h_mod2, h_mod_val2]

    have hq_dvd_Y1 : q ∣ Y - 1 := by
      use Y / q
      have h_div_mod := Nat.mod_add_div Y q
      rw [h_mod_Y] at h_div_mod
      omega
    have h_Y1_pos : Y - 1 > 0 := by
      have hp_ge : p ≥ 2 := hp.two_le
      have hk_ge : 1 ≤ A018804 k := by
        rw [A018804_eq_sum_divisors k hk_pos]
        have h1 : 1 ∈ k.divisors := by
          rw [mem_divisors]
          exact ⟨one_dvd k, hk_pos.ne'⟩
        have h_sum_le : 1 * (k / 1).totient ≤ ∑ d ∈ k.divisors, d * (k / d).totient := by
          apply single_le_sum (f := fun d => d * (k / d).totient) (a := 1)
          · intro d _
            positivity
          · exact h1
        have h_k1 : k / 1 = k := Nat.div_one k
        have : (k / 1).totient > 0 := by
          rw [h_k1]
          exact Nat.totient_pos.mpr hk_pos
        omega
      have : Y ≥ (2 * p - 1) * 1 := Nat.mul_le_mul_left (2 * p - 1) hk_ge
      have : Y - 1 > 0 := by omega
      exact this
    have h_q_le : q ≤ Y - 1 := Nat.le_of_dvd h_Y1_pos hq_dvd_Y1
    by_cases hk1 : k = 1
    · dsimp [Y] at *
      rw [hk1] at h_Y1_pos h_q_le hq_dvd_Y1 h_mod_Y
      have h_Y_eq : (2 * p - 1) * A018804 1 = 2 * p - 1 := by
        have : A018804 1 = 1 := by
          dsimp [A018804]
          have : Finset.Ico 1 2 = {1} := rfl
          rw [this]; simp
        rw [this, mul_one]
      rw [h_Y_eq] at hq_dvd_Y1 h_q_le
      by_cases hp2 : p = 2
      · rw [hp2] at hq_dvd_Y1 h_q_le
        have : 2 * 2 - 1 - 1 = 2 := rfl
        rw [this] at hq_dvd_Y1
        have hq_le_2 : q ≤ 2 := Nat.le_of_dvd (by decide) hq_dvd_Y1
        omega
      · have hp_odd : p > 2 := by omega
        have h_gcd : Nat.Coprime q 2 := by
          apply hq.coprime_iff_not_dvd.mpr
          intro hd
          have hq_le_2 : q ≤ 2 := Nat.le_of_dvd (by decide) hd
          have : q = 2 := by omega
          omega
        have h_div : q ∣ p - 1 := by
          have h_eq_sub2 : 2 * p - 1 - 1 = 2 * p - 2 := by omega
          rw [h_eq_sub2] at hq_dvd_Y1
          have h_eq_sub : 2 * p - 2 = 2 * (p - 1) := by omega
          rw [h_eq_sub] at hq_dvd_Y1
          exact h_gcd.dvd_of_dvd_mul_left hq_dvd_Y1
        have hp1 : p - 1 > 0 := by omega
        have hq_le : q ≤ p - 1 := Nat.le_of_dvd hp1 h_div
        omega
    · let r := k.minFac
      have hr : r.Prime := Nat.minFac_prime (by omega)
      have hr_dvd_k : r ∣ k := k.minFac_dvd
      have hr_dvd_m : r ∣ m := by
        rw [h_eq_m]
        exact dvd_mul_of_dvd_right hr_dvd_k q
      have h_r_ne_q : r ≠ q := by
        intro hc
        rw [hc] at hr_dvd_k
        exact h_not_dvd_k hr_dvd_k
      have hq_le_r : q ≤ r := Nat.minFac_le_of_dvd hr.two_le hr_dvd_m
      have hq_lt_r : q < r := by omega

      have hp_ge_2 : p ≥ 2 := hp.two_le
      have h_succ : succ (2 * p - 1) = 2 * p := by omega
      have h_Y_add : Y + A018804 k = p * (2 * A018804 k) := by
        dsimp [Y]
        rw [← Nat.succ_mul]
        rw [h_succ]
        ring

      have h_alg_p : (2 * q - 1) * Y + 1 + A018804 m = p * ((2 * q - 1) * (2 * A018804 k)) + 1 := by
        have h_add_comm : (2 * q - 1) * Y + 1 + A018804 m = (2 * q - 1) * Y + A018804 m + 1 := by omega
        rw [h_add_comm, h_Am_eq, ← mul_add, h_Y_add]
        ring

      have h_alg_p2 : q * c' + A018804 m = p * ((2 * q - 1) * (2 * A018804 k)) + 1 := by
        rwa [hc'] at h_alg_p

      have h_m_eq : A018804 m = p * (A018804 m / p) + 1 := by
        have := Nat.div_add_mod (A018804 m) p
        rw [h_mod_m] at this
        exact this.symm

      have h_alg_p3 : q * c' + (p * (A018804 m / p) + 1) = p * ((2 * q - 1) * (2 * A018804 k)) + 1 := by
        rwa [h_m_eq] at h_alg_p2

      have h_alg_p4 : q * c' + p * (A018804 m / p) = p * ((2 * q - 1) * (2 * A018804 k)) := by
        have h_add : q * c' + (p * (A018804 m / p) + 1) = q * c' + p * (A018804 m / p) + 1 := by omega
        rw [h_add] at h_alg_p3
        omega

      have hp_dvd_qc' : p ∣ q * c' := by
        have h_dvd : p ∣ (q * c' + p * (A018804 m / p)) := by
          rw [h_alg_p4]
          exact dvd_mul_right p _
        have h_dvd_p : p ∣ p * (A018804 m / p) := dvd_mul_right p _
        exact (Nat.dvd_add_iff_left h_dvd_p).mpr h_dvd

      have h_not_p_dvd_q : ¬ p ∣ q := by
        intro hd
        rcases hq.eq_one_or_self_of_dvd p hd with hp1 | hpq
        · have : p ≥ 2 := hp.two_le
          omega
        · omega
      have h_cop_pq : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr h_not_p_dvd_q
      have hp_dvd_c' : p ∣ c' := h_cop_pq.dvd_of_dvd_mul_left hp_dvd_qc'

      have hr_dvd_n : r ∣ n := by
        rw [h_eq, h_eq_m]
        exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hr_dvd_k q) p

      have hr_dvd_An1 : r ∣ 1 + A018804 n := dvd_trans hr_dvd_n h_n_dvd

      have h_An1_eq : 1 + A018804 n = q * c' := by
        rw [h_An_eq2]
        have h_Y_eq : (2 * p - 1) * (2 * q - 1) * A018804 k = (2 * q - 1) * Y := by
          dsimp [Y]
          ring
        rw [h_Y_eq]
        have : 1 + (2 * q - 1) * Y = (2 * q - 1) * Y + 1 := by omega
        rw [this, hc']

      have hr_dvd_qc' : r ∣ q * c' := by
        rw [← h_An1_eq]
        exact hr_dvd_An1

      have h_not_q_dvd_r : ¬ q ∣ r := by
        intro hd
        rcases hr.eq_one_or_self_of_dvd q hd with hq1 | hqr
        · have : q ≥ 2 := hq.two_le
          omega
        · omega
      have h_cop_qr : Nat.Coprime q r := hq.coprime_iff_not_dvd.mpr h_not_q_dvd_r
      have hr_dvd_c' : r ∣ c' := h_cop_qr.symm.dvd_of_dvd_mul_left hr_dvd_qc'

      have h_not_p_dvd_r : ¬ p ∣ r := by
        intro hd
        rcases hr.eq_one_or_self_of_dvd p hd with hp1 | hpr
        · have : p ≥ 2 := hp.two_le
          omega
        · omega
      have h_cop_pr : Nat.Coprime p r := hp.coprime_iff_not_dvd.mpr h_not_p_dvd_r

      have hpr_dvd_c' : p * r ∣ c' := h_cop_pr.mul_dvd_of_dvd_of_dvd hp_dvd_c' hr_dvd_c'
      rcases hpr_dvd_c' with ⟨d, hd⟩

      have hd_eq : q * (p * r * d) = q * p * r * d := by ring
      rw [hd] at hc'
      have h_alg_eq4 : q * p * r * d = (2 * q - 1) * Y + 1 := by
        rw [← hd_eq, hc']

      let k' := k / r
      have h_eq_k : k = r * k' := by
        rw [Nat.mul_comm]
        exact (Nat.div_mul_cancel hr_dvd_k).symm

      have hk_sq : Squarefree k := by
        have h_m_eq_qk : m = q * k := h_eq_m
        rw [h_m_eq_qk] at hm_sq
        exact Squarefree.of_mul_right hm_sq

      have h_not_dvd_k' : ¬ r ∣ k' := by
        intro hr_dvd_k'
        have hr_sq_dvd : r^2 ∣ k := by
          rw [sq, h_eq_k]
          exact mul_dvd_mul_left r hr_dvd_k'
        have hr_not : ¬ r^2 ∣ k := by
          have h_pf : ¬ r * r ∣ k := squarefree_iff_prime_squarefree.mp hk_sq r hr
          rwa [sq]
        exact hr_not hr_sq_dvd

      have hk'_ne_zero : k' ≠ 0 := by
        intro hc
        rw [hc] at h_eq_k
        rw [mul_zero] at h_eq_k
        omega
      have hk'_pos : k' > 0 := Nat.pos_of_ne_zero hk'_ne_zero

      have h_Ak_eq : A018804 k = (2 * r - 1) * A018804 k' := by
        rw [h_eq_k]
        exact A018804_mul_of_prime_of_not_dvd hr h_not_dvd_k' hk'_pos

      have h_Y_eq_Ak' : Y = (2 * p - 1) * (2 * r - 1) * A018804 k' := by
        dsimp [Y]
        rw [h_Ak_eq, mul_assoc]

      have h_alg_eq5 : q * p * r * d = (2 * q - 1) * ((2 * p - 1) * (2 * r - 1) * A018804 k') + 1 := by
        rw [h_Y_eq_Ak'] at h_alg_eq4
        exact h_alg_eq4

      have hr_dvd_term : r ∣ q * p * r * d := by
        use q * p * d
        ring
      rw [h_alg_eq5] at hr_dvd_term

      have hk'_ge : A018804 k' ≥ 1 := by
        rw [A018804_eq_sum_divisors k' hk'_pos]
        have h1 : 1 ∈ k'.divisors := by
          rw [mem_divisors]
          exact ⟨one_dvd k', hk'_pos.ne'⟩
        have h_sum_le : 1 * (k' / 1).totient ≤ ∑ d ∈ k'.divisors, d * (k' / d).totient := by
          apply single_le_sum (f := fun d => d * (k' / d).totient) (a := 1)
          · intro d _
            positivity
          · exact h1
        have h_k1 : k' / 1 = k' := Nat.div_one k'
        have : (k' / 1).totient > 0 := by
          rw [h_k1]
          exact Nat.totient_pos.mpr hk'_pos
        omega

      have h_Ak'_ge_k' : A018804 k' ≥ k' := by
        rw [A018804_eq_sum_divisors k' hk'_pos]
        have hk' : k' ∈ k'.divisors := by
          rw [mem_divisors]
          exact ⟨dvd_rfl, hk'_pos.ne'⟩
        have h_sum_le : k' * (k' / k').totient ≤ ∑ d ∈ k'.divisors, d * (k' / d).totient := by
          apply single_le_sum (f := fun d => d * (k' / d).totient) (a := k')
          · intro d _
            positivity
          · exact hk'
        have h_self : k' / k' = 1 := Nat.div_self hk'_pos
        rw [h_self] at h_sum_le
        have h_one : (1 : ℕ).totient = 1 := rfl
        rw [h_one] at h_sum_le
        omega

      let B := (2 * q - 1) * (2 * p - 1) * A018804 k'

      have hq_ge : 3 ≤ q := by omega
      have hp_ge : 2 ≤ p := hp.two_le
      have h_fac1 : 5 ≤ 2 * q - 1 := by omega
      have h_fac2 : 3 ≤ 2 * p - 1 := by omega
      have h_prod : 15 ≤ (2 * q - 1) * (2 * p - 1) := Nat.mul_le_mul h_fac1 h_fac2

      have hB_ge : 15 ≤ B := by
        have : 15 * 1 ≤ (2 * q - 1) * (2 * p - 1) * A018804 k' := Nat.mul_le_mul h_prod hk'_ge
        omega

      have h_term_eq : (2 * q - 1) * ((2 * p - 1) * (2 * r - 1) * A018804 k') + 1 = B * (2 * r - 1) + 1 := by
        dsimp [B]
        ring

      rw [h_term_eq] at hr_dvd_term

      have hr_ge_2 : r ≥ 2 := hr.two_le
      have h_add_eq : B * (2 * r - 1) + 1 + B = r * (2 * B) + 1 := by
        have h_mul : B * (2 * r - 1) + B = B * (2 * r) := by
          have h_eq : B * (2 * r - 1) + B = B * (2 * r - 1) + B * 1 := by ring
          rw [h_eq, ← mul_add]
          have : 2 * r - 1 + 1 = 2 * r := by omega
          rw [this]
        have : B * (2 * r - 1) + 1 + B = (B * (2 * r - 1) + B) + 1 := by omega
        rw [this, h_mul]
        ring

      have hB_eq : B = (B - 1) + 1 := by omega
      have h_alg_add : r * (2 * B) = (B * (2 * r - 1) + 1) + (B - 1) := by
        have h_add_eq' : B * (2 * r - 1) + 1 + B = r * (2 * B) + 1 := h_add_eq
        omega

      have hr_dvd_B1 : r ∣ B - 1 := by
        have h_dvd_sum : r ∣ (B * (2 * r - 1) + 1) + (B - 1) := by
          rw [← h_alg_add]
          exact dvd_mul_right r (2 * B)
        exact (Nat.dvd_add_iff_right hr_dvd_term).mpr h_dvd_sum

      have hB1_pos : B - 1 > 0 := by omega
      have hr_le_B1 : r ≤ B - 1 := Nat.le_of_dvd hB1_pos hr_dvd_B1
      have hn_eq_all : n = q * p * r * k' := by
        calc
          n = p * m := h_eq
          _ = p * (q * k) := by rw [h_eq_m]
          _ = p * (q * (r * k')) := by rw [h_eq_k]
          _ = q * p * r * k' := by ring

      have h_div_n_c' : q * p * r * k' ∣ q * c' := by
        have h_temp : n ∣ q * c' := by
          rw [← h_An1_eq]
          exact h_n_dvd
        rwa [hn_eq_all] at h_temp

      have hq_pos : q > 0 := hq.pos
      have h_div_prk' : p * r * k' ∣ c' := by
        have h_temp2 : q * (p * r * k') ∣ q * c' := by
          have : q * (p * r * k') = q * p * r * k' := by ring
          rwa [this]
        rwa [Nat.mul_dvd_mul_iff_left hq_pos] at h_temp2

      have h_div_k'_d : k' ∣ d := by
        have h_temp3 : p * r * k' ∣ p * r * d := by
          rwa [← hd]
        have hpr_pos : p * r > 0 := by positivity
        rwa [Nat.mul_dvd_mul_iff_left hpr_pos] at h_temp3

      by_cases hp2 : p = 2
      · have hq3 : q ≠ 3 := by
          intro hq3_eq
          rw [hq3_eq] at h_mod_Y
          have hp2' : p = 2 := hp2
          have h_Y_div : Y = 3 * A018804 k := by
            dsimp [Y]
            rw [hp2']
          have h_mod0 : Y % 3 = 0 := by
            rw [h_Y_div]
            exact Nat.mul_mod_right 3 _
          omega
        have hq_ge5 : 5 ≤ q := by
          rcases eq_or_lt_of_le (by omega : 4 ≤ q) with h4 | h4_lt
          · rw [← h4] at hq
            have : ¬ Nat.Prime 4 := by decide
            exact False.elim (this hq)
          · omega
        have hr_ge7 : 7 ≤ r := by
          rcases eq_or_lt_of_le (by omega : 6 ≤ r) with h6 | h6_lt
          · rw [← h6] at hr
            have : ¬ Nat.Prime 6 := by decide
            exact False.elim (this hr)
          · omega

        let j := (B - 1) / r
        have h_B1_eq_rj : B - 1 = r * j := by
          rw [Nat.mul_comm]
          exact (Nat.div_mul_cancel hr_dvd_B1).symm

        have h_eq' : q * p * d + j = r * (2 * j) + 2 := by
          have h_r_mul : r * (2 * B) = r * (q * p * d + j) := by
            calc
              r * (2 * B) = (B * (2 * r - 1) + 1) + (B - 1) := h_alg_add
              _ = (q * p * r * d) + (B - 1) := by rw [← h_term_eq, ← h_alg_eq5]
              _ = q * p * r * d + r * j := by rw [h_B1_eq_rj]
              _ = r * (q * p * d + j) := by ring

          have h_cancel : 2 * B = q * p * d + j := by
            have hr_pos : r > 0 := by omega
            exact Nat.eq_of_mul_eq_mul_left hr_pos h_r_mul

          have h_2B_eq : 2 * B = r * (2 * j) + 2 := by
            calc
              2 * B = 2 * (B - 1 + 1) := by omega
              _ = 2 * (r * j + 1) := by rw [← h_B1_eq_rj]
              _ = r * (2 * j) + 2 := by ring

          omega

        have hj_even : j % 2 = 0 := by
          have h_eq_even : 2 * q * d + j = r * (2 * j) + 2 := by
            calc
              2 * q * d + j = q * p * d + j := by rw [hp2]; ring
              _ = r * (2 * j) + 2 := h_eq'
          have h_rw : r * (2 * j) = 2 * (r * j) := by ring
          have h_rw_qd : 2 * q * d = 2 * (q * d) := by ring
          rw [h_rw, h_rw_qd] at h_eq_even
          omega

        let h := j / 2
        have h_eq_2h : j = 2 * h := by
          rw [Nat.mul_comm]
          exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hj_even)).symm

        have h_qd_add_h : q * d + h = 2 * r * h + 1 := by
          have h_eq_p2 : q * 2 * d + 2 * h = r * (2 * (2 * h)) + 2 := by
            calc
              q * 2 * d + 2 * h = q * p * d + j := by rw [hp2, h_eq_2h]
              _ = r * (2 * j) + 2 := h_eq'
              _ = r * (2 * (2 * h)) + 2 := by rw [h_eq_2h]
          have h_rw2 : r * (2 * (2 * h)) = 4 * (r * h) := by ring
          have h_rw3 : q * 2 * d = 2 * (q * d) := by ring
          rw [h_rw2, h_rw3] at h_eq_p2
          have h_goal_rw : 2 * r * h = 2 * (r * h) := by ring
          rw [h_goal_rw]
          omega

        have h_sub_id : (2 * r - 1) * h + h = 2 * r * h := by
          have h_eq_add : (2 * r - 1) * h + h = ((2 * r - 1) + 1) * h := by ring
          rw [h_eq_add]
          have h_r_ge : 2 * r ≥ 1 := by omega
          have h_sub_one : 2 * r - 1 + 1 = 2 * r := by omega
          rw [h_sub_one]

        have h_qd_eq : q * d = (2 * r - 1) * h + 1 := by
          omega
        have h_B_p2 : B = 3 * (2 * q - 1) * A018804 k' := by
          dsimp [B]
          rw [hp2]
          ring
        have h_B_eq : 3 * (2 * q - 1) * A018804 k' = 2 * r * h + 1 := by
          have h1 : B - 1 = 2 * r * h := by
            calc
              B - 1 = r * j := h_B1_eq_rj
              _ = r * (2 * h) := by rw [h_eq_2h]
              _ = 2 * r * h := by ring
          have h2 : B = 2 * r * h + 1 := by omega
          exact h_B_p2.symm.trans h2

        by_cases hk'1 : k' = 1
        · have h_A1 : A018804 k' = 1 := by
            rw [hk'1]
            dsimp [A018804]
            have : Finset.Ico 1 2 = {1} := rfl
            rw [this]; simp
          rw [h_A1, mul_one] at h_B_eq
          have h_eq_all : r * h + 2 = 3 * q := by
            have h_double : 2 * (r * h + 2) = 2 * (3 * q) := by
              calc
                2 * (r * h + 2) = 2 * r * h + 4 := by ring
                _ = (2 * r * h + 1) + 3 := by omega
                _ = 3 * (2 * q - 1) + 3 := by rw [← h_B_eq]
                _ = 2 * (3 * q) := by omega
            omega

          have h_eq_all2 : q * d + h + 3 = 6 * q := by
            calc
              q * d + h + 3 = (2 * r - 1) * h + 1 + h + 3 := by rw [h_qd_eq]
              _ = (2 * r - 1) * h + h + 4 := by omega
              _ = 2 * r * h + 4 := by rw [h_sub_id]
              _ = (2 * r * h + 1) + 3 := by omega
              _ = 3 * (2 * q - 1) + 3 := by rw [← h_B_eq]
              _ = 6 * q := by omega

          have hd_lt_6 : d < 6 := by
            by_contra h_ge
            have h_le : q * 6 ≤ q * d := Nat.mul_le_mul_left q (by omega)
            have h_ring : 6 * q = q * 6 := by ring
            omega

          have hd_ge_1 : d ≥ 1 := by
            by_contra h_zero
            have : d = 0 := by omega
            subst this
            have h_zero' : q * 0 = 0 := by ring
            omega

          have h_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
          rcases h_cases with rfl | rfl | rfl | rfl | rfl
          · generalize h_rh : r * h = rh
            have h_rh_ge : rh ≥ 7 * h := by
              rw [← h_rh]
              exact Nat.mul_le_mul_right h hr_ge7
            omega
          · generalize h_rh : r * h = rh
            have h_rh_ge : rh ≥ 7 * h := by
              rw [← h_rh]
              exact Nat.mul_le_mul_right h hr_ge7
            omega
          · generalize h_rh : r * h = rh
            have h_rh_ge : rh ≥ 7 * h := by
              rw [← h_rh]
              exact Nat.mul_le_mul_right h hr_ge7
            omega
          · generalize h_rh : r * h = rh
            have h_rh_ge : rh ≥ 7 * h := by
              rw [← h_rh]
              exact Nat.mul_le_mul_right h hr_ge7
            omega
          · generalize h_rh : r * h = rh
            have h_rh_ge : rh ≥ 7 * h := by
              rw [← h_rh]
              exact Nat.mul_le_mul_right h hr_ge7
            omega
        · have h_alg_sum2 : 2 * q * r * d + (6 * q + 6 * r - 3) * A018804 k' = 12 * q * r * A018804 k' + 1 := by
            have h_step1 : 2 * q * r * d + (6 * q + 6 * r - 3) * A018804 k' = q * p * r * d + (6 * q + 6 * r - 3) * A018804 k' := by
              rw [hp2]
              ring
            have hp_eval : 2 * p - 1 = 3 := by rw [hp2]
            have h_step2 : q * p * r * d + (6 * q + 6 * r - 3) * A018804 k' = ((2 * q - 1) * (3 * (2 * r - 1) * A018804 k') + 1) + (6 * q + 6 * r - 3) * A018804 k' := by
              rw [h_alg_eq5, hp_eval]
            have hq_21 : 1 ≤ 2 * q := by omega
            have hr_21 : 1 ≤ 2 * r := by omega
            have hqr_63 : 3 ≤ 6 * q + 6 * r := by omega
            rw [h_step1, h_step2]
            apply (Nat.cast_inj (R := ℤ)).mp
            push_cast
            rw [Nat.cast_sub hq_21, Nat.cast_sub hr_21, Nat.cast_sub hqr_63]
            push_cast
            ring
          have h_lt_6A : d < 6 * A018804 k' := by
            by_contra hg
            push_neg at hg
            have h_mul : 2 * q * r * d ≥ 12 * q * r * A018804 k' := by
              calc
                2 * q * r * d = (2 * q * r) * d := by ring
                _ ≥ (2 * q * r) * (6 * A018804 k') := Nat.mul_le_mul_left (2 * q * r) hg
                _ = 12 * q * r * A018804 k' := by ring
            have h_coef_ge : 6 * q + 6 * r - 3 > 1 := by omega
            have h_coef_term : (6 * q + 6 * r - 3) * A018804 k' > 1 := by
              calc
                (6 * q + 6 * r - 3) * A018804 k' ≥ (6 * q + 6 * r - 3) * 1 := Nat.mul_le_mul_left (6 * q + 6 * r - 3) hk'_ge
                _ > 1 := by omega
            omega
          let Y_pos := 6 * A018804 k' - d
          have h_Y_pos_gt : Y_pos > 0 := by omega
          have h_Y_alg : 2 * q * r * Y_pos + 1 = (6 * q + 6 * r - 3) * A018804 k' := by
            apply (Nat.cast_inj (R := ℤ)).mp
            have hd_le : d ≤ 6 * A018804 k' := by omega
            have hqr_63 : 3 ≤ 6 * q + 6 * r := by omega
            have h_Y_pos_cast : (Y_pos : ℤ) = 6 * (A018804 k' : ℤ) - (d : ℤ) := by
              rw [Nat.cast_sub hd_le]
              push_cast
              rfl
            have h_alg_sum2_cast : 2 * (q : ℤ) * (r : ℤ) * (d : ℤ) + (6 * (q : ℤ) + 6 * (r : ℤ) - 3) * (A018804 k' : ℤ) = 12 * (q : ℤ) * (r : ℤ) * (A018804 k' : ℤ) + 1 := by
              have h_init : ((2 * q * r * d + (6 * q + 6 * r - 3) * A018804 k' : ℕ) : ℤ) = ((12 * q * r * A018804 k' + 1 : ℕ) : ℤ) := by
                congr 1
              simp only [Nat.cast_add, Nat.cast_mul] at h_init
              rw [Nat.cast_sub hqr_63] at h_init
              push_cast at h_init
              exact h_init
            have h_goal_rhs : (((6 * q + 6 * r - 3) * A018804 k' : ℕ) : ℤ) = (6 * (q : ℤ) + 6 * (r : ℤ) - 3) * (A018804 k' : ℤ) := by
              simp only [Nat.cast_mul]
              rw [Nat.cast_sub hqr_63]
              push_cast
              rfl
            rw [h_goal_rhs]
            calc
              (2 * q * r * Y_pos + 1 : ℤ) = 2 * q * r * (6 * A018804 k' - d) + 1 := by rw [h_Y_pos_cast]
              _ = 12 * q * r * A018804 k' + 1 - 2 * q * r * d := by ring
              _ = 2 * q * r * d + (6 * q + 6 * r - 3) * A018804 k' - 2 * q * r * d := by rw [h_alg_sum2_cast]
              _ = (6 * q + 6 * r - 3) * A018804 k' := by ring
          have h_qr_ineq : 6 * q + 6 * r - 3 < 2 * q * r := by
            have h_rw : q * (2 * r - 6) = 2 * q * r - 6 * q := by
              rw [Nat.mul_sub_left_distrib]
              have h_mul1 : q * (2 * r) = 2 * q * r := by ring
              have h_mul2 : q * 6 = 6 * q := by ring
              rw [h_mul1, h_mul2]
            have h_nonlin : q * (2 * r - 6) ≥ 5 * (2 * r - 6) := Nat.mul_le_mul_right (2 * r - 6) hq_ge5
            omega
          have h_Y_pos_lt : Y_pos < A018804 k' := by
            by_contra h_ge
            push_neg at h_ge
            have h_mul_lt : (6 * q + 6 * r - 3) * A018804 k' < 2 * q * r * Y_pos + 1 := by
              calc
                (6 * q + 6 * r - 3) * A018804 k' < 2 * q * r * A018804 k' := Nat.mul_lt_mul_of_pos_right h_qr_ineq hk'_ge
                _ ≤ 2 * q * r * Y_pos := Nat.mul_le_mul_left (2 * q * r) h_ge
                _ < 2 * q * r * Y_pos + 1 := by omega
            have h_eq : 2 * q * r * Y_pos + 1 = (6 * q + 6 * r - 3) * A018804 k' := h_Y_alg
            omega
          exfalso
          have h_Ak'_odd : A018804 k' % 2 = 1 := by
            have h_eq : 6 * q * A018804 k' = 2 * r * h + 1 + 3 * A018804 k' := by
              have h_rew : 3 * (2 * q - 1) = 6 * q - 3 := by omega
              have h_eq2 : (6 * q - 3) * A018804 k' = 2 * r * h + 1 := by
                calc
                  (6 * q - 3) * A018804 k' = 3 * (2 * q - 1) * A018804 k' := by rw [h_rew]
                  _ = 2 * r * h + 1 := h_B_eq
              have h_expand : (6 * q - 3) * A018804 k' = 6 * q * A018804 k' - 3 * A018804 k' := by
                rw [Nat.sub_mul]
              omega
            have h_even1 : (6 * q * A018804 k') % 2 = 0 := by
              have : 6 * q * A018804 k' = 2 * (3 * q * A018804 k') := by ring
              rw [this]
              exact Nat.mul_mod_right 2 _
            have h_even2 : (2 * r * h) % 2 = 0 := by
              have : 2 * r * h = 2 * (r * h) := by ring
              rw [this]
              exact Nat.mul_mod_right 2 _
            omega
          have hk'_odd : k' % 2 = 1 := by
            by_contra h_even
            have h_even' : k' % 2 = 0 := by omega
            have hk'_dvd : 2 ∣ k' := Nat.dvd_of_mod_eq_zero h_even'
            have h_4_dvd : 4 ∣ n := by
              rw [hn_eq_all, hp2]
              rcases hk'_dvd with ⟨k'', hk'_eq⟩
              rw [hk'_eq]
              use q * r * k''
              ring
            have h_sq_dvd : 2^2 ∣ n := by
              have : (2^2 : ℕ) = 4 := rfl
              rwa [this]
            have h_pf : ¬ 2 * 2 ∣ n := squarefree_iff_prime_squarefree.mp h_sq 2 (by decide)
            have h_sq_not : ¬ 2^2 ∣ n := by
              have : (2^2 : ℕ) = 2 * 2 := rfl
              rwa [this]
            exact h_sq_not h_sq_dvd
          have h_Ak'_ge_2 : A018804 k' ≥ 2 := by omega
          have h_Ak'_ne_2 : A018804 k' ≠ 2 := by
            intro h_eq
            have h_odd : (2 * q * r * Y_pos + 1) % 2 = 1 := by
              have : 2 * q * r * Y_pos + 1 = 1 + 2 * (q * r * Y_pos) := by ring
              rw [this, Nat.add_mul_mod_self_left]
            have h_even : ((6 * q + 6 * r - 3) * A018804 k') % 2 = 0 := by
              have : (6 * q + 6 * r - 3) * A018804 k' = 2 * (6 * q + 6 * r - 3) := by
                rw [h_eq]
                ring
              rw [this]
              exact Nat.mul_mod_right 2 _
            have h_alg : 2 * q * r * Y_pos + 1 = (6 * q + 6 * r - 3) * A018804 k' := h_Y_alg
            omega
          have h_Ak'_ge_3 : A018804 k' ≥ 3 := by omega
          have h_exact : 2 * r * q * d = 3 * (2 * q - 1) * (2 * r - 1) * A018804 k' + 1 := by
            apply (Nat.cast_inj (R := ℤ)).mp
            have h_q_ge : 1 ≤ 2 * q := by omega
            have h_r_ge : 1 ≤ 2 * r := by omega
            push_cast
            rw [Nat.cast_sub h_q_ge, Nat.cast_sub h_r_ge]
            simp only [Nat.cast_mul, Nat.cast_ofNat]
            have h_qd_cast : (q : ℤ) * d = (2 * r - 1) * h + 1 := by exact_mod_cast h_qd_eq
            have h_B_cast : 3 * (2 * q - 1) * (A018804 k' : ℤ) = 2 * r * h + 1 := by exact_mod_cast h_B_eq
            linear_combination (2 * r : ℤ) * h_qd_cast - (2 * r - 1 : ℤ) * h_B_cast
          have h_k'_dvd_exact : k' ∣ 3 * (2 * q - 1) * (2 * r - 1) * A018804 k' + 1 := by
            rw [← h_exact]
            have : 2 * r * q * d = d * (2 * r * q) := by ring
            rw [this]
            exact dvd_mul_of_dvd_left h_div_k'_d _
          have hk'_gt1 : k' > 1 := by omega
          let g := k'.minFac
          have hg : g.Prime := Nat.minFac_prime hk'_gt1.ne'
          have h_g_dvd : g ∣ k' := k'.minFac_dvd
          have h_g_dvd_exact : g ∣ 3 * (2 * q - 1) * (2 * r - 1) * A018804 k' + 1 := dvd_trans h_g_dvd h_k'_dvd_exact
          let k'' := k' / g
          have hk'_eq : k' = g * k'' := by
            have : k' = k' / g * g := (Nat.div_mul_cancel h_g_dvd).symm
            rw [this]
            ring
          have hk''_pos : k'' > 0 := by
            by_cases hk''0 : k'' = 0
            · rw [hk''0] at hk'_eq
              rw [mul_zero] at hk'_eq
              omega
            · exact Nat.pos_of_ne_zero hk''0
          have h_sq_k' : Squarefree k' := by
            have h_eq_tmp : n = (q * p * r) * k' := by
              calc
                n = q * p * r * k' := hn_eq_all
                _ = (q * p * r) * k' := by ring
            rw [h_eq_tmp] at h_sq
            exact Squarefree.of_mul_right h_sq
          have hg_not_dvd_k'' : ¬ g ∣ k'' := by
            intro h_dvd
            have h_g2_dvd : g^2 ∣ k' := by
              rw [sq, hk'_eq]
              exact mul_dvd_mul_left g h_dvd
            have h_g2_not_dvd : ¬ g^2 ∣ k' := by
              have h_pf : ¬ g * g ∣ k' := squarefree_iff_prime_squarefree.mp h_sq_k' g hg
              rwa [sq]
            exact h_g2_not_dvd h_g2_dvd
          have h_Ak''_ge_k'' : A018804 k'' ≥ k'' := by
            rw [A018804_eq_sum_divisors k'' hk''_pos]
            have hk'' : k'' ∈ k''.divisors := by
              rw [mem_divisors]
              exact ⟨dvd_rfl, hk''_pos.ne'⟩
            have h_sum_le : k'' * (k'' / k'').totient ≤ ∑ d ∈ k''.divisors, d * (k'' / d).totient := by
              apply single_le_sum (f := fun d => d * (k'' / d).totient) (a := k'')
              · intro d _
                positivity
              · exact hk''
            have h_self : k'' / k'' = 1 := Nat.div_self hk''_pos
            rw [h_self] at h_sum_le
            have h_one : (1 : ℕ).totient = 1 := rfl
            rw [h_one] at h_sum_le
            omega
          have h_Agk'' : A018804 k' = (2 * g - 1) * A018804 k'' := by
            rw [hk'_eq]
            exact A018804_mul_of_prime_of_not_dvd hg hg_not_dvd_k'' hk''_pos
          rcases h_div_k'_d with ⟨c, hc⟩
          have h_A_pos : A018804 k'' > 0 := Nat.lt_of_lt_of_le hk''_pos h_Ak''_ge_k''
          generalize h_A : A018804 k'' = A_val
          rw [h_A] at h_A_pos
          have h_Agk''_val : A018804 k' = (2 * g - 1) * A_val := by
            rw [h_A] at h_Agk''
            exact h_Agk''
          have h_g_k''_c : d = g * k'' * c := by
            calc
              d = k' * c := hc
              _ = (g * k'') * c := by rw [hk'_eq]
              _ = g * k'' * c := by ring
          have h_k''c_lt : k'' * c < 12 * A_val := by
            have h_d_lt : d < 6 * A018804 k' := h_lt_6A
            rw [h_g_k''_c, h_Agk''_val] at h_d_lt
            have h_g2_lt : (2 * g - 1) * A_val < 2 * g * A_val := by
              have h_g_pos : g > 0 := hg.pos
              have : 2 * g - 1 < 2 * g := by omega
              exact Nat.mul_lt_mul_of_pos_right this h_A_pos
            have h_mul_lt : g * (k'' * c) < g * (12 * A_val) := by
              calc
                g * (k'' * c) = g * k'' * c := by ring
                _ < 6 * ((2 * g - 1) * A_val) := h_d_lt
                _ < 6 * (2 * g * A_val) := Nat.mul_lt_mul_of_pos_left h_g2_lt (by decide)
                _ = g * (12 * A_val) := by ring
            exact Nat.lt_of_mul_lt_mul_left h_mul_lt
          have h_c_ge6 : c ≥ 6 := by
            have h_d_gt : d > 5 * A018804 k' := by
              have : Y_pos = 6 * A018804 k' - d := rfl
              omega
            have h_k'5_lt : k' * 5 < k' * c := by
              calc
                k' * 5 = 5 * k' := by ring
                _ < d := by omega
                _ = k' * c := hc
            have : 5 < c := Nat.lt_of_mul_lt_mul_left h_k'5_lt
            omega
          let M := 3 * (2 * q - 1) * (2 * r - 1) * A_val
          have h_g_dvd_M : g ∣ (2 * g - 1) * M + 1 := by
            have h_eq_term : 3 * (2 * q - 1) * (2 * r - 1) * A018804 k' + 1 = (2 * g - 1) * M + 1 := by
              rw [h_Agk''_val]
              dsimp [M]
              ring
            rwa [← h_eq_term]
          have h_M_pos : M > 0 := by
            have h1 : 3 > 0 := by decide
            have h2 : 2 * q - 1 > 0 := by omega
            have h3 : 2 * r - 1 > 0 := by omega
            have h5 : 3 * (2 * q - 1) > 0 := Nat.mul_pos h1 h2
            have h6 : 3 * (2 * q - 1) * (2 * r - 1) > 0 := Nat.mul_pos h5 h3
            exact Nat.mul_pos h6 h_A_pos
          have h_M_ge1 : M ≥ 1 := by omega
          have h_sub_mul_eq : (2 * g - 1) * M = 2 * g * M - M := by
            have : (2 * g - 1) * M = 2 * g * M - 1 * M := by
              rw [Nat.sub_mul]
            rwa [one_mul] at this
          have h_eq_omega : ((2 * g - 1) * M + 1) + (M - 1) = 2 * g * M := by
            have h1 : ((2 * g - 1) * M + 1) + (M - 1) = (2 * g - 1) * M + M := by omega
            have h2 : (2 * g - 1) * M + M = 2 * g * M := by
              rw [← Nat.succ_mul]
              have h_g_ge2 : g ≥ 2 := hg.two_le
              have : (2 * g - 1).succ = 2 * g := by omega
              rw [this]
            rw [h1, h2]
          have h_g_dvd_sum : g ∣ ((2 * g - 1) * M + 1) + (M - 1) := by
            rw [h_eq_omega]
            use 2 * M
            ring
          have h_g_dvd_M1 : g ∣ M - 1 := (Nat.dvd_add_iff_right h_g_dvd_M).mpr h_g_dvd_sum
          have h2 : 2 * r * q * g * k'' * c = (2 * g - 1) * M + 1 := by
            calc
              2 * r * q * g * k'' * c = 2 * r * q * d := by
                rw [h_g_k''_c]
                ring
              _ = 3 * (2 * q - 1) * (2 * r - 1) * A018804 k' + 1 := h_exact
              _ = (2 * g - 1) * M + 1 := by
                rw [h_Agk'']
                dsimp [M]
                ring
          have h_exact_g : (M - 1) + 2 * r * q * g * k'' * c = 2 * g * M := by
            rw [h2, h_sub_mul_eq]
            omega
          have h_g_H_eq : g * (2 * M - 2 * r * q * k'' * c) = M - 1 := by
            have : g * (2 * M - 2 * r * q * k'' * c) = 2 * g * M - 2 * r * q * g * k'' * c := by
              rw [Nat.mul_sub_left_distrib]
              ring
            rw [this]
            omega
          let Y := 2 * M - 2 * r * q * k'' * c
          have h_gY : g * Y = M - 1 := h_g_H_eq
          have h_Y_pos : Y > 0 := by
            by_contra hc
            have hY0 : Y = 0 := by omega
            have h_g0 : g * 0 = M - 1 := by rw [← hY0, h_gY]
            rw [mul_zero] at h_g0
            have h_M1 : M = 1 := by omega
            have h_X : M = 3 * ((2 * q - 1) * (2 * r - 1) * A018804 k'') := by ring
            have h_div3 : 3 ∣ M := ⟨(2 * q - 1) * (2 * r - 1) * A018804 k'', h_X⟩
            have h_div3_1 : 3 ∣ 1 := by rwa [h_M1] at h_div3
            have h_contr : ¬ 3 ∣ 1 := by decide
            exact h_contr h_div3_1
          have h_Y_even : Y % 2 = 0 := by
            dsimp [Y]
            omega
          let Y' := Y / 2
          have h_Y_eq : Y = 2 * Y' := by
            rw [Nat.mul_comm]
            exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_Y_even)).symm
          have h_Y'_pos : Y' > 0 := by omega
          have h_M_eq_Y' : M = 2 * g * Y' + 1 := by
            calc
              M = (M - 1) + 1 := by omega
              _ = g * Y + 1 := by rw [h_gY]
              _ = g * (2 * Y') + 1 := by rw [h_Y_eq]
              _ = 2 * g * Y' + 1 := by ring
          have h_rq_eq : r * q * k'' * c = Y' * (2 * g - 1) + 1 := by
            apply Nat.eq_of_mul_eq_mul_left (by decide : 2 > 0)
            have h_alg : 2 * (r * q * k'' * c) = 2 * M - 2 * Y' := by
              omega
            rw [h_alg, h_M_eq_Y']
            have h_rw_sub : Y' * (2 * g - 1) = 2 * g * Y' - Y' := by
              rw [Nat.mul_sub_left_distrib]
              ring
            rw [h_rw_sub]
            generalize g * Y' = gY'
            omega
          have h_k''c_ge6 : k'' * c ≥ 6 := by
            have h1 : 1 * 6 ≤ k'' * c := Nat.mul_le_mul hk''_pos h_c_ge6
            omega
          have h_g_dvd_k : g ∣ k := by
            rw [h_eq_k]
            exact dvd_mul_of_dvd_right h_g_dvd r
          have hr_le_g : r ≤ g := Nat.minFac_le_of_dvd hg.two_le h_g_dvd_k
          have h_g_ne_r : g ≠ r := by
            intro h_eq_gr
            subst h_eq_gr
            have h_g2_dvd : g^2 ∣ n := by
              use q * p * k''
              rw [hn_eq_all, hk'_eq, hp2]
              ring
            have h_g2_not_dvd : ¬ g^2 ∣ n := by
              have h_pf : ¬ g * g ∣ n := squarefree_iff_prime_squarefree.mp h_sq g hg
              rwa [sq]
            exact h_g2_not_dvd h_g2_dvd
          have h_g_gt_r : g > r := by omega
          by_cases h_Y'_case : Y' = 1
          · have h_rq_eq2 : r * q * k'' * c = 2 * g := by
              rw [h_Y'_case] at h_rq_eq
              omega
            have h_r_dvd_2g : r ∣ 2 * g := by
              use q * k'' * c
              rw [h_rq_eq2]
              ring
            have h_r_dvd_g : r ∣ g := by
              have hr_prime : r.Prime := hr
              have hr_not_dvd2 : ¬ r ∣ 2 := by
                intro hd
                have : r ≤ 2 := Nat.le_of_dvd (by decide) hd
                omega
              exact (Nat.Prime.dvd_mul hr_prime).mp h_r_dvd_2g |>.resolve_left hr_not_dvd2
            have h_r_eq_g : r = g := hg.eq_one_or_self_of_dvd r h_r_dvd_g |>.resolve_left (by omega)
            omega
          · have h_Y'_ge2 : Y' ≥ 2 := by omega
            have h_2gY' : 2 * g * Y' = M - 1 := by omega
            have h_rq_add : r * q * k'' * c + Y' = 2 * g * Y' + 1 := by
              calc
                r * q * k'' * c + Y' = (Y' * (2 * g - 1) + 1) + Y' := by rw [h_rq_eq]
                _ = 2 * g * Y' + 1 := by ring
            have h_alg1 : 2 * g * (r * q * k'' * c) = M * (2 * g - 1) + 1 := by
              have h_eq1 : r * q * k'' * c = 2 * g * Y' + 1 - Y' := by omega
              rw [h_eq1]
              have h_expand1 : 2 * g * (2 * g * Y' + 1 - Y') = (2 * g * Y') * (2 * g - 1) + 2 * g := by ring
              rw [h_expand1, h_2gY']
              have h_expand2 : M * (2 * g - 1) + 1 = (M - 1) * (2 * g - 1) + 2 * g := by
                generalize h_tg1 : 2 * g - 1 = tg1
                have : 2 * g = tg1 + 1 := by omega
                omega
              rw [h_expand2]
            have h_M_val : M = (12 * q * r - 6 * q - 6 * r + 3) * A_val := by
              dsimp [M]
              ring
            have h_alg2 : 2 * g * r * q * k'' * c = (12 * q * r - 6 * q - 6 * r + 3) * A_val * (2 * g - 1) + 1 := by
              calc
                2 * g * r * q * k'' * c = 2 * g * (r * q * k'' * c) := by ring
                _ = M * (2 * g - 1) + 1 := h_alg1
                _ = (12 * q * r - 6 * q - 6 * r + 3) * A_val * (2 * g - 1) + 1 := by rw [h_M_val]
            have h_pos : 2 * g * r * q > 0 := by omega
            have h_k_c_bound : 2 * g * r * q * k'' * c < 24 * g * r * q * A_val := by
              have h_mul := Nat.mul_lt_mul_of_pos_left h_k''c_lt h_pos
              calc
                2 * g * r * q * k'' * c = (2 * g * r * q) * (k'' * c) := by ring
                _ < (2 * g * r * q) * (12 * A_val) := h_mul
                _ = 24 * g * r * q * A_val := by ring
            let W := 12 * A_val - k'' * c
            have h_W_val : 12 * A_val = W + k'' * c := by omega
            have h_W_add : 2 * g * q * r * W + 2 * g * r * q * k'' * c = 24 * g * q * r * A_val := by
              calc
                2 * g * q * r * W + 2 * g * r * q * k'' * c = 2 * g * q * r * (W + k'' * c) := by ring
                _ = 2 * g * q * r * (12 * A_val) := by rw [← h_W_val]
                _ = 24 * g * q * r * A_val := by ring
            have h_W_add2 : 2 * g * q * r * W + (12 * q * r - 6 * q - 6 * r + 3) * A_val * (2 * g - 1) + 1 = 24 * g * q * r * A_val := by
              rw [← h_alg2]
              exact h_W_add
            have h_W_alg : 2 * g * q * r * W + (6 * q + 6 * r - 3) * A_val + 1 = 12 * q * r * A_val + 2 * g * (6 * q + 6 * r - 3) * A_val := by
              have h_A_eq : (12 * q * r - 6 * q - 6 * r + 3) * A_val = 12 * q * r * A_val - (6 * q + 6 * r - 3) * A_val := by
                have : 12 * q * r - 6 * q - 6 * r + 3 = 12 * q * r - (6 * q + 6 * r - 3) := by omega
                rw [this, Nat.sub_mul]
              have h_dist : (12 * q * r - 6 * q - 6 * r + 3) * A_val * (2 * g - 1) = 2 * g * ((12 * q * r - 6 * q - 6 * r + 3) * A_val) - (12 * q * r - 6 * q - 6 * r + 3) * A_val := by
                rw [Nat.mul_sub_left_distrib, mul_comm, one_mul]
              have h_sub_le : (6 * q + 6 * r - 3) * A_val ≤ 12 * q * r * A_val := by
                have : 6 * q + 6 * r - 3 ≤ 12 * q * r := by omega
                exact Nat.mul_le_mul_right A_val this
              generalize h_gqrW : 2 * g * q * r * W = gqrW
              generalize h_qrA : 12 * q * r * A_val = qrA
              generalize h_coA : (6 * q + 6 * r - 3) * A_val = coA
              generalize h_gcoA : 2 * g * ((6 * q + 6 * r - 3) * A_val) = gcoA
              generalize h_gqrA : 2 * g * (12 * q * r * A_val) = gqrA
              have h_g_le : gcoA ≤ gqrA := by
                rw [← h_gcoA, ← h_gqrA, ← h_coA, ← h_qrA]
                exact Nat.mul_le_mul_left (2 * g) h_sub_le
              rw [h_dist, h_A_eq] at h_W_add2
              have h_term : (12 * q * r - 6 * q - 6 * r + 3) * A_val = qrA - coA := by
                rw [h_A_eq, ← h_qrA, ← h_coA]
              rw [h_term] at h_W_add2 h_dist
              have h_g_sub : 2 * g * (qrA - coA) = gqrA - gcoA := by
                rw [Nat.mul_sub_left_distrib, ← h_gqrA, ← h_gcoA, ← h_qrA, ← h_coA]
              rw [h_g_sub] at h_W_add2
              omega
            have h_W_gt : q * r * W > (6 * q + 6 * r - 3) * A_val := by
              by_contra hc
              push_neg at hc
              have h_mul_le : 2 * g * q * r * W ≤ 2 * g * ((6 * q + 6 * r - 3) * A_val) := Nat.mul_le_mul_left (2 * g) hc
              have h_co_pos : (6 * q + 6 * r - 3) * A_val > 0 := by omega
              have h_ineq : 12 * q * r * A_val < (6 * q + 6 * r - 3) * A_val + 1 := by omega
              have h_ineq2 : 12 * q * r * A_val ≤ (6 * q + 6 * r - 3) * A_val := by omega
              have h_qr_bound : 12 * q * r > 6 * q + 6 * r - 3 := by
                calc
                  12 * q * r = 6 * q * r + 6 * q * r := by ring
                  _ ≥ 6 * 5 * r + 6 * q * 7 := by
                    have h1 : 6 * q * r ≥ 6 * 5 * r := Nat.mul_le_mul_right (6 * r) hq_ge5
                    have h2 : 6 * q * r ≥ 6 * q * 7 := Nat.mul_le_mul_left (6 * q) hr_ge7
                    omega
                  _ = 30 * r + 42 * q := by ring
                  _ > 6 * q + 6 * r - 3 := by omega
              have h_final_lt : (6 * q + 6 * r - 3) * A_val < 12 * q * r * A_val := Nat.mul_lt_mul_of_pos_right h_qr_bound h_A_pos
              omega
            have h_W_lt : g * q * r * W < (6 * g * q + 6 * g * r - 3 * g + 6 * q * r) * A_val := by
              have h_expand : (6 * g * q + 6 * g * r - 3 * g + 6 * q * r) * A_val = 6 * q * r * A_val + 2 * g * (6 * q + 6 * r - 3) * A_val - g * (6 * q + 6 * r - 3) * A_val := by ring
              have h_div : 2 * (g * q * r * W) < 2 * (6 * q * r * A_val + g * (6 * q + 6 * r - 3) * A_val) := by
                calc
                  2 * (g * q * r * W) = 2 * g * q * r * W := by ring
                  _ < 2 * g * q * r * W + (6 * q + 6 * r - 3) * A_val + 1 := by omega
                  _ = 12 * q * r * A_val + 2 * g * (6 * q + 6 * r - 3) * A_val := h_W_alg
                  _ < 12 * q * r * A_val + 2 * g * (6 * q + 6 * r - 3) * A_val + 12 * q * r * A_val := by omega
                  _ = 2 * (6 * q * r * A_val + g * (6 * q + 6 * r - 3) * A_val) := by ring
              have h_gqrW_lt : g * q * r * W < 6 * q * r * A_val + g * (6 * q + 6 * r - 3) * A_val := Nat.lt_of_mul_lt_mul_left h_div
              rw [h_expand]
              omega
            have h_g_W_gt : g * q * r * W > g * ((6 * q + 6 * r - 3) * A_val) := by
              have h_g_pos : g > 0 := by omega
              exact Nat.mul_lt_mul_of_pos_left h_W_gt h_g_pos
            have h_contr : g * ((6 * q + 6 * r - 3) * A_val) < (6 * g * q + 6 * g * r - 3 * g + 6 * q * r) * A_val := by
              calc
                g * ((6 * q + 6 * r - 3) * A_val) < g * q * r * W := h_g_W_gt
                _ < (6 * g * q + 6 * g * r - 3 * g + 6 * q * r) * A_val := h_W_lt
            have h_contr_expand : g * ((6 * q + 6 * r - 3) * A_val) = (6 * g * q + 6 * g * r - 3 * g) * A_val := by ring
            rw [h_contr_expand] at h_contr
            have h_contr_lt : 6 * g * q + 6 * g * r - 3 * g < 6 * g * q + 6 * g * r - 3 * g + 6 * q * r := by
              have : 6 * g * q + 6 * g * r ≥ 3 * g := by omega
              omega
            have h_contr_mul : (6 * g * q + 6 * g * r - 3 * g) * A_val < (6 * g * q + 6 * g * r - 3 * g + 6 * q * r) * A_val := Nat.mul_lt_mul_of_pos_right h_contr_lt h_A_pos
            omega
      · have hp_ge3 : p ≥ 3 := by
          have : p ≥ 2 := hp.two_le
          omega
        have hq_ge5 : q ≥ 5 := by
          have : q ≥ 2 := hq.two_le
          by_cases hq4 : q = 4
          · rw [hq4] at hq
            have : ¬ Nat.Prime 4 := by decide
            exact False.elim (this hq)
          · omega
        have hr_ge7 : r ≥ 7 := by
          have : r ≥ 2 := hr.two_le
          by_cases hr6 : r = 6
          · rw [hr6] at hr
            have : ¬ Nat.Prime 6 := by decide
            exact False.elim (this hr)
          · omega
        have hpq : p * q ≥ 15 := Nat.mul_le_mul hp_ge3 hq_ge5
        have hpr : p * r ≥ 21 := Nat.mul_le_mul hp_ge3 hr_ge7
        have hqr : q * r ≥ 35 := Nat.mul_le_mul hq_ge5 hr_ge7
        have hpq_q : p * q ≥ 3 * q := Nat.mul_le_mul_right q hp_ge3
        have hpr_r : p * r ≥ 3 * r := Nat.mul_le_mul_right r hp_ge3
        have hqr_p : q * r ≥ 5 * p := by
          have h1 : q * r ≥ 5 * r := Nat.mul_le_mul_right r hq_ge5
          have h2 : r ≥ p := by omega
          have h3 : 5 * r ≥ 5 * p := Nat.mul_le_mul_left 5 h2
          omega
        have h_coef : 4 * (p * q + p * r + q * r) + 1 > 2 * (p + q + r) := by omega
        have h_alg_sum_cast : (q : ℤ) * p * r * d + (4 * (p * q + p * r + q * r) + 1) * A018804 k' = 8 * p * q * r * A018804 k' + 2 * (p + q + r) * A018804 k' + 1 := by
          have h_init : ((q * p * r * d : ℕ) : ℤ) = (((2 * q - 1) * ((2 * p - 1) * (2 * r - 1) * A018804 k') + 1 : ℕ) : ℤ) := by
            rw [h_alg_eq5]
          push_cast at h_init
          have h_p21 : 1 ≤ 2 * p := by omega
          have h_q21 : 1 ≤ 2 * q := by omega
          have h_r21 : 1 ≤ 2 * r := by omega
          rw [Nat.cast_sub h_p21, Nat.cast_sub h_q21, Nat.cast_sub h_r21] at h_init
          push_cast at h_init
          rw [h_init]
          ring

        have h_lt_8A : d < 8 * A018804 k' := by
          by_contra hg
          push_neg at hg
          have h_mul : (q : ℤ) * p * r * d ≥ 8 * q * p * r * A018804 k' := by
            have h_mul_nat : q * p * r * d ≥ 8 * q * p * r * A018804 k' := by
              calc
                q * p * r * d = (q * p * r) * d := by ring
                _ ≥ (q * p * r) * (8 * A018804 k') := Nat.mul_le_mul_left (q * p * r) hg
                _ = 8 * q * p * r * A018804 k' := by ring
            exact_mod_cast h_mul_nat
          have h_coef_strict : 4 * (p * q + p * r + q * r) + 1 ≥ 2 * (p + q + r) + 2 := by omega
          have h_coef_nat : (4 * (p * q + p * r + q * r) + 1) * A018804 k' > 2 * (p + q + r) * A018804 k' + 1 := by
            have h_step2 : (4 * (p * q + p * r + q * r) + 1) * A018804 k' ≥ (2 * (p + q + r) + 2) * A018804 k' := Nat.mul_le_mul_right (A018804 k') h_coef_strict
            have h_step3 : (2 * (p + q + r) + 2) * A018804 k' = 2 * (p + q + r) * A018804 k' + 2 * A018804 k' := by ring
            have : A018804 k' ≥ 1 := hk'_ge
            omega
          have h_coef_cast : ((4 * (p * q + p * r + q * r) + 1) * A018804 k' : ℤ) > 2 * (p + q + r) * A018804 k' + 1 := by
            exact_mod_cast h_coef_nat
          have h_mul_reorder : (8 * (q : ℤ) * p * r * A018804 k') = 8 * p * q * r * A018804 k' := by ring
          have h_mul' : (q : ℤ) * p * r * d ≥ 8 * p * q * r * A018804 k' := by
            calc
              (q : ℤ) * p * r * d ≥ 8 * q * p * r * A018804 k' := h_mul
              _ = 8 * p * q * r * A018804 k' := h_mul_reorder
          have h_add : (q : ℤ) * p * r * d + (4 * (p * q + p * r + q * r) + 1) * A018804 k' > 8 * p * q * r * A018804 k' + 2 * (p + q + r) * A018804 k' + 1 := by omega
          omega
  · rintro (rfl | hp)
    · exact a_one
    · exact a_prime hp
