import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A233549: Number of ways to write $n = p + q$ ($q > 0$) with $p$ prime and $(\phi(p)\phi(q))^4 + 1$ prime,
where $\phi(\cdot)$ is Euler's totient function (A000010).
-/
def a (n : ℕ) : ℕ :=
  Finset.card <| Finset.filter (fun p : ℕ =>
    p.Prime ∧
    let q := n - p
    Nat.Prime ((p.totient * q.totient) ^ 4 + 1)
  ) (Finset.range n)

/--
Conjecture: (i) a(n) > 0 for all n > 2.
Part (i) of the conjecture implies that there are infinitely many primes of the form x^4 + 1.
-/
lemma prime_le_two_mul_sub_one {p : ℕ} (hp : 2 ≤ p) : p ≤ 2 * (p - 1) := by
  omega

lemma n_le_totient_mul_two_pow (n : ℕ) :
    n ≤ n.totient * 2 ^ n.primeFactors.card := by
  have hdvd : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  have h_prod_le : ∏ p ∈ n.primeFactors, p ≤ ∏ p ∈ n.primeFactors, 2 * (p - 1) := by
    apply Finset.prod_le_prod
    · intros p hp
      exact Nat.zero_le _
    · intros p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have h_ge : 2 ≤ p := hp_prime.two_le
      exact prime_le_two_mul_sub_one h_ge
  have h_two_pow : 2 ^ n.primeFactors.card = ∏ p ∈ n.primeFactors, 2 := (Finset.prod_const 2).symm
  have h_dist : (∏ p ∈ n.primeFactors, (p - 1)) * ∏ p ∈ n.primeFactors, 2 = ∏ p ∈ n.primeFactors, 2 * (p - 1) := by
    rw [← Finset.prod_mul_distrib]
    congr 1; ext x
    ring
  have h_rhs : n.totient * 2 ^ n.primeFactors.card = (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, 2 * (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul n, h_two_pow]
    rw [mul_assoc, h_dist]
  nth_rw 1 [← Nat.div_mul_cancel hdvd]
  rw [h_rhs]
  exact Nat.mul_le_mul_left _ h_prod_le

lemma prod_sub_one_ge_two_pow (S : Finset ℕ) (hP : ∀ p ∈ S, p.Prime) (h2 : 2 ∉ S) :
    2 ^ S.card ≤ ∏ p ∈ S, (p - 1) := by
  induction S using Finset.induction_on with
  | empty =>
    simp
  | insert q S' hq ih =>
    have hq_prime : q.Prime := hP q (Finset.mem_insert_self q S')
    have hq_ne_two : q ≠ 2 := by
      intro hc
      subst hc
      exact h2 (Finset.mem_insert_self 2 S')
    have hq_ge : 2 ≤ q := hq_prime.two_le
    have hq_ge_three : 3 ≤ q := by omega
    have hq_sub_one_ge_two : 2 ≤ q - 1 := by omega
    have hS'_prime : ∀ p ∈ S', p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hS'_not_two : 2 ∉ S' := fun hp => h2 (Finset.mem_insert_of_mem hp)
    have h_ih : 2 ^ S'.card ≤ ∏ p ∈ S', (p - 1) := ih hS'_prime hS'_not_two
    rw [Finset.card_insert_of_notMem hq]
    rw [Finset.prod_insert hq]
    rw [pow_succ']
    have h_mul_le : 2 * 2 ^ S'.card ≤ (q - 1) * ∏ p ∈ S', (p - 1) := Nat.mul_le_mul hq_sub_one_ge_two h_ih
    exact h_mul_le

lemma card_le_prod_sub_one (S : Finset ℕ) (hP : ∀ p ∈ S, p.Prime) :
    2 ^ S.card ≤ 2 * ∏ p ∈ S, (p - 1) := by
  by_cases h2 : 2 ∈ S
  · have h_eq : S = insert 2 (S.erase 2) := (Finset.insert_erase h2).symm
    have hnot : 2 ∉ S.erase 2 := Finset.notMem_erase 2 S
    have hS'_prime : ∀ p ∈ S.erase 2, p.Prime := fun p hp => hP p (Finset.erase_subset 2 S hp)
    have h_card : S.card = (S.erase 2).card + 1 := by
      nth_rw 1 [h_eq]
      rw [Finset.card_insert_of_notMem hnot]
    have h_prod : ∏ p ∈ S, (p - 1) = ∏ p ∈ S.erase 2, (p - 1) := by
      nth_rw 1 [h_eq]
      rw [Finset.prod_insert hnot]
      simp
    rw [h_card, pow_succ', h_prod]
    have h_le : 2 ^ (S.erase 2).card ≤ ∏ p ∈ S.erase 2, (p - 1) := prod_sub_one_ge_two_pow (S.erase 2) hS'_prime hnot
    exact Nat.mul_le_mul_left 2 h_le
  · have h_le : 2 ^ S.card ≤ ∏ p ∈ S, (p - 1) := prod_sub_one_ge_two_pow S hP h2
    have h_ge : ∏ p ∈ S, (p - 1) ≤ 2 * ∏ p ∈ S, (p - 1) := by omega
    exact h_le.trans h_ge

lemma prod_primeFactors_sub_one_le_totient (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, (p - 1) ≤ n.totient := by
  rw [Nat.totient_eq_div_primeFactors_mul n]
  have hdvd : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  have h_pos : 0 < ∏ p ∈ n.primeFactors, p := by
    apply Finset.prod_pos
    intros p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact hp_prime.pos
  have h_le : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have h_div_pos : 0 < n / ∏ p ∈ n.primeFactors, p := Nat.div_pos h_le h_pos
  have h1 : 1 ≤ n / ∏ p ∈ n.primeFactors, p := h_div_pos
  have h_mul_le : 1 * ∏ p ∈ n.primeFactors, (p - 1) ≤ (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1) := Nat.mul_le_mul_right _ h1
  rw [one_mul] at h_mul_le
  exact h_mul_le

lemma n_le_two_mul_totient_square (n : ℕ) (hn : n ≠ 0) :
    n ≤ 2 * n.totient ^ 2 := by
  have h1 : n ≤ n.totient * 2 ^ n.primeFactors.card := n_le_totient_mul_two_pow n
  have h2 : 2 ^ n.primeFactors.card ≤ 2 * ∏ p ∈ n.primeFactors, (p - 1) := by
    apply card_le_prod_sub_one
    intros p hp
    exact Nat.prime_of_mem_primeFactors hp
  have h3 : ∏ p ∈ n.primeFactors, (p - 1) ≤ n.totient := prod_primeFactors_sub_one_le_totient n hn
  have h4 : n.totient * 2 ^ n.primeFactors.card ≤ 2 * n.totient ^ 2 := by
    have ha : n.totient * 2 ^ n.primeFactors.card ≤ n.totient * (2 * ∏ p ∈ n.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ h2
    have hb : n.totient * (2 * ∏ p ∈ n.primeFactors, (p - 1)) = 2 * n.totient * ∏ p ∈ n.primeFactors, (p - 1) := by ring
    have hc : 2 * n.totient * ∏ p ∈ n.primeFactors, (p - 1) ≤ 2 * n.totient * n.totient := Nat.mul_le_mul_left _ h3
    have hd : 2 * n.totient * n.totient = 2 * n.totient ^ 2 := by ring
    rw [hb] at ha
    rw [hd] at hc
    exact ha.trans hc
  exact h1.trans h4

theorem oeis_233549_conjecture_1 :
  (∀ n, 2 < n → 0 < a n) →
  Set.Infinite {p : ℕ | Nat.Prime p ∧ ∃ x : ℕ, p = x ^ 4 + 1} := by
  intro h_inf
  by_contra h_finite
  rw [Set.Infinite] at h_finite
  push_neg at h_finite
  let S_finset : Finset ℕ := h_finite.toFinset
  let M := S_finset.sup id
  have h_bound : ∀ p, Nat.Prime p ∧ (∃ x : ℕ, p = x ^ 4 + 1) → p ≤ M := by
    intros p hp
    have hp_mem : p ∈ S_finset := by
      rw [Set.Finite.mem_toFinset]
      exact hp
    exact Finset.le_sup (f := id) hp_mem
  let C := 2 * M ^ 2
  let n := M + 3 + C
  have h_two_lt_n : 2 < n := by omega
  have h_a_pos : 0 < a n := h_inf n h_two_lt_n
  have h_filter_nonempty : (Finset.filter (fun p : ℕ =>
    p.Prime ∧
    let q := n - p
    Nat.Prime ((p.totient * q.totient) ^ 4 + 1)
  ) (Finset.range n)).Nonempty := Finset.card_pos.mp h_a_pos
  rcases h_filter_nonempty with ⟨p, hp_mem⟩
  rw [Finset.mem_filter] at hp_mem
  have hp_range : p ∈ Finset.range n := hp_mem.1
  have hp_cond : p.Prime ∧ let q := n - p; Nat.Prime ((p.totient * q.totient) ^ 4 + 1) := hp_mem.2
  rw [Finset.mem_range] at hp_range
  have hp_prime : p.Prime := hp_cond.1
  let q := n - p
  have hq_prime_expr : Nat.Prime ((p.totient * q.totient) ^ 4 + 1) := hp_cond.2
  have hq_pos : 0 < q := by omega
  have hq_ne_zero : q ≠ 0 := by omega
  let x := p.totient * q.totient
  have h_prime_x : Nat.Prime (x ^ 4 + 1) := hq_prime_expr
  have h_mem_S : x ^ 4 + 1 ∈ {p : ℕ | Nat.Prime p ∧ ∃ y : ℕ, p = y ^ 4 + 1} := by
    simp only [Set.mem_setOf_eq]
    exact ⟨h_prime_x, ⟨x, rfl⟩⟩
  have h_x_bound : x ^ 4 + 1 ≤ M := h_bound (x ^ 4 + 1) h_mem_S
  have h_x_le_M : x ≤ M := by
    have h_x_le_pow : x ≤ x ^ 4 := by
      cases x with
      | zero => simp
      | succ x =>
        have h_pow : x + 1 ≤ (x + 1) ^ 4 := Nat.le_self_pow (by omega) (x + 1)
        exact h_pow
    omega
  have hq_le : q ≤ 2 * q.totient ^ 2 := n_le_two_mul_totient_square q hq_ne_zero
  have hp_tot : p.totient = p - 1 := Nat.totient_prime hp_prime
  have h_p_tot_pos : 0 < p.totient := by
    rw [hp_tot]
    have : 2 ≤ p := hp_prime.two_le
    omega
  have h_q_tot_pos : 0 < q.totient := Nat.totient_pos.mpr hq_pos
  have h_q_tot_le_x : q.totient ≤ x := by
    have : 1 * q.totient ≤ p.totient * q.totient := Nat.mul_le_mul_right q.totient h_p_tot_pos
    rw [one_mul] at this
    exact this
  have h_q_tot_le_M : q.totient ≤ M := h_q_tot_le_x.trans h_x_le_M
  have hq_bound_M : q ≤ C := by
    have h_sq_le : q.totient ^ 2 ≤ M ^ 2 := by
      exact Nat.pow_le_pow_left h_q_tot_le_M 2
    have h_mul_sq : 2 * q.totient ^ 2 ≤ 2 * M ^ 2 := Nat.mul_le_mul_left 2 h_sq_le
    exact hq_le.trans h_mul_sq
  have hp_tot_le_x : p.totient ≤ x := by
    have : p.totient * 1 ≤ p.totient * q.totient := Nat.mul_le_mul_left p.totient h_q_tot_pos
    rw [mul_one] at this
    exact this
  have hp_tot_le_M : p.totient ≤ M := hp_tot_le_x.trans h_x_le_M
  have hp_bound_M : p ≤ M + 1 := by
    rw [hp_tot] at hp_tot_le_M
    omega
  have hn_sum : n = p + q := by omega
  have hn_le : n ≤ M + 1 + C := by
    rw [hn_sum]
    exact Nat.add_le_add hp_bound_M hq_bound_M
  omega



