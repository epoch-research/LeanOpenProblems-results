import FormalConjectures.Util.ProblemImports

open Nat

lemma dvd_two_pow_iff {a N : ℕ} (h : a ∣ 2 ^ N) : ∃ k ≤ N, a = 2 ^ k := by
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp h with ⟨k, hk, rfl⟩
  exact ⟨k, hk, rfl⟩

lemma not_prime_two_pow_add_one (c d : ℕ) (hc : 0 < c) (hd : Odd d) (hd1 : 1 < d) : ¬ Nat.Prime (2 ^ (c * d) + 1) := by
  have hdvd : 2 ^ c + 1 ∣ (2 ^ c) ^ d + 1 ^ d := hd.nat_add_dvd_pow_add_pow (2 ^ c) 1
  rw [one_pow] at hdvd
  rw [← pow_mul] at hdvd
  have h_two_pow_ge : 2 ^ c ≥ 2 := by
    have : 2 ^ 1 ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) hc
    exact this
  have h_div_gt : 1 < 2 ^ c + 1 := by omega
  have h_div_lt : 2 ^ c + 1 < 2 ^ (c * d) + 1 := by
    rw [add_lt_add_iff_right]
    have h_lt : c < c * d := by
      calc c = c * 1 := (mul_one c).symm
      _ < c * d := Nat.mul_lt_mul_of_pos_left hd1 hc
    exact Nat.pow_lt_pow_right (by decide) h_lt
  intro h_prime
  have h_eq_or_eq := h_prime.eq_one_or_self_of_dvd (2 ^ c + 1) hdvd
  omega

lemma eq_two_pow_of_prime_two_pow_add_one {u : ℕ} (hu : 0 < u) (hp : Nat.Prime (2 ^ u + 1)) : ∃ a : ℕ, u = 2 ^ a := by
  rcases exists_eq_two_pow_mul_odd (Nat.ne_of_gt hu) with ⟨a, d, hd, rfl⟩
  have hd_pos : 0 < d := by
    by_contra hd0
    have : d = 0 := by omega
    subst this
    simp [mul_zero] at hu
  by_cases hd1 : 1 < d
  · have h_not_prime := not_prime_two_pow_add_one (2 ^ a) d (Nat.two_pow_pos a) hd hd1
    contradiction
  · have hd_eq : d = 1 := by omega
    subst hd_eq
    rw [mul_one]
    exact ⟨a, rfl⟩

lemma eq_of_pow_two_mul_odd {N K Q : ℕ} (hQ : Odd Q) (h : 2 ^ N = 2 ^ K * Q) : K = N ∧ Q = 1 := by
  rcases hQ with ⟨q, rfl⟩
  have h_le : N ≤ K ∨ K < N := by omega
  rcases h_le with h_le | h_lt
  · have h_eq : 2 ^ N * 1 = 2 ^ N * (2 ^ (K - N) * (2 * q + 1)) := by
      rw [mul_one, ← mul_assoc, ← pow_add]
      have : N + (K - N) = K := by omega
      rw [this, h]
    have h_eq2 : 1 = 2 ^ (K - N) * (2 * q + 1) := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos N) h_eq
    by_cases h_K_N : K = N
    · subst h_K_N
      simp only [tsub_self, pow_zero, one_mul] at h_eq2
      omega
    · have h_gt : K - N > 0 := by omega
      have h_even_pow : Even (2 ^ (K - N)) := by
        have h_dec : K - N = (K - N - 1) + 1 := by omega
        rw [h_dec, pow_succ, mul_comm]
        exact even_two_mul _
      have h_even : Even (2 ^ (K - N) * (2 * q + 1)) := Even.mul_right h_even_pow _
      rw [← h_eq2] at h_even
      contradiction
  · have h_eq : 2 ^ K * 2 ^ (N - K) = 2 ^ K * (2 * q + 1) := by
      rw [← pow_add]
      have : K + (N - K) = N := by omega
      rw [this, h]
    have h_eq2 : 2 ^ (N - K) = 2 * q + 1 := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos K) h_eq
    have h_even : Even (2 ^ (N - K)) := by
      have h_dec : N - K = (N - K - 1) + 1 := by omega
      rw [h_dec, pow_succ, mul_comm]
      exact even_two_mul _
    rw [h_eq2] at h_even
    have h_odd : Odd (2 * q + 1) := by use q
    have h_not_even := Nat.not_even_iff_odd.mpr h_odd
    contradiction

lemma dvd_totient_of_mem_primeFactors {n p : ℕ} (hp : p ∈ n.primeFactors) : p - 1 ∣ totient n := by
  by_cases hn : n = 0
  · subst hn; simp
  · rw [totient_eq_div_primeFactors_mul n, mul_comm]
    have h_mem : p - 1 ∣ ∏ x ∈ n.primeFactors, (x - 1) := Finset.dvd_prod_of_mem (fun x => x - 1) hp
    have h_div : (∏ x ∈ n.primeFactors, (x - 1)) ∣ (∏ x ∈ n.primeFactors, (x - 1)) * (n / ∏ p ∈ n.primeFactors, p) := dvd_mul_right _ _
    exact dvd_trans h_mem h_div

lemma m_eq_pow_p {m p : ℕ} (hm : m ≠ 0) (hS : m.primeFactors = {p}) : m = p ^ (m.factorization p) := by
  have h := factorization_prod_pow_eq_self hm
  rw [prod_factorization_eq_prod_primeFactors] at h
  rw [hS] at h
  rw [Finset.prod_singleton] at h
  exact h.symm

lemma prime_factor_fermat {N : ℕ} {m p : ℕ} (hm_odd : ¬ 2 ∣ m) (hp : p ∈ m.primeFactors) (h_tot : totient m = 2 ^ N) : ∃ a, p - 1 = 2 ^ (2 ^ a) := by
  have hdvd : p - 1 ∣ totient m := dvd_totient_of_mem_primeFactors hp
  rw [h_tot] at hdvd
  rcases dvd_two_pow_iff hdvd with ⟨u, _, hu_eq⟩
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_gt2 : p > 2 := by
    have hp_ge2 : p ≥ 2 := hp_prime.two_le
    by_contra h_le
    have hp_eq2 : p = 2 := by omega
    subst hp_eq2
    have hdvd_m : 2 ∣ m := (Nat.mem_primeFactors.mp hp).2.1
    contradiction
  have hu_pos : 0 < u := by
    by_contra hu0
    have : u = 0 := by omega
    subst this
    simp at hu_eq
    omega
  have hp_eq : p = 2 ^ u + 1 := by omega
  have hp_prime' : Nat.Prime (2 ^ u + 1) := by
    rw [← hp_eq]
    exact hp_prime
  rcases eq_two_pow_of_prime_two_pow_add_one hu_pos hp_prime' with ⟨a, rfl⟩
  use a

lemma prime_dvd_totient_of_sq_dvd {p m : ℕ} (hp : p.Prime) (hsq : p ^ 2 ∣ m) : p ∣ totient m := by
  have hdvd_tot : totient (p ^ 2) ∣ totient m := totient_dvd_of_dvd hsq
  have h_tot_p2 : totient (p ^ 2) = p * (p - 1) := by
    have h := totient_prime_pow_succ hp 1
    have h11 : 1 + 1 = 2 := rfl
    have hp1 : p ^ 1 = p := pow_one p
    rw [h11, hp1] at h
    exact h
  rw [h_tot_p2] at hdvd_tot
  have hdvd_p : p ∣ p * (p - 1) := dvd_mul_right p (p - 1)
  exact dvd_trans hdvd_p hdvd_tot

lemma my_geom_sum_two (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : 2 ^ n > 0 := Nat.two_pow_pos n
    omega

lemma sum_two_pow_lt_two_pow (s : Finset ℕ) (N : ℕ) (h : ∀ x ∈ s, x < N) :
    ∑ i ∈ s, 2 ^ i < 2 ^ N := by
  have h_sub : s ⊆ Finset.range N := by
    intro x hx
    rw [Finset.mem_range]
    exact h x hx
  have h_le : ∑ i ∈ s, 2 ^ i ≤ ∑ i ∈ Finset.range N, 2 ^ i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
    intro i _ _
    exact Nat.zero_le _
  rw [my_geom_sum_two N] at h_le
  have h_pos : 2 ^ N > 0 := Nat.two_pow_pos N
  omega


lemma totient_composite_contradiction {N_idx N m : ℕ} (hN_idx : N_idx > 0) (hN : N = 2 ^ N_idx) (hm_gt : 1 < m) (hm_odd : ¬ 2 ∣ m) (hm_comp : ¬ m.Prime) (h_tot : totient m = 2 ^ N) : False := by
  let S := m.primeFactors
  have hm_nz : m ≠ 0 := by omega
  have h_a : ∀ p, ∃ k, p ∈ S → p - 1 = 2 ^ (2 ^ k) := by
    intro p
    by_cases hp : p ∈ S
    · rcases prime_factor_fermat hm_odd hp h_tot with ⟨k, hk⟩
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  let a := fun p => Classical.choose (h_a p)
  have ha_spec : ∀ p ∈ S, p - 1 = 2 ^ (2 ^ (a p)) := by
    intro p hp
    exact Classical.choose_spec (h_a p) hp
  rcases Nat.exists_prime_and_dvd (by omega : m ≠ 1) with ⟨p, hp_prime, hp_dvd⟩
  have hp_mem : p ∈ S := Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hm_nz⟩
  have hS_card_pos : S.card > 0 := Finset.card_pos.mpr ⟨p, hp_mem⟩
  have hS_card_ne1 : S.card ≠ 1 := by
    intro h_card1
    have hS_eq : S = {p} := by
      rw [Finset.card_eq_one] at h_card1
      rcases h_card1 with ⟨q, hq⟩
      have hp_mem' := hp_mem
      rw [hq] at hp_mem'
      simp only [Finset.mem_singleton] at hp_mem'
      subst hp_mem'
      exact hq
    have hm_eq : m = p ^ (m.factorization p) := m_eq_pow_p hm_nz hS_eq
    have hp_fac_pos : m.factorization p ≠ 0 := by
      by_contra hc
      have : m.factorization p = 0 := by omega
      rw [this, pow_zero] at hm_eq
      omega
    by_cases h_fac1 : m.factorization p = 1
    · rw [h_fac1, pow_one] at hm_eq
      subst hm_eq
      exact hm_comp hp_prime
    · have hp_fac_ge2 : m.factorization p ≥ 2 := by omega
      have hp2_dvd : p ^ 2 ∣ m := by
        rw [hm_eq]
        exact pow_dvd_pow p hp_fac_ge2
      have hp_dvd_tot : p ∣ totient m := prime_dvd_totient_of_sq_dvd hp_prime hp2_dvd
      rw [h_tot] at hp_dvd_tot
      have hp_dvd_two : p ∣ 2 := hp_prime.dvd_of_dvd_pow hp_dvd_tot
      have hp_eq2 : p = 2 := by
        have : p ≥ 2 := hp_prime.two_le
        have : p ≤ 2 := Nat.le_of_dvd (by decide) hp_dvd_two
        omega
      subst hp_eq2
      have h2_dvd_m : 2 ∣ m := hp_dvd
      contradiction
  have hS_card_ge2 : S.card ≥ 2 := by omega
  let f := fun p => 2 ^ (a p)
  let U := S.image f
  have h_inj : Set.InjOn f S := by
    intro x hx y hy hxy
    have hx' := ha_spec x hx
    have hy' := ha_spec y hy
    have hx_prime := Nat.prime_of_mem_primeFactors hx
    have hy_prime := Nat.prime_of_mem_primeFactors hy
    have hx2 : x ≥ 2 := hx_prime.two_le
    have hy2 : y ≥ 2 := hy_prime.two_le
    have h_pow2 : 2 ^ (2 ^ a x) = 2 ^ (2 ^ a y) := by
      exact congr_arg (fun g => 2 ^ g) hxy
    have h_pow1 : 2 ^ a x = 2 ^ a y := Nat.pow_right_injective (by decide) h_pow2
    have h_eq : a x = a y := Nat.pow_right_injective (by decide) h_pow1
    omega
  have h_card_U : U.card = S.card := Finset.card_image_of_injOn h_inj
  have h_card_U_ge2 : U.card ≥ 2 := by omega
  have h_tot_eq' : totient m = (∏ p ∈ S, (p - 1)) * (m / ∏ p ∈ S, p) := by
    rw [totient_eq_div_primeFactors_mul m, mul_comm]
  let Q := m / ∏ p ∈ S, p
  have h_prod_eq : ∏ p ∈ S, (p - 1) = ∏ p ∈ S, 2 ^ (2 ^ (a p)) := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    exact ha_spec x hx
  have h_pow_sum : ∏ p ∈ S, 2 ^ (2 ^ (a p)) = 2 ^ (∑ p ∈ S, 2 ^ (a p)) := by
    exact Finset.prod_pow_eq_pow_sum S (fun p => 2 ^ (a p)) 2
  have h_tot_eq'' : totient m = 2 ^ (∑ p ∈ S, 2 ^ (a p)) * Q := by
    rw [h_tot_eq', h_prod_eq, h_pow_sum]
  let K := ∑ p ∈ S, 2 ^ (a p)
  have hQ_odd : Odd Q := by
    have h_dvd : Q ∣ m := Nat.div_dvd_of_dvd (prod_primeFactors_dvd m)
    have : ¬ 2 ∣ Q := by
      intro h2_dvd
      have : 2 ∣ m := dvd_trans h2_dvd h_dvd
      exact hm_odd this
    rw [← even_iff_two_dvd] at this
    exact Nat.not_even_iff_odd.mp this
  have h_tot_K : 2 ^ N = 2 ^ K * Q := by
    rw [← h_tot, h_tot_eq'']
  rcases eq_of_pow_two_mul_odd hQ_odd h_tot_K with ⟨h_K_eq, hQ_eq⟩
  have h_lt : ∀ p ∈ S, 2 ^ (a p) < N := by
    intro p hp
    have h_sum : ∑ q ∈ S, 2 ^ (a q) = 2 ^ (a p) + ∑ q ∈ S \ {p}, 2 ^ (a q) := by
      exact Finset.sum_eq_add_sum_diff_singleton hp (fun q => 2 ^ (a q))
    change K = 2 ^ (a p) + ∑ q ∈ S \ {p}, 2 ^ (a q) at h_sum
    rw [h_K_eq] at h_sum
    have h_nonempty : (S \ {p}).Nonempty := by
      have h_card : (S \ {p}).card = S.card - 1 := by
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hp)]
        rfl
      have : (S \ {p}).card > 0 := by omega
      exact Finset.card_pos.mp this
    rcases h_nonempty with ⟨q, hq⟩
    have h_pos : 2 ^ (a q) > 0 := Nat.two_pow_pos _
    have h_le : 2 ^ (a q) ≤ ∑ y ∈ S \ {p}, 2 ^ (a y) := Finset.single_le_sum (f := fun y => 2 ^ (a y)) (fun _ _ => Nat.zero_le _) hq
    have h_sum_pos : ∑ y ∈ S \ {p}, 2 ^ (a y) > 0 := by omega
    omega
  have ha_lt : ∀ x ∈ S.image a, x < N_idx := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨p, hp, rfl⟩
    have h_lt' := h_lt p hp
    rw [hN] at h_lt'
    exact Nat.pow_lt_pow_iff_right (by decide) |>.mp h_lt'
  have ha_inj : Set.InjOn a S := by
    intro x hx y hy hxy
    have h_f : f x = f y := by
      dsimp [f]
      rw [hxy]
    exact h_inj hx hy h_f
  have h_sum_image : ∑ x ∈ S.image a, 2 ^ x = ∑ p ∈ S, 2 ^ (a p) := by
    exact Finset.sum_image ha_inj
  have h_sum_lt := sum_two_pow_lt_two_pow (S.image a) N_idx ha_lt
  rw [h_sum_image] at h_sum_lt
  rw [← hN] at h_sum_lt
  change K < N at h_sum_lt
  rw [h_K_eq] at h_sum_lt
  omega

