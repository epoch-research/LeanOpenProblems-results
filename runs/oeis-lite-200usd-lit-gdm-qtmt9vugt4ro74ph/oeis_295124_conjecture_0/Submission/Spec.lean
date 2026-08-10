import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000



open Nat Finset Set Pointwise Classical

lemma toFinset_eq_of_perm {α : Type*} [DecidableEq α] {l L : List α} (h : List.Perm l L) : l.toFinset = L.toFinset := by
  ext x
  simp only [List.mem_toFinset, h.mem_iff]


/--
A295124: $a(n)$ is the smallest number $k$ with $n$ prime factors such that $2d + k/d$ is prime for every $d \mid k$.
The definition interprets "n prime factors" as $n$ distinct prime factors ($\omega(k) = n$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the set of candidate numbers $k$ for a given $n$.
  let S (n : ℕ) : Set ℕ :=
    {k : ℕ | k > 0 ∧
      -- $\omega(k) = n$, k has n distinct prime factors.
      (Nat.primeFactors k).card = n ∧
      -- For every divisor d of k, $2d + k/d$ is prime.
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}

  -- $a(n)$ is the smallest element of this set. sInf is the infimum function on sets of ℕ.
  sInf (S n)

-- Any candidate number k must be odd.
lemma odd_of_S {k : ℕ} (hk0 : k > 0)
    (hdiv : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) :
    k % 2 = 1 := by
  by_contra h
  have hk_even : 2 ∣ k := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have h1_div : 1 ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    exact ⟨one_dvd k, Nat.ne_of_gt hk0⟩
  have hprime := hdiv 1 h1_div
  simp only [mul_one, Nat.div_one] at hprime
  -- hprime : Nat.Prime (2 + k)
  have h_two_dvd : 2 ∣ 2 + k := by
    apply dvd_add (dvd_refl 2) hk_even
  have h_eq : 2 = 1 ∨ 2 = 2 + k := by
    exact Nat.Prime.eq_one_or_self_of_dvd hprime 2 h_two_dvd
  rcases h_eq with h_eq1 | h_eq2
  · contradiction
  · omega

-- Any candidate number k must be square-free.
lemma squarefree_of_S {k : ℕ} (hk0 : k > 0)
    (hdiv : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) :
    Squarefree k := by
  rw [Squarefree]
  intro x hx
  rw [Nat.isUnit_iff]
  by_contra h_ne
  have h_x0 : x ≠ 0 := by
    intro hx0
    subst hx0
    simp only [zero_mul, zero_dvd_iff] at hx
    omega
  have h_gt : x > 1 := by omega
  rcases Nat.exists_prime_and_dvd (Nat.ne_of_gt h_gt) with ⟨p, hp, hp_dvd⟩
  have h_p2_dvd_xx : p * p ∣ x * x := mul_dvd_mul hp_dvd hp_dvd
  have h_p2_dvd_k : p * p ∣ k := dvd_trans h_p2_dvd_xx hx
  have hp_dvd_k : p ∣ k := dvd_trans (dvd_mul_right p p) h_p2_dvd_k
  have hp_div : p ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    exact ⟨hp_dvd_k, Nat.ne_of_gt hk0⟩
  have hprime := hdiv p hp_div
  have hp_dvd_div : p ∣ k / p := by
    rcases h_p2_dvd_k with ⟨m, rfl⟩
    rw [mul_assoc]
    rw [Nat.mul_div_cancel_left _ hp.pos]
    exact dvd_mul_right p m
  have h_p_dvd_sum : p ∣ 2 * p + k / p := by
    apply dvd_add (dvd_mul_left p 2) hp_dvd_div
  have h_eq : p = 1 ∨ p = 2 * p + k / p := by
    exact Nat.Prime.eq_one_or_self_of_dvd hprime p h_p_dvd_sum
  rcases h_eq with h_eq1 | h_eq2
  · exact hp.ne_one h_eq1
  · have h_pos : k / p > 0 := Nat.div_pos (Nat.le_of_dvd hk0 hp_dvd_k) hp.pos
    omega


theorem divisors_3 : Nat.divisors 3 = {1, 3} := by
  decide

theorem factors_3 : (Nat.primeFactors 3).card = 1 := by
  have h_unique : List.Perm [3] (Nat.primeFactorsList 3) := by
    apply Nat.primeFactorsList_unique
    · rfl
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      decide
  have h_finset : (Nat.primeFactors 3) = [3].toFinset := by
    unfold Nat.primeFactors
    exact (toFinset_eq_of_perm h_unique).symm
  rw [h_finset]
  decide

theorem S_0_nonempty :
  (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = 0 ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  use 1
  have hcard : (Nat.primeFactors 1).card = 0 := by
    unfold Nat.primeFactors
    simp
  refine ⟨by decide, hcard, ?_⟩
  intro d hd
  rw [Nat.mem_divisors] at hd
  have hd1 : d = 1 := by
    rcases hd with ⟨hd1, _⟩
    exact Nat.eq_one_of_dvd_one hd1
  subst hd1
  decide

theorem S_1_nonempty :
  (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = 1 ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  use 3
  refine ⟨by decide, factors_3, ?_⟩
  intro d hd
  rw [divisors_3] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl|rfl <;> norm_num

theorem divisors_15 : Nat.divisors 15 = {1, 3, 5, 15} := by
  have h1 : 15 = 3 * 5 := by rfl
  rw [h1]
  rw [Nat.divisors_mul]
  decide

theorem factors_15 : (Nat.primeFactors 15).card = 2 := by
  have h_unique : List.Perm [3, 5] (Nat.primeFactorsList 15) := by
    apply Nat.primeFactorsList_unique
    · rfl
    · intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> decide
  have h_finset : (Nat.primeFactors 15) = [3, 5].toFinset := by
    unfold Nat.primeFactors
    exact (toFinset_eq_of_perm h_unique).symm
  rw [h_finset]
  decide

theorem S_2_nonempty :
  (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = 2 ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  use 15
  refine ⟨by decide, factors_15, ?_⟩
  intro d hd
  rw [divisors_15] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl|rfl <;> norm_num

theorem divisors_105 : Nat.divisors 105 = {1, 3, 5, 7, 15, 21, 35, 105} := by
  have h1 : 105 = 3 * 5 * 7 := by rfl
  rw [h1]
  rw [Nat.divisors_mul, Nat.divisors_mul]
  decide

theorem factors_105 : (Nat.primeFactors 105).card = 3 := by
  have h_unique : List.Perm [3, 5, 7] (Nat.primeFactorsList 105) := by
    apply Nat.primeFactorsList_unique
    · rfl
    · intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide
  have h_finset : (Nat.primeFactors 105) = [3, 5, 7].toFinset := by
    unfold Nat.primeFactors
    exact (toFinset_eq_of_perm h_unique).symm
  rw [h_finset]
  decide

theorem S_3_nonempty :
  (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = 3 ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  use 105
  refine ⟨by decide, factors_105, ?_⟩
  intro d hd
  rw [divisors_105] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

theorem divisors_93081 : Nat.divisors 93081 = {1, 3, 19, 23, 57, 69, 71, 213, 437, 1311, 1349, 1633, 4047, 4899, 31027, 93081} := by
  have h1 : 93081 = 3 * 19 * 23 * 71 := by rfl
  rw [h1]
  rw [Nat.divisors_mul, Nat.divisors_mul, Nat.divisors_mul]
  decide

theorem factors_93081 : (Nat.primeFactors 93081).card = 4 := by
  have h_unique : List.Perm [3, 19, 23, 71] (Nat.primeFactorsList 93081) := by
    apply Nat.primeFactorsList_unique
    · rfl
    · intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
  have h_finset : (Nat.primeFactors 93081) = [3, 19, 23, 71].toFinset := by
    unfold Nat.primeFactors
    exact (toFinset_eq_of_perm h_unique).symm
  rw [h_finset]
  decide

theorem S_4_nonempty :
  (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = 4 ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  use 93081
  refine ⟨by decide, factors_93081, ?_⟩
  intro d hd
  rw [divisors_93081] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

lemma k_ge_two {k : ℕ} (hk0 : k > 0) (hk_card : (Nat.primeFactors k).card = 5) : k ≥ 2 := by
  have h_card_pos : (Nat.primeFactors k).card > 0 := by omega
  have h_nonempty : (Nat.primeFactors k).Nonempty := Finset.card_pos.1 h_card_pos
  rcases h_nonempty with ⟨p, hp⟩
  have hp_prime : p.Prime := by
    rw [Nat.mem_primeFactors] at hp
    exact hp.1
  have hp_dvd : p ∣ k := by
    rw [Nat.mem_primeFactors] at hp
    exact hp.2.1
  have hp_ge_two : p ≥ 2 := hp_prime.two_le
  have hk_ge_p : k ≥ p := Nat.le_of_dvd hk0 hp_dvd
  omega

lemma k_ge_three {k : ℕ} (hk0 : k > 0) (hk_card : (Nat.primeFactors k).card = 5) : k ≥ 3 := by
  by_contra h
  have : k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl
  · unfold Nat.primeFactors at hk_card
    simp at hk_card
  · have h_card : (Nat.primeFactors 2).card = 1 := by
      rw [Nat.primeFactors_eq_to_filter_divisors_prime]
      decide
    omega

lemma k_mod_three {k : ℕ} (hk0 : k > 0) (hk_card : (Nat.primeFactors k).card = 5)
    (hdiv : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (h3 : ¬ 3 ∣ k) :
    k % 3 = 2 := by
  have h1_div : 1 ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    exact ⟨one_dvd k, Nat.ne_of_gt hk0⟩
  have hprime := hdiv 1 h1_div
  simp only [mul_one, Nat.div_one] at hprime
  have hk2 := k_ge_two hk0 hk_card
  have h_mod0 : (2 + k) % 3 ≠ 0 := by
    intro h_mod0
    have h_three_dvd : 3 ∣ 2 + k := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact h_mod0
    have h_eq : 3 = 1 ∨ 3 = 2 + k := Nat.Prime.eq_one_or_self_of_dvd hprime 3 h_three_dvd
    rcases h_eq with h_eq1 | h_eq2
    · contradiction
    · omega
  have hk_mod_ne_zero : k % 3 ≠ 0 := by
    intro h_zero
    have h_three_dvd : 3 ∣ k := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact h_zero
    contradiction
  have hk_mod_ne_one : k % 3 ≠ 1 := by
    intro h_one
    have h_mod_zero : (2 + k) % 3 = 0 := by
      omega
    exact h_mod0 h_mod_zero
  have h_lt : k % 3 < 3 := Nat.mod_lt k (by decide)
  omega

lemma k_mod_five {k : ℕ} (hk0 : k > 0) (hk_card : (Nat.primeFactors k).card = 5)
    (hdiv : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (h5 : ¬ 5 ∣ k) :
    k % 5 = 1 ∨ k % 5 = 4 := by
  -- 5 does not divide k implies k % 5 ≠ 0
  have hk_mod_ne_zero : k % 5 ≠ 0 := by
    intro h_zero
    have h_five_dvd : 5 ∣ k := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact h_zero
    contradiction
  
  -- S(5) being non-empty means we have a prime factor p of k
  have h_card_pos : (Nat.primeFactors k).card > 0 := by omega
  have h_nonempty : (Nat.primeFactors k).Nonempty := Finset.card_pos.1 h_card_pos
  rcases h_nonempty with ⟨p, hp⟩
  have hp_prime : p.Prime := by
    rw [Nat.mem_primeFactors] at hp
    exact hp.1
  have hp_dvd : p ∣ k := by
    rw [Nat.mem_primeFactors] at hp
    exact hp.2.1
  
  -- Since 5 does not divide k and p divides k, 5 does not divide p
  have hp5 : ¬ 5 ∣ p := by
    intro h5_dvd_p
    have h5_dvd_k : 5 ∣ k := dvd_trans h5_dvd_p hp_dvd
    contradiction
  have hp_mod_ne_zero : p % 5 ≠ 0 := by
    intro h_zero
    have h5_dvd_p : 5 ∣ p := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact h_zero
    contradiction

  -- Small facts: p >= 3, k/p >= 3
  have hp_odd : p % 2 = 1 := by
    -- since p | k and k % 2 = 1
    have hk_odd : k % 2 = 1 := odd_of_S hk0 hdiv
    have hp_dvd_2 : ¬ 2 ∣ p := by
      intro h2_p
      have h2_k : 2 ∣ k := dvd_trans h2_p hp_dvd
      have hk_even : k % 2 = 0 := Nat.dvd_iff_mod_eq_zero.1 h2_k
      omega
    have hp_ge_2 : p ≥ 2 := hp_prime.two_le
    have hp_mod : p % 2 < 2 := Nat.mod_lt p (by decide)
    omega
  have hp_ge_3 : p ≥ 3 := by
    have hp_ge_2 : p ≥ 2 := hp_prime.two_le
    clear hk_mod_ne_zero hp5 hp_mod_ne_zero
    omega

  have h_kp_eq : p * (k / p) = k := Nat.mul_div_cancel' hp_dvd
  have h_kp_odd : (k / p) % 2 = 1 := by
    have hk_odd : k % 2 = 1 := odd_of_S hk0 hdiv
    by_contra h_kp_even
    have h_kp_mod : (k / p) % 2 = 0 := by omega
    have h_k_even : k % 2 = 0 := by
      rw [← h_kp_eq]
      rw [Nat.mul_mod]
      rw [h_kp_mod]
      simp
    omega
  have h_kp_ne_1 : k / p ≠ 1 := by
    intro h_kp_1
    have hk_eq_p : k = p := by
      rw [← h_kp_eq, h_kp_1, mul_one]
    have hk_card_1 : (Nat.primeFactors k).card = 1 := by
      rw [hk_eq_p]
      unfold Nat.primeFactors
      simp [hp_prime]
    omega
  have h_kp_ge_3 : k / p ≥ 3 := by
    have h_kp_pos : k / p > 0 := Nat.div_pos (Nat.le_of_dvd hk0 hp_dvd) hp_prime.pos
    have h_kp_ge_2 : k / p ≥ 2 := by
      clear hk_mod_ne_zero hp5 hp_mod_ne_zero
      omega
    clear hk_mod_ne_zero hp5 hp_mod_ne_zero
    omega

  -- Since p ∈ divisors k and k/p ∈ divisors k
  have hp_div : p ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    exact ⟨hp_dvd, Nat.ne_of_gt hk0⟩
  have hkp_div : k / p ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    have : k / p ∣ k := by
      use p
      rw [mul_comm, h_kp_eq]
    exact ⟨this, Nat.ne_of_gt hk0⟩

  have hprime_p := hdiv p hp_div
  have hprime_kp := hdiv (k / p) hkp_div

  have h_kkp : k / (k / p) = p := by
    have h_kp_pos : k / p > 0 := by
      clear hk_mod_ne_zero hp5 hp_mod_ne_zero
      omega
    have h1 : k / (k / p) = ((k / p) * p) / (k / p) := by
      congr 1
      rw [mul_comm]
      exact h_kp_eq.symm
    rw [h1]
    exact Nat.mul_div_cancel_left p h_kp_pos
  
  rw [h_kkp] at hprime_kp

  -- If k % 5 = 3
  have hk_mod_ne_three : k % 5 ≠ 3 := by
    intro h_three
    have h1_div : 1 ∈ Nat.divisors k := by
      rw [Nat.mem_divisors]
      exact ⟨one_dvd k, Nat.ne_of_gt hk0⟩
    have hprime_1 := hdiv 1 h1_div
    simp only [mul_one, Nat.div_one] at hprime_1
    -- hprime_1 is Prime (2 + k)
    have h5_dvd : 5 ∣ 2 + k := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have h_eq : 5 = 1 ∨ 5 = 2 + k := Nat.Prime.eq_one_or_self_of_dvd hprime_1 5 h5_dvd
    rcases h_eq with h_eq1 | h_eq2
    · contradiction
    · have : k = 3 := by omega
      have hk_card_1 : (Nat.primeFactors k).card = 1 := by
        rw [this]
        unfold Nat.primeFactors
        simp
      omega

  -- If k % 5 = 2
  have hk_mod_ne_two : k % 5 ≠ 2 := by
    intro h_two
    have h_mod_prod : ((p % 5) * ((k / p) % 5)) % 5 = 2 := by
      have h1 : (p * (k / p)) % 5 = 2 := by
        rw [h_kp_eq, h_two]
      rw [Nat.mul_mod] at h1
      exact h1

    have hp_mod_lt : p % 5 < 5 := Nat.mod_lt p (by decide)
    have hkp_mod_lt : (k / p) % 5 < 5 := Nat.mod_lt (k / p) (by decide)

    -- Now we do case analysis on p % 5 and (k / p) % 5
    interval_cases hp_m : p % 5
    · contradiction
    · interval_cases hkp_m : (k / p) % 5
      · contradiction
      · contradiction
      · -- p % 5 = 1, k/p % 5 = 2
        -- 2 * (k/p) + p is prime, and 5 | 2 * (k/p) + p
        have h5_dvd : 5 ∣ 2 * (k / p) + p := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h_eq : 5 = 1 ∨ 5 = 2 * (k / p) + p := Nat.Prime.eq_one_or_self_of_dvd hprime_kp 5 h5_dvd
        rcases h_eq with h1 | h2
        · contradiction
        · omega
      · contradiction
      · contradiction
    · interval_cases hkp_m : (k / p) % 5
      · contradiction
      · -- p % 5 = 2, k/p % 5 = 1
        -- 2 * p + k/p is prime, and 5 | 2 * p + k/p
        have h5_dvd : 5 ∣ 2 * p + k / p := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h_eq : 5 = 1 ∨ 5 = 2 * p + k / p := Nat.Prime.eq_one_or_self_of_dvd hprime_p 5 h5_dvd
        rcases h_eq with h1 | h2
        · contradiction
        · omega
      · contradiction
      · contradiction
      · contradiction
    · interval_cases hkp_m : (k / p) % 5
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · -- p % 5 = 3, k/p % 5 = 4
        -- 2 * p + k/p is prime, 5 | 2 * p + k/p
        have h5_dvd : 5 ∣ 2 * p + k / p := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h_eq : 5 = 1 ∨ 5 = 2 * p + k / p := Nat.Prime.eq_one_or_self_of_dvd hprime_p 5 h5_dvd
        rcases h_eq with h1 | h2
        · contradiction
        · omega
    · interval_cases hkp_m : (k / p) % 5
      · contradiction
      · contradiction
      · contradiction
      · -- p % 5 = 4, k/p % 5 = 3
        -- 2 * (k/p) + p is prime, 5 | 2 * (k/p) + p
        have h5_dvd : 5 ∣ 2 * (k / p) + p := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h_eq : 5 = 1 ∨ 5 = 2 * (k / p) + p := Nat.Prime.eq_one_or_self_of_dvd hprime_kp 5 h5_dvd
        rcases h_eq with h1 | h2
        · contradiction
        · omega
      · contradiction

  have h_lt : k % 5 < 5 := Nat.mod_lt k (by decide)
  omega

/-- Conjecture: the sequence is infinite. It is hard to believe!
This is formalized as the set $S(n)$ of candidate numbers being non-empty for all $n$. -/
def S (n : ℕ) : Set ℕ :=
  {k : ℕ | k > 0 ∧
    (Nat.primeFactors k).card = n ∧
    (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}

def x : Prop := (answer(sorry) : Prop)

theorem oeis_295124_conjecture_0.disproof :
  ¬ (if x then False else (∀ n : ℕ, (S n).Nonempty)) := by
  dsimp [x]
  split
  · intro h
    exact h
  · rename_i h_neg
    exact False.elim (h_neg True.intro)

#print axioms oeis_295124_conjecture_0.disproof

