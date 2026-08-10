import FormalConjectures.Util.ProblemImports

open Nat Finset Set

set_option quotPrecheck false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

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


lemma k_not_even (k : ℕ) (hk : k > 0) (h_prime : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) : ¬ 2 ∣ k := by
  intro h_even
  have h_dvd : k / 2 ∣ k := by
    exact Nat.div_dvd_of_dvd h_even
  have h_div_mem : k / 2 ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    exact ⟨h_dvd, hk.ne'⟩
  have h_pr := h_prime (k / 2) h_div_mem
  have h_eq : 2 * (k / 2) + k / (k / 2) = k + 2 := by
    rw [Nat.mul_div_cancel' h_even]
    rw [Nat.div_div_self h_even hk.ne']
  rw [h_eq] at h_pr
  -- Now we show that k + 2 is composite (or not prime)
  -- Since k is even, k = 2 * m
  rcases h_even with ⟨m, rfl⟩
  -- Since k > 0, m > 0
  have hm : m > 0 := by
    cases m
    · contradiction
    · exact Nat.succ_pos _
  -- So k + 2 = 2 * m + 2 = 2 * (m + 1)
  have h_comp : 2 * m + 2 = 2 * (m + 1) := by ring
  rw [h_comp] at h_pr
  -- Since m > 0, m + 1 > 1
  have hm1 : m + 1 > 1 := Nat.succ_lt_succ hm
  -- So 2 * (m + 1) is not prime because it has factor 2 and m + 1
  have h_not_prime : ¬ Nat.Prime (2 * (m + 1)) := by
    exact Nat.not_prime_mul (by decide) hm1.ne'
  exact h_not_prime h_pr


lemma k_squarefree (k : ℕ) (hk : k > 0) (h_prime : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (p : ℕ) (hp : p.Prime) : ¬ p^2 ∣ k := by
  intro h_div
  rcases h_div with ⟨m, rfl⟩
  have h_dvd : p * m ∣ p ^ 2 * m := by
    use p
    ring
  have h_div_mem : p * m ∈ Nat.divisors (p ^ 2 * m) := by
    rw [Nat.mem_divisors]
    refine ⟨h_dvd, ?_⟩
    intro h0
    exact hk.ne' h0
  have h_pr := h_prime (p * m) h_div_mem
  have hp_pos : p > 0 := hp.pos
  have hm_pos : m > 0 := by
    cases m
    · contradiction
    · exact Nat.succ_pos _
  have hpm_pos : p * m > 0 := Nat.mul_pos hp_pos hm_pos
  have h_eq : 2 * (p * m) + (p ^ 2 * m) / (p * m) = p * (2 * m + 1) := by
    have h_prod : p ^ 2 * m = p * (p * m) := by ring
    rw [h_prod, Nat.mul_div_cancel _ hpm_pos]
    ring
  rw [h_eq] at h_pr
  have h2m1_ne : 2 * m + 1 ≠ 1 := by
    omega
  have hp_ne : p ≠ 1 := hp.ne_one
  have h_not_prime : ¬ Nat.Prime (p * (2 * m + 1)) := by
    exact Nat.not_prime_mul hp_ne h2m1_ne
  exact h_not_prime h_pr


lemma test_card_two : (Nat.primeFactors 2).card = 1 := by
  have h : Nat.primeFactors 2 = {2} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have x_eq_2 := Nat.prime_two.eq_one_or_self_of_dvd x hx_dvd
      rcases x_eq_2 with h1 | h2
      · subst h1
        have h_not : ¬ Nat.Prime 1 := Nat.not_prime_one
        contradiction
      · exact h2
    · rintro rfl
      refine ⟨Nat.prime_two, by decide, by decide⟩
  rw [h]
  rfl

lemma k_mod_five_two (k : ℕ) (hk : k > 0) (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (hk_card : (Nat.primeFactors k).card = 5) : k % 5 ≠ 2 := by
  intro h_mod
  have hd : k ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    exact ⟨Nat.dvd_refl k, hk.ne'⟩
  have hp := h k hd
  have h_eq : 2 * k + k / k = 2 * k + 1 := by
    rw [Nat.div_self hk]
  rw [h_eq] at hp
  have h_mod_5 : (2 * k + 1) % 5 = 0 := by omega
  have h_dvd : 5 ∣ 2 * k + 1 := Nat.dvd_of_mod_eq_zero h_mod_5
  have h_eq_5 := hp.eq_one_or_self_of_dvd 5 h_dvd
  rcases h_eq_5 with h1 | h2
  · contradiction
  · have hk2 : k = 2 := by omega
    rw [hk2] at hk_card
    rw [test_card_two] at hk_card
    contradiction

lemma test_card : (Nat.primeFactors 3).card = 1 := by
  have h : Nat.primeFactors 3 = {3} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have x_eq_3 := Nat.prime_three.eq_one_or_self_of_dvd x hx_dvd
      rcases x_eq_3 with h1 | h2
      · subst h1
        have h_not : ¬ Nat.Prime 1 := Nat.not_prime_one
        contradiction
      · exact h2
    · rintro rfl
      refine ⟨Nat.prime_three, by decide, by decide⟩
  rw [h]
  rfl

lemma k_mod_five_three (k : ℕ) (hk : k > 0) (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (hk_card : (Nat.primeFactors k).card = 5) : k % 5 ≠ 3 := by
  intro h_mod
  have hd : 1 ∈ Nat.divisors k := Nat.one_mem_divisors.mpr hk.ne'
  have hp := h 1 hd
  have h_eq : 2 * 1 + k / 1 = 2 + k := by omega
  rw [h_eq] at hp
  have h_mod_5 : (2 + k) % 5 = 0 := by omega
  have h_dvd : 5 ∣ 2 + k := Nat.dvd_of_mod_eq_zero h_mod_5
  have h_eq_5 := hp.eq_one_or_self_of_dvd 5 h_dvd
  rcases h_eq_5 with h1 | h2
  · contradiction
  · have hk3 : k = 3 := by omega
    rw [hk3] at hk_card
    rw [test_card] at hk_card
    contradiction

lemma test_card_five : (Nat.primeFactors 5).card = 1 := by
  have h : Nat.primeFactors 5 = {5} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have hp5 : Nat.Prime 5 := by decide
      have x_eq_5 := hp5.eq_one_or_self_of_dvd x hx_dvd
      rcases x_eq_5 with h1 | h2
      · subst h1; contradiction
      · exact h2
    · rintro rfl
      refine ⟨by decide, by decide, by decide⟩
  rw [h]
  rfl

lemma test_card_six : (Nat.primeFactors 6).card = 2 := by
  have h : Nat.primeFactors 6 = {2, 3} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have hx_le : x ≤ 6 := Nat.le_of_dvd (by decide) hx_dvd
      have hx_pos : x > 0 := hx_prime.pos
      interval_cases x
      · contradiction
      · left; rfl
      · right; rfl
      · contradiction
      · contradiction
      · contradiction
    · rintro (rfl | rfl)
      · exact ⟨Nat.prime_two, by decide, by decide⟩
      · exact ⟨Nat.prime_three, by decide, by decide⟩
  rw [h]
  rfl

lemma k_mod_seven_three (k : ℕ) (hk : k > 0) (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (hk_card : (Nat.primeFactors k).card = 5) : k % 7 ≠ 3 := by
  intro h_mod
  have hd : k ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    exact ⟨Nat.dvd_refl k, hk.ne'⟩
  have hp := h k hd
  have h_eq : 2 * k + k / k = 2 * k + 1 := by
    rw [Nat.div_self hk]
  rw [h_eq] at hp
  have h_mod_7 : (2 * k + 1) % 7 = 0 := by omega
  have h_dvd : 7 ∣ 2 * k + 1 := Nat.dvd_of_mod_eq_zero h_mod_7
  have h_eq_7 := hp.eq_one_or_self_of_dvd 7 h_dvd
  rcases h_eq_7 with h1 | h2
  · contradiction
  · have hk3 : k = 3 := by omega
    rw [hk3] at hk_card
    rw [test_card] at hk_card
    contradiction

lemma k_mod_seven_five (k : ℕ) (hk : k > 0) (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (hk_card : (Nat.primeFactors k).card = 5) : k % 7 ≠ 5 := by
  intro h_mod
  have hd : 1 ∈ Nat.divisors k := Nat.one_mem_divisors.mpr hk.ne'
  have hp := h 1 hd
  have h_eq : 2 * 1 + k / 1 = 2 + k := by omega
  rw [h_eq] at hp
  have h_mod_7 : (2 + k) % 7 = 0 := by omega
  have h_dvd : 7 ∣ 2 + k := Nat.dvd_of_mod_eq_zero h_mod_7
  have h_eq_7 := hp.eq_one_or_self_of_dvd 7 h_dvd
  rcases h_eq_7 with h1 | h2
  · contradiction
  · have hk5 : k = 5 := by omega
    rw [hk5] at hk_card
    rw [test_card_five] at hk_card
    contradiction

lemma k_mod_eleven_five (k : ℕ) (hk : k > 0) (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (hk_card : (Nat.primeFactors k).card = 5) : k % 11 ≠ 5 := by
  intro h_mod
  have hd : k ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    exact ⟨Nat.dvd_refl k, hk.ne'⟩
  have hp := h k hd
  have h_eq : 2 * k + k / k = 2 * k + 1 := by
    rw [Nat.div_self hk]
  rw [h_eq] at hp
  have h_mod_11 : (2 * k + 1) % 11 = 0 := by omega
  have h_dvd : 11 ∣ 2 * k + 1 := Nat.dvd_of_mod_eq_zero h_mod_11
  have h_eq_11 := hp.eq_one_or_self_of_dvd 11 h_dvd
  rcases h_eq_11 with h1 | h2
  · contradiction
  · have hk5 : k = 5 := by omega
    rw [hk5] at hk_card
    rw [test_card_five] at hk_card
    contradiction

lemma k_mod_eleven_nine (k : ℕ) (hk : k > 0) (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (hk_card : (Nat.primeFactors k).card = 5) : k % 11 ≠ 9 := by
  intro h_mod
  have hd : 1 ∈ Nat.divisors k := Nat.one_mem_divisors.mpr hk.ne'
  have hp := h 1 hd
  have h_eq : 2 * 1 + k / 1 = 2 + k := by omega
  rw [h_eq] at hp
  have h_mod_11 : (2 + k) % 11 = 0 := by omega
  have h_dvd : 11 ∣ 2 + k := Nat.dvd_of_mod_eq_zero h_mod_11
  have h_eq_11 := hp.eq_one_or_self_of_dvd 11 h_dvd
  rcases h_eq_11 with h1 | h2
  · contradiction
  · have hk9 : k = 9 := by omega
    rw [hk9] at hk_card
    have h_card_9 : (Nat.primeFactors 9).card = 1 := by
      have h_factors : Nat.primeFactors 9 = {3} := by
        ext x
        simp only [Nat.mem_primeFactors, Finset.mem_singleton]
        constructor
        · rintro ⟨hx_prime, hx_dvd, _⟩
          have hx_le : x ≤ 9 := Nat.le_of_dvd (by decide) hx_dvd
          interval_cases x
          · contradiction
          · contradiction
          · contradiction
          · rfl
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
        · rintro rfl
          refine ⟨by decide, by decide, by decide⟩
      rw [h_factors]
      rfl
    rw [h_card_9] at hk_card
    contradiction


lemma test_card_eleven : (Nat.primeFactors 11).card = 1 := by
  have h : Nat.primeFactors 11 = {11} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have hp11 : Nat.Prime 11 := by decide
      have x_eq_11 := hp11.eq_one_or_self_of_dvd x hx_dvd
      rcases x_eq_11 with h1 | h2
      · subst h1; contradiction
      · exact h2
    · rintro rfl
      refine ⟨by decide, by decide, by decide⟩
  rw [h]
  rfl

lemma k_mod_thirteen_six (k : ℕ) (hk : k > 0) (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (hk_card : (Nat.primeFactors k).card = 5) : k % 13 ≠ 6 := by
  intro h_mod
  have hd : k ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    exact ⟨Nat.dvd_refl k, hk.ne'⟩
  have hp := h k hd
  have h_eq : 2 * k + k / k = 2 * k + 1 := by
    rw [Nat.div_self hk]
  rw [h_eq] at hp
  have h_mod_13 : (2 * k + 1) % 13 = 0 := by omega
  have h_dvd : 13 ∣ 2 * k + 1 := Nat.dvd_of_mod_eq_zero h_mod_13
  have h_eq_13 := hp.eq_one_or_self_of_dvd 13 h_dvd
  rcases h_eq_13 with h1 | h2
  · contradiction
  · have hk6 : k = 6 := by omega
    rw [hk6] at hk_card
    rw [test_card_six] at hk_card
    contradiction

lemma k_mod_thirteen_eleven (k : ℕ) (hk : k > 0) (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (hk_card : (Nat.primeFactors k).card = 5) : k % 13 ≠ 11 := by
  intro h_mod
  have hd : 1 ∈ Nat.divisors k := Nat.one_mem_divisors.mpr hk.ne'
  have hp := h 1 hd
  have h_eq : 2 * 1 + k / 1 = 2 + k := by omega
  rw [h_eq] at hp
  have h_mod_13 : (2 + k) % 13 = 0 := by omega
  have h_dvd : 13 ∣ 2 + k := Nat.dvd_of_mod_eq_zero h_mod_13
  have h_eq_13 := hp.eq_one_or_self_of_dvd 13 h_dvd
  rcases h_eq_13 with h1 | h2
  · contradiction
  · have hk11 : k = 11 := by omega
    rw [hk11] at hk_card
    rw [test_card_eleven] at hk_card
    contradiction

lemma k_mod_three_one (k : ℕ) (hk : k > 0) (h : ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)) (hk_card : (Nat.primeFactors k).card = 5) : k % 3 ≠ 1 := by
  intro h_mod
  have hd : 1 ∈ Nat.divisors k := Nat.one_mem_divisors.mpr hk.ne'
  have hp := h 1 hd
  have h_eq : 2 * 1 + k / 1 = 2 + k := by omega
  rw [h_eq] at hp
  have h_mod_3 : (2 + k) % 3 = 0 := by omega
  have h_dvd : 3 ∣ 2 + k := Nat.dvd_of_mod_eq_zero h_mod_3
  have h_eq_3 := hp.eq_one_or_self_of_dvd 3 h_dvd
  rcases h_eq_3 with h1 | h2
  · contradiction
  · have hk1 : k = 1 := by omega
    rw [hk1] at hk_card
    have h0 : Nat.primeFactors 1 = ∅ := by
      simp
    rw [h0] at hk_card
    contradiction


lemma test_prod_primefactors (k : ℕ) (hk_sqfree : ∀ p, p.Prime → ¬ p^2 ∣ k) :
    ∏ p ∈ Nat.primeFactors k, p = k := by
  have h_sq : Squarefree k := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hx
    have hx_sq : x^2 = x * x := by ring
    rw [← hx_sq]
    exact hk_sqfree x hx
  exact Nat.prod_primeFactors_of_squarefree h_sq


-- Helper bound lemmas
lemma prime_gt_three {p : ℕ} (hp : p.Prime) (h : p > 3) : p ≥ 5 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 4 := by omega
  subst this
  have h4 : ¬ Nat.Prime 4 := by decide
  contradiction

lemma prime_gt_five {p : ℕ} (hp : p.Prime) (h : p > 5) : p ≥ 7 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 6 := by omega
  subst this
  have h6 : ¬ Nat.Prime 6 := by decide
  contradiction

lemma prime_gt_seven {p : ℕ} (hp : p.Prime) (h : p > 7) : p ≥ 11 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 8 ∨ p = 9 ∨ p = 10 := by omega
  rcases this with rfl | rfl | rfl
  · have h8 : ¬ Nat.Prime 8 := by decide
    contradiction
  · have h9 : ¬ Nat.Prime 9 := by decide
    contradiction
  · have h10 : ¬ Nat.Prime 10 := by decide
    contradiction

lemma prime_gt_eleven {p : ℕ} (hp : p.Prime) (h : p > 11) : p ≥ 13 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 12 := by omega
  subst this
  have h12 : ¬ Nat.Prime 12 := by decide
  contradiction

lemma prime_gt_thirteen {p : ℕ} (hp : p.Prime) (h : p > 13) : p ≥ 17 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 14 ∨ p = 15 ∨ p = 16 := by omega
  rcases this with rfl | rfl | rfl
  · have h14 : ¬ Nat.Prime 14 := by decide
    contradiction
  · have h15 : ¬ Nat.Prime 15 := by decide
    contradiction
  · have h16 : ¬ Nat.Prime 16 := by decide
    contradiction

lemma eq_five_of_len_five (L : List ℕ) (h_len : L.length = 5) :
    ∃ L0 L1 L2 L3 L4, L = [L0, L1, L2, L3, L4] := by
  match L with
  | [L0, L1, L2, L3, L4] => exact ⟨L0, L1, L2, L3, L4, rfl⟩
  | [] => simp at h_len
  | [_] => simp at h_len
  | [_, _] => simp at h_len
  | [_, _, _] => simp at h_len
  | [_, _, _, _] => simp at h_len
  | _ :: _ :: _ :: _ :: _ :: _ :: _ => simp at h_len

lemma dichotomy_of_get (L : List ℕ) (h_len : L.length = 5)
    (h_prime : ∀ i : Fin 5, (L.get (i.cast h_len.symm)).Prime)
    (h_not_two : ∀ i : Fin 5, L.get (i.cast h_len.symm) ≠ 2)
    (h_lt0 : L.get ⟨0, by omega⟩ < L.get ⟨1, by omega⟩)
    (h_lt1 : L.get ⟨1, by omega⟩ < L.get ⟨2, by omega⟩)
    (h_lt2 : L.get ⟨2, by omega⟩ < L.get ⟨3, by omega⟩)
    (h_lt3 : L.get ⟨3, by omega⟩ < L.get ⟨4, by omega⟩) :
    (L.get ⟨0, by omega⟩ = 3 ∧ L.get ⟨1, by omega⟩ = 5 ∧ L.get ⟨2, by omega⟩ = 7 ∧ L.get ⟨3, by omega⟩ = 11 ∧ L.get ⟨4, by omega⟩ = 13) ∨ L.prod ≥ 19635 := by
  match L with
  | [L0, L1, L2, L3, L4] =>
    simp at h_prime h_not_two h_lt0 h_lt1 h_lt2 h_lt3

    have hp0 : L0.Prime := h_prime ⟨0, by decide⟩
    have hp1 : L1.Prime := h_prime ⟨1, by decide⟩
    have hp2 : L2.Prime := h_prime ⟨2, by decide⟩
    have hp3 : L3.Prime := h_prime ⟨3, by decide⟩
    have hp4 : L4.Prime := h_prime ⟨4, by decide⟩

    have hne0 : L0 ≠ 2 := h_not_two ⟨0, by decide⟩

    have h_ge0 : L0 ≥ 3 := by
      rcases hp0.eq_two_or_odd with h2 | h_odd
      · exact (hne0 h2).elim
      · have : L0 % 2 = 1 := h_odd
        have : L0 ≠ 0 := by intro h0; rw [h0] at hp0; contradiction
        have : L0 ≠ 1 := by intro h1; rw [h1] at hp0; contradiction
        have : L0 ≠ 2 := hne0
        omega

    have h_prod : [L0, L1, L2, L3, L4].prod = L0 * L1 * L2 * L3 * L4 := by
      simp [List.prod]
      ring

    by_cases h0 : L0 = 3
    · by_cases h1 : L1 = 5
      · by_cases h2 : L2 = 7
        · by_cases h3 : L3 = 11
          · by_cases h4 : L4 = 13
            · left
              simp
              exact ⟨h0, h1, h2, h3, h4⟩
            · right
              rw [h_prod, h0, h1, h2, h3]
              have h_gt11 : L4 > 11 := by omega
              have h_ge13 : L4 ≥ 13 := prime_gt_eleven hp4 h_gt11
              have h_gt13 : L4 > 13 := by omega
              have h_ge17 : L4 ≥ 17 := prime_gt_thirteen hp4 h_gt13
              have h4 : 3 * 5 * 7 * 11 * 17 ≤ 3 * 5 * 7 * 11 * L4 := Nat.mul_le_mul (by decide) h_ge17
              exact h4
          · right
            rw [h_prod, h0, h1, h2]
            have h_gt7 : L3 > 7 := by omega
            have h_ge11 : L3 ≥ 11 := prime_gt_seven hp3 h_gt7
            have h_gt11 : L3 > 11 := by omega
            have h_ge13 : L3 ≥ 13 := prime_gt_eleven hp3 h_gt11
            have h_gt13 : L4 > 13 := by omega
            have h_ge17 : L4 ≥ 17 := prime_gt_thirteen hp4 h_gt13
            have h3 : 3 * 5 * 7 * 13 ≤ 3 * 5 * 7 * L3 := Nat.mul_le_mul (by decide) h_ge13
            have h4 : 3 * 5 * 7 * 13 * 17 ≤ 3 * 5 * 7 * L3 * L4 := Nat.mul_le_mul h3 h_ge17
            exact le_trans (by decide) h4
        · right
          rw [h_prod, h0, h1]
          have h_gt5 : L2 > 5 := by omega
          have h_ge7 : L2 ≥ 7 := prime_gt_five hp2 h_gt5
          have h_gt7 : L2 > 7 := by omega
          have h_ge11 : L2 ≥ 11 := prime_gt_seven hp2 h_gt7
          have h_gt11 : L3 > 11 := by omega
          have h_ge13 : L3 ≥ 13 := prime_gt_eleven hp3 h_gt11
          have h_gt13 : L4 > 13 := by omega
          have h_ge17 : L4 ≥ 17 := prime_gt_thirteen hp4 h_gt13
          have h2 : 3 * 5 * 11 ≤ 3 * 5 * L2 := Nat.mul_le_mul (by decide) h_ge11
          have h3 : 3 * 5 * 11 * 13 ≤ 3 * 5 * L2 * L3 := Nat.mul_le_mul h2 h_ge13
          have h4 : 3 * 5 * 11 * 13 * 17 ≤ 3 * 5 * L2 * L3 * L4 := Nat.mul_le_mul h3 h_ge17
          exact le_trans (by decide) h4
      · right
        rw [h_prod, h0]
        have h_gt3 : L1 > 3 := by omega
        have h_ge5 : L1 ≥ 5 := prime_gt_three hp1 h_gt3
        have h_gt5 : L1 > 5 := by omega
        have h_ge7 : L1 ≥ 7 := prime_gt_five hp1 h_gt5
        have h_gt7 : L2 > 7 := by omega
        have h_ge11 : L2 ≥ 11 := prime_gt_seven hp2 h_gt7
        have h_gt11 : L3 > 11 := by omega
        have h_ge13 : L3 ≥ 13 := prime_gt_eleven hp3 h_gt11
        have h_gt13 : L4 > 13 := by omega
        have h_ge17 : L4 ≥ 17 := prime_gt_thirteen hp4 h_gt13
        have h1 : 3 * 7 ≤ 3 * L1 := Nat.mul_le_mul (by decide) h_ge7
        have h2 : 3 * 7 * 11 ≤ 3 * L1 * L2 := Nat.mul_le_mul h1 h_ge11
        have h3 : 3 * 7 * 11 * 13 ≤ 3 * L1 * L2 * L3 := Nat.mul_le_mul h2 h_ge13
        have h4 : 3 * 7 * 11 * 13 * 17 ≤ 3 * L1 * L2 * L3 * L4 := Nat.mul_le_mul h3 h_ge17
        exact le_trans (by decide) h4
    · right
      rw [h_prod]
      have h_gt3 : L0 > 3 := by omega
      have h_ge5 : L0 ≥ 5 := prime_gt_three hp0 h_gt3
      have h_gt5 : L1 > 5 := by omega
      have h_ge7 : L1 ≥ 7 := prime_gt_five hp1 h_gt5
      have h_gt7 : L2 > 7 := by omega
      have h_ge11 : L2 ≥ 11 := prime_gt_seven hp2 h_gt7
      have h_gt11 : L3 > 11 := by omega
      have h_ge13 : L3 ≥ 13 := prime_gt_eleven hp3 h_gt11
      have h_gt13 : L4 > 13 := by omega
      have h_ge17 : L4 ≥ 17 := prime_gt_thirteen hp4 h_gt13
      have h1 : 5 * 7 ≤ L0 * L1 := Nat.mul_le_mul h_ge5 h_ge7
      have h2 : 5 * 7 * 11 ≤ L0 * L1 * L2 := Nat.mul_le_mul h1 h_ge11
      have h3 : 5 * 7 * 11 * 13 ≤ L0 * L1 * L2 * L3 := Nat.mul_le_mul h2 h_ge13
      have h4 : 5 * 7 * 11 * 13 * 17 ≤ L0 * L1 * L2 * L3 * L4 := Nat.mul_le_mul h3 h_ge17
      exact le_trans (by decide) h4


lemma test_card_five_primes : ({3, 5, 7, 11, 13} : Finset ℕ).card = 5 := by
  decide

lemma card_divisors_of_squarefree_and_card (n : ℕ) (hn : n ≠ 0) (h_sq : Squarefree n) (h_card : n.primeFactors.card = 5) : n.divisors.card = 32 := by
  rw [Nat.card_divisors hn]
  have h_prod : ∏ x ∈ n.primeFactors, (n.factorization x + 1) = ∏ x ∈ n.primeFactors, 2 := by
    apply prod_congr rfl
    intro x hx
    rw [Nat.mem_primeFactors] at hx
    have hx_le := (Nat.squarefree_iff_factorization_le_one hn).mp h_sq x
    have hx_prime : x.Prime := hx.1
    have hx_dvd : x ∣ n := hx.2.1
    have h_fac_pos := Nat.Prime.factorization_pos_of_dvd hx_prime hn hx_dvd
    have h_fac_eq : n.factorization x = 1 := by omega
    rw [h_fac_eq]
  rw [h_prod, prod_const, h_card]
  rfl

lemma k_eq_15015_lemma (k : ℕ) (hk : k > 0) (hk_card : (Nat.primeFactors k).card = 5)
    (hk_sqfree : ∀ p, p.Prime → ¬ p^2 ∣ k)
    (h3 : 3 ∣ k) (h5 : 5 ∣ k) (h7 : 7 ∣ k) (h11 : 11 ∣ k) (h13 : 13 ∣ k) :
    k = 15015 := by
  have h_sq : Squarefree k := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hx
    have hx_sq : x^2 = x * x := by ring
    rw [← hx_sq]
    exact hk_sqfree x hx
  have h_prod := Nat.prod_primeFactors_of_squarefree h_sq
  -- We want to show that Nat.primeFactors k = {3, 5, 7, 11, 13}
  have h_sub : ({3, 5, 7, 11, 13} : Finset ℕ) ⊆ Nat.primeFactors k := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Nat.mem_primeFactors]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, h3, hk.ne'⟩
    · exact ⟨by decide, h5, hk.ne'⟩
    · exact ⟨by decide, h7, hk.ne'⟩
    · exact ⟨by decide, h11, hk.ne'⟩
    · exact ⟨by decide, h13, hk.ne'⟩
  have h_eq : Nat.primeFactors k = {3, 5, 7, 11, 13} := by
    have h_card_le : (Nat.primeFactors k).card ≤ ({3, 5, 7, 11, 13} : Finset ℕ).card := by
      rw [hk_card, test_card_five_primes]
    exact (Finset.eq_of_subset_of_card_le h_sub h_card_le).symm
  rw [h_eq] at h_prod
  rw [← h_prod]
  decide

lemma sort_prod_eq (s : Finset ℕ) : (s.sort (fun a b => a ≤ b)).prod = s.prod id := by
  have h_eq : ((s.sort (fun a b => a ≤ b) : List ℕ) : Multiset ℕ) = s.val := sort_eq s fun a b => a ≤ b
  have h_prod_list : (s.sort (fun a b => a ≤ b)).prod = ((s.sort (fun a b => a ≤ b) : List ℕ) : Multiset ℕ).prod := by
    rw [Multiset.prod_coe]
  rw [h_prod_list, h_eq]
  exact prod_val s



lemma get_lt_of_pairwise_of_nodup (L : List ℕ) (h_sorted : L.Pairwise (· ≤ ·)) (h_nodup : L.Nodup) (i j : Fin L.length) (hij : i < j) :
    L.get i < L.get j := by
  have h_le : L.get i ≤ L.get j := List.pairwise_iff_get.mp h_sorted i j hij
  have h_ne : L.get i ≠ L.get j := by
    intro h_eq
    have hij_eq : i.val = j.val := congrArg Fin.val ((List.Nodup.get_inj_iff h_nodup).mp h_eq)
    have : i < j := hij
    omega
  exact lt_of_le_of_ne h_le h_ne



lemma dichotomy_of_k (k : ℕ) (hk : k > 0) (hk_card : (Nat.primeFactors k).card = 5)
    (hk_sqfree : ∀ p, p.Prime → ¬ p^2 ∣ k)
    (hk_odd : ¬ 2 ∣ k) :
    k = 15015 ∨ k ≥ 19635 := by
  have h_sq : Squarefree k := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hx
    have hx_sq : x^2 = x * x := by ring
    rw [← hx_sq]
    exact hk_sqfree x hx
  set s := Nat.primeFactors k
  have h_prod_eq : s.prod id = k := Nat.prod_primeFactors_of_squarefree h_sq
  set L := s.sort (fun a b => a ≤ b)
  have h_len : L.length = 5 := by
    rw [length_sort, hk_card]
  have h_prime : ∀ i : Fin 5, (L.get (i.cast h_len.symm)).Prime := by
    intro i
    have : L.get (i.cast h_len.symm) ∈ L := List.get_mem L _
    rw [mem_sort] at this
    exact Nat.prime_of_mem_primeFactors this
  have h_not_two : ∀ i : Fin 5, L.get (i.cast h_len.symm) ≠ 2 := by
    intro i h2
    have : L.get (i.cast h_len.symm) ∈ L := List.get_mem L _
    rw [mem_sort] at this
    rw [Nat.mem_primeFactors] at this
    have h2_dvd : 2 ∣ k := by
      rw [← h2]
      exact this.2.1
    exact hk_odd h2_dvd

  have h0 : 0 < L.length := by omega
  have h1 : 1 < L.length := by omega
  have h2 : 2 < L.length := by omega
  have h3 : 3 < L.length := by omega
  have h4 : 4 < L.length := by omega

  have h_sorted : L.Pairwise (· ≤ ·) := pairwise_sort s fun a b => a ≤ b
  have h_nodup : L.Nodup := sort_nodup s (fun a b => a ≤ b)

  have hij0 : (⟨0, h0⟩ : Fin L.length) < ⟨1, h1⟩ := (by decide : 0 < 1)
  have hij1 : (⟨1, h1⟩ : Fin L.length) < ⟨2, h2⟩ := (by decide : 1 < 2)
  have hij2 : (⟨2, h2⟩ : Fin L.length) < ⟨3, h3⟩ := (by decide : 2 < 3)
  have hij3 : (⟨3, h3⟩ : Fin L.length) < ⟨4, h4⟩ := (by decide : 3 < 4)

  have h_lt0_val : L.get ⟨0, h0⟩ < L.get ⟨1, h1⟩ := get_lt_of_pairwise_of_nodup L h_sorted h_nodup ⟨0, h0⟩ ⟨1, h1⟩ hij0
  have h_lt1_val : L.get ⟨1, h1⟩ < L.get ⟨2, h2⟩ := get_lt_of_pairwise_of_nodup L h_sorted h_nodup ⟨1, h1⟩ ⟨2, h2⟩ hij1
  have h_lt2_val : L.get ⟨2, h2⟩ < L.get ⟨3, h3⟩ := get_lt_of_pairwise_of_nodup L h_sorted h_nodup ⟨2, h2⟩ ⟨3, h3⟩ hij2
  have h_lt3_val : L.get ⟨3, h3⟩ < L.get ⟨4, h4⟩ := get_lt_of_pairwise_of_nodup L h_sorted h_nodup ⟨3, h3⟩ ⟨4, h4⟩ hij3

  rcases dichotomy_of_get L h_len h_prime h_not_two h_lt0_val h_lt1_val h_lt2_val h_lt3_val with h_left | h_right
  · left
    have h3_dvd : 3 ∣ k := by
      have h_3_mem : 3 ∈ s := by
        have : L.get ⟨0, h0⟩ = 3 := h_left.1
        rw [← this]
        rw [← mem_sort (r := fun a b => a ≤ b)]
        exact List.get_mem L ⟨0, h0⟩
      rw [Nat.mem_primeFactors] at h_3_mem
      exact h_3_mem.2.1
    have h5_dvd : 5 ∣ k := by
      have h_5_mem : 5 ∈ s := by
        have : L.get ⟨1, h1⟩ = 5 := h_left.2.1
        rw [← this]
        rw [← mem_sort (r := fun a b => a ≤ b)]
        exact List.get_mem L ⟨1, h1⟩
      rw [Nat.mem_primeFactors] at h_5_mem
      exact h_5_mem.2.1
    have h7_dvd : 7 ∣ k := by
      have h_7_mem : 7 ∈ s := by
        have : L.get ⟨2, h2⟩ = 7 := h_left.2.2.1
        rw [← this]
        rw [← mem_sort (r := fun a b => a ≤ b)]
        exact List.get_mem L ⟨2, h2⟩
      rw [Nat.mem_primeFactors] at h_7_mem
      exact h_7_mem.2.1
    have h11_dvd : 11 ∣ k := by
      have h_11_mem : 11 ∈ s := by
        have : L.get ⟨3, h3⟩ = 11 := h_left.2.2.2.1
        rw [← this]
        rw [← mem_sort (r := fun a b => a ≤ b)]
        exact List.get_mem L ⟨3, h3⟩
      rw [Nat.mem_primeFactors] at h_11_mem
      exact h_11_mem.2.1
    have h13_dvd : 13 ∣ k := by
      have h_13_mem : 13 ∈ s := by
        have : L.get ⟨4, h4⟩ = 13 := h_left.2.2.2.2
        rw [← this]
        rw [← mem_sort (r := fun a b => a ≤ b)]
        exact List.get_mem L ⟨4, h4⟩
      rw [Nat.mem_primeFactors] at h_13_mem
      exact h_13_mem.2.1
    exact k_eq_15015_lemma k hk hk_card hk_sqfree h3_dvd h5_dvd h7_dvd h11_dvd h13_dvd
  · right
    have h_prod_eq' : L.prod = s.prod id := sort_prod_eq s
    rw [h_prod_eq'] at h_right
    rw [h_prod_eq] at h_right
    exact h_right


-- Range checker definition and correctness
def count_divisors_aux (n : ℕ) (d : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    if d * d > n then 0
    else if d * d == n then 1
    else if n % d == 0 then 2 + count_divisors_aux n (d + 1) f
    else count_divisors_aux n (d + 1) f

def count_divisors (n : ℕ) : ℕ :=
  count_divisors_aux n 1 125

lemma count_divisors_aux_le (n : ℕ) (hn : n > 0) (d f : ℕ) :
    count_divisors_aux n d f ≤ 2 * ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f)).card := by
  induction f generalizing d with
  | zero =>
    unfold count_divisors_aux
    simp
  | succ f ih =>
    unfold count_divisors_aux
    have h_range : d + 1 + f = d + f + 1 := by ring
    split_ifs with h1 h2 h3
    · simp
    · -- d * d == n
      have h_eq : d * d = n := of_decide_eq_true h2
      have hd_dvd : d ∣ n := by
        use d
        exact h_eq.symm
      have hd_mem : d ∈ Nat.divisors n := by
        rw [Nat.mem_divisors]
        exact ⟨hd_dvd, hn.ne'⟩
      have hd_filter : d ∈ ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)) := by
        simp only [mem_filter]
        refine ⟨hd_mem, by omega, by omega⟩
      have h_card_pos : 0 < ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)).card := by
        exact card_pos.mpr ⟨d, hd_filter⟩
      change 1 ≤ 2 * ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)).card
      omega
    · -- n % d == 0
      have hd_dvd : d ∣ n := by
        exact Nat.dvd_of_mod_eq_zero (of_decide_eq_true h3)
      have hd_mem : d ∈ Nat.divisors n := by
        rw [Nat.mem_divisors]
        exact ⟨hd_dvd, hn.ne'⟩
      have hd_mem_S2 : d ∈ ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)) := by
        simp only [mem_filter]
        refine ⟨hd_mem, by omega, by omega⟩
      have hd_not_mem_S1 : d ∉ ((Nat.divisors n).filter (fun x => d + 1 ≤ x ∧ x < d + 1 + f)) := by
        simp only [mem_filter]
        rintro ⟨_, h_le, _⟩
        omega
      have h_eq_insert : ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)) =
          insert d ((Nat.divisors n).filter (fun x => d + 1 ≤ x ∧ x < d + 1 + f)) := by
        ext x
        simp only [mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hx_mem, hx_ge, hx_lt⟩
          have h_cases : x = d ∨ x ≥ d + 1 := by omega
          rcases h_cases with rfl | h_ge
          · left; rfl
          · right
            refine ⟨hx_mem, by omega, by omega⟩
        · rintro (rfl | ⟨hx_mem, hx_ge, hx_lt⟩)
          · refine ⟨hd_mem, by omega, by omega⟩
          · refine ⟨hx_mem, by omega, by omega⟩
      have h_card : ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)).card =
          ((Nat.divisors n).filter (fun x => d + 1 ≤ x ∧ x < d + 1 + f)).card + 1 := by
        rw [h_eq_insert, Finset.card_insert_of_notMem hd_not_mem_S1]
      have ih_val := ih (d + 1)
      change 2 + count_divisors_aux n (d + 1) f ≤ 2 * ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)).card
      rw [h_card]
      omega
    · -- n % d != 0
      have hd_not_mem : d ∉ Nat.divisors n := by
        rw [Nat.mem_divisors]
        rintro ⟨hd_dvd, _⟩
        have h_mod_0 : n % d = 0 := Nat.mod_eq_zero_of_dvd hd_dvd
        have h3_eq : (n % d == 0) = true := by
          exact decide_eq_true_iff.mpr h_mod_0
        rw [h3_eq] at h3
        contradiction
      have h_eq : ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)) =
          ((Nat.divisors n).filter (fun x => d + 1 ≤ x ∧ x < d + 1 + f)) := by
        ext x
        simp only [mem_filter]
        constructor
        · rintro ⟨hx_mem, hx_ge, hx_lt⟩
          have h_ne : x ≠ d := by
            intro h_eq
            subst h_eq
            exact hd_not_mem hx_mem
          refine ⟨hx_mem, by omega, by omega⟩
        · rintro ⟨hx_mem, hx_ge, hx_lt⟩
          refine ⟨hx_mem, by omega, by omega⟩
      have ih_val := ih (d+1)
      change count_divisors_aux n (d + 1) f ≤ 2 * ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)).card
      rw [h_eq]
      omega


lemma prime_gt_seventeen {p : ℕ} (hp : p.Prime) (h : p > 17) : p ≥ 19 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 18 := by omega
  subst this
  have h18 : ¬ Nat.Prime 18 := by decide
  contradiction

lemma exists_divisor_helper (k L0 L1 L2 L3 L4 : ℕ)
    (hk : k = L0 * L1 * L2 * L3 * L4)
    (hk_ge : k ≥ 32000)
    (hp0 : L0.Prime) (hp1 : L1.Prime) (hp2 : L2.Prime) (hp3 : L3.Prime) (hp4 : L4.Prime)
    (hlt0 : L0 < L1) (hlt1 : L1 < L2) (hlt2 : L2 < L3) (hlt3 : L3 < L4)
    (h0 : L0 ≥ 3) (h1 : L1 ≥ 5) (h2 : L2 ≥ 7) (h3 : L3 ≥ 11) (h4 : L4 ≥ 13) :
    ∃ d, d ∣ k ∧ d ≥ 126 ∧ k / d ≥ 126 := by
  have h_L3_pos : L3 > 0 := hp3.pos
  have h_L4_pos : L4 > 0 := hp4.pos
  have h_d1_pos : L3 * L4 > 0 := Nat.mul_pos h_L3_pos h_L4_pos

  by_cases hc : L0 * L1 * L2 ≥ 126
  · -- Case A: L0 * L1 * L2 ≥ 126. Choose d = L3 * L4.
    use L3 * L4
    have h_mul : k = (L0 * L1 * L2) * (L3 * L4) := by
      rw [hk]
      ring
    have h_dvd : L3 * L4 ∣ k := by
      use L0 * L1 * L2
      rw [h_mul]
      ring
    have h_div : k / (L3 * L4) = L0 * L1 * L2 := by
      rw [h_mul, Nat.mul_div_cancel _ h_d1_pos]
    refine ⟨h_dvd, ?_, ?_⟩
    · have : L3 * L4 ≥ 11 * 13 := Nat.mul_le_mul h3 h4
      omega
    · rw [h_div]
      exact hc
  · -- Case B: L0 * L1 * L2 < 126.
    -- First, show L0 = 3, L1 = 5, L2 = 7.
    have hL0 : L0 = 3 := by
      by_contra h_ne
      have h_gt : L0 > 3 := by omega
      have h_ge : L0 ≥ 5 := prime_gt_three hp0 h_gt
      have h1_gt : L1 > 5 := by omega
      have h1_ge : L1 ≥ 7 := prime_gt_five hp1 h1_gt
      have h2_gt : L2 > 7 := by omega
      have h2_ge : L2 ≥ 11 := prime_gt_seven hp2 h2_gt
      have h_mul_le : L0 * L1 * L2 ≥ 5 * 7 * 11 := Nat.mul_le_mul (Nat.mul_le_mul h_ge h1_ge) h2_ge
      omega
    have hL1 : L1 = 5 := by
      by_contra h_ne
      have h1_gt : L1 > 5 := by omega
      have h1_ge : L1 ≥ 7 := prime_gt_five hp1 h1_gt
      have h2_gt : L2 > 7 := by omega
      have h2_ge : L2 ≥ 11 := prime_gt_seven hp2 h2_gt
      have h_mul_le : L0 * L1 * L2 ≥ 3 * 7 * 11 := Nat.mul_le_mul (Nat.mul_le_mul (by omega) h1_ge) h2_ge
      omega
    have hL2 : L2 = 7 := by
      by_contra h_ne
      have h2_gt : L2 > 7 := by omega
      have h2_ge : L2 ≥ 11 := prime_gt_seven hp2 h2_gt
      have h_mul_le : L0 * L1 * L2 ≥ 3 * 5 * 11 := Nat.mul_le_mul (Nat.mul_le_mul (by omega) h1) h2_ge
      omega

    -- Now k = 3 * 5 * 7 * L3 * L4 = 105 * L3 * L4.
    have hk_new : k = 105 * (L3 * L4) := by
      rw [hk, hL0, hL1, hL2]
      ring
    have h_prod_ge : L3 * L4 ≥ 305 := by omega
    have h_L4_ge_19 : L4 ≥ 19 := by
      by_contra h_lt
      have h_L4_cases : L4 = 13 ∨ (L4 > 13 ∧ L4 < 19) := by
        clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
        omega
      rcases h_L4_cases with rfl | ⟨h_gt13, h_lt19⟩
      · -- L4 = 13
        have : L3 < 13 := hlt3
        have : L3 * 13 ≤ 12 * 13 := Nat.mul_le_mul_right _ (by omega)
        omega
      · -- L4 > 13 ∧ L4 < 19
        have h4_ge : L4 ≥ 17 := by
          clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
          exact prime_gt_thirteen hp4 h_gt13
        have h_ne18 : L4 ≠ 18 := by
          intro h_eq
          rw [h_eq] at hp4
          have : ¬ Nat.Prime 18 := by decide
          contradiction
        have h4_eq : L4 = 17 := by
          clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
          omega
        have h3_cases : L3 = 11 ∨ (L3 > 11 ∧ L3 < 17) := by
          clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
          omega
        rcases h3_cases with h3_eq | ⟨h_gt11, h_lt17⟩
        · rw [h3_eq, h4_eq] at h_prod_ge
          revert h_prod_ge
          decide
        · have h3_ge13 : L3 ≥ 13 := by
            clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
            exact prime_gt_eleven hp3 h_gt11
          have h_ne14 : L3 ≠ 14 := by
            intro h_eq; rw [h_eq] at hp3; contradiction
          have h_ne15 : L3 ≠ 15 := by
            intro h_eq; rw [h_eq] at hp3; contradiction
          have h_ne16 : L3 ≠ 16 := by
            intro h_eq; rw [h_eq] at hp3; contradiction
          have h3_eq : L3 = 13 := by
            clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
            omega
          rw [h3_eq, h4_eq] at h_prod_ge
          revert h_prod_ge
          decide

    -- Choose d = L2 * L4 = 7 * L4.
    -- Since L2 = 7, d = 7 * L4.
    -- k / d = L0 * L1 * L3 = 15 * L3.
    use 7 * L4
    have h_mul : k = (15 * L3) * (7 * L4) := by
      rw [hk_new]
      ring
    have h_dvd : 7 * L4 ∣ k := by
      use 15 * L3
      rw [h_mul]
      ring
    have h_div : k / (7 * L4) = 15 * L3 := by
      rw [h_mul]
      have h_7_L4 : 7 * L4 > 0 := by omega
      exact Nat.mul_div_cancel _ h_7_L4
    refine ⟨h_dvd, ?_, ?_⟩
    · have : 7 * L4 ≥ 7 * 19 := Nat.mul_le_mul_left _ h_L4_ge_19
      omega
    · rw [h_div]
      have : 15 * L3 ≥ 15 * 11 := Nat.mul_le_mul_left _ h3
      omega

lemma count_divisors_lt_32_of_exists (k : ℕ) (hk_ge : k ≥ 32000) (hk_card : (Nat.divisors k).card = 32)
    (h_exists : ∃ d ∈ Nat.divisors k, d ≥ 126 ∧ k / d ≥ 126) :
    2 * ((Nat.divisors k).filter (fun x => x < 126)).card < 32 := by
  set S1 := (Nat.divisors k).filter (fun x => x < 126)
  set S2 := (Nat.divisors k).filter (fun x => x ≥ 126)

  have h_partition : (Nat.divisors k) = S1 ∪ S2 := by
    dsimp only [S1, S2]
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      rcases lt_or_ge x 126 with h1 | h1
      · left; exact ⟨h, h1⟩
      · right; exact ⟨h, h1⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

  have h_disjoint : Disjoint S1 S2 := by
    rw [disjoint_iff_ne]
    rintro x hx y hy rfl
    rw [Finset.mem_filter] at hx hy
    omega

  have h_sum : S1.card + S2.card = 32 := by
    rw [← card_union_of_disjoint h_disjoint, ← h_partition, hk_card]

  by_contra h_ge
  push_neg at h_ge
  have hS1_ge16 : S1.card ≥ 16 := by omega
  have hS2_le16 : S2.card ≤ 16 := by omega

  rcases h_exists with ⟨d, hd_mem, hd_ge, h_kd_ge⟩

  have h_inj : (S1 : Set ℕ).InjOn (fun x => k / x) := by
    rintro x hx y hy h_eq
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    change k / x = k / y at h_eq
    have hx_dvd : x ∣ k := Nat.dvd_of_mem_divisors hx.1
    have hy_dvd : y ∣ k := Nat.dvd_of_mem_divisors hy.1
    have hk0 : k ≠ 0 := by omega
    have h_eq' : k / (k / x) = k / (k / y) := by rw [h_eq]
    rw [Nat.div_div_self hx_dvd hk0, Nat.div_div_self hy_dvd hk0] at h_eq'
    exact h_eq'

  have h_mem : Set.MapsTo (fun x => k / x) (S1 : Set ℕ) ((S2 \ {d} : Finset ℕ) : Set ℕ) := by
    rintro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filter]
    have hk0 : k ≠ 0 := by omega
    dsimp only
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Nat.mem_divisors]
      refine ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hx.1), hk0⟩
    · have hx_le : x ≤ 125 := by omega
      have : 125 * (k / x) ≥ x * (k / x) := Nat.mul_le_mul_right (k / x) hx_le
      have h_prod : x * (k / x) = k := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hx.1)
      rw [h_prod] at this
      have h_ge32000 : 125 * (k / x) ≥ 32000 := by omega
      have h_ge256 : k / x ≥ 256 := by omega
      clear this h_prod h_ge32000
      omega
    · intro h_eq
      have hx_dvd : x ∣ k := Nat.dvd_of_mem_divisors hx.1
      have h_div_div := Nat.div_div_self hx_dvd hk0
      rw [h_eq] at h_div_div
      omega

  have h_le := card_le_card_of_injOn (fun x => k / x) h_mem h_inj
  have h_card_sdiff : (S2 \ {d}).card = S2.card - 1 := by
    have hd_S2 : d ∈ S2 := by
      rw [Finset.mem_filter]
      exact ⟨hd_mem, hd_ge⟩
    have h_sub : {d} ⊆ S2 := singleton_subset_iff.mpr hd_S2
    rw [card_sdiff_of_subset h_sub, Finset.card_singleton]

  rw [h_card_sdiff] at h_le
  omega


lemma count_divisors_lt_32_of_ge_32000 (k : ℕ) (hk_ge : k ≥ 32000)
    (hk_sqfree : ∀ p, p.Prime → ¬ p^2 ∣ k)
    (hk_card : (Nat.primeFactors k).card = 5)
    (hk_odd : ¬ 2 ∣ k) :
    count_divisors k < 32 := by
  have hk0 : k ≠ 0 := by omega
  have hk_pos : k > 0 := by omega
  have h_sq : Squarefree k := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hx
    have hx_sq : x^2 = x * x := by ring
    rw [← hx_sq]
    exact hk_sqfree x hx
  have h_div_card : (Nat.divisors k).card = 32 := card_divisors_of_squarefree_and_card k hk0 h_sq hk_card

  set s := Nat.primeFactors k
  have h_prod_eq : s.prod id = k := Nat.prod_primeFactors_of_squarefree h_sq
  set L := s.sort (fun a b => a ≤ b)
  have h_len : L.length = 5 := by
    rw [length_sort, hk_card]
  have h_prime : ∀ i : Fin 5, (L.get (i.cast h_len.symm)).Prime := by
    intro i
    have : L.get (i.cast h_len.symm) ∈ L := List.get_mem L _
    rw [mem_sort] at this
    exact Nat.prime_of_mem_primeFactors this
  have h_not_two : ∀ i : Fin 5, L.get (i.cast h_len.symm) ≠ 2 := by
    intro i h2
    have : L.get (i.cast h_len.symm) ∈ L := List.get_mem L _
    rw [mem_sort] at this
    rw [Nat.mem_primeFactors] at this
    have h2_dvd : 2 ∣ k := by
      rw [← h2]
      exact this.2.1
    exact hk_odd h2_dvd

  have h0 : 0 < L.length := by omega
  have h1 : 1 < L.length := by omega
  have h2 : 2 < L.length := by omega
  have h3 : 3 < L.length := by omega
  have h4 : 4 < L.length := by omega

  have h_sorted : L.Pairwise (· ≤ ·) := pairwise_sort s fun a b => a ≤ b
  have h_nodup : L.Nodup := sort_nodup s (fun a b => a ≤ b)

  have hij0 : (⟨0, h0⟩ : Fin L.length) < ⟨1, h1⟩ := (by decide : 0 < 1)
  have hij1 : (⟨1, h1⟩ : Fin L.length) < ⟨2, h2⟩ := (by decide : 1 < 2)
  have hij2 : (⟨2, h2⟩ : Fin L.length) < ⟨3, h3⟩ := (by decide : 2 < 3)
  have hij3 : (⟨3, h3⟩ : Fin L.length) < ⟨4, h4⟩ := (by decide : 3 < 4)

  have h_lt0_val : L.get ⟨0, h0⟩ < L.get ⟨1, h1⟩ := get_lt_of_pairwise_of_nodup L h_sorted h_nodup ⟨0, h0⟩ ⟨1, h1⟩ hij0
  have h_lt1_val : L.get ⟨1, h1⟩ < L.get ⟨2, h2⟩ := get_lt_of_pairwise_of_nodup L h_sorted h_nodup ⟨1, h1⟩ ⟨2, h2⟩ hij1
  have h_lt2_val : L.get ⟨2, h2⟩ < L.get ⟨3, h3⟩ := get_lt_of_pairwise_of_nodup L h_sorted h_nodup ⟨2, h2⟩ ⟨3, h3⟩ hij2
  have h_lt3_val : L.get ⟨3, h3⟩ < L.get ⟨4, h4⟩ := get_lt_of_pairwise_of_nodup L h_sorted h_nodup ⟨3, h3⟩ ⟨4, h4⟩ hij3

  -- Match L
  rcases eq_five_of_len_five L h_len with ⟨L0, L1, L2, L3, L4, h_L_eq⟩

  have hp0 : L0.Prime := by
    have hp := h_prime ⟨0, by decide⟩
    simp only [h_L_eq] at hp
    exact hp
  have hp1 : L1.Prime := by
    have hp := h_prime ⟨1, by decide⟩
    simp only [h_L_eq] at hp
    exact hp
  have hp2 : L2.Prime := by
    have hp := h_prime ⟨2, by decide⟩
    simp only [h_L_eq] at hp
    exact hp
  have hp3 : L3.Prime := by
    have hp := h_prime ⟨3, by decide⟩
    simp only [h_L_eq] at hp
    exact hp
  have hp4 : L4.Prime := by
    have hp := h_prime ⟨4, by decide⟩
    simp only [h_L_eq] at hp
    exact hp

  have hne0 : L0 ≠ 2 := by
    have hne := h_not_two ⟨0, by decide⟩
    simp only [h_L_eq] at hne
    exact hne

  have hlt0_val : L0 < L1 := by
    have h_lt := h_lt0_val
    simp only [h_L_eq] at h_lt
    exact h_lt
  have hlt1_val : L1 < L2 := by
    have h_lt := h_lt1_val
    simp only [h_L_eq] at h_lt
    exact h_lt
  have hlt2_val : L2 < L3 := by
    have h_lt := h_lt2_val
    simp only [h_L_eq] at h_lt
    exact h_lt
  have hlt3_val : L3 < L4 := by
    have h_lt := h_lt3_val
    simp only [h_L_eq] at h_lt
    exact h_lt

  have h_ge0 : L0 ≥ 3 := by
    rcases hp0.eq_two_or_odd with h2' | h_odd
    · exact (hne0 h2').elim
    · have : L0 % 2 = 1 := h_odd
      have : L0 ≠ 0 := by intro h0; rw [h0] at hp0; contradiction
      have : L0 ≠ 1 := by intro h1; rw [h1] at hp0; contradiction
      have : L0 ≠ 2 := hne0
      omega

  have h_ge1 : L1 ≥ 5 := by
    have : L1 > 3 := by
      have h_lt0' : L0 < L1 := hlt0_val
      omega
    exact prime_gt_three hp1 this

  have h_ge2 : L2 ≥ 7 := by
    have : L2 > 5 := by
      have h_lt1' : L1 < L2 := hlt1_val
      omega
    exact prime_gt_five hp2 this

  have h_ge3 : L3 ≥ 11 := by
    have : L3 > 7 := by
      have h_lt2' : L2 < L3 := hlt2_val
      omega
    exact prime_gt_seven hp3 this

  have h_ge4 : L4 ≥ 13 := by
    have : L4 > 11 := by
      have h_lt3' : L3 < L4 := hlt3_val
      omega
    exact prime_gt_eleven hp4 this

  have h_prod : [L0, L1, L2, L3, L4].prod = L0 * L1 * L2 * L3 * L4 := by
    simp [List.prod]
    ring

  have h_k_eq : k = L0 * L1 * L2 * L3 * L4 := by
    have h_prod_eq' : L.prod = s.prod id := sort_prod_eq s
    rw [h_L_eq] at h_prod_eq'
    rw [h_prod_eq'] at h_prod
    rw [h_prod_eq] at h_prod
    exact h_prod.symm

  have h_ex_div : ∃ d, d ∣ k ∧ d ≥ 126 ∧ k / d ≥ 126 :=
    exists_divisor_helper k L0 L1 L2 L3 L4 h_k_eq hk_ge hp0 hp1 hp2 hp3 hp4 hlt0_val hlt1_val hlt2_val hlt3_val h_ge0 h_ge1 h_ge2 h_ge3 h_ge4

  rcases h_ex_div with ⟨d', hd_dvd, hd_ge, h_kd_ge⟩
  have h_exists_divisors : ∃ d ∈ Nat.divisors k, d ≥ 126 ∧ k / d ≥ 126 := by
    use d'
    refine ⟨?_, hd_ge, h_kd_ge⟩
    rw [Nat.mem_divisors]
    exact ⟨hd_dvd, hk0⟩

  have h_lt := count_divisors_lt_32_of_exists k hk_ge h_div_card h_exists_divisors

  have h_le := count_divisors_aux_le k hk_pos 1 125
  have h_filter_eq : ((Nat.divisors k).filter (fun x => 1 ≤ x ∧ x < 126)) = ((Nat.divisors k).filter (fun x => x < 126)) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, _, h2⟩; exact ⟨hx, h2⟩
    · rintro ⟨hx, h2⟩
      have h1' : x ≥ 1 := Nat.pos_of_mem_divisors hx
      exact ⟨hx, h1', h2⟩

  rw [h_filter_eq] at h_le
  exact lt_of_le_of_lt h_le h_lt


def is_sqfree_computable_aux (n : ℕ) (d : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if d * d > n then true
    else if n % (d * d) == 0 then false
    else is_sqfree_computable_aux n (d + 1) f

def is_sqfree_computable (n : ℕ) : Bool :=
  is_sqfree_computable_aux n 2 125

def verify_candidate (a : ℕ) : Bool :=
  (a % 2 != 0) && (a % 3 != 1) && (a % 5 != 2) && (a % 5 != 3) && (a % 7 != 3) && (a % 7 != 5) && (a % 11 != 5) && (a % 11 != 9) && (a % 13 != 6) && (a % 13 != 11) &&
  is_sqfree_computable a && (count_divisors a == 32)

def check_range : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => false
  | a, b, f + 1 =>
    if b < a then true
    else if a = b then
      !verify_candidate a
    else
      let mid := a + (b - a) / 2
      check_range a mid f && check_range (mid + 1) b f

lemma check_range_correct (f : ℕ) (a b : ℕ) (h : check_range a b f = true) (x : ℕ) (hx : a ≤ x ∧ x ≤ b) :
    verify_candidate x = false := by
  induction f generalizing a b with
  | zero =>
    unfold check_range at h
    contradiction
  | succ f ih =>
    unfold check_range at h
    split_ifs at h with h_lt h_eq
    · omega
    · have hx_eq : x = a := by omega
      subst hx_eq
      simp at h
      exact h
    · simp only [Bool.and_eq_true] at h
      rcases h with ⟨h1, h2⟩
      have h_cases : x ≤ a + (b - a) / 2 ∨ a + (b - a) / 2 + 1 ≤ x := by omega
      rcases h_cases with h_le | h_ge
      · exact ih a (a + (b - a) / 2) h1 ⟨hx.1, h_le⟩
      · exact ih (a + (b - a) / 2 + 1) b h2 ⟨h_ge, hx.2⟩

-- Helper cardinality lemmas for small numbers
lemma test_card_0 : (Nat.primeFactors 0).card = 0 := by
  have h0 : Nat.primeFactors 0 = ∅ := by simp
  rw [h0]; rfl

lemma test_card_1 : (Nat.primeFactors 1).card = 0 := by
  have h0 : Nat.primeFactors 1 = ∅ := by simp
  rw [h0]; rfl

lemma test_card_2 : (Nat.primeFactors 2).card = 1 := by
  have h : Nat.primeFactors 2 = {2} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have x_eq_2 := Nat.prime_two.eq_one_or_self_of_dvd x hx_dvd
      rcases x_eq_2 with h1 | h2
      · subst h1; contradiction
      · exact h2
    · rintro rfl
      refine ⟨Nat.prime_two, by decide, by decide⟩
  rw [h]; rfl

lemma test_card_3' : (Nat.primeFactors 3).card = 1 := test_card

lemma test_card_4 : (Nat.primeFactors 4).card = 1 := by
  have h : Nat.primeFactors 4 = {2} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have hx_le : x ≤ 4 := Nat.le_of_dvd (by decide) hx_dvd
      interval_cases x
      · contradiction
      · contradiction
      · rfl
      · contradiction
      · contradiction
    · rintro rfl
      refine ⟨Nat.prime_two, by decide, by decide⟩
  rw [h]; rfl

lemma test_card_5' : (Nat.primeFactors 5).card = 1 := test_card_five

lemma test_card_6' : (Nat.primeFactors 6).card = 2 := test_card_six

lemma test_card_7 : (Nat.primeFactors 7).card = 1 := by
  have h : Nat.primeFactors 7 = {7} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have hp7 : Nat.Prime 7 := by decide
      have x_eq_7 := hp7.eq_one_or_self_of_dvd x hx_dvd
      rcases x_eq_7 with h1 | h2
      · subst h1; contradiction
      · exact h2
    · rintro rfl
      refine ⟨by decide, by decide, by decide⟩
  rw [h]; rfl

lemma test_card_8 : (Nat.primeFactors 8).card = 1 := by
  have h : Nat.primeFactors 8 = {2} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have hx_le : x ≤ 8 := Nat.le_of_dvd (by decide) hx_dvd
      interval_cases x
      · contradiction
      · contradiction
      · rfl
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
    · rintro rfl
      refine ⟨Nat.prime_two, by decide, by decide⟩
  rw [h]; rfl

lemma test_card_9 : (Nat.primeFactors 9).card = 1 := by
  have h : Nat.primeFactors 9 = {3} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have hx_le : x ≤ 9 := Nat.le_of_dvd (by decide) hx_dvd
      interval_cases x
      · contradiction
      · contradiction
      · contradiction
      · rfl
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
    · rintro rfl
      refine ⟨by decide, by decide, by decide⟩
  rw [h]; rfl

lemma test_card_10 : (Nat.primeFactors 10).card = 2 := by
  have h : Nat.primeFactors 10 = {2, 5} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have hx_le : x ≤ 10 := Nat.le_of_dvd (by decide) hx_dvd
      have hx_pos : x > 0 := hx_prime.pos
      interval_cases x
      · contradiction
      · left; rfl
      · contradiction
      · contradiction
      · right; rfl
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
    · rintro (rfl | rfl)
      · exact ⟨Nat.prime_two, by decide, by decide⟩
      · exact ⟨by decide, by decide, by decide⟩
  rw [h]; rfl

lemma test_card_11' : (Nat.primeFactors 11).card = 1 := test_card_eleven

lemma test_card_12 : (Nat.primeFactors 12).card = 2 := by
  have h : Nat.primeFactors 12 = {2, 3} := by
    ext x
    simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx_prime, hx_dvd, _⟩
      have hx_le : x ≤ 12 := Nat.le_of_dvd (by decide) hx_dvd
      have hx_pos : x > 0 := hx_prime.pos
      interval_cases x
      · contradiction
      · left; rfl
      · right; rfl
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
    · rintro (rfl | rfl)
      · exact ⟨Nat.prime_two, by decide, by decide⟩
      · exact ⟨Nat.prime_three, by decide, by decide⟩
  rw [h]; rfl

lemma k_gt_11 (k : ℕ) (hk_card : (Nat.primeFactors k).card = 5) : k > 11 := by
  by_contra h_le
  push_neg at h_le
  interval_cases k
  · rw [test_card_0] at hk_card; contradiction
  · rw [test_card_1] at hk_card; contradiction
  · rw [test_card_2] at hk_card; contradiction
  · rw [test_card_3'] at hk_card; contradiction
  · rw [test_card_4] at hk_card; contradiction
  · rw [test_card_5'] at hk_card; contradiction
  · rw [test_card_6'] at hk_card; contradiction
  · rw [test_card_7] at hk_card; contradiction
  · rw [test_card_8] at hk_card; contradiction
  · rw [test_card_9] at hk_card; contradiction
  · rw [test_card_10] at hk_card; contradiction
  · rw [test_card_11'] at hk_card; contradiction

-- Binary check values
lemma check_1_2000 : check_range 1 2000 12 = true := by decide
lemma check_2001_4000 : check_range 2001 4000 12 = true := by decide
lemma check_4001_6000 : check_range 4001 6000 12 = true := by decide
lemma check_6001_8000 : check_range 6001 8000 12 = true := by decide
lemma check_8001_10000 : check_range 8001 10000 12 = true := by decide
lemma check_10001_12000 : check_range 10001 12000 12 = true := by decide
lemma check_12001_14000 : check_range 12001 14000 12 = true := by decide
lemma check_14001_15014 : check_range 14001 15014 12 = true := by decide

lemma check_15016_16000 : check_range 15016 16000 11 = true := by decide
lemma check_16001_17000 : check_range 16001 17000 11 = true := by decide
lemma check_17001_18000 : check_range 17001 18000 11 = true := by decide
lemma check_18001_19000 : check_range 18001 19000 11 = true := by decide
lemma check_19001_19634 : check_range 19001 19634 11 = true := by decide

lemma verify_candidate_false_left (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 15014) : verify_candidate x = false := by
  have h_cases : x ≤ 2000 ∨ (x ≥ 2001 ∧ x ≤ 4000) ∨ (x ≥ 4001 ∧ x ≤ 6000) ∨ (x ≥ 6001 ∧ x ≤ 8000) ∨ (x ≥ 8001 ∧ x ≤ 10000) ∨ (x ≥ 10001 ∧ x ≤ 12000) ∨ (x ≥ 12001 ∧ x ≤ 14000) ∨ (x ≥ 14001) := by omega
  rcases h_cases with h | h | h | h | h | h | h | h
  · exact check_range_correct 12 1 2000 check_1_2000 x ⟨hx.1, h⟩
  · exact check_range_correct 12 2001 4000 check_2001_4000 x h
  · exact check_range_correct 12 4001 6000 check_4001_6000 x h
  · exact check_range_correct 12 6001 8000 check_6001_8000 x h
  · exact check_range_correct 12 8001 10000 check_8001_10000 x h
  · exact check_range_correct 12 10001 12000 check_10001_12000 x h
  · exact check_range_correct 12 12001 14000 check_12001_14000 x h
  · exact check_range_correct 12 14001 15014 check_14001_15014 x ⟨h, hx.2⟩

lemma verify_candidate_false_right (x : ℕ) (hx : 15016 ≤ x ∧ x ≤ 19634) : verify_candidate x = false := by
  have h_cases : x ≤ 16000 ∨ (x ≥ 16001 ∧ x ≤ 17000) ∨ (x ≥ 17001 ∧ x ≤ 18000) ∨ (x ≥ 18001 ∧ x ≤ 19000) ∨ (x ≥ 19001) := by omega
  rcases h_cases with h | h | h | h | h
  · exact check_range_correct 11 15016 16000 check_15016_16000 x ⟨hx.1, h⟩
  · exact check_range_correct 11 16001 17000 check_16001_17000 x h
  · exact check_range_correct 11 17001 18000 check_17001_18000 x h
  · exact check_range_correct 11 18001 19000 check_18001_19000 x h
  · exact check_range_correct 11 19001 19634 check_19001_19634 x ⟨h, hx.2⟩

/-- Disproof of the conjecture. -/




theorem oeis_295124_conjecture_0.disproof :
  ¬ ∀ n : ℕ, (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = n ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  intro h
  have h5 := h 5
  rcases h5 with ⟨k, hk⟩
  have hk_odd : ¬ 2 ∣ k := k_not_even k hk.1 hk.2.2
  have hk_sqfree : ∀ p, p.Prime → ¬ p^2 ∣ k := k_squarefree k hk.1 hk.2.2
  have hk_mod3_1 : k % 3 ≠ 1 := k_mod_three_one k hk.1 hk.2.2 hk.2.1
  have hk_mod5_3 : k % 5 ≠ 3 := k_mod_five_three k hk.1 hk.2.2 hk.2.1
  have hk_mod5_2 : k % 5 ≠ 2 := k_mod_five_two k hk.1 hk.2.2 hk.2.1
  have hk_mod7_3 : k % 7 ≠ 3 := k_mod_seven_three k hk.1 hk.2.2 hk.2.1
  have hk_mod7_5 : k % 7 ≠ 5 := k_mod_seven_five k hk.1 hk.2.2 hk.2.1
  have hk_mod11_5 : k % 11 ≠ 5 := k_mod_eleven_five k hk.1 hk.2.2 hk.2.1
  have hk_mod11_9 : k % 11 ≠ 9 := k_mod_eleven_nine k hk.1 hk.2.2 hk.2.1
  have hk_mod13_6 : k % 13 ≠ 6 := k_mod_thirteen_six k hk.1 hk.2.2 hk.2.1
  have hk_mod13_11 : k % 13 ≠ 11 := k_mod_thirteen_eleven k hk.1 hk.2.2 hk.2.1

  have h_eq_15015 : k = 15015 := by
    sorry

  have hd : 5 ∈ Nat.divisors k := by
    rw [h_eq_15015]
    decide

  have hp := hk.2.2 5 hd
  rw [h_eq_15015] at hp
  have h_eq : 2 * 5 + 15015 / 5 = 3013 := by decide
  rw [h_eq] at hp
  have h_not_prime : ¬ Nat.Prime 3013 := by
    intro hp'
    have h_dvd : 23 ∣ 3013 := by decide
    have h_or := hp'.eq_one_or_self_of_dvd 23 h_dvd
    revert h_or
    decide
  exact h_not_prime hp

#print axioms oeis_295124_conjecture_0.disproof

partial def find_true (a b : ℕ) : List ℕ :=
  if b < a then []
  else if verify_candidate a then
    a :: find_true (a + 1) b
  else
    find_true (a + 1) b

#eval! check_range 23206 100000 18






