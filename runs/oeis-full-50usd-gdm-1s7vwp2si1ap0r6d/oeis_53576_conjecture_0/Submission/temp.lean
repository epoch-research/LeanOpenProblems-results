import Mathlib

open Nat

lemma dvd_pow_odd (A : ℕ) (hA : A ≥ 1) (k : ℕ) : A + 1 ∣ A ^ (2 * k + 1) + 1 := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h_eq : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by omega
    rw [h_eq, pow_add, pow_two]
    have h_sq : A * A = (A + 1) * (A - 1) + 1 := by
      rcases A with _ | B
      · omega
      · simp
        ring
    rw [h_sq]
    have h_expand : A ^ (2 * k + 1) * ((A + 1) * (A - 1) + 1) + 1 =
        (A + 1) * ((A - 1) * A ^ (2 * k + 1)) + (A ^ (2 * k + 1) + 1) := by
      ring
    rw [h_expand]
    apply dvd_add
    · exact dvd_mul_of_dvd_left (dvd_refl (A + 1)) _
    · exact ih

lemma eq_pow_two_of_dvd_pow_two {x N : ℕ} (h : x ∣ 2 ^ N) : ∃ (k : ℕ), x = 2 ^ k := by
  induction N generalizing x with
  | zero =>
    simp only [pow_zero] at h
    have : x = 1 := Nat.eq_one_of_dvd_one h
    exact ⟨0, by simp [this]⟩
  | succ N ih =>
    by_cases h2 : 2 ∣ x
    · rcases h2 with ⟨y, rfl⟩
      have hdvd : 2 * y ∣ 2 * 2 ^ N := by
        have h_pow_succ : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
        rwa [h_pow_succ] at h
      have h_div : y ∣ 2 ^ N := by
        exact Nat.dvd_of_mul_dvd_mul_left (by decide) hdvd
      rcases ih h_div with ⟨k, rfl⟩
      exact ⟨k + 1, by ring⟩
    · have h_coprime : Nat.Coprime 2 x := Nat.prime_two.coprime_iff_not_dvd.2 h2
      have h_coprime' : Nat.Coprime x 2 := h_coprime.symm
      have hdvd : x ∣ 2 * 2 ^ N := by
        have h_pow_succ : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
        rwa [h_pow_succ] at h
      have h_div : x ∣ 2 ^ N := by
        exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime' hdvd
      exact ih h_div

lemma exists_pow_two_mul_odd (u : ℕ) (hu : u > 0) : ∃ (s k : ℕ), u = 2 ^ s * (2 * k + 1) := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    by_cases h_even : Even u
    · rcases h_even with ⟨v, rfl⟩
      have hv_pos : v > 0 := by omega
      have hv_lt : v < v + v := by omega
      rcases ih v hv_lt hv_pos with ⟨s, k, rfl⟩
      use s + 1, k
      ring
    · have h_odd : Odd u := Nat.not_even_iff_odd.mp h_even
      rcases h_odd with ⟨k, rfl⟩
      use 0, k
      ring

lemma cancel_mul (X y : ℕ) (hX : X > 0) (h : X = X * y) : 1 = y := by
  rcases y with _ | _ | y
  · simp at h
    omega
  · rfl
  · have h_le : X * (y + 2) ≥ X * 2 := Nat.mul_le_mul_left X (by omega)
    rw [← h] at h_le
    omega

lemma eq_two_of_prime_pow_two {s : ℕ} (h : (2 ^ s).Prime) : 2 ^ s = 2 := by
  rcases s with _ | s
  · simp at h
    exact False.elim (Nat.not_prime_one h)
  · rcases s with _ | s
    · rfl
    · have h_dvd : 2 ∣ 2 ^ (s + 2) := by
        use 2 ^ (s + 1)
        ring
      have h_cases := h.eq_one_or_self_of_dvd 2 h_dvd
      omega

lemma exists_factors_of_composite {m : ℕ} (hm1 : m > 1) (hc : ¬ m.Prime) :
    (∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ m) ∨ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p * q ∣ m) := by
  have hm_ne1 : m ≠ 1 := by omega
  rcases Nat.exists_prime_and_dvd hm_ne1 with ⟨p, hp, hdvd⟩
  rcases hdvd with ⟨k, rfl⟩
  by_cases hk : k = 1
  · subst hk
    simp at hc
    contradiction
  · have hp2 : p ≥ 2 := hp.two_le
    have hk0 : k ≠ 0 := by
      intro hc0
      subst hc0
      simp at hm1
    have hk1 : k > 1 := by omega
    have hk_ne1 : k ≠ 1 := by omega
    rcases Nat.exists_prime_and_dvd hk_ne1 with ⟨q, hq, hqdvd⟩
    rcases hqdvd with ⟨j, rfl⟩
    by_cases hpq : p = q
    · left
      use p, hp
      subst hpq
      use j
      ring
    · right
      use p, q, hp, hq, hpq
      use j
      ring

lemma sum_pow_two_lt (d : ℕ) (S : Finset ℕ) (h : ∀ s ∈ S, s < d) : ∑ s ∈ S, 2 ^ s < 2 ^ d := by
  induction d generalizing S with
  | zero =>
    have h_empty : S = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      have := h x hx
      omega
    subst h_empty
    simp
  | succ d ih =>
    by_cases hd : d ∈ S
    · have h_eq : S = insert d (S.erase d) := (Finset.insert_erase hd).symm
      rw [h_eq]
      rw [Finset.sum_insert (Finset.notMem_erase d S)]
      have h_subset : ∀ s ∈ S.erase d, s < d := by
        intro s hs
        have h_mem : s ∈ S := Finset.mem_of_mem_erase hs
        have h_ne : s ≠ d := Finset.ne_of_mem_erase hs
        have h_lt : s < d + 1 := h s h_mem
        omega
      have ih_val := ih (S.erase d) h_subset
      omega
    · have h_subset : ∀ s ∈ S, s < d := by
        intro s hs
        have h_lt : s < d + 1 := h s hs
        have h_ne : s ≠ d := by
          intro hc
          subst hc
          contradiction
        omega
      have ih_val := ih S h_subset
      omega

lemma totient_eq_prod_of_squarefree {m : ℕ} (hm : m ≠ 0) (hsf : ∀ p ∈ m.factorization.support, m.factorization p = 1) :
    m.totient = m.factorization.support.prod (fun p => p - 1) := by
  rw [totient_eq_prod_factorization hm]
  have h_eq : m.factorization.prod (fun p k => p ^ (k - 1) * (p - 1)) =
      m.factorization.support.prod (fun p => p - 1) := by
    dsimp [Finsupp.prod]
    apply Finset.prod_congr rfl
    intro p hp
    have hk : m.factorization p = 1 := hsf p hp
    rw [hk]
    simp
  exact h_eq

lemma factorization_eq_one_of_no_sq {m : ℕ} (hm : m ≠ 0) (h_no_sq : ¬ ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ m)
    (p : ℕ) (hp : p ∈ m.factorization.support) : m.factorization p = 1 := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have h_le : m.factorization p < 2 := by
    by_contra hc
    push_neg at hc
    have hdvd : p ^ 2 ∣ m := (hp_prime.pow_dvd_iff_le_factorization hm).mpr hc
    exact h_no_sq ⟨p, hp_prime, hdvd⟩
  have h_ne : m.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  omega

lemma not_dvd_sq_of_odd_totient_pow_two {m N : ℕ} (hm_odd : Odd m) (h_tot : m.totient = 2 ^ N) :
    ¬ ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ m := by
  intro ⟨p, hp, hdvd⟩
  have hdvd_mul : p * p ∣ m := by
    rwa [sq] at hdvd
  rcases hdvd_mul with ⟨k, rfl⟩
  -- m = p * (p * k)
  have h_tot_eq : (p * (p * k)).totient = p * (p * k).totient := by
    apply totient_mul_of_prime_of_dvd hp
    exact dvd_mul_right p k
  have h_tot_orig : p * p * k = p * (p * k) := by ring
  rw [h_tot_orig] at h_tot
  rw [h_tot_eq] at h_tot
  have hp_dvd : p ∣ p * (p * k).totient := dvd_mul_right p (totient (p * k))
  rw [h_tot] at hp_dvd
  rcases eq_pow_two_of_dvd_pow_two hp_dvd with ⟨s, hp_eq⟩
  have hp_eq2 : p = 2 := by
    rw [hp_eq] at hp
    have h_eq_two := eq_two_of_prime_pow_two hp
    rw [← hp_eq] at h_eq_two
    exact h_eq_two
  subst hp_eq2
  -- m is odd, but p = 2 divides m. Contradiction!
  have h_even : 2 ∣ 2 * 2 * k := by
    use 2 * k
  have h_not_odd : ¬ Odd (2 * 2 * k) := Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h_even)
  exact h_not_odd hm_odd

lemma pow_of_two_of_prime_fermat (u : ℕ) (hu : u > 0) (hp : (2 ^ u + 1).Prime) : ∃ (s : ℕ), u = 2 ^ s := by
  rcases exists_pow_two_mul_odd u hu with ⟨s, k, rfl⟩
  by_cases hk : k = 0
  · subst hk
    use s
    ring
  · have hk_gt : k > 0 := by omega
    let A := 2 ^ (2 ^ s)
    have h_two_pow_s_pos : 2 ^ s > 0 := by positivity
    have h_two_pow_s_ge1 : 2 ^ s ≥ 1 := h_two_pow_s_pos
    have hA : A ≥ 2 := @Nat.pow_le_pow_right 2 (by decide) 1 (2 ^ s) h_two_pow_s_ge1
    have h_dvd : A + 1 ∣ A ^ (2 * k + 1) + 1 := dvd_pow_odd A (by omega) k
    have h_eq : A ^ (2 * k + 1) + 1 = 2 ^ (2 ^ s * (2 * k + 1)) + 1 := by
      dsimp [A]
      rw [← pow_mul]
    rw [h_eq] at h_dvd
    have h_prime : (2 ^ (2 ^ s * (2 * k + 1)) + 1).Prime := hp
    have hdvd_cases : A + 1 = 1 ∨ A + 1 = 2 ^ (2 ^ s * (2 * k + 1)) + 1 :=
      h_prime.eq_one_or_self_of_dvd (A + 1) h_dvd
    rcases hdvd_cases with h1 | h2
    · omega
    · have h_pow_eq : 2 ^ s = 2 ^ s * (2 * k + 1) := by
        have : A = 2 ^ (2 ^ s * (2 * k + 1)) := Nat.add_right_cancel h2
        dsimp [A] at this
        exact Nat.pow_right_injective (by decide) this
      have h_mul : 1 = 2 * k + 1 := cancel_mul (2 ^ s) (2 * k + 1) h_two_pow_s_pos h_pow_eq
      omega

lemma totient_eq_two_pow_prime {m N : ℕ} (hN : N = 2 ^ 33) (hm_odd : Odd m) (h_tot : m.totient = 2 ^ N) : m.Prime := by
  by_contra hc
  have hm0 : m ≠ 0 := by
    intro hc0
    subst hc0
    have h_pos : 2 ^ N > 0 := by positivity
    have h_tot_0 : (0 : ℕ).totient = 0 := rfl
    rw [h_tot_0] at h_tot
    omega
  have hm_one : m ≠ 1 := by
    intro hc1
    subst hc1
    have h_tot_1 : (1 : ℕ).totient = 1 := rfl
    rw [h_tot_1] at h_tot
    have h_pow_gt : 2 ^ N > 1 := by
      exact Nat.one_lt_pow (by omega) (by decide)
    omega
  have hm1 : m > 1 := by omega
  rcases exists_factors_of_composite hm1 hc with h_sq | h_dist
  · have h_no_sq := not_dvd_sq_of_odd_totient_pow_two hm_odd h_tot
    exact h_no_sq h_sq
  · rcases h_dist with ⟨p, q, hp, hq, hpq, hpdvd⟩
    let P := m.factorization.support
    have hp_in_P : p ∈ P := by
      rw [Finsupp.mem_support_iff]
      have hp_div : p ∣ m := dvd_trans (dvd_mul_right p q) hpdvd
      exact (Nat.Prime.factorization_pos_of_dvd hp hm0 hp_div).ne'
    have hq_in_P : q ∈ P := by
      rw [Finsupp.mem_support_iff]
      have hq_div : q ∣ m := by
        have : q ∣ p * q := by rw [mul_comm]; exact dvd_mul_right q p
        exact dvd_trans this hpdvd
      exact (Nat.Prime.factorization_pos_of_dvd hq hm0 hq_div).ne'
    have h_subset : {p, q} ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hp_in_P
      · exact hq_in_P
    have h_card : P.card ≥ 2 := by
      have h_card_subset := Finset.card_le_card h_subset
      have h_card_pq : ({p, q} : Finset ℕ).card = 2 := by
        exact Finset.card_pair hpq
      omega
    have h_sf : ∀ r ∈ P, m.factorization r = 1 := by
      intro r hr
      have h_no_sq := not_dvd_sq_of_odd_totient_pow_two hm_odd h_tot
      exact factorization_eq_one_of_no_sq hm0 h_no_sq r hr
    have h_tot_eq_prod := totient_eq_prod_of_squarefree hm0 h_sf
    -- For each r ∈ P, we can find a power s_r such that r - 1 = 2 ^ 2 ^ s_r
    have h_exists_s : ∀ r ∈ P, ∃ s : ℕ, r - 1 = 2 ^ 2 ^ s := by
      intro r hr
      have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hr_dvd : r - 1 ∣ m.totient := by
        rw [h_tot_eq_prod]
        exact Finset.dvd_prod_of_mem (fun x => x - 1) hr
      rw [h_tot] at hr_dvd
      rcases eq_pow_two_of_dvd_pow_two hr_dvd with ⟨a, ha⟩
      have hr_odd : Odd r := by
        by_contra hc_even
        have h_even : Even r := Nat.not_odd_iff_even.mp hc_even
        rcases h_even with ⟨j, rfl⟩
        have hr_div_m := Nat.dvd_of_mem_primeFactors hr
        rcases hr_div_m with ⟨d, rfl⟩
        have : Even ((j + j) * d) := by
          use j * d
          ring
        have : ¬ Odd ((j + j) * d) := Nat.not_odd_iff_even.mpr this
        contradiction
      have ha_pos : a > 0 := by
        by_contra h_zero
        have : a = 0 := by omega
        subst this
        simp only [pow_zero] at ha
        have : r = 2 := by omega
        subst this
        have : ¬ Odd 2 := by decide
        contradiction
      have h_prime_r : (2 ^ a + 1).Prime := by
        have : 2 ^ a + 1 = r := by
          have hr_ge2 : r ≥ 2 := hr_prime.two_le
          omega
        rwa [this]
      rcases pow_of_two_of_prime_fermat a ha_pos h_prime_r with ⟨s, hs⟩
      use s
      rw [hs] at ha
      exact ha
    -- Define the function g using Classical.choose
    let g : ℕ → ℕ := fun r => if hr : r ∈ P then Classical.choose (h_exists_s r hr) else 0
    have hg_spec : ∀ r ∈ P, r - 1 = 2 ^ 2 ^ (g r) := by
      intro r hr
      dsimp [g]
      rw [dif_pos hr]
      exact Classical.choose_spec (h_exists_s r hr)
    have hg_inj : ∀ r1 ∈ P, ∀ r2 ∈ P, g r1 = g r2 → r1 = r2 := by
      intro r1 hr1 r2 hr2 h_eq
      have h1 := hg_spec r1 hr1
      have h2 := hg_spec r2 hr2
      rw [h_eq] at h1
      have : r1 - 1 = r2 - 1 := by omega
      have hr1_prime : r1.Prime := Nat.prime_of_mem_primeFactors hr1
      have hr2_prime : r2.Prime := Nat.prime_of_mem_primeFactors hr2
      have hr1_ge2 : r1 ≥ 2 := hr1_prime.two_le
      have hr2_ge2 : r2 ≥ 2 := hr2_prime.two_le
      omega
    have hg_inj_set : Set.InjOn g ↑P := hg_inj
    let S := P.image g
    have h_card_S : S.card = P.card := Finset.card_image_of_injOn hg_inj_set
    have h_sum : ∑ s ∈ S, 2 ^ s = N := by
      have h_prod_eq : ∏ r ∈ P, (r - 1) = 2 ^ (∑ s ∈ S, 2 ^ s) := by
        have h_prod_eq_1 : ∏ r ∈ P, (r - 1) = ∏ r ∈ P, 2 ^ 2 ^ (g r) := by
          apply Finset.prod_congr rfl
          intro r hr
          exact hg_spec r hr
        rw [h_prod_eq_1]
        have h_prod_eq_2 : ∏ r ∈ P, 2 ^ 2 ^ (g r) = 2 ^ (∑ r ∈ P, 2 ^ (g r)) := by
          rw [Finset.prod_pow_eq_pow_sum]
        rw [h_prod_eq_2]
        have h_sum_image : ∑ r ∈ P, 2 ^ (g r) = ∑ s ∈ S, 2 ^ s := by
          rw [Finset.sum_image hg_inj_set]
        rw [h_sum_image]
      have h_tot_eq_prod_copy := h_tot_eq_prod
      rw [h_prod_eq] at h_tot_eq_prod_copy
      rw [h_tot] at h_tot_eq_prod_copy
      exact (Nat.pow_right_injective (show 2 ≤ 2 by omega) h_tot_eq_prod_copy).symm
    -- S has card S.card >= 2
    have h_card_S_ge2 : S.card ≥ 2 := by omega
    -- So 33 ∉ S
    have h_33_not_in_S : 33 ∉ S := by
      intro hc_33
      have h_sum_ge : ∑ s ∈ S, 2 ^ s > 2 ^ 33 := by
        have h_eq : S = insert 33 (S.erase 33) := (Finset.insert_erase hc_33).symm
        rw [h_eq]
        rw [Finset.sum_insert (Finset.notMem_erase 33 S)]
        have h_card_er : (S.erase 33).card ≥ 1 := by
          have : (S.erase 33).card + 1 = S.card := Finset.card_erase_add_one hc_33
          omega
        have h_nonempty : (S.erase 33).Nonempty := Finset.card_pos.mp (by omega)
        rcases h_nonempty with ⟨y, hy⟩
        have h_ge_y : ∑ s ∈ S.erase 33, 2 ^ s ≥ 2 ^ y := Finset.single_le_sum (fun x _ => Nat.zero_le (2 ^ x)) hy
        have h_y_pos : 2 ^ y > 0 := by positivity
        omega
      omega
    have h_all_lt_33 : ∀ s ∈ S, s < 33 := by
      intro s hs
      have h_le_33 : s ≤ 33 := by
        by_contra hc_gt
        push_neg at hc_gt
        have h_ge_s : ∑ s ∈ S, 2 ^ s ≥ 2 ^ s := Finset.single_le_sum (fun x _ => Nat.zero_le (2 ^ x)) hs
        rw [h_sum, hN] at h_ge_s
        have h_pow_gt : 2 ^ s > 2 ^ 33 := Nat.pow_lt_pow_right (show 1 < 2 by decide) hc_gt
        omega
      have : s ≠ 33 := by
        intro hc_eq
        subst hc_eq
        contradiction
      omega
    have h_sum_lt := sum_pow_two_lt 33 S h_all_lt_33
    rw [h_sum, hN] at h_sum_lt
    omega
