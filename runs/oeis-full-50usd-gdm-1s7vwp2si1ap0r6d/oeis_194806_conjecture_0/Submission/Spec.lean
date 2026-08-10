import FormalConjectures.Util.ProblemImports

open Finset Nat

/-- The set of all products of elements from a Finset S. -/
def set_prod (S : Finset ℕ) : Finset ℕ :=
  (S.product S).image fun p : ℕ × ℕ => p.fst * p.snd

/--
A194806: Size of the smallest subset $S$ of $T = \{1,2,3,\dots,n\}$ such that $S \cdot S$ contains $T$,
where $S \cdot S$ is the set of all products of elements of $S$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let T_n := Icc 1 n

    -- The set of subsets $S \subseteq T_n$ such that $T_n ⊆ S \cdot S$.
    let valid_subsets : Finset (Finset ℕ) :=
      T_n.powerset.filter (fun S : Finset ℕ => T_n ⊆ set_prod S)

    -- Proof that $T_n$ is guaranteed to be a valid subset, ensuring `valid_subsets` is non-empty.
    have T_n_is_valid : T_n ∈ valid_subsets := by
      apply mem_filter.mpr
      constructor
      -- 1. T_n ∈ T_n.powerset (i.e., T_n ⊆ T_n)
      apply mem_powerset.mpr; rfl
      -- 2. T_n ⊆ set_prod T_n
      intro k hk

      have one_le_n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
      have h1 : 1 ∈ T_n := mem_Icc.mpr ⟨Nat.le_refl 1, one_le_n⟩

      -- We show k = k * 1 is in set_prod T_n
      -- set_prod T_n is the image of T_n × T_n under multiplication.
      simp only [set_prod, mem_image, Prod.exists]
      use k, 1
      constructor
      -- Show that (k, 1) ∈ T_n × T_n
      · exact mem_product.mpr ⟨hk, h1⟩
      -- Show that k * 1 = k
      · exact Nat.mul_one k

    have h_nonempty : valid_subsets.Nonempty := ⟨T_n, T_n_is_valid⟩

    let sizes := valid_subsets.image Finset.card

    -- The min' function requires proof that the finset is non-empty.
    have h_sizes_nonempty : sizes.Nonempty := h_nonempty.image Finset.card

    -- We return the minimum card of all valid subsets.
    sizes.min' h_sizes_nonempty

lemma a_le_of_valid {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS1 : S ⊆ Icc 1 n) (hS2 : Icc 1 n ⊆ set_prod S) :
    a n ≤ S.card := by
  unfold a
  split_ifs with h
  · contradiction
  · dsimp only
    have hS : S ∈ (Icc 1 n).powerset.filter (fun S : Finset ℕ => Icc 1 n ⊆ set_prod S) := by
      apply mem_filter.mpr
      exact ⟨mem_powerset.mpr hS1, hS2⟩
    have h_card : S.card ∈ ((Icc 1 n).powerset.filter (fun S : Finset ℕ => Icc 1 n ⊆ set_prod S)).image Finset.card := by
      apply mem_image.mpr
      exact ⟨S, hS, rfl⟩
    exact Finset.min'_le _ _ h_card

lemma Icc_subset_set_prod (n : ℕ) : Icc 1 n ⊆ set_prod (Icc 1 n) := by
  intro k hk
  by_cases hn : n = 0
  · subst hn
    have h_empty : Icc 1 0 = ∅ := rfl
    rw [h_empty] at hk
    simp at hk
  · have one_le_n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have h1 : 1 ∈ Icc 1 n := mem_Icc.mpr ⟨Nat.le_refl 1, one_le_n⟩
    simp only [set_prod, mem_image, Prod.exists]
    use k, 1
    constructor
    · exact mem_product.mpr ⟨hk, h1⟩
    · exact Nat.mul_one k

lemma a_le_n (n : ℕ) : a n ≤ n := by
  by_cases hn : n = 0
  · subst hn; rfl
  · have h_le := a_le_of_valid hn (subset_refl _) (Icc_subset_set_prod n)
    have h_card : (Icc 1 n).card = n := by
      rw [Nat.card_Icc]
      have one_le_n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      omega
    omega

theorem primeCounting_two_pow_ge (k : ℕ) : k ≤ Nat.primeCounting (2^k) := by
  induction' k with k ih
  · simp [primeCounting]
  · rw [primeCounting, Nat.pow_succ]
    have h_two_pow_ne : 2^k ≠ 0 := by positivity
    obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (2^k) h_two_pow_ne
    have h1 : 2^k + 1 ≤ p := hp_gt
    have h_pc_le : primeCounting' (2^k + 1) ≤ primeCounting' p := Nat.monotone_primeCounting' h1
    have h_lt_succ : p < 2^k * 2 + 1 := by omega
    have h_pc_lt : primeCounting' p < primeCounting' (2^k * 2 + 1) := by
      apply Nat.count_strict_mono hp_prime h_lt_succ
    have h2 : k < primeCounting' (2^k * 2 + 1) := by
      calc
        k ≤ primeCounting' (2^k + 1) := ih
        _ ≤ primeCounting' p := h_pc_le
        _ < primeCounting' (2^k * 2 + 1) := h_pc_lt
    exact h2

theorem primeCounting_ge_log (n : ℕ) (hn : 2 ≤ n) : Nat.log 2 n ≤ Nat.primeCounting n := by
  have h_ne : n ≠ 0 := by omega
  have h1 : 2^(Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 h_ne
  have h2 : Nat.log 2 n ≤ Nat.primeCounting (2^(Nat.log 2 n)) := primeCounting_two_pow_ge (Nat.log 2 n)
  have h3 : Nat.primeCounting (2^(Nat.log 2 n)) ≤ Nat.primeCounting n := Nat.monotone_primeCounting h1
  omega

-- Candidate set S_n
def S_set (n : ℕ) : Finset ℕ :=
  Icc 1 (n / 4) ∪ (Icc 1 n).filter (fun p => Nat.Prime p) ∪ ({1} : Finset ℕ)

theorem primes_in_Icc_eq_primeCounting (n : ℕ) :
    ((Icc 1 n).filter (fun p => Nat.Prime p)).card = Nat.primeCounting n := by
  have h1 : (Icc 1 n).filter (fun p => Nat.Prime p) = (range (n+1)).filter (fun p => Nat.Prime p) := by
    ext x
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · rintro ⟨⟨hx1, hxn⟩, hxp⟩
      exact ⟨by omega, hxp⟩
    · rintro ⟨hxn, hxp⟩
      have : 1 ≤ x := by
        by_contra h
        have : x = 0 := by omega
        subst this
        exact Nat.not_prime_zero hxp
      exact ⟨⟨this, by omega⟩, hxp⟩
  rw [h1]
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

theorem primeCounting_pos (n : ℕ) (hn : 2 ≤ n) : 1 ≤ Nat.primeCounting n := by
  have h : 2 ∈ (Icc 1 n).filter (fun p => Nat.Prime p) := by
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨by decide, hn⟩, Nat.prime_two⟩
  have h_card : 1 ≤ ((Icc 1 n).filter (fun p => Nat.Prime p)).card := by
    have : ((Icc 1 n).filter (fun p => Nat.Prime p)).Nonempty := ⟨2, h⟩
    exact Finset.Nonempty.card_pos this
  rw [primes_in_Icc_eq_primeCounting] at h_card
  exact h_card

theorem S_set_card (n : ℕ) (hn : 2 ≤ n) : (S_set n).card ≤ n / 4 + Nat.primeCounting n + 1 := by
  have h_union1 : (S_set n).card ≤ (Icc 1 (n / 4) ∪ (Icc 1 n).filter (fun p => Nat.Prime p)).card + ({1} : Finset ℕ).card := by
    exact card_union_le _ _
  have h_union2 : (Icc 1 (n / 4) ∪ (Icc 1 n).filter (fun p => Nat.Prime p)).card ≤ (Icc 1 (n / 4)).card + ((Icc 1 n).filter (fun p => Nat.Prime p)).card := by
    exact card_union_le _ _
  have h_card1 : (Icc 1 (n / 4)).card ≤ n / 4 := by
    rw [Nat.card_Icc]
    omega
  have h_card2 := primes_in_Icc_eq_primeCounting n
  have h_card3 : ({1} : Finset ℕ).card = 1 := card_singleton 1
  omega

theorem S_set_subset (n : ℕ) (hn : n ≠ 0) : S_set n ⊆ Icc 1 n := by
  intro x hx
  simp only [S_set, mem_union, mem_Icc, mem_filter, mem_singleton] at hx
  rcases hx with ((⟨h1, h2⟩ | ⟨⟨h1, h2⟩, hp⟩) | rfl)
  · -- x ∈ Icc 1 (n/4)
    have : n / 4 ≤ n := Nat.div_le_self n 4
    exact mem_Icc.mpr ⟨h1, le_trans h2 this⟩
  · -- x ∈ (Icc 1 n).filter Prime
    exact mem_Icc.mpr ⟨h1, h2⟩
  · -- x = 1
    have : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    exact mem_Icc.mpr ⟨by omega, this⟩

theorem S_set_valid (n : ℕ) (hn : 3000 ≤ n) : Icc 1 n ⊆ set_prod (S_set n) := by
  intro k hk
  rw [mem_Icc] at hk
  by_cases hk1 : k = 1
  · subst hk1
    simp only [set_prod, mem_image, Prod.exists]
    use 1, 1
    have h1 : 1 ∈ S_set n := by
      simp only [S_set, mem_union, mem_Icc, mem_filter, mem_singleton]
      right; trivial
    have h_prod : (1, 1) ∈ S_set n ×ˢ S_set n := by
      rw [mem_product]
      exact ⟨h1, h1⟩
    exact ⟨h_prod, rfl⟩
  · by_cases hk_prime : Nat.Prime k
    · simp only [set_prod, mem_image, Prod.exists]
      use k, 1
      have hk_in : k ∈ S_set n := by
        simp only [S_set, mem_union, mem_Icc, mem_filter, mem_singleton]
        left; right
        exact ⟨⟨by omega, hk.2⟩, hk_prime⟩
      have h1 : 1 ∈ S_set n := by
        simp only [S_set, mem_union, mem_Icc, mem_filter, mem_singleton]
        right; trivial
      have h_prod : (k, 1) ∈ S_set n ×ˢ S_set n := by
        rw [mem_product]
        exact ⟨hk_in, h1⟩
      exact ⟨h_prod, mul_one k⟩
    · -- k is composite
      simp only [set_prod, mem_image, Prod.exists]
      have hk_gt : 1 < k := by omega
      have hp_prime : Nat.Prime (minFac k) := minFac_prime (by omega)
      have hp_dvd : minFac k ∣ k := minFac_dvd k
      have hp_ge_2 : 2 ≤ minFac k := Nat.Prime.two_le hp_prime
      by_cases hp_ge_4 : 4 ≤ minFac k
      · -- Case p >= 4
        use minFac k, k / minFac k
        have h_div_pos : 1 ≤ k / minFac k := by
          have : minFac k ≤ k := Nat.le_of_dvd (by omega : 0 < k) hp_dvd
          exact Nat.div_pos this (by omega)
        have h_div_le : k / minFac k ≤ n / 4 := by
          have h_div : k / minFac k ≤ k / 4 := Nat.div_le_div_left hp_ge_4 (by omega)
          have h_le_n : k / 4 ≤ n / 4 := Nat.div_le_div_right hk.2
          omega
        have hp_in : minFac k ∈ S_set n := by
          simp only [S_set, mem_union, mem_Icc, mem_filter, mem_singleton]
          left; right
          constructor
          · constructor
            · omega
            · have : minFac k ≤ k := Nat.le_of_dvd (by omega : 0 < k) hp_dvd
              omega
          · exact hp_prime
        have h_div_in : k / minFac k ∈ S_set n := by
          simp only [S_set, mem_union, mem_Icc, mem_filter, mem_singleton]
          left; left
          exact ⟨h_div_pos, h_div_le⟩
        have h_prod : (minFac k, k / minFac k) ∈ S_set n ×ˢ S_set n := by
          rw [mem_product]
          exact ⟨hp_in, h_div_in⟩
        exact ⟨h_prod, Nat.mul_div_cancel' hp_dvd⟩
      · -- Case p < 4
        have hp_lt_4 : minFac k < 4 := by omega
        let p := minFac k
        let q := k / p
        have hp_dvd : p ∣ k := minFac_dvd k
        by_cases hq_prime : Nat.Prime q
        · -- q is prime
          use p, q
          have hp_in : p ∈ S_set n := by
            simp only [S_set, mem_union, mem_Icc, mem_filter, mem_singleton]
            left; right
            constructor
            · constructor
              · omega
              · have : p ≤ k := Nat.le_of_dvd (by omega : 0 < k) hp_dvd
                omega
            · exact hp_prime
          have hq_in : q ∈ S_set n := by
            simp only [S_set, mem_union, mem_Icc, mem_filter, mem_singleton]
            left; right
            constructor
            · constructor
              · have : 2 ≤ q := Nat.Prime.two_le hq_prime
                omega
              · have : q ≤ k := Nat.div_le_self k p
                omega
            · exact hq_prime
          have h_prod : (p, q) ∈ S_set n ×ˢ S_set n := by
            rw [mem_product]
            exact ⟨hp_in, hq_in⟩
          exact ⟨h_prod, Nat.mul_div_cancel' hp_dvd⟩
        · -- q is composite
          have hq_gt : 1 < q := by
            have h_lt : p < k := by
              have hp_le : p ≤ k := Nat.le_of_dvd (by omega) hp_dvd
              have hp_ne : p ≠ k := by
                intro h_eq
                apply hk_prime
                rw [← h_eq]
                exact hp_prime
              omega
            have : p * 1 < p * q := by
              rw [Nat.mul_one]
              have h_eq : k = p * q := (Nat.mul_div_cancel' hp_dvd).symm
              omega
            have : 1 < q := Nat.lt_of_mul_lt_mul_left this
            omega
          have hq_not_prime : ¬ Nat.Prime q := hq_prime
          have hr_prime : Nat.Prime (minFac q) := minFac_prime (by omega)
          have hr_dvd : minFac q ∣ q := minFac_dvd q
          let r := minFac q
          let s := q / r
          have hr_ge_p : p ≤ r := by
            have : r ∣ k := by
              have : r ∣ q := minFac_dvd q
              exact dvd_trans this (div_dvd_of_dvd hp_dvd)
            exact Nat.minFac_le_of_dvd (Nat.Prime.two_le hr_prime) this
          have hs_ge_r : r ≤ s := Nat.minFac_le_div (by omega) hq_not_prime
          use p * r, s
          have h_pr_ge_4 : 4 ≤ p * r := by
            calc
              4 ≤ 2 * 2 := by decide
              _ ≤ p * r := by nlinarith [hp_ge_2, hr_ge_p]
          have h_div_eq : s = k / (p * r) := by
            have h_mul_eq : k = (p * r) * s := by
              calc
                k = p * q := by rw [Nat.mul_div_cancel' hp_dvd]
                _ = p * (r * s) := by rw [Nat.mul_div_cancel' hr_dvd]
                _ = (p * r) * s := by ring
            rw [h_mul_eq, Nat.mul_div_cancel_left]
            positivity
          have hs_le_n4 : s ≤ n / 4 := by
            have h1 : k / (p * r) ≤ k / 4 := Nat.div_le_div_left h_pr_ge_4 (by omega)
            have h2 : k / 4 ≤ n / 4 := Nat.div_le_div_right hk.2
            rw [h_div_eq]
            exact Nat.le_trans h1 h2
          have h_div_pos : 1 ≤ s := by
            have : r ≤ q := Nat.le_of_dvd (by omega) hr_dvd
            exact Nat.div_pos this (by omega)
          have h_pr_pr : (p * r) * (p * r) ≤ 9 * n := by
            have hr_sq_le : r * r ≤ r * s := Nat.mul_le_mul_left r hs_ge_r
            have hp_sq : p * p ≤ 9 := by
              rcases show p = 2 ∨ p = 3 by omega with hp2 | hp3
              · rw [hp2]
                decide
              · rw [hp3]
            have h_step1 : p * p * (r * r) ≤ 9 * (r * r) := Nat.mul_le_mul_right (r * r) hp_sq
            have h_step2 : 9 * (r * r) ≤ 9 * (r * s) := Nat.mul_le_mul_left 9 hr_sq_le
            calc
              (p * r) * (p * r) = p * p * (r * r) := by ring
              _ ≤ 9 * (r * s) := Nat.le_trans h_step1 h_step2
              _ = 9 * q := by rw [Nat.mul_div_cancel' hr_dvd]
              _ ≤ 9 * n := by
                gcongr
                have h_le : q ≤ n := by
                  have h1 : k / p ≤ k := Nat.div_le_self k p
                  have h2 : k ≤ n := hk.2
                  change k / p ≤ n
                  omega
                exact h_le
          have h_pr_le_n4 : p * r ≤ n / 4 := by
            by_contra h_gt
            have h_gt' : n / 4 < p * r := by omega
            have h_sq_gt : (n / 4) * (n / 4) < (p * r) * (p * r) := by
              gcongr
            have h_comb : (n / 4) * (n / 4) < 9 * n := by omega
            have h_n4_ge : 750 ≤ n / 4 := by
              have : 3000 / 4 ≤ n / 4 := Nat.div_le_div_right hn
              omega
            have h_large : 9 * n ≤ (n / 4) * (n / 4) := by
              calc
                9 * n ≤ 750 * (n / 4) := by omega
                _ ≤ (n / 4) * (n / 4) := by gcongr
            omega
          have h_pr_in : p * r ∈ S_set n := by
            simp only [S_set, mem_union, mem_Icc, mem_filter, mem_singleton]
            left; left
            exact ⟨by omega, h_pr_le_n4⟩
          have hs_in : s ∈ S_set n := by
            simp only [S_set, mem_union, mem_Icc, mem_filter, mem_singleton]
            left; left
            exact ⟨h_div_pos, hs_le_n4⟩
          have h_prod : (p * r, s) ∈ S_set n ×ˢ S_set n := by
            rw [mem_product]
            exact ⟨h_pr_in, hs_in⟩
          refine ⟨h_prod, ?_⟩
          calc
            (p * r) * s = p * (r * s) := by ring
            _ = p * q := by rw [Nat.mul_div_cancel' hr_dvd]
            _ = k := by rw [Nat.mul_div_cancel' hp_dvd]

/--
**OEIS A194806 Conjecture:** Is $a(n)/\pi(n)$ bounded as $n \to \infty$?
(Where $\pi(n) = A000720(n)$ is the prime counting function `Nat.primeCounting n`).
-/
theorem oeis_194806_conjecture_0 :
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    (a n : ℝ) / (Nat.primeCounting n : ℝ) ≤ C := by
  use 3000
  intro n hn
  have hn_ne : n ≠ 0 := by omega
  have h_pi_pos : 0 < (Nat.primeCounting n : ℝ) := by
    have h_pc_pos : 0 < Nat.primeCounting n := primeCounting_pos n hn
    exact_mod_cast h_pc_pos
  rw [div_le_iff₀ h_pi_pos]
  rcases lt_or_ge n 3000 with h_lt | h_ge
  · -- n < 3000
    have h_le_n : (a n : ℝ) ≤ (n : ℝ) := by exact_mod_cast a_le_n n
    have h_pi_ge : 1 ≤ (Nat.primeCounting n : ℝ) := by exact_mod_cast primeCounting_pos n hn
    calc
      (a n : ℝ) ≤ (n : ℝ) := h_le_n
      _ ≤ 3000 := by exact_mod_cast (by omega : n ≤ 3000)
      _ ≤ 3000 * (Nat.primeCounting n : ℝ) := by linarith
  · -- n >= 3000
    have hn_ne : n ≠ 0 := by omega
    have h_le := a_le_of_valid hn_ne (S_set_subset n hn_ne) (S_set_valid n h_ge)
    have h_card := S_set_card n hn
    have h_le_trans : a n ≤ n / 4 + Nat.primeCounting n + 1 := by omega
    have h_le_cast : (a n : ℝ) ≤ (n / 4 + Nat.primeCounting n + 1 : ℝ) := by exact_mod_cast h_le_trans
    sorry
