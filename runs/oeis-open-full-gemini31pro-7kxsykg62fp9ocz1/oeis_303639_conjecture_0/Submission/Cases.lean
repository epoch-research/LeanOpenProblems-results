import Mathlib

lemma no_sum_sq_of_padic (R q k M : ℕ)
    (hR0 : R ≠ 0)
    (hq_prime : q.Prime)
    (hR : R = q ^ (2 * k + 1) * M)
    (hM : ¬ q ∣ M)
    (hq3 : q % 4 = 3) :
    ∀ a b : ℕ, a ^ 2 + b ^ 2 ≠ R := by
  intro a b hab
  have h_eq : ∃ x y, R = x ^ 2 + y ^ 2 := ⟨a, b, hab.symm⟩
  have h_iff := Nat.eq_sq_add_sq_iff.mp h_eq q
  have h_mem : q ∈ R.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hq_prime, ?_, hR0⟩
    rw [hR]
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
  have h_even := h_iff h_mem hq3
  haveI : Fact q.Prime := ⟨hq_prime⟩
  have h_padic : padicValNat q R = 2 * k + 1 := by
    rw [hR]
    have hM0 : M ≠ 0 := by rintro rfl; exact hM (dvd_zero _)
    have hqpow0 : q ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ hq_prime.ne_zero
    rw [padicValNat.mul hqpow0 hM0]
    have : padicValNat q M = 0 := padicValNat.eq_zero_of_not_dvd hM
    rw [this, add_zero]
    rw [padicValNat.pow (2 * k + 1) hq_prime.ne_zero]
    rw [padicValNat_self]
    omega
  rw [h_padic] at h_even
  have h_odd : ¬ Even (2 * k + 1) := by
    rintro ⟨x, hx⟩
    omega
  exact h_odd h_even

def B (k : ℕ) : ℕ := (2 * k + 1).choose k

lemma no_sol_0_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 0 = 2 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322178 := by omega
  have h2 := no_sum_sq_of_padic 800322178 647 0 1236974 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 1 = 4 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322176 := by omega
  have h2 := no_sum_sq_of_padic 800322176 163 0 4909952 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 2 = 11 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322169 := by omega
  have h2 := no_sum_sq_of_padic 800322169 67 0 11945107 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 3 = 36 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322144 := by omega
  have h2 := no_sum_sq_of_padic 800322144 3 0 266774048 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 4 = 127 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322053 := by omega
  have h2 := no_sum_sq_of_padic 800322053 23 0 34796611 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 5 = 463 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321717 := by omega
  have h2 := no_sum_sq_of_padic 800321717 467 0 1713751 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 6 = 1717 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320463 := by omega
  have h2 := no_sum_sq_of_padic 800320463 223 0 3588881 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 7 = 6436 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315744 := by omega
  have h2 := no_sum_sq_of_padic 800315744 991 0 807584 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 8 = 24311 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297869 := by omega
  have h2 := no_sum_sq_of_padic 800297869 7 0 114328267 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 9 = 92379 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229801 := by omega
  have h2 := no_sum_sq_of_padic 800229801 3 0 266743267 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 10 = 352717 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969463 := by omega
  have h2 := no_sum_sq_of_padic 799969463 23 0 34781281 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 11 = 1352079 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798970101 := by omega
  have h2 := no_sum_sq_of_padic 798970101 3 0 266323367 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 12 = 5200301 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121879 := by omega
  have h2 := no_sum_sq_of_padic 795121879 887 0 896417 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 13 = 20058301 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263879 := by omega
  have h2 := no_sum_sq_of_padic 780263879 26905651 0 29 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 14 = 77558761 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722763419 := by omega
  have h2 := no_sum_sq_of_padic 722763419 7 0 103251917 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_0_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 0 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 0 + B 15 = 300540196 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781984 := by omega
  have h2 := no_sum_sq_of_padic 499781984 1999 0 250016 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 0 = 4 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322176 := by omega
  have h2 := no_sum_sq_of_padic 800322176 163 0 4909952 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 1 = 6 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322174 := by omega
  have h2 := no_sum_sq_of_padic 800322174 3 1 29641562 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 2 = 13 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322167 := by omega
  have h2 := no_sum_sq_of_padic 800322167 643 0 1244669 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 3 = 38 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322142 := by omega
  have h2 := no_sum_sq_of_padic 800322142 19 0 42122218 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 4 = 129 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322051 := by omega
  have h2 := no_sum_sq_of_padic 800322051 3 0 266774017 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 5 = 465 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321715 := by omega
  have h2 := no_sum_sq_of_padic 800321715 3 3 365945 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 6 = 1719 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320461 := by omega
  have h2 := no_sum_sq_of_padic 800320461 3 0 266773487 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 7 = 6438 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315742 := by omega
  have h2 := no_sum_sq_of_padic 800315742 3 0 266771914 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 8 = 24313 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297867 := by omega
  have h2 := no_sum_sq_of_padic 800297867 78607 0 10181 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 9 = 92381 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229799 := by omega
  have h2 := no_sum_sq_of_padic 800229799 27594131 0 29 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 10 = 352719 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969461 := by omega
  have h2 := no_sum_sq_of_padic 799969461 3 0 266656487 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 11 = 1352081 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798970099 := by omega
  have h2 := no_sum_sq_of_padic 798970099 31 0 25773229 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 12 = 5200303 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121877 := by omega
  have h2 := no_sum_sq_of_padic 795121877 11 0 72283807 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 13 = 20058303 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263877 := by omega
  have h2 := no_sum_sq_of_padic 780263877 3 0 260087959 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 14 = 77558763 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722763417 := by omega
  have h2 := no_sum_sq_of_padic 722763417 3 0 240921139 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_1_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 1 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 1 + B 15 = 300540198 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781982 := by omega
  have h2 := no_sum_sq_of_padic 499781982 3 0 166593994 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 0 = 11 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322169 := by omega
  have h2 := no_sum_sq_of_padic 800322169 67 0 11945107 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 1 = 13 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322167 := by omega
  have h2 := no_sum_sq_of_padic 800322167 643 0 1244669 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 2 = 20 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322160 := by omega
  have h2 := no_sum_sq_of_padic 800322160 11 0 72756560 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 3 = 45 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322135 := by omega
  have h2 := no_sum_sq_of_padic 800322135 3 0 266774045 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 4 = 136 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322044 := by omega
  have h2 := no_sum_sq_of_padic 800322044 200080511 0 4 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 5 = 472 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321708 := by omega
  have h2 := no_sum_sq_of_padic 800321708 23 0 34796596 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 6 = 1726 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320454 := by omega
  have h2 := no_sum_sq_of_padic 800320454 284003 0 2818 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 7 = 6445 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315735 := by omega
  have h2 := no_sum_sq_of_padic 800315735 4326031 0 185 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 8 = 24320 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297860 := by omega
  have h2 := no_sum_sq_of_padic 800297860 19 0 42120940 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 9 = 92388 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229792 := by omega
  have h2 := no_sum_sq_of_padic 800229792 3 0 266743264 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 10 = 352726 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969454 := by omega
  have h2 := no_sum_sq_of_padic 799969454 399984727 0 2 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 11 = 1352088 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798970092 := by omega
  have h2 := no_sum_sq_of_padic 798970092 3 0 266323364 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 12 = 5200310 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121870 := by omega
  have h2 := no_sum_sq_of_padic 795121870 79512187 0 10 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 13 = 20058310 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263870 := by omega
  have h2 := no_sum_sq_of_padic 780263870 127 0 6143810 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 14 = 77558770 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722763410 := by omega
  have h2 := no_sum_sq_of_padic 722763410 2819 0 256390 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_2_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 2 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 2 + B 15 = 300540205 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781975 := by omega
  have h2 := no_sum_sq_of_padic 499781975 7 0 71397425 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 0 = 36 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322144 := by omega
  have h2 := no_sum_sq_of_padic 800322144 3 0 266774048 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 1 = 38 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322142 := by omega
  have h2 := no_sum_sq_of_padic 800322142 19 0 42122218 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 2 = 45 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322135 := by omega
  have h2 := no_sum_sq_of_padic 800322135 3 0 266774045 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 3 = 70 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322110 := by omega
  have h2 := no_sum_sq_of_padic 800322110 7 0 114331730 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 4 = 161 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322019 := by omega
  have h2 := no_sum_sq_of_padic 800322019 7 0 114331717 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 5 = 497 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321683 := by omega
  have h2 := no_sum_sq_of_padic 800321683 7 0 114331669 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 6 = 1751 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320429 := by omega
  have h2 := no_sum_sq_of_padic 800320429 43 0 18612103 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 7 = 6470 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315710 := by omega
  have h2 := no_sum_sq_of_padic 800315710 5843 0 136970 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 8 = 24345 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297835 := by omega
  have h2 := no_sum_sq_of_padic 800297835 3 0 266765945 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 9 = 92413 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229767 := by omega
  have h2 := no_sum_sq_of_padic 800229767 7923067 0 101 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 10 = 352751 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969429 := by omega
  have h2 := no_sum_sq_of_padic 799969429 7 0 114281347 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 11 = 1352113 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798970067 := by omega
  have h2 := no_sum_sq_of_padic 798970067 7 0 114138581 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 12 = 5200335 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121845 := by omega
  have h2 := no_sum_sq_of_padic 795121845 3 0 265040615 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 13 = 20058335 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263845 := by omega
  have h2 := no_sum_sq_of_padic 780263845 23 0 33924515 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 14 = 77558795 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722763385 := by omega
  have h2 := no_sum_sq_of_padic 722763385 23 0 31424495 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_3_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 3 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 3 + B 15 = 300540230 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781950 := by omega
  have h2 := no_sum_sq_of_padic 499781950 23 0 21729650 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 0 = 127 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322053 := by omega
  have h2 := no_sum_sq_of_padic 800322053 23 0 34796611 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 1 = 129 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322051 := by omega
  have h2 := no_sum_sq_of_padic 800322051 3 0 266774017 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 2 = 136 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322044 := by omega
  have h2 := no_sum_sq_of_padic 800322044 200080511 0 4 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 3 = 161 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800322019 := by omega
  have h2 := no_sum_sq_of_padic 800322019 7 0 114331717 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 4 = 252 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321928 := by omega
  have h2 := no_sum_sq_of_padic 800321928 3 0 266773976 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 5 = 588 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321592 := by omega
  have h2 := no_sum_sq_of_padic 800321592 3 0 266773864 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 6 = 1842 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320338 := by omega
  have h2 := no_sum_sq_of_padic 800320338 719 0 1113102 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 7 = 6561 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315619 := by omega
  have h2 := no_sum_sq_of_padic 800315619 3 0 266771873 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 8 = 24436 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297744 := by omega
  have h2 := no_sum_sq_of_padic 800297744 563 0 1421488 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 9 = 92504 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229676 := by omega
  have h2 := no_sum_sq_of_padic 800229676 200057419 0 4 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 10 = 352842 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969338 := by omega
  have h2 := no_sum_sq_of_padic 799969338 3 1 29628494 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 11 = 1352204 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798969976 := by omega
  have h2 := no_sum_sq_of_padic 798969976 7 0 114138568 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 12 = 5200426 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121754 := by omega
  have h2 := no_sum_sq_of_padic 795121754 7 0 113588822 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 13 = 20058426 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263754 := by omega
  have h2 := no_sum_sq_of_padic 780263754 3 0 260087918 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 14 = 77558886 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722763294 := by omega
  have h2 := no_sum_sq_of_padic 722763294 3 0 240921098 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_4_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 4 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 4 + B 15 = 300540321 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781859 := by omega
  have h2 := no_sum_sq_of_padic 499781859 3 0 166593953 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 0 = 463 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321717 := by omega
  have h2 := no_sum_sq_of_padic 800321717 467 0 1713751 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 1 = 465 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321715 := by omega
  have h2 := no_sum_sq_of_padic 800321715 3 3 365945 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 2 = 472 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321708 := by omega
  have h2 := no_sum_sq_of_padic 800321708 23 0 34796596 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 3 = 497 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321683 := by omega
  have h2 := no_sum_sq_of_padic 800321683 7 0 114331669 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 4 = 588 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321592 := by omega
  have h2 := no_sum_sq_of_padic 800321592 3 0 266773864 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 5 = 924 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800321256 := by omega
  have h2 := no_sum_sq_of_padic 800321256 3 1 29641528 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 6 = 2178 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320002 := by omega
  have h2 := no_sum_sq_of_padic 800320002 3 0 266773334 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 7 = 6897 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315283 := by omega
  have h2 := no_sum_sq_of_padic 800315283 3 0 266771761 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 8 = 24772 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297408 := by omega
  have h2 := no_sum_sq_of_padic 800297408 12504647 0 64 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 9 = 92840 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229340 := by omega
  have h2 := no_sum_sq_of_padic 800229340 23 0 34792580 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 10 = 353178 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969002 := by omega
  have h2 := no_sum_sq_of_padic 799969002 3 0 266656334 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 11 = 1352540 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798969640 := by omega
  have h2 := no_sum_sq_of_padic 798969640 7 0 114138520 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 12 = 5200762 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121418 := by omega
  have h2 := no_sum_sq_of_padic 795121418 7 0 113588774 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 13 = 20058762 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263418 := by omega
  have h2 := no_sum_sq_of_padic 780263418 3 0 260087806 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 14 = 77559222 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722762958 := by omega
  have h2 := no_sum_sq_of_padic 722762958 3 0 240920986 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_5_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 5 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 5 + B 15 = 300540657 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781523 := by omega
  have h2 := no_sum_sq_of_padic 499781523 3 0 166593841 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 0 = 1717 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320463 := by omega
  have h2 := no_sum_sq_of_padic 800320463 223 0 3588881 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 1 = 1719 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320461 := by omega
  have h2 := no_sum_sq_of_padic 800320461 3 0 266773487 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 2 = 1726 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320454 := by omega
  have h2 := no_sum_sq_of_padic 800320454 284003 0 2818 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 3 = 1751 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320429 := by omega
  have h2 := no_sum_sq_of_padic 800320429 43 0 18612103 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 4 = 1842 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320338 := by omega
  have h2 := no_sum_sq_of_padic 800320338 719 0 1113102 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 5 = 2178 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800320002 := by omega
  have h2 := no_sum_sq_of_padic 800320002 3 0 266773334 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 6 = 3432 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800318748 := by omega
  have h2 := no_sum_sq_of_padic 800318748 3 0 266772916 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 7 = 8151 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800314029 := by omega
  have h2 := no_sum_sq_of_padic 800314029 19 0 42121791 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 8 = 26026 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800296154 := by omega
  have h2 := no_sum_sq_of_padic 800296154 7 0 114328022 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 9 = 94094 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800228086 := by omega
  have h2 := no_sum_sq_of_padic 800228086 7 0 114318298 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 10 = 354432 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799967748 := by omega
  have h2 := no_sum_sq_of_padic 799967748 3 0 266655916 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 11 = 1353794 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798968386 := by omega
  have h2 := no_sum_sq_of_padic 798968386 139 0 5747974 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 12 = 5202016 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795120164 := by omega
  have h2 := no_sum_sq_of_padic 795120164 227 0 3502732 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 13 = 20060016 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780262164 := by omega
  have h2 := no_sum_sq_of_padic 780262164 11 0 70932924 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 14 = 77560476 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722761704 := by omega
  have h2 := no_sum_sq_of_padic 722761704 3 2 2974328 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_6_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 6 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 6 + B 15 = 300541911 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499780269 := by omega
  have h2 := no_sum_sq_of_padic 499780269 67 0 7459407 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 0 = 6436 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315744 := by omega
  have h2 := no_sum_sq_of_padic 800315744 991 0 807584 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 1 = 6438 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315742 := by omega
  have h2 := no_sum_sq_of_padic 800315742 3 0 266771914 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 2 = 6445 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315735 := by omega
  have h2 := no_sum_sq_of_padic 800315735 4326031 0 185 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 3 = 6470 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315710 := by omega
  have h2 := no_sum_sq_of_padic 800315710 5843 0 136970 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 4 = 6561 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315619 := by omega
  have h2 := no_sum_sq_of_padic 800315619 3 0 266771873 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 5 = 6897 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800315283 := by omega
  have h2 := no_sum_sq_of_padic 800315283 3 0 266771761 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 6 = 8151 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800314029 := by omega
  have h2 := no_sum_sq_of_padic 800314029 19 0 42121791 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 7 = 12870 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800309310 := by omega
  have h2 := no_sum_sq_of_padic 800309310 3 0 266769770 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 8 = 30745 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800291435 := by omega
  have h2 := no_sum_sq_of_padic 800291435 199 0 4021565 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 9 = 98813 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800223367 := by omega
  have h2 := no_sum_sq_of_padic 800223367 31 0 25813657 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 10 = 359151 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799963029 := by omega
  have h2 := no_sum_sq_of_padic 799963029 31 0 25805259 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 11 = 1358513 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798963667 := by omega
  have h2 := no_sum_sq_of_padic 798963667 3331 0 239857 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 12 = 5206735 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795115445 := by omega
  have h2 := no_sum_sq_of_padic 795115445 139 0 5720255 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 13 = 20064735 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780257445 := by omega
  have h2 := no_sum_sq_of_padic 780257445 3 0 260085815 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 14 = 77565195 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722756985 := by omega
  have h2 := no_sum_sq_of_padic 722756985 3 0 240918995 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_7_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 7 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 7 + B 15 = 300546630 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499775550 := by omega
  have h2 := no_sum_sq_of_padic 499775550 3 0 166591850 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 0 = 24311 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297869 := by omega
  have h2 := no_sum_sq_of_padic 800297869 7 0 114328267 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 1 = 24313 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297867 := by omega
  have h2 := no_sum_sq_of_padic 800297867 78607 0 10181 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 2 = 24320 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297860 := by omega
  have h2 := no_sum_sq_of_padic 800297860 19 0 42120940 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 3 = 24345 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297835 := by omega
  have h2 := no_sum_sq_of_padic 800297835 3 0 266765945 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 4 = 24436 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297744 := by omega
  have h2 := no_sum_sq_of_padic 800297744 563 0 1421488 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 5 = 24772 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800297408 := by omega
  have h2 := no_sum_sq_of_padic 800297408 12504647 0 64 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 6 = 26026 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800296154 := by omega
  have h2 := no_sum_sq_of_padic 800296154 7 0 114328022 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 7 = 30745 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800291435 := by omega
  have h2 := no_sum_sq_of_padic 800291435 199 0 4021565 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 8 = 48620 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800273560 := by omega
  have h2 := no_sum_sq_of_padic 800273560 689891 0 1160 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 9 = 116688 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800205492 := by omega
  have h2 := no_sum_sq_of_padic 800205492 3 0 266735164 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 10 = 377026 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799945154 := by omega
  have h2 := no_sum_sq_of_padic 799945154 223 0 3587198 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 11 = 1376388 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798945792 := by omega
  have h2 := no_sum_sq_of_padic 798945792 3 0 266315264 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 12 = 5224610 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795097570 := by omega
  have h2 := no_sum_sq_of_padic 795097570 59 0 13476230 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 13 = 20082610 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780239570 := by omega
  have h2 := no_sum_sq_of_padic 780239570 11 0 70930870 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 14 = 77583070 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722739110 := by omega
  have h2 := no_sum_sq_of_padic 722739110 7591 0 95210 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_8_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 8 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 8 + B 15 = 300564505 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499757675 := by omega
  have h2 := no_sum_sq_of_padic 499757675 19990307 0 25 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 0 = 92379 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229801 := by omega
  have h2 := no_sum_sq_of_padic 800229801 3 0 266743267 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 1 = 92381 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229799 := by omega
  have h2 := no_sum_sq_of_padic 800229799 27594131 0 29 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 2 = 92388 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229792 := by omega
  have h2 := no_sum_sq_of_padic 800229792 3 0 266743264 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 3 = 92413 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229767 := by omega
  have h2 := no_sum_sq_of_padic 800229767 7923067 0 101 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 4 = 92504 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229676 := by omega
  have h2 := no_sum_sq_of_padic 800229676 200057419 0 4 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 5 = 92840 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800229340 := by omega
  have h2 := no_sum_sq_of_padic 800229340 23 0 34792580 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 6 = 94094 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800228086 := by omega
  have h2 := no_sum_sq_of_padic 800228086 7 0 114318298 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 7 = 98813 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800223367 := by omega
  have h2 := no_sum_sq_of_padic 800223367 31 0 25813657 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 8 = 116688 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800205492 := by omega
  have h2 := no_sum_sq_of_padic 800205492 3 0 266735164 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 9 = 184756 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 800137424 := by omega
  have h2 := no_sum_sq_of_padic 800137424 19 0 42112496 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 10 = 445094 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799877086 := by omega
  have h2 := no_sum_sq_of_padic 799877086 887 0 901778 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 11 = 1444456 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798877724 := by omega
  have h2 := no_sum_sq_of_padic 798877724 19 0 42046196 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 12 = 5292678 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795029502 := by omega
  have h2 := no_sum_sq_of_padic 795029502 3 0 265009834 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 13 = 20150678 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780171502 := by omega
  have h2 := no_sum_sq_of_padic 780171502 11 0 70924682 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 14 = 77651138 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722671042 := by omega
  have h2 := no_sum_sq_of_padic 722671042 19 0 38035318 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_9_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 9 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 9 + B 15 = 300632573 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499689607 := by omega
  have h2 := no_sum_sq_of_padic 499689607 19 0 26299453 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 0 = 352717 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969463 := by omega
  have h2 := no_sum_sq_of_padic 799969463 23 0 34781281 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 1 = 352719 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969461 := by omega
  have h2 := no_sum_sq_of_padic 799969461 3 0 266656487 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 2 = 352726 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969454 := by omega
  have h2 := no_sum_sq_of_padic 799969454 399984727 0 2 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 3 = 352751 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969429 := by omega
  have h2 := no_sum_sq_of_padic 799969429 7 0 114281347 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 4 = 352842 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969338 := by omega
  have h2 := no_sum_sq_of_padic 799969338 3 1 29628494 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 5 = 353178 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799969002 := by omega
  have h2 := no_sum_sq_of_padic 799969002 3 0 266656334 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 6 = 354432 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799967748 := by omega
  have h2 := no_sum_sq_of_padic 799967748 3 0 266655916 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 7 = 359151 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799963029 := by omega
  have h2 := no_sum_sq_of_padic 799963029 31 0 25805259 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 8 = 377026 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799945154 := by omega
  have h2 := no_sum_sq_of_padic 799945154 223 0 3587198 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 9 = 445094 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799877086 := by omega
  have h2 := no_sum_sq_of_padic 799877086 887 0 901778 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 10 = 705432 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 799616748 := by omega
  have h2 := no_sum_sq_of_padic 799616748 3 0 266538916 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 11 = 1704794 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798617386 := by omega
  have h2 := no_sum_sq_of_padic 798617386 19 0 42032494 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 12 = 5553016 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 794769164 := by omega
  have h2 := no_sum_sq_of_padic 794769164 7 0 113538452 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 13 = 20411016 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 779911164 := by omega
  have h2 := no_sum_sq_of_padic 779911164 19 0 41047956 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 14 = 77911476 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722410704 := by omega
  have h2 := no_sum_sq_of_padic 722410704 3 1 26755952 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_10_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 10 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 10 + B 15 = 300892911 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499429269 := by omega
  have h2 := no_sum_sq_of_padic 499429269 19 0 26285751 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 0 = 1352079 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798970101 := by omega
  have h2 := no_sum_sq_of_padic 798970101 3 0 266323367 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 1 = 1352081 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798970099 := by omega
  have h2 := no_sum_sq_of_padic 798970099 31 0 25773229 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 2 = 1352088 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798970092 := by omega
  have h2 := no_sum_sq_of_padic 798970092 3 0 266323364 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 3 = 1352113 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798970067 := by omega
  have h2 := no_sum_sq_of_padic 798970067 7 0 114138581 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 4 = 1352204 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798969976 := by omega
  have h2 := no_sum_sq_of_padic 798969976 7 0 114138568 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 5 = 1352540 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798969640 := by omega
  have h2 := no_sum_sq_of_padic 798969640 7 0 114138520 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 6 = 1353794 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798968386 := by omega
  have h2 := no_sum_sq_of_padic 798968386 139 0 5747974 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 7 = 1358513 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798963667 := by omega
  have h2 := no_sum_sq_of_padic 798963667 3331 0 239857 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 8 = 1376388 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798945792 := by omega
  have h2 := no_sum_sq_of_padic 798945792 3 0 266315264 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 9 = 1444456 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798877724 := by omega
  have h2 := no_sum_sq_of_padic 798877724 19 0 42046196 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 10 = 1704794 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 798617386 := by omega
  have h2 := no_sum_sq_of_padic 798617386 19 0 42032494 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 11 = 2704156 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 797618024 := by omega
  have h2 := no_sum_sq_of_padic 797618024 7 0 113945432 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 12 = 6552378 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 793769802 := by omega
  have h2 := no_sum_sq_of_padic 793769802 3 0 264589934 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 13 = 21410378 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 778911802 := by omega
  have h2 := no_sum_sq_of_padic 778911802 19 0 40995358 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 14 = 78910838 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 721411342 := by omega
  have h2 := no_sum_sq_of_padic 721411342 19 0 37969018 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_11_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 11 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 11 + B 15 = 301892273 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 498429907 := by omega
  have h2 := no_sum_sq_of_padic 498429907 19 0 26233153 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 0 = 5200301 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121879 := by omega
  have h2 := no_sum_sq_of_padic 795121879 887 0 896417 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 1 = 5200303 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121877 := by omega
  have h2 := no_sum_sq_of_padic 795121877 11 0 72283807 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 2 = 5200310 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121870 := by omega
  have h2 := no_sum_sq_of_padic 795121870 79512187 0 10 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 3 = 5200335 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121845 := by omega
  have h2 := no_sum_sq_of_padic 795121845 3 0 265040615 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 4 = 5200426 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121754 := by omega
  have h2 := no_sum_sq_of_padic 795121754 7 0 113588822 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 5 = 5200762 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795121418 := by omega
  have h2 := no_sum_sq_of_padic 795121418 7 0 113588774 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 6 = 5202016 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795120164 := by omega
  have h2 := no_sum_sq_of_padic 795120164 227 0 3502732 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 7 = 5206735 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795115445 := by omega
  have h2 := no_sum_sq_of_padic 795115445 139 0 5720255 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 8 = 5224610 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795097570 := by omega
  have h2 := no_sum_sq_of_padic 795097570 59 0 13476230 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 9 = 5292678 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 795029502 := by omega
  have h2 := no_sum_sq_of_padic 795029502 3 0 265009834 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 10 = 5553016 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 794769164 := by omega
  have h2 := no_sum_sq_of_padic 794769164 7 0 113538452 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 11 = 6552378 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 793769802 := by omega
  have h2 := no_sum_sq_of_padic 793769802 3 0 264589934 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 12 = 10400600 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 789921580 := by omega
  have h2 := no_sum_sq_of_padic 789921580 7 0 112845940 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 13 = 25258600 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 775063580 := by omega
  have h2 := no_sum_sq_of_padic 775063580 19 0 40792820 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 14 = 82759060 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 717563120 := by omega
  have h2 := no_sum_sq_of_padic 717563120 19 0 37766480 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_12_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 12 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 12 + B 15 = 305740495 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 494581685 := by omega
  have h2 := no_sum_sq_of_padic 494581685 19 0 26030615 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 0 = 20058301 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263879 := by omega
  have h2 := no_sum_sq_of_padic 780263879 26905651 0 29 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 1 = 20058303 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263877 := by omega
  have h2 := no_sum_sq_of_padic 780263877 3 0 260087959 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 2 = 20058310 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263870 := by omega
  have h2 := no_sum_sq_of_padic 780263870 127 0 6143810 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 3 = 20058335 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263845 := by omega
  have h2 := no_sum_sq_of_padic 780263845 23 0 33924515 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 4 = 20058426 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263754 := by omega
  have h2 := no_sum_sq_of_padic 780263754 3 0 260087918 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 5 = 20058762 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780263418 := by omega
  have h2 := no_sum_sq_of_padic 780263418 3 0 260087806 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 6 = 20060016 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780262164 := by omega
  have h2 := no_sum_sq_of_padic 780262164 11 0 70932924 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 7 = 20064735 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780257445 := by omega
  have h2 := no_sum_sq_of_padic 780257445 3 0 260085815 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 8 = 20082610 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780239570 := by omega
  have h2 := no_sum_sq_of_padic 780239570 11 0 70930870 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 9 = 20150678 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 780171502 := by omega
  have h2 := no_sum_sq_of_padic 780171502 11 0 70924682 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 10 = 20411016 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 779911164 := by omega
  have h2 := no_sum_sq_of_padic 779911164 19 0 41047956 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 11 = 21410378 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 778911802 := by omega
  have h2 := no_sum_sq_of_padic 778911802 19 0 40995358 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 12 = 25258600 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 775063580 := by omega
  have h2 := no_sum_sq_of_padic 775063580 19 0 40792820 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 13 = 40116600 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 760205580 := by omega
  have h2 := no_sum_sq_of_padic 760205580 3 0 253401860 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 14 = 97617060 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 702705120 := by omega
  have h2 := no_sum_sq_of_padic 702705120 3 0 234235040 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_13_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 13 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 13 + B 15 = 320598495 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 479723685 := by omega
  have h2 := no_sum_sq_of_padic 479723685 3 0 159907895 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 0 = 77558761 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722763419 := by omega
  have h2 := no_sum_sq_of_padic 722763419 7 0 103251917 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 1 = 77558763 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722763417 := by omega
  have h2 := no_sum_sq_of_padic 722763417 3 0 240921139 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 2 = 77558770 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722763410 := by omega
  have h2 := no_sum_sq_of_padic 722763410 2819 0 256390 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 3 = 77558795 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722763385 := by omega
  have h2 := no_sum_sq_of_padic 722763385 23 0 31424495 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 4 = 77558886 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722763294 := by omega
  have h2 := no_sum_sq_of_padic 722763294 3 0 240921098 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 5 = 77559222 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722762958 := by omega
  have h2 := no_sum_sq_of_padic 722762958 3 0 240920986 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 6 = 77560476 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722761704 := by omega
  have h2 := no_sum_sq_of_padic 722761704 3 2 2974328 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 7 = 77565195 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722756985 := by omega
  have h2 := no_sum_sq_of_padic 722756985 3 0 240918995 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 8 = 77583070 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722739110 := by omega
  have h2 := no_sum_sq_of_padic 722739110 7591 0 95210 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 9 = 77651138 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722671042 := by omega
  have h2 := no_sum_sq_of_padic 722671042 19 0 38035318 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 10 = 77911476 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 722410704 := by omega
  have h2 := no_sum_sq_of_padic 722410704 3 1 26755952 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 11 = 78910838 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 721411342 := by omega
  have h2 := no_sum_sq_of_padic 721411342 19 0 37969018 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 12 = 82759060 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 717563120 := by omega
  have h2 := no_sum_sq_of_padic 717563120 19 0 37766480 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 13 = 97617060 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 702705120 := by omega
  have h2 := no_sum_sq_of_padic 702705120 3 0 234235040 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 14 = 155117520 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 645204660 := by omega
  have h2 := no_sum_sq_of_padic 645204660 3 0 215068220 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_14_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 14 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 14 + B 15 = 378098955 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 422223225 := by omega
  have h2 := no_sum_sq_of_padic 422223225 3 0 140741075 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_0 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 0 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 0 = 300540196 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781984 := by omega
  have h2 := no_sum_sq_of_padic 499781984 1999 0 250016 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_1 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 1 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 1 = 300540198 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781982 := by omega
  have h2 := no_sum_sq_of_padic 499781982 3 0 166593994 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_2 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 2 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 2 = 300540205 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781975 := by omega
  have h2 := no_sum_sq_of_padic 499781975 7 0 71397425 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_3 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 3 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 3 = 300540230 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781950 := by omega
  have h2 := no_sum_sq_of_padic 499781950 23 0 21729650 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_4 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 4 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 4 = 300540321 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781859 := by omega
  have h2 := no_sum_sq_of_padic 499781859 3 0 166593953 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_5 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 5 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 5 = 300540657 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499781523 := by omega
  have h2 := no_sum_sq_of_padic 499781523 3 0 166593841 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_6 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 6 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 6 = 300541911 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499780269 := by omega
  have h2 := no_sum_sq_of_padic 499780269 67 0 7459407 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_7 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 7 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 7 = 300546630 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499775550 := by omega
  have h2 := no_sum_sq_of_padic 499775550 3 0 166591850 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_8 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 8 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 8 = 300564505 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499757675 := by omega
  have h2 := no_sum_sq_of_padic 499757675 19990307 0 25 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_9 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 9 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 9 = 300632573 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499689607 := by omega
  have h2 := no_sum_sq_of_padic 499689607 19 0 26299453 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_10 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 10 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 10 = 300892911 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 499429269 := by omega
  have h2 := no_sum_sq_of_padic 499429269 19 0 26285751 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_11 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 11 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 11 = 301892273 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 498429907 := by omega
  have h2 := no_sum_sq_of_padic 498429907 19 0 26233153 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_12 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 12 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 12 = 305740495 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 494581685 := by omega
  have h2 := no_sum_sq_of_padic 494581685 19 0 26030615 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_13 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 13 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 13 = 320598495 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 479723685 := by omega
  have h2 := no_sum_sq_of_padic 479723685 3 0 159907895 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_14 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 14 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 14 = 378098955 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 422223225 := by omega
  have h2 := no_sum_sq_of_padic 422223225 3 0 140741075 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1

lemma no_sol_15_15 (a b : ℕ) : a ^ 2 + b ^ 2 + B 15 + B 15 ≠ 800322180 := by
  intro h
  have hB : B 15 + B 15 = 601080390 := by rfl
  have h1 : a ^ 2 + b ^ 2 = 199241790 := by omega
  have h2 := no_sum_sq_of_padic 199241790 3 0 66413930 (by decide) (by norm_num) (by rfl) (by decide) (by decide) a b
  exact h2 h1


lemma B_step (c : ℕ) : B c < B (c + 1) := by
  dsimp [B]
  have h1 : 2 * (c + 1) + 1 = 2 * c + 2 + 1 := by omega
  rw [h1, Nat.choose_succ_succ' (2 * c + 2) c]
  have h2 : 2 * c + 2 = 2 * c + 1 + 1 := by omega
  rw [h2, Nat.choose_succ_succ' (2 * c + 1) c]
  have hpos : 0 < (2 * c + 1 + 1).choose c := by
    apply Nat.choose_pos
    omega
  set X := (2 * c + 1).choose c
  set Y := (2 * c + 1).choose (c + 1)
  set Z := (2 * c + 1 + 1).choose c
  omega

lemma B_ge_16 (c : ℕ) (hc : 16 ≤ c) : B c > 800322180 := by
  induction' c, hc using Nat.le_induction with k hk ih
  · decide
  · exact lt_trans ih (B_step k)
