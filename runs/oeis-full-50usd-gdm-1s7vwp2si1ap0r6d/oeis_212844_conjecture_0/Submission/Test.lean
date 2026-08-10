import FormalConjectures.Util.ProblemImports

open Function


def a : ℕ → ℕ
| 0     => 0
| (n+1) => (2 ^ ((n + 1) + 2)) % (n + 1)

lemma pow_mod_step (a p B q r : ℕ) (hB : a ^ B ≡ 1 [MOD p]) :
    a ^ (B * q + r) ≡ a ^ r [MOD p] := by
  rw [Nat.pow_add, Nat.pow_mul]
  have h1 : (a ^ B) ^ q ≡ 1 ^ q [MOD p] := Nat.ModEq.pow q hB
  simp only [one_pow] at h1
  have h2 : (a ^ B) ^ q * a ^ r ≡ 1 * a ^ r [MOD p] := Nat.ModEq.mul h1 Nat.ModEq.rfl
  rw [one_mul] at h2
  exact h2

lemma pow_mod_rem (a p A B : ℕ) (hA : a ^ A ≡ 1 [MOD p]) (hB : a ^ B ≡ 1 [MOD p]) :
    a ^ (A % B) ≡ 1 [MOD p] := by
  have h_eq : A = B * (A / B) + A % B := (Nat.div_add_mod A B).symm
  have h_step := pow_mod_step a p B (A / B) (A % B) hB
  rw [← h_eq] at h_step
  exact h_step.symm.trans hA

theorem pow_mod_gcd (a p A B : ℕ) (hA : a ^ A ≡ 1 [MOD p]) (hB : a ^ B ≡ 1 [MOD p]) :
    a ^ (Nat.gcd A B) ≡ 1 [MOD p] := by
  by_cases hA_zero : A = 0
  · subst hA_zero
    rw [Nat.gcd_zero_left]
    exact hB
  · rw [Nat.gcd_rec]
    have h_rem := pow_mod_rem a p B A hB hA
    exact pow_mod_gcd a p (B % A) A h_rem hA
termination_by A
decreasing_by exact Nat.mod_lt B (Nat.pos_of_ne_zero hA_zero)

lemma gcd_g_n_eq_one {g n p : ℕ} (hp : p.Prime) (hg : g ∣ p - 1)
    (h_smallest : ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q) : Nat.gcd g n = 1 := by
  by_contra hc
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hc
  have hq_g : q ∣ g := hq_dvd.trans (Nat.gcd_dvd_left g n)
  have hq_n : q ∣ n := hq_dvd.trans (Nat.gcd_dvd_right g n)
  have hq_p1 : q ∣ p - 1 := hq_g.trans hg
  have h_p1_pos : p - 1 > 0 := by
    have : p ≥ 2 := hp.two_le
    omega
  have hq_le_p1 : q ≤ p - 1 := Nat.le_of_dvd h_p1_pos hq_p1
  have hq_lt_p : q < p := by omega
  have hq_ge_p : p ≤ q := h_smallest q hq_prime hq_n
  omega

lemma pow_mod_flt (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ^ k ≡ 2 ^ (k % (p - 1)) [MOD p] := by
  have h_coprime : Nat.Coprime 2 p := by
    have h1 : Nat.Coprime p 2 := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hdvd
      have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
      have hp_ge : p ≥ 2 := hp.two_le
      omega
    exact h1.symm
  have h_flt := Nat.ModEq.pow_card_sub_one_eq_one hp h_coprime
  have h_eq : k = (p - 1) * (k / (p - 1)) + k % (p - 1) := (Nat.div_add_mod k (p - 1)).symm
  have h_step := pow_mod_step 2 p (p - 1) (k / (p - 1)) (k % (p - 1)) h_flt
  rw [← h_eq] at h_step
  exact h_step

lemma not_power_of_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h : ∀ r < p - 1, 2 ^ r % p ≠ 69 % p) :
    ∀ k, 2 ^ k % p ≠ 69 % p := by
  intro k hc
  have h_modeq := pow_mod_flt p k hp hp2
  rw [Nat.ModEq] at h_modeq
  rw [h_modeq] at hc
  have h_lt : k % (p - 1) < p - 1 := by
    apply Nat.mod_lt
    have : p ≥ 2 := hp.two_le
    omega
  have h_not := h (k % (p - 1)) h_lt
  exact h_not hc

lemma minFac_is_smallest {n q : ℕ} (hq : q.Prime) (hdvd : q ∣ n) : n.minFac ≤ q :=
  Nat.minFac_le_of_dvd hq.two_le hdvd

lemma gt_69_of_a_eq_69 (n : ℕ) (h : a n = 69) : n > 69 := by
  cases n with
  | zero =>
    simp [a] at h
  | succ n =>
    have h_a_def : a (n + 1) = (2 ^ (n + 3)) % (n + 1) := rfl
    rw [h_a_def] at h
    have h_lt : (2 ^ (n + 3)) % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    omega

lemma pow_mod_prime_of_a_eq_69 {n p : ℕ} (h : a n = 69) (hp : p ∣ n) : (2 ^ (n + 2)) % p = 69 % p := by
  have h_gt : n > 69 := gt_69_of_a_eq_69 n h
  cases n with
  | zero => omega
  | succ m =>
    have h_a_def : a (m + 1) = (2 ^ (m + 3)) % (m + 1) := rfl
    have h_eq : m + 3 = (m + 1) + 2 := by omega
    rw [h_a_def] at h
    have h_mod := (Nat.mod_mod_of_dvd (2 ^ (m + 3)) hp).symm
    rw [h_mod, h]


lemma prime_not_dvd_of_not_power_of_two (n : ℕ) (p : ℕ) (hp : p.Prime) (hp_ne_2 : p ≠ 2)
    (h_not_pow : ∀ r < p - 1, 2 ^ r % p ≠ 69 % p) (hn : a n = 69) : ¬ (p ∣ n) := by
  intro hdvd
  have h_mod := pow_mod_prime_of_a_eq_69 hn hdvd
  have h_all := not_power_of_two p hp hp_ne_2 h_not_pow
  have h_not_pow_n2 := h_all (n + 2)
  exact h_not_pow_n2 h_mod

lemma mod_19_cases (k : ℕ) (h : 2 ^ k % 19 = 69 % 19) : k % 18 = 15 := by
  have h_flt := pow_mod_flt 19 k (by decide) (by decide)
  rw [Nat.ModEq] at h_flt
  rw [h_flt] at h
  have h_lt : k % 18 < 18 := Nat.mod_lt _ (by decide)
  generalize k % 18 = r at h_lt h
  revert r h_lt h
  decide







def check_range_bin_fuel (fuel start len : ℕ) : Bool :=
  match fuel with
  | 0 => len == 0
  | f + 1 =>
    if len = 0 then true
    else if len = 1 then (a start != 69)
    else
      let half := len / 2
      check_range_bin_fuel f start half && check_range_bin_fuel f (start + half) (len - half)

lemma check_range_bin_fuel_correct (fuel start len : ℕ) (h_fuel : len ≤ 2 ^ fuel)
    (h : check_range_bin_fuel fuel start len = true) :
    ∀ i < len, a (start + i) ≠ 69 := by
  induction fuel generalizing start len with
  | zero =>
    unfold check_range_bin_fuel at h
    have : len = 0 := by
      cases len with
      | zero => rfl
      | succ n => simp at h
    subst this
    intro i hi
    omega
  | succ f ih =>
    by_cases h_len0 : len = 0
    · subst h_len0
      intro i hi
      omega
    · by_cases h_len1 : len = 1
      · subst h_len1
        intro i hi
        have : i = 0 := by omega
        subst this
        rw [Nat.add_zero]
        unfold check_range_bin_fuel at h
        simp [h_len0] at h
        intro hc
        rw [hc] at h
        contradiction
      · unfold check_range_bin_fuel at h
        simp [h_len0, h_len1] at h
        rcases h with ⟨h1, h2⟩
        have h_pow : 2 ^ (f + 1) = 2 ^ f * 2 := by ring
        rw [h_pow] at h_fuel
        have h_eq_div : len = 2 * (len / 2) + len % 2 := (Nat.div_add_mod len 2).symm
        have h_mod_lt : len % 2 < 2 := Nat.mod_lt _ (by decide)
        have h_sub : len - len / 2 = len / 2 + len % 2 := by omega
        have h_half_lt : len / 2 ≤ 2 ^ f := by omega
        have h_rem_lt : len - len / 2 ≤ 2 ^ f := by omega
        intro i hi
        by_cases h_half : i < len / 2
        · exact ih start (len / 2) h_half_lt h1 i h_half
        · have h_rec := ih (start + len / 2) (len - len / 2) h_rem_lt h2 (i - len / 2) (by omega)
          have : start + len / 2 + (i - len / 2) = start + i := by omega
          rw [this] at h_rec
          exact h_rec

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000
theorem a_not_69_lt_100489 : ∀ n < 100489, a n ≠ 69 := by
  intro n hn
  have h_check : check_range_bin_fuel 20 0 100489 = true := by decide
  have h_corr := check_range_bin_fuel_correct 20 0 100489 (by decide) h_check n hn
  rw [Nat.zero_add] at h_corr
  exact h_corr
