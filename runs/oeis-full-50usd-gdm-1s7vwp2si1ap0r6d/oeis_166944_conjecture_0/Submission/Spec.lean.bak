import FormalConjectures.Util.ProblemImports

/--
A166944: $a(1)=2$; $a(n) = a(n-1) + \gcd(n, a(n-1))$ if $n$ is even, $a(n) = a(n-1) + \gcd(n-2, a(n-1))$ if $n$ is odd.
-/
def a : ℕ → ℕ
| 0 => 0
| 1 => 2
| n + 1 => -- Defines a(n+1) in terms of a(n) for n >= 1. Current index is n+1 >= 2.
  let current_idx := n + 1
  let prev_a := a n
  if current_idx % 2 = 0 then
    prev_a + Nat.gcd current_idx prev_a
  else
    -- Since current_idx is odd and >= 3, current_idx - 2 is safely in ℕ.
    prev_a + Nat.gcd (current_idx - 2) prev_a

-- Start of the conjecture formalization

/-- The difference sequence $d_n = a(n) - a(n-1)$. D is defined for n >= 2. -/
def d (n : ℕ) : ℕ := a n - a (n-1)

/-- A natural number `p` is the greater of a twin prime pair if `p` is prime and `p - 2` is prime. -/
def is_greater_twin_prime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p - 2)

/-- A value `R : ℕ` is a record for the sequence of differences `d(n)` if
there exists an index `n` such that $d(n)=R$, and $R$ is strictly larger
than all previous differences.
The sequence of differences starts at n=2.
-/
def is_difference_record (R : ℕ) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ d n = R ∧ (∀ k : ℕ, 2 ≤ k ∧ k < n → d k < R)

lemma gcd_odd_right (a b : ℕ) (hb : b % 2 = 1) : Nat.gcd a b % 2 = 1 := by
  have h_dvd : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
  rcases h_dvd with ⟨k, hk⟩
  rw [hk] at hb
  rw [Nat.mul_mod] at hb
  have h1 : Nat.gcd a b % 2 < 2 := Nat.mod_lt _ (by decide)
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases h : Nat.gcd a b % 2
  · simp at hb
  · rfl

lemma gcd_odd_left (a b : ℕ) (ha : a % 2 = 1) : Nat.gcd a b % 2 = 1 := by
  rw [Nat.gcd_comm]
  exact gcd_odd_right b a ha

lemma a_parity : ∀ n : ℕ, 2 ≤ n → a n % 2 = n % 2 := by
  intro n hn
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases hn1 : n = 1
    · subst hn1
      rfl
    · have hn2 : 2 ≤ n := by omega
      have ih_hyp := ih hn2
      have h_step : a (n+1) =
        let current_idx := n + 1
        let prev_a := a n
        if current_idx % 2 = 0 then
          prev_a + Nat.gcd current_idx prev_a
        else
          prev_a + Nat.gcd (current_idx - 2) prev_a := by
        rw [a]
        omega
      rw [h_step]
      dsimp only
      by_cases h_even : (n+1) % 2 = 0
      · rw [if_pos h_even]
        rw [Nat.add_mod, ih_hyp]
        have h_odd : a n % 2 = 1 := by omega
        rw [gcd_odd_right (n+1) (a n) h_odd]
        omega
      · rw [if_neg h_even]
        rw [Nat.add_mod, ih_hyp]
        have h_even_an : a n % 2 = 0 := by omega
        have h_odd_idx : (n + 1 - 2) % 2 = 1 := by omega
        rw [gcd_odd_left (n + 1 - 2) (a n) h_odd_idx]
        omega

lemma odd_div_even_le {d n : ℕ} (hn : n % 2 = 0) (hd : d % 2 = 1) (hdvd : d ∣ n) (hn0 : 0 < n) : d ≤ n / 2 := by
  rcases hdvd with ⟨k, rfl⟩
  have h_even : (d * k) % 2 = 0 := hn
  rw [Nat.mul_mod] at h_even
  have h_d_mod : d % 2 = 1 := hd
  rw [h_d_mod] at h_even
  simp at h_even
  have hk_even : k % 2 = 0 := h_even
  have hk_dvd : 2 ∣ k := Nat.dvd_of_mod_eq_zero hk_even
  rcases hk_dvd with ⟨j, rfl⟩
  have hj0 : 0 < j := by
    by_contra hc
    have : j = 0 := by omega
    subst this
    omega
  have : d * (2 * j) = 2 * d * j := by ring
  rw [this]
  have : 2 * d ≤ 2 * d * j := Nat.le_mul_of_pos_right _ hj0
  omega

lemma d_le_sub_two (n : ℕ) (hn : 3 ≤ n) : d n ≤ n - 2 := by
  unfold d
  have h_step : a n =
    let current_idx := n
    let prev_a := a (n-1)
    if current_idx % 2 = 0 then
      prev_a + Nat.gcd current_idx prev_a
    else
      prev_a + Nat.gcd (current_idx - 2) prev_a := by
    induction n with
    | zero => contradiction
    | succ m ih =>
      rw [a]
      congr
      omega
  rw [h_step]
  dsimp only
  by_cases h_even : n % 2 = 0
  · rw [if_pos h_even]
    have h_cancel : a (n-1) + Nat.gcd n (a (n-1)) - a (n-1) = Nat.gcd n (a (n-1)) := by omega
    rw [h_cancel]
    -- gcd n (a (n-1)) ≤ n - 2
    have h_odd : a (n-1) % 2 = 1 := by
      have : 2 ≤ n - 1 := by omega
      have := a_parity (n-1) this
      omega
    have h_gcd_odd : Nat.gcd n (a (n-1)) % 2 = 1 := gcd_odd_right n (a (n-1)) h_odd
    have h_dvd : Nat.gcd n (a (n-1)) ∣ n := Nat.gcd_dvd_left n (a (n-1))
    have h_le := odd_div_even_le h_even h_gcd_odd h_dvd (by omega)
    omega
  · rw [if_neg h_even]
    have h_cancel : a (n-1) + Nat.gcd (n-2) (a (n-1)) - a (n-1) = Nat.gcd (n-2) (a (n-1)) := by omega
    rw [h_cancel]
    -- gcd (n-2) (a (n-1)) ≤ n - 2
    have h_pos : 0 < n - 2 := by omega
    have h_le := Nat.gcd_le_left (a (n-1)) h_pos
    exact h_le

lemma a_le_succ (n : ℕ) : a n ≤ a (n+1) := by
  by_cases h0 : n = 0
  · subst h0; decide
  · have h_step : a (n+1) =
        let current_idx := n + 1
        let prev_a := a n
        if current_idx % 2 = 0 then
          prev_a + Nat.gcd current_idx prev_a
        else
          prev_a + Nat.gcd (current_idx - 2) prev_a := by
        rw [a]
        omega
    rw [h_step]
    dsimp only
    by_cases h_even : (n+1) % 2 = 0
    · rw [if_pos h_even]; omega
    · rw [if_neg h_even]; omega

lemma a_mono (m n : ℕ) (h : m ≤ n) : a m ≤ a n := by
  induction h with
  | refl => rfl
  | step h_le ih =>
    exact le_trans ih (a_le_succ _)

lemma d_odd (n : ℕ) (hn : 3 ≤ n) : d n % 2 = 1 := by
  unfold d
  have hn2 : 2 ≤ n := by omega
  have hn1 : 2 ≤ n - 1 := by omega
  have h1 := a_parity n hn2
  have h2 := a_parity (n-1) hn1
  have h_mono : a (n-1) ≤ a n := by
    apply a_mono
    omega
  omega

lemma record_odd {R : ℕ} (hR : 5 < R) (hr : is_difference_record R) : R % 2 = 1 := by
  rcases hr with ⟨n, hn, rfl, h_rec⟩
  have hn3 : 3 ≤ n := by
    by_contra! hc
    interval_cases n
    · -- n = 2
      -- d 2 = 2, so R = 2, contradicting 5 < R
      have hd2 : d 2 = 2 := rfl
      omega
  exact d_odd n hn3


lemma a_strict_mono (n : ℕ) : a n < a (n+1) := by
  by_cases h0 : n = 0
  · subst h0; decide
  · have h_step : a (n+1) =
        let current_idx := n + 1
        let prev_a := a n
        if current_idx % 2 = 0 then
          prev_a + Nat.gcd current_idx prev_a
        else
          prev_a + Nat.gcd (current_idx - 2) prev_a := by
        rw [a]
        omega
    rw [h_step]
    dsimp only
    by_cases h_even : (n+1) % 2 = 0
    · rw [if_pos h_even]
      have h_pos : 0 < Nat.gcd (n+1) (a n) := by
        apply Nat.gcd_pos_of_pos_left
        omega
      omega
    · rw [if_neg h_even]
      have h_pos : 0 < Nat.gcd (n+1-2) (a n) := by
        apply Nat.gcd_pos_of_pos_left
        omega
      omega

lemma a_ge_self (n : ℕ) : n ≤ a n := by
  induction n with
  | zero => omega
  | succ m ih =>
    have h1 := a_strict_mono m
    omega

lemma D_even (n : ℕ) (hn : 2 ≤ n) : (a n - n) % 2 = 0 := by
  have hp := a_parity n hn
  have h_ge := a_ge_self n
  omega

lemma d_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ d n := by
  unfold d
  have h1 := a_strict_mono (n-1)
  have : n - 1 + 1 = n := by omega
  rw [this] at h1
  omega

lemma D_mono (n : ℕ) (hn : 2 ≤ n) : a (n-1) - (n-1) ≤ a n - n := by
  have h_mono := a_strict_mono (n-1)
  have : n - 1 + 1 = n := by omega
  rw [this] at h_mono
  have h_ge := a_ge_self (n-1)
  omega

/--
Conjecture: Every record of differences $a(n)-a(n-1)$ more than 5 is the greater of twin primes (A006512).
-/
lemma d_eq_gcd (n : ℕ) (hn : 2 ≤ n) :
  d n = if n % 2 = 0 then Nat.gcd n (a (n-1)) else Nat.gcd (n-2) (a (n-1)) := by
  unfold d
  have h_step : a n =
    if n % 2 = 0 then
      a (n-1) + Nat.gcd n (a (n-1))
    else
      a (n-1) + Nat.gcd (n-2) (a (n-1)) := by
    induction n with
    | zero => contradiction
    | succ m ih =>
      rw [a]
      congr
      omega
  rw [h_step]
  split_ifs with h_even
  · rw [Nat.add_sub_cancel_left]
  · rw [Nat.add_sub_cancel_left]

lemma cases_of_record_index (R n : ℕ) (hR : 5 < R) (hr : is_difference_record R) (hn2 : 2 ≤ n) (hn : d n = R) :
  n = R + 2 ∨ (n ≥ 2 * R) := by
  have h_R_odd : R % 2 = 1 := record_odd hR hr
  have hn3 : 3 ≤ n := by
    by_contra! hc
    have : n = 2 := by omega
    subst this
    have hd2 : d 2 = 2 := rfl
    omega
  have hd_eq := d_eq_gcd n hn2
  rw [hn] at hd_eq
  by_cases h_even : n % 2 = 0
  · rw [if_pos h_even] at hd_eq
    have hdvd : Nat.gcd n (a (n-1)) ∣ n := Nat.gcd_dvd_left n (a (n-1))
    rw [← hd_eq] at hdvd
    rcases hdvd with ⟨c, hc⟩
    have h_mod : (R * c) % 2 = c % 2 := by
      rw [Nat.mul_mod, h_R_odd]
      simp
    have hc_even : c % 2 = 0 := by omega
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp [hc] at hn3
    have hc_ge : 2 ≤ c := by omega
    right
    have h1 : R * 2 ≤ R * c := Nat.mul_le_mul_left R hc_ge
    rw [Nat.mul_comm R 2] at h1
    rw [← hc] at h1
    omega
  · rw [if_neg h_even] at hd_eq
    have hdvd : Nat.gcd (n-2) (a (n-1)) ∣ n - 2 := Nat.gcd_dvd_left (n-2) (a (n-1))
    rw [← hd_eq] at hdvd
    rcases hdvd with ⟨c, hc⟩
    have hn_sub_odd : (n-2) % 2 = 1 := by omega
    have h_mod : (R * c) % 2 = c % 2 := by
      rw [Nat.mul_mod, h_R_odd]
      simp
    have hc_odd : c % 2 = 1 := by omega
    by_cases hc1 : c = 1
    · subst hc1
      left
      omega
    · have hc_ge : 3 ≤ c := by omega
      right
      have h1 : R * 3 ≤ R * c := Nat.mul_le_mul_left R hc_ge
      rw [Nat.mul_comm R 3] at h1
      rw [← hc] at h1
      omega



lemma gcd_eq_left_of_dvd {m n : ℕ} (hpos : 0 < m) (hdvd : m ∣ n) : Nat.gcd m n = m := by
  have h1 : Nat.gcd m n ≤ m := Nat.gcd_le_left n hpos
  have h2 : m ∣ Nat.gcd m n := Nat.dvd_gcd (dvd_refl m) hdvd
  have h3 : m ≤ Nat.gcd m n := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left n hpos) h2
  omega

lemma minFac_sq_le (n : ℕ) (hn : 2 ≤ n) (hc : ¬ n.Prime) : n.minFac * n.minFac ≤ n := by
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  rcases hdvd with ⟨k, hk⟩
  have hk_pos : 0 < k := by
    by_contra hc0
    have : k = 0 := by omega
    subst this
    omega
  have h_min : n.minFac ≤ k := by
    by_contra! h_lt
    by_cases hk1 : k = 1
    · subst hk1
      have hkn1 : n = n.minFac := by omega
      have hn1 : n ≠ 1 := by omega
      have h_prime_min := Nat.minFac_prime hn1
      rw [← hkn1] at h_prime_min
      exact hc h_prime_min
    · -- k has a prime factor, which must be >= n.minFac
      have hk_ge : 2 ≤ k := by omega
      let p := k.minFac
      have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
      have hp2 : 2 ≤ p := hp_prime.two_le
      have hp_dvd : p ∣ k := Nat.minFac_dvd k
      have hp_dvd_n : p ∣ n := by
        rw [hk]
        exact dvd_mul_of_dvd_right hp_dvd n.minFac
      have hp_ge_min : n.minFac ≤ p := Nat.minFac_le_of_dvd hp2 hp_dvd_n
      have hp_le_k : p ≤ k := Nat.minFac_le (by omega)
      omega
  conv_rhs => rw [hk]
  exact Nat.mul_le_mul_left n.minFac h_min

lemma D_ge_sub_two : ∀ k : ℕ, 3 ≤ k → a k - k ≥ k - 2 := by
  intro k
  induction' k using Nat.strong_induction_on with k ih
  intro hk
  by_cases hk5 : k < 5
  · interval_cases k
    · decide
    · decide
  · have hk_ge : 5 ≤ k := by omega
    have hk_prev : 3 ≤ k - 1 := by omega
    have ih_prev := ih (k-1) (by omega) hk_prev
    have h_mono : a (k-1) - (k-1) ≤ a k - k := D_mono k (by omega)
    by_cases h_case : a (k-1) - (k-1) ≥ k - 2
    · omega
    · have h_eq : a (k-1) - (k-1) = k - 3 := by omega
      have h_ak1 : a (k-1) = 2*k - 4 := by
        have : k - 1 ≤ a (k-1) := a_ge_self (k-1)
        omega
      by_cases h_even : k % 2 = 0
      · have hd_eq : d k = Nat.gcd k (a (k-1)) := by
          have hd_eq_g := d_eq_gcd k (by omega)
          rw [hd_eq_g, if_pos h_even]
        rw [h_ak1] at hd_eq
        have hdvd1 : 2 ∣ k := Nat.dvd_of_mod_eq_zero h_even
        have hdvd2 : 2 ∣ 2*k - 4 := by
          use k - 2
          omega
        have h_gcd_dvd : 2 ∣ Nat.gcd k (2*k - 4) := Nat.dvd_gcd hdvd1 hdvd2
        have h_gcd_pos : 0 < Nat.gcd k (2*k - 4) := by
          apply Nat.gcd_pos_of_pos_left
          omega
        have h_gcd_ge : 2 ≤ Nat.gcd k (2*k - 4) := Nat.le_of_dvd h_gcd_pos h_gcd_dvd
        unfold d at hd_eq
        omega
      · have hd_eq : d k = Nat.gcd (k-2) (a (k-1)) := by
          have hd_eq_g := d_eq_gcd k (by omega)
          rw [hd_eq_g, if_neg h_even]
        rw [h_ak1] at hd_eq
        have h_dvd : (k-2) ∣ 2*k - 4 := by
          use 2
          omega
        have h_gcd_eq : Nat.gcd (k-2) (2*k - 4) = k-2 := gcd_eq_left_of_dvd (by omega) h_dvd
        rw [h_gcd_eq] at hd_eq
        unfold d at hd_eq
        omega


lemma a_eq_prev_add_d (k : ℕ) (hk : 1 ≤ k) : a k = a (k-1) + d k := by
  unfold d
  have h_mono : a (k-1) ≤ a k := a_mono (k-1) k (by omega)
  omega

lemma a_le_three_n (k : ℕ) : a k ≤ 3 * k := by
  induction' k using Nat.strong_induction_on with k ih
  by_cases hk : k < 9
  · interval_cases k <;> decide
  · have hk_ge : 9 ≤ k := by omega
    have h_step : a k = a (k-1) + d k := a_eq_prev_add_d k (by omega)
    rw [h_step]
    have ih_prev := ih (k-1) (by omega)
    have hk2 : 2 ≤ k := by omega
    have hd_eq := d_eq_gcd k hk2
    by_cases h_even : k % 2 = 0
    · rw [if_pos h_even] at hd_eq
      generalize hg_eq : Nat.gcd k (a (k-1)) = g
      rw [hg_eq] at hd_eq
      by_cases hg3 : g ≤ 3
      · rw [hd_eq]
        omega
      · have hg4 : 4 ≤ g := by omega
        have h_g_dvd_k : g ∣ k := by
          rw [← hg_eq]
          exact Nat.gcd_dvd_left k (a (k-1))
        have h_g_dvd_a : g ∣ a (k-1) := by
          rw [← hg_eq]
          exact Nat.gcd_dvd_right k (a (k-1))
        rcases h_g_dvd_k with ⟨d_val, hd_val⟩
        rcases h_g_dvd_a with ⟨c_val, hc_val⟩
        have hd_val_pos : 0 < d_val := by
          by_contra hc0
          have : d_val = 0 := by omega
          subst this
          omega
        by_cases hd_val_two : d_val = 2
        · rw [hd_eq]
          rw [hc_val, hd_val, hd_val_two] at ih_prev ⊢
          have h_ring : 3 * (g * 2 - 1) = 6 * g - 3 := by omega
          rw [h_ring] at ih_prev
          have h_lt : g * c_val < 6 * g := by omega
          have hc_val_lt : c_val < 6 := by
            by_contra! hc_ge
            have h_le : g * 6 ≤ g * c_val := Nat.mul_le_mul_left g hc_ge
            have h_ring_eq : g * 6 = 6 * g := by ring
            rw [h_ring_eq] at h_le
            clear h_step ih hd_eq hg_eq hd_val_pos hd_val_two hd_val hc_val hk_ge hk2
            omega
          have : c_val ≤ 5 := by omega
          have : g * c_val ≤ g * 5 := Nat.mul_le_mul_left g this
          omega
        · by_cases hd_val_one : d_val = 1
          · rw [hd_eq]
            rw [hc_val, hd_val, hd_val_one] at ih_prev ⊢
            have h_ring : 3 * (g * 1 - 1) = 3 * g - 3 := by omega
            rw [h_ring] at ih_prev
            have h_lt : g * c_val < 3 * g := by omega
            have : c_val < 3 := by
              by_contra! hc_ge
              have h_le : g * 3 ≤ g * c_val := Nat.mul_le_mul_left g hc_ge
              have h_ring_eq : g * 3 = 3 * g := by ring
              rw [h_ring_eq] at h_le
              clear h_step ih hd_eq hg_eq hd_val_pos hd_val_one hd_val hc_val hk_ge hk2
              omega
            have : c_val ≤ 2 := by omega
            have : g * c_val ≤ g * 2 := Nat.mul_le_mul_left g this
            omega
          · rw [hd_eq]
            rw [hc_val, hd_val] at ih_prev ⊢
            have h_ring : 3 * d_val * g = (g * d_val) * 3 := by ring
            have h_lt : g * c_val < 3 * d_val * g := by
              rw [h_ring]
              have h_ring5 : 3 * (g * d_val - 1) = (g * d_val) * 3 - 3 := by omega
              rw [h_ring5] at ih_prev
              omega
            have hc_val_lt : c_val < 3 * d_val := by
              by_contra! hc_ge
              have h_le : g * (3 * d_val) ≤ g * c_val := Nat.mul_le_mul_left g hc_ge
              have h_ring2 : g * (3 * d_val) = 3 * d_val * g := by ring
              rw [h_ring2] at h_le
              clear h_step ih hd_eq hg_eq hd_val_pos hd_val hc_val hk_ge hk2 h_ring
              omega
            have : g * c_val + g ≤ g * (3 * d_val) := by
              have hc_val_le : c_val + 1 ≤ 3 * d_val := by omega
              have h_le : g * (c_val + 1) ≤ g * (3 * d_val) := Nat.mul_le_mul_left g hc_val_le
              have h_ring3 : g * (c_val + 1) = g * c_val + g := by ring
              rw [h_ring3] at h_le
              clear h_step ih hd_eq hg_eq hd_val_pos hd_val hc_val hk_ge hk2 h_ring h_lt h_ring3
              omega
            have h_ring4 : g * (3 * d_val) = 3 * (g * d_val) := by ring
            rw [← h_ring4]
            clear h_step ih hd_eq hg_eq hd_val_pos hd_val hc_val hk_ge hk2 h_ring ih_prev h_lt h_ring4
            omega
    · rw [if_neg h_even] at hd_eq
      generalize hg_eq : Nat.gcd (k-2) (a (k-1)) = g
      rw [hg_eq] at hd_eq
      by_cases hg3 : g ≤ 3
      · rw [hd_eq]
        omega
      · have hg4 : 4 ≤ g := by omega
        have h_g_dvd_k2 : g ∣ k-2 := by
          rw [← hg_eq]
          exact Nat.gcd_dvd_left (k-2) (a (k-1))
        have h_g_dvd_a : g ∣ a (k-1) := by
          rw [← hg_eq]
          exact Nat.gcd_dvd_right (k-2) (a (k-1))
        rcases h_g_dvd_k2 with ⟨d_val, hd_val⟩
        rcases h_g_dvd_a with ⟨c_val, hc_val⟩
        have hd_val_pos : 0 < d_val := by
          by_contra hc0
          have : d_val = 0 := by omega
          subst this
          omega
        by_cases hd_val_one : d_val = 1
        · have hk_sub : k - 1 = (k-2) + 1 := by omega
          have hk_eq : k = (k-2) + 2 := by omega
          rw [hd_eq]
          rw [hc_val] at ⊢
          rw [hk_eq, hd_val] at ⊢
          rw [hd_val_one] at ⊢
          rw [hc_val, hk_sub, hd_val, hd_val_one] at ih_prev
          have h_lt : g * c_val < 4 * g := by omega
          have : c_val < 4 := by
            by_contra! hc_ge
            have h_le : g * 4 ≤ g * c_val := Nat.mul_le_mul_left g hc_ge
            have h_ring_eq : 4 * g = g * 4 := by ring
            rw [← h_ring_eq] at h_le
            have h_ring2 : 3 * (g * 1 + 1) = 3 * g + 3 := by omega
            rw [h_ring2] at ih_prev
            have h_ring3 : 4 * g = 3 * g + g := by ring
            rw [h_ring3] at h_le
            clear h_step ih hd_eq hg_eq hd_val_pos hd_val_one hd_val hc_val hk_ge hk2 hk_sub hk_eq h_lt h_ring_eq h_ring2 h_ring3
            omega
          by_cases hc_val_three : c_val = 3
          · have h_parity_a : a (k-1) % 2 = 0 := by
              have := a_parity (k-1) (by omega)
              omega
            have h_parity_val : (3 * (k-2)) % 2 = 1 := by
              have h_odd : (k-2) % 2 = 1 := by omega
              rw [Nat.mul_mod, h_odd]
            have h_eq : a (k-1) = 3 * (k-2) := by
              calc a (k-1) = g * c_val := hc_val
              _ = g * 3 := by rw [hc_val_three]
              _ = 3 * (k-2) := by
                rw [hd_val, hd_val_one]
                ring
            omega
          · have h_le : g * c_val ≤ g * 2 := Nat.mul_le_mul_left g (by omega)
            omega
        · have hk_sub : k - 1 = (k-2) + 1 := by omega
          have hk_eq : k = (k-2) + 2 := by omega
          rw [hd_eq]
          rw [hc_val] at ⊢
          rw [hk_eq, hd_val] at ⊢
          rw [hc_val, hk_sub, hd_val] at ih_prev
          have h_c_le_3d : c_val ≤ 3 * d_val := by
            by_contra! hc_ge
            have h_le : g * (3 * d_val + 1) ≤ g * c_val := Nat.mul_le_mul_left g hc_ge
            have h1 : g * (3 * d_val + 1) = g * d_val * 3 + g := by ring
            have h2 : 3 * (g * d_val + 1) = g * d_val * 3 + 3 := by ring
            rw [h1] at h_le
            rw [h2] at ih_prev
            clear h_step ih hd_eq hg_eq hd_val_pos hd_val hc_val hk_ge hk2 hk_sub hk_eq h1 h2
            omega
          by_cases hc_val_three_d : c_val = 3 * d_val
          · have h_eq : a (k-1) = 3 * (k-2) := by
              calc a (k-1) = g * c_val := hc_val
              _ = g * (3 * d_val) := by rw [hc_val_three_d]
              _ = 3 * (g * d_val) := by ring
              _ = 3 * (k-2) := by rw [← hd_val]
            have h_parity_a : a (k-1) % 2 = 0 := by
              have := a_parity (k-1) (by omega)
              omega
            have h_parity_val : (3 * (k-2)) % 2 = 1 := by
              have h_odd : (k-2) % 2 = 1 := by omega
              rw [Nat.mul_mod, h_odd]
            omega
          · have h_sum_le : g * c_val + g ≤ g * (3 * d_val) := by
              have h_le : g * (c_val + 1) ≤ g * (3 * d_val) := Nat.mul_le_mul_left g (by omega)
              have h_ring3 : g * (c_val + 1) = g * c_val + g := by ring
              rw [h_ring3] at h_le
              exact h_le
            have h_ring5 : g * (3 * d_val) = 3 * (g * d_val) := by ring
            rw [h_ring5] at h_sum_le
            have h_ring4 : 3 * (g * d_val + 2) = 3 * (g * d_val) + 6 := by omega
            rw [h_ring4]
            clear h_step ih hd_eq hg_eq hd_val_pos ih_prev hd_val hc_val hk_ge hk2 hk_sub hk_eq hc_val_three_d h_ring5 h_ring4
            omega

lemma a_R_plus_one_eq_two_R (R n : ℕ) (hR : 5 < R) (hr : is_difference_record R) (hn2 : 2 ≤ n) (hn : d n = R) (hn_eq : n = R + 2) :
  a (R+1) = 2 * R := by
  have hR_odd : R % 2 = 1 := record_odd hR hr
  have hn_odd : n % 2 = 1 := by omega
  have hd_eq := d_eq_gcd n hn2
  rw [hn, hn_eq, if_neg (by omega)] at hd_eq
  have h_gcd : Nat.gcd R (a (R+1)) = R := hd_eq.symm
  have h_dvd : R ∣ a (R+1) := by
    nth_rw 1 [← h_gcd]
    exact Nat.gcd_dvd_right R (a (R+1))
  have h_le3 := a_le_three_n (R+1)
  have h_ge_sub := D_ge_sub_two (R+1) (by omega)
  have h_ge_self := a_ge_self (R+1)
  have h_ge2R : 2 * R ≤ a (R+1) := by omega
  rcases h_dvd with ⟨c, hc⟩
  rw [hc] at h_le3 h_ge2R
  have hc_even : c % 2 = 0 := by
    have h_par := a_parity (R+1) (by omega)
    rw [hc, Nat.mul_mod, hR_odd] at h_par
    omega
  have hc_lt4 : c < 4 := by
    by_contra! hc_ge
    have : R * 4 ≤ R * c := Nat.mul_le_mul_left R hc_ge
    have : R * 4 ≤ 3 * (R + 1) := le_trans this h_le3
    omega
  have hc_ge2 : 2 ≤ c := by
    by_contra! hc_lt
    interval_cases c
    · simp [hc] at h_ge_self
    · omega
  have hc2 : c = 2 := by omega
  rw [hc, hc2, Nat.mul_comm]

lemma D_mono_general (m n : ℕ) (hm : 2 ≤ m) (h_le : m ≤ n) : a m - m ≤ a n - n := by
  induction h_le with
  | refl => rfl
  | step hk ih =>
    rename_i k
    have h_le_k : m ≤ k := hk
    have h_sub : k + 1 - 1 = k := by omega
    have h_step := D_mono (k+1) (by omega)
    rw [h_sub] at h_step
    exact le_trans ih h_step


lemma prime_of_record (R : ℕ) (hR : 5 < R) (hr : is_difference_record R) : Nat.Prime R := by
  have hR_ge : 2 ≤ R := by omega
  by_contra h_not_prime
  have hR_odd : R % 2 = 1 := record_odd hR hr
  let p := R.minFac
  have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ R := Nat.minFac_dvd R
  have hp_lt : p < R := by
    by_contra! hc
    have hp_le : p ≤ R := Nat.le_of_dvd (by omega) hp_dvd
    have h_eq : p = R := by omega
    rw [h_eq] at hp_prime
    exact h_not_prime hp_prime
  have hp_odd : p % 2 = 1 := by
    rcases hp_dvd with ⟨c, hc⟩
    rw [hc] at hR_odd
    rw [Nat.mul_mod] at hR_odd
    have h_p_mod : p % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases h : p % 2
    · simp at hR_odd
    · rfl
  have hp_ge : 3 ≤ p := by
    have hp_le2 : p ≥ 2 := hp_prime.two_le
    omega
  rcases hr with ⟨n, hn2, hn, h_rec⟩
  have h_cases := cases_of_record_index R n hR ⟨n, hn2, hn, h_rec⟩ hn2 hn
  rcases h_cases with hn_eq | hn_ge
  · have h_ak : a (R+1) = 2 * R := a_R_plus_one_eq_two_R R n hR ⟨n, hn2, hn, h_rec⟩ hn2 hn hn_eq
    have h_Dp : a (p+2) - (p+2) ≥ p + 1 := by
      have h1 := D_ge_sub_two (p+2) (by omega)
      have h2 := D_even (p+2) (by omega)
      omega
    have h_mono : a (p+2) - (p+2) ≤ a (R+1) - (R+1) := by
      have h_le : p+2 ≤ R+1 := by
        have hp_sq : p * p ≤ R := minFac_sq_le R hR_ge h_not_prime
        have h_3p : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp_ge
        have : 3 * p ≤ R := le_trans h_3p hp_sq
        omega
      apply D_mono_general
      · omega
      · exact h_le
    have h_R_sub : a (R+1) - (R+1) = R - 1 := by
      rw [h_ak]
      omega
    omega
  · -- Case hn_ge : n ≥ 2 * R
    -- Since n ≥ 2 * R, we have R+2 < 2R ≤ n
    have h_R2 : R + 2 < n := by omega
    have h_rec_R2 : d (R+2) < R := h_rec (R+2) ⟨by omega, h_R2⟩
    have hd_eq_g := d_eq_gcd (R+2) (by omega)
    have h_odd : (R+2) % 2 = 1 := by
      have : R % 2 = 1 := hR_odd
      omega
    rw [hd_eq_g, if_neg (by omega)] at h_rec_R2
    have h_sub : R + 2 - 2 = R := by omega
    rw [h_sub] at h_rec_R2
    -- gcd R (a (R+1)) < R
    have h_gcd_lt : Nat.gcd R (a (R+1)) < R := h_rec_R2
    have h_not_dvd : ¬ R ∣ a (R+1) := by
      intro hdvd
      have h_gcd_eq : Nat.gcd R (a (R+1)) = R := gcd_eq_left_of_dvd (by omega) hdvd
      omega
    -- Since D(R+1) = a(R+1) - (R+1) ≥ R-1 by D_ge_sub_two
    have h_Dp : a (R+1) - (R+1) ≥ R - 1 := by
      have h1 := D_ge_sub_two (R+1) (by omega)
      have h2 := D_even (R+1) (by omega)
      omega
    -- If D(R+1) = R-1, then a(R+1) = 2R, so R ∣ a(R+1), contradiction!
    by_cases h_Dp_eq : a (R+1) - (R+1) = R - 1
    · have h_ak : a (R+1) = 2 * R := by
        have h_ge := a_ge_self (R+1)
        omega
      have hdvd : R ∣ a (R+1) := by
        rw [h_ak]
        exact dvd_mul_left R 2
      exact h_not_dvd hdvd
    · -- Since D(R+1) ≥ R-1 and not equal, D(R+1) ≥ R + 1 (since even/odd parity)
      have h_Dp_ge : a (R+1) - (R+1) ≥ R + 1 := by
        have h_even := D_even (R+1) (by omega)
        omega
      omega

lemma prime_sub_of_record (R : ℕ) (hR : 5 < R) (hr : is_difference_record R) : Nat.Prime (R - 2) := by
  have hR_sub_ge : 2 ≤ R - 2 := by omega
  by_contra h_not_prime_sub
  have hR_odd : R % 2 = 1 := record_odd hR hr
  let q := (R - 2).minFac
  have hq_prime : Nat.Prime q := Nat.minFac_prime (by omega)
  have hq_dvd : q ∣ R - 2 := Nat.minFac_dvd (R - 2)
  have hq_lt : q < R - 2 := by
    by_contra! hc
    have hq_le : q ≤ R - 2 := Nat.le_of_dvd (by omega) hq_dvd
    have h_eq : q = R - 2 := by omega
    rw [h_eq] at hq_prime
    exact h_not_prime_sub hq_prime
  have hq_odd : q % 2 = 1 := by
    rcases hq_dvd with ⟨c, hc⟩
    have hR_sub_odd : (R - 2) % 2 = 1 := by omega
    rw [hc] at hR_sub_odd
    rw [Nat.mul_mod] at hR_sub_odd
    have h_q_mod : q % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases h : q % 2
    · simp at hR_sub_odd
    · rfl
  have hq_ge : 3 ≤ q := by
    have hq_le2 : q ≥ 2 := hq_prime.two_le
    omega
  rcases hr with ⟨n, hn2, hn, h_rec⟩
  have h_cases := cases_of_record_index R n hR ⟨n, hn2, hn, h_rec⟩ hn2 hn
  rcases h_cases with hn_eq | hn_ge
  · have h_ak : a (R+1) = 2 * R := a_R_plus_one_eq_two_R R n hR ⟨n, hn2, hn, h_rec⟩ hn2 hn hn_eq
    have h_Dq : a (q+2) - (q+2) ≥ q + 1 := by
      have h1 := D_ge_sub_two (q+2) (by omega)
      have h2 := D_even (q+2) (by omega)
      omega
    have h_mono : a (q+2) - (q+2) ≤ a (R+1) - (R+1) := by
      have h_le : q+2 ≤ R+1 := by
        have hq_sq : q * q ≤ R - 2 := minFac_sq_le (R - 2) hR_sub_ge h_not_prime_sub
        have h_3q : 3 * q ≤ q * q := Nat.mul_le_mul_right q hq_ge
        have : 3 * q ≤ R - 2 := le_trans h_3q hq_sq
        omega
      apply D_mono_general
      · omega
      · exact h_le
    have h_R_sub : a (R+1) - (R+1) = R - 1 := by
      rw [h_ak]
      omega
    omega
  · -- Case hn_ge : n ≥ 2 * R
    -- Since n ≥ 2 * R, we have R+2 < 2R ≤ n
    have h_R2 : R + 2 < n := by omega
    have h_rec_R2 : d (R+2) < R := h_rec (R+2) ⟨by omega, h_R2⟩
    have hd_eq_g := d_eq_gcd (R+2) (by omega)
    have h_odd : (R+2) % 2 = 1 := by
      have : R % 2 = 1 := hR_odd
      omega
    rw [hd_eq_g, if_neg (by omega)] at h_rec_R2
    have h_sub : R + 2 - 2 = R := by omega
    rw [h_sub] at h_rec_R2
    -- gcd R (a (R+1)) < R
    have h_gcd_lt : Nat.gcd R (a (R+1)) < R := h_rec_R2
    have h_not_dvd : ¬ R ∣ a (R+1) := by
      intro hdvd
      have h_gcd_eq : Nat.gcd R (a (R+1)) = R := gcd_eq_left_of_dvd (by omega) hdvd
      omega
    -- Since D(R+1) = a(R+1) - (R+1) ≥ R-1 by D_ge_sub_two
    have h_Dp : a (R+1) - (R+1) ≥ R - 1 := by
      have h1 := D_ge_sub_two (R+1) (by omega)
      have h2 := D_even (R+1) (by omega)
      omega
    -- If D(R+1) = R-1, then a(R+1) = 2R, so R ∣ a(R+1), contradiction!
    by_cases h_Dp_eq : a (R+1) - (R+1) = R - 1
    · have h_ak : a (R+1) = 2 * R := by
        have h_ge := a_ge_self (R+1)
        omega
      have hdvd : R ∣ a (R+1) := by
        rw [h_ak]
        exact dvd_mul_left R 2
      exact h_not_dvd hdvd
    · -- Since D(R+1) ≥ R-1 and not equal, D(R+1) ≥ R + 1 (since even/odd parity)
      have h_Dp_ge : a (R+1) - (R+1) ≥ R + 1 := by
        have h_even := D_even (R+1) (by omega)
        omega
      omega

/--
Conjecture: Every record of differences $a(n)-a(n-1)$ more than 5 is the greater of twin primes (A006512).
-/
theorem oeis_166944_conjecture_0 :
  ∀ R : ℕ, 5 < R → is_difference_record R → is_greater_twin_prime R := by
  intro R hR hr
  unfold is_greater_twin_prime
  exact ⟨prime_of_record R hR hr, prime_sub_of_record R hR hr⟩
