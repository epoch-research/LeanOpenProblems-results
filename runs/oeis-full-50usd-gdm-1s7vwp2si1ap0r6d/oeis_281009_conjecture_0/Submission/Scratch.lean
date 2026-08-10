import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma coprime_two_of_odd (o : ℕ) (ho : o % 2 = 1) : Coprime o 2 := by
  have h1 : Nat.gcd o 2 ∣ 2 := Nat.gcd_dvd_right o 2
  have h2 : Nat.gcd o 2 ∣ o := Nat.gcd_dvd_left o 2
  have h3 : Nat.gcd o 2 ≠ 0 := by
    intro hc
    have h_div : 0 ∣ 2 := by
      rw [← hc]
      exact h1
    rcases h_div with ⟨c, hc2⟩
    omega
  have h3_pos : Nat.gcd o 2 > 0 := by omega
  have h4 : Nat.gcd o 2 ≤ 2 := Nat.le_of_dvd (by decide) h1
  have h5 : Nat.gcd o 2 = 1 ∨ Nat.gcd o 2 = 2 := by omega
  rcases h5 with h_eq | h_eq
  · exact h_eq
  · -- if gcd o 2 = 2, then 2 | o, so o % 2 = 0
    have : 2 ∣ o := by
      rw [← h_eq]
      exact h2
    have : o % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp this
    omega

def oddPart (d : ℕ) : ℕ := d / 2 ^ (padicValNat 2 d)

lemma oddPart_odd (d : ℕ) (hd : d ≠ 0) : oddPart d % 2 = 1 := by
  have h_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ padicValNat 2 d ∣ d := pow_padicValNat_dvd
  have h_eq : d = 2 ^ padicValNat 2 d * oddPart d := by
    exact (Nat.mul_div_cancel' hdvd).symm
  have hnot : ¬ 2 ^ (padicValNat 2 d + 1) ∣ d := pow_succ_padicValNat_not_dvd hd
  have h_odd : ¬ 2 ∣ oddPart d := by
    intro h2
    rcases h2 with ⟨k, hk⟩
    have hdvd2 : 2 ^ (padicValNat 2 d + 1) ∣ d := by
      use k
      nth_rw 1 [h_eq]
      rw [hk]
      ring
    exact hnot hdvd2
  omega

lemma oddPart_dvd (d : ℕ) : oddPart d ∣ d := by
  have hdvd : 2 ^ padicValNat 2 d ∣ d := pow_padicValNat_dvd
  use 2 ^ padicValNat 2 d
  rw [mul_comm]
  exact (Nat.mul_div_cancel' hdvd).symm

lemma oddPart_mem_odd_divisors {n d : ℕ} (hn : n ≠ 0) (hd : d ∈ divisors n) :
    oddPart d ∈ (divisors n).filter (fun x => x % 2 = 1) := by
  have hd_ne : d ≠ 0 := by
    rintro rfl
    have := mem_divisors.mp hd
    omega
  have h_odd := oddPart_odd d hd_ne
  have h_div_d := oddPart_dvd d
  have h_div_n : oddPart d ∣ n := by
    have hd_div := mem_divisors.mp hd
    exact dvd_trans h_div_d hd_div.1
  rw [mem_filter, mem_divisors]
  exact ⟨⟨h_div_n, hn⟩, h_odd⟩

lemma dvd_oddPart_of_dvd (n : ℕ) (o : ℕ) (ho : o % 2 = 1) (hdvd : o ∣ n) : o ∣ oddPart n := by
  have h_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd_pow : 2 ^ padicValNat 2 n ∣ n := pow_padicValNat_dvd
  have h_eq : n = 2 ^ padicValNat 2 n * oddPart n := by
    exact (Nat.mul_div_cancel' hdvd_pow).symm
  have h_cop2 : Coprime o 2 := coprime_two_of_odd o ho
  have h_cop_pow : Coprime o (2 ^ padicValNat 2 n) := Coprime.pow_right (padicValNat 2 n) h_cop2
  have hdvd_mul : o ∣ 2 ^ padicValNat 2 n * oddPart n := by
    rw [← h_eq]
    exact hdvd
  exact Coprime.dvd_of_dvd_mul_left h_cop_pow hdvd_mul

lemma le_pow_four_self (x : ℕ) : x ≤ 4^x := by
  induction x with
  | zero => omega
  | succ x ih =>
    have h_four_pos : 4^x ≥ 1 := Nat.one_le_pow x 4 (by decide)
    calc x + 1 ≤ 4^x + 1 := by omega
    _ ≤ 4^x + 4^x := by omega
    _ ≤ 4 * 4^x := by omega
    _ = 4^(x + 1) := by ring

lemma exist_middle_divisor (n : ℕ) (hn : n ≠ 0) (o : ℕ) (ho : o % 2 = 1) (ho_div : o ∣ oddPart n)
    (ho1 : o ^ 2 < 2 * n) (ho2 : (oddPart n / o) ^ 2 < 2 * n) :
    ∃ j ≤ padicValNat 2 n, n ≤ 2 * (2^j * o)^2 ∧ (2^j * o)^2 < 2 * n := by
  have h_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ padicValNat 2 n ∣ n := pow_padicValNat_dvd
  have h_eq : n = 2 ^ padicValNat 2 n * oddPart n := by
    exact (Nat.mul_div_cancel' hdvd).symm
  -- Define the finset of candidates
  let A := (range (2 * n + 1)).filter (fun i => 4^i * o^2 < 2 * n)
  have h0 : 0 ∈ A := by
    rw [mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    simp only [pow_zero, one_mul]
    exact ho1
  have h_nonempty : A.Nonempty := ⟨0, h0⟩
  let j := A.max' h_nonempty
  have hj_mem : j ∈ A := max'_mem A h_nonempty
  rw [mem_filter, mem_range] at hj_mem
  have hj_lt : 4^j * o^2 < 2 * n := hj_mem.2
  have h_pow : (2^j * o)^2 = 4^j * o^2 := by
    calc (2^j * o)^2 = (2^j)^2 * o^2 := by ring
    _ = (2^2)^j * o^2 := by
      congr 1
      rw [← pow_mul, mul_comm, pow_mul]
    _ = 4^j * o^2 := by rfl
  -- Prove that j + 1 is not in A
  have hj1_not_mem : j + 1 ∉ A := by
    intro h
    have := le_max' A (j + 1) h
    omega
  -- This implies 4^(j+1) * o^2 >= 2 * n
  have hj1_ge : 4^(j+1) * o^2 ≥ 2 * n := by
    by_contra hc
    have hc_lt : 4^(j+1) * o^2 < 2 * n := by omega
    have hj1_range : j + 1 < 2 * n + 1 := by
      have ho_ge : o^2 ≥ 1 := by
        have : o > 0 := by
          by_contra hc2
          have : o = 0 := by omega
          subst this
          omega
        exact Nat.one_le_pow 2 o this
      have : 4^(j+1) < 2 * n := by
        calc 4^(j+1) = 4^(j+1) * 1 := by ring
        _ ≤ 4^(j+1) * o^2 := Nat.mul_le_mul_left (4^(j+1)) ho_ge
        _ < 2 * n := hc_lt
      calc j + 1 ≤ 4^(j+1) := le_pow_four_self (j+1)
      _ < 2 * n := this
      _ < 2 * n + 1 := by omega
    have hj1_mem : j + 1 ∈ A := by
      rw [mem_filter, mem_range]
      exact ⟨hj1_range, hc_lt⟩
    exact hj1_not_mem hj1_mem
  -- Now we show n <= 2 * (2^j * o)^2
  have hn_le : n ≤ 2 * (2^j * o)^2 := by
    have : 4^(j+1) * o^2 = 4 * (4^j * o^2) := by ring
    rw [this] at hj1_ge
    rw [h_pow]
    omega
  -- Finally, we show j <= K
  have hj_le : j ≤ padicValNat 2 n := by
    by_contra hc
    have hj_ge_K1 : j ≥ padicValNat 2 n + 1 := by omega
    -- Then 4^j * o^2 >= 4^(K+1) * o^2
    have h_pow_ge : 4^j ≥ 4^(padicValNat 2 n + 1) := Nat.pow_le_pow_right (by decide) hj_ge_K1
    have h_ge1 : 4^j * o^2 ≥ 4^(padicValNat 2 n + 1) * o^2 := Nat.mul_le_mul_right (o^2) h_pow_ge
    -- Let's define o' = oddPart n / o
    let o' := oddPart n / o
    have h_o_mul : oddPart n = o * o' := by
      exact (Nat.mul_div_cancel' ho_div).symm
    have h_o_mul_comm : oddPart n = o' * o := by
      rw [h_o_mul, mul_comm]
    -- We want to show 4^(K+1) * o^2 >= 2 * n
    have h_eq2 : 2 * n = 2^(padicValNat 2 n + 1) * o * o' := by
      nth_rw 1 [h_eq]
      rw [h_o_mul_comm]
      ring
    have h_eq3 : 4^(padicValNat 2 n + 1) * o^2 = (2^(padicValNat 2 n + 1) * o) * (2^(padicValNat 2 n + 1) * o) := by
      have : 4^(padicValNat 2 n + 1) = 2^(2 * (padicValNat 2 n + 1)) := by
        rw [show 4 = 2^2 by decide, ← pow_mul]
      rw [this]
      ring
    have ho'_lt : o' ^ 2 < 2^(padicValNat 2 n + 1) * o * o' := by
      rw [← h_eq2]
      exact ho2
    have ho'_pos : o' > 0 := by
      have h_odd_ne : oddPart n ≠ 0 := by
        intro hc2
        have : n = 0 := by rw [h_eq, hc2, mul_zero]
        exact hn this
      have h_mul_ne : o * o' ≠ 0 := by
        rwa [← h_o_mul]
      have h_ne_zero : o' ≠ 0 := by
        intro h_zero
        rw [h_zero, mul_zero] at h_mul_ne
        exact h_mul_ne rfl
      exact Nat.pos_of_ne_zero h_ne_zero
    have ho'_lt_o : o' < 2^(padicValNat 2 n + 1) * o := by
      have : o' * o' < (2^(padicValNat 2 n + 1) * o) * o' := by
        calc o' * o' = o'^2 := by ring
        _ < 2^(padicValNat 2 n + 1) * o * o' := ho'_lt
        _ = (2^(padicValNat 2 n + 1) * o) * o' := by ring
      exact Nat.lt_of_mul_lt_mul_right this
    have h_le_o : o' ≤ 2^(padicValNat 2 n + 1) * o := by omega
    have h_ge2 : (2^(padicValNat 2 n + 1) * o) * (2^(padicValNat 2 n + 1) * o) ≥ (2^(padicValNat 2 n + 1) * o) * o' := by
      exact Nat.mul_le_mul_left (2^(padicValNat 2 n + 1) * o) h_le_o
    have h_contra_step : 4^(padicValNat 2 n + 1) * o^2 ≥ 2 * n := by
      rw [h_eq2, h_eq3]
      exact h_ge2
    omega
  use j, hj_le, hn_le
  rw [h_pow]
  exact hj_lt

lemma unique_middle_divisor (n : ℕ) (o : ℕ) (j1 j2 : ℕ)
    (hj1 : n ≤ 2 * (2^j1 * o)^2 ∧ (2^j1 * o)^2 < 2 * n)
    (hj2 : n ≤ 2 * (2^j2 * o)^2 ∧ (2^j2 * o)^2 < 2 * n) :
    j1 = j2 := by
  by_contra hc
  have h_cases : j1 < j2 ∨ j2 < j1 := by omega
  rcases h_cases with h_lt | h_lt
  · have h_le : j1 + 1 ≤ j2 := h_lt
    have h_pow_ge : 2^j2 ≥ 2^(j1 + 1) := Nat.pow_le_pow_right (by decide) h_le
    have h_ge : 2^j2 * o ≥ 2 * (2^j1 * o) := by
      calc 2^j2 * o ≥ 2^(j1+1) * o := Nat.mul_le_mul_right o h_pow_ge
      _ = 2 * (2^j1 * o) := by ring
    have h_ge_sq : (2^j2 * o)^2 ≥ 4 * (2^j1 * o)^2 := by
      have : (2^j2 * o)^2 = (2^j2 * o) * (2^j2 * o) := by ring
      rw [this]
      have h_mul := Nat.mul_le_mul h_ge h_ge
      have h_ring : (2 * (2^j1 * o)) * (2 * (2^j1 * o)) = 4 * (2^j1 * o)^2 := by ring
      rw [h_ring] at h_mul
      exact h_mul
    have : 4 * (2^j1 * o)^2 = 2 * (2 * (2^j1 * o)^2) := by ring
    have h_ge2 : 4 * (2^j1 * o)^2 ≥ 2 * n := by
      rw [this]
      omega
    have : (2^j2 * o)^2 ≥ 2 * n := by omega
    omega
  · have h_le : j2 + 1 ≤ j1 := h_lt
    have h_pow_ge : 2^j1 ≥ 2^(j2 + 1) := Nat.pow_le_pow_right (by decide) h_le
    have h_ge : 2^j1 * o ≥ 2 * (2^j2 * o) := by
      calc 2^j1 * o ≥ 2^(j2+1) * o := Nat.mul_le_mul_right o h_pow_ge
      _ = 2 * (2^j2 * o) := by ring
    have h_ge_sq : (2^j1 * o)^2 ≥ 4 * (2^j2 * o)^2 := by
      have : (2^j1 * o)^2 = (2^j1 * o) * (2^j1 * o) := by ring
      rw [this]
      have h_mul := Nat.mul_le_mul h_ge h_ge
      have h_ring : (2 * (2^j2 * o)) * (2 * (2^j2 * o)) = 4 * (2^j2 * o)^2 := by ring
      rw [h_ring] at h_mul
      exact h_mul
    have : 4 * (2^j2 * o)^2 = 2 * (2 * (2^j2 * o)^2) := by ring
    have h_ge2 : 4 * (2^j2 * o)^2 ≥ 2 * n := by
      rw [this]
      omega
    have : (2^j1 * o)^2 ≥ 2 * n := by omega
    omega

lemma card_M_o_eq_zero_of_gt1 (n : ℕ) (hn : n ≠ 0) (o : ℕ) (ho : o^2 ≥ 2 * n) :
    ((divisors n).filter (fun d => oddPart d = o ∧ n ≤ 2 * d^2 ∧ d^2 < 2 * n)) = ∅ := by
  ext d
  rw [mem_filter]
  constructor
  · rintro ⟨hd, h_odd, hn_le, hd_lt⟩
    have hd_ne : d ≠ 0 := by
      rintro rfl
      have := mem_divisors.mp hd
      omega
    have h_d_eq : d = 2 ^ padicValNat 2 d * oddPart d := by
      have hdvd : 2 ^ padicValNat 2 d ∣ d := pow_padicValNat_dvd
      exact (Nat.mul_div_cancel' hdvd).symm
    have h_pow_ge : 2 ^ padicValNat 2 d ≥ 1 := by
      exact Nat.one_le_pow (padicValNat 2 d) 2 (by decide)
    have hd_ge : d ≥ o := by
      rw [h_d_eq, h_odd]
      calc 2 ^ padicValNat 2 d * o ≥ 1 * o := Nat.mul_le_mul_right o h_pow_ge
      _ = o := by ring
    have hd_sq_ge : d^2 ≥ o^2 := by
      have : d^2 = d * d := by ring
      rw [this]
      have := Nat.mul_le_mul hd_ge hd_ge
      have h_ring : o * o = o^2 := by ring
      rw [h_ring] at this
      exact this
    omega
  · intro h
    exact (Finset.notMem_empty d h).elim

lemma card_M_o_eq_zero_of_gt2 (n : ℕ) (hn : n ≠ 0) (o : ℕ) (ho : o % 2 = 1) (ho_div : o ∣ oddPart n)
    (ho2 : (oddPart n / o)^2 ≥ 2 * n) :
    ((divisors n).filter (fun d => oddPart d = o ∧ n ≤ 2 * d^2 ∧ d^2 < 2 * n)) = ∅ := by
  have h_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ padicValNat 2 n ∣ n := pow_padicValNat_dvd
  have h_eq : n = 2 ^ padicValNat 2 n * oddPart n := by
    exact (Nat.mul_div_cancel' hdvd).symm
  let o' := oddPart n / o
  have h_o_mul : oddPart n = o * o' := by
    exact (Nat.mul_div_cancel' ho_div).symm
  ext d
  rw [mem_filter]
  constructor
  · rintro ⟨hd, h_odd, hn_le, hd_lt⟩
    have hd_ne : d ≠ 0 := by
      rintro rfl
      have := mem_divisors.mp hd
      omega
    have h_le_K : padicValNat 2 d ≤ padicValNat 2 n := by
      have hd_dvd : 2^(padicValNat 2 d) ∣ d := pow_padicValNat_dvd
      have hd_div := mem_divisors.mp hd
      have h_n_dvd : 2^(padicValNat 2 d) ∣ n := dvd_trans hd_dvd hd_div.1
      exact (padicValNat_dvd_iff_le hn).mp h_n_dvd
    let d' := n / d
    have hd_eq : d = 2^padicValNat 2 d * o := by
      have hdvd : 2 ^ padicValNat 2 d ∣ d := pow_padicValNat_dvd
      calc d = 2^padicValNat 2 d * oddPart d := (Nat.mul_div_cancel' hdvd).symm
      _ = 2^padicValNat 2 d * o := by rw [h_odd]
    have h_prod_val : 2^(padicValNat 2 n - padicValNat 2 d) * o' * (2^padicValNat 2 d * o) = n := by
      have h_odd_mul : oddPart n = o' * o := by
        rw [h_o_mul, mul_comm]
      nth_rw 2 [h_eq]
      rw [h_odd_mul]
      have h_pow : 2^(padicValNat 2 n - padicValNat 2 d) * 2^padicValNat 2 d = 2^padicValNat 2 n := by
        rw [← pow_add]
        congr 1
        omega
      calc 2^(padicValNat 2 n - padicValNat 2 d) * o' * (2^padicValNat 2 d * o)
        = (2^(padicValNat 2 n - padicValNat 2 d) * 2^padicValNat 2 d) * o' * o := by ring
      _ = 2^padicValNat 2 n * o' * o := by rw [h_pow]
      _ = 2^padicValNat 2 n * (o' * o) := by ring
    have h_prod : 2^(padicValNat 2 n - padicValNat 2 d) * o' * d = n := by
      calc 2^(padicValNat 2 n - padicValNat 2 d) * o' * d
        = 2^(padicValNat 2 n - padicValNat 2 d) * o' * (2^padicValNat 2 d * o) := by nth_rw 2 [hd_eq]
      _ = n := h_prod_val
    have hd'_eq : d' = 2^(padicValNat 2 n - padicValNat 2 d) * o' := by
      unfold d'
      conv_lhs => rw [← h_prod]
      exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd_ne)
    have ho'_odd : o' % 2 = 1 := by
      have h_odd_n := oddPart_odd n hn
      rw [h_o_mul] at h_odd_n
      have : o' % 2 = 0 ∨ o' % 2 = 1 := Nat.mod_two_eq_zero_or_one o'
      rcases this with h0 | h1
      · have hdvd : 2 ∣ o' := Nat.dvd_of_mod_eq_zero h0
        have hdvd_mul : 2 ∣ o * o' := dvd_mul_of_dvd_right hdvd o
        have : (o * o') % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd_mul
        omega
      · exact h1
    have h_padic_o' : padicValNat 2 o' = 0 := by
      have : ¬ 2 ∣ o' := by
        intro hc2
        have : o' % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hc2
        omega
      exact padicValNat.eq_zero_of_not_dvd this
    have h_padic_d' : padicValNat 2 d' = padicValNat 2 n - padicValNat 2 d := by
      rw [hd'_eq]
      have h_pow_ne : 2^(padicValNat 2 n - padicValNat 2 d) ≠ 0 := by
        have : 2^(padicValNat 2 n - padicValNat 2 d) ≥ 1 := Nat.one_le_pow (padicValNat 2 n - padicValNat 2 d) 2 (by decide)
        omega
      have h_o'_ne : o' ≠ 0 := by omega
      have h_mul := padicValNat.mul (p := 2) h_pow_ne h_o'_ne
      rw [h_mul, h_padic_o', add_zero]
      exact padicValNat.prime_pow (padicValNat 2 n - padicValNat 2 d)
    have hd'_odd : oddPart d' = o' := by
      rw [oddPart, h_padic_d', hd'_eq]
      have h_pow_pos : 2^(padicValNat 2 n - padicValNat 2 d) > 0 := by
        have : 2^(padicValNat 2 n - padicValNat 2 d) ≥ 1 := Nat.one_le_pow (padicValNat 2 n - padicValNat 2 d) 2 (by decide)
        omega
      rw [Nat.mul_div_cancel_left]
      exact h_pow_pos
    -- Let's show n <= 2 * d'^2
    have h_d'_le : n ≤ 2 * d'^2 := by
      by_contra hc
      have hc_lt : 2 * d'^2 < n := by omega
      have : 2 * n^2 < d^2 * n := by
        have hd_mul_d' : d * d' = n := Nat.mul_div_cancel' (mem_divisors.mp hd).1
        calc 2 * n^2 = 2 * (d * d')^2 := by rw [hd_mul_d']
        _ = d^2 * (2 * d'^2) := by ring
        _ < d^2 * n := Nat.mul_lt_mul_of_pos_left hc_lt (by
          have hd_pos : d > 0 := Nat.pos_of_ne_zero hd_ne
          have : d^2 = d * d := by ring
          omega)
      have : (2 * n) * n < d^2 * n := by
        calc (2 * n) * n = 2 * n^2 := by ring
        _ < d^2 * n := this
      have : 2 * n < d^2 := Nat.lt_of_mul_lt_mul_right this
      omega
    have h_d'_lt : d'^2 < 2 * n := by
      by_contra hc
      have hc_ge : 2 * n ≤ d'^2 := by omega
      have h_n_ge : n ≥ 2 * d^2 := by
        have h_prod2 : d^2 * d'^2 = n^2 := by
          have h_dd' : d * d' = n := Nat.mul_div_cancel' (mem_divisors.mp hd).1
          calc d^2 * d'^2 = (d * d')^2 := by ring
          _ = n^2 := by rw [h_dd']
        have : d^2 * 2 * n ≤ d^2 * d'^2 := by
          calc d^2 * 2 * n = d^2 * (2 * n) := by ring
          _ ≤ d^2 * d'^2 := Nat.mul_le_mul_left (d^2) hc_ge
        rw [h_prod2] at this
        have h_mul_le : (2 * d^2) * n ≤ n * n := by
          calc (2 * d^2) * n = d^2 * 2 * n := by ring
          _ ≤ n^2 := this
          _ = n * n := by ring
        exact Nat.le_of_mul_le_mul_right h_mul_le (Nat.pos_of_ne_zero hn)
      -- So we must have n = 2 * d^2
      have h_n_eq : n = 2 * d^2 := by omega
      -- This implies o' = o, and 2 * n = 2^(2j+2) * o^2
      -- which contradicts o'^2 >= 2 * n
      have h_d_sq : d^2 = (2^padicValNat 2 d * o)^2 := by conv_lhs => rw [hd_eq]
      have hn_eq : n = 2^(2 * padicValNat 2 d + 1) * o^2 := by
        calc n = 2 * d^2 := h_n_eq
        _ = 2 * (2^padicValNat 2 d * o)^2 := by rw [h_d_sq]
        _ = 2^(2 * padicValNat 2 d + 1) * o^2 := by ring
      have h_o_mul_eq : oddPart n = o^2 := by
        have h_padic_n : padicValNat 2 n = 2 * padicValNat 2 d + 1 := by
          rw [hn_eq]
          have h_o2_ne : o^2 ≠ 0 := by
            have : o^2 ≥ 1 := Nat.one_le_pow 2 o (by omega)
            omega
          have h_pow_ne2 : 2^(2 * padicValNat 2 d + 1) ≠ 0 := by
            have : 2^(2 * padicValNat 2 d + 1) ≥ 1 := Nat.one_le_pow (2 * padicValNat 2 d + 1) 2 (by decide)
            omega
          have h_mul := padicValNat.mul (p := 2) h_pow_ne2 h_o2_ne
          rw [h_mul]
          have h_padic_o2 : padicValNat 2 (o^2) = 0 := by
            have : ¬ 2 ∣ o^2 := by
              intro hc2
              have h_mod : o^2 % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hc2
              rw [pow_two] at h_mod
              rw [Nat.mul_mod, ho] at h_mod
              omega
            exact padicValNat.eq_zero_of_not_dvd this
          rw [h_padic_o2, add_zero]
          exact padicValNat.prime_pow _
        have h_div_n : n / 2^(padicValNat 2 n) = o^2 := by
          nth_rw 1 [hn_eq]
          rw [h_padic_n]
          have h_pow_pos2 : 2^(2 * padicValNat 2 d + 1) > 0 := by
            have : 2^(2 * padicValNat 2 d + 1) ≥ 1 := Nat.one_le_pow (2 * padicValNat 2 d + 1) 2 (by decide)
            omega
          rw [Nat.mul_div_cancel_left]
          exact h_pow_pos2
        exact h_div_n
      have ho'_eq : o' = o := by
        calc o' = oddPart n / o := rfl
        _ = o^2 / o := by rw [h_o_mul_eq]
        _ = o := by
          have : o^2 = o * o := by ring
          rw [this]
          rw [Nat.mul_div_cancel_left]
          exact Nat.pos_of_ne_zero (by omega)
      have : o'^2 < 2 * n := by
        rw [ho'_eq, hn_eq]
        have h_pow_ge : 2^(2 * padicValNat 2 d + 2) ≥ 4 := by
          have : 2 * padicValNat 2 d + 2 ≥ 2 := by omega
          have := Nat.pow_le_pow_right (n := 2) (by decide) this
          omega
        have ho_pos : o > 0 := by omega
        have h_o2_pos : 0 < o^2 := by nlinarith
        have h_lt_four : 1 < 2^(2 * padicValNat 2 d + 2) := by omega
        calc o^2 = 1 * o^2 := by ring
        _ < 2^(2 * padicValNat 2 d + 2) * o^2 := Nat.mul_lt_mul_of_pos_right (k := o^2) h_lt_four h_o2_pos
        _ = 2 * (2^(2 * padicValNat 2 d + 1) * o^2) := by ring
      change o'^2 ≥ 2 * n at ho2
      omega
    -- Now, we have hd'_odd : oddPart d' = o', h_d'_le : n <= 2 * d'^2, h_d'_lt : d'^2 < 2 * n.
    -- This means d' is in the filter of divisors n with o'.
    -- But that filter is empty because o'^2 >= 2 * n!
    have hd'_mem : d' ∈ (divisors n).filter (fun x => oddPart x = o' ∧ n ≤ 2 * x^2 ∧ x^2 < 2 * n) := by
      rw [mem_filter]
      refine ⟨?_, hd'_odd, h_d'_le, h_d'_lt⟩
      rw [mem_divisors]
      refine ⟨?_, hn⟩
      use d
      rw [mul_comm]
      exact (Nat.mul_div_cancel' (mem_divisors.mp hd).1).symm
    have h_empty := card_M_o_eq_zero_of_gt1 n hn o' ho2
    rw [h_empty] at hd'_mem
    exact (Finset.notMem_empty d' hd'_mem).elim
  · intro h
    exact (Finset.notMem_empty d h).elim

lemma oddPart_two_pow_mul (a j : ℕ) (hj : j % 2 = 1) :
    oddPart (2 ^ a * j) = j := by
  have hj0 : j ≠ 0 := by omega
  have h_two_pow : 2 ^ a ≠ 0 := by
    have : 2^a ≥ 1 := Nat.one_le_pow a 2 (by decide)
    omega
  have h_mul := padicValNat.mul (p := 2) h_two_pow hj0
  have h_padic_j : padicValNat 2 j = 0 := by
    have : ¬ 2 ∣ j := by
      intro hc2
      have : j % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hc2
      omega
    exact padicValNat.eq_zero_of_not_dvd this
  have h_padic_all : padicValNat 2 (2^a * j) = a := by
    rw [h_mul, h_padic_j, add_zero]
    exact padicValNat.prime_pow a
  unfold oddPart
  rw [h_padic_all]
  have h_pow_pos : 2^a > 0 := by
    have : 2^a ≥ 1 := Nat.one_le_pow a 2 (by decide)
    omega
  exact Nat.mul_div_cancel_left j h_pow_pos


lemma card_M_o_eq (n : ℕ) (hn : n ≠ 0) (o : ℕ) (ho : o % 2 = 1) (ho_div : o ∣ oddPart n) :
    ((divisors n).filter (fun d => oddPart d = o ∧ n ≤ 2 * d^2 ∧ d^2 < 2 * n)).card =
    if o^2 < 2 * n ∧ (oddPart n / o)^2 < 2 * n then 1 else 0 := by
  split_ifs with h_cond
  · rcases exist_middle_divisor n hn o ho ho_div h_cond.1 h_cond.2 with ⟨j, hj_le, hj_cond⟩
    let d := 2^j * o
    have hd_mem : d ∈ (divisors n).filter (fun d => oddPart d = o ∧ n ≤ 2 * d^2 ∧ d^2 < 2 * n) := by
      rw [mem_filter]
      refine ⟨?_, ?_, hj_cond.1, hj_cond.2⟩
      · rw [mem_divisors]
        refine ⟨?_, hn⟩
        have hdvd : 2 ^ padicValNat 2 n ∣ n := pow_padicValNat_dvd
        have h_eq2 : n = 2 ^ padicValNat 2 n * oddPart n := by
          exact (Nat.mul_div_cancel' hdvd).symm
        have h_odd_mul : oddPart n = o * (oddPart n / o) := by
          exact (Nat.mul_div_cancel' ho_div).symm
        rw [h_odd_mul] at h_eq2
        rw [h_eq2]
        have : 2^(padicValNat 2 n) * (o * (oddPart n / o)) = 2^j * o * (2^(padicValNat 2 n - j) * (oddPart n / o)) := by
          have : 2^(padicValNat 2 n) = 2^j * 2^(padicValNat 2 n - j) := by
            rw [← pow_add]
            congr 1
            omega
          rw [this]
          ring
        rw [this]
        exact dvd_mul_right (2^j * o) _
      · exact oddPart_two_pow_mul j o ho
    have hd_unique : ∀ x ∈ (divisors n).filter (fun d => oddPart d = o ∧ n ≤ 2 * d^2 ∧ d^2 < 2 * n), x = d := by
      intro x hx
      rw [mem_filter] at hx
      have h_odd : oddPart x = o := hx.2.1
      have hx0 : x ≠ 0 := by
        intro h_zero
        subst h_zero
        rw [mem_divisors] at hx
        omega
      have hx_eq : x = 2 ^ padicValNat 2 x * o := by
        have hdvd : 2 ^ padicValNat 2 x ∣ x := pow_padicValNat_dvd
        calc x = 2 ^ padicValNat 2 x * oddPart x := (Nat.mul_div_cancel' hdvd).symm
        _ = 2 ^ padicValNat 2 x * o := by rw [h_odd]
      have hj_eq : padicValNat 2 x = j := by
        apply unique_middle_divisor n o (padicValNat 2 x) j
        · rw [← hx_eq]
          exact ⟨hx.2.2.1, hx.2.2.2⟩
        · exact hj_cond
      rw [hx_eq, hj_eq]
    have : ((divisors n).filter (fun d => oddPart d = o ∧ n ≤ 2 * d^2 ∧ d^2 < 2 * n)) = {d} := by
      ext y
      rw [mem_filter, mem_singleton]
      constructor
      · intro hy
        exact hd_unique y (by rw [mem_filter]; exact hy)
      · rintro rfl
        rw [mem_filter] at hd_mem
        exact hd_mem
    rw [this, card_singleton]
  · push_neg at h_cond
    by_cases h1 : o^2 ≥ 2 * n
    · have h_empty := card_M_o_eq_zero_of_gt1 n hn o h1
      rw [h_empty, card_empty]
    · have h2 : (oddPart n / o)^2 ≥ 2 * n := by omega
      have h_empty := card_M_o_eq_zero_of_gt2 n hn o ho ho_div h2
      rw [h_empty, card_empty]


lemma odd_of_dvd_odd (a b : ℕ) (ha : a % 2 = 1) (hb : b ∣ a) : b % 2 = 1 := by
  have : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
  rcases this with h0 | h1
  · have : 2 ∣ b := Nat.dvd_of_mod_eq_zero h0
    have : 2 ∣ a := dvd_trans this hb
    have : a % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp this
    omega
  · exact h1

lemma divisors_filter_odd_eq (n : ℕ) (hn : n ≠ 0) :
    (divisors n).filter (fun d => d % 2 = 1) = divisors (oddPart n) := by
  ext d
  rw [mem_filter, mem_divisors, mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, h_odd⟩
    refine ⟨dvd_oddPart_of_dvd n d h_odd hd, ?_⟩
    have h_odd_n := oddPart_odd n hn
    omega
  · rintro ⟨hd, -⟩
    have h_odd_n := oddPart_odd n hn
    have hd_odd := odd_of_dvd_odd (oddPart n) d h_odd_n hd
    refine ⟨⟨?_, hn⟩, hd_odd⟩
    have hdvd : oddPart n ∣ n := oddPart_dvd n
    exact dvd_trans hd hdvd

lemma oddPart_mem_divisors_oddPart {n d : ℕ} (hn : n ≠ 0) (hd : d ∈ divisors n) :
    oddPart d ∈ divisors (oddPart n) := by
  rw [← divisors_filter_odd_eq n hn]
  exact oddPart_mem_odd_divisors hn hd

lemma card_M_eq_sum (n : ℕ) (hn : n ≠ 0) :
    ((divisors n).filter (fun d => n ≤ 2 * d^2 ∧ d^2 < 2 * n)).card =
    ∑ o ∈ divisors (oddPart n), (((divisors n).filter (fun d => n ≤ 2 * d^2 ∧ d^2 < 2 * n)).filter (fun d => oddPart d = o)).card := by
  apply Finset.card_eq_sum_card_fiberwise
  intro d hd
  rw [Finset.mem_coe, mem_filter] at hd
  exact oddPart_mem_divisors_oddPart hn hd.1

lemma card_M_eq_sum_if (n : ℕ) (hn : n ≠ 0) :
    ((divisors n).filter (fun d => n ≤ 2 * d^2 ∧ d^2 < 2 * n)).card =
    ∑ o ∈ divisors (oddPart n), (if o^2 < 2 * n ∧ (oddPart n / o)^2 < 2 * n then 1 else 0) := by
  rw [card_M_eq_sum n hn]
  apply Finset.sum_congr rfl
  intro o ho
  rw [mem_divisors] at ho
  have ho_odd : o % 2 = 1 := by
    have h_odd_n := oddPart_odd n hn
    exact odd_of_dvd_odd (oddPart n) o h_odd_n ho.1
  have h_eq_filter : ((divisors n).filter (fun d => n ≤ 2 * d^2 ∧ d^2 < 2 * n)).filter (fun d => oddPart d = o) =
                     (divisors n).filter (fun d => oddPart d = o ∧ n ≤ 2 * d^2 ∧ d^2 < 2 * n) := by
    ext d
    rw [mem_filter, mem_filter, mem_filter]
    tauto
  rw [h_eq_filter]
  exact card_M_o_eq n hn o ho_odd ho.1


lemma odd_sq_ne_two_mul (o n : ℕ) (ho : o % 2 = 1) : o^2 ≠ 2 * n := by
  intro h
  have h1 : o^2 % 2 = 1 := by
    rw [pow_two]
    have : (o * o) % 2 = (o % 2 * (o % 2)) % 2 := Nat.mul_mod o o 2
    rw [this, ho]
  have h2 : (2 * n) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_right 2 n)
  rw [h] at h1
  rw [h2] at h1
  contradiction

lemma not_both_gt (n : ℕ) (hn : n ≠ 0) (o : ℕ) (ho_div : o ∣ oddPart n) :
    ¬ (2 * n < o^2 ∧ 2 * n < (oddPart n / o)^2) := by
  rintro ⟨h1, h2⟩
  let o' := oddPart n / o
  have h_mul : o * o' = oddPart n := Nat.mul_div_cancel' ho_div
  have h_le : oddPart n ≤ n := by
    unfold oddPart
    exact Nat.div_le_self n (2^padicValNat 2 n)
  have h_prod : (o * o')^2 = o^2 * o'^2 := by ring
  have h_n_pos : n > 0 := Nat.pos_of_ne_zero hn
  have h_o2_pos : o'^2 > 0 := by
    dsimp [o']
    have : 2 * n > 0 := Nat.mul_pos (by decide) h_n_pos
    omega
  have h_gt : o^2 * o'^2 > 4 * n^2 := by
    have h_step1 : o^2 * o'^2 > (2 * n) * o'^2 := Nat.mul_lt_mul_of_pos_right h1 h_o2_pos
    have h_step2 : (2 * n) * o'^2 > (2 * n) * (2 * n) := Nat.mul_lt_mul_of_pos_left h2 (by omega)
    calc o^2 * o'^2 > (2 * n) * o'^2 := h_step1
    _ > (2 * n) * (2 * n) := h_step2
    _ = 4 * n^2 := by ring
  have h_le_n : (o * o')^2 ≤ n^2 := by
    rw [h_mul]
    exact Nat.pow_le_pow_left h_le 2
  rw [h_prod] at h_le_n
  omega


lemma indicator_identity (n : ℕ) (hn : n ≠ 0) (o : ℕ) (ho : o % 2 = 1) (ho_div : o ∣ oddPart n) :
    ((if o^2 < 2 * n ∧ (oddPart n / o)^2 < 2 * n then 1 else 0 : ℤ)) =
    1 - (if 2 * n < o^2 then 1 else 0) - (if 2 * n < (oddPart n / o)^2 then 1 else 0) := by
  let o' := oddPart n / o
  have h_not_eq1 : o^2 ≠ 2 * n := odd_sq_ne_two_mul o n ho
  have h_not_eq2 : o'^2 ≠ 2 * n := by
    have ho'_odd : o' % 2 = 1 := by
      have h_odd_n := oddPart_odd n hn
      have h_o_mul : oddPart n = o * o' := (Nat.mul_div_cancel' ho_div).symm
      rw [h_o_mul] at h_odd_n
      exact odd_of_dvd_odd (o * o') o' h_odd_n (dvd_mul_left o' o)
    exact odd_sq_ne_two_mul o' n ho'_odd
  have h_not_both : ¬ (2 * n < o^2 ∧ 2 * n < o'^2) := not_both_gt n hn o ho_div
  dsimp [o'] at *
  have h_tri1 : o^2 < 2 * n ∨ 2 * n < o^2 := by omega
  have h_tri2 : (oddPart n / o)^2 < 2 * n ∨ 2 * n < (oddPart n / o)^2 := by omega
  rcases h_tri1 with h1_lt | h1_gt
  · rcases h_tri2 with h2_lt | h2_gt
    · split_ifs with h_cond <;> try omega
    · split_ifs with h_cond <;> try omega
  · rcases h_tri2 with h2_lt | h2_gt
    · split_ifs with h_cond <;> try omega
    · exfalso
      exact h_not_both ⟨h1_gt, h2_gt⟩

lemma card_odd_divisors_eq_sum (n : ℕ) (hn : n ≠ 0) :
    (↑(((divisors n).filter (fun d => d % 2 = 1)).card) : ℤ) = ∑ o ∈ divisors (oddPart n), (1 : ℤ) := by
  rw [divisors_filter_odd_eq n hn]
  rw [card_eq_sum_ones]
  push_cast
  rfl


lemma card_middle_divisors_eq_sum (n : ℕ) (hn : n ≠ 0) :
    (↑(((divisors n).filter (fun d => n ≤ 2 * d^2 ∧ d^2 < 2 * n)).card) : ℤ) =
    ∑ o ∈ divisors (oddPart n), (if o^2 < 2 * n ∧ (oddPart n / o)^2 < 2 * n then 1 else 0 : ℤ) := by
  rw [card_M_eq_sum_if n hn]
  push_cast
  rfl




def A281009 (n : ℕ) : ℤ :=
  if h : n = 0 then
    0
  else
    let odd_div_count : ℕ := (divisors n).filter (fun d => d % 2 = 1) |>.card
    let middle_div_condition (d : ℕ) : Prop := n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n
    let middle_div_count : ℕ := (divisors n).filter middle_div_condition |>.card
    (odd_div_count : ℤ) - (middle_div_count : ℤ)

theorem oeis_281009_conjecture_0 (n : ℕ) (hn : n ≠ 0) :
    (A281009 n : ℤ) = 2 * (↑(((divisors n).filter (fun d => d % 2 = 1 ∧ 2 * n < d ^ 2)).card) : ℤ) := by
  unfold A281009
  split_ifs with h_zero
  · contradiction
  · dsimp only
    have h_odd : (↑(((divisors n).filter (fun d => d % 2 = 1)).card) : ℤ) = ∑ o ∈ divisors (oddPart n), (1 : ℤ) := card_odd_divisors_eq_sum n hn
    have h_mid : (↑(((divisors n).filter (fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n)).card) : ℤ) =
      ∑ o ∈ divisors (oddPart n), (if o^2 < 2 * n ∧ (oddPart n / o)^2 < 2 * n then 1 else 0 : ℤ) := card_middle_divisors_eq_sum n hn
    have h_gt : (↑(((divisors n).filter (fun d => d % 2 = 1 ∧ 2 * n < d ^ 2)).card) : ℤ) =
      ∑ o ∈ divisors (oddPart n), (if 2 * n < o^2 then 1 else 0 : ℤ) := by
      have h_eq_filter : (divisors n).filter (fun d => d % 2 = 1 ∧ 2 * n < d^2) =
                         ((divisors n).filter (fun d => d % 2 = 1)).filter (fun d => 2 * n < d^2) := by
        ext d
        rw [mem_filter, mem_filter, mem_filter]
        tauto
      rw [h_eq_filter, divisors_filter_odd_eq n hn]
      rw [card_eq_sum_ones]
      push_cast
      rw [sum_filter]
    have h_sum_identity : ∑ o ∈ divisors (oddPart n), (if o^2 < 2 * n ∧ (oddPart n / o)^2 < 2 * n then 1 else 0 : ℤ) =
                          ∑ o ∈ divisors (oddPart n), (1 - (if 2 * n < o^2 then 1 else 0) - (if 2 * n < (oddPart n / o)^2 then 1 else 0) : ℤ) := by
      apply Finset.sum_congr rfl
      intro o ho
      rw [mem_divisors] at ho
      have ho_odd : o % 2 = 1 := by
        have h_odd_n := oddPart_odd n hn
        exact odd_of_dvd_odd (oddPart n) o h_odd_n ho.1
      exact indicator_identity n hn o ho_odd ho.1
    have h_sum_div : ∑ o ∈ divisors (oddPart n), (if 2 * n < (oddPart n / o)^2 then 1 else 0 : ℤ) =
                     ∑ o ∈ divisors (oddPart n), (if 2 * n < o^2 then 1 else 0 : ℤ) := by
      exact Nat.sum_div_divisors (oddPart n) (fun x : ℕ => (if 2 * n < x^2 then 1 else 0 : ℤ))
    have h_distrib : ∑ o ∈ divisors (oddPart n), (1 - (if 2 * n < o^2 then 1 else 0) - (if 2 * n < (oddPart n / o)^2 then 1 else 0) : ℤ) =
                     (∑ o ∈ divisors (oddPart n), (1 : ℤ)) -
                     (∑ o ∈ divisors (oddPart n), (if 2 * n < o^2 then 1 else 0 : ℤ)) -
                     (∑ o ∈ divisors (oddPart n), (if 2 * n < (oddPart n / o)^2 then 1 else 0 : ℤ)) := by
      simp only [sum_sub_distrib]
    rw [h_odd, h_mid, h_gt, h_sum_identity, h_distrib, h_sum_div]
    omega




