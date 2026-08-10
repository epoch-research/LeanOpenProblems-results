import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

lemma prime_gcd_eq_one_of_lt {p m : ℕ} (hp : Nat.Prime p) (hm0 : m ≠ 0) (hmp : m < p) : Nat.gcd m p = 1 := by
  rw [Nat.gcd_comm]
  have h_min : minFac p = p := Nat.Prime.minFac_eq hp
  have h_lt : m < minFac p := by rwa [h_min]
  exact gcd_eq_one_of_lt_minFac hm0 h_lt

lemma prime_sum_gcd {p : ℕ} (hp : Nat.Prime p) :
    (Finset.Ico 1 p).sum (fun k => Nat.gcd k p) = p - 1 := by
  have h_congr : (Finset.Ico 1 p).sum (fun k => Nat.gcd k p) = (Finset.Ico 1 p).sum (fun k => 1) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk0 : k ≠ 0 := by omega
    exact prime_gcd_eq_one_of_lt hp hk0 hk.2
  rw [h_congr]
  rw [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Nat.card_Ico]

lemma prime_A018804 {p : ℕ} (hp : Nat.Prime p) :
    (Finset.Ico 1 (p + 1)).sum (fun k => Nat.gcd k p) = 2 * p - 1 := by
  have hp_le : 1 ≤ p := by
    have hp2 : p ≥ 2 := Nat.Prime.two_le hp
    omega
  rw [Ico_succ_right_eq_insert_Ico hp_le]
  have hp_not_mem : p ∉ Finset.Ico 1 p := by
    rw [Finset.mem_Ico]
    omega
  rw [Finset.sum_insert hp_not_mem]
  rw [Nat.gcd_self]
  rw [prime_sum_gcd hp]
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  omega

lemma prime_a_eq_1 {p : ℕ} (hp : Nat.Prime p) : a p = 1 := by
  change p / Nat.gcd p (1 + (Finset.Ico 1 (p + 1)).sum (fun k => Nat.gcd k p)) = 1
  rw [prime_A018804 hp]
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have h_add : 1 + (2 * p - 1) = 2 * p := by omega
  rw [h_add]
  have h_gcd : Nat.gcd p (2 * p) = p := Nat.gcd_eq_left (dvd_mul_left p 2)
  rw [h_gcd]
  exact Nat.div_self (by omega)

lemma gcd_sum_eq_divisors_sum (n : ℕ) (hn : n ≠ 0) :
    (Finset.range n).sum (fun k => Nat.gcd k n) = n.divisors.sum (fun d => d * (Finset.filter (fun k => Nat.gcd k n = d) (Finset.range n)).card) := by
  have h_maps : ∀ k ∈ Finset.range n, Nat.gcd k n ∈ n.divisors := by
    intro k _
    rw [mem_divisors]
    exact ⟨Nat.gcd_dvd_right k n, hn⟩
  rw [← Finset.sum_fiberwise_of_maps_to h_maps]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have h_congr : (Finset.filter (fun k => Nat.gcd k n = d) (Finset.range n)).sum (fun k => Nat.gcd k n) =
                 (Finset.filter (fun k => Nat.gcd k n = d) (Finset.range n)).sum (fun _ => d) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_filter] at hk
    exact hk.2
  rw [h_congr]
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma gcd_sum_eq_divisors_totient (n : ℕ) (hn : n ≠ 0) :
    (Finset.range n).sum (fun k => Nat.gcd k n) = n.divisors.sum (fun d => d * φ (n / d)) := by
  rw [gcd_sum_eq_divisors_sum n hn]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have h_dvd : d ∣ n := dvd_of_mem_divisors hd
  have h_totient := totient_div_of_dvd h_dvd
  have h_card : (Finset.filter (fun k => Nat.gcd k n = d) (Finset.range n)).card = (Finset.filter (fun k => Nat.gcd n k = d) (Finset.range n)).card := by
    simp_rw [Nat.gcd_comm]
  rw [h_card]
  rw [← h_totient]

lemma A018804_eq_range_sum (n : ℕ) : (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) = (Finset.range n).sum (fun k => Nat.gcd k n) := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn1 : 1 ≤ n := hn
  rw [Ico_succ_right_eq_insert_Ico hn1]
  have hn_not_mem : n ∉ Finset.Ico 1 n := by
    rw [Finset.mem_Ico]
    omega
  rw [Finset.sum_insert hn_not_mem]
  have h_range : Finset.range n = insert 0 (Finset.Ico 1 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [h_range]
  have h0_not_mem : 0 ∉ Finset.Ico 1 n := by
    rw [Finset.mem_Ico]
    omega
  rw [Finset.sum_insert h0_not_mem]
  simp only [Nat.gcd_self, Nat.gcd_zero_left]

lemma prime_sq_dvd_A {n p : ℕ} (hp : Nat.Prime p) (hn0 : n ≠ 0) (h_sq : p ^ 2 ∣ n) : p ∣ (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) := by
  rw [A018804_eq_range_sum n]
  rw [gcd_sum_eq_divisors_totient n hn0]
  refine Finset.dvd_sum ?_
  intro d hd
  have hd_dvd : d ∣ n := dvd_of_mem_divisors hd
  by_cases hpd : p ∣ d
  · exact dvd_mul_of_dvd_left hpd _
  · have h_cop : Nat.Coprime (p ^ 2) d := by
      have h1 : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
      exact h1.pow_left 2
    have h_mul : p ^ 2 ∣ (n / d) * d := by
      rw [Nat.div_mul_cancel hd_dvd]
      exact h_sq
    have h_nd : p ^ 2 ∣ n / d := h_cop.dvd_of_dvd_mul_right h_mul
    have h_p_nd : p ∣ n / d := by
      have h_p_sq : p ∣ p ^ 2 := by
        use p
        ring
      exact dvd_trans h_p_sq h_nd
    have h_tot : p ∣ φ (n / d) := by
      have h_div_cancel : n / d = p * (n / d / p) := by
        exact (Nat.mul_div_cancel' h_p_nd).symm
      rw [h_div_cancel]
      rw [totient_mul_of_prime_of_dvd hp]
      · exact dvd_mul_right p (φ (n / d / p))
      · have h_z : p ^ 2 ∣ n / d := h_nd
        rcases h_z with ⟨z, hz⟩
        have h_eq : n / d / p = p * z := by
          rw [hz]
          have hp2_eq : p ^ 2 = p * p := by ring
          rw [hp2_eq, mul_assoc]
          exact Nat.mul_div_cancel_left (p * z) hp.pos
        rw [h_eq]
        exact dvd_mul_right p z
    exact dvd_mul_of_dvd_right h_tot d
