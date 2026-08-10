import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

theorem minFac_lt_of_composite (n : ℕ) (hn1 : n ≠ 1) (hn0 : n ≠ 0) (hnp : ¬ Nat.Prime n) :
    n.minFac < n := by
  have hp_prime : Nat.Prime n.minFac := Nat.minFac_prime hn1
  have hp_dvd : n.minFac ∣ n := Nat.minFac_dvd n
  rcases hp_dvd with ⟨m, hm⟩
  have hp_ge2 : 2 ≤ n.minFac := hp_prime.two_le
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    rw [← hm] at hp_prime
    exact hnp hp_prime
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact hn0 hm
  have hm_ge2 : 2 ≤ m := by omega
  have h_le_m : n.minFac ≤ m := by
    apply Nat.minFac_le_of_dvd hm_ge2
    rw [hm]
    exact dvd_mul_left m n.minFac
  have : 1 < m := by omega
  nth_rw 2 [hm]
  have h_pos : 0 < n.minFac := by omega
  exact lt_mul_of_one_lt_right h_pos this


lemma sum_erase_two {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) {x y : α} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    ∑ i ∈ s, f i = f x + f y + ∑ i ∈ (s.erase x).erase y, f i := by
  rw [← Finset.add_sum_erase s f hx]
  have hy_erase : y ∈ s.erase x := by
    rw [Finset.mem_erase]
    exact ⟨hne.symm, hy⟩
  rw [← Finset.add_sum_erase (s.erase x) f hy_erase]
  omega

theorem sum_composite_ge (n : ℕ) (hn1 : n ≠ 1) (hn0 : n ≠ 0) (h_comp : ¬ Nat.Prime n) :
    ∑ k ∈ Finset.Ico 1 n, Nat.gcd k n ≥ n := by
  let d := n.minFac
  have hd_prime : Nat.Prime d := Nat.minFac_prime hn1
  have hd_dvd : d ∣ n := Nat.minFac_dvd n
  have hd_lt : d < n := minFac_lt_of_composite n hn1 hn0 h_comp
  have hd_ge2 : 2 ≤ d := hd_prime.two_le
  have hn_gt2 : 2 < n := by omega
  have h1 : 1 ∈ Finset.Ico 1 n := by
    rw [Finset.mem_Ico]
    omega
  have hd : d ∈ Finset.Ico 1 n := by
    rw [Finset.mem_Ico]
    omega
  have h_ne : 1 ≠ d := by omega
  have h_split := sum_erase_two (Finset.Ico 1 n) (fun k => Nat.gcd k n) h1 hd h_ne
  rw [h_split]
  dsimp only
  have h_gcd1 : Nat.gcd 1 n = 1 := Nat.gcd_one_left n
  have h_gcd_d : Nat.gcd d n = d := Nat.gcd_eq_left hd_dvd
  rw [h_gcd1, h_gcd_d]
  have h_card1 : (Finset.Ico 1 n).card = n - 1 := by
    rw [card_Ico]
  have h_card2 : ((Finset.Ico 1 n).erase 1).card = n - 2 := by
    rw [Finset.card_erase_of_mem h1, h_card1]
    omega
  have h_mem_erase1 : d ∈ (Finset.Ico 1 n).erase 1 := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm h_ne, hd⟩
  have h_card3 : (((Finset.Ico 1 n).erase 1).erase d).card = n - 3 := by
    rw [Finset.card_erase_of_mem h_mem_erase1, h_card2]
    omega
  have h_sum_ge : ∑ k ∈ ((Finset.Ico 1 n).erase 1).erase d, Nat.gcd k n ≥ n - 3 := by
    have h_const : ∑ k ∈ ((Finset.Ico 1 n).erase 1).erase d, 1 = n - 3 := by
      rw [Finset.sum_const, smul_eq_mul, mul_one]
      exact h_card3
    rw [← h_const]
    apply Finset.sum_le_sum
    intro k hk
    have hn_pos : 0 < n := by omega
    have hg_pos : 0 < Nat.gcd k n := Nat.gcd_pos_of_pos_right k hn_pos
    omega
  omega
lemma gcd_le_third (n : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < n) (hk3 : k ≠ n / 2) (hn : 6 ≤ n) : Nat.gcd k n ≤ n / 3 := by
  have hdvd : Nat.gcd k n ∣ n := Nat.gcd_dvd_right k n
  rcases hdvd with ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    omega
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc
    have hg_dvd : Nat.gcd k n ∣ k := Nat.gcd_dvd_left k n
    rw [← hc] at hg_dvd
    have : n ≤ k := Nat.le_of_dvd (by omega) hg_dvd
    omega
  have hc2 : c ≠ 2 := by
    rintro rfl
    rw [mul_two] at hc
    have hg_dvd : Nat.gcd k n ∣ k := Nat.gcd_dvd_left k n
    have hn_even : 2 ∣ n := by
      use Nat.gcd k n
      omega
    have h_gcd_eq : Nat.gcd k n = n / 2 := by
      omega
    rw [h_gcd_eq] at hg_dvd
    rcases hg_dvd with ⟨a, ha⟩
    rw [ha] at hk2
    rcases a with _ | _ | a
    · omega
    · have : n / 2 * 1 = n / 2 := by omega
      rw [this] at hk2
      rw [ha] at hk3
      rw [this] at hk3
      exact hk3 rfl
    · have h_eq2 : n / 2 * 2 = n := by omega
      have h_le : n / 2 * 2 ≤ n / 2 * (a + 2) := Nat.mul_le_mul_left (n / 2) (by omega)
      rw [h_eq2] at h_le
      have h_eq3 : a + 1 + 1 = a + 2 := by omega
      rw [h_eq3] at hk2
      omega
  have hc_ge3 : 3 ≤ c := by omega
  have : Nat.gcd k n * 3 ≤ Nat.gcd k n * c := Nat.mul_le_mul_left (Nat.gcd k n) hc_ge3
  rw [← hc] at this
  omega
lemma gcd_le_third_odd (n : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hn_odd : ¬ 2 ∣ n) (hk2 : k < n) : Nat.gcd k n ≤ n / 3 := by
  have hdvd : Nat.gcd k n ∣ n := Nat.gcd_dvd_right k n
  rcases hdvd with ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    omega
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc
    have hg_dvd : Nat.gcd k n ∣ k := Nat.gcd_dvd_left k n
    rw [← hc] at hg_dvd
    have : n ≤ k := Nat.le_of_dvd hk1 hg_dvd
    omega
  have hc_odd : ¬ 2 ∣ c := by
    rintro ⟨x, rfl⟩
    have : 2 ∣ n := by
      use x * Nat.gcd k n
      nth_rw 1 [hc]
      ring
    exact hn_odd this
  have hc_ge3 : 3 ≤ c := by omega
  have : Nat.gcd k n * 3 ≤ Nat.gcd k n * c := Nat.mul_le_mul_left (Nat.gcd k n) hc_ge3
  rw [← hc] at this
  omega
theorem S_mod_p_sq (p L : ℕ) (hp : Nat.Prime p) : p ∣ (Finset.Ico 1 (p^2 * L + 1)).sum (fun k => Nat.gcd k (p^2 * L)) := by
  sorry
lemma gcd_add_mul_self_left (a b c : ℕ) : Nat.gcd (a * b + c) b = Nat.gcd c b := by
  induction a with
  | zero =>
    rw [zero_mul, zero_add]
  | succ a ih =>
    rw [succ_mul]
    have : a * b + b + c = (a * b + c) + b := by omega
    rw [this]
    rw [Nat.gcd_add_self_left]
    exact ih

lemma gcd_le_half (n : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < n) (hn : 2 ≤ n) : Nat.gcd k n ≤ n / 2 := by
  have hdvd : Nat.gcd k n ∣ n := Nat.gcd_dvd_right k n
  rcases hdvd with ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    omega
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc
    have hg_dvd : Nat.gcd k n ∣ k := Nat.gcd_dvd_left k n
    rw [← hc] at hg_dvd
    have : n ≤ k := Nat.le_of_dvd (by omega) hg_dvd
    omega
  have hc_ge2 : 2 ≤ c := by omega
  have : Nat.gcd k n * 2 ≤ Nat.gcd k n * c := Nat.mul_le_mul_left (Nat.gcd k n) hc_ge2
  rw [← hc] at this
  omega
theorem sum_composite_le (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.Ico 1 n, Nat.gcd k n ≤ (n - 1) * (n / 2) := by
  have h_const : ∑ k ∈ Finset.Ico 1 n, (n / 2) = (n - 1) * (n / 2) := by
    rw [Finset.sum_const, card_Ico, smul_eq_mul]
  rw [← h_const]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact gcd_le_half n k hk.1 hk.2 hn


