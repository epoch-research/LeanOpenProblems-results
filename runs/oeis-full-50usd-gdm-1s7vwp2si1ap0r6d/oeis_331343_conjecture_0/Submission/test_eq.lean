import FormalConjectures.Util.ProblemImports

open Nat

-- Let's put a skeleton of the definitions and hypotheses to see if it compiles
def L_seq (n : ℕ) : ℕ := (Finset.Ico 1 (n + 1)).lcm id

lemma L_seq_ne_zero (m : ℕ) (hm : m ≥ 1) : L_seq m ≠ 0 := sorry

lemma padicValNat_gcd {p A B : ℕ} [hp : Fact p.Prime] (hA : A ≠ 0) (hB : B ≠ 0) :
    padicValNat p (A.gcd B) = min (padicValNat p A) (padicValNat p B) := sorry

lemma pow_p_dvd_L (p : ℕ) [hp : Fact p.Prime] {m k : ℕ} (hm : m ≥ 1) (hk : p^k ≤ m) : p^k ∣ L_seq m := sorry

lemma vp_L_ne_vp_n {n : ℕ} (hn : n ≥ 15) (hp : ¬ Nat.Prime n) (h_odd : n % 2 = 1) :
    let p := Nat.minFac n
    padicValNat p (L_seq (n - 1)) ≠ padicValNat p n := sorry

lemma test_derivation {n : ℕ} (hn15 : n ≥ 15) (hp : ¬ Nat.Prime n) (h_odd : n % 2 = 1) :
    let p := Nat.minFac n
    let L := L_seq (n - 1)
    let g := Nat.gcd L n
    let k := padicValNat p n
    padicValNat p (L / g) = 0 → n = p^k := by
  intro p L g k h_case2_2
  have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have h_ne_n : n ≠ 0 := by omega
  have h_ne_L : L ≠ 0 := L_seq_ne_zero (n - 1) (by omega)
  have h_ne_g : g ≠ 0 := by
    intro hc
    have : g ∣ n := Nat.gcd_dvd_right L n
    rw [hc] at this
    have : n = 0 := Nat.eq_zero_of_zero_dvd this
    omega
  have h_mul_L : L = g * (L / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left L n)).symm
  have h_val_L : padicValNat p L = padicValNat p g + padicValNat p (L / g) := by
    nth_rw 1 [h_mul_L]
    rw [padicValNat.mul h_ne_g (by
      intro hc
      have : L = 0 := by rw [h_mul_L, hc, mul_zero]
      contradiction)]
  have h_L_eq_g : padicValNat p L = padicValNat p g := by
    rw [h_case2_2] at h_val_L
    omega
  have h_ne_vp : padicValNat p L ≠ padicValNat p n := vp_L_ne_vp_n hn15 hp h_odd
  have h_gcd : padicValNat p g = min (padicValNat p L) (padicValNat p n) := padicValNat_gcd h_ne_L h_ne_n
  rw [← h_L_eq_g] at h_gcd
  have h_L_lt_n : padicValNat p L < k := by
    have h_min : padicValNat p L = min (padicValNat p L) k := h_gcd
    have h_cases : padicValNat p L < k ∨ padicValNat p L = k ∨ padicValNat p L > k := by omega
    rcases h_cases with h1 | h2 | h3
    · exact h1
    · contradiction
    · have : min (padicValNat p L) k = k := by omega
      omega
  have h_lt_pk : n - 1 < p^k := by
    by_contra hc
    push_neg at hc
    have hdvd_L : p^k ∣ L := pow_p_dvd_L p (by omega) hc
    have h_le_vp : k ≤ padicValNat p L := by
      have h_dvd_iff : p^k ∣ L ↔ L = 0 ∨ k ≤ padicValNat p L := padicValNat_dvd_iff k L
      rw [h_dvd_iff] at hdvd_L
      rcases hdvd_L with h_zero | h_le
      · contradiction
      · exact h_le
    omega
  have h_pk_le_n : p^k ≤ n := by
    have hdvd_n : p^k ∣ n := pow_padicValNat_dvd
    exact Nat.le_of_dvd (by omega) hdvd_n
  have h_n_eq : n = p^k := by omega
  exact h_n_eq
