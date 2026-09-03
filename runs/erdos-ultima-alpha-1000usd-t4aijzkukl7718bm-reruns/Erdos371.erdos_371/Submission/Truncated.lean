import FormalConjecturesUtil

/-! Finite-cutoff symmetry for the largest-prime-factor comparison. -/

namespace Erdos371Exploration

/-- Keep just the prime divisors present in a fixed modulus. -/
def cut (Q n : ℕ) : ℕ := Nat.maxPrimeFac (Nat.gcd n Q)

lemma cut_periodic (Q n : ℕ) : cut Q (n + Q) = cut Q n := by
  simp [cut, Nat.gcd_add_self_left]

lemma cut_reflect (Q n : ℕ) (hn : n ≤ Q) : cut Q (Q - n) = cut Q n := by
  simp only [cut, Nat.gcd_self_sub_left hn]

lemma cut_consecutive_ne {Q : ℕ} (hQ : 0 < Q) (h2 : 2 ∣ Q) (n : ℕ) :
    cut Q (n + 1) ≠ cut Q n := by
  intro h
  have hd : cut Q (n + 1) ∣ n + 1 :=
    Nat.dvd_trans Nat.maxPrimeFac_dvd (Nat.gcd_dvd_left _ _)
  have hd' : cut Q (n + 1) ∣ n := by
    rw [h]
    exact Nat.dvd_trans Nat.maxPrimeFac_dvd (Nat.gcd_dvd_left _ _)
  have h1 : cut Q (n + 1) = 1 :=
    Nat.dvd_one.mp ((Nat.dvd_add_iff_right hd').mpr hd)
  have hp : 2 ∣ n ∨ 2 ∣ n + 1 := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  rcases hp with hp | hp
  · have hh : 2 ≤ cut Q n :=
      Nat.le_maxPrimeFac (Nat.ne_of_gt (Nat.gcd_pos_of_pos_right n hQ))
        Nat.prime_two (Nat.dvd_gcd hp h2)
    omega
  · have hh : 2 ≤ cut Q (n + 1) :=
      Nat.le_maxPrimeFac (Nat.ne_of_gt (Nat.gcd_pos_of_pos_right (n + 1) hQ))
        Nat.prime_two (Nat.dvd_gcd hp h2)
    omega

lemma cut_reflect_comparison {Q : ℕ} (hQ : 0 < Q) (h2 : 2 ∣ Q)
    {n : ℕ} (hn : n < Q) :
    (cut Q (Q - 1 - n) < cut Q (Q - 1 - n + 1)) ↔
      ¬(cut Q n < cut Q (n + 1)) := by
  have hsub : Q - 1 - n = Q - (n + 1) := by omega
  have hadd : Q - 1 - n + 1 = Q - n := by omega
  rw [hadd, hsub, cut_reflect Q n (by omega),
    cut_reflect Q (n + 1) (by omega)]
  have hne := cut_consecutive_ne hQ h2 n
  omega

lemma cut_count_half_period {Q : ℕ} (hQ : 0 < Q) (h2 : 2 ∣ Q) :
    2 * ((Finset.range Q).filter (fun n => cut Q n < cut Q (n + 1))).card = Q := by
  let p := fun n => cut Q n < cut Q (n + 1)
  have hr {n : ℕ} (hn : n < Q) : p (Q - 1 - n) ↔ ¬p n :=
    cut_reflect_comparison hQ h2 hn
  have hh : ((Finset.range Q).filter p).card =
      ((Finset.range Q).filter (fun n => ¬p n)).card := by
    apply Finset.card_bij' (fun n _ => Q - 1 - n) (fun n _ => Q - 1 - n)
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      constructor
      · omega
      · rw [hr hn.1]
        exact not_not.mpr hn.2
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨by omega, (hr hn.1).mpr hn.2⟩
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      omega
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      omega
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.range Q) p
  simp only [Finset.card_range] at hc
  change 2 * ((Finset.range Q).filter p).card = Q
  omega

lemma factorial_cut_eventually_eq (n : ℕ) (hn : 0 < n) :
    ∀ k ≥ n, cut k.factorial n = Nat.maxPrimeFac n := by
  intro k hk
  rw [cut, Nat.gcd_eq_left_iff_dvd.mpr (Nat.dvd_factorial hn hk)]

end Erdos371Exploration
