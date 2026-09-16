import FormalConjectures.Util.ProblemImports
import Submission.SpecLemmas

/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

lemma minFac_eq_of_dvd_of_not_dvd {x p : ℕ} (hx : x > 1) (hp : p.Prime) (hdvd : p ∣ x) (hnot : ∀ q < p, q.Prime → ¬ q ∣ x) : x.minFac = p := by
  have h_ne_one : x ≠ 1 := by omega
  have h1 : x.minFac ∣ x := Nat.minFac_dvd x
  have h2 : x.minFac.Prime := Nat.minFac_prime h_ne_one
  have hp2 : 2 ≤ p := hp.two_le
  have h3 : x.minFac ≤ p := Nat.minFac_le_of_dvd hp2 hdvd
  rcases lt_trichotomy x.minFac p with hlt | heq | hgt
  · exfalso
    exact hnot x.minFac hlt h2 h1
  · exact heq
  · exfalso
    linarith

lemma not_dvd_of_zmod {x p : ℕ} (h : ((x : ℕ) : ZMod p) ≠ 0) : ¬ p ∣ x := by
  intro hdvd
  have h_eq_zero : (x : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p x).mpr hdvd
  exact h h_eq_zero

lemma dvd_of_zmod {x p : ℕ} (h : ((x : ℕ) : ZMod p) = 0) : p ∣ x := by
  exact (CharP.cast_eq_zero_iff (ZMod p) p x).mp h

/-- OEIS A248802 Conjecture 1: a(10n+2) = 67 for n >= 0. -/
theorem oeis_248802_conjecture_0 (n : ℕ) : a (10 * n + 2) = 67 := by
  unfold a
  apply minFac_eq_of_dvd_of_not_dvd
  · have h1 : 2 ^ (2 ^ (10 * n + 2) + 2) + 3 ≥ 3 := Nat.le_add_left 3 _
    omega
  · decide
  · apply dvd_of_zmod
    push_cast
    exact p67_is_dvd n
  · intro q hq hq_prime
    interval_cases q
    · have h_not : ¬ Nat.Prime 0 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 1 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p2_not_dvd n
    · apply not_dvd_of_zmod; push_cast; exact p3_not_dvd n
    · have h_not : ¬ Nat.Prime 4 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p5_not_dvd n
    · have h_not : ¬ Nat.Prime 6 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p7_not_dvd n
    · have h_not : ¬ Nat.Prime 8 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 9 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 10 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p11_not_dvd n
    · have h_not : ¬ Nat.Prime 12 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p13_not_dvd n
    · have h_not : ¬ Nat.Prime 14 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 15 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 16 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p17_not_dvd n
    · have h_not : ¬ Nat.Prime 18 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p19_not_dvd n
    · have h_not : ¬ Nat.Prime 20 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 21 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 22 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p23_not_dvd n
    · have h_not : ¬ Nat.Prime 24 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 25 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 26 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 27 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 28 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p29_not_dvd n
    · have h_not : ¬ Nat.Prime 30 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p31_not_dvd n
    · have h_not : ¬ Nat.Prime 32 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 33 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 34 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 35 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 36 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p37_not_dvd n
    · have h_not : ¬ Nat.Prime 38 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 39 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 40 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p41_not_dvd n
    · have h_not : ¬ Nat.Prime 42 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p43_not_dvd n
    · have h_not : ¬ Nat.Prime 44 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 45 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 46 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p47_not_dvd n
    · have h_not : ¬ Nat.Prime 48 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 49 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 50 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 51 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 52 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p53_not_dvd n
    · have h_not : ¬ Nat.Prime 54 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 55 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 56 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 57 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 58 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p59_not_dvd n
    · have h_not : ¬ Nat.Prime 60 := by decide
      exfalso; exact h_not hq_prime
    · apply not_dvd_of_zmod; push_cast; exact p61_not_dvd n
    · have h_not : ¬ Nat.Prime 62 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 63 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 64 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 65 := by decide
      exfalso; exact h_not hq_prime
    · have h_not : ¬ Nat.Prime 66 := by decide
      exfalso; exact h_not hq_prime

theorem oeis_248802_conjecture_0.disproof : ¬ (type_of% @oeis_248802_conjecture_0) := sorry
#print axioms oeis_248802_conjecture_0
