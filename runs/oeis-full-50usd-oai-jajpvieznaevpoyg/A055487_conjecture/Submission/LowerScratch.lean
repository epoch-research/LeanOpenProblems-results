import FormalConjectures.Util.ProblemImports
open Set
open Nat

noncomputable def A055487 (n : ℕ) : ℕ :=
  sInf {m : ℕ | Nat.totient m = Nat.factorial n}

def prime_candidates (n : ℕ) : Set ℕ :=
  let N := Nat.factorial n
  { p : ℕ | Nat.Prime p ∧ Nat.sqrt N < p ∧ (p - 1) ∣ N ∧ Nat.Prime (N / (p - 1) + 1) }

lemma totient_preimage_ge_succ_of_gt_one (a M : ℕ) (ha : Nat.totient a = M) (hM : 1 < M) :
    M + 1 ≤ a := by
  have ha_pos : 0 < a := by
    by_contra hz
    have : a = 0 := Nat.eq_zero_of_not_pos hz
    rw [this, Nat.totient_zero] at ha
    omega
  have hlt : Nat.totient a < a := by
    by_cases h1 : a = 1
    · rw [h1, Nat.totient_one] at ha
      omega
    have ha_gt : 1 < a := by omega
    exact Nat.totient_lt a ha_gt
  omega

lemma lower_from_factor (N r a : ℕ) (hr : Nat.Prime r) (hcop : r.Coprime a)
    (hphi : Nat.totient (r * a) = N) (hM : 1 < N / (r - 1)) :
    r * (N / (r - 1) + 1) ≤ r * a := by
  have htot : Nat.totient a = N / (r - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hr] at hphi
    have hrpos : 0 < r - 1 := Nat.sub_pos_of_lt hr.one_lt
    rw [← hphi]
    exact (Nat.mul_div_right (Nat.totient a) hrpos).symm
  exact Nat.mul_le_mul_left r (totient_preimage_ge_succ_of_gt_one a (N / (r - 1)) htot hM)
