import Mathlib

open Nat Finset BigOperators

/-!
Legendre lemma (input (ii) of the proof).

`c m n = (m*n)! / (n!)^m` is the multinomial coefficient.
Its p-adic valuation is `v_p(c m n) = ∑_{i≥1} (⌊mn/p^i⌋ - m⌊n/p^i⌋)`.

MAIN GOAL of this file:
  if `p^j ∣ (c + e)`, `p ∤ c`, `p ∤ e`, then
  `padicValNat p (cmul m c) + padicValNat p (cmul m e) ≥ (m-1)*j`.
-/

namespace LegLemma

/-- The multinomial coefficient `(m n)! / (n!)^m`. -/
def cmul (m n : ℕ) : ℕ := (m * n).factorial / (n.factorial ^ m)

/-- `(n!)^m ∣ (m*n)!` so `cmul` is exact. -/
lemma pow_factorial_dvd (m n : ℕ) : (n.factorial ^ m) ∣ (m * n).factorial := by
  have h := Nat.prod_factorial_dvd_factorial_sum (Finset.range m) (fun _ => n)
  simpa [Finset.prod_const, Finset.sum_const, mul_comm] using h

lemma cmul_mul (m n : ℕ) : cmul m n * (n.factorial ^ m) = (m * n).factorial := by
  rw [cmul, Nat.div_mul_cancel (pow_factorial_dvd m n)]

lemma cmul_ne_zero (m n : ℕ) : cmul m n ≠ 0 := by
  intro h
  have := cmul_mul m n
  rw [h, zero_mul] at this
  exact (Nat.factorial_ne_zero _) this.symm

variable (p : ℕ)

/-- The valuation of `cmul` equals `v_p((mn)!) - m v_p(n!)` via the exact product. -/
lemma padicValNat_cmul_add [hp : Fact p.Prime] (m n : ℕ) :
    padicValNat p (cmul m n) + m * padicValNat p (n.factorial) = padicValNat p ((m * n).factorial) := by
  have hne1 : cmul m n ≠ 0 := cmul_ne_zero m n
  have hne2 : (n.factorial ^ m) ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  have := cmul_mul m n
  have h1 : padicValNat p (cmul m n * (n.factorial ^ m)) = padicValNat p ((m*n).factorial) := by
    rw [this]
  rw [padicValNat.mul hne1 hne2, padicValNat.pow _ (Nat.factorial_ne_zero _)] at h1
  omega

/-- Legendre valuation as a sum over levels: `v_p(cmul m n) = ∑_{i∈[1,b)} ⌊m·(n mod p^i)/p^i⌋`
whenever `b` is large enough (`log p (m*n) < b`). -/
lemma padicValNat_cmul_sum [hp : Fact p.Prime] (m n b : ℕ) (hm : 1 ≤ m)
    (hb : Nat.log p (m * n) < b) :
    padicValNat p (cmul m n) = ∑ i ∈ Finset.Ico 1 b, (m * (n % p ^ i)) / p ^ i := by
  have hbn : Nat.log p n < b :=
    lt_of_le_of_lt (Nat.log_mono_right (Nat.le_mul_of_pos_left n (by omega))) hb
  have key := padicValNat_cmul_add p m n
  rw [padicValNat_factorial hb, padicValNat_factorial hbn, Finset.mul_sum] at key
  -- key : v_p(cmul) + ∑ m*(n/p^i) = ∑ (m*n)/p^i
  have hterm : ∀ i ∈ Finset.Ico 1 b, (m * n) / p ^ i = m * (n / p ^ i) + (m * (n % p ^ i)) / p ^ i := by
    intro i _
    have hp0 : 0 < p ^ i := pow_pos hp.out.pos i
    have hmn : m * n = p ^ i * (m * (n / p ^ i)) + m * (n % p ^ i) := by
      conv_lhs => rw [← Nat.div_add_mod n (p ^ i)]
      ring
    rw [hmn, Nat.mul_add_div hp0]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib] at key
  omega

/-- Pure arithmetic core: `m*P = P*A + P*B + (r1+r2)` with `r1+r2 < 2P` forces `m-1 ≤ A+B`. -/
lemma arith_core (m P A B R : ℕ) (hP : 0 < P) (hc : m * P = P * A + P * B + R)
    (hr : R < 2 * P) : m - 1 ≤ A + B := by
  by_contra hcon
  push_neg at hcon
  have hle : (A + B + 2) * P ≤ m * P := Nat.mul_le_mul_right _ (by omega)
  have hexp : (A + B + 2) * P = P * A + P * B + 2 * P := by ring
  omega

/-- Per-level bound: if `rc + re = P`, `1 ≤ rc`, `1 ≤ re`, then `⌊m rc/P⌋ + ⌊m re/P⌋ ≥ m-1`. -/
lemma per_level_bound (m P rc re : ℕ) (hP : 0 < P) (hsum : rc + re = P) :
    m - 1 ≤ (m * rc) / P + (m * re) / P := by
  have h1 : m * rc = P * ((m * rc) / P) + (m * rc) % P := (Nat.div_add_mod _ _).symm
  have h2 : m * re = P * ((m * re) / P) + (m * re) % P := (Nat.div_add_mod _ _).symm
  have h3 : (m * rc) % P < P := Nat.mod_lt _ hP
  have h4 : (m * re) % P < P := Nat.mod_lt _ hP
  have hmul : m * rc + m * re = m * P := by rw [← Nat.mul_add, hsum]
  refine arith_core m P ((m * rc) / P) ((m * re) / P) ((m * rc) % P + (m * re) % P) hP ?_ (by omega)
  omega

/-- **Legendre lemma (input (ii))**: if `p^j ∣ (c+e)`, `p ∤ c`, `p ∤ e`, then
`v_p(cmul m c) + v_p(cmul m e) ≥ (m-1)·j`. -/
theorem legendre_lemma [hp : Fact p.Prime] {m c e j : ℕ} (hm : 1 ≤ m)
    (hc : ¬ p ∣ c) (he : ¬ p ∣ e) (hdvd : p ^ j ∣ (c + e)) :
    (m - 1) * j ≤ padicValNat p (cmul m c) + padicValNat p (cmul m e) := by
  set b := Nat.log p (m * c) + Nat.log p (m * e) + j + 1 with hbdef
  have hbc : Nat.log p (m * c) < b := by omega
  have hbe : Nat.log p (m * e) < b := by omega
  rw [padicValNat_cmul_sum p m c b hm hbc, padicValNat_cmul_sum p m e b hm hbe,
      ← Finset.sum_add_distrib]
  have hsub : Finset.Ico 1 (j + 1) ⊆ Finset.Ico 1 b :=
    Finset.Ico_subset_Ico (le_refl 1) (by omega)
  -- lower bound the subsum by (m-1) per term
  have hterm : ∀ i ∈ Finset.Ico 1 (j + 1),
      m - 1 ≤ (m * (c % p ^ i)) / p ^ i + (m * (e % p ^ i)) / p ^ i := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi1 : 1 ≤ i := hi.1
    have hij : i ≤ j := by omega
    have hp0 : 0 < p ^ i := pow_pos hp.out.pos i
    have hdvdi : p ^ i ∣ (c + e) := dvd_trans (pow_dvd_pow p hij) hdvd
    have hrc : c % p ^ i ≠ 0 := fun h =>
      hc (dvd_trans (dvd_pow_self p (by omega : i ≠ 0)) (Nat.dvd_of_mod_eq_zero h))
    have hre : e % p ^ i ≠ 0 := fun h =>
      he (dvd_trans (dvd_pow_self p (by omega : i ≠ 0)) (Nat.dvd_of_mod_eq_zero h))
    have hmodc : c % p ^ i < p ^ i := Nat.mod_lt _ hp0
    have hmode : e % p ^ i < p ^ i := Nat.mod_lt _ hp0
    have hcpos : 0 < c % p ^ i := Nat.pos_of_ne_zero hrc
    have hsum : c % p ^ i + e % p ^ i = p ^ i := by
      have hdvd2 : p ^ i ∣ (c % p ^ i + e % p ^ i) := by
        apply Nat.dvd_of_mod_eq_zero
        rw [← Nat.add_mod]; exact Nat.dvd_iff_mod_eq_zero.mp hdvdi
      obtain ⟨k, hk⟩ := hdvd2
      have hk1 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · exfalso; rw [h, mul_zero] at hk
          exact hrc (Nat.eq_zero_of_add_eq_zero_right hk)
        · exact h
      have hlt : c % p ^ i + e % p ^ i < p ^ i * 2 := by omega
      rw [hk] at hlt
      have hk2 : k < 2 := Nat.lt_of_mul_lt_mul_left hlt
      have hk3 : k = 1 := by omega
      rw [hk, hk3, mul_one]
    exact per_level_bound m (p ^ i) (c % p ^ i) (e % p ^ i) hp0 hsum
  calc (m - 1) * j
      = ∑ _i ∈ Finset.Ico 1 (j + 1), (m - 1) := by
        rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel, smul_eq_mul]
        exact Nat.mul_comm _ _
    _ ≤ ∑ i ∈ Finset.Ico 1 (j + 1),
          ((m * (c % p ^ i)) / p ^ i + (m * (e % p ^ i)) / p ^ i) := Finset.sum_le_sum hterm
    _ ≤ ∑ i ∈ Finset.Ico 1 b,
          ((m * (c % p ^ i)) / p ^ i + (m * (e % p ^ i)) / p ^ i) :=
        Finset.sum_le_sum_of_subset hsub

end LegLemma
