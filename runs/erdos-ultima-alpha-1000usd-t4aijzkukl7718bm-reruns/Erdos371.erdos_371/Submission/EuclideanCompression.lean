import FormalConjecturesUtil
import Submission.PrimeDiscrepancy
import Submission.CofactorReflection

/-! An arithmetic reduction of descents to smaller ascents.
No injectivity or density-preservation assertion is made. -/

namespace Erdos371EuclideanCompression

open Erdos371PrimeDiscrepancy

lemma prime_mod_pos {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q < p) :
    0 < p % q := by
  have hqd : ¬ q ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with he | he
    · exact hq.ne_one he
    · omega
  exact Nat.pos_of_ne_zero (fun hz => hqd (Nat.dvd_of_mod_eq_zero hz))

lemma twice_mod_le {p q : ℕ} (hq : 0 < q) (hqp : q < p) :
    2 * (p % q) ≤ p := by
  have hr := Nat.mod_lt p hq
  by_cases h : 2 * q ≤ p
  · omega
  · have hdiv : p / q = 1 := by
      apply Nat.div_eq_of_lt_le (by omega) (by omega)
    have he := Nat.mod_add_div p q
    rw [hdiv] at he
    omega

/-- The reduced cofactor and prime are both residues modulo the smaller prime. -/
def descend (n : ℕ) : ℕ :=
  ((n / P n) % P (n + 1)) * (P n % P (n + 1))

lemma descent_reduces {n : ℕ} (hn : 1 < n) (hdec : P (n + 1) < P n) :
    P (descend n) < P (n + 1) ∧
    P (descend n + 1) = P (n + 1) ∧
    2 * descend n ≤ n := by
  let p := P n
  let q := P (n + 1)
  let a := n / p
  let r := p % q
  let c := a % q
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq : q.Prime := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hqp : q < p := hdec
  have ha : a * p = n := Nat.div_mul_cancel Nat.maxPrimeFac_dvd
  have hqnext : q ∣ n + 1 := Nat.maxPrimeFac_dvd
  have hrpos : 0 < r := prime_mod_pos hp hq hqp
  have hrlt : r < q := Nat.mod_lt p hq.pos
  have hclt : c < q := Nat.mod_lt a hq.pos
  have hcpos : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hqa : q ∣ a := Nat.dvd_of_mod_eq_zero hz
    have hqn : q ∣ n := ha ▸ dvd_mul_of_dvd_left hqa p
    exact hq.not_dvd_one ((Nat.dvd_add_iff_right hqn).2 hqnext)
  have hprodmod : (c * r + 1) % q = 0 := by
    have he : (a * p + 1) % q = 0 := by
      rw [ha]
      exact Nat.mod_eq_zero_of_dvd hqnext
    simpa [c, r, Nat.add_mod, Nat.mul_mod] using he
  have hqd : q ∣ c * r + 1 := Nat.dvd_of_mod_eq_zero hprodmod
  have hbound : c * r + 1 ≤ c * q := by
    have hm := Nat.mul_le_mul_left c (show r + 1 ≤ q by omega)
    nlinarith
  have hdpos : 0 < (c * r + 1) / q :=
    Nat.div_pos (Nat.le_of_dvd (by positivity) hqd) hq.pos
  have hdle : (c * r + 1) / q ≤ c := by
    apply (Nat.div_le_div_right hbound).trans
    rw [Nat.mul_div_left _ hq.pos]
  have hfac : (c * r + 1) / q * q = c * r + 1 := Nat.div_mul_cancel hqd
  have hm : descend n = c * r := rfl
  rw [hm]
  refine ⟨?_, ?_, ?_⟩
  · rw [P, Nat.maxPrimeFac_mul (by omega) (by omega)]
    exact max_lt (Nat.maxPrimeFac_le.trans_lt hclt)
      (Nat.maxPrimeFac_le.trans_lt hrlt)
  · rw [← hfac]
    exact Erdos371Cofactor.small_cofactor_max hdpos hq (hdle.trans hclt.le)
  · have hcr : c ≤ a := Nat.mod_le a q
    have hr2 : 2 * r ≤ p := twice_mod_le hq.pos hqp
    calc
      2 * (c * r) = c * (2 * r) := by ring
      _ ≤ a * p := Nat.mul_le_mul hcr hr2
      _ = n := ha

lemma descent_strictly_reduces {n : ℕ} (hn : 1 < n) (hdec : P (n + 1) < P n) :
    descend n < n := by
  have h := (descent_reduces hn hdec).2.2
  omega

lemma compression_collision : descend 5 = 2 ∧ descend 17 = 2 := by
  decide +kernel

lemma compression_not_injective : ¬ Function.Injective descend := by
  intro h
  have he := h (compression_collision.1.trans compression_collision.2.symm)
  norm_num at he

lemma residue_product_three {a b : ℕ} (h : 3 ∣ a * b + 1) :
    (a % 3) * (b % 3) = 2 := by
  have hz : ((a % 3) * (b % 3) + 1) % 3 = 0 := by
    simpa [Nat.add_mod, Nat.mul_mod] using Nat.mod_eq_zero_of_dvd h
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp [ha, hb] at hz ⊢

lemma descend_of_loser_three {n : ℕ} (hq : P (n + 1) = 3) :
    descend n = 2 := by
  unfold descend
  rw [hq]
  apply residue_product_three
  rw [Nat.div_mul_cancel Nat.maxPrimeFac_dvd]
  rw [← hq]
  exact Nat.maxPrimeFac_dvd

lemma power_family_descends (k : ℕ) :
    P (27 ^ (k + 1) - 1 + 1) < P (27 ^ (k + 1) - 1) ∧
    descend (27 ^ (k + 1) - 1) = 2 := by
  have hp1 : 1 ≤ 27 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have hp27 : 27 ≤ 27 ^ (k + 1) := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < 27) (by omega : 1 ≤ k + 1))
  have hthree : P (27 ^ (k + 1) - 1 + 1) = 3 := by
    rw [Nat.sub_add_cancel hp1, P, Nat.maxPrimeFac_pow (by omega)]
    decide +kernel
  have h13 : 13 ∣ 27 ^ (k + 1) - 1 := by
    have hd := Nat.sub_dvd_pow_sub_pow 27 1 (k + 1)
    simp only [one_pow] at hd
    exact (by decide +kernel : 13 ∣ 27 - 1).trans hd
  have hlarge : 13 ≤ P (27 ^ (k + 1) - 1) :=
    Nat.le_maxPrimeFac (by omega) (by decide +kernel) h13
  exact ⟨by omega, descend_of_loser_three hthree⟩

/-- Even the restriction to descents has an infinite fiber.
This does not rule out estimates after discarding bounded losing primes. -/
lemma infinite_descent_fiber :
    {n | P (n + 1) < P n ∧ descend n = 2}.Infinite := by
  have hs : StrictMono (fun k : ℕ => 27 ^ (k + 1) - 1) := by
    intro a b hab
    have hpow := Nat.pow_lt_pow_right (by omega : 1 < 27)
      (by omega : a + 1 < b + 1)
    have hp1 : 1 ≤ 27 ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
    change 27 ^ (a + 1) - 1 < 27 ^ (b + 1) - 1
    omega
  apply (Set.infinite_range_of_injective hs.injective).mono
  rintro n ⟨k, rfl⟩
  exact power_family_descends k


/-- The analogous residue reduction for an ascent. -/
def ascend (n : ℕ) : ℕ :=
  (((n + 1) / P (n + 1)) % P n) * (P (n + 1) % P n) - 1

lemma ascent_reduces {n : ℕ} (hn : 1 < n) (hinc : P n < P (n + 1)) :
    (ascend n = 0 ∨
      (P (ascend n) = P n ∧ P (ascend n + 1) < P n)) ∧
    2 * ascend n < n := by
  let p := P (n + 1)
  let q := P n
  let a := (n + 1) / p
  let r := p % q
  let c := a % q
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hq : q.Prime := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hqp : q < p := hinc
  have ha : a * p = n + 1 := Nat.div_mul_cancel Nat.maxPrimeFac_dvd
  have hqn : q ∣ n := Nat.maxPrimeFac_dvd
  have hrpos : 0 < r := prime_mod_pos hp hq hqp
  have hrlt : r < q := Nat.mod_lt p hq.pos
  have hclt : c < q := Nat.mod_lt a hq.pos
  have hcpos : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hqa : q ∣ a := Nat.dvd_of_mod_eq_zero hz
    have hqnext : q ∣ n + 1 := ha ▸ dvd_mul_of_dvd_left hqa p
    exact hq.not_dvd_one ((Nat.dvd_add_iff_right hqn).2 hqnext)
  have hprodmod : (c * r) % q = 1 := by
    have he : (a * p) % q = 1 := by
      rw [ha, Nat.add_mod, Nat.mod_eq_zero_of_dvd hqn]
      simp [Nat.mod_eq_of_lt hq.one_lt]
    simpa [c, r, Nat.mul_mod] using he
  have hcrpos : 0 < c * r := Nat.mul_pos hcpos hrpos
  have hqd : q ∣ c * r - 1 := by
    apply (Nat.modEq_iff_dvd' (by omega : 1 ≤ c * r)).mp
    show 1 % q = (c * r) % q
    rw [hprodmod, Nat.mod_eq_of_lt hq.one_lt]
  have hbound : c * r - 1 ≤ c * q :=
    (Nat.sub_le _ _).trans (Nat.mul_le_mul_left c hrlt.le)
  have hdle : (c * r - 1) / q ≤ c := by
    apply (Nat.div_le_div_right hbound).trans
    rw [Nat.mul_div_left _ hq.pos]
  have hfac : (c * r - 1) / q * q = c * r - 1 := Nat.div_mul_cancel hqd
  have hm : ascend n = c * r - 1 := rfl
  rw [hm]
  constructor
  · by_cases hz : c * r - 1 = 0
    · exact Or.inl hz
    · apply Or.inr
      have hdpos : 0 < (c * r - 1) / q :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hqd) hq.pos
      constructor
      · rw [← hfac]
        exact Erdos371Cofactor.small_cofactor_max hdpos hq (hdle.trans hclt.le)
      · rw [Nat.sub_add_cancel (by omega : 1 ≤ c * r), P,
          Nat.maxPrimeFac_mul (by omega) (by omega)]
        exact max_lt (Nat.maxPrimeFac_le.trans_lt hclt)
          (Nat.maxPrimeFac_le.trans_lt hrlt)
  · have hcr : c ≤ a := Nat.mod_le a q
    have hr2 : 2 * r ≤ p := twice_mod_le hq.pos hqp
    have hb : 2 * (c * r) ≤ n + 1 := by
      calc
        2 * (c * r) = c * (2 * r) := by ring
        _ ≤ a * p := Nat.mul_le_mul hcr hr2
        _ = n + 1 := ha
    omega

lemma ascent_terminal_iff {n : ℕ} (hn : 1 < n) (hinc : P n < P (n + 1)) :
    ascend n = 0 ↔
      ((n + 1) / P (n + 1)) % P n = 1 ∧ P (n + 1) % P n = 1 := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hq := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hr : 0 < P (n + 1) % P n := prime_mod_pos hp hq hinc
  have hc : 0 < ((n + 1) / P (n + 1)) % P n := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hd : P n ∣ (n + 1) / P (n + 1) := Nat.dvd_of_mod_eq_zero hz
    have he : (n + 1) / P (n + 1) * P (n + 1) = n + 1 :=
      Nat.div_mul_cancel Nat.maxPrimeFac_dvd
    have hd' : P n ∣ n + 1 := he ▸ dvd_mul_of_dvd_left hd (P (n + 1))
    exact hq.not_dvd_one ((Nat.dvd_add_iff_right Nat.maxPrimeFac_dvd).2 hd')
  unfold ascend
  constructor
  · intro h
    have hpos := Nat.mul_pos hc hr
    have he : (((n + 1) / P (n + 1)) % P n) * (P (n + 1) % P n) = 1 := by
      omega
    exact ⟨Nat.eq_one_of_mul_eq_one_right he, Nat.eq_one_of_mul_eq_one_left he⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]


end Erdos371EuclideanCompression

#print axioms Erdos371EuclideanCompression.descent_reduces
#print axioms Erdos371EuclideanCompression.compression_not_injective
#print axioms Erdos371EuclideanCompression.infinite_descent_fiber
#print axioms Erdos371EuclideanCompression.ascent_reduces
#print axioms Erdos371EuclideanCompression.ascent_terminal_iff
