import FormalConjecturesUtil

/-! Cofactor ordering and a reflection that reverses actual largest-prime-factor comparisons.
The reflection changes the counting range; these identities alone do not establish a density. -/

namespace Erdos371Cofactor

abbrev P := Nat.maxPrimeFac

def cofactor (n : ℕ) : ℕ := n / P n

lemma cofactor_mul (n : ℕ) : cofactor n * P n = n :=
  Nat.div_mul_cancel Nat.maxPrimeFac_dvd

lemma cofactor_pos {n : ℕ} (hn : 1 < n) : 0 < cofactor n :=
  Nat.div_pos Nat.maxPrimeFac_le (Nat.prime_maxPrimeFac_of_one_lt n hn).pos

lemma cofactor_consecutive_ne {n : ℕ} (hn : 3 ≤ n) : cofactor n ≠ cofactor (n + 1) := by
  intro he
  have hd : cofactor n ∣ n := ⟨P n, (cofactor_mul n).symm⟩
  have hd' : cofactor n ∣ n + 1 := by
    rw [he]
    exact ⟨P (n + 1), (cofactor_mul (n + 1)).symm⟩
  have h1 : cofactor n = 1 := Nat.dvd_one.mp ((Nat.dvd_add_iff_right hd).2 hd')
  have h2 : cofactor (n + 1) = 1 := he ▸ h1
  have hpn : P n = n := by simpa [h1] using cofactor_mul n
  have hpnext : P (n + 1) = n + 1 := by simpa [h2] using cofactor_mul (n + 1)
  have hnprime : n.Prime := by
    rw [← hpn]
    exact Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  have hnextprime : (n + 1).Prime := by
    rw [← hpnext]
    exact Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have heven : Even (n + 1) := (hnprime.odd_of_ne_two (by omega)).add_odd odd_one
  have := hnextprime.even_iff.mp heven
  omega

lemma comparison_iff_cofactor_reverse {n : ℕ} (hn : 3 ≤ n) :
    P n < P (n + 1) ↔ cofactor (n + 1) < cofactor n := by
  have ha := cofactor_mul n
  have hb := cofactor_mul (n + 1)
  have hap := cofactor_pos (n := n) (by omega)
  have hpp := (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).two_le
  have hne := cofactor_consecutive_ne hn
  constructor
  · intro h
    by_contra hc
    have hac : cofactor n + 1 ≤ cofactor (n + 1) := by omega
    have hpc : P n + 1 ≤ P (n + 1) := h
    have hm := Nat.mul_le_mul hac hpc
    nlinarith
  · intro h
    by_contra hc
    have hm := Nat.mul_le_mul (Nat.le_of_lt h) (Nat.le_of_not_gt hc)
    nlinarith

/-- A prime times a positive smaller cofactor has that prime as its largest prime factor. -/
lemma small_cofactor_max {a p : ℕ} (ha : 0 < a) (hp : p.Prime) (hap : a ≤ p) :
    P (a * p) = p := by
  rw [P, Nat.maxPrimeFac_mul ha.ne' hp.ne_zero, hp.maxPrimeFac_eq_self,
    max_eq_right (Nat.maxPrimeFac_le.trans hap)]

/-- A reflection of a consecutive factorization, retaining the larger prime. -/
lemma reflected_factorization {a b p q : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hq : q.Prime)
    (hab : a * p + 1 = b * q) (haq : a < q) (hbp : b < p) (hqp : q < p) :
    P ((p - b) * q) < p ∧ P ((p - b) * q + 1) = p := by
  have hx : (p - b) * q + b * q = p * q := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hbp.le]
  have hy : (q - a) * p + a * p = p * q := by
    rw [← Nat.add_mul, Nat.sub_add_cancel haq.le, Nat.mul_comm]
  have he : (p - b) * q + 1 = (q - a) * p := by omega
  have hcb : 0 < p - b := Nat.sub_pos_of_lt hbp
  have hda : 0 < q - a := Nat.sub_pos_of_lt haq
  constructor
  · rw [P, Nat.maxPrimeFac_mul hcb.ne' hq.ne_zero, hq.maxPrimeFac_eq_self]
    apply max_lt
    · exact Nat.maxPrimeFac_le.trans_lt (Nat.sub_lt hp.pos hb)
    · exact hqp
  · rw [he]
    exact small_cofactor_max hda hp ((Nat.sub_le q a).trans hqp.le)

lemma reflection_reverses_decrease {n : ℕ} (hn : 1 < n)
    (hdec : P (n + 1) < P n) (hbound : n + 1 < P n * P (n + 1)) :
    P (P n * P (n + 1) - 1 - n) < P n ∧
      P (P n * P (n + 1) - 1 - n + 1) = P n := by
  have ha := cofactor_mul n
  have hb := cofactor_mul (n + 1)
  have haq : cofactor n < P (n + 1) := by
    by_contra h
    have hh := Nat.mul_le_mul_right (P n) (Nat.le_of_not_gt h)
    nlinarith
  have hbp : cofactor (n + 1) < P n := by
    by_contra h
    have hh := Nat.mul_le_mul_right (P (n + 1)) (Nat.le_of_not_gt h)
    nlinarith
  have h := reflected_factorization (cofactor_pos (by omega))
    (Nat.prime_maxPrimeFac_of_one_lt n hn)
    (Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega))
    (by omega : cofactor n * P n + 1 = cofactor (n + 1) * P (n + 1)) haq hbp hdec
  have he : (P n - cofactor (n + 1)) * P (n + 1) = P n * P (n + 1) - 1 - n := by
    rw [Nat.sub_mul, hb]
    omega
  rwa [he] at h

/-- The prime-factor reflection is not itself a density-preserving bijection. -/
def reflect (n : ℕ) : ℕ := P n * P (n + 1) - 1 - n

lemma reflection_collision : reflect 17 = 33 ∧ reflect 153 = 33 := by decide +kernel

lemma reflection_not_injective : ¬Function.Injective reflect := by
  intro h
  have he := h (reflection_collision.1.trans reflection_collision.2.symm)
  norm_num at he

lemma reflection_changes_loser : P 18 = 3 ∧ P (reflect 17) = 11 := by decide +kernel

def groupImbalance (p N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N,
    if max (P n) (P (n + 1)) = p then
      if P n < P (n + 1) then 1 else -1
    else 0

lemma group_imbalance_exceeds_one : groupImbalance 11 33 = 2 := by decide +kernel

end Erdos371Cofactor

#print axioms Erdos371Cofactor.comparison_iff_cofactor_reverse
#print axioms Erdos371Cofactor.reflection_reverses_decrease
