import FormalConjecturesUtil

/-! Cofactor descent along earlier unfavorable vertices of an affine
prime-factor predecessor graph. Termination is not an injective matching:
several source chains may have the same favorable terminal vertex. -/

namespace Erdos371AffineCofactorDescent

abbrev P := Nat.maxPrimeFac

def cofactor (a : ℕ) : ℕ := a / P a

lemma prime_mul_cofactor (a : ℕ) :
    P a * cofactor a = a := by
  exact Nat.mul_div_cancel' Nat.maxPrimeFac_dvd

lemma cofactor_pos {a : ℕ} (ha : 0 < a) : 0 < cofactor a := by
  have hp : 0 < P a := Nat.pos_of_dvd_of_pos Nat.maxPrimeFac_dvd ha
  exact Nat.div_pos (Nat.maxPrimeFac_le) hp

/-- An earlier integer with a larger top prime has a smaller cofactor. -/
theorem cofactor_lt_of_earlier_larger_prime {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hp : P a < P b) :
    cofactor b < cofactor a := by
  have hea := prime_mul_cofactor a
  have heb := prime_mul_cofactor b
  have hc := cofactor_pos ha
  by_contra h
  have hm := Nat.mul_le_mul_left (P b) (show cofactor a ≤ cofactor b by omega)
  nlinarith

/-- This applies to any nonzero neighboring value, not just an affine one. -/
theorem predecessor_cofactor_lt {a b v : ℕ}
    (ha : 1 < a) (hb : 0 < b) (hba : b < a) (hv : v ≠ 0)
    (hd : P a ∣ v) (hbad : P v < P b) : cofactor b < cofactor a := by
  have hprime := Nat.prime_maxPrimeFac_of_one_lt a ha
  have hP : P a ≤ P v := Nat.le_maxPrimeFac hv hprime hd
  exact cofactor_lt_of_earlier_larger_prime (by omega) hb hba (hP.trans_lt hbad)

lemma minus_predecessor_cofactor_lt {p a b : ℕ}
    (hp : 2 ≤ p) (ha : 1 < a) (hb : 0 < b) (hba : b < a)
    (hd : P a ∣ p*b-1) (hbad : P (p*b-1) < P b) :
    cofactor b < cofactor a := by
  have hv : p*b-1 ≠ 0 := by
    have hh : 2 ≤ p*b := by nlinarith
    omega
  exact predecessor_cofactor_lt ha hb hba hv hd hbad

lemma plus_predecessor_cofactor_lt {p a b : ℕ}
    (ha : 1 < a) (hb : 0 < b) (hba : b < a)
    (hd : P a ∣ p*b+1) (hbad : P (p*b+1) < P b) :
    cofactor b < cofactor a :=
  predecessor_cofactor_lt ha hb hba (by omega) hd hbad

lemma decreasing_cofactor_length (a : ℕ → ℕ) {k : ℕ}
    (hstep : ∀ i < k, cofactor (a (i+1)) < cofactor (a i)) :
    k + cofactor (a k) ≤ cofactor (a 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := ih (fun i hi => hstep i (by omega))
    have hs := hstep k (by omega)
    omega

/-- A chain whose vertices are all unfavorable has fewer steps than the
initial cofactor. This is a depth bound, not a bound on the number of sources
sharing a terminal vertex. -/
theorem predecessor_chain_length (a : ℕ → ℕ) (F : ℕ → ℕ) {k : ℕ}
    (ha : ∀ i ≤ k, 1 < a i)
    (hstep : ∀ i < k, a (i+1) < a i ∧ F (a (i+1)) ≠ 0 ∧
      P (a i) ∣ F (a (i+1)) ∧ P (F (a (i+1))) < P (a (i+1))) :
    k < cofactor (a 0) := by
  have hlen := decreasing_cofactor_length a (k := k) (fun i hi => by
    obtain ⟨hb, hv, hd, hbad⟩ := hstep i hi
    exact predecessor_cofactor_lt (ha i (by omega)) (by have := ha (i+1) (by omega); omega)
      hb hv hd hbad)
  have hp := cofactor_pos (a := a k) (by have := ha k (by omega); omega)
  omega

end Erdos371AffineCofactorDescent

#print axioms Erdos371AffineCofactorDescent.predecessor_cofactor_lt
#print axioms Erdos371AffineCofactorDescent.predecessor_chain_length
