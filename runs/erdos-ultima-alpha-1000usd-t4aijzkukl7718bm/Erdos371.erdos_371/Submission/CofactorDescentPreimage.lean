import Submission.CofactorDescent

/-! Exact residue and quotient formulas for cofactor descent. These formulas
retain both a primality condition and a smoothness condition in the inverse
problem; they do not assert cancellation of the resulting weighted sums. -/

namespace Erdos371

private lemma prime_mod_pos_of_lt (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) : 0 < q % p := by
  apply Nat.pos_of_ne_zero
  intro h
  have hd := Nat.dvd_of_mod_eq_zero h
  rcases (Nat.dvd_prime hq).mp hd with h | h
  · exact hp.ne_one h
  · omega

private lemma successor_block_decomposition (n p q b : ℕ)
    (hp : 0 < p) (hb : 0 < b) (hprod : n + 1 = b * q)
    (hr : 0 < q % p) :
    n % (p*b) = b*(q%p)-1 ∧ n / (p*b) = q/p := by
  have hrem : b*(q%p) < p*b := by
    simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left (Nat.mod_lt q hp) hb
  have hpos : 0 < b*(q%p) := Nat.mul_pos hb hr
  have hsub : b*(q%p)-1+1 = b*(q%p) := Nat.sub_add_cancel hpos
  have he : n = (b*(q%p)-1)+(p*b)*(q/p) := by
    have hdiv := Nat.mod_add_div q p
    nlinarith
  have hlt : b*(q%p)-1 < p*b := by omega
  constructor
  · rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [he, Nat.add_mul_div_left _ _ (Nat.mul_pos hp hb), Nat.div_eq_of_lt hlt]
    simp

/-- On the rising orientation, the winning prime is replaced by its residue
modulo the losing prime. This identity holds even outside the large-product
region where the sign-reversal theorem applies. -/
theorem primeCofactorDescent_rise_residue (n : ℕ) (hn : 1 < n)
    (hrise : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) :
    primeCofactorDescent n =
      primeCofactor (n+1)*(Nat.maxPrimeFac (n+1)%Nat.maxPrimeFac n)-1 ∧
    n / (Nat.maxPrimeFac n * primeCofactor (n+1)) =
      Nat.maxPrimeFac (n+1) / Nat.maxPrimeFac n := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  have hprod := maxPrimeFac_mul_primeCofactor (n+1)
  have hb : 0 < primeCofactor (n+1) := by
    by_contra h
    have he : primeCofactor (n+1) = 0 := by omega
    simp only [he, mul_zero] at hprod
    omega
  have h := successor_block_decomposition n (Nat.maxPrimeFac n)
    (Nat.maxPrimeFac (n+1)) (primeCofactor (n+1)) hp.pos hb
    (by simpa only [Nat.mul_comm] using hprod.symm)
    (prime_mod_pos_of_lt _ _ hp hq hrise)
  simpa only [primeCofactorDescent, if_pos hrise] using h

/-- The corresponding residue formula for the falling orientation. -/
theorem primeCofactorDescent_fall_residue (n : ℕ) (hn : 1 < n)
    (hfall : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n) :
    primeCofactorDescent n =
      primeCofactor n*(Nat.maxPrimeFac n%Nat.maxPrimeFac (n+1)) ∧
    n / (Nat.maxPrimeFac (n+1) * primeCofactor n) =
      Nat.maxPrimeFac n / Nat.maxPrimeFac (n+1) := by
  have hprod := maxPrimeFac_mul_primeCofactor n
  have hb : 0 < primeCofactor n := by
    by_contra h
    have he : primeCofactor n = 0 := by omega
    simp only [he, mul_zero] at hprod
    omega
  have hnot : ¬ Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) := by omega
  constructor
  · rw [primeCofactorDescent, if_neg hnot]
    conv_lhs => arg 1; rw [← hprod]
    rw [Nat.mul_comm (Nat.maxPrimeFac n), Nat.mul_comm (Nat.maxPrimeFac (n+1)),
      Nat.mul_mod_mul_left]
  · conv_lhs => arg 1; rw [← hprod]
    rw [Nat.mul_comm (Nat.maxPrimeFac n), Nat.mul_comm (Nat.maxPrimeFac (n+1)),
      Nat.mul_div_mul_left _ _ hb]

/-- Exact inverse data for a rising preimage. The last remaining condition is
smoothness of a linear form, simultaneously with the explicit prime linear
form in `hq`. In particular, primality of the new winner alone is insufficient. -/
theorem primeCofactorDescent_rising_preimage
    (p b r k : ℕ) (hp : p.Prime) (hb : 1 < b) (hbp : b < p)
    (hr : 0 < r) (hrp : r < p) (hk : 0 < k)
    (hd : p ∣ b*r-1) (hq : (r+p*k).Prime) :
    let n := b*(r+p*k)-1
    let a := (b*r-1)/p+b*k
    (Nat.maxPrimeFac n = p ↔ Nat.maxPrimeFac a ≤ p) ∧
    (Nat.maxPrimeFac a ≤ p →
      Nat.maxPrimeFac (n+1) = r+p*k ∧
      Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) ∧
      primeCofactorDescent n = b*r-1 ∧
      n < Nat.maxPrimeFac n*Nat.maxPrimeFac (n+1) ∧
      n/(p*b) = k) := by
  dsimp only
  let q := r+p*k
  let a := (b*r-1)/p+b*k
  let n := b*q-1
  have hpq : p < q := by dsimp [q]; nlinarith
  have hbr : 0 < b*r := Nat.mul_pos (by omega) hr
  have hbq : 0 < b*q := Nat.mul_pos (by omega) hq.pos
  have hbr1 : b*r-1+1 = b*r := Nat.sub_add_cancel hbr
  have hn1 : n+1 = b*q := Nat.sub_add_cancel hbq
  have hfac : p*((b*r-1)/p) = b*r-1 := Nat.mul_div_cancel' hd
  have hna : n = p*a := by
    dsimp [a, q] at *
    nlinarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hn : 1 < n := by rw [hna]; nlinarith [hp.two_le]
  have hP : Nat.maxPrimeFac n = max p (Nat.maxPrimeFac a) := by
    rw [hna, Nat.maxPrimeFac_mul hp.ne_zero ha.ne', hp.maxPrimeFac_eq_self]
  have hPn1 : Nat.maxPrimeFac (n+1) = q := by
    rw [hn1, Nat.maxPrimeFac_mul (by omega : b ≠ 0) hq.ne_zero, hq.maxPrimeFac_eq_self]
    exact max_eq_right (Nat.maxPrimeFac_le.trans (hbp.le.trans hpq.le))
  change (Nat.maxPrimeFac n = p ↔ Nat.maxPrimeFac a ≤ p) ∧ _
  refine ⟨by rw [hP, max_eq_left_iff], ?_⟩
  intro hs
  have hnP : Nat.maxPrimeFac n = p := by rw [hP, max_eq_left hs]
  have hrise : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) := by rwa [hnP, hPn1]
  have hbco : primeCofactor (n+1) = b := by
    rw [primeCofactor, hPn1, hn1, Nat.mul_div_cancel _ hq.pos]
  have hmod : q%p = r := by
    dsimp [q]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrp]
  have hdiv : q/p = k := by
    dsimp [q]
    rw [Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hrp, zero_add]
  have hdesc := primeCofactorDescent_rise_residue n hn hrise
  rw [hnP, hPn1, hbco, hmod, hdiv] at hdesc
  refine ⟨hPn1, hrise, hdesc.1, ?_, hdesc.2⟩
  rw [hnP, hPn1]
  nlinarith

/-- The falling inverse has the opposite sign in the divisibility condition,
but still retains a prime linear form and a simultaneous smooth linear form. -/
theorem primeCofactorDescent_falling_preimage
    (p b r k : ℕ) (hp : p.Prime) (hb : 0 < b) (hbp : b < p)
    (hr : 0 < r) (hrp : r < p) (hk : 0 < k)
    (hd : p ∣ b*r+1) (hq : (r+p*k).Prime) :
    let n := b*(r+p*k)
    let a := (b*r+1)/p+b*k
    (Nat.maxPrimeFac (n+1) = p ↔ Nat.maxPrimeFac a ≤ p) ∧
    (Nat.maxPrimeFac a ≤ p →
      Nat.maxPrimeFac n = r+p*k ∧
      Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n ∧
      primeCofactorDescent n = b*r ∧
      n < Nat.maxPrimeFac n*Nat.maxPrimeFac (n+1) ∧
      n/(p*b) = k) := by
  dsimp only
  let q := r+p*k
  let a := (b*r+1)/p+b*k
  let n := b*q
  have hpq : p < q := by dsimp [q]; nlinarith
  have hfac : p*((b*r+1)/p) = b*r+1 := Nat.mul_div_cancel' hd
  have hna : n+1 = p*a := by
    dsimp [a, n, q] at *
    nlinarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hn : 1 < n := by dsimp [n]; nlinarith [hq.two_le]
  have hP : Nat.maxPrimeFac (n+1) = max p (Nat.maxPrimeFac a) := by
    rw [hna, Nat.maxPrimeFac_mul hp.ne_zero ha.ne', hp.maxPrimeFac_eq_self]
  have hPn : Nat.maxPrimeFac n = q := by
    rw [show n = b*q from rfl, Nat.maxPrimeFac_mul hb.ne' hq.ne_zero, hq.maxPrimeFac_eq_self]
    exact max_eq_right (Nat.maxPrimeFac_le.trans (hbp.le.trans hpq.le))
  change (Nat.maxPrimeFac (n+1) = p ↔ Nat.maxPrimeFac a ≤ p) ∧ _
  refine ⟨by rw [hP, max_eq_left_iff], ?_⟩
  intro hs
  have hnP : Nat.maxPrimeFac (n+1) = p := by rw [hP, max_eq_left hs]
  have hfall : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n := by rwa [hnP, hPn]
  have hbco : primeCofactor n = b := by
    rw [primeCofactor, hPn, show n = b*q from rfl, Nat.mul_div_cancel _ hq.pos]
  have hmod : q%p = r := by
    dsimp [q]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrp]
  have hdiv : q/p = k := by
    dsimp [q]
    rw [Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hrp, zero_add]
  have hdesc := primeCofactorDescent_fall_residue n hn hfall
  rw [hnP, hPn, hbco, hmod, hdiv] at hdesc
  refine ⟨hPn, hfall, hdesc.1, ?_, hdesc.2⟩
  rw [hnP, hPn]
  change b*q < q*p
  simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hbp hq.pos

#print axioms primeCofactorDescent_rise_residue
#print axioms primeCofactorDescent_fall_residue
#print axioms primeCofactorDescent_rising_preimage
#print axioms primeCofactorDescent_falling_preimage

end Erdos371
