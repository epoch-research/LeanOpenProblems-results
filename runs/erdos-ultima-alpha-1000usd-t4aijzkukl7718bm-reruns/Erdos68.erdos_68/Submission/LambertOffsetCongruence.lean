import Submission.FactorialCongruence

/-!
Offset congruences for the original factorial Lambert coefficients.
These arithmetic lemmas do not supply the small-tail or nonvanishing step
needed to settle Erdős Problem 68.
-/

namespace LambertOffsetCongruence

open Finset Erdos68Development

/-- Removing one element from each of j blocks produces a multinomial
whose two different block sizes force divisibility by the new total. -/
lemma offset_dvd_uniform_aux (d j l : ℕ) (hj : 0 < j)
    (hcop : ((d+1)*(j+l+1)).Coprime j) :
    ((d+1)*(j+l+1)-j) ∣
      ((d+1)*(j+l+1)).factorial / (d+1).factorial^(j+l+1) := by
  let k := j+l+1
  let n := (d+1)*k
  let N := d*j+(d+1)*(l+1)
  let f : ℕ → ℕ := fun i => if i<j then d else d+1
  let V := Nat.multinomial (range k) f
  let R := d.factorial^j*(d+1).factorial^(l+1)
  let U := n.factorial/(d+1).factorial^k
  have hNj : N+j=n := by dsimp [N,n,k]; ring
  have hNn : N ≤ n := by omega
  have hsum : (∑ i ∈ range k, f i) = N := by
    rw [show k=j+(l+1) by dsimp [k]; omega, Finset.sum_range_add]
    have hleft : (∑ i ∈ range j, f i) = j*d := by
      simp only [f]
      rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))]
      simp
    have hright : (∑ i ∈ range (l+1), f (j+i)) = (l+1)*(d+1) := by
      simp [f, show ∀ i : ℕ, ¬j+i<j by omega]
    rw [hleft, hright]
    dsimp [N]
    ring
  have hprod : (∏ i ∈ range k, (f i).factorial) = R := by
    rw [show k=j+(l+1) by dsimp [k]; omega, Finset.prod_range_add]
    have hleft : (∏ i ∈ range j, (f i).factorial) = d.factorial^j := by
      calc
        _ = ∏ _i ∈ range j, d.factorial := by
          apply Finset.prod_congr rfl
          intro i hi
          simp only [f, if_pos (Finset.mem_range.mp hi)]
        _ = _ := by simp
    have hright : (∏ i ∈ range (l+1), (f (j+i)).factorial) =
        (d+1).factorial^(l+1) := by
      simp [f, show ∀ i : ℕ, ¬j+i<j by omega]
    rw [hleft, hright]
  have h0 : N ∣ d*V := by
    simpa only [hsum, f, if_pos hj] using
      total_dvd_count_mul_multinomial (range k) f (a:=0)
        (by simp [k])
  have h1 : N ∣ (d+1)*V := by
    simpa only [hsum, f, lt_self_iff_false, if_false] using
      total_dvd_count_mul_multinomial (range k) f (a:=j)
        (by simp [k])
  have hV : N ∣ V := by
    have h := Nat.dvd_sub h1 h0
    simpa [Nat.add_mul] using h
  have hVR : R*V=N.factorial := by
    simpa only [hsum, hprod] using Nat.multinomial_spec (range k) f
  have hRpos : 0<R := by dsimp [R]; positivity
  have hden : (d+1).factorial^k = (d+1)^j*R := by
    dsimp [k,R]
    rw [show j+l+1=j+(l+1) by omega, pow_add]
    conv_lhs => arg 1; rw [Nat.factorial_succ, mul_pow]
    ring
  have hU : U*((d+1).factorial^k)=n.factorial := by
    exact Nat.div_mul_cancel (factorial_pow_dvd_factorial_mul (d+1) k)
  have hC : (n.factorial/N.factorial)*N.factorial=n.factorial :=
    Nat.div_mul_cancel (Nat.factorial_dvd_factorial hNn)
  have hid : U*(d+1)^j=(n.factorial/N.factorial)*V := by
    apply Nat.eq_of_mul_eq_mul_right hRpos
    calc
      (U*(d+1)^j)*R = n.factorial := by rw [mul_assoc, ← hden, hU]
      _ = ((n.factorial/N.factorial)*V)*R := by rw [mul_assoc, mul_comm V R, hVR, hC]
  have hNbase : N.Coprime (d+1) := by
    apply Nat.dvd_one.mp
    have hgN := Nat.gcd_dvd_left N (d+1)
    have hgb := Nat.gcd_dvd_right N (d+1)
    have hgn : N.gcd (d+1) ∣ n := hgb.trans (dvd_mul_right (d+1) k)
    have hgj : N.gcd (d+1) ∣ j := by
      have h := Nat.dvd_sub hgn hgN
      simpa only [← hNj, Nat.add_sub_cancel_left] using h
    have h := Nat.dvd_gcd hgn hgj
    simpa only [show n.gcd j=1 from hcop] using h
  have hdiv : N ∣ U*(d+1)^j := by
    rw [hid]
    exact dvd_mul_of_dvd_right hV _
  have hu : N ∣ U := (hNbase.pow_right j).dvd_of_dvd_mul_right hdiv
  change n-j ∣ U
  rw [← hNj, Nat.add_sub_cancel_right]
  exact hu

/-- A uniform multinomial is divisible by a coprime offset from its total,
provided that the offset is smaller than the number of blocks. -/
theorem offset_dvd_uniform (d k j : ℕ) (hd : 0<d) (hj : 0<j)
    (hjk : j<k) (hcop : (d*k).Coprime j) :
    d*k-j ∣ (d*k).factorial/d.factorial^k := by
  have he : j+(k-j-1)+1=k := by omega
  have hd' : d-1+1=d := by omega
  simpa only [he, hd'] using
    offset_dvd_uniform_aux (d-1) j (k-j-1) hj (by simpa only [he, hd'] using hcop)

lemma offset_dvd_proper_summand (n d j : ℕ) (hn : 2≤n)
    (hd : d ∈ n.divisors) (hd2 : 2≤d) (hne : d≠n)
    (hj : 0<j) (hjm : j<n.minFac) :
    n-j ∣ n.factorial/d.factorial^(n/d) := by
  have hdn := Nat.dvd_of_mem_divisors hd
  have he : d*(n/d)=n := Nat.mul_div_cancel' hdn
  have hkpos : 0<n/d := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (by omega)
  have hk : 2≤n/d := by
    by_contra h
    have hk1 : n/d=1 := by omega
    rw [hk1, mul_one] at he
    exact hne he
  have hkdiv : n/d ∣ n := Nat.div_dvd_of_dvd hdn
  have hjk := hjm.trans_le (Nat.minFac_le_of_dvd hk hkdiv)
  have hcop := Nat.coprime_of_lt_minFac hj.ne' hjm
  have h := offset_dvd_uniform d (n/d) j (by omega) hj hjk (by simpa only [he] using hcop)
  simpa only [he] using h

/-- The predecessor congruence extends to every positive offset smaller
than the least prime factor. This concerns the original coefficients. -/
theorem lambertCoeff_modEq_offset (n j : ℕ) (hn : 2≤n)
    (hj : 0<j) (hjm : j<n.minFac) :
    Nat.ModEq (n-j) (lambertCoeff n) 1 := by
  have hsum : (∑ d ∈ n.divisors, if d=n then 1 else 0)=1 := by
    simp [Nat.mem_divisors, show n≠0 by omega]
  conv_rhs => rw [← hsum]
  apply Nat.ModEq.sum
  intro d hd
  by_cases he : d=n
  · subst d
    simp only [if_pos hn, Nat.div_self (by omega : 0<n), pow_one,
      Nat.div_self (Nat.factorial_pos n)]
    rfl
  · rw [if_neg he]
    by_cases hd2 : 2≤d
    · rw [if_pos hd2]
      exact Nat.modEq_zero_iff_dvd.mpr
        (offset_dvd_proper_summand n d j hn hd hd2 he hj hjm)
    · simp only [if_neg hd2]
      rfl

end LambertOffsetCongruence

#print axioms LambertOffsetCongruence.offset_dvd_uniform_aux

#print axioms LambertOffsetCongruence.lambertCoeff_modEq_offset
