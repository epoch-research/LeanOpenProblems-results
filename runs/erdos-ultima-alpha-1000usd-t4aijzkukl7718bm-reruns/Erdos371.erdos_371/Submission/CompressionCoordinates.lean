import FormalConjecturesUtil
import Submission.EuclideanCompression

/-! Exact coordinates for the inverse images of the Euclidean compression
in the high-product region. No equidistribution of these inverse images is
asserted: the smoothness condition on the second linear form remains. -/

namespace Erdos371CompressionCoordinates

open Erdos371PrimeDiscrepancy Erdos371EuclideanCompression

/-- The cofactor of the smaller prime after undoing one compression step. -/
def linearCofactor (a q r k : ℕ) : ℕ := a*k+(a*r+1)/q

lemma lift_factorization {a q r k : ℕ} (hd : q ∣ a*r+1) :
    a*(k*q+r)+1=linearCofactor a q r k*q := by
  have h := Nat.div_mul_cancel hd
  unfold linearCofactor
  nlinarith

lemma lift_comparison {a q r k : ℕ}
    (ha : 0<a) (haq : a<q) (hr : 0<r) (hrq : r<q) (hk : 0<k)
    (hq : q.Prime) (hd : q ∣ a*r+1) (hp : (k*q+r).Prime)
    (hs : P (linearCofactor a q r k) ≤ q) :
    P (a*(k*q+r))=k*q+r ∧
    P (a*(k*q+r)+1)=q ∧
    a*(k*q+r)+1<P (a*(k*q+r))*P (a*(k*q+r)+1) ∧
    descend (a*(k*q+r))=a*r := by
  have hqp : q<k*q+r := by
    have hm := Nat.mul_le_mul_right q hk
    omega
  have he := lift_factorization (k := k) hd
  have hc : 0<linearCofactor a q r k := by
    unfold linearCofactor
    exact (Nat.mul_pos ha hk).trans_le (Nat.le_add_right _ _)
  have hleft : P (a*(k*q+r))=k*q+r := by
    rw [P,Nat.maxPrimeFac_mul ha.ne' hp.ne_zero,hp.maxPrimeFac_eq_self]
    exact max_eq_right (Nat.maxPrimeFac_le.trans (by omega))
  have hright : P (a*(k*q+r)+1)=q := by
    rw [he,P,Nat.maxPrimeFac_mul hc.ne' hq.ne_zero,hq.maxPrimeFac_eq_self]
    exact max_eq_right hs
  refine ⟨hleft,hright,?_,?_⟩
  · rw [hleft,hright]
    have hm := Nat.mul_le_mul_right (k*q+r) (show a+1≤q by omega)
    nlinarith [hp.two_le]
  · unfold descend
    rw [hleft,hright,Nat.mul_div_cancel _ hp.pos,Nat.mod_eq_of_lt haq]
    simp [Nat.add_mod,Nat.mod_eq_of_lt hrq]

/-- Every decreasing comparison in the high-product region has these
coordinates. Primality of one form and smoothness of the other are both
necessary, not assumptions that can be dropped in a prime-counting argument. -/
theorem descent_coordinates {n : ℕ} (hn : 1<n)
    (hdec : P (n+1)<P n) (hhigh : n+1<P n*P (n+1)) :
    ∃ a q r k : ℕ,
      0<a ∧ a<q ∧ 0<r ∧ r<q ∧ 0<k ∧ q.Prime ∧
      q∣a*r+1 ∧ (k*q+r).Prime ∧
      P (linearCofactor a q r k)≤q ∧
      n=a*(k*q+r) ∧ P (n+1)=q ∧ descend n=a*r := by
  let p := P n
  let q := P (n+1)
  let a := n/p
  let r := p%q
  let k := p/q
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq : q.Prime := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  have hqp : q<p := hdec
  have hap : a*p=n := Nat.div_mul_cancel Nat.maxPrimeFac_dvd
  have ha : 0<a := Nat.div_pos Nat.maxPrimeFac_le hp.pos
  have haq : a<q := by
    by_contra h
    have hm := Nat.mul_le_mul_right p (Nat.le_of_not_gt h)
    change n+1<p*q at hhigh
    nlinarith
  have hr : 0<r := prime_mod_pos hp hq hqp
  have hrq : r<q := Nat.mod_lt p hq.pos
  have hk : 0<k := Nat.div_pos hqp.le hq.pos
  have hpk : k*q+r=p := by
    simpa [k,r,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div p q
  have hd : q∣a*r+1 := by
    apply Nat.dvd_of_mod_eq_zero
    have hz : (a*p+1)%q=0 := by
      rw [hap]
      exact Nat.mod_eq_zero_of_dvd Nat.maxPrimeFac_dvd
    simpa [r,Nat.add_mod,Nat.mul_mod] using hz
  have hnfac : n=a*(k*q+r) := by rw [hpk,hap]
  have he : n+1=linearCofactor a q r k*q := by
    rw [hnfac]
    exact lift_factorization hd
  have hc : 0<linearCofactor a q r k := by
    unfold linearCofactor
    exact (Nat.mul_pos ha hk).trans_le (Nat.le_add_right _ _)
  have hs : P (linearCofactor a q r k)≤q := by
    have hh : max (P (linearCofactor a q r k)) q=q := by
      calc
        _ = P (linearCofactor a q r k*q) := by
          rw [P,Nat.maxPrimeFac_mul hc.ne' hq.ne_zero,hq.maxPrimeFac_eq_self]
        _ = q := by rw [← he]
    exact (le_max_left _ _).trans hh.le
  have hp' : (k*q+r).Prime := hpk.symm ▸ hp
  have hm := (lift_comparison ha haq hr hrq hk hq hd hp' hs).2.2.2
  refine ⟨a,q,r,k,ha,haq,hr,hrq,hk,hq,hd,hp',hs,hnfac,rfl,?_⟩
  simpa only [← hnfac] using hm

end Erdos371CompressionCoordinates

#print axioms Erdos371CompressionCoordinates.descent_coordinates
