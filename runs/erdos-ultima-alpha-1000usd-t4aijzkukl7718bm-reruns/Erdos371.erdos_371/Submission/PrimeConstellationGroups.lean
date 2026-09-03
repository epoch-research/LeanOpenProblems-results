import FormalConjecturesUtil
import Submission.CofactorDiscrepancy

/-! A finite construction of large individual winning-prime groups from
prime constellations. No existence assertion for an infinite family of
constellations, and no conclusion about Erdős 371, is assumed here. -/

namespace Erdos371PrimeConstellationGroups

open Finset Erdos371PrimeDiscrepancy Erdos371CofactorDiscrepancy

/-- The quotient of `a*p+1` by `a-1`, when `a-1` divides `p+1`. -/
def plusQuotient (a p : ℕ) : ℕ := a*((p+1)/(a-1))-1

lemma minus_smooth {a p : ℕ} (ha : 0<a) (hap : a+1<p) (hd : a+1∣p+1) :
    P (a*p-1)<p := by
  let t := (p+1)/(a+1)
  have ht : (a+1)*t=p+1 := Nat.mul_div_cancel' hd
  have htpos : 0<t := Nat.div_pos (Nat.le_of_dvd (by omega : 0<p+1) hd) (by omega)
  have hat : 0<a*t := Nat.mul_pos ha htpos
  have hfactor : (a+1)*(a*t-1)=a*p-1 := by
    rw [Nat.mul_sub]
    have he : (a+1)*(a*t)=a*p+a := by nlinarith
    rw [he]
    omega
  have hsmall : a*t-1<p := by
    have he : a*t+t=p+1 := by nlinarith [ht]
    omega
  have hnonzero : a*t-1≠0 := by
    intro h
    rw [h,mul_zero] at hfactor
    have hh : p≤a*p := by simpa using Nat.mul_le_mul_right p ha
    omega
  rw [← hfactor,P,Nat.maxPrimeFac_mul (by omega) hnonzero]
  exact max_lt (Nat.maxPrimeFac_le.trans_lt hap) (Nat.maxPrimeFac_le.trans_lt hsmall)

lemma plusQuotient_factor {a p : ℕ} (ha : 2≤a) (hd : a-1∣p+1) :
    p<plusQuotient a p ∧ (a-1)*plusQuotient a p=a*p+1 := by
  let t := (p+1)/(a-1)
  have ht : (a-1)*t=p+1 := Nat.mul_div_cancel' hd
  have htpos : 0<t := Nat.div_pos (Nat.le_of_dvd (by omega : 0<p+1) hd) (by omega)
  have hat : a*t=p+1+t := by
    have he : a=(a-1)+1 := by omega
    calc
      a*t = ((a-1)+1)*t := congrArg (fun x : ℕ => x*t) he
      _ = (a-1)*t+t := by ring
      _ = p+1+t := by rw [ht]
  have hq : plusQuotient a p=p+t := by simp only [plusQuotient]; change a*t-1=p+t; omega
  rw [hq]
  refine ⟨by omega,?_⟩
  have he : (a-1)*p+p=a*p := by
    calc
      _ = ((a-1)+1)*p := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1≤a)]
  nlinarith

lemma plus_large {a p : ℕ} (ha : 2≤a) (hd : a-1∣p+1)
    (hq : (plusQuotient a p).Prime) : p<P (a*p+1) := by
  obtain ⟨hlt,hfac⟩ := plusQuotient_factor ha hd
  have hdiv : plusQuotient a p∣a*p+1 := ⟨a-1,by simpa [Nat.mul_comm] using hfac.symm⟩
  exact hlt.trans_le (Nat.le_maxPrimeFac (by omega) hq hdiv)

/-- Under these finite divisibility and primality hypotheses, all interior
cofactors `2,...,A-1` contribute with the same sign. The last arrival is
included, but its departure lies outside the interval. -/
theorem group_eq_of_constellation {A p : ℕ} (hA : 2≤A) (hp : p.Prime) (hAp : A+1<p)
    (hd : ∀ d ∈ Finset.Icc 1 (A+1),d∣p+1)
    (hq : ∀ a ∈ Finset.Icc 2 (A-1),(plusQuotient a p).Prime) :
    group p (A*p)=(A:ℤ)-1 := by
  have hp2 : 2<p := by omega
  have before (a : ℕ) (ha : a∈Finset.Icc 1 A) : P a≤p ∧ P (a*p-1)<p := by
    obtain ⟨ha1,haA⟩ := Finset.mem_Icc.mp ha
    refine ⟨Nat.maxPrimeFac_le.trans (by omega),?_⟩
    exact minus_smooth (by omega) (by omega) (hd (a+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
  have after (a : ℕ) (ha : a∈Finset.Icc 2 (A-1)) : p<P (a*p+1) := by
    obtain ⟨ha2,haA⟩ := Finset.mem_Icc.mp ha
    exact plus_large ha2 (hd (a-1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)) (hq a ha)
  have hb : ((Finset.Icc 1 A).filter fun a => P a≤p ∧ P (a*p-1)<p)=Finset.Icc 1 A := by
    exact Finset.filter_eq_self.mpr before
  have ha : ((Finset.Icc 1 (A-1)).filter fun a => P a≤p ∧ P (a*p+1)<p)={1} := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨ha1,haA⟩,_,hsmall⟩
      by_contra he
      have hh := after a (Finset.mem_Icc.mpr ⟨by omega,haA⟩)
      omega
    · rintro rfl
      refine ⟨⟨by omega,by omega⟩,?_,?_⟩
      · simp only [P,Nat.maxPrimeFac_one]; omega
      · simpa only [one_mul] using after_odd_prime hp hp2
  have hprod : (A-1)*p+p=A*p := by
    calc
      _ = ((A-1)+1)*p := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1≤A)]
  have hpos : 0<A*p := Nat.mul_pos (by omega) hp.pos
  have hdiv : (A*p-1)/p=A-1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.sub_add_cancel (by omega : 1≤A)]
      omega
  have hc := count_prime_cofactors hp (A*p-1) (fun n => P (n+1)<p)
  rw [Nat.sub_add_cancel (by omega : 1≤A*p),hdiv,ha] at hc
  rw [group_eq_counts,count_before_prime hp,Nat.mul_div_cancel _ hp.pos,hb,hc]
  simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma example_5039 : group 5039 (8*5039)=7 := by
  have hd : ∀ d ∈ Finset.Icc 1 9,d∣5040 := by
    intro d hd
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num
  have hq : ∀ a ∈ Finset.Icc 2 7,(plusQuotient a 5039).Prime := by
    intro a ha
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp ha
    interval_cases a <;> norm_num [plusQuotient]
  have h := group_eq_of_constellation (A := 8) (p := 5039) (by norm_num)
    (by norm_num) (by norm_num) hd hq
  norm_num only [Nat.cast_ofNat,Int.reduceSub] at h
  exact h

end Erdos371PrimeConstellationGroups

#print axioms Erdos371PrimeConstellationGroups.group_eq_of_constellation
#print axioms Erdos371PrimeConstellationGroups.example_5039
