import Submission.LambertOffsetCongruence

/-!
A descending-factorial strengthening of the offset congruences.
These are original-coefficient statements, not an irrationality proof.
-/
namespace LambertDescendingCongruence

open Finset Erdos68Development LambertOffsetCongruence

lemma removed_blocks_identity (d j l : ℕ) (hj : 0<j) :
    ∃ V : ℕ, ((d+1)*(j+l+1)-j) ∣ V ∧
      (((d+1)*(j+l+1)).factorial/(d+1).factorial^(j+l+1))*(d+1)^j =
        ((d+1)*(j+l+1)).descFactorial j * V := by
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
  refine ⟨V, ?_, ?_⟩
  · change n-j ∣ V
    rw [← hNj, Nat.add_sub_cancel_right]
    exact hV
  · change U*(d+1)^j = n.descFactorial j*V
    rw [Nat.descFactorial_eq_div (by omega : j≤n), show n-j=N by omega]
    exact hid

lemma offset_coprime_of_dvd (n d j : ℕ) (hd : d∣n) (hj : j≤n)
    (hcop : n.Coprime j) : (n-j).Coprime d := by
  apply Nat.dvd_one.mp
  have hgN := Nat.gcd_dvd_left (n-j) d
  have hgd := Nat.gcd_dvd_right (n-j) d
  have hgn : (n-j).gcd d ∣ n := hgd.trans hd
  have hgj : (n-j).gcd d ∣ j := by
    have h := Nat.dvd_sub hgn hgN
    simpa only [Nat.sub_sub_self hj] using h
  have h := Nat.dvd_gcd hgn hgj
  simpa only [hcop.gcd_eq_one] using h

lemma desc_pred_coprime (n d j : ℕ) (hd : d∣n) (hj : j<n)
    (hcop : n.Coprime j.factorial) : ((n-1).descFactorial j).Coprime d := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjn : j<n := by omega
    have hcprev : n.Coprime j.factorial :=
      hcop.of_dvd_right (Nat.factorial_dvd_factorial (by omega))
    have hcj : n.Coprime (j+1) :=
      hcop.of_dvd_right (Nat.dvd_factorial (by omega) le_rfl)
    have hc := offset_coprime_of_dvd n d (j+1) hd (by omega) hcj
    rw [Nat.descFactorial_succ, show n-1-j=n-(j+1) by omega]
    exact hc.mul_left (ih hjn hcprev)

/-- The complete product of offsets divides the uniform multinomial under
coprimality with j!, not just each factor separately. -/
theorem descending_dvd_uniform (d k j : ℕ) (hd : 0<d) (hjk : j<k)
    (hcop : (d*k).Coprime j.factorial) :
    ((d*k)-1).descFactorial j ∣ (d*k).factorial/d.factorial^k := by
  by_cases hj0 : j=0
  · subst j; simp
  have hj : 0<j := by omega
  have he : j+(k-j-1)+1=k := by omega
  have hd' : d-1+1=d := by omega
  obtain ⟨V,hV,hid⟩ := removed_blocks_identity (d-1) j (k-j-1) hj
  simp only [he,hd'] at hV hid
  have hnk : k≤d*k := by nlinarith
  have hn : 0<d*k := by omega
  have hdesc : (d*k).descFactorial (j+1) ∣
      ((d*k).factorial/d.factorial^k)*d^j := by
    rw [hid, Nat.descFactorial_succ]
    simpa only [mul_comm] using Nat.mul_dvd_mul_left ((d*k).descFactorial j) hV
  have hoff : ((d*k)-1).descFactorial j ∣ (d*k).descFactorial (j+1) := by
    conv_rhs => arg 1; rw [← Nat.sub_add_cancel (by omega : 1≤d*k)]
    rw [Nat.succ_descFactorial_succ]
    exact dvd_mul_left _ _
  have hc := desc_pred_coprime (d*k) d j (dvd_mul_right d k) (by omega) hcop
  exact (hc.pow_right j).dvd_of_dvd_mul_right (hoff.trans hdesc)

lemma descending_dvd_proper_summand (n d j : ℕ) (hn : 2≤n)
    (hd : d∈n.divisors) (hd2 : 2≤d) (hne : d≠n) (hjm : j<n.minFac) :
    (n-1).descFactorial j ∣ n.factorial/d.factorial^(n/d) := by
  have hdn := Nat.dvd_of_mem_divisors hd
  have he : d*(n/d)=n := Nat.mul_div_cancel' hdn
  have hkpos : 0<n/d := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (by omega)
  have hk : 2≤n/d := by
    by_contra h
    have hk1 : n/d=1 := by omega
    rw [hk1, mul_one] at he
    exact hne he
  have hjk := hjm.trans_le (Nat.minFac_le_of_dvd hk (Nat.div_dvd_of_dvd hdn))
  have hcop : n.Coprime j.factorial :=
    (Nat.coprime_factorial_iff (by omega : n≠1)).mpr hjm
  simpa only [he] using descending_dvd_uniform d (n/d) j (by omega) hjk
    (by simpa only [he] using hcop)

/-- A stronger original-coefficient congruence with the full descending
factorial modulus. It is not asserted for any carried coefficient sequence. -/
theorem lambertCoeff_modEq_descending (n j : ℕ) (hn : 2≤n)
    (hjm : j<n.minFac) :
    Nat.ModEq ((n-1).descFactorial j) (lambertCoeff n) 1 := by
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
        (descending_dvd_proper_summand n d j hn hd hd2 he hjm)
    · simp only [if_neg hd2]
      rfl

theorem lambertCoeff_modEq_minFac_descending (n : ℕ) (hn : 2≤n) :
    Nat.ModEq ((n-1).descFactorial (n.minFac-1)) (lambertCoeff n) 1 := by
  exact lambertCoeff_modEq_descending n (n.minFac-1) hn
    (by have := Nat.minFac_pos n; omega)

/-- In particular the correction at an odd index is divisible by two
consecutive predecessors. No such claim is made for carried coefficients. -/
theorem lambertCoeff_modEq_odd_quadratic (n : ℕ) (hn : 3≤n) (ho : Odd n) :
    Nat.ModEq ((n-1)*(n-2)) (lambertCoeff n) 1 := by
  have hc : n.Coprime (2 : ℕ).factorial := by
    simpa only [show (2 : ℕ).factorial=2 by decide] using ho.coprime_two_right
  have hmin : 2<n.minFac := (Nat.coprime_factorial_iff (by omega : n≠1)).mp hc
  have h := lambertCoeff_modEq_descending n 2 (by omega) hmin
  simpa [Nat.descFactorial_succ, Nat.sub_sub, mul_comm] using h

end LambertDescendingCongruence

#print axioms LambertDescendingCongruence.descending_dvd_uniform
#print axioms LambertDescendingCongruence.lambertCoeff_modEq_descending

#print axioms LambertDescendingCongruence.lambertCoeff_modEq_odd_quadratic
