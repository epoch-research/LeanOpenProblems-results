import FormalConjecturesUtil
import Submission.SuzukiTraceFourier

/-! Elementary trace and half-trace identities in odd-degree binary fields. -/
namespace Erdos713SuzukiTraceBasics
open Finset Erdos713SuzukiTraceFourier
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
set_option maxHeartbeats 2000000

noncomputable def tr (m : ℕ) (x : F) : F := ∑ i : Fin m, x^(2^i.val)

omit [Fintype F] [CharP F 2] in
lemma lin_eq (m : ℕ) (a x : F) : lin m a x = tr m (a*x) := by
  simp only [lin,tr,mul_pow]

omit [Fintype F] in
lemma tr_add (m : ℕ) (x y : F) : tr m (x+y)=tr m x+tr m y := by
  simp only [tr,add_pow_char_pow,sum_add_distrib]

omit [Fintype F] in
lemma tr_pow (m n : ℕ) (x : F) : tr m (x^(2^n))=(tr m x)^(2^n) := by
  have hs := map_sum (iterateFrobenius F 2 n) (fun i : Fin m => x^(2^i.val)) univ
  simp only [iterateFrobenius_def] at hs
  simp only [tr]
  rw [hs]
  apply sum_congr rfl
  intro i _
  rw [← pow_mul,← pow_mul]
  congr 1
  exact Nat.mul_comm _ _

omit [Fintype F] [CharP F 2] in
lemma tr_zero (m : ℕ) : tr m (0 : F)=0 := by
  simp [tr,zero_pow (Nat.two_pow_pos _).ne']

omit [CharP F 2] in
lemma power_period (m : ℕ) (hcard : Fintype.card F=2^m) (x : F) :
    Function.Periodic (fun n : ℕ => x^(2^n)) m := by
  intro n
  change x^(2^(n+m))=x^(2^n)
  rw [pow_add,mul_comm, pow_mul,← hcard,FiniteField.pow_card]

omit [CharP F 2] in
lemma power_mod (m : ℕ) (hcard : Fintype.card F=2^m) (x : F) (n : ℕ) :
    x^(2^(n%m))=x^(2^n) := (power_period m hcard x).map_mod_nat n

lemma tr_square (m : ℕ) (hcard : Fintype.card F=2^m) (x : F) : (tr m x)^2=tr m x := by
  have hs := map_sum (frobenius F 2) (fun i : Fin m => x^(2^i.val)) univ
  simp only [frobenius_def] at hs
  change (tr m x)^2 = _ at hs
  rw [hs]
  have he : (∑ i : Fin m, (x^(2^i.val))^2) = ∑ i ∈ range m, x^(2^(i+1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    rw [show 2^(i.val+1)=2^i.val*2 from pow_succ _ _,pow_mul]
  rw [he,tr,Fin.sum_univ_eq_sum_range (fun i : ℕ => x^(2^i))]
  apply add_right_cancel (b := x)
  have h₁ := sum_range_succ' (fun i => x^(2^i)) m
  have h₂ := sum_range_succ (fun i => x^(2^i)) m
  have hx : x^(2^m)=x := by rw [← hcard,FiniteField.pow_card]
  simpa only [pow_zero,pow_one,hx] using h₁.symm.trans h₂

lemma tr_binary (m : ℕ) (hcard : Fintype.card F=2^m) (x : F) :
    tr m x=0 ∨ tr m x=1 := by
  have hsq := tr_square m hcard x
  have he : tr m x*(tr m x-1)=0 := by linear_combination hsq
  rcases mul_eq_zero.mp he with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

lemma tr_pow_invariant (m : ℕ) (hcard : Fintype.card F=2^m) (n : ℕ) (x : F) :
    tr m (x^(2^n))=tr m x := by
  rw [tr_pow]
  rcases tr_binary m hcard x with h | h
  · rw [h,zero_pow (Nat.two_pow_pos n).ne']
  · rw [h,one_pow]

omit [Fintype F] in
lemma tr_one (r : ℕ) (hr : 1 ≤ r) : tr (2*r-1) (1 : F)=1 := by
  simp only [tr,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [Nat.cast_sub (by omega),Nat.cast_mul]
  norm_num only [Nat.cast_ofNat]
  rw [CharTwo.two_eq_zero,zero_mul,zero_sub,CharTwo.neg_eq]

omit [CharP F 2] in
lemma sigma_twice (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card F=2^(2*r-1)) (x : F) :
    (x^(2^r))^(2^r)=x^2 := by
  rw [← pow_mul,← pow_add]
  have he : r+r=(2*r-1)+1 := by omega
  rw [he,pow_add,pow_mul,← hcard,FiniteField.pow_card]
  norm_num

omit [CharP F 2] in
lemma sigma_inverse (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card F=2^(2*r-1)) (x : F) :
    (x^(2^(r-1)))^(2^r)=x := by
  rw [← pow_mul,← pow_add,show r-1+r=2*r-1 by omega,← hcard,FiniteField.pow_card]

omit [CharP F 2] in
lemma invQuad_eq (r : ℕ) (hcard : Fintype.card F=2^(2*r-1)) (b x : F) :
    invQuad r b x = tr (2*r-1) (b/(x*x^(2^r))) := by
  simp only [invQuad,tr,div_pow,mul_pow]
  apply sum_congr rfl
  intro i _
  have he : (x^(2^r))^(2^i.val)=x^(2^((i.val+r)%(2*r-1))) := by
    rw [power_mod (2*r-1) hcard x,← pow_mul,← pow_add,add_comm]
  rw [he,pow_add]

/-- A zero Fourier coefficient with nonzero `b` forces `d` into the prime field. -/
lemma coefficient_binary (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card F=2^(2*r-1))
    (b d : F) (hb : b ≠ 0) (h : b*(d^4+d^(2^(r+2)))=0) : d=0 ∨ d=1 := by
  have he := (mul_eq_zero.mp h).resolve_left hb
  have he' : d^4=d^(2^(r+2)) := by
    simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_left he)
  have heq : d=d^(2^r) := by
    apply iterateFrobenius_inj F 2 2
    simpa only [iterateFrobenius_def,show (2:ℕ)^2=4 by decide,pow_add,pow_mul] using he'
  have hs : d^2=d := by
    have hh := sigma_twice r hr hcard d
    rw [← heq,← heq] at hh
    exact hh.symm
  have hh : d*(d-1)=0 := by linear_combination hs
  rcases mul_eq_zero.mp hh with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- No affine codimension-two slice with first trace one is contained
in the one-set of a nonzero inverse twisted quadratic trace. -/
theorem reciprocal_slice (r : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card F=2^(2*r-1)) (b d a : F)
    (hb : b ≠ 0) (hd0 : d ≠ 0) (hd1 : d ≠ 1) (ha : a=0 ∨ a=1) :
    ∃ x : F, x ≠ 0 ∧ tr (2*r-1) x=1 ∧ tr (2*r-1) (d*x)=a ∧
      tr (2*r-1) (b/(x*x^(2^r)))=0 := by
  by_contra! hNo
  have hprod (x : Fˣ) : (invQuad r b (x : F)+1)*lin (2*r-1) 1 (x : F)*
      (lin (2*r-1) d (x : F)+(a+1))=0 := by
    rw [invQuad_eq r hcard,lin_eq,lin_eq,one_mul]
    rcases tr_binary (2*r-1) hcard (b/((x : F)*(x : F)^(2^r))) with hq | hq
    · rcases tr_binary (2*r-1) hcard (x : F) with hx | hx
      · rw [hx,mul_zero,zero_mul]
      · have hd : tr (2*r-1) (d*(x : F)) ≠ a := by
          intro he
          exact hNo (x : F) (Units.ne_zero x) hx he hq
        rcases tr_binary (2*r-1) hcard (d*(x : F)) with hd' | hd'
        all_goals rcases ha with ha | ha
        all_goals simp_all [CharTwo.add_self_eq_zero]
    · rw [hq,CharTwo.add_self_eq_zero,zero_mul,zero_mul]
  have he := product_coefficient r hr hcard (a+1) b d hprod
  rcases coefficient_binary r (by omega) hcard b d hb he with h | h
  · exact hd0 h
  · exact hd1 h

end Erdos713SuzukiTraceBasics
