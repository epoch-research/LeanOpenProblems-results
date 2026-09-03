import FormalConjecturesUtil
import Submission.SuzukiTraceBasics

/-! Trace-zero solvability and shifted-hyperplane intersections. -/
namespace Erdos713SuzukiTraceSlices
open Finset Erdos713SuzukiTraceBasics
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
set_option maxHeartbeats 2000000

omit [Fintype F] [CharP F 2] in
lemma even_odd_sum (f : ℕ → F) (r : ℕ) :
    (∑ i ∈ range r, f (2*i))+(∑ i ∈ range r, f (2*i+1)) = ∑ i ∈ range (2*r), f i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ,sum_range_succ,show 2*(r+1)=(2*r+1)+1 by omega,
      sum_range_succ,sum_range_succ,← ih]
    ring

noncomputable def halfTrace (r : ℕ) (x : F) : F := ∑ i ∈ range r, x^(2^(2*i))

omit [Fintype F] in
lemma halfTrace_square_add (r : ℕ) (x : F) :
    (halfTrace r x)^2+halfTrace r x=tr (2*r) x := by
  have hs := map_sum (frobenius F 2) (fun i : ℕ => x^(2^(2*i))) (range r)
  simp only [frobenius_def] at hs
  change (halfTrace r x)^2 = _ at hs
  rw [hs,halfTrace,tr,Fin.sum_univ_eq_sum_range (fun i : ℕ => x^(2^i))]
  have he : (∑ i ∈ range r, (x^(2^(2*i)))^2) = ∑ i ∈ range r, x^(2^(2*i+1)) := by
    apply sum_congr rfl
    intro i _
    rw [show 2^(2*i+1)=2^(2*i)*2 from pow_succ _ _]
    exact (pow_mul x (2^(2*i)) 2).symm
  rw [he,add_comm]
  exact even_odd_sum (fun i => x^(2^i)) r

lemma halfTrace_solves (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card F=2^(2*r-1))
    (x : F) (hx : tr (2*r-1) x=0) : (halfTrace r x)^2+halfTrace r x=x := by
  rw [halfTrace_square_add,tr,Fin.sum_univ_eq_sum_range (fun i : ℕ => x^(2^i))]
  have he : 2*r=(2*r-1)+1 := by omega
  rw [he,sum_range_succ]
  have ht : (∑ i ∈ range (2*r-1), x^(2^i))=0 := by
    simpa only [tr,Fin.sum_univ_eq_sum_range (fun i : ℕ => x^(2^i))] using hx
  rw [ht,zero_add,← hcard,FiniteField.pow_card]

omit [CharP F 2] in
lemma fixed_binary (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card F=2^(2*r-1))
    (x : F) (hx : x^(2^r)=x) : x=0 ∨ x=1 := by
  have hs := sigma_twice r hr hcard x
  rw [hx,hx] at hs
  have he : x*(x-1)=0 := by linear_combination -hs
  rcases mul_eq_zero.mp he with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The image of `x ↦ x+x^sigma` contains every trace-zero element. -/
theorem solve_twisted_add (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card F=2^(2*r-1))
    (e : F) (he : tr (2*r-1) e=0) : ∃ x : F, x+x^(2^r)=e := by
  let x := halfTrace r (e+e^(2^r))
  have hη : tr (2*r-1) (e+e^(2^r))=0 := by
    rw [tr_add,tr_pow_invariant (2*r-1) hcard,CharTwo.add_self_eq_zero]
  have hx : x^2+x=e+e^(2^r) := halfTrace_solves r hr hcard _ hη
  let z := x+x^(2^r)+e
  have hz : z^(2^r)=z := by
    apply CharTwo.add_eq_zero.mp
    have heq : z^(2^r)+z = (x^2+x)+(e+e^(2^r))+(x^(2^r)+x^(2^r)) := by
      dsimp [z]
      rw [add_pow_char_pow,add_pow_char_pow,sigma_twice r hr hcard]
      ring
    rw [heq,hx,CharTwo.add_self_eq_zero,CharTwo.add_self_eq_zero,zero_add]
  have htz : tr (2*r-1) z=0 := by
    dsimp [z]
    rw [tr_add,tr_add,tr_pow_invariant (2*r-1) hcard,CharTwo.add_self_eq_zero,zero_add,he]
  have hz0 : z=0 := by
    rcases fixed_binary r hr hcard z hz with h | h
    · exact h
    · rw [h,tr_one r hr] at htz
      exact (one_ne_zero htz).elim
  exact ⟨x,CharTwo.add_eq_zero.mp hz0⟩

omit [CharP F 2] in
lemma reverse_sigma_inverse (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card F=2^(2*r-1))
    (x : F) : (x^(2^r))^(2^(r-1))=x := by
  simpa only [← pow_mul,Nat.mul_comm] using sigma_inverse r hr hcard x

lemma trace_pairing (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card F=2^(2*r-1))
    (d t : F) : tr (2*r-1) (d*t^(2^r))=tr (2*r-1) (d^(2^(r-1))*t) := by
  have h := tr_pow_invariant (2*r-1) hcard r (d^(2^(r-1))*t)
  rw [mul_pow,sigma_inverse r hr hcard] at h
  exact h

lemma adjoint_parameter (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card F=2^(2*r-1))
    (δ : F) (hδ : tr (2*r-1) δ=0) : ∃ d : F, d+d^(2^(r-1))=δ := by
  have hδ' : tr (2*r-1) (δ^(2^r))=0 := by rw [tr_pow_invariant (2*r-1) hcard,hδ]
  obtain ⟨d,hd⟩ := solve_twisted_add r hr hcard (δ^(2^r)) hδ'
  have he := congrArg (fun x : F => x^(2^(r-1))) hd
  dsimp only at he
  rw [add_pow_char_pow,reverse_sigma_inverse r hr hcard,
    reverse_sigma_inverse r hr hcard] at he
  exact ⟨d,by simpa only [add_comm] using he⟩

/-- Every shifted hyperplane whose direction contains `1` supplies a
parameter for the restricted-center mixed octagon criterion. -/
theorem shifted_hyperplane_intersection (r : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card F=2^(2*r-1)) (b δ a : F)
    (hb : b ≠ 0) (hδ0 : δ ≠ 0) (hδ : tr (2*r-1) δ=0) (ha : a=0 ∨ a=1) :
    ∃ t : F, tr (2*r-1) (δ*t)=a ∧
      tr (2*r-1) (b/((1+t+t^(2^r))*(1+t+t^(2^r))^(2^r)))=0 := by
  obtain ⟨d,hd⟩ := adjoint_parameter r (by omega) hcard δ hδ
  have hd0 : d ≠ 0 := by intro h; rw [h,zero_pow (Nat.two_pow_pos _).ne',zero_add] at hd; exact hδ0 hd.symm
  have hd1 : d ≠ 1 := by intro h; rw [h,one_pow,CharTwo.add_self_eq_zero] at hd; exact hδ0 hd.symm
  have ha' : a+tr (2*r-1) d=0 ∨ a+tr (2*r-1) d=1 := by
    rcases tr_binary (2*r-1) hcard d with h | h
    all_goals rcases ha with ha | ha
    all_goals simp [h,ha,CharTwo.add_self_eq_zero]
  obtain ⟨k,_hk0,hk1,hkd,hkb⟩ := reciprocal_slice r hr hcard b d (a+tr (2*r-1) d) hb hd0 hd1 ha'
  have hkt : tr (2*r-1) (k+1)=0 := by
    rw [tr_add,hk1,tr_one r (by omega),CharTwo.add_self_eq_zero]
  obtain ⟨t,ht⟩ := solve_twisted_add r (by omega) hcard (k+1) hkt
  have he : 1+t+t^(2^r)=k := by
    calc
      1+t+t^(2^r) = (t+t^(2^r))+1 := by ring
      _ = (k+1)+1 := by rw [ht]
      _ = k := by rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]
  refine ⟨t,?_,by simpa only [he] using hkb⟩
  have htr : tr (2*r-1) (d*k) = tr (2*r-1) d + tr (2*r-1) (δ*t) := by
    rw [← he]
    have hp : d*(1+t+t^(2^r))=d+d*t+d*t^(2^r) := by ring
    rw [hp,tr_add,tr_add,trace_pairing r (by omega) hcard]
    rw [add_assoc,← tr_add,← add_mul,hd]
  rw [htr] at hkd
  exact add_left_cancel (by simpa only [add_comm] using hkd)

end Erdos713SuzukiTraceSlices
