import Submission.RetainedRealCompression

/-! Positive finite chain compression for interleaved terminal/stem groups.
The geometric marginal probabilities are (p-1)/p^a and1/p^a. This is an
auxiliary comparison theorem, not an odd-covering-system obstruction. -/
namespace Erdos7InterleavedGeometricCompression
open scoped BigOperators
open Erdos7RealChain Erdos7RetainedRealCompression
set_option autoImplicit false
set_option maxHeartbeats 2500000

def weave {α : Type*} (T S : ℕ → α) (j : ℕ) : α :=
  if j%2=0 then T (j/2) else S (j/2)

@[simp] lemma weave_even {α : Type*} (T S : ℕ → α) (a : ℕ) : weave T S (2*a) = T a := by
  simp [weave]

@[simp] lemma weave_odd {α : Type*} (T S : ℕ → α) (a : ℕ) : weave T S (2*a+1) = S a := by
  simp [weave, Nat.add_div, Nat.add_mod]

lemma sum_pairs (f : ℕ → ℝ) (R : ℕ) :
    (∑ j ∈ Finset.range (2*R), f j) = ∑ a ∈ Finset.range R, (f (2*a)+f (2*a+1)) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [show 2*(R+1)=2*R+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

noncomputable def cumulative (T S : ℕ → ℝ) (R : ℕ) : ℝ :=
  ∑ a ∈ Finset.range R, (T a+S a)

lemma prefix_weave_even (T S : ℕ → ℝ) (R : ℕ) :
    prefixWeight (weave T S) (2*R) = cumulative T S R := by
  simp only [prefixWeight, sum_pairs, weave_even, weave_odd, cumulative]

lemma prefix_weave_odd (T S : ℕ → ℝ) (R : ℕ) :
    prefixWeight (weave T S) (2*R+1) = cumulative T S R+T R := by
  rw [show prefixWeight (weave T S) (2*R+1) =
    prefixWeight (weave T S) (2*R)+weave T S (2*R) from Finset.sum_range_succ _ _]
  rw [prefix_weave_even, weave_even]

lemma chain_even (φ : ℝ → ℝ) (A : ℝ) (T S : ℕ → ℝ) (a : ℕ) :
    chainIncrement φ A (weave T S) (2*a) =
      φ (A+cumulative T S a+T a)-φ (A+cumulative T S a) := by
  simp only [chainIncrement, prefix_weave_odd, prefix_weave_even, add_assoc]

lemma chain_odd (φ : ℝ → ℝ) (A : ℝ) (T S : ℕ → ℝ) (a : ℕ) :
    chainIncrement φ A (weave T S) (2*a+1) =
      φ (A+cumulative T S (a+1))-φ (A+cumulative T S a+T a) := by
  unfold chainIncrement
  rw [show 2*a+1+1=2*(a+1) by omega, prefix_weave_even, prefix_weave_odd]
  simp only [add_assoc]

lemma paired_charge (φ : ℝ → ℝ) (A : ℝ) (T S qT qS : ℕ → ℝ) (R : ℕ) :
    (φ A+∑ j ∈ Finset.range (2*R), weave qT qS j*chainIncrement φ A (weave T S) j) =
      φ A+∑ a ∈ Finset.range R,
        (qT a*(φ (A+cumulative T S a+T a)-φ (A+cumulative T S a))+
         qS a*(φ (A+cumulative T S (a+1))-φ (A+cumulative T S a+T a))) := by
  rw [sum_pairs]
  simp only [weave_even, weave_odd, chain_even, chain_odd]

/-- Exact finite summation by parts. The final reserve is essential:
there is no unjustified omission of an infinite geometric tail. -/
theorem geometric_identity (p : ℝ) (hp : p ≠ 0) (f g : ℕ → ℝ) (R : ℕ) :
    (f 0+∑ a ∈ Finset.range R,
      ((p-1)/p^(a+1)*(g a-f a)+1/p^(a+1)*(f (a+1)-g a))) =
      f 0/p+∑ a ∈ Finset.range R,
        ((p-2)/p^(a+1)*g a+1/p^(a+2)*f (a+1))+
      (p-1)/p^(R+1)*f R := by
  induction R with
  | zero => simp; field_simp; ring
  | succ R ih =>
    simp only [Finset.sum_range_succ]
    rw [← add_assoc, ih]
    rw [show R+1+1=R+2 by omega, show R+2=(R+1)+1 by omega, pow_succ p (R+1)]
    field_simp
    ring

/-- Group compression specialized to an interleaved pair of level families.
Within each level the terminal and stem parts retain their own count bounds. -/
theorem paired_group_compression {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : (∑ y, μ y) = 1)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (A : ℝ) (T S : ℕ → ℝ) (t s : ℕ → Ω → ℝ) (qT qS : ℕ → ℝ) (R : ℕ)
    (hT : ∀ a<R, 0 ≤ T a) (hS : ∀ a<R, 0 ≤ S a)
    (ht : ∀ a<R, ∀ y, 0 ≤ t a y ∧ t a y ≤ T a)
    (hs : ∀ a<R, ∀ y, 0 ≤ s a y ∧ s a y ≤ S a)
    (hmt : ∀ a<R, (∑ y, μ y*t a y) ≤ qT a*T a)
    (hms : ∀ a<R, (∑ y, μ y*s a y) ≤ qS a*S a) :
    (∑ y, μ y*φ (A+∑ a ∈ Finset.range R, (t a y+s a y))) ≤
      φ A+∑ a ∈ Finset.range R,
        (qT a*(φ (A+cumulative T S a+T a)-φ (A+cumulative T S a))+
         qS a*(φ (A+cumulative T S (a+1))-φ (A+cumulative T S a+T a))) := by
  let W := weave T S
  let X : ℕ → Ω → ℝ := fun j y => weave (fun a => t a y) (fun a => s a y) j
  let q := weave qT qS
  have hW : ∀ j<2*R, 0 ≤ W j := by
    intro j hj
    have ha : j/2<R := by omega
    dsimp [W, weave]
    split_ifs <;> first | exact hT _ ha | exact hS _ ha
  have hX : ∀ j<2*R, ∀ y, 0 ≤ X j y := by
    intro j hj y
    have ha : j/2<R := by omega
    dsimp [X, weave]
    split_ifs <;> first | exact (ht _ ha y).1 | exact (hs _ ha y).1
  have hXW : ∀ j<2*R, ∀ y, X j y ≤ W j := by
    intro j hj y
    have ha : j/2<R := by omega
    dsimp [X, W, weave]
    split_ifs <;> first | exact (ht _ ha y).2 | exact (hs _ ha y).2
  have hmq : ∀ j<2*R, (∑ y, μ y*X j y) ≤ 1*q j*W j := by
    intro j hj
    have ha : j/2<R := by omega
    by_cases he : j%2=0
    · simpa only [X, W, q, weave, if_pos he, one_mul] using hmt _ ha
    · simpa only [X, W, q, weave, if_neg he, one_mul] using hms _ ha
  have hh := retained_group_compression μ hμ 1 1 (by simpa using hmass)
    φ hφ hmφ A W X q (2*R) hW hX hXW hmq
  change (∑ y, μ y*φ (A+prefixWeight (weave (fun a => t a y) (fun a => s a y)) (2*R))) ≤
    1*(1*φ A+∑ j ∈ Finset.range (2*R), weave qT qS j*chainIncrement φ A (weave T S) j) at hh
  simpa only [one_mul, prefix_weave_even, cumulative, paired_charge] using hh

/-- The positive interleaved geometric bound, valid at every finite depth.
Its last term is the exact remaining geometric mass at the last cumulative
count. All coefficients are nonnegative when p>=2. -/
theorem geometric_group_compression {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : (∑ y, μ y) = 1)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (A p : ℝ) (hp : 2 ≤ p) (T S : ℕ → ℝ) (t s : ℕ → Ω → ℝ) (R : ℕ)
    (hT : ∀ a<R, 0 ≤ T a) (hS : ∀ a<R, 0 ≤ S a)
    (ht : ∀ a<R, ∀ y, 0 ≤ t a y ∧ t a y ≤ T a)
    (hs : ∀ a<R, ∀ y, 0 ≤ s a y ∧ s a y ≤ S a)
    (hmt : ∀ a<R, (∑ y, μ y*t a y) ≤ (p-1)/p^(a+1)*T a)
    (hms : ∀ a<R, (∑ y, μ y*s a y) ≤ 1/p^(a+1)*S a) :
    (∑ y, μ y*φ (A+∑ a ∈ Finset.range R, (t a y+s a y))) ≤
      φ A/p+∑ a ∈ Finset.range R,
        ((p-2)/p^(a+1)*φ (A+cumulative T S a+T a)+
         1/p^(a+2)*φ (A+cumulative T S (a+1)))+
      (p-1)/p^(R+1)*φ (A+cumulative T S R) := by
  have hh := paired_group_compression μ hμ hmass φ hφ hmφ A T S t s
    (fun a => (p-1)/p^(a+1)) (fun a => 1/p^(a+1)) R hT hS ht hs hmt hms
  have he := geometric_identity p (by linarith : p ≠ 0)
    (fun a => φ (A+cumulative T S a)) (fun a => φ (A+cumulative T S a+T a)) R
  have hz : cumulative T S 0 = 0 := by simp [cumulative]
  simp only [hz, add_zero] at he
  exact hh.trans_eq he

#print axioms geometric_group_compression
end Erdos7InterleavedGeometricCompression
