import Submission.SupportPolynomialTail

/-! Finite iteration of the support-sensitive polynomial tail. All exponent
caps are finite but arbitrary. This is not an unrestricted covering theorem. -/
namespace Erdos7SupportTailIteration
open scoped BigOperators
open Erdos7SupportCompression Erdos7SupportPolynomialTail
open Erdos7CompressionSieve Erdos7Distortion
set_option autoImplicit false
set_option maxHeartbeats 3000000

lemma pairExpect_mono (μ : TripleState →₀ ℚ) (hμ : ∀ x, 0 ≤ μ x)
    {f g : TripleState → ℚ} (h : ∀ x, f x ≤ g x) : pairExpect μ f ≤ pairExpect μ g := by
  unfold pairExpect Finsupp.sum
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (hμ x))

lemma pairExpect_nonneg (μ : TripleState →₀ ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (f : TripleState → ℚ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ pairExpect μ f := by
  unfold pairExpect
  exact Finsupp.sum_nonneg (fun x _ => mul_nonneg (hμ x) (hf x))

lemma pairExpect_test_add (μ : TripleState →₀ ℚ) (f g : TripleState → ℚ) :
    pairExpect μ (fun x => f x+g x)=pairExpect μ f+pairExpect μ g := by
  simp only [pairExpect,Finsupp.sum,mul_add,Finset.sum_add_distrib]

lemma pairExpect_test_mul (μ : TripleState →₀ ℚ) (c : ℚ) (f : TripleState → ℚ) :
    pairExpect μ (fun x => c*f x)=c*pairExpect μ f := by
  unfold pairExpect Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma pairExpect_test_div (μ : TripleState →₀ ℚ) (c : ℚ) (f : TripleState → ℚ) :
    pairExpect μ (fun x => f x/c)=pairExpect μ f/c := by
  simpa only [div_eq_mul_inv,mul_comm] using pairExpect_test_mul μ c⁻¹ f

lemma pairExpect_test_sum {I : Type*} (S : Finset I) (μ : TripleState →₀ ℚ)
    (f : I → TripleState → ℚ) :
    pairExpect μ (fun x => ∑ i ∈ S,f i x)=∑ i ∈ S,pairExpect μ (f i) := by
  unfold pairExpect Finsupp.sum
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

lemma tripleUpdate_zero (x : TripleState) : tripleUpdate 0 x=x := by
  simp [tripleUpdate]

lemma pairExpect_op (E : ℕ) (q : ℕ → ℚ) (μ : TripleState →₀ ℚ) (f : TripleState → ℚ) :
    pairExpect μ (fun x => op E q (fun a => f (tripleUpdate a x))) =
      pairExpect (tripleStep E q μ) f := by
  simp only [op,tripleUpdate_zero,pairExpect_test_add,pairExpect_test_mul,
    pairExpect_test_sum,pairExpect_step]

def statePotential (x : TripleState) : ℚ := potential x.1 x.2

def stateLoss (p : ℕ) (x : TripleState) : ℚ :=
  residual (5/4) ((tripleCount x:ℚ)/((p:ℚ)-1))

lemma statePotential_nonneg (x : TripleState) : 0 ≤ statePotential x :=
  potential_nonneg _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma finite_tail_step_spaced (p q E : ℕ) (hp : 128 ≤ p) (hq : p+2 ≤ q) (x : TripleState) :
    stateLoss p x+op E (powerTail p (5/4) E) (fun a => statePotential (tripleUpdate a x))/((q:ℚ)-1)^2 ≤
      statePotential x/((p:ℚ)-1)^2 := by
  have hpQ : (128:ℚ) ≤ p := by exact_mod_cast hp
  have hqQ : (p:ℚ)+2 ≤ q := by exact_mod_cast hq
  have hq0 := powerTail_zero_le_one p (by omega) (5/4) (by linarith) E
  have hdec := powerTail_decreasing p (by omega) (5/4) (by norm_num) E
  have hn := op_mono E _ hq0 (fun a _ => hdec a)
    (fun a => statePotential_nonneg (tripleUpdate a x))
  rw [op_const E _ (powerTail_terminal p (5/4) E) 0] at hn
  have hden : ((p:ℚ)+1)^2 ≤ ((q:ℚ)-1)^2 := by nlinarith
  have hdiv := div_le_div_of_nonneg_left hn
    (show 0 < ((p:ℚ)+1)^2 by positivity) hden
  have h := finite_tail_step p E hp (x.1:ℚ) (x.2:ℚ) (by positivity) (by positivity)
  have h' : stateLoss p x+op E (powerTail p (5/4) E)
      (fun a => statePotential (tripleUpdate a x))/((p:ℚ)+1)^2 ≤
      statePotential x/((p:ℚ)-1)^2 := by
    simpa only [stateLoss,statePotential,tripleCount,tripleUpdate,Nat.cast_add,Nat.cast_one,
      Nat.cast_mul] using h
  exact (add_le_add le_rfl hdiv).trans h'

lemma integrated_tail_step (p q E : ℕ) (hp : 128 ≤ p) (hq : p+2 ≤ q)
    (μ : TripleState →₀ ℚ) (hμ : ∀ x, 0 ≤ μ x) :
    pairExpect μ (stateLoss p)+
      pairExpect (tripleStep E (powerTail p (5/4) E) μ) statePotential/((q:ℚ)-1)^2 ≤
      pairExpect μ statePotential/((p:ℚ)-1)^2 := by
  have h := pairExpect_mono μ hμ (finite_tail_step_spaced p q E hp hq)
  simpa only [pairExpect_test_add,pairExpect_test_div,pairExpect_op] using h

/-- Telescoping over any finite increasing list with gaps at least two.
No prime counting and no common upper bound on the finite exponents is used. -/
theorem finite_tail_sum (n : ℕ) (p E : ℕ → ℕ) (μ : ℕ → TripleState →₀ ℚ)
    (hμ : ∀ i, i ≤ n → ∀ x, 0 ≤ μ i x)
    (hp : ∀ i, i < n → 128 ≤ p i)
    (hgap : ∀ i, i < n → p i+2 ≤ p (i+1))
    (hstep : ∀ i, i < n → μ (i+1)=tripleStep (E i) (powerTail (p i) (5/4) (E i)) (μ i)) :
    (∑ i ∈ Finset.range n,pairExpect (μ i) (stateLoss (p i))) ≤
      pairExpect (μ 0) statePotential/((p 0:ℚ)-1)^2 := by
  have hbound (j : ℕ) (hj : j ≤ n) :
      (∑ i ∈ Finset.range j,pairExpect (μ i) (stateLoss (p i)))+
        pairExpect (μ j) statePotential/((p j:ℚ)-1)^2 ≤
        pairExpect (μ 0) statePotential/((p 0:ℚ)-1)^2 := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hjn : j < n := by omega
      have hh := integrated_tail_step (p j) (p (j+1)) (E j) (hp j hjn) (hgap j hjn)
        (μ j) (hμ j (by omega))
      rw [← hstep j hjn] at hh
      rw [Finset.sum_range_succ]
      have hi := ih (by omega)
      linarith
  have hh := hbound n le_rfl
  have hn : 0 ≤ pairExpect (μ n) statePotential/((p n:ℚ)-1)^2 :=
    div_nonneg (pairExpect_nonneg (μ n) (hμ n le_rfl) _ statePotential_nonneg) (sq_nonneg _)
  linarith

#print axioms finite_tail_sum
end Erdos7SupportTailIteration
