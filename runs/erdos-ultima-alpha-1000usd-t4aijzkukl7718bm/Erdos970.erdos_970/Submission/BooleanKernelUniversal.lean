import Submission.FirstHitBooleanCost

/-! Completeness of the finite orthogonal kernels: every nonnegative function
on the Boolean cube is a square of such a kernel. No cost bound follows merely
from this representation. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma full_reproducing_factorization (q : ι → ℝ) (ω η : ι → Bool) :
    (∑ Q : Finset ι, weight q Q * basis q Q ω * basis q Q η) =
      ∏ i, (1 + q i / (1 - q i) * contrast (q i) (ω i) * contrast (q i) (η i)) := by
  have hb (Q : Finset ι) : weight q Q * basis q Q ω * basis q Q η =
      ∏ i ∈ Q, (q i / (1 - q i) * contrast (q i) (ω i) * contrast (q i) (η i)) := by
    simp only [weight, basis, prod_ite_mem, univ_inter, prod_mul_distrib]
  simp_rw [hb]
  simpa using sum_supersets_prod
    (fun i => q i / (1 - q i) * contrast (q i) (ω i) * contrast (q i) (η i)) (∅ : Finset ι)

lemma bernoulli_reproducing_factor (q : ℝ) (hq : 0 < q ∧ q < 1) (a b : Bool) :
    (if b then q else 1 - q) *
      (1 + q / (1 - q) * contrast q a * contrast q b) = if a = b then 1 else 0 := by
  have h0 := hq.1.ne'
  have h1 := (sub_pos.mpr hq.2).ne'
  cases a <;> cases b <;> simp only [contrast, Bool.false_eq_true, Bool.true_eq_false,
    if_true, if_false]
  all_goals field_simp
  all_goals nlinarith

/-- The full finite reproducing kernel is a delta after weighting by its atom mass. -/
lemma full_reproducing_delta (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (ω η : ι → Bool) :
    probability q η * (∑ Q : Finset ι, weight q Q * basis q Q ω * basis q Q η) =
      if ω = η then 1 else 0 := by
  rw [full_reproducing_factorization, probability, ← prod_mul_distrib]
  simp_rw [bernoulli_reproducing_factor _ (hq _)]
  rw [prod_boole]
  simp only [mem_univ, forall_const, funext_iff]

noncomputable def fourierCoefficient (q : ι → ℝ) (f : (ι → Bool) → ℝ)
    (Q : Finset ι) : ℝ := weight q Q * average q (fun ω => f ω * basis q Q ω)

/-- An explicit inversion formula for arbitrary real functions on the Boolean cube. -/
theorem linearKernel_fourierCoefficient (q : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (f : (ι → Bool) → ℝ) (ω : ι → Bool) :
    linearKernel q (fourierCoefficient q f) ω = f ω := by
  unfold linearKernel fourierCoefficient average
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  calc
    _ = ∑ η, f η * (probability q η *
        (∑ Q : Finset ι, weight q Q * basis q Q ω * basis q Q η)) := by
      apply sum_congr rfl
      intro η hη
      simp only [mul_sum]
      apply sum_congr rfl
      intro Q hQ
      ring
    _ = ∑ η, f η * if ω = η then 1 else 0 := by
      simp_rw [full_reproducing_delta q hq]
    _ = f ω := by simp

/-- Squares of unrestricted signed orthogonal kernels represent every nonnegative
Boolean function. This says nothing about how large the coefficient cost is. -/
theorem exists_square_kernel (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (f : (ι → Bool) → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    ∃ c : Finset ι → ℝ, ∀ ω, linearKernel q c ω ^ 2 = f ω := by
  refine ⟨fourierCoefficient q (fun ω => Real.sqrt (f ω)), ?_⟩
  intro ω
  rw [linearKernel_fourierCoefficient q hq]
  exact Real.sq_sqrt (hf ω)

/-- Normalization at the empty pattern becomes sum(c)=1, as required in the
first-hit criterion. -/
theorem exists_normalized_square_kernel (q : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1)
    (f : (ι → Bool) → ℝ) (hf : ∀ ω, 0 ≤ f ω) (h0 : f (fun _ => false) = 1) :
    ∃ c : Finset ι → ℝ, (∑ Q : Finset ι, c Q) = 1 ∧
      ∀ ω, linearKernel q c ω ^ 2 = f ω := by
  refine ⟨fourierCoefficient q (fun ω => Real.sqrt (f ω)), ?_, ?_⟩
  · have he := linearKernel_fourierCoefficient q hq (fun ω => Real.sqrt (f ω)) (fun _ => false)
    simpa only [linearKernel, basis_at_empty, mul_one, h0, Real.sqrt_one] using he
  · intro ω
    rw [linearKernel_fourierCoefficient q hq]
    exact Real.sq_sqrt (hf ω)

#print axioms linearKernel_fourierCoefficient
#print axioms exists_normalized_square_kernel
end Erdos970.FiniteSelberg
