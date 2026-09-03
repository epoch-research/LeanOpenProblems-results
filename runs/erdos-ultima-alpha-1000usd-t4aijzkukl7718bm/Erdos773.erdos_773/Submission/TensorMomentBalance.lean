import Submission.SmallSignJets
import Submission.MomentLifting

/-!
Moment balance under the two sign changes in a tensor norm identity.
These auxiliary algebraic results do not settle Erdős 773.
-/
namespace Erdos773.TensorMomentBalance
open Finset Polynomial
set_option maxHeartbeats 2000000
noncomputable section

/-- Vanishing signed moments in the background coordinates. -/
def Balanced {ι : Type*} [Fintype ι] (a f : ι → ℤ) (k : ℕ) : Prop :=
  ∀ j < k, ∑ i, a i ^ j * f i = 0

lemma signed_odd_pow {z : ℤ} (hz : -1 ≤ z ∧ z ≤ 1) {n : ℕ}
    (hn : Odd n) : z^n=z := by
  have hcases : z=-1 ∨ z=0 ∨ z=1 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact hn.neg_one_pow
  · exact zero_pow (by have := hn.pos; omega)
  · exact one_pow _

/-- A balanced signed vector is insensitive, in its first moments, to reversal
of its signed perturbation. -/
lemma moment_flip {ι : Type*} [Fintype ι] (a f : ι → ℤ) (k n : ℕ)
    (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) (hb : Balanced a f k) (hn : n ≤ k)
    (x y : ℤ) :
    (∑ i, (a i*x+f i*y)^n) = ∑ i, (a i*x+(-f i)*y)^n := by
  simp_rw [add_pow, mul_pow]
  rw [sum_comm, sum_comm (s := univ)]
  apply sum_congr rfl
  intro j hj
  rcases Nat.even_or_odd (n-j) with he | ho
  · simp_rw [he.neg_pow]
  · have hjk : j < k := by
      have hh := ho.pos
      omega
    have hz : (∑ i, a i^j*x^j*(f i^(n-j)*y^(n-j))*(n.choose j : ℤ)) = 0 := by
      calc
        _ = (x^j*y^(n-j)*(n.choose j : ℤ)) * ∑ i, a i^j*f i := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i hi
          rw [signed_odd_pow (hf i) ho]
          ring
        _ = 0 := by rw [hb j hjk, mul_zero]
    rw [hz]
    simp_rw [ho.neg_pow]
    calc
      0 = -(∑ i, a i^j*x^j*(f i^(n-j)*y^(n-j))*(n.choose j : ℤ)) := by rw [hz]; simp
      _ = _ := by rw [← sum_neg_distrib]; apply sum_congr rfl; intro i hi; ring

/-- The digit tensor, whose two independent sign changes make the four roots. -/
def tensor {ι κ : Type*} (a f : ι → ℤ) (d g : κ → ℤ) (ij : ι × κ) : ℤ :=
  (a ij.1+f ij.1)*d ij.2+(a ij.1-f ij.1)*g ij.2

lemma tensor_flip_first {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a f : ι → ℤ) (d g : κ → ℤ) (k n : ℕ)
    (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) (hb : Balanced a f k) (hn : n ≤ k) :
    (∑ ij, tensor a f d g ij ^ n) = ∑ ij, tensor a (-f) d g ij ^ n := by
  simp only [Fintype.sum_prod_type]
  conv_lhs => rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  convert moment_flip a f k n hf hb hn (d j+g j) (d j-g j) using 1 <;>
    apply sum_congr rfl <;> intro i hi <;> congr 1 <;> simp only [tensor, Pi.neg_apply] <;> ring

lemma tensor_flip_second {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a f : ι → ℤ) (d g : κ → ℤ) (k n : ℕ)
    (hg : ∀ j, -1 ≤ g j ∧ g j ≤ 1) (hb : Balanced d g k) (hn : n ≤ k) :
    (∑ ij, tensor a f d g ij ^ n) = ∑ ij, tensor a f d (-g) ij ^ n := by
  simp only [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i hi
  convert moment_flip d g k n hg hb hn (a i+f i) (a i-f i) using 1 <;>
    apply sum_congr rfl <;> intro j hj <;> congr 1 <;> simp only [tensor, Pi.neg_apply] <;> ring

/-- Any fixed number of balanced moments is preserved by all four tensor words. -/
theorem four_moments {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a f : ι → ℤ) (d g : κ → ℤ) (k : ℕ)
    (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) (hg : ∀ j, -1 ≤ g j ∧ g j ≤ 1)
    (ha : Balanced a f k) (hd : Balanced d g k) :
    ∀ n ≤ k,
      (∑ ij, tensor a f d g ij ^ n) = (∑ ij, tensor a (-f) d g ij ^ n) ∧
      (∑ ij, tensor a f d g ij ^ n) = (∑ ij, tensor a f d (-g) ij ^ n) ∧
      (∑ ij, tensor a f d g ij ^ n) = (∑ ij, tensor a (-f) d (-g) ij ^ n) := by
  intro n hn
  have h1 := tensor_flip_first a f d g k n hf ha hn
  have h2 := tensor_flip_second a f d g k n hg hd hn
  exact ⟨h1,h2,h1.trans (tensor_flip_second a (-f) d g k n hg hd hn)⟩


/-- Signed balance survives an arbitrary affine change of background. -/
lemma affine_balanced {ι : Type*} [Fintype ι] (a f : ι → ℤ) (k : ℕ)
    (hb : Balanced a f k) (A L : ℤ) :
    Balanced (fun i => A+L*a i) f k := by
  intro j hj
  simp_rw [add_pow, mul_pow, sum_mul]
  rw [sum_comm]
  apply sum_eq_zero
  intro m hm
  calc
    _ = (A^m*L^(j-m)*(j.choose m : ℤ)) * ∑ i, a i^(j-m)*f i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [hb (j-m) (by omega), mul_zero]

/-- Bounded nonzero signed vectors with arbitrarily many vanishing moments.
The length is polynomial in the number of requested moments. -/
theorem exists_balanced_signs (k : ℕ) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 16*(k+1)^2*((k+1).log2+1) ∧
      ∃ f : Fin D → ℤ,
        (∀ i, -1 ≤ f i ∧ f i ≤ 1) ∧ (∃ i, f i=1) ∧
        Balanced (fun i => (i.val : ℤ)) f k := by
  obtain ⟨V,hV,hdeg,hlead,hcoeff,hjet⟩ :=
    SmallSignJets.exists_signed_jet_quadratic_log (k+1) (by omega)
  let D := V.natDegree+1
  let f : Fin D → ℤ := fun i => V.coeff i.val
  refine ⟨D,by dsimp [D]; omega,by dsimp [D]; omega,f,?_,?_,?_⟩
  · intro i
    exact hcoeff i.val
  · refine ⟨⟨V.natDegree,by dsimp [D]; omega⟩,?_⟩
    simpa only [f,coeff_natDegree] using hlead
  · intro j hj
    have he := eulerIter_eval_one_of_jet (P := V) (Q := 0)
      (by simpa using hjet) (by omega : j < k+1)
    have hz : eulerIter j (0 : ℤ[X]) = 0 := by
      ext i
      simp [eulerIter_coeff]
    rw [hz,eval_zero] at he
    have ht : ∀ i, D ≤ i → V.coeff i=0 := by
      intro i hi
      exact coeff_eq_zero_of_natDegree_lt (by dsimp [D] at hi; omega)
    have hp : polynomialDigitMoment D V j=0 := (polynomialDigitMoment_eq V j ht).trans he
    change (∑ i : Fin D, (i.val : ℤ)^j*V.coeff i.val)=0
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℤ)^j*V.coeff i)]
    simpa only [polynomialDigitMoment, mul_comm] using hp

#print axioms moment_flip
#print axioms four_moments
#print axioms affine_balanced
#print axioms exists_balanced_signs
end
end Erdos773.TensorMomentBalance
