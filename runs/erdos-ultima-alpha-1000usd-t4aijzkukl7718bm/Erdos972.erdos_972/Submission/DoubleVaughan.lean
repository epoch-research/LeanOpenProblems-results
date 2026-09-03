import Submission.GrowingTypeIIReduction

/-! An exact second Vaughan expansion of the remaining correlation. This
exposes a four-factor lattice sum; it does not assert cancellation in it. -/
namespace Erdos972DoubleVaughan

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972CorrelationVaughan Erdos972PrimePowerError

noncomputable def pairSum (α : ℝ) (N : ℕ) (f g : ArithmeticFunction ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 N, f n*g (floorMul α n)

noncomputable def typeIPart (U V : ℕ) : ArithmeticFunction ℝ :=
  cutoff (μ : ArithmeticFunction ℝ) U*ArithmeticFunction.log-
    cutoff (μ : ArithmeticFunction ℝ) U*ζ*cutoff Λ V+cutoff Λ V

noncomputable def typeIIPart (U V : ℕ) : ArithmeticFunction ℝ :=
  tail (μ : ArithmeticFunction ℝ) U*ζ*tail Λ V

lemma mangoldt_split (U V : ℕ) : Λ = typeIPart U V+typeIIPart U V := vaughan_identity U V

lemma pairSum_add_left (α : ℝ) (N : ℕ) (f g h : ArithmeticFunction ℝ) :
    pairSum α N (f+g) h = pairSum α N f h+pairSum α N g h := by
  simp only [pairSum, ArithmeticFunction.add_apply, add_mul, sum_add_distrib]

lemma pairSum_add_right (α : ℝ) (N : ℕ) (f g h : ArithmeticFunction ℝ) :
    pairSum α N f (g+h) = pairSum α N f g+pairSum α N f h := by
  simp only [pairSum, ArithmeticFunction.add_apply, mul_add, sum_add_distrib]

/-- The residual pair correlation is not the product of two nonnegative
functions: Vaughan's large-input part has no general sign. -/
theorem double_vaughan_identity (α : ℝ) (N U V S T : ℕ) :
    mangoldtCorrelation α N =
      pairSum α N (typeIPart U V) Λ+pairSum α N Λ (typeIPart S T)-
        pairSum α N (typeIPart U V) (typeIPart S T)+
          pairSum α N (typeIIPart U V) (typeIIPart S T) := by
  unfold mangoldtCorrelation pairSum
  simp only [← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have h₁ := congrArg (fun f : ArithmeticFunction ℝ => f n) (mangoldt_split U V)
  have h₂ := congrArg (fun f : ArithmeticFunction ℝ => f (floorMul α n)) (mangoldt_split S T)
  simp only [ArithmeticFunction.add_apply] at h₁ h₂
  rw [h₁, h₂]
  ring

/-- At prime arguments the genuine large-input remainder vanishes. -/
lemma typeIIPart_prime {U V p : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hp : p.Prime) :
    typeIIPart U V p = 0 := by
  unfold typeIIPart
  rw [ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro ab hab
  have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
  have hpab : (ab.1*ab.2).Prime := he ▸ hp
  rcases Nat.prime_mul_iff.mp hpab with ⟨_, hb⟩ | ⟨_, ha⟩
  · rw [hb, tail_eq_zero_of_le _ hV, mul_zero]
  · rw [ha, tail_mul_zeta_eq_zero_of_le _ U 1 hU, zero_mul]

lemma typeIPart_prime {U V p : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hp : p.Prime) :
    typeIPart U V p = Real.log p := by
  have hh := congrArg (fun f : ArithmeticFunction ℝ => f p) (mangoldt_split U V)
  simp only [ArithmeticFunction.add_apply] at hh
  rw [typeIIPart_prime hU hV hp, add_zero, vonMangoldt_apply_prime hp] at hh
  exact hh.symm

lemma point_mass_weightedSum (f : ArithmeticFunction ℝ) {Q q : ℕ} (hq : q ∈ Ioc 0 Q) :
    weightedSum f (fun t => if t = q then 1 else 0) Q = f q := by
  simp only [weightedSum, mul_ite, mul_one, mul_zero, sum_ite_eq', if_pos hq]

/-- Both convolutions are expanded while keeping the original floor relation
exact, including its endpoints. -/
theorem pairSum_convolution_convolution {α : ℝ} (hα : 1 ≤ α)
    (N : ℕ) (a b c d : ArithmeticFunction ℝ) :
    pairSum α N (a*b) (c*d) =
      ∑ m ∈ Ioc 0 N, a m*∑ n ∈ Ioc 0 (N/m), b n*
        ∑ k ∈ Ioc 0 (floorMul α N), c k*
          ∑ l ∈ Ioc 0 (floorMul α N/k), d l*(if k*l = floorMul α (m*n) then 1 else 0) := by
  change weightedSum (a*b) (fun n => (c*d) (floorMul α n)) N = _
  rw [weightedSum_convolution]
  apply sum_congr rfl
  intro m hm
  congr 1
  apply sum_congr rfl
  intro n hn
  congr 1
  have hmn0 : 0 < m*n := Nat.mul_pos (mem_Ioc.mp hm).1 (mem_Ioc.mp hn).1
  have hmnN : m*n ≤ N := (Nat.mul_le_mul_left m (mem_Ioc.mp hn).2).trans (Nat.mul_div_le N m)
  have hq : floorMul α (m*n) ∈ Ioc 0 (floorMul α N) := mem_Ioc.mpr
    ⟨floorMul_pos hα hmn0, (floorMul_strictMono hα).monotone hmnN⟩
  rw [← point_mass_weightedSum (c*d) hq, weightedSum_convolution]

lemma floor_relation_iff {α : ℝ} (hα : 0 ≤ α) (m n k l : ℕ) :
    k*l = floorMul α (m*n) ↔
      (k : ℝ)*l ≤ α*m*n ∧ α*m*n < (k : ℝ)*l+1 := by
  rw [eq_comm, floorMul, Nat.floor_eq_iff (show 0 ≤ α*(m*n : ℕ) by positivity)]
  push_cast
  simp only [mul_assoc]

noncomputable def fourFactorRemainder (α : ℝ) (N U V S T : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 N, (tail (μ : ArithmeticFunction ℝ) U*ζ) m*
    ∑ n ∈ Ioc 0 (N/m), tail Λ V n*
      ∑ k ∈ Ioc 0 (floorMul α N), (tail (μ : ArithmeticFunction ℝ) S*ζ) k*
        ∑ l ∈ Ioc 0 (floorMul α N/k), tail Λ T l*
          (if k*l = floorMul α (m*n) then 1 else 0)

lemma typeII_pair_eq_fourFactor {α : ℝ} (hα : 1 ≤ α) (N U V S T : ℕ) :
    pairSum α N (typeIIPart U V) (typeIIPart S T) = fourFactorRemainder α N U V S T :=
  pairSum_convolution_convolution hα N _ _ _ _

/-- Every nonzero term has two genuinely large factors on each side. The
prime factors are retained rather than bounded as an unweighted lattice count. -/
lemma fourFactor_support (U V S T m n k l : ℕ)
    (h : (tail (μ : ArithmeticFunction ℝ) U*ζ) m*tail Λ V n*
      (tail (μ : ArithmeticFunction ℝ) S*ζ) k*tail Λ T l ≠ 0) :
    U < m ∧ V < n ∧ S < k ∧ T < l := by
  simp only [mul_ne_zero_iff] at h
  obtain ⟨⟨⟨hm, hn⟩, hk⟩, hl⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hh
    exact hm (tail_mul_zeta_eq_zero_of_le _ U m (Nat.le_of_not_gt hh))
  · by_contra hh
    exact hn (tail_eq_zero_of_le _ (Nat.le_of_not_gt hh))
  · by_contra hh
    exact hk (tail_mul_zeta_eq_zero_of_le _ S k (Nat.le_of_not_gt hh))
  · by_contra hh
    exact hl (tail_eq_zero_of_le _ (Nat.le_of_not_gt hh))

/-- A general lower-bound identity for genuine nonnegative majorants. A
Vaughan Type-I part cannot be substituted here without proving the majorant
hypotheses: its large-input remainder need not be nonpositive. -/
lemma pairSum_majorant_lower (α : ℝ) (N : ℕ) (f g A B : ArithmeticFunction ℝ)
    (hA : ∀ n ∈ Ioc 0 N, f n ≤ A n)
    (hB : ∀ n ∈ Ioc 0 N, g (floorMul α n) ≤ B (floorMul α n)) :
    pairSum α N A g+pairSum α N f B-pairSum α N A B ≤ pairSum α N f g := by
  simp only [pairSum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_le_sum
  intro n hn
  nlinarith only [mul_nonneg (sub_nonneg.mpr (hA n hn)) (sub_nonneg.mpr (hB n hn))]

#print axioms double_vaughan_identity
#print axioms pairSum_convolution_convolution
#print axioms fourFactor_support

end Erdos972DoubleVaughan
