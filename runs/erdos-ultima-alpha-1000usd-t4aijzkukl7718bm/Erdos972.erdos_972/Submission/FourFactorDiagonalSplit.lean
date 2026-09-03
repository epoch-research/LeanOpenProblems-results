import Submission.VaughanDiagonalBound
import Submission.PrimeFactorRemainder

/-! An exact decomposition of a two-convolution Beatty correlation into
common-factor diagonal and unequal-factor off-diagonal contributions.
This is an identity, not a signed estimate for the off-diagonal. -/
namespace Erdos972FourFactorDiagonalSplit

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972PrimePowerError Erdos972DoubleVaughan Erdos972FloorDiagonalCount
open Erdos972Vaughan Erdos972VaughanDiagonalBound Erdos972MellinDivisorCoefficient
open Erdos972PrimeFactorRemainder
set_option maxHeartbeats 1500000

noncomputable def factorOffDiagonal (α : ℝ) (N : ℕ)
    (a b : ArithmeticFunction ℝ) : ℝ :=
  ∑ m ∈ Ioc 0 N, a m*∑ p ∈ Ioc 0 (N/m), b p*
    ∑ k ∈ Ioc 0 (floorMul α N), a k*
      ∑ q ∈ Ioc 0 (floorMul α N/k), b q*
        (if k*q = floorMul α (m*p) ∧ p ≠ q then 1 else 0)

noncomputable def factorDiagonal (α : ℝ) (N : ℕ)
    (a b : ArithmeticFunction ℝ) : ℝ :=
  ∑ p ∈ Ioc 0 N, ∑ m ∈ diagonalRows α N p,
    a m*a (floorMul α m)*(b p)^2

lemma diagonal_inner_sum {α : ℝ} (hα : 1 ≤ α) {N m p : ℕ}
    (hm : 0 < m) (hp : 0 < p) (hmp : m*p ≤ N) (a b : ArithmeticFunction ℝ) :
    (∑ k ∈ Ioc 0 (floorMul α N), a k*
      ∑ q ∈ Ioc 0 (floorMul α N/k), b q*
        (if k*q = floorMul α (m*p) ∧ p = q then 1 else 0)) =
      if Int.fract (α*m) < 1/(p : ℝ) then a (floorMul α m)*b p else 0 := by
  classical
  have hmN : m ≤ N := (Nat.le_mul_of_pos_right m hp).trans hmp
  have hK : floorMul α m ∈ Ioc 0 (floorMul α N) := mem_Ioc.mpr
    ⟨floorMul_pos hα hm, (floorMul_strictMono hα).monotone hmN⟩
  have hY : floorMul α (m*p) ≤ floorMul α N := (floorMul_strictMono hα).monotone hmp
  have hi (k : ℕ) (hk : k ∈ Ioc 0 (floorMul α N)) :
      (∑ q ∈ Ioc 0 (floorMul α N/k), b q*
        (if k*q = floorMul α (m*p) ∧ p = q then 1 else 0)) =
      b p*(if k*p = floorMul α (m*p) then 1 else 0) := by
    rw [sum_eq_single p]
    · simp
    · intro q hq hqp
      simp [Ne.symm hqp]
    · intro hnot
      have hnrel : k*p ≠ floorMul α (m*p) := by
        intro hh
        apply hnot
        exact mem_Ioc.mpr ⟨hp, (Nat.le_div_iff_mul_le (mem_Ioc.mp hk).1).mpr
          (by simpa only [mul_comm p k] using hh.le.trans hY)⟩
      simp [hnrel]
  rw [sum_congr rfl (fun k hk => congrArg (a k * ·) (hi k hk))]
  have hrel (k : ℕ) : k*p = floorMul α (m*p) ↔
      k = floorMul α m ∧ Int.fract (α*m) < 1/(p : ℝ) :=
    floor_diagonal_iff (by linarith) hp
  simp_rw [hrel]
  rw [sum_eq_single (floorMul α m)]
  · by_cases hf : Int.fract (α*m) < 1/(p : ℝ) <;> simp [hf]
  · intro k hk hkne
    simp [hkne]
  · exact fun hnot => (hnot hK).elim

lemma diagonal_expansion {α : ℝ} (hα : 1 ≤ α) (N : ℕ)
    (a b : ArithmeticFunction ℝ) :
    (∑ m ∈ Ioc 0 N, a m*∑ p ∈ Ioc 0 (N/m), b p*
      ∑ k ∈ Ioc 0 (floorMul α N), a k*
        ∑ q ∈ Ioc 0 (floorMul α N/k), b q*
          (if k*q = floorMul α (m*p) ∧ p = q then 1 else 0)) = factorDiagonal α N a b := by
  classical
  have hreduced :
      (∑ m ∈ Ioc 0 N, a m*∑ p ∈ Ioc 0 (N/m), b p*
        ∑ k ∈ Ioc 0 (floorMul α N), a k*
          ∑ q ∈ Ioc 0 (floorMul α N/k), b q*
            (if k*q = floorMul α (m*p) ∧ p = q then 1 else 0)) =
      ∑ m ∈ Ioc 0 N, ∑ p ∈ Ioc 0 (N/m),
        if Int.fract (α*m) < 1/(p : ℝ) then a m*a (floorMul α m)*(b p)^2 else 0 := by
    apply sum_congr rfl
    intro m hm
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    have hmp : m*p ≤ N := (Nat.mul_le_mul_left m (mem_Ioc.mp hp).2).trans (Nat.mul_div_le N m)
    rw [diagonal_inner_sum hα (mem_Ioc.mp hm).1 (mem_Ioc.mp hp).1 hmp]
    split_ifs <;> ring
  rw [hreduced]
  let F : ℕ → ℕ → ℝ := fun m p =>
    if Int.fract (α*m) < 1/(p : ℝ) then a m*a (floorMul α m)*(b p)^2 else 0
  have hswap : (∑ m ∈ Ioc 0 N, ∑ p ∈ Ioc 0 (N/m), F m p) =
      ∑ p ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N/p), F m p := by
    rw [← Erdos972DivisorEnergy.sum_divisorsAntidiagonal_eq_sum_hyperbola F N,
      ← Erdos972DivisorEnergy.sum_divisorsAntidiagonal_eq_sum_hyperbola (fun p m => F m p) N]
    apply sum_congr rfl
    intro n hn
    rw [Nat.sum_divisorsAntidiagonal F, Nat.sum_divisorsAntidiagonal' (fun p m => F m p)]
  change (∑ m ∈ Ioc 0 N, ∑ p ∈ Ioc 0 (N/m), F m p) = _
  rw [hswap]
  unfold factorDiagonal diagonalRows
  simp only [sum_filter]
  rfl

theorem pair_convolution_diagonal_split {α : ℝ} (hα : 1 ≤ α) (N : ℕ)
    (a b : ArithmeticFunction ℝ) :
    pairSum α N (a*b) (a*b) = factorDiagonal α N a b + factorOffDiagonal α N a b := by
  classical
  rw [pairSum_convolution_convolution hα, ← diagonal_expansion hα]
  unfold factorOffDiagonal
  simp only [← sum_add_distrib, ← mul_add]
  apply sum_congr rfl
  intro m hm
  congr 1
  apply sum_congr rfl
  intro p hp
  congr 1
  apply sum_congr rfl
  intro k hk
  congr 1
  apply sum_congr rfl
  intro q hq
  by_cases hrel : k*q = floorMul α (m*p) <;> by_cases heq : p = q <;> simp [hrel, heq]

lemma factorDiagonal_tail (α : ℝ) (N V : ℕ) (a g : ArithmeticFunction ℝ) :
    factorDiagonal α N a (tail g V) =
      ∑ p ∈ Ioc V N, ∑ m ∈ diagonalRows α N p,
        a m*a (floorMul α m)*(g p)^2 := by
  classical
  unfold factorDiagonal
  have hsub : Ioc V N ⊆ Ioc 0 N := by
    intro p hp
    exact mem_Ioc.mpr ⟨(Nat.zero_le V).trans_lt (mem_Ioc.mp hp).1, (mem_Ioc.mp hp).2⟩
  calc
    _ = ∑ p ∈ Ioc V N, ∑ m ∈ diagonalRows α N p,
        a m*a (floorMul α m)*(tail g V p)^2 := by
      symm
      apply sum_subset hsub
      intro p hp hnot
      have hpV : p ≤ V := by
        by_contra hh
        exact hnot (mem_Ioc.mpr ⟨by omega, (mem_Ioc.mp hp).2⟩)
      simp only [tail_eq_zero_of_le g hpV, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero, sum_const_zero]
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      rw [tail_eq_of_lt g (mem_Ioc.mp hp).1]

lemma factorDiagonal_vaughan (α : ℝ) (N U V : ℕ) :
    factorDiagonal α N (tail (μ : ArithmeticFunction ℝ) U*ζ) (tail Λ V) =
      vaughanDiagonal α N U V := by
  rw [factorDiagonal_tail]
  rfl

theorem fourFactor_diagonal_split {α : ℝ} (hα : 1 ≤ α) (N U V : ℕ) :
    fourFactorRemainder α N U V U V = vaughanDiagonal α N U V +
      factorOffDiagonal α N (tail (μ : ArithmeticFunction ℝ) U*ζ) (tail Λ V) := by
  rw [← typeII_pair_eq_fourFactor hα]
  change pairSum α N (_*_) (_*_) = _
  rw [pair_convolution_diagonal_split hα, factorDiagonal_vaughan]

noncomputable def primeVaughanDiagonal (α : ℝ) (N U V : ℕ) : ℝ :=
  ∑ p ∈ Ioc V N, ∑ m ∈ diagonalRows α N p,
    divisorCoeff U m*divisorCoeff U (floorMul α m)*(primeMangoldt p)^2

noncomputable def primeFactorOffDiagonal (α : ℝ) (N U V : ℕ) : ℝ :=
  factorOffDiagonal α N (tail (μ : ArithmeticFunction ℝ) U*ζ) (tail primeMangoldt V)

theorem prime_remainder_diagonal_split {α : ℝ} (hα : 1 ≤ α) (N U V : ℕ) :
    pairSum α N (primeTypeIIPart U V) (primeTypeIIPart U V) =
      primeVaughanDiagonal α N U V + primeFactorOffDiagonal α N U V := by
  unfold primeTypeIIPart
  rw [pair_convolution_diagonal_split hα, factorDiagonal_tail]
  rfl

lemma tail_primeMangoldt_nonzero {V p : ℕ} (h : tail primeMangoldt V p ≠ 0) :
    V < p ∧ p.Prime := by
  have hVp : V < p := by
    by_contra hh
    exact h (tail_eq_zero_of_le _ (by omega))
  rw [tail_eq_of_lt _ hVp] at h
  change (if p.Prime then Λ p else 0) ≠ 0 at h
  refine ⟨hVp, ?_⟩
  by_contra hp
  simp only [if_neg hp, ne_self_iff_false] at h

lemma prime_offDiagonal_support (α : ℝ) (U V m p k q : ℕ)
    (h : divisorCoeff U m*tail primeMangoldt V p*divisorCoeff U k*tail primeMangoldt V q*
      (if k*q = floorMul α (m*p) ∧ p ≠ q then (1 : ℝ) else 0) ≠ 0) :
    U < m ∧ V < p ∧ U < k ∧ V < q ∧ p.Prime ∧ q.Prime ∧ p ≠ q ∧
      k*q = floorMul α (m*p) := by
  classical
  simp only [mul_ne_zero_iff] at h
  obtain ⟨⟨⟨⟨hm, hp⟩, hk⟩, hq⟩, hrel⟩ := h
  have hmU : U < m := by
    by_contra hh
    exact hm (tail_mul_zeta_eq_zero_of_le _ U m (by omega))
  have hkU : U < k := by
    by_contra hh
    exact hk (tail_mul_zeta_eq_zero_of_le _ U k (by omega))
  have hp' := tail_primeMangoldt_nonzero hp
  have hq' := tail_primeMangoldt_nonzero hq
  have hrel' : k*q = floorMul α (m*p) ∧ p ≠ q := by
    by_contra hh
    simp [hh] at hrel
  exact ⟨hmU, hp'.1, hkU, hq'.1, hp'.2, hq'.2, hrel'.2, hrel'.1⟩

lemma prime_vaughan_diagonal_bound {α : ℝ} {a q N U V : ℕ}
    (hα : 0 ≤ α) (hq : 0 < q) (haq : a.Coprime q)
    (happrox : |α-(a : ℝ)/q| *N ≤ 1) (hN : N ≤ q^2) (hV : 0 < V) :
    |primeVaughanDiagonal α N U V| ≤
      ((U : ℝ)+1)^2*(Real.log N)^2*
        (10*N/(V : ℝ)+(2*N/(q : ℝ)+5*q)*(1+Real.log (2*q : ℕ))+2*q) := by
  apply weighted_diagonal_bound hα hq haq happrox hN hV _ (by positivity)
  intro p hp m _hm
  have hp0 : 0 < p := hV.trans (mem_Ioc.mp hp).1
  have hpN : p ≤ N := (mem_Ioc.mp hp).2
  have hΛ : primeMangoldt p ≤ Real.log N := (primeMangoldt_le p).trans
    (vonMangoldt_le_log.trans (Real.log_le_log (Nat.cast_pos.mpr hp0) (Nat.cast_le.mpr hpN)))
  have hsq := pow_le_pow_left₀ (primeMangoldt_nonneg p) hΛ 2
  simp only [abs_mul, abs_pow, sq_abs]
  have hh := mul_le_mul (divisorCoeff_abs_le U m) (divisorCoeff_abs_le U (floorMul α m))
    (abs_nonneg _) (by positivity)
  exact (mul_le_mul hh hsq (sq_nonneg _) (by positivity)).trans_eq (by ring)

#print axioms diagonal_inner_sum
#print axioms diagonal_expansion
#print axioms pair_convolution_diagonal_split
#print axioms fourFactor_diagonal_split
#print axioms prime_remainder_diagonal_split
#print axioms prime_offDiagonal_support
#print axioms prime_vaughan_diagonal_bound
end Erdos972FourFactorDiagonalSplit
