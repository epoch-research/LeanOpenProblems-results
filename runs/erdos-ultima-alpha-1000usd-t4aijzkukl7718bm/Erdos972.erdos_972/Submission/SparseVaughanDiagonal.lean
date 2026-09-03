import Submission.SparseCommonDivisorSupport
import Submission.SparseDivisorMoment

/-! A fourth-moment diagonal bound independent of the Mobius cutoff.
It uses the sparse large-common-divisor support, without signed cancellation. -/
namespace Erdos972SparseVaughanDiagonal
open Finset Classical ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972SparseCommonDivisorSupport Erdos972SparseDivisorMoment
open Erdos972FloorDiagonalCount Erdos972FourFactorDiagonalSplit
open Erdos972Vaughan Erdos972MellinDivisorCoefficient Erdos972PrimePowerError
set_option maxHeartbeats 1500000

noncomputable def diagonalAt (α : ℝ) (U V : ℕ) (g : ArithmeticFunction ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.divisors, if V < p ∧ p ∣ floorMul α n then
    divisorCoeff U (n/p)*divisorCoeff U (floorMul α n/p)*(g p)^2 else 0

lemma diagonalAt_zero_outside {α : ℝ} {U V N n : ℕ} (g : ArithmeticFunction ℝ)
    (hn : n ∈ Ioc 0 N) (hnot : n ∉ commonDivisorSet α N V) : diagonalAt α U V g n = 0 := by
  apply sum_eq_zero
  intro p hp
  have hh : ¬ (V < p ∧ p ∣ floorMul α n) := by
    rintro ⟨hpV, hpf⟩
    exact hnot (mem_filter.mpr ⟨hn, p, hpV, Nat.dvd_of_mem_divisors hp, hpf⟩)
  simp only [if_neg hh]

lemma diagonalAt_sum_eq {α : ℝ} (hα : 0 ≤ α) (N U V : ℕ) (g : ArithmeticFunction ℝ) :
    (∑ n ∈ Ioc 0 N, diagonalAt α U V g n) =
      factorDiagonal α N (tail (μ : ArithmeticFunction ℝ) U*ζ) (tail g V) := by
  let F : ℕ → ℕ → ℝ := fun p m => if V < p ∧ p ∣ floorMul α (m*p) then
    divisorCoeff U m*divisorCoeff U (floorMul α (m*p)/p)*(g p)^2 else 0
  have hrep (n : ℕ) : diagonalAt α U V g n = ∑ ab ∈ n.divisorsAntidiagonal, F ab.1 ab.2 := by
    rw [Nat.sum_divisorsAntidiagonal F]
    apply sum_congr rfl
    intro p hp
    dsimp only [F]
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hp)]
  simp only [hrep]
  rw [Erdos972DivisorEnergy.sum_divisorsAntidiagonal_eq_sum_hyperbola F N,
    factorDiagonal_tail]
  have hsub : Ioc V N ⊆ Ioc 0 N := by
    intro p hp
    exact mem_Ioc.mpr ⟨(Nat.zero_le V).trans_lt (mem_Ioc.mp hp).1, (mem_Ioc.mp hp).2⟩
  calc
    _ = ∑ p ∈ Ioc V N, ∑ m ∈ Ioc 0 (N/p), F p m := by
      symm
      apply sum_subset hsub
      intro p hp hnot
      have hpV : ¬ V < p := fun hh => hnot (mem_Ioc.mpr ⟨hh, (mem_Ioc.mp hp).2⟩)
      simp only [F, hpV, false_and, if_false, sum_const_zero]
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      have hp0 : 0 < p := (Nat.zero_le V).trans_lt (mem_Ioc.mp hp).1
      rw [diagonalRows, sum_filter]
      apply sum_congr rfl
      intro m hm
      dsimp only [F]
      simp only [(mem_Ioc.mp hp).1, true_and]
      by_cases hd : p ∣ floorMul α (m*p)
      · rw [if_pos hd, if_pos ((floor_common_divisor_iff hα hp0).mp hd), floor_div_common_eq hα hp0 hd]
        rfl
      · rw [if_neg hd, if_neg (fun hf => hd ((floor_common_divisor_iff hα hp0).mpr hf))]

lemma absolute_divisor_mangoldt_sum (U n : ℕ) :
    (∑ p ∈ n.divisors, |divisorCoeff U (n/p)| *Λ p) ≤ (n.divisors.card : ℝ)*Real.log n := by
  calc
    _ ≤ ∑ p ∈ n.divisors, (n.divisors.card : ℝ)*Λ p := by
      apply sum_le_sum
      intro p hp
      have hd := Nat.mem_divisors.mp hp
      have hc := Nat.cast_le (α := ℝ).mpr
        (card_le_card (Nat.divisors_subset_of_dvd hd.2 (Nat.div_dvd_of_dvd hd.1)))
      exact mul_le_mul_of_nonneg_right
        ((abs_typeII_coefficient_le_card_divisors U (n/p)).trans hc) vonMangoldt_nonneg
    _ = _ := by rw [← mul_sum, vonMangoldt_sum]

lemma diagonalAt_abs_bound {α : ℝ} (hα : 1 ≤ α) (U V n : ℕ)
    (g : ArithmeticFunction ℝ) (hg : ∀ p, 0 ≤ g p) (hgΛ : ∀ p, g p ≤ Λ p) :
    |diagonalAt α U V g n| ≤
      (n.divisors.card : ℝ)*Real.log n*
        ((floorMul α n).divisors.card : ℝ)*Real.log (floorMul α n) := by
  by_cases hn : n = 0
  · subst n
    simp [diagonalAt]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hout : floorMul α n ≠ 0 := (floorMul_pos hα hn0).ne'
  let A : ℕ → ℝ := fun p => |divisorCoeff U (n/p)| *Λ p
  let B : ℕ → ℝ := fun p => |divisorCoeff U (floorMul α n/p)| *Λ p
  have hA (p : ℕ) : 0 ≤ A p := mul_nonneg (abs_nonneg _) vonMangoldt_nonneg
  have hB (p : ℕ) : 0 ≤ B p := mul_nonneg (abs_nonneg _) vonMangoldt_nonneg
  have hterm (p : ℕ) (hp : p ∈ n.divisors) :
      |if V < p ∧ p ∣ floorMul α n then
        divisorCoeff U (n/p)*divisorCoeff U (floorMul α n/p)*(g p)^2 else 0| ≤
      A p * ∑ q ∈ (floorMul α n).divisors, B q := by
    split_ifs with h
    · have hpout := Nat.mem_divisors.mpr ⟨h.2, hout⟩
      have hBb := single_le_sum (fun q _ => hB q) hpout
      have hsq := pow_le_pow_left₀ (hg p) (hgΛ p) 2
      simp only [abs_mul, abs_pow, sq_abs]
      calc
        _ ≤ |divisorCoeff U (n/p)| *|divisorCoeff U (floorMul α n/p)| *(Λ p)^2 := by gcongr
        _ = A p*B p := by dsimp [A, B]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hBb (hA p)
    · rw [abs_zero]
      exact mul_nonneg (hA p) (sum_nonneg (fun q _ => hB q))
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum hterm).trans
  rw [← sum_mul]
  have ha := absolute_divisor_mangoldt_sum U n
  have hb := absolute_divisor_mangoldt_sum U (floorMul α n)
  change (∑ p ∈ n.divisors, A p) ≤ _ at ha
  change (∑ p ∈ (floorMul α n).divisors, B p) ≤ _ at hb
  exact (mul_le_mul ha hb (sum_nonneg (fun q _ => hB q))
    (by positivity [Real.log_natCast_nonneg n])).trans_eq (by ring)

lemma diagonalAt_log_bound {α L : ℝ} (hα : 1 ≤ α) {U V N n : ℕ}
    (hn : n ∈ Ioc 0 N) (hiL : 1+Real.log N ≤ L)
    (hoL : 1+Real.log (floorMul α N) ≤ L)
    (g : ArithmeticFunction ℝ) (hg : ∀ p, 0 ≤ g p) (hgΛ : ∀ p, g p ≤ Λ p) :
    |diagonalAt α U V g n| ≤ L^2*(n.divisors.card : ℝ)*(floorMul α n).divisors.card := by
  have hL : 0 ≤ L := by linarith [Real.log_natCast_nonneg N]
  have hi := (log_input_le hn).trans (show Real.log N ≤ L by linarith)
  have ho : Real.log (floorMul α n) ≤ L := (Real.log_le_log
    (Nat.cast_pos.mpr (floorMul_pos hα (mem_Ioc.mp hn).1))
    (Nat.cast_le.mpr ((floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2))).trans
      (by linarith only [hoL])
  apply (diagonalAt_abs_bound hα U V n g hg hgΛ).trans
  calc
    _ ≤ (n.divisors.card : ℝ)*L*((floorMul α n).divisors.card : ℝ)*L := by
      gcongr <;> positivity [Real.log_natCast_nonneg n]
    _ = _ := by ring

/-- No bound on U occurs in this estimate. -/
theorem sparse_diagonal_fourth_bound {α L : ℝ} (hα : 1 ≤ α) {N U V : ℕ}
    (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L)
    (g : ArithmeticFunction ℝ) (hg : ∀ p, 0 ≤ g p) (hgΛ : ∀ p, g p ≤ Λ p) :
    |factorDiagonal α N (tail (μ : ArithmeticFunction ℝ) U*ζ) (tail g V)|^4 ≤
      ((commonDivisorSet α N V).card : ℝ)^2*(N : ℝ)*(floorMul α N : ℝ)*L^38 := by
  rw [← diagonalAt_sum_eq (show 0 ≤ α by linarith)]
  have he : (∑ n ∈ Ioc 0 N, diagonalAt α U V g n) =
      ∑ n ∈ commonDivisorSet α N V, diagonalAt α U V g n := by
    symm
    apply sum_subset (commonDivisorSet_subset α N V)
    intro n hn hnot
    exact diagonalAt_zero_outside g hn hnot
  rw [he]
  have hh := sparse_sum_fourth_bound hα (commonDivisorSet α N V)
    (commonDivisorSet_subset α N V) hiL hoL (diagonalAt α U V g)
    (fun n hn => diagonalAt_log_bound hα (commonDivisorSet_subset α N V hn) hiL hoL g hg hgΛ)
  exact hh.trans_eq (by ring)

theorem sparse_diagonal_normalized_fourth {α L : ℝ} (hα : 1 ≤ α) {N U V : ℕ}
    (hN : 0 < N) (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L)
    (g : ArithmeticFunction ℝ) (hg : ∀ p, 0 ≤ g p) (hgΛ : ∀ p, g p ≤ Λ p) :
    |factorDiagonal α N (tail (μ : ArithmeticFunction ℝ) U*ζ) (tail g V)/(N : ℝ)|^4 ≤
      α*(((commonDivisorSet α N V).card : ℝ)/N)^2*L^38 := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hL : 0 ≤ L := by linarith [Real.log_natCast_nonneg N]
  have hh := sparse_diagonal_fourth_bound (U := U) (V := V) hα hiL hoL g hg hgΛ
  have hY := floorMul_le_real hα (le_refl N)
  have hb : |factorDiagonal α N (tail (μ : ArithmeticFunction ℝ) U*ζ) (tail g V)|^4 ≤
      ((commonDivisorSet α N V).card : ℝ)^2*(N : ℝ)*(α*N)*L^38 := by
    apply hh.trans
    gcongr
  rw [abs_div, abs_of_pos hN0, div_pow]
  apply (div_le_iff₀ (pow_pos hN0 4)).mpr
  exact hb.trans_eq (by field_simp <;> ring)

#print axioms diagonalAt_sum_eq
#print axioms diagonalAt_abs_bound
#print axioms sparse_diagonal_normalized_fourth
end Erdos972SparseVaughanDiagonal
