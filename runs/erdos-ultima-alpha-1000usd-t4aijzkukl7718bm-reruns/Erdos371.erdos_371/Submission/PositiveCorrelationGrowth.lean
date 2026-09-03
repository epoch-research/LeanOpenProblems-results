import FormalConjecturesUtil
import Submission.UnsignedEnergyGrowth
import Submission.GcdCorrelation

/-! Positive off-diagonal winning-prime correlations have genuinely
superlinear total count. This is not a lower bound for signed energy and
not a disproof of the original density conjecture. -/

namespace Erdos371PositiveCorrelationGrowth

open Finset Filter Erdos371PrimeDiscrepancy Erdos371PrimeEnergy
open Erdos371OffDiagonalEnergy Erdos371UnsignedEnergyGrowth Erdos371GcdCorrelation
open scoped Topology

noncomputable def unsignedCorrelation (n m : ℕ) : ℝ :=
  if 0<n ∧ 0 < m ∧ winner n=winner m then 1 else 0

lemma unsignedCorrelation_symm (n m : ℕ) :
    unsignedCorrelation n m=unsignedCorrelation m n := by
  simp only [unsignedCorrelation]
  by_cases hn : 0<n <;> by_cases hm : 0 < m <;>
    by_cases hw : winner n=winner m <;> simp_all [eq_comm]

lemma unsignedCorrelation_self (n : ℕ) :
    unsignedCorrelation n n=if n=0 then 0 else 1 := by
  by_cases hn : n=0 <;> simp [unsignedCorrelation,hn,Nat.pos_of_ne_zero]

lemma unsignedEnergy_eq_double_sum (N : ℕ) :
    unsignedEnergy N=∑ n ∈ range N, ∑ m ∈ range N, unsignedCorrelation n m := by
  have hm (p : ℕ) : mass p N=∑ n ∈ range N, if winner n=p then (1:ℝ) else 0 := by
    simp [mass]
  unfold unsignedEnergy
  simp_rw [hm,pow_two,sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  have hwn := winner_mem_iff (mem_range.mp hn)
  have hwm := winner_mem_iff (mem_range.mp hm)
  by_cases he : winner n=winner m
  · have hpos : 0<n ↔ 0 < m := by rw [← hwn,← hwm,he]
    simp only [he,ite_mul,mul_ite,mul_zero,zero_mul,one_mul,sum_ite_eq,
      unsignedCorrelation,and_true]
    by_cases h : 0 < m <;> simp_all
  · have hz (p : ℕ) :
        (if winner n=p then (1:ℝ) else 0)*(if winner m=p then 1 else 0)=0 := by
      split_ifs <;> simp_all
    simp [hz,unsignedCorrelation,he]

lemma unsigned_triangle_eq (N : ℕ) :
    (∑ m ∈ range N, ∑ n ∈ range m, unsignedCorrelation n m)=
      (sameCount N:ℝ)+(oppositeCount N:ℝ) := by
  unfold sameCount oppositeCount
  push_cast
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  rw [← sum_boole,← sum_boole,← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  have hnm := mem_range.mp hn
  have hm0 : 0 < m := by omega
  unfold unsignedCorrelation
  by_cases hn0 : 0<n <;> by_cases hw : winner n=winner m <;>
    by_cases hs : sign n=sign m <;> simp [hn0,hm0,hw,hs]

lemma unsignedEnergy_eq_counts (N : ℕ) : unsignedEnergy N=
    (N-1:ℕ)+2*((sameCount N:ℝ)+(oppositeCount N:ℝ)) := by
  rw [unsignedEnergy_eq_double_sum,
    sum_square_eq_diagonal_add_twice_triangle unsignedCorrelation unsignedCorrelation_symm,
    unsigned_triangle_eq]
  have he : (∑ n ∈ range N, unsignedCorrelation n n)=(N-1:ℕ) := by
    simp_rw [unsignedCorrelation_self]
    cases N with
    | zero => simp
    | succ N => rw [sum_range_succ']; simp
  rw [he]

/-- The positive pair count includes both signs of the original comparisons,
provided the two signs agree. It is not the signed off-diagonal sum. -/
theorem four_sameCount_eq (N : ℕ) :
    4*(sameCount N:ℝ)=unsignedEnergy N+energy N-2*(N-1:ℕ) := by
  rw [unsignedEnergy_eq_counts,energy_eq_pair_counts]
  ring

lemma unsignedEnergy_le_sameCount (N : ℕ) :
    unsignedEnergy N≤4*(sameCount N:ℝ)+2*(N:ℝ) := by
  have hd : ((N-1:ℕ):ℝ)≤N := Nat.cast_le.mpr (Nat.sub_le _ _)
  have he := four_sameCount_eq N
  linarith [energy_nonneg N]

/-- Even the positive correlations alone cannot be majorized by N times any
fixed logarithmic power. Their cancellation against negative correlations
is indispensable. This theorem does NOT disprove a near-linear signed bound. -/
theorem not_eventually_polylog_sameCount (B : ℕ) (C : ℝ) :
    ¬ ∀ᶠ N : ℕ in atTop, (sameCount N:ℝ)≤C*N*Real.log (N:ℝ)^B := by
  intro h
  apply not_eventually_polylog_unsignedEnergy B (4*|C|+2)
  have hl : ∀ᶠ N : ℕ in atTop, 1≤Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop 1)
  filter_upwards [h,hl] with N hN hlN
  have hp : 1≤Real.log (N:ℝ)^B := one_le_pow₀ hlN
  have hC : C*(N:ℝ)*Real.log (N:ℝ)^B≤|C| *N*Real.log (N:ℝ)^B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C)
      (Nat.cast_nonneg N)) (by positivity)
  have h2 : 2*(N:ℝ)≤2*N*Real.log (N:ℝ)^B := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hU := unsignedEnergy_le_sameCount N
  nlinarith

def farPositiveCount (N : ℕ) : ℕ :=
  ∑ m ∈ range N, ((range m).filter fun n =>
    0<n ∧ winner n=winner m ∧ sign n=sign m ∧ ¬close n m).card

lemma same_not_close {n m : ℕ} (hs : sign n=sign m) : ¬close n m :=
  fun h => close_signs_opposite h hs

lemma farPositiveCount_eq (N : ℕ) : farPositiveCount N=sameCount N := by
  unfold farPositiveCount sameCount
  apply sum_congr rfl
  intro m hm
  congr 1
  ext n
  simp only [mem_filter]
  exact and_congr_right fun hn =>
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1⟩,
      fun h => ⟨h.1,h.2.1,h.2.2,same_not_close h.2.2⟩⟩

/-- Removing the checked negative gcd region removes NO positive pairs. -/
theorem not_eventually_polylog_farPositiveCount (B : ℕ) (C : ℝ) :
    ¬ ∀ᶠ N : ℕ in atTop, (farPositiveCount N:ℝ)≤C*N*Real.log (N:ℝ)^B := by
  simpa only [farPositiveCount_eq] using not_eventually_polylog_sameCount B C

end Erdos371PositiveCorrelationGrowth

#print axioms Erdos371PositiveCorrelationGrowth.four_sameCount_eq
#print axioms Erdos371PositiveCorrelationGrowth.not_eventually_polylog_sameCount
#print axioms Erdos371PositiveCorrelationGrowth.not_eventually_polylog_farPositiveCount
