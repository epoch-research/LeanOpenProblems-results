import Submission.FourFactorDiagonalSplit

/-! Sparse support for large common divisors of n and floor(alpha*n).
The support count is independent of any Mobius cutoff. -/
namespace Erdos972SparseCommonDivisorSupport
open Finset Classical
open Erdos972FloorDiagonalCount Erdos972PrimePowerError
set_option maxHeartbeats 1200000

lemma floor_common_divisor_iff {α : ℝ} (hα : 0 ≤ α) {p m : ℕ} (hp : 0 < p) :
    p ∣ floorMul α (m*p) ↔ Int.fract (α*m) < 1/(p : ℝ) := by
  constructor
  · intro hd
    have he : (floorMul α (m*p)/p)*p = floorMul α (m*p) := Nat.div_mul_cancel hd
    exact ((floor_diagonal_iff hα hp).mp he).2
  · intro hf
    have he := floor_diagonal_of_fract hα hp hf
    change floorMul α m*p = floorMul α (m*p) at he
    rw [← he]
    exact dvd_mul_left _ _

lemma floor_div_common_eq {α : ℝ} (hα : 0 ≤ α) {p m : ℕ} (hp : 0 < p)
    (hd : p ∣ floorMul α (m*p)) :
    floorMul α (m*p)/p = floorMul α m := by
  exact ((floor_diagonal_iff hα hp).mp (Nat.div_mul_cancel hd)).1

noncomputable def commonDivisorSet (α : ℝ) (N V : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter fun n => ∃ p : ℕ, V < p ∧ p ∣ n ∧ p ∣ floorMul α n

lemma commonDivisorSet_subset (α : ℝ) (N V : ℕ) :
    commonDivisorSet α N V ⊆ Ioc 0 N := filter_subset _ _

lemma commonDivisorSet_eq_union {α : ℝ} (hα : 0 ≤ α) (N V : ℕ) :
    commonDivisorSet α N V = (Ioc V N).biUnion fun p =>
      (diagonalRows α N p).image (fun m => m*p) := by
  classical
  ext n
  simp only [commonDivisorSet, mem_filter, mem_biUnion, mem_image]
  constructor
  · rintro ⟨hn, p, hpV, hpn, hpf⟩
    have hp0 : 0 < p := (Nat.zero_le V).trans_lt hpV
    have hn0 := (mem_Ioc.mp hn).1
    have hpnle := Nat.le_of_dvd hn0 hpn
    have hmult : n/p*p = n := Nat.div_mul_cancel hpn
    refine ⟨p, mem_Ioc.mpr ⟨hpV, hpnle.trans (mem_Ioc.mp hn).2⟩, n/p, ?_, hmult⟩
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨Nat.div_pos hpnle hp0, Nat.div_le_div_right (mem_Ioc.mp hn).2⟩, ?_⟩
    apply (floor_common_divisor_iff hα hp0).mp
    rwa [hmult]
  · rintro ⟨p, hp, m, hm, rfl⟩
    have hp0 : 0 < p := (Nat.zero_le V).trans_lt (mem_Ioc.mp hp).1
    obtain ⟨hmI, hmfrac⟩ := mem_filter.mp hm
    refine ⟨mem_Ioc.mpr ⟨Nat.mul_pos (mem_Ioc.mp hmI).1 hp0,
      (Nat.mul_le_mul_right p (mem_Ioc.mp hmI).2).trans (Nat.div_mul_le_self N p)⟩,
      p, (mem_Ioc.mp hp).1, dvd_mul_left _ _, ?_⟩
    exact (floor_common_divisor_iff hα hp0).mpr hmfrac

lemma commonDivisorSet_card_le_rows {α : ℝ} (hα : 0 ≤ α) (N V : ℕ) :
    ((commonDivisorSet α N V).card : ℝ) ≤
      ∑ p ∈ Ioc V N, ((diagonalRows α N p).card : ℝ) := by
  classical
  rw [commonDivisorSet_eq_union hα]
  have hh := (card_biUnion_le (s := Ioc V N)
    (t := fun p => (diagonalRows α N p).image (fun m => m*p))).trans
      (sum_le_sum (fun p _ => card_image_le))
  exact_mod_cast hh

theorem commonDivisorSet_card_bound {α : ℝ} {a q N V : ℕ}
    (hα : 0 ≤ α) (hq : 0 < q) (haq : a.Coprime q)
    (happrox : |α-(a : ℝ)/q| * N ≤ 1) (hN : N ≤ q^2) (hV : 0 < V) :
    ((commonDivisorSet α N V).card : ℝ) ≤
      10*N/(V : ℝ)+(2*N/(q : ℝ)+5*q)*(1+Real.log (2*q : ℕ))+2*q :=
  (commonDivisorSet_card_le_rows hα N V).trans
    (diagonal_count_bound hα hq haq happrox hN hV)

#print axioms floor_common_divisor_iff
#print axioms commonDivisorSet_card_bound
end Erdos972SparseCommonDivisorSupport
