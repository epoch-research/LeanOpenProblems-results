import Submission.PacketMatchingExplore

/-! Uniform matching-potential bounds depend only on the sum of reciprocal
square roots of coordinate sizes, not on a fourth power of their indices. -/
namespace Erdos66PacketMatchingMass
open Erdos66MultiPacket Erdos66MultiPacketSelection Erdos66PacketMatching
  Erdos66MatchingPartition Erdos66HeterogeneousSelection Erdos66UniformSelection
open scoped Classical
set_option maxHeartbeats 1400000

lemma reciprocal_geometric_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    1/b ≤ (1/Real.sqrt a)*(1/Real.sqrt b) := by
  have hprod : Real.sqrt a * Real.sqrt b ≤ b := by
    have hh := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hab) (Real.sqrt_nonneg b)
    nlinarith [Real.sq_sqrt hb.le]
  have hpos : 0 < Real.sqrt a * Real.sqrt b := mul_pos (Real.sqrt_pos.2 ha) (Real.sqrt_pos.2 hb)
  simpa only [one_div_mul_one_div] using one_div_le_one_div_of_le hpos hprod

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def sqrtMass (q : ι → ℕ) : ℝ := ∑ i, 1 / Real.sqrt (q i)
noncomputable def edgeWeight (q : ι → ℕ) (p : Edge ι) : ℝ :=
  (1/Real.sqrt (q p.1.1))*(1/Real.sqrt (q p.2.1))

def payer (q : ι → ℕ) (p : Edge ι) : ι := if q p.1.1 ≤ q p.2.1 then p.2.1 else p.1.1

lemma payer_mem (q : ι → ℕ) (p : Edge ι) : payer q p = p.1.1 ∨ payer q p = p.2.1 := by
  unfold payer
  split_ifs <;> simp

lemma payer_cost_le (q : ι → ℕ) (hq : ∀ i, 0 < q i) (p : Edge ι) :
    1/(q (payer q p) : ℝ) ≤ edgeWeight q p := by
  have ha : (0:ℝ) < q p.1.1 := by exact_mod_cast hq p.1.1
  have hb : (0:ℝ) < q p.2.1 := by exact_mod_cast hq p.2.1
  unfold payer edgeWeight
  split_ifs with hh
  · exact reciprocal_geometric_bound _ _ ha hb (by exact_mod_cast hh)
  · simpa only [mul_comm] using reciprocal_geometric_bound _ _ hb ha
      (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hh)))

lemma edgeWeight_nonneg (q : ι → ℕ) (p : Edge ι) : 0 ≤ edgeWeight q p := by
  unfold edgeWeight; positivity

lemma edgeWeight_sum (q : ι → ℕ) : (∑ p : Edge ι, edgeWeight q p) = 4*(sqrtMass q)^2 := by
  simp only [edgeWeight,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_bool,
    nsmul_eq_mul,Nat.cast_ofNat,← Finset.mul_sum,← Finset.sum_mul,sqrtMass]
  ring

lemma edgeWeight_sum_le (q : ι → ℕ) (S : Finset (Edge ι)) :
    (∑ p ∈ S, edgeWeight q p) ≤ 4*(sqrtMass q)^2 := by
  rw [← edgeWeight_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _ ↦ edgeWeight_nonneg q p)

lemma payer_cost_sum_le (q : ι → ℕ) (hq : ∀ i, 0 < q i) (S : Finset (Edge ι)) :
    (∑ p ∈ S, 1/(q (payer q p) : ℝ)) ≤ 4*(sqrtMass q)^2 := by
  exact (Finset.sum_le_sum (fun p _ ↦ payer_cost_le q hq p)).trans (edgeWeight_sum_le q S)

variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, DecidableEq (α i)]

lemma mean_sumIndicator_le (n : ι → ℤ) (x : ∀ i, α i → ℤ)
    (hx : ∀ i, Function.Injective (x i)) (z : ℤ) (p : Edge ι) (hp : p ∈ sumEvents) :
    mean (sumIndicator n x z p) ≤ edgeWeight (fun i ↦ Fintype.card (α i)) p := by
  let q := fun i ↦ Fintype.card (α i)
  have hf : mean (sumIndicator n x z p) ≤ 1/(q (payer q p) : ℝ) := by
    apply Erdos66HeterogeneousSelection.one_fiber_indicator_bound _ (payer q p)
    intro ω a b ha hb
    have hh := sum_fiber n p.1 p.2 (Finset.mem_filter.mp hp).2 z
      (payer q p) (payer_mem q p) (chosen x ω) (x (payer q p) a) (x (payer q p) b)
    rw [chosen_update] at ha hb
    exact hx _ (hh ha hb)
  exact hf.trans (payer_cost_le q (fun i ↦ Fintype.card_pos) p)

noncomputable def offTest (n : ι → ℤ) (x : ∀ i, α i → ℤ) (z : ℤ)
    (t : ℝ) (ω : ∀ i, α i) : ℝ :=
  if Function.Injective (point n (chosen x ω)) then Real.exp (t*(offPairs n x z ω).card) else 0

lemma offTest_nonneg (n : ι → ℤ) (x : ∀ i, α i → ℤ) (z : ℤ) (t : ℝ) (ω : ∀ i, α i) :
    0 ≤ offTest n x z t ω := by unfold offTest; split_ifs <;> positivity

/-- A uniform MGF bound for the unintended pair count, restricted to
injective point choices. Its exponent is independent of the number of
packets whenever their reciprocal-square-root mass is bounded. -/
theorem mean_offTest_le (n : ι → ℤ) (x : ∀ i, α i → ℤ)
    (hx : ∀ i, Function.Injective (x i)) (z : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    mean (offTest n x z t) ≤
      Real.exp ((Real.exp (8*t)-1)*4*(sqrtMass (fun i ↦ Fintype.card (α i)))^2) := by
  have h8 : 0 ≤ 8*t := by positivity
  have hm := mean_partition_le sumEvents support (sumIndicator n x z) (8*t) h8
    (edgeWeight (fun i ↦ Fintype.card (α i)))
    (fun p _ ω ↦ sumIndicator_nonneg n x z p ω)
    (fun p _ ↦ sumIndicator_depends n x z p)
    (fun p hp ↦ mean_sumIndicator_le n x hx z p hp)
  have hb : mean (offTest n x z t) ≤ mean (partition sumEvents support (sumIndicator n x z) (8*t)) := by
    apply mean_mono
    intro ω
    unfold offTest
    split_ifs with hinj
    · exact offPairs_exp_le n x z ω hinj t ht
    · exact partition_nonneg sumEvents support (sumIndicator n x z) (8*t) h8
        (fun p _ ω ↦ sumIndicator_nonneg n x z p ω) ω
  apply (hb.trans hm).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left
    (edgeWeight_sum_le (fun i ↦ Fintype.card (α i)) sumEvents)
    (sub_nonneg.mpr (Real.one_le_exp h8))
  nlinarith

end Erdos66PacketMatchingMass
