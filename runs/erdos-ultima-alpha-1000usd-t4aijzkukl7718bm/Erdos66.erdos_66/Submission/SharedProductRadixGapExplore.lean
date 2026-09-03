import Submission.AnchoredProductRepairExplore
import Submission.CarryExplore
import Submission.Explore

/-! The literal lexicographic mixed-radix lift of shared parabolas has a
large initial gap. Exact group-slice compatibility therefore does not give
compatible integer prefixes. These are obstructions to this construction,
not to the existential conjecture. -/
namespace Erdos66SharedProductRadixGap
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66SharedParameterSet
  Erdos66AnchoredProductRepair Erdos66Carry Erdos66Explore
  AdditiveCombinatorics Filter
open scoped Topology Classical
set_option maxHeartbeats 700000

section GeneralEncoding
variable {G : Type*} {q : ℕ} [NeZero q]

/-- Old coordinates are the least-significant block; the new field plane
occupies the two following radix-q positions. -/
def extensionCode (M : ℕ) (e : G → ℕ) (z : G × (ZMod q × ZMod q)) : ℕ :=
  e z.1+M*digitEncode q z.2

lemma extensionCode_gap (M : ℕ) (hM : 0<M) (e : G → ℕ) (he : ∀ x, e x<M)
    (S : Finset (G × (ZMod q × ZMod q)))
    (hzero : ∀ z∈S, z.2.2=0 → z.2=0)
    (z : G × (ZMod q × ZMod q)) (hz : z∈S) (hlt : extensionCode M e z<M*q) :
    extensionCode M e z<M := by
  have hyval : z.2.2.val=0 := by
    by_contra hn
    have hpos : 1≤z.2.2.val := by omega
    have hqy : q≤q*z.2.2.val := by simpa using Nat.mul_le_mul_left q hpos
    have hqcode : q≤digitEncode q z.2 := hqy.trans (Nat.le_add_left _ _)
    have hh := Nat.mul_le_mul_left M hqcode
    dsimp only [extensionCode] at hlt
    omega
  have hy : z.2.2=0 := (ZMod.val_eq_zero _).mp hyval
  have hz0 := hzero z hz hy
  simpa only [extensionCode,hz0,digitEncode,Prod.fst_zero,Prod.snd_zero,ZMod.val_zero,
    mul_zero,add_zero] using he z.1

lemma encoded_prefix_gap (M : ℕ) (hM : 0<M) (e : G → ℕ) (he : ∀ x, e x<M)
    (S : Finset (G × (ZMod q × ZMod q)))
    (hzero : ∀ z∈S, z.2.2=0 → z.2=0) :
    ∀ a∈S.image (extensionCode M e), a<M*q → a<M := by
  intro a ha hlt
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
  exact extensionCode_gap M hM e he S hzero z hz hlt

end GeneralEncoding

lemma sumRep_eq_zero_of_prefix_gap (A : Set ℕ) (M L : ℕ)
    (hgap : ∀ a∈A, a<L → a<M) (n : ℕ) (hn : 2*M≤n) (hnL : n<L) :
    sumRep A n=0 := by
  rw [sumRep_def,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro ab hab hm
  have hs := Finset.mem_antidiagonal.mp hab
  have ha := hgap ab.1 hm.1 (by omega)
  have hb := hgap ab.2 hm.2 (by omega)
  omega

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {q : ℕ} [Fact q.Prime]

lemma anchored_horizontal_zero (h : ℕ) (u : ℕ → F) (v : ℕ → ZMod q)
    (hv : ∀ i<h, v i ≠ 0) (D : Finset (F × F))
    (z : (F × F) × (ZMod q × ZMod q)) (hz : z∈anchoredSet h u v D)
    (hy : z.2.2=0) : z.2=0 := by
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨i,hi,hzi⟩ := Finset.mem_biUnion.mp hz
    have hcurve := (mem_curve (v i) z.2).mp (Finset.mem_product.mp hzi).2
    have hsq : z.2.1^2=0 := ((div_eq_zero_iff).mp (hcurve.symm.trans hy)).resolve_right
      (hv i (Finset.mem_range.mp hi))
    exact Prod.ext (eq_zero_of_pow_eq_zero hsq) hy
  · exact ((anchored_mem D z).mp hz).2

/-- This is an actual zero representation count on a whole initial interval,
not just a loss in the finite-field error estimate. -/
theorem anchored_encoding_hole (h : ℕ) (u : ℕ → F) (v : ℕ → ZMod q)
    (hv : ∀ i<h, v i ≠ 0) (D : Finset (F × F))
    (M : ℕ) (hM : 0<M) (e : F × F → ℕ) (he : ∀ x, e x<M)
    (n : ℕ) (hn : 2*M≤n) (hnq : n<M*q) :
    sumRep (((anchoredSet h u v D).image (extensionCode M e) : Finset ℕ) : Set ℕ) n=0 := by
  apply sumRep_eq_zero_of_prefix_gap _ M (M*q) _ n hn hnq
  exact encoded_prefix_gap M hM e he _ (anchored_horizontal_zero h u v hv D)

/-- Repeated literal encodings with unbounded old-block lengths force
infinitely many holes, ruling out every nonzero normalized limit for that
construction. The hypotheses are not asserted for arbitrary sets. -/
theorem prefix_gaps_exclude_nonzero_limit (A : Set ℕ) (M q : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) (hq : ∀ k, 3≤q k)
    (hgap : ∀ k a, a∈A → a<M k*q k → a<M k) (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro h
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((sumRep_tendsto_atTop hc h).eventually_ge_atTop 1)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hM.eventually_ge_atTop (max N 1))
  have hMK : max N 1≤M K := hK K le_rfl
  have hMK0 : 0<M K := by omega
  have hqK := hq K
  have hlt : 2*M K<M K*q K := by nlinarith
  have hz := sumRep_eq_zero_of_prefix_gap A (M K) (M K*q K) (hgap K) (2*M K) le_rfl hlt
  have hp := hN (2*M K) (by omega)
  omega

end Erdos66SharedProductRadixGap
