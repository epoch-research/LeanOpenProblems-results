import Submission.GraphBlockGeometryExplore
import Submission.LogTuningExplore

/-! Uniformly negligible mixed counts for growing old prefixes that fit
within a new row, under the existing logarithmic thickness tuning. -/
namespace Erdos66GraphPrefixLimit
open Filter AdditiveCombinatorics Erdos66GraphBlockGeometry Erdos66GraphRowGeometry
  Erdos66IntegerBlock Erdos66CyclicThickening Erdos66LogTuning
open scoped Classical Topology
set_option maxHeartbeats 1200000

lemma normalized_graph_prefix_bound (p K : ℕ) [NeZero p] [NeZero K] (hp : 2 ≤ p)
    (B : ℕ → Finset (ZMod p×ZMod p)) (H : ℕ)
    (hB : ∀ q s, rowCount (B q) s ≤ H)
    (A : Finset ℕ) (L n : ℕ) (hA : ∀ a∈A, a<L) (hL : L ≤ p*K)
    (hd : Disjoint (A : Set ℕ) (blockSet ((p*K)^2) (fun k ↦ thickenedSet p K (B k))))
    (hn : (p*K)^2 ≤ n) :
    let C := blockSet ((p*K)^2) (fun k ↦ thickenedSet p K (B k))
    |(sumRep ((A : Set ℕ)∪C) n : ℝ)/Real.log n-(sumRep C n : ℝ)/Real.log n| ≤
      4*(K : ℝ)*H/Real.log p := by
  have hK : 1 ≤ K := NeZero.pos K
  have hb : p ≤ p*K := by nlinarith
  have hbn : p*K ≤ n := by nlinarith
  have h2L : 2*L ≤ n := by nlinarith
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hlogs : Real.log (p : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast (show 0<p by omega)) (by exact_mod_cast hb.trans hbn)
  have hh := thickened_block_prefix_bound p K B H hB A L n hA hL hd h2L
  dsimp only at hh ⊢
  let C := blockSet ((p*K)^2) (fun k ↦ thickenedSet p K (B k))
  change sumRep C n ≤ sumRep ((A : Set ℕ)∪C) n ∧
    sumRep ((A : Set ℕ)∪C) n ≤ sumRep C n+4*K*H at hh
  have hlo : 0 ≤ (sumRep ((A : Set ℕ)∪C) n : ℝ)-sumRep C n := by
    have hm : (sumRep C n : ℝ) ≤ sumRep ((A : Set ℕ)∪C) n := by exact_mod_cast hh.1
    linarith
  have hhi : (sumRep ((A : Set ℕ)∪C) n : ℝ)-sumRep C n ≤ 4*(K : ℝ)*H := by
    have hm : (sumRep ((A : Set ℕ)∪C) n : ℝ) ≤ sumRep C n+4*(K : ℝ)*H := by
      exact_mod_cast hh.2
    linarith
  change |(sumRep ((A : Set ℕ)∪C) n : ℝ)/Real.log n-(sumRep C n : ℝ)/Real.log n| ≤ _
  rw [← sub_div,abs_div,abs_of_pos hlogn,abs_of_nonneg hlo]
  exact (div_le_div_of_nonneg_right hhi hlogn.le).trans
    (div_le_div_of_nonneg_left (by positivity) hlogp hlogs)

/-- The stage threshold is uniform over the old finite set, the new plane
family, and EVERY target above the new period. In particular, the old set
may grow with the prime; its length need only be at most p*K. -/
theorem tuned_short_prefix_negligible (d : ℝ) (hd : 0<d) (H : ℕ)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ p : ℕ in atTop, ∃ hp : NeZero p, ∃ hK : NeZero (thickness d p),
      letI := hp
      letI := hK
      ∀ B : ℕ → Finset (ZMod p×ZMod p),
        (∀ q s, rowCount (B q) s ≤ H) →
        ∀ A : Finset ℕ, ∀ L : ℕ, (∀ a∈A, a<L) → L ≤ p*thickness d p →
        Disjoint (A : Set ℕ)
          (blockSet ((p*thickness d p)^2) (fun k ↦ thickenedSet p (thickness d p) (B k))) →
        ∀ n : ℕ, (p*thickness d p)^2 ≤ n →
          let C := blockSet ((p*thickness d p)^2) (fun k ↦ thickenedSet p (thickness d p) (B k))
          |(sumRep ((A : Set ℕ)∪C) n : ℝ)/Real.log n-(sumRep C n : ℝ)/Real.log n| < ε := by
  have hlim := (thickness_log_ratio hd).const_mul (4*(H : ℝ))
  simp only [mul_zero] at hlim
  filter_upwards [eventually_ge_atTop 2,
    (thickness_atTop hd).eventually_ge_atTop 1,hlim.eventually_lt_const hε] with p hp hK hsmall
  letI hp' : NeZero p := ⟨by omega⟩
  letI hK' : NeZero (thickness d p) := ⟨by omega⟩
  refine ⟨hp',hK',?_⟩
  intro B hB A L hA hL hdis n hn
  have hh := normalized_graph_prefix_bound p (thickness d p) hp B H hB A L n hA hL hdis hn
  apply hh.trans_lt
  convert hsmall using 1 <;> ring

end Erdos66GraphPrefixLimit
