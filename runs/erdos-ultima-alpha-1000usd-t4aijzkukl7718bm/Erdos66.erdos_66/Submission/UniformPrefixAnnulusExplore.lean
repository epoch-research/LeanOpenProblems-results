import Submission.RowControlledAnnulusExplore
import Submission.UpperExtensionExplore

/-! A single finite annular template extends every upper-bounded prefix
shorter than its row width. No lower bound is asserted in the support gap. -/
namespace Erdos66UniformPrefixAnnulus
open Filter AdditiveCombinatorics Erdos66RowControlledAnnulus Erdos66RowSparsePrefix
  Erdos66Explore Erdos66Compactness
open scoped Topology Classical
set_option maxHeartbeats 1200000

/-- The new set is selected before the old prefix. The old prefix may have
arbitrarily many points below `b`, provided its global upper bound holds. -/
theorem exists_uniform_prefix_annulus (c ε : ℝ) (hc : 0<c) (hε : 0<ε)
    (R N₀ : ℕ) (hR : 1≤R) :
    ∃ b N : ℕ, 2≤b ∧ N₀≤b ∧ b^2≤N ∧ ∃ D : Set ℕ,
      D.Finite ∧ D ⊆ Set.Ici (b^2) ∧
      ∀ A : Finset ℕ, (∀ a∈A, a<b) →
        (∀ n : ℕ, (sumRep (A : Set ℕ) n : ℝ)/Real.log n ≤ c) →
        (∀ x<b^2, x∈(A : Set ℕ)∪D ↔ x∈A) ∧
        (∀ n : ℕ, (sumRep ((A : Set ℕ)∪D) n : ℝ)/Real.log n ≤ c) ∧
        ∀ n : ℕ, N≤n → n≤R*N →
          |(sumRep ((A : Set ℕ)∪D) n : ℝ)/Real.log n-c|<ε := by
  let η : ℝ := min (ε/8) (c/8)
  have hη : 0<η := lt_min (by positivity) (by positivity)
  have hηε : η≤ε/8 := min_le_left _ _
  have hηc : η≤c/8 := min_le_right _ _
  have hbase : 0<c-4*η := by linarith
  obtain ⟨N, hN₀, hN, b, H, hb, hbN₀, hbN, D, hDfin, hDsupp, hrows, hcost, hDup, hDgood⟩ :=
    exists_row_controlled_annulus (c-4*η) η hbase hη R N₀ hR
  refine ⟨b,N,hb,hbN₀,hbN,D,hDfin,hDsupp,?_⟩
  intro A hA hupper
  have heq (x : ℕ) (hx : x<b^2) : x∈(A : Set ℕ)∪D ↔ x∈A := by
    have hnot : x∉D := by intro hd; have hh := hDsupp hd; change b^2≤x at hh; omega
    simp [hnot]
  have hrep (n : ℕ) (hn : n<b^2) : sumRep ((A : Set ℕ)∪D) n=sumRep (A : Set ℕ) n := by
    apply sumRep_congr_below
    intro x hx
    exact heq x (by omega)
  have hdis : Disjoint (A : Set ℕ) D := by
    apply Set.disjoint_left.mpr
    intro x hx hxd
    have hxA := hA x hx
    have hxD := hDsupp hxd
    change b^2≤x at hxD
    nlinarith
  have hlogb : 0<Real.log ((b^2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<b^2 by nlinarith))
  have herr (n : ℕ) (hn : b^2≤n) :
      0≤(sumRep ((A : Set ℕ)∪D) n : ℝ)/Real.log n-(sumRep D n : ℝ)/Real.log n ∧
      (sumRep ((A : Set ℕ)∪D) n : ℝ)/Real.log n-(sumRep D n : ℝ)/Real.log n<η := by
    have hh := union_short_prefix_bound A D b b H n hA hdis (by omega) le_rfl hrows
      (by nlinarith)
    have hlogcomp : Real.log ((b^2 : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0<b^2 by positivity)) (by exact_mod_cast hn)
    have hlogn : 0<Real.log (n : ℝ) := hlogb.trans_le hlogcomp
    have hlow : (sumRep D n : ℝ)≤sumRep ((A : Set ℕ)∪D) n := by exact_mod_cast hh.1
    have hhigh : (sumRep ((A : Set ℕ)∪D) n : ℝ)≤sumRep D n+4*(H : ℝ) := by
      exact_mod_cast hh.2
    constructor
    · exact sub_nonneg.mpr (div_le_div_of_nonneg_right hlow hlogn.le)
    · rw [← sub_div]
      apply (div_le_div_of_nonneg_right (show (sumRep ((A : Set ℕ)∪D) n : ℝ)-sumRep D n≤4*H by linarith) hlogn.le).trans_lt
      exact (div_le_div_of_nonneg_left (by positivity) hlogb hlogcomp).trans_lt hcost
  refine ⟨heq,?_,?_⟩
  · intro n
    by_cases hn : n<b^2
    · rw [hrep n hn]
      exact hupper n
    have hh := (herr n (by omega)).2
    have hd := hDup n
    linarith
  · intro n hnlo hnhi
    obtain ⟨hlo,hhi⟩ := herr n (by omega)
    have hd := hDgood n hnlo hnhi
    rw [abs_lt] at hd ⊢
    constructor <;> linarith

end Erdos66UniformPrefixAnnulus
