import Submission.SeparatedBracketMovesExplore

/-! Distinct cumulative-rank cells give separated admissible moves. Thus an
arbitrary finite family of omitted points in distinct cells can be inserted
while preserving all original brackets, with exactly as many deletions. -/
namespace Erdos66RankCellExchange
open Erdos66Counting Erdos66Generating Erdos66ClampedPrefixContinuation
  Erdos66BracketOrderedExchange Erdos66OrderedPartialReplacement
  Erdos66BracketRankMove Erdos66SeparatedBracketMoves
open scoped Classical
set_option maxHeartbeats 2400000

lemma rankPoint_mass_bounds (p : ℕ → ℝ) (A : Set ℕ)
    (hbr : ∀ L, PrefixBrackets p A L) (hunb : ∀ j, ∃ N, j<count A N) (j : ℕ) :
    mass p (rankPoint A hunb j)<(j : ℝ)+1 ∧
      (j : ℝ)< mass p (rankPoint A hunb j+1) := by
  let d := rankPoint A hunb j
  have hd := rankPoint_mem A hunb j
  have hc := rankPoint_count A hunb j
  have hb := hbr d d le_rfl
  have hs := hbr (d+1) (d+1) le_rfl
  simp only [mass_indicator_eq_count] at hb hs
  have hcd : count A d=j := hc
  rw [hcd] at hb
  rw [count_succ,if_pos hd,hcd] at hs
  have hfloor : ⌊mass p d⌋ ≤ (j : ℤ) := by exact_mod_cast hb.1
  have hceil : (j : ℤ)+1 ≤ ⌈mass p (d+1)⌉ := by exact_mod_cast hs.2
  constructor
  · have hh := Int.floor_lt.mp (show ⌊mass p d⌋ < (j : ℤ)+1 by omega)
    simpa only [Int.cast_add,Int.cast_natCast,Int.cast_one] using hh
  · have hh := Int.lt_ceil.mp (show (j : ℤ)<⌈mass p (d+1)⌉ by omega)
    simpa only [Int.cast_natCast] using hh

noncomputable def cell (p : ℕ → ℝ) (f : ℕ) : ℕ := ⌊mass p f⌋₊

lemma cell_mono (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) : Monotone (cell p) :=
  fun _ _ h ↦ Nat.floor_mono (mass_mono hp h)

lemma cell_lower (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (f : ℕ) :
    (cell p f : ℝ) ≤ mass p f := Nat.floor_le (Finset.sum_nonneg (fun i _ ↦ hp i))

lemma cell_upper (p : ℕ → ℝ) (f : ℕ) : mass p f<(cell p f : ℝ)+1 := Nat.lt_floor_add_one _

/-- Not just the new points but both endpoints of each move respect the
strict order of their cumulative-rank cells. -/
theorem cell_moves_separated (p : ℕ → ℝ) (A : Set ℕ)
    (hp : ∀ k, 0 ≤ p k) (hbr : ∀ L, PrefixBrackets p A L)
    (hunb : ∀ j, ∃ N, j<count A N) (f g : ℕ) (hf : f∉A)
    (hfg : cell p f<cell p g) :
    max (rankPoint A hunb (cell p f)) f < min (rankPoint A hunb (cell p g)) g := by
  let j := cell p f
  let k := cell p g
  have hjk : j<k := hfg
  have hreal : (j : ℝ)+1 ≤ k := by exact_mod_cast (show j+1 ≤ k by omega)
  have hd := (rankPoint_mass_bounds p A hbr hunb j).1
  have he := (rankPoint_mass_bounds p A hbr hunb k).2
  have hfm : mass p f<(j : ℝ)+1 := cell_upper p f
  have hgm : (k : ℝ) ≤ mass p g := cell_lower p hp g
  have hde : rankPoint A hunb j<rankPoint A hunb k := rankPoint_strictMono A hunb hjk
  have hfg' : f<g := by
    by_contra hn
    have hh := cell_mono p hp (show g ≤ f by omega)
    omega
  have hdg : rankPoint A hunb j<g := by
    by_contra hn
    have hh := mass_mono hp (show g ≤ rankPoint A hunb j by omega)
    linarith
  have hfe : f<rankPoint A hunb k := by
    by_contra hn
    have hne : rankPoint A hunb k≠f := fun hh ↦ hf (hh ▸ rankPoint_mem A hunb k)
    have hh := mass_mono hp (show rankPoint A hunb k+1 ≤ f by omega)
    linarith
  exact max_lt_iff.mpr ⟨lt_min hde hdg,lt_min hfe hfg'⟩

/-- A finite selection with no repeated rank cell preserves all brackets.
There is no stagewise addition to the prefix-discrepancy allowance. -/
theorem rank_family_brackets {ι : Type*} [Fintype ι]
    (p : ℕ → ℝ) (A : Set ℕ) (hp : ∀ k, 0 ≤ p k)
    (hbr : ∀ L, PrefixBrackets p A L) (hunb : ∀ j, ∃ N, j<count A N)
    (f : ι → ℕ) (hf : ∀ i, f i∉A) (hpf : ∀ i, 0<p (f i))
    (hcell : Function.Injective (fun i ↦ cell p (f i))) :
    ∀ L, PrefixBrackets p
      (swap A (Finset.univ.image (fun i ↦ rankPoint A hunb (cell p (f i))))
        (Finset.univ.image f)) L := by
  let d : ι → ℕ := fun i ↦ rankPoint A hunb (cell p (f i))
  have hd : Function.Injective d := (rankPoint_strictMono A hunb).injective.comp hcell
  have hfinj : Function.Injective f := by
    intro i j he
    exact hcell (congrArg (cell p) he)
  apply family_brackets p A d f hd hfinj (fun i ↦ rankPoint_mem A hunb _) hf hbr
  · intro i L
    exact (omitted_point_admits_rank_move p A hp hbr hunb (f i) (hf i) (hpf i)).2.2 L
  · intro N i j hi hj
    by_contra hij
    have hneq : cell p (f i)≠cell p (f j) := fun he ↦ hij (hcell he)
    have hloc1 := delta_ne_zero_location (d i) (f i) N hi
    have hloc2 := delta_ne_zero_location (d j) (f j) N hj
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · have hs := cell_moves_separated p A hp hbr hunb (f i) (f j) (hf i) hlt
      change max (d i) (f i)< min (d j) (f j) at hs
      omega
    · have hs := cell_moves_separated p A hp hbr hunb (f j) (f i) (hf j) hgt
      change max (d j) (f j)< min (d i) (f i) at hs
      omega

end Erdos66RankCellExchange
