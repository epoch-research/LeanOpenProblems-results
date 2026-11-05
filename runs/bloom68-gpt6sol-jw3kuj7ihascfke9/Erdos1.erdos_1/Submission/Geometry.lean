import Submission.Common
import Submission.GeometrySchedule

/-! Rational lattices in arbitrarily high dimension with positive, arbitrarily
small covolume and no nonzero integer-input point in the open cube and slab. -/

namespace Erdos1Aux

/-- An escape triple excludes integer vectors in the intersection of the cube
and the height slab, irrespective of its finite indexing type. -/
theorem EscapeTriple.cubeSlab {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : EscapeTriple ι) (z : ι → ℤ)
    (hc : ∀ i, |T.B.mulVec (fun j => (z j : ℚ)) i| < 1)
    (hs : |∑ i, T.B.mulVec (fun j => (z j : ℚ)) i| < 1) : z = 0 := by
  have hzq : |(z T.ht : ℚ)| < 1 := by simpa only [T.height] using hs
  have hupper : z T.ht < 1 := by exact_mod_cast (abs_lt.mp hzq).2
  have hlower : -(1 : ℤ) < z T.ht := by exact_mod_cast (abs_lt.mp hzq).1
  exact T.cube z (by omega) hc

/-- The rational escape invariant also holds for *real* height coefficients.
The forbidden open cube is stable under a small change of coefficient; a
hypothetical real counterexample therefore gives a rational counterexample
on the same side of either escape threshold. -/
theorem EscapeTriple.realEscape {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : EscapeTriple ι) (z : ι → ℤ) (a : ℝ)
    (hz : z T.ht = 0) (ha : (T.H : ℝ) ≤ |a|) :
    ¬ ∀ i : ι,
      |((T.B.mulVec (fun j => (z j : ℚ)) i : ℚ) : ℝ) +
        a * ((T.B.col T.ht i : ℚ) : ℝ)| < 1 := by
  intro hshort
  let v : ι → ℚ := T.B.mulVec (fun j => (z j : ℚ))
  let w : ι → ℚ := T.B.col T.ht
  let U : Set ℝ := ⋂ i : ι, {b : ℝ | |(v i : ℝ) + b * (w i : ℝ)| < 1}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt (by fun_prop) (by fun_prop)
  have haU : a ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
    exact hshort
  obtain ⟨l, u, ⟨hla, hau⟩, hinterval⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds haU)
  have hrat (q : ℚ) (hq : (q : ℝ) ∈ U) :
      ∀ i, |T.B.mulVec (fun j => (z j : ℚ)) i + q * T.B.col T.ht i| < 1 := by
    intro i
    have hreal : |(v i : ℝ) + (q : ℝ) * (w i : ℝ)| < 1 :=
      (Set.mem_iInter.mp hq) i
    have hq' : |v i + q * w i| < 1 := by exact_mod_cast hreal
    exact hq'
  rcases le_total 0 a with hnonneg | hnonpos
  · have hpositive : (T.H : ℝ) ≤ a := by
      simpa only [abs_of_nonneg hnonneg] using ha
    obtain ⟨q, hqa, hqu⟩ := exists_rat_btwn hau
    have hqH : (T.H : ℝ) ≤ (q : ℝ) := hpositive.trans hqa.le
    have hqpos : 0 ≤ (q : ℝ) :=
      (by exact_mod_cast T.Hpos.le : (0 : ℝ) ≤ (T.H : ℝ)).trans hqH
    have hqAbs : T.H ≤ |q| := by
      have hcast : (T.H : ℝ) ≤ |(q : ℝ)| := by
        simpa only [abs_of_nonneg hqpos] using hqH
      exact_mod_cast hcast
    exact T.escape z q hz hqAbs (hrat q (hinterval ⟨hla.trans hqa, hqu⟩))
  · have hnegative : a ≤ -(T.H : ℝ) := by
      rw [abs_of_nonpos hnonpos] at ha
      linarith
    obtain ⟨q, hql, hqa⟩ := exists_rat_btwn hla
    have hqH : (q : ℝ) ≤ -(T.H : ℝ) := hqa.le.trans hnegative
    have hqneg : (q : ℝ) ≤ 0 := by
      have hH : (0 : ℝ) ≤ (T.H : ℝ) := by exact_mod_cast T.Hpos.le
      linarith
    have hqAbs : T.H ≤ |q| := by
      have hcast : (T.H : ℝ) ≤ |(q : ℝ)| := by
        rw [abs_of_nonpos hqneg]
        linarith
      exact_mod_cast hcast
    exact T.escape z q hz hqAbs (hrat q (hinterval ⟨hql, hqa.trans hau⟩))

/-- Reindexing an escape triple by a common row and column permutation
preserves its cube-and-slab condition. -/
theorem EscapeTriple.reindex_cubeSlab {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : EscapeTriple ι) (e : ι ≃ κ) (z : κ → ℤ)
    (hc : ∀ j, |(Matrix.reindex e e T.B).mulVec (fun q => (z q : ℚ)) j| < 1)
    (hs : |∑ j, (Matrix.reindex e e T.B).mulVec (fun q => (z q : ℚ)) j| < 1) :
    z = 0 := by
  let z' : ι → ℤ := fun i => z (e i)
  have hmul : (Matrix.reindex e e T.B).mulVec (fun q => (z q : ℚ)) =
      (T.B.mulVec (fun i => (z' i : ℚ))) ∘ e.symm := by
    simpa only [Matrix.reindex_apply, z', Function.comp_apply] using
      (Matrix.submatrix_mulVec_equiv T.B (fun q : κ => (z q : ℚ)) e.symm e.symm)
  have hc' : ∀ i, |T.B.mulVec (fun q => (z' q : ℚ)) i| < 1 := by
    intro i
    have h := hc (e i)
    rw [hmul] at h
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h
  have hsum : (∑ j : κ, (Matrix.reindex e e T.B).mulVec (fun q => (z q : ℚ)) j) =
      ∑ i : ι, T.B.mulVec (fun q => (z' q : ℚ)) i := by
    rw [hmul]
    exact e.symm.sum_comp _
  rw [hsum] at hs
  have hzero := T.cubeSlab z' hc' hs
  funext j
  have h := congrFun hzero (e.symm j)
  simpa only [z', Equiv.apply_symm_apply, Pi.zero_apply] using h

/-- Positive rational covolume can be made arbitrarily small without admitting
any nonzero lattice point in the open cube-and-slab region. -/
theorem exists_small_admissible (ε : ℚ) (hε : 0 < ε) :
    ∃ d : ℕ, 0 < d ∧ ∃ B : Matrix (Fin d) (Fin d) ℚ,
      0 < B.det ∧ B.det < ε ∧ CubeSlabAdmissible B := by
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one
    (x := ε / 2) (y := (1 / 2 : ℚ)) (by positivity) (by norm_num)
  have hpowpos : (0 : ℚ) < (2 : ℚ) ^ r := by positivity
  have hpow : (2 : ℚ) < ε * (2 : ℚ) ^ r := by
    have hpowinv : (1 / 2 : ℚ) ^ r = 1 / (2 : ℚ) ^ r := by
      rw [one_div, inv_pow, one_div]
    rw [hpowinv] at hr
    have hh := (div_lt_iff₀ hpowpos).mp hr
    nlinarith
  obtain ⟨ι, F, E, T, hthreshold, hcost⟩ := exists_escape_triple r 1 (by norm_num)
  letI : Fintype ι := F
  letI : DecidableEq ι := E
  let d : ℕ := Fintype.card ι
  let e : ι ≃ Fin d := Fintype.equivFin ι
  let B : Matrix (Fin d) (Fin d) ℚ := Matrix.reindex e e T.B
  refine ⟨d, Fintype.card_pos_iff.mpr ⟨T.ht⟩, B, ?_, ?_, ?_⟩
  · simpa only [B, Matrix.det_reindex_self] using T.detpos
  · have hεH : (2 : ℚ) < ε * T.H :=
      hpow.trans_le (mul_le_mul_of_nonneg_left hthreshold hε.le)
    have hsmall : T.B.det < ε := by
      apply lt_of_mul_lt_mul_left (a := T.H) (b := T.B.det) (c := ε) _ T.Hpos.le
      calc
        T.H * T.B.det < 2 := by norm_num at hcost ⊢; exact hcost
        _ < ε * T.H := hεH
        _ = T.H * ε := mul_comm _ _
    simpa only [B, Matrix.det_reindex_self] using hsmall
  · intro z hc hs
    exact T.reindex_cubeSlab e z hc hs

end Erdos1Aux
