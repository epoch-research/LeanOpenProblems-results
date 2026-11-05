import Submission.GeometryShear

/-! Rational small-covolume escape triples built by successively shearing height directions. -/

namespace Erdos1Aux

open Filter
open scoped Topology

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The exact recurrence for the threshold times the determinant. -/
theorem shearEscapeTriple_cost (inner : EscapeTriple α) (outer : EscapeTriple β) :
    (shearEscapeTriple inner outer).H * (shearEscapeTriple inner outer).B.det =
      (outer.H * outer.B.det) *
        (inner.H * inner.B.det) ^ Fintype.card β := by
  have hk : 1 ≤ Fintype.card β := Fintype.card_pos_iff.mpr ⟨outer.ht⟩
  have heq : Fintype.card β - 1 + 1 = Fintype.card β := Nat.sub_add_cancel hk
  change (inner.H * outer.H) * (shearedTripleMatrix inner outer).det = _
  rw [shearedTripleMatrix_det]
  calc
    (inner.H * outer.H) *
        (inner.B.det ^ Fintype.card β *
          (outer.B.det * inner.H ^ (Fintype.card β - 1))) =
      (outer.H * outer.B.det) *
        ((inner.H ^ (Fintype.card β - 1) * inner.H) *
          inner.B.det ^ Fintype.card β) := by ring
    _ = (outer.H * outer.B.det) *
          (inner.H ^ Fintype.card β * inner.B.det ^ Fintype.card β) := by
      rw [← pow_succ, heq]
    _ = _ := by rw [mul_pow]

/-- The odd cycle can be chosen with escape threshold at least two, and with
    threshold times determinant arbitrarily close to one. The choice of `t`
    is rational and the number of rows is an odd integer. -/
theorem exists_odd_escape_cost (δ : ℚ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (t : ℚ), 0 < t ∧ t < 1 ∧
      2 < (1 + t) / t ∧
      ((1 + t) / t) * (oddBlock n t).det < 1 + δ := by
  let c : ℚ := 1 + δ / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hless : 1 / c < 1 := (div_lt_iff₀ hc).2 (by dsimp [c]; linarith)
  obtain ⟨t, htLower, htUpper⟩ := exists_between hless
  have ht : 0 < t := (div_pos zero_lt_one hc).trans htLower
  have hInv : 1 / t < c := by
    apply (div_lt_iff₀ ht).2
    have hh := (div_lt_iff₀ hc).1 htLower
    simpa only [mul_comm] using hh
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (x := δ * t / 2) (y := t) (by positivity) htUpper
  have hpow : t ^ (2 * N + 3) < δ * t / 2 :=
    (pow_le_pow_of_le_one ht.le htUpper.le (by omega)).trans_lt hN
  refine ⟨N, t, ht, htUpper, ?_, ?_⟩
  · exact (lt_div_iff₀ ht).2 (by linarith)
  · rw [oddBlock_det]
    have htOne : 1 + t ≠ 0 := ne_of_gt (by linarith)
    have hform : ((1 + t) / t) * ((1 + t ^ (2 * N + 3)) / (1 + t)) =
        (1 + t ^ (2 * N + 3)) / t := by
      field_simp
    rw [hform]
    apply (div_lt_iff₀ ht).2
    have h1 : 1 < (1 + δ / 2) * t := by simpa only [c] using (div_lt_iff₀ ht).1 hInv
    nlinarith

/-- There are rational numbers strictly above one whose given power is below
    any fixed rational bound above one. -/
private theorem exists_rational_pow_between (c : ℚ) (hc : 1 < c) (k : ℕ) :
    ∃ b : ℚ, 1 < b ∧ b ^ k < c := by
  have hp : (1 : ℚ) ^ k < c := by simpa using hc
  have hevent : {b : ℚ | b ^ k < c} ∈ 𝓝 (1 : ℚ) :=
    Filter.Tendsto.eventually_lt_const hp (continuousAt_pow (1 : ℚ) k)
  obtain ⟨l, u, ⟨hlo, hhi⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hevent
  obtain ⟨b, hb1, hbu⟩ := exists_between hhi
  exact ⟨b, hb1, hsub ⟨hlo.trans hb1, hbu⟩⟩

/-- Rational cost remains arbitrarily close to the optimal value one while
    the escape threshold grows by (at least) a factor of two per stage. -/
theorem exists_escape_triple (r : ℕ) (δ : ℚ) (hδ : 0 < δ) :
    ∃ (ι : Type) (F : Fintype ι) (E : DecidableEq ι),
      ∃ T : @EscapeTriple ι F E,
        (2 : ℚ) ^ r ≤ T.H ∧ T.H * T.B.det < 1 + δ := by
  induction r generalizing δ with
  | zero =>
      obtain ⟨n, t, ht, ht1, hH, hcost⟩ := exists_odd_escape_cost δ hδ
      refine ⟨Fin (2 * n + 3), inferInstance, inferInstance,
        oddEscapeTriple n t ht ht1, ?_, ?_⟩
      · change (1 : ℚ) ≤ (1 + t) / t
        linarith
      · exact hcost
  | succ r ih =>
      have hhalf : 0 < δ / 2 := by positivity
      obtain ⟨n, t, ht, ht1, hH, hcost⟩ := exists_odd_escape_cost (δ / 2) hhalf
      let outer := oddEscapeTriple n t ht ht1
      let c : ℚ := (1 + δ) / (1 + δ / 2)
      have hden : 0 < (1 + δ / 2 : ℚ) := by linarith
      have hc : 1 < c := by
        dsimp [c]
        apply (one_lt_div hden).2
        linarith
      obtain ⟨b, hb, hbpow⟩ := exists_rational_pow_between c hc (Fintype.card (Fin (2 * n + 3)))
      have hη : 0 < b - 1 := sub_pos.mpr hb
      obtain ⟨ι, F, E, inner, hthreshold, hinner⟩ := ih (b - 1) hη
      letI : Fintype ι := F
      letI : DecidableEq ι := E
      refine ⟨ι × Fin (2 * n + 3), inferInstance, inferInstance,
        shearEscapeTriple inner outer, ?_, ?_⟩
      · change (2 : ℚ) ^ (r + 1) ≤ inner.H * outer.H
        rw [pow_succ]
        have : (2 : ℚ) ≤ outer.H := by dsimp [outer, oddEscapeTriple]; linarith
        exact mul_le_mul hthreshold this (by positivity) inner.Hpos.le
      · rw [shearEscapeTriple_cost]
        have hcOuter : outer.H * outer.B.det < 1 + δ / 2 := hcost
        have hcInner : inner.H * inner.B.det < b := by linarith
        have hcInnerPos : 0 < inner.H * inner.B.det :=
          mul_pos inner.Hpos inner.detpos
        have hk : 0 < Fintype.card (Fin (2 * n + 3)) := by simp
        have hpwr : (inner.H * inner.B.det) ^ Fintype.card (Fin (2 * n + 3)) <
            b ^ Fintype.card (Fin (2 * n + 3)) :=
          pow_lt_pow_left₀ hcInner hcInnerPos.le hk.ne'
        have hppos : 0 ≤ (inner.H * inner.B.det) ^ Fintype.card (Fin (2 * n + 3)) :=
          pow_nonneg hcInnerPos.le _
        calc
          (outer.H * outer.B.det) *
              (inner.H * inner.B.det) ^ Fintype.card (Fin (2 * n + 3)) ≤
            (1 + δ / 2) * b ^ Fintype.card (Fin (2 * n + 3)) := by
              apply mul_le_mul hcOuter.le hpwr.le (by positivity) hden.le
          _ < 1 + δ := by
            apply (lt_div_iff₀ hden).mp at hbpow
            simpa only [c, mul_comm] using hbpow

end Erdos1Aux
