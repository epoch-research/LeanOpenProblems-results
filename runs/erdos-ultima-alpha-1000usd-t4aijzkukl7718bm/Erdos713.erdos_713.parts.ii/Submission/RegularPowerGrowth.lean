import FormalConjecturesUtil
import Submission.RestrictedPolarity

/-! Regular C4-free graph families can have irrational power edge growth.
These graph families are NOT claimed to maximize their edge counts. Thus this
is a diagnostic for local-structure arguments, not a disproof of Erdos 713. -/
open SimpleGraph Filter Asymptotics
open scoped Topology
namespace Erdos713RegularPowerGrowth
set_option maxHeartbeats 1000000

private def fieldOrder (n : ℕ) : ℕ := 2 ^ (n + 1)

private lemma fieldOrder_gt_one (n : ℕ) : 1 < fieldOrder n := by
  exact one_lt_pow₀ (by norm_num) (by omega)

private lemma fieldOrder_tendsto : Tendsto fieldOrder atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp
    (tendsto_add_atTop_nat 1)

private noncomputable def slopeCount (β : ℝ) (n : ℕ) : ℕ :=
  ⌊(fieldOrder n : ℝ) ^ β⌋₊

private lemma slopeCount_lt {β : ℝ} (hβ : β < 1) (n : ℕ) :
    slopeCount β n < fieldOrder n := by
  apply (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr
  simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt
    (show (1 : ℝ) < fieldOrder n by exact_mod_cast fieldOrder_gt_one n) hβ

private lemma slopeCount_pos {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    1 ≤ slopeCount β n := by
  apply Nat.le_floor
  simpa only [Nat.cast_one] using Real.one_le_rpow
    (show (1 : ℝ) ≤ fieldOrder n by exact_mod_cast (fieldOrder_gt_one n).le) hβ

private lemma slope_ratio_limit {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n => (slopeCount β n : ℝ) / (fieldOrder n : ℝ) ^ β)
      atTop (𝓝 1) := by
  have hQ : Tendsto (fun n => (fieldOrder n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp fieldOrder_tendsto
  have hfloor : (fun n => (slopeCount β n : ℝ)) ~[atTop]
      (fun n => (fieldOrder n : ℝ) ^ β) :=
    isEquivalent_nat_floor.comp_tendsto ((tendsto_rpow_atTop hβ).comp hQ)
  apply (isEquivalent_iff_tendsto_one _).mp hfloor
  exact Eventually.of_forall fun n => (Real.rpow_pos_of_pos
    (show (0 : ℝ) < fieldOrder n by exact_mod_cast (fieldOrder_gt_one n).trans' zero_lt_one)
    β).ne'

/-- The two monomial scales agree when beta(2-alpha)=alpha-1. -/
lemma edge_ratio_identity {d q α β : ℝ} (hd : 0 < d) (hq : 0 < q)
    (hrel : β * (2 - α) = α - 1) :
    (d ^ 2 * q) / (d * q) ^ α = (d / q ^ β) ^ (2 - α) := by
  rw [Real.div_rpow hd.le (Real.rpow_nonneg hq.le β),
    ← Real.rpow_mul hq.le, hrel, Real.rpow_sub hd 2 α,
    Real.rpow_sub hq α 1, Real.rpow_two, Real.rpow_one,
    Real.mul_rpow hd.le hq.le]
  field_simp

open scoped Classical in
/-- Every exponent strictly between 1 and 3/2 occurs in a family of actual
regular C4-free graphs. The order tends to infinity, and edge growth is
measured against that order, not against the family index. No extremality
or asymptotic for extremalNumber is asserted. -/
theorem exists_regular_power_family {α : ℝ} (hα : 1 < α) (hαhi : α < 3 / 2) :
    ∃ N d : ℕ → ℕ, Tendsto N atTop atTop ∧ Tendsto d atTop atTop ∧
      ∃ G : ∀ i, SimpleGraph (Fin (N i)),
        (∀ i, (cycleGraph 4).Free (G i) ∧ ∀ v, (G i).degree v = d i) ∧
        (fun i => (Nat.card (G i).edgeSet : ℝ)) ~[atTop]
          (fun i => (1 / 2 : ℝ) * (N i : ℝ) ^ α) ∧
        (fun i => (d i : ℝ)) ~[atTop]
          (fun i => (N i : ℝ) ^ (α - 1)) := by
  classical
  let β : ℝ := (α - 1) / (2 - α)
  have hden : 0 < 2 - α := by linarith
  have hβ : 0 < β := div_pos (by linarith) hden
  have hβhi : β < 1 := (div_lt_one hden).mpr (by linarith)
  have hrel : β * (2 - α) = α - 1 := div_mul_cancel₀ _ hden.ne'
  let d : ℕ → ℕ := slopeCount β
  let N : ℕ → ℕ := fun n => d n * fieldOrder n
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) fieldOrder_tendsto
    have hd := slopeCount_pos hβ.le n
    dsimp [N, d]
    nlinarith
  have hdlim : Tendsto d atTop atTop := by
    have hpow := (tendsto_rpow_atTop hβ).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp fieldOrder_tendsto)
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [hpow.eventually_ge_atTop (k : ℝ)] with n hn
    exact Nat.le_floor hn
  have hex (n : ℕ) : ∃ G : SimpleGraph (Fin (N n)),
      (cycleGraph 4).Free G ∧ (∀ v, G.degree v = d n) ∧
      2 * Nat.card G.edgeSet = (d n) ^ 2 * fieldOrder n := by
    let K := GaloisField 2 (n + 1)
    letI : Fintype K := Fintype.ofFinite K
    have hc : Fintype.card K = fieldOrder n := by
      simpa only [← Nat.card_eq_fintype_card, K, fieldOrder] using
        (GaloisField.card 2 (n + 1) (by omega : n + 1 ≠ 0))
    have hd : d n < Fintype.card K := hc.symm ▸ slopeCount_lt hβhi n
    have hg := Erdos713RestrictedPolarity.exists_regular_c4_free (K := K) (d n) hd
    rw [hc] at hg
    obtain ⟨G, hfree, hdeg, he⟩ := hg
    refine ⟨G, hfree, hdeg, ?_⟩
    simpa only [edgeFinset_card, ← Nat.card_eq_fintype_card] using he
  choose G hfree hdeg he using hex
  have hlim := (slope_ratio_limit hβ).rpow_const
    (Or.inl (by norm_num : (1 : ℝ) ≠ 0) : (1 : ℝ) ≠ 0 ∨ 0 ≤ 2 - α)
  simp only [Real.one_rpow] at hlim
  have hNpos (n : ℕ) : (0 : ℝ) < N n := by
    have hd := slopeCount_pos hβ.le n
    have hq := fieldOrder_gt_one n
    have hn : 0 < N n := by
      dsimp [N, d]
      exact Nat.mul_pos (by omega) (by omega)
    exact_mod_cast hn
  refine ⟨N, d, hN, hdlim, G, fun n => ⟨hfree n, hdeg n⟩, ?_, ?_⟩
  · have hz : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) * (N n : ℝ) ^ α ≠ 0 := by
      apply Eventually.of_forall
      intro n
      apply mul_ne_zero (by norm_num)
      apply (Real.rpow_pos_of_pos _ α).ne'
      exact hNpos n
    apply (isEquivalent_iff_tendsto_one hz).mpr
    apply hlim.congr'
    apply Eventually.of_forall
    intro n
    have hd : (0 : ℝ) < d n := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (slopeCount_pos hβ.le n))
    have hq : (0 : ℝ) < fieldOrder n := by
      exact_mod_cast (fieldOrder_gt_one n).trans' zero_lt_one
    have he' : 2 * (Nat.card (G n).edgeSet : ℝ) = (d n : ℝ) ^ 2 * fieldOrder n := by
      exact_mod_cast he n
    change (d n / (fieldOrder n : ℝ) ^ β) ^ (2 - α) =
      (Nat.card (G n).edgeSet : ℝ) / ((1 / 2 : ℝ) * (N n : ℝ) ^ α)
    rw [← edge_ratio_identity hd hq hrel]
    have he'' : (Nat.card (G n).edgeSet : ℝ) = (d n : ℝ) ^ 2 * fieldOrder n / 2 := by
      linarith
    rw [he'', show (N n : ℝ) = (d n : ℝ) * fieldOrder n by simp only [N, Nat.cast_mul]]
    ring
  · have hz : ∀ᶠ n : ℕ in atTop, (N n : ℝ) ^ (α - 1) ≠ 0 :=
      Eventually.of_forall fun n => (Real.rpow_pos_of_pos (hNpos n) _).ne'
    apply (isEquivalent_iff_tendsto_one hz).mpr
    apply hlim.congr'
    apply Eventually.of_forall
    intro n
    have hd : (0 : ℝ) < d n := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (slopeCount_pos hβ.le n))
    have hq : (0 : ℝ) < fieldOrder n := by
      exact_mod_cast (fieldOrder_gt_one n).trans' zero_lt_one
    change (d n / (fieldOrder n : ℝ) ^ β) ^ (2 - α) =
      (d n : ℝ) / (N n : ℝ) ^ (α - 1)
    rw [← edge_ratio_identity hd hq hrel, Real.rpow_sub (hNpos n) α 1,
      Real.rpow_one,
      show (N n : ℝ) = (d n : ℝ) * fieldOrder n by simp only [N, Nat.cast_mul]]
    field_simp

open scoped Classical in
/-- An explicit irrational index occurs with exact power asymptotics, actual
C4-freeness, regularity, and degrees tending to infinity. -/
theorem exists_irrational_regular_family :
    ∃ α : ℝ, 1 < α ∧ α < 3 / 2 ∧ Irrational α ∧
      ∃ N d : ℕ → ℕ, Tendsto N atTop atTop ∧ Tendsto d atTop atTop ∧
        ∃ G : ∀ i, SimpleGraph (Fin (N i)),
          (∀ i, (cycleGraph 4).Free (G i) ∧ ∀ v, (G i).degree v = d i) ∧
          (fun i => (Nat.card (G i).edgeSet : ℝ)) ~[atTop]
            (fun i => (1 / 2 : ℝ) * (N i : ℝ) ^ α) ∧
          (fun i => (d i : ℝ)) ~[atTop]
            (fun i => (N i : ℝ) ^ (α - 1)) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hlow : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hhigh : Real.sqrt 2 < (3 : ℝ) / 2 := by nlinarith
  exact ⟨Real.sqrt 2, hlow, hhigh, irrational_sqrt_two,
    exists_regular_power_family hlow hhigh⟩

#print axioms edge_ratio_identity
#print axioms exists_regular_power_family
#print axioms exists_irrational_regular_family
end Erdos713RegularPowerGrowth
