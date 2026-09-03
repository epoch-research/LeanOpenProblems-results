import Submission.PhaseCompletePaletteExplore

/-! Arbitrarily large families of DISTINCT equal-cardinality templates with
simultaneous mixed and endpoint-prefix flatness at logarithmic mean. They
are finite same-modulus families, not an infinite integer construction. -/
namespace Erdos66EqualCardinalityMixedFamily
open Erdos66TranslatedPrefixPalette Erdos66PhaseCompletePalette
  Erdos66OuterMixedPrefix Erdos66OuterCarryProfile Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 2400000

variable (M : ℕ) [NeZero M]

noncomputable def shiftOrbit (B : Finset (ZMod M)) : Finset (Finset (ZMod M)) :=
  Finset.univ.image (shift M B)

lemma mem_shiftOrbit (B C : Finset (ZMod M)) :
    C∈shiftOrbit M B ↔ ∃ t : ZMod M, shift M B t=C := by
  simp [shiftOrbit]

lemma shiftOrbit_cardinality (B C : Finset (ZMod M)) (hC : C∈shiftOrbit M B) :
    C.card=B.card := by
  obtain ⟨t,rfl⟩ := (mem_shiftOrbit M B C).mp hC
  exact shift_card M B t

lemma shiftOrbit_covers (B : Finset (ZMod M)) (hB : B.Nonempty) :
    (shiftOrbit M B).biUnion id=Finset.univ := by
  ext z
  simp only [Finset.mem_biUnion,Finset.mem_univ,iff_true,id_eq]
  obtain ⟨b,hb⟩ := hB
  refine ⟨shift M B (z-b),(mem_shiftOrbit M B _).mpr ⟨z-b,rfl⟩,?_⟩
  rw [mem_shift]
  simpa only [sub_sub_cancel] using hb

/-- No assumption of a trivial stabilizer is needed: the distinct translates
cover the group, so their number times the common size is at least M. -/
theorem shiftOrbit_size_bound (B : Finset (ZMod M)) (hB : B.Nonempty) :
    M≤ (shiftOrbit M B).card*B.card := by
  have hh : ((shiftOrbit M B).biUnion id).card≤ ∑ C∈shiftOrbit M B, C.card :=
    Finset.card_biUnion_le
  rw [shiftOrbit_covers M B hB,Finset.card_univ,ZMod.card] at hh
  have he : (∑ C∈shiftOrbit M B, C.card)=(shiftOrbit M B).card*B.card := by
    calc
      _ = ∑ _C∈shiftOrbit M B, B.card := Finset.sum_congr rfl
        (fun C hC ↦ shiftOrbit_cardinality M B C hC)
      _ = _ := by simp
  exact hh.trans_eq he

lemma shiftOrbit_large (B : Finset (ZMod M)) (hB : 0<B.card) (q : ℕ)
    (hfit : (q:ℝ)*B.card≤ M) : q≤ (shiftOrbit M B).card := by
  have hb := shiftOrbit_size_bound M B (Finset.card_pos.mp hB)
  have hf : q*B.card≤ M := by exact_mod_cast hfit
  exact Nat.le_of_mul_le_mul_right (hf.trans hb) hB

/-- For arbitrary c>0 and precision, the number of DISTINCT jointly flat,
equal-cardinality templates can be arbitrarily large. Translation does not
create a loss in coefficient or an additional number-of-colors error. -/
theorem exists_large_equal_cardinality_family (c τ η : ℝ)
    (hc : 0<c) (hτ : 0<τ) (hη : 0<η) (hη1 : η≤ 1) (q N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ 1<M ∧ ∃ _hM : NeZero M,
      ∃ (k : ℕ) (P : Finset (Finset (ZMod M))),
        0<k ∧ q≤ P.card ∧
        |((k:ℝ)^2/M)/Real.log M-c|<τ ∧
        (∀ B∈P, B.card=k) ∧
        (∀ B∈P, ∀ C∈P, ∀ z,
          |(cyclicCount M B C z:ℝ)-(k:ℝ)^2/M|≤ η*((k:ℝ)^2/M)) ∧
        (∀ B∈P, ∀ C∈P, ∀ z u, u≤ M →
          |(prefixCount M B C z u:ℝ)-(u:ℝ)/M*((k:ℝ)^2/M)|≤ η*((k:ℝ)^2/M)) := by
  obtain ⟨M,hMN,hM1,hM,B,Q,hB,hBQ,hfit,htune,hphase,hprefix,hcover⟩ :=
    exists_fitting_phase_palette c τ η 1 (q:ℝ) hc hτ hη hη1
      (by norm_num) (by norm_num) (by positivity) N₀
  letI := hM
  have hsub : shiftOrbit M B⊆ Q := by
    intro C hC
    obtain ⟨t,rfl⟩ := (mem_shiftOrbit M B C).mp hC
    exact hphase B hBQ t
  have hmean (C : Finset (ZMod M)) (hC : C∈shiftOrbit M B)
      (D : Finset (ZMod M)) (hD : D∈shiftOrbit M B) :
      actualMean M C D=(B.card:ℝ)^2/M := by
    rw [actualMean,shiftOrbit_cardinality M B C hC,shiftOrbit_cardinality M B D hD,pow_two]
  have hpre (C : Finset (ZMod M)) (hC : C∈shiftOrbit M B)
      (D : Finset (ZMod M)) (hD : D∈shiftOrbit M B) (z : ZMod M) (u : ℕ) (hu : u≤ M) :
      |(prefixCount M C D z u:ℝ)-(u:ℝ)/M*((B.card:ℝ)^2/M)|≤ η*((B.card:ℝ)^2/M) := by
    have hh := hprefix C (hsub hC) D (hsub hD) z u hu
    simpa only [hmean C hC D hD] using hh
  refine ⟨M,hMN,hM1,hM,B.card,shiftOrbit M B,hB,shiftOrbit_large M B hB q hfit,?_,
    fun C hC ↦ shiftOrbit_cardinality M B C hC,?_,hpre⟩
  · simpa only [actualMean,pow_two] using htune
  · intro C hC D hD z
    have hh := hpre C hC D hD z M le_rfl
    simpa only [prefix_full,div_self (by exact_mod_cast NeZero.ne M : (M:ℝ)≠0),one_mul] using hh

end Erdos66EqualCardinalityMixedFamily
