import Submission.RootFreeFactorElimination

/-! Large U2 of a positive-pivot integer phase combination yields a genuine
one-coordinate reduction of a local quadratic factor, with explicit rank,
radius, observable-error, and Lipschitz bounds. The domain is initially
parameterized by the 2n-dilate; no roots or branch labels are introduced. -/
namespace Erdos3BohrFactorCoordinateElimination
open Finset Erdos3RootFreeFactorElimination Erdos3ReducedObservableExtension
  Erdos3LocalQuadraticU2Linearization Erdos3ExplicitPhaseFlattening
  Erdos3BoundedFrequencyPhaseApproximation Erdos3LocalQuadraticInverse
  Erdos3StableMaskedUniformity Erdos3FiniteUniformity Erdos3FiniteBohr
  Erdos3BohrCovering Erdos3BohrPatternGeometry Erdos3RelativeStableBohr
  Erdos3CorrelationSifting
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 7000000

noncomputable def eliminationRadius (d : ℕ) (R τ β : ℝ) (o n : ℕ) : ℝ :=
  min (explicitBaseRadius d R (τ/(8*(n : ℝ))) β o/(2*(n : ℝ)))
    (min (explicitStepRadius d R (τ/(8*(n : ℝ))) β o/2) (τ/8))

lemma eliminationRadius_pos (d : ℕ) {R τ β : ℝ}
    (hR : 0 < R) (hτ : 0 < τ) (hβ : 0 < β) {o n : ℕ} (ho : 0 < o) (hn : 0 < n) :
    0 < eliminationRadius d R τ β o n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hσ : 0 < τ/(8*(n : ℝ)) := by positivity
  have hb := explicitBaseRadius_pos d (σ := τ/(8*(n : ℝ))) (β := β) hR ho
  have ht := explicitStepRadius_pos d hR hσ hβ ho
  unfold eliminationRadius
  positivity

variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I] [DecidableEq I]

/-- A complete one-coordinate reduction for a positive pivot. All reduced
coordinates are unit and locally quadratic, and the observable is globally
bounded and Lipschitz. The new coordinate type has cardinality |I|-1. -/
theorem bohr_factor_elimination_positive_pivot (D : Finset (AddChar G ℂ))
    {R β τ : ℝ} (hR : 0 < R) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) {o : ℕ} (ho : 0 < o)
    (hst : RelativeStable D o R) (hoB : 1/(o : ℝ) ≤ β/8)
    (j : I) (n : ℕ) (hn : 0 < n) (k : I → ℤ) (hk : k j = n)
    (Q : I → G → ℂ) (hQ : ∀ i x, ‖Q i x‖ = 1)
    (hquad : ∀ i, IsLocallyQuadratic (bohr D R : Set G) (Q i))
    (hU : β^2*(density (bohr D R))^3 ≤
      uniformityPower 1 (mask (bohr D R) (fun x ↦ integerPhase k (fun i ↦ Q i x))))
    (H : (I → ℂ) → ℝ) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1)
    {L : NNReal} (hLip : LipschitzWith L H) :
    ∃ C : Finset (AddChar G ℂ), ∃ u : ℝ, ∃ b ∈ bohr D R,
      ∃ P : {i : I // i ≠ j} → G → ℂ, ∃ H' : ({i : I // i ≠ j} → ℂ) → ℝ,
        (C.card : ℝ) ≤ D.card+32/β^2+1 ∧ eliminationRadius D.card R τ β o n ≤ u ∧ 0 < u ∧
        (∀ x ∈ bohr C u, b+(2*n) • x ∈ bohr D R) ∧
        (∀ i x, ‖P i x‖ = 1) ∧ (∀ i, IsLocallyQuadratic (bohr C u : Set G) (P i)) ∧
        (∀ v, 0 ≤ H' v ∧ H' v ≤ 1) ∧ LipschitzWith (L*reconstructionCost n k) H' ∧
        ∀ x ∈ bohr C u, |H (fun i ↦ Q i (b+(2*n) • x))-H' (fun i ↦ P i x)| ≤ (L : ℝ)*τ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let σ := τ/(8*(n : ℝ))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσ1 : σ ≤ 1 := by
    dsimp [σ]
    apply (div_le_one (by positivity)).mpr
    linarith
  let q : G → ℂ := fun x ↦ integerPhase k (fun i ↦ Q i x)
  have hq (x : G) : ‖q x‖ = 1 := integerPhase_norm k _ (fun i ↦ hQ i x)
  have hqquad : IsLocallyQuadratic (bohr D R : Set G) q := integerPhase_locally_quadratic k Q hquad
  obtain ⟨ψ,E,s,t,b,hb,hE,hDE,hsL,htL,hs,ht,hdom,hbase,_⟩ :=
    local_quadratic_U2_linearization D hR hβ hβ1 hσ hσ1 ho hst hoB q hq hqquad hU
  let C := (D ∪ E) ∪ {ψ}
  let u := min (s/(2*(n : ℝ))) (min (t/2) (τ/8))
  have hu : 0 < u := by dsimp [u]; positivity
  have hus : u ≤ s/(2*(n : ℝ)) := min_le_left _ _
  have hut : u ≤ t/2 := (min_le_right _ _).trans (min_le_left _ _)
  have huτ : u ≤ τ/8 := (min_le_right _ _).trans (min_le_right _ _)
  have hcu : bohr C u ⊆ bohr (D ∪ E) u := by
    intro x hx
    exact mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hx χ (mem_union_left _ hχ))
  have hdu : bohr C u ⊆ bohr D u := by
    intro x hx
    exact mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp (hcu hx) χ (mem_union_left _ hχ))
  have hψ (x : G) (hx : x ∈ bohr C u) : ‖ψ x-1‖ ≤ τ/8 :=
    (mem_bohr.mp hx ψ (mem_union_right _ (mem_singleton_self _))).trans huτ
  have hsteps (x : G) (hx : x ∈ bohr C u) (l : ℕ) (hl : l ≤ 2*n) :
      b+l • x ∈ bohr D R := by
    have hls : (l : ℝ)*u ≤ s := by
      have hlR : (l : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast hl
      have hs' := (le_div_iff₀ (show 0 < 2*(n : ℝ) by positivity)).mp hus
      nlinarith [mul_le_mul_of_nonneg_right hlR hu.le]
    have hx' := bohr_mono D hls (bohr_nsmul (hdu hx) l)
    simpa only [add_zero] using hdom (l • x) hx' 0 (bohr_zero _ ht.le)
  have hrel1 (x : G) (hx : x ∈ bohr C u) : ‖q (b+x)-q b*ψ x‖ ≤ σ/2 :=
    hbase x (bohr_mono (D ∪ E) (by linarith : u ≤ t) (hcu hx))
  have hrel2 (x : G) (hx : x ∈ bohr C u) :
      ‖q (b+(2 : ℕ) • x)-q b*ψ ((2 : ℕ) • x)‖ ≤ σ/2 := by
    apply hbase
    apply bohr_mono (D ∪ E) (by norm_num; linarith : (2 : ℕ)*u ≤ t)
    exact bohr_nsmul (hcu hx) 2
  obtain ⟨P,H',hP,hPquad,hH',hLip',happrox⟩ := root_free_factor_elimination j n hn k hk Q hQ hquad b
    hsteps ψ (show 0 ≤ σ/2 by positivity) (show 0 ≤ τ/8 by positivity) hrel1 hrel2 hψ H hH hLip
  have hC : (C.card : ℝ) ≤ D.card+32/β^2+1 := by
    have hh : (C.card : ℝ) ≤ ((D ∪ E).card : ℝ)+1 := by
      dsimp [C]
      have hc := card_union_le (D ∪ E) {ψ}
      simpa only [card_singleton,Nat.cast_add,Nat.cast_one] using (show ((D ∪ E ∪ {ψ}).card : ℝ) ≤ (D ∪ E).card+({ψ} : Finset (AddChar G ℂ)).card by exact_mod_cast hc)
    linarith
  have hrad : eliminationRadius D.card R τ β o n ≤ u := by
    apply min_le_min
    · exact div_le_div_of_nonneg_right hsL (by positivity)
    · exact min_le_min_right _ (div_le_div_of_nonneg_right htL (by norm_num))
  refine ⟨C,u,b,hb,P,H',hC,hrad,hu,fun x hx ↦ hsteps x hx (2*n) le_rfl,hP,hPquad,hH',hLip',?_⟩
  intro x hx
  apply (happrox x hx).trans
  apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
  have he : 6*(n : ℝ)*(σ/2)+2*(τ/8) = 5*τ/8 := by
    dsimp [σ]
    field_simp
    ring
  rw [he]
  linarith

#print axioms bohr_factor_elimination_positive_pivot
end Erdos3BohrFactorCoordinateElimination
