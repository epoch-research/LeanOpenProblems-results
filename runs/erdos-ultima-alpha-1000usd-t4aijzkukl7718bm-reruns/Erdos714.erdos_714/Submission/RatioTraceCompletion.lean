import Submission.RatioFilteredNorm

/-!
Exact trace interpolation and translation of weighted norm grids.
The compatibility hypothesis is explicit. Finite field searches are not
silently promoted to kernel theorems, and Erdős 714 is not settled here.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714TraceCompletion

variable {K E I : Type*} [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

/-- A trace interpolation problem is solvable exactly when all coefficient
relations also annihilate the requested values. -/
theorem trace_interpolation_iff (a : I → E) (b : I → K) :
    (∃ x : E, ∀ i, Algebra.trace K E (x*a i) = b i) ↔
    (∀ c : I →₀ K, Finsupp.linearCombination K a c = 0 →
      Finsupp.linearCombination K b c = 0) := by
  let f := Finsupp.linearCombination K a
  let g := Finsupp.linearCombination K b
  constructor
  · rintro ⟨x,hx⟩ c hc
    have he : (Algebra.traceForm K E x).comp f = g := by
      apply Finsupp.lhom_ext
      intro i t
      simp only [LinearMap.comp_apply, f, g, Finsupp.linearCombination_single,
        map_smul, Algebra.traceForm_apply, hx, smul_eq_mul]
    have h := LinearMap.congr_fun he c
    rw [LinearMap.comp_apply, show f c = 0 from hc, map_zero] at h
    exact h.symm
  · intro h
    have hg : g ∈ f.ker.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro c hc
      exact h c hc
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker f] at hg
    obtain ⟨φ,hφ⟩ := hg
    obtain ⟨x,hx⟩ := (Algebra.traceForm K E).toDual
      (traceForm_nondegenerate K E) |>.surjective φ
    refine ⟨x,fun i => ?_⟩
    have hi := LinearMap.congr_fun hφ (Finsupp.single i 1)
    have he := LinearMap.congr_fun (show Algebra.traceForm K E x = φ from hx) (a i)
    simp only [LinearMap.dualMap_apply, f,g,
      Finsupp.linearCombination_single, one_smul] at hi
    simpa only [Algebra.traceForm_apply] using he.trans hi

/-- The target equations for a common translation of a rectangular grid. -/
def Compatible {J : Type*} (r : I → E) (c : J → E) (γ : K) : Prop :=
  ∀ u : (I × J) →₀ K,
    Finsupp.linearCombination K (fun p : I × J => (r p.1+c p.2)⁻¹) u = 0 →
    Finsupp.linearCombination K
      (fun p : I × J => γ-Algebra.trace K E (r p.1/(r p.1+c p.2))) u = 0

/-- All ratio-trace equations are solved by ONE translation, rather than
by making a separate incompatible choice on each edge. -/
theorem exists_translation {J : Type*} (r : I → E) (c : J → E) (γ : K)
    (h : Compatible r c γ) :
    ∃ t : E, ∀ i j,
      Algebra.trace K E ((r i+t)/((r i+t)+(c j-t))) = γ := by
  obtain ⟨t,ht⟩ := (trace_interpolation_iff
    (fun p : I × J => (r p.1+c p.2)⁻¹)
    (fun p : I × J => γ-Algebra.trace K E (r p.1/(r p.1+c p.2)))).mpr h
  refine ⟨t,fun i j => ?_⟩
  have hs : (r i+t)+(c j-t) = r i+c j := by ring
  rw [hs, add_div, map_add, div_eq_mul_inv t]
  have hh := ht (i,j)
  dsimp only at hh
  rw [hh]
  ring

variable {F : Type*} [Field F] [Algebra F E] [Fintype E]

/-- Translate an actual weighted norm K44 while programming all ratio traces.
Nonzero point coordinates follow from excluding trace values at zero and one. -/
def gridCopy (r c : Fin 4 → E) (a b : Fin 4 → Fˣ)
    (hr : Function.Injective r) (hc : Function.Injective c)
    (hnorm : ∀ i j, Algebra.norm F (r i+c j) = (a i : F)*(b j : F))
    (γ : K) (hγ0 : γ ≠ 0) (hγ1 : γ ≠ Algebra.trace K E 1)
    (hcompat : Compatible r c γ) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy
      (Erdos714RatioFilteredNorm.graph (Units.map (Algebra.norm F)) (Algebra.trace K E) γ) := by
  let t := Classical.choose (exists_translation r c γ hcompat)
  have ht := Classical.choose_spec (exists_translation r c γ hcompat)
  have hsum (i j : Fin 4) : (r i+t)+(c j-t) = r i+c j := by ring
  have hrow (i : Fin 4) : r i+t ≠ 0 := by
    intro h
    have hh := ht i 0
    rw [h, zero_div, map_zero] at hh
    exact hγ0 hh.symm
  have hcol (j : Fin 4) : c j-t ≠ 0 := by
    intro h
    have hh := ht 0 j
    rw [h, add_zero, div_self (hrow 0)] at hh
    exact hγ1 hh.symm
  let R : Fin 4 ↪ Erdos714RatioFilteredNorm.Vertex E F :=
    ⟨fun i => (Units.mk0 (r i+t) (hrow i), a i), by
      intro i j h
      apply hr
      have he := congrArg (fun p : Erdos714RatioFilteredNorm.Vertex E F => (p.1:E)) h
      exact add_right_cancel he⟩
  let C : Fin 4 ↪ Erdos714RatioFilteredNorm.Vertex E F :=
    ⟨fun j => (Units.mk0 (c j-t) (hcol j), b j), by
      intro i j h
      apply hc
      have he := congrArg (fun p : Erdos714RatioFilteredNorm.Vertex E F => (p.1:E)) h
      exact sub_left_injective he⟩
  have hedge (i j : Fin 4) : Erdos714RatioFilteredNorm.Rel
      (Units.map (Algebra.norm F)) (Algebra.trace K E) γ (R i) (C j) := by
    apply (Erdos714RatioFilteredNorm.norm_rel_iff _ _ _ _).mpr
    change Algebra.norm F ((r i+t)+(c j-t)) = (a i : F)*(b j : F) ∧
      Algebra.trace K E ((r i+t)/((r i+t)+(c j-t))) = γ
    exact ⟨by rw [hsum]; exact hnorm i j, ht i j⟩
  refine ⟨⟨R.sumMap C,?_⟩,(R.sumMap C).injective⟩
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at hxy
    | inr j => exact hedge i j
  | inr j =>
    cases y with
    | inr i => simp at hxy
    | inl i => exact hedge i j

/-- An explicit compatibility certificate suffices to refute freeness of
this filtered construction, in any characteristic. -/
theorem not_free_of_compatible (r c : Fin 4 → E) (a b : Fin 4 → Fˣ)
    (hr : Function.Injective r) (hc : Function.Injective c)
    (hnorm : ∀ i j, Algebra.norm F (r i+c j) = (a i : F)*(b j : F))
    (γ : K) (hγ0 : γ ≠ 0) (hγ1 : γ ≠ Algebra.trace K E 1)
    (hcompat : Compatible r c γ) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714RatioFilteredNorm.graph (Units.map (Algebra.norm F)) (Algebra.trace K E) γ) := by
  intro h
  exact h ⟨gridCopy r c a b hr hc hnorm γ hγ0 hγ1 hcompat⟩

#print axioms trace_interpolation_iff
#print axioms exists_translation
#print axioms gridCopy
#print axioms not_free_of_compatible
end Erdos714TraceCompletion
