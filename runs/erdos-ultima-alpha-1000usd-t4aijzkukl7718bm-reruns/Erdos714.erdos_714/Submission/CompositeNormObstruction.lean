import Submission.QuarticNormProduct

/-!
A subgroup/normal-basis obstruction to trace-zero weighted norm graphs.
This is an obstruction to one proposed construction, not a disproof of Erdős 714.
-/

open SimpleGraph

noncomputable section

namespace Erdos714CompositeNorm

open Erdos714QuarticNormProduct

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E]

/-- A trace-compatible full conjugacy orbit supplies a complete bipartite copy. -/
def conjugateGrid (u v : E) (hu : u ≠ 0) (htu : Algebra.trace F E u = 0)
    (horbit : Function.Injective (fun g : Gal(E/F) => g v))
    (htuv : ∀ g : Gal(E/F), Algebra.trace F E (u * g v) = 0)
    (hv : ∀ t : F, algebraMap F E t + v ≠ 0) :
    Copy (completeBipartiteGraph F Gal(E/F)) (graph (F := F) (E := E)) := by
  have htu' (t : F) : Algebra.trace F E (algebraMap F E t * u) = 0 := by
    rw [← Algebra.smul_def, map_smul, htu, smul_zero]
  let weight (t : F) : Fˣ := Units.mk0
    (Algebra.norm F u * Algebra.norm F (algebraMap F E t + v))
    (mul_ne_zero (Algebra.norm_ne_zero_iff.mpr hu) (Algebra.norm_ne_zero_iff.mpr (hv t)))
  let L (t : F) : Point F E × Fˣ := (⟨algebraMap F E t * u, htu' t⟩, weight t)
  let R (g : Gal(E/F)) : Point F E × Fˣ := (⟨u * g v, htuv g⟩, 1)
  have hL : Function.Injective L := by
    intro t s h
    exact (algebraMap F E).injective (mul_right_cancel₀ hu
      (congrArg (fun w : Point F E × Fˣ => (w.1 : E)) h))
  have hR : Function.Injective R := by
    intro g k h
    exact horbit (mul_left_cancel₀ hu
      (congrArg (fun w : Point F E × Fˣ => (w.1 : E)) h))
  have hE (t : F) (g : Gal(E/F)) : graph.Adj (.inl (L t)) (.inr (R g)) := by
    change Algebra.norm F (algebraMap F E t * u + u * g v) =
      (Algebra.norm F u * Algebra.norm F (algebraMap F E t + v)) * 1
    rw [show algebraMap F E t * u + u * g v =
      u * (algebraMap F E t + g v) by ring, map_mul, mul_one]
    congr 1
    rw [show algebraMap F E t + g v = g (algebraMap F E t + v) by
      rw [map_add, g.commutes], Algebra.norm_eq_of_algEquiv]
  let le : F ↪ Point F E × Fˣ := ⟨L, hL⟩
  let re : Gal(E/F) ↪ Point F E × Fˣ := ⟨R, hR⟩
  refine ⟨⟨le.sumMap re, ?_⟩, (le.sumMap re).injective⟩
  intro a b hab
  cases a with
  | inl t =>
    cases b with
    | inl s => simp at hab
    | inr g => exact hE t g
  | inr g =>
    cases b with
    | inl t => exact hE t g
    | inr k => simp at hab

variable [IsGalois F E]

/-- In odd characteristic a difference of two normal-basis vectors has full orbit. -/
theorem normal_difference_injective (h2 : (2 : F) ≠ 0) (τ : Gal(E/F)) (hτ : τ ≠ 1) :
    Function.Injective (fun g : Gal(E/F) =>
      g (IsGalois.normalBasis F E 1 - IsGalois.normalBasis F E τ)) := by
  classical
  let b := IsGalois.normalBasis F E
  have hact (g k : Gal(E/F)) : g (b k) = b (g * k) := by
    dsimp only [b]
    rw [IsGalois.normalBasis_apply k, ← AlgEquiv.mul_apply,
      ← IsGalois.normalBasis_apply (g * k)]
  intro g k he
  by_contra hne
  have hgt : g * τ ≠ g := by
    intro he
    exact hτ (mul_left_cancel (show g * τ = g * 1 by simpa using he))
  have hc := congrArg (fun x : E => b.repr x g) he
  change b.repr (g (b 1 - b τ)) g = b.repr (k (b 1 - b τ)) g at hc
  simp only [map_sub, hact, mul_one, Finsupp.sub_apply, Module.Basis.repr_self_apply] at hc
  by_cases hkt : k * τ = g
  · simp only [ite_true, if_neg hgt, if_neg (Ne.symm hne), if_pos hkt,
      sub_zero, zero_sub] at hc
    exact h2 (by linear_combination hc)
  · simp [hgt, Ne.symm hne, hkt] at hc

/-- A proper subgroup with a central nonidentity element provides the parameters. -/
theorem subgroup_parameters (h2 : (2 : F) ≠ 0) (H : Subgroup Gal(E/F))
    (σ τ : Gal(E/F)) (hσ : σ ∉ H) (hτ : τ ∈ H) (hτ1 : τ ≠ 1)
    (hcentral : ∀ g : Gal(E/F), τ * g = g * τ) :
    ∃ u v : E, u ≠ 0 ∧ Algebra.trace F E u = 0 ∧
      Function.Injective (fun g : Gal(E/F) => g v) ∧
      (∀ g : Gal(E/F), Algebra.trace F E (u * g v) = 0) ∧
      (∀ t : F, algebraMap F E t + v ≠ 0) := by
  classical
  letI := Fintype.ofFinite Gal(E/F)
  letI := Fintype.ofFinite H
  let b := IsGalois.normalBasis F E
  have hact (g k : Gal(E/F)) : g (b k) = b (g * k) := by
    dsimp only [b]
    rw [IsGalois.normalBasis_apply k, ← AlgEquiv.mul_apply,
      ← IsGalois.normalBasis_apply (g * k)]
  let T : E := ∑ h : H, b h
  let u : E := T - σ T
  let v : E := b 1 - b τ
  have hcoef (g : Gal(E/F)) : b.repr T g = if g ∈ H then 1 else 0 := by
    dsimp only [T]
    simp only [map_sum, Finsupp.finset_sum_apply, Module.Basis.repr_self_apply]
    split_ifs with hg
    · rw [Finset.sum_eq_single (⟨g, hg⟩ : H)]
      · simp
      · intro k _ hk
        have hkg : (k : Gal(E/F)) ≠ g := by
          intro he
          exact hk (Subtype.ext he)
        simp [hkg]
      · simp
    · apply Finset.sum_eq_zero
      intro k _
      have hkg : (k : Gal(E/F)) ≠ g := by rintro rfl; exact hg k.property
      simp [hkg]
  have hcoefσ : b.repr (σ T) 1 = 0 := by
    dsimp only [T]
    simp only [map_sum, hact, Finsupp.finset_sum_apply, Module.Basis.repr_self_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hk : σ * (k : Gal(E/F)) ≠ 1 := by
      intro he
      apply hσ
      have hs : σ = (k : Gal(E/F))⁻¹ := eq_inv_of_mul_eq_one_left he
      rw [hs]
      exact H.inv_mem k.property
    simp [hk]
  have hu0 : u ≠ 0 := by
    intro he
    have hc := congrArg (fun x : E => b.repr x 1) he
    simp [u, hcoef, H.one_mem, hcoefσ] at hc
  have htu : Algebra.trace F E u = 0 := by
    dsimp only [u]
    rw [map_sub, Algebra.trace_eq_of_algEquiv, sub_self]
  have hτT : τ T = T := by
    dsimp only [T]
    simp only [map_sum, hact]
    exact Equiv.sum_comp (Equiv.mulLeft (⟨τ, hτ⟩ : H)) (fun k : H => b k)
  have hτu : τ u = u := by
    dsimp only [u]
    rw [map_sub, hτT, ← AlgEquiv.mul_apply, hcentral, AlgEquiv.mul_apply, hτT]
  have hinj : Function.Injective (fun g : Gal(E/F) => g v) :=
    normal_difference_injective h2 τ hτ1
  refine ⟨u, v, hu0, htu, hinj, ?_, ?_⟩
  · intro g
    have he : u * g v = u * g (b 1) - τ (u * g (b 1)) := by
      dsimp only [v]
      rw [map_sub, mul_sub, map_mul, hτu]
      congr 1
      simp only [hact, mul_one]
      rw [hcentral]
    rw [he, map_sub, Algebra.trace_eq_of_algEquiv, sub_self]
  · intro t ht
    have he : v = -algebraMap F E t := eq_neg_of_add_eq_zero_right ht
    have hvfix : τ v = (1 : Gal(E/F)) v := by
      rw [he, map_neg, τ.commutes, map_neg, AlgEquiv.commutes]
    exact hτ1 (hinj hvfix)

/-- This weighted norm graph contains `K_(|F|,[E:F])` under the subgroup hypotheses. -/
def subgroupGrid (h2 : (2 : F) ≠ 0) (H : Subgroup Gal(E/F))
    (σ τ : Gal(E/F)) (hσ : σ ∉ H) (hτ : τ ∈ H) (hτ1 : τ ≠ 1)
    (hcentral : ∀ g : Gal(E/F), τ * g = g * τ) :
    Copy (completeBipartiteGraph F Gal(E/F)) (graph (F := F) (E := E)) := by
  apply Classical.choice
  obtain ⟨u, v, hu, htu, hinj, huv, hv⟩ := subgroup_parameters h2 H σ τ hσ hτ hτ1 hcentral
  exact ⟨conjugateGrid u v hu htu hinj huv hv⟩

/-- A finite cyclic group of composite order has a proper nontrivial subgroup. -/
theorem composite_subgroup {G : Type*} [CommGroup G] [Fintype G]
    (hcard : 2 ≤ Fintype.card G) (hcomp : ¬ (Fintype.card G).Prime) :
    ∃ H : Subgroup G, H ≠ ⊥ ∧ H ≠ ⊤ := by
  classical
  letI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp hcard
  by_contra! h
  have hs : IsSimpleGroup G := ⟨by
    intro H _
    by_cases hbot : H = ⊥
    · exact Or.inl hbot
    · exact Or.inr (h H hbot)⟩
  exact hcomp (by simpa only [Nat.card_eq_fintype_card] using
    CommGroup.is_simple_iff_prime_card.mp hs)

omit [IsGalois F E] in
/-- Every odd finite-field extension of composite degree has a full conjugate grid. -/
def finiteCompositeGrid [Fintype F] [Finite E] (h2 : (2 : F) ≠ 0)
    (hdegree : 2 ≤ Module.finrank F E) (hcomp : ¬ (Module.finrank F E).Prime) :
    Copy (completeBipartiteGraph F Gal(E/F)) (graph (F := F) (E := E)) := by
  classical
  letI := Fintype.ofFinite Gal(E/F)
  letI : CommGroup Gal(E/F) := IsCyclic.commGroup
  have hcard : Fintype.card Gal(E/F) = Module.finrank F E :=
    Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank F E)
  apply Classical.choice
  obtain ⟨H, hbot, htop⟩ := composite_subgroup (hcard ▸ hdegree) (hcard ▸ hcomp)
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(E/F), σ ∉ H := by
    by_contra! hmem
    exact htop (H.eq_top_iff'.mpr hmem)
  obtain ⟨τ, hτ, hτ1⟩ : ∃ τ : Gal(E/F), τ ∈ H ∧ τ ≠ 1 := by
    by_contra! hmem
    exact hbot (H.eq_bot_iff_forall.mpr hmem)
  exact ⟨subgroupGrid h2 H σ τ hσ hτ hτ1 (fun g => mul_comm τ g)⟩

omit [IsGalois F E] in
/-- For q at least the composite extension degree, the full graph is not K_(n,n)-free. -/
theorem finiteComposite_not_free [Fintype F] [Finite E] (h2 : (2 : F) ≠ 0)
    (hdegree : 2 ≤ Module.finrank F E) (hcomp : ¬ (Module.finrank F E).Prime)
    (hq : Module.finrank F E ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin (Module.finrank F E))
      (Fin (Module.finrank F E))).Free (graph (F := F) (E := E)) := by
  classical
  letI := Fintype.ofFinite Gal(E/F)
  have hcard : Fintype.card Gal(E/F) = Module.finrank F E :=
    Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank F E)
  let e : Fin (Module.finrank F E) ↪ F :=
    (Fin.castLEEmb hq).trans (Fintype.equivFin F).symm.toEmbedding
  let f : Fin (Module.finrank F E) ↪ Gal(E/F) :=
    (finCongr hcard.symm).toEmbedding.trans (Fintype.equivFin Gal(E/F)).symm.toEmbedding
  have c : Copy (completeBipartiteGraph (Fin (Module.finrank F E))
      (Fin (Module.finrank F E))) (completeBipartiteGraph F Gal(E/F)) := by
    refine ⟨⟨e.sumMap f, ?_⟩, (e.sumMap f).injective⟩
    intro x y h
    cases x <;> cases y <;> simp_all
  intro hfree
  exact hfree ⟨(finiteCompositeGrid h2 hdegree hcomp).comp c⟩

#print axioms normal_difference_injective
#print axioms subgroup_parameters
#print axioms subgroupGrid
#print axioms finiteCompositeGrid
#print axioms finiteComposite_not_free

end Erdos714CompositeNorm
