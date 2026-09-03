import Submission.BinaryNormFilter
import Submission.BinaryTranslationThinning

/-! Translation-invariant, but otherwise arbitrary, thinnings of actual
binary cubic norm graphs. This is not a disproof of Erdős714. -/
noncomputable section
open Finset SimpleGraph Classical
namespace Erdos714BinaryNormThinning
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [CharP E 2] [Fintype F] [Fintype E]

/-- The full ordinary norm graph. Zero sums never satisfy its norm equation. -/
abbrev host : SimpleGraph (Bool × (E × Fˣ)) :=
  Erdos714BinaryNormFilter.graph (F := F) (univ : Finset E)

omit [FiniteDimensional F E] [Fintype F] in
/-- The full host has the translation symmetry. An arbitrary subgraph need not. -/
theorem host_invariant : Erdos714BinaryTranslation.Invariant (host (F := F) (E := E)) := by
  intro z u v
  change (u.1 ≠ v.1 ∧ (u.2.1+z)+(v.2.1+z) ∈ univ ∧
    Algebra.norm F ((u.2.1+z)+(v.2.1+z)) = (u.2.2 : F)*(v.2.2 : F)) ↔
    (u.1 ≠ v.1 ∧ u.2.1+v.2.1 ∈ univ ∧
    Algebra.norm F (u.2.1+v.2.1) = (u.2.2 : F)*(v.2.2 : F))
  have hz : (u.2.1+z)+(v.2.1+z) = u.2.1+v.2.1 := by
    calc
      _ = (u.2.1+v.2.1)+(z+z) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
  rw [hz]

omit [FiniteDimensional F E] in
/-- No constant-density translation-invariant thinning at the critical cubic
scale is K44-free. The retained rule may depend on both weights. -/
theorem subgraph_bound (H : SimpleGraph (Bool × (E × Fˣ)))
    (hH : H ≤ host (F := F) (E := E))
    (hI : Erdos714BinaryTranslation.Invariant H)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hdim : Module.finrank F E = 3) :
    (H.edgeFinset.card : ℝ)^2 ≤ 3*(Fintype.card F : ℝ)^13 := by
  refine Erdos714BinaryTranslation.cubic_scale_bound H hI ?_ hfree (Fintype.card F) ?_ ?_
  · intro u v huv
    exact (hH huv).1
  · rw [Module.card_eq_pow_finrank (K := F) (V := E), hdim]
  · rw [Fintype.card_units]
    exact Nat.sub_le _ _

omit [CharP E 2] [Fintype F] in
/-- Deleting zero from the allowed sums changes no actual norm edge. -/
theorem host_eq_nonzero : host (F := F) (E := E) =
    Erdos714BinaryNormFilter.graph (F := F) (univ.erase (0 : E)) := by
  ext u v
  simp only [host, Erdos714BinaryNormFilter.graph, mem_univ, true_and, mem_erase,
    and_true]
  constructor
  · rintro ⟨hs,hn⟩
    refine ⟨hs,?_,hn⟩
    intro hz
    rw [hz, Algebra.norm_zero] at hn
    exact (mul_ne_zero u.2.2.ne_zero v.2.2.ne_zero) hn.symm
  · exact fun h => ⟨h.1,h.2.2⟩

omit [CharP E 2] in
/-- Exact original host edge count. -/
theorem host_edges (hdim : Module.finrank F E = 3) :
    (host (F := F) (E := E)).edgeFinset.card =
      Fintype.card F^3*(Fintype.card F-1)*(Fintype.card F^3-1) := by
  rw [host_eq_nonzero, Erdos714BinaryNormFilter.edge_count _ (by simp)]
  simp only [card_erase_of_mem (mem_univ _), card_univ,
    Module.card_eq_pow_finrank (K := F) (V := E), hdim]

/-- A quantitative vanishing-density consequence. This is conditional on
translation invariance of H itself, not only that of its ambient host. -/
theorem relative_bound (H : SimpleGraph (Bool × (E × Fˣ)))
    (hH : H ≤ host (F := F) (E := E))
    (hI : Erdos714BinaryTranslation.Invariant H)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hdim : Module.finrank F E = 3) :
    (Fintype.card F : ℝ) * (H.edgeFinset.card : ℝ)^2 ≤
      48 * ((host (F := F) (E := E)).edgeFinset.card : ℝ)^2 := by
  let q : ℝ := Fintype.card F
  have hq : 2 ≤ q := by
    have h : 2 ≤ Fintype.card F := Fintype.one_lt_card (α := F)
    dsimp [q]
    exact_mod_cast h
  have hq3 : (2 : ℝ) ≤ q^3 := by
    have h : (2 : ℝ)^3 ≤ q^3 := by gcongr
    norm_num at h
    linarith
  have he : ((host (F := F) (E := E)).edgeFinset.card : ℝ) =
      q^3*(q-1)*(q^3-1) := by
    rw [host_edges hdim]
    push_cast [Nat.cast_sub (by have := Fintype.one_lt_card (α := F); omega :
      1 ≤ Fintype.card F)]
    have h3 : 1 ≤ Fintype.card F^3 := one_le_pow₀ (by exact Fintype.card_pos)
    rw [Nat.cast_sub h3]
    push_cast
    rfl
  have hlo : q^7 ≤ 4*((host (F := F) (E := E)).edgeFinset.card : ℝ) := by
    rw [he]
    have hqm1 : 0 ≤ q-1 := by linarith
    have h : q^3 * q * q^3 ≤ q^3 * (2*(q-1)) * (2*(q^3-1)) := by
      gcongr <;> first | positivity | linarith
    nlinarith
  have hsq := sq_le_sq₀ (by positivity : 0 ≤ q^7)
    (by positivity : 0 ≤ 4*((host (F := F) (E := E)).edgeFinset.card : ℝ))
  have hsq' := hsq.mpr hlo
  have hb := subgraph_bound H hH hI hfree hdim
  change (H.edgeFinset.card : ℝ)^2 ≤ 3*q^13 at hb
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ q by positivity)
  change q*(H.edgeFinset.card : ℝ)^2 ≤ _
  nlinarith

#print axioms host_invariant
#print axioms subgraph_bound
#print axioms host_edges
#print axioms relative_bound
end Erdos714BinaryNormThinning
