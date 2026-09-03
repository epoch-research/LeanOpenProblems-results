import Submission.ProfileThinning
import Submission.NormQuadraticCode

/-!
Quadratic coordinate profiles cannot be repaired by retaining a positive
fraction of their edges. This includes the refined norm code. These are
construction obstructions, not a resolution of Erdős 714.
-/

noncomputable section
open SimpleGraph Finset Classical

namespace Erdos714QuadraticProfileThinning

variable {C X F : Type*} [Fintype C] [Fintype X] [Field F] [Fintype F]

/-- The code can be arbitrary across coordinate blocks and nonlinear in its
messages. Only its restriction within each block must be quadratic. -/
theorem fourth_power_bound (f : C → X × F → F)
    (P₀ P₁ P₂ : X → C → F)
    (hf : ∀ c x s, f c (x,s) = P₀ x c + P₁ x c*s + P₂ x c*s^2)
    (H : SimpleGraph (C ⊕ ((X × F) × F))) (hH : H ≤ Erdos714Coding.graph f)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hX : Fintype.card X ≤ Fintype.card F ^ 2)
    (hC : Fintype.card C ≤ Fintype.card F ^ 4) :
    H.edgeFinset.card ^ 4 ≤ 165888 * Fintype.card F ^ 27 := by
  let g (x : X) (c : C) : F × F × F := (P₀ x c,P₁ x c,P₂ x c)
  let ev (_ : X) (p : F × F × F) (s : F) := p.1 + p.2.1*s + p.2.2*s^2
  have he : f = Erdos714ProfileThinning.code g ev := by
    funext c i
    exact hf c i.1 i.2
  apply Erdos714ProfileThinning.critical_scale_bound g ev H
    (by simpa only [← he] using hH) hfree (Fintype.card F)
    (Fintype.card_pos) le_rfl hX hC
  simp [pow_succ, mul_assoc]

end Erdos714QuadraticProfileThinning

namespace Erdos714NormQuadraticCode

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F]

/-- Polar cross coefficient of the quadratic norm adjoint. -/
def polar (z w : E) : F := Algebra.trace F E
  (z ^ Fintype.card F * w ^ (Fintype.card F * Fintype.card F) +
    w ^ Fintype.card F * z ^ (Fintype.card F * Fintype.card F))

lemma base_power_affine (z w : E) (s : F) :
    (z+s • w) ^ Fintype.card F = z ^ Fintype.card F + s • w ^ Fintype.card F := by
  change (FiniteField.frobeniusAlgHom F E) (z+s • w) =
    (FiniteField.frobeniusAlgHom F E) z + s • (FiniteField.frobeniusAlgHom F E) w
  rw [map_add, map_smul]

lemma quadratic_affine (z w : E) (s : F) :
    quadratic (z+s • w) = quadratic (F := F) z + s*polar (F := F) z w + s^2*quadratic (F := F) w := by
  have h₂ : (z+s • w) ^ (Fintype.card F * Fintype.card F) =
      z ^ (Fintype.card F * Fintype.card F) +
        s • w ^ (Fintype.card F * Fintype.card F) := by
    simp only [pow_mul, base_power_affine]
  unfold quadratic polar
  rw [base_power_affine, h₂, add_mul, mul_add, mul_add]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, map_add, map_smul, smul_eq_mul]
  ring

/-- The affine-line expansion is checked at every center, not only at zero. -/
lemma affine_line (p : F × E) (z v : E) (s : F) :
    family p (z+s • v) = family p z +
      (p.1*Algebra.trace F E (v*p.2) + polar (F := F) (z*p.2) (v*p.2))*s +
        quadratic (F := F) (v*p.2)*s^2 := by
  unfold family
  rw [add_mul, smul_mul_assoc, map_add, map_smul, smul_eq_mul, quadratic_affine]
  ring

variable {C X : Type*} [Fintype C] [Fintype X]

/-- Edge-thinning bound for an arbitrary collection of parallel coordinate
lines and an arbitrary selection of message parameters. -/
theorem parallel_lines_thinning (p : C → F × E) (z : X → E) (v : E)
    (H : SimpleGraph (C ⊕ ((X × F) × F)))
    (hH : H ≤ Erdos714Coding.graph (fun c i => family (p c) (z i.1 + i.2 • v)))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hX : Fintype.card X ≤ Fintype.card F ^ 2)
    (hC : Fintype.card C ≤ Fintype.card F ^ 4) :
    H.edgeFinset.card ^ 4 ≤ 165888 * Fintype.card F ^ 27 := by
  exact Erdos714QuadraticProfileThinning.fourth_power_bound _
    (fun x c => family (p c) (z x))
    (fun x c => (p c).1*Algebra.trace F E (v*(p c).2) +
      polar (F := F) (z x*(p c).2) (v*(p c).2))
    (fun _ c => quadratic (F := F) (v*(p c).2))
    (fun c x s => affine_line (p c) (z x) v s) H hH hfree hX hC

variable [Fintype E]

/-- Transport the parallel-line bound back to the original coordinate type.
The coordinate parametrization and its affine identity are explicit. -/
theorem thinning_of_coordinates (p : C → F × E) (coord : (X × F) ≃ E)
    (z : X → E) (v : E) (hc : ∀ x s, coord (x,s) = z x + s • v)
    (H : SimpleGraph (C ⊕ (E × F)))
    (hH : H ≤ Erdos714Coding.graph (fun c t => family (p c) t))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hX : Fintype.card X ≤ Fintype.card F ^ 2)
    (hC : Fintype.card C ≤ Fintype.card F ^ 4) :
    H.edgeFinset.card ^ 4 ≤ 165888 * Fintype.card F ^ 27 := by
  let e := Equiv.sumCongr (Equiv.refl C) (Equiv.prodCongr coord (Equiv.refl F))
  let H' := H.comap e
  have hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H' :=
    Erdos714GraphAveraging.free_comap _ H e.toEmbedding hfree
  have hh : H' ≤ Erdos714Coding.graph (fun c i => family (p c) (z i.1 + i.2 • v)) := by
    intro a b h
    have h' := hH h
    cases a with
    | inl c =>
      cases b with
      | inl d => exact h'
      | inr t =>
        rcases t with ⟨⟨x,s⟩,a⟩
        simpa [e, Erdos714Coding.graph, Erdos714Packing.incidence, hc] using h' 
    | inr t =>
      cases b with
      | inr u => exact h'
      | inl c =>
        rcases t with ⟨⟨x,s⟩,a⟩
        simpa [e, Erdos714Coding.graph, Erdos714Packing.incidence, hc] using h' 
  let iso : H' ≃g H := ⟨e, Iff.rfl⟩
  have hb := parallel_lines_thinning p z v H' hh hf hX hC
  rw [iso.card_edgeFinset_eq] at hb
  exact hb

/-- Every cubic finite-field coordinate space has the required parallel-line
parametrization. Thus the bound applies to the actual original norm-code host,
not merely to a separately assumed coordinate model. -/
theorem cubic_thinning (p : C → F × E)
    (hE : Fintype.card E = Fintype.card F ^ 3)
    (H : SimpleGraph (C ⊕ (E × F)))
    (hH : H ≤ Erdos714Coding.graph (fun c t => family (p c) t))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hC : Fintype.card C ≤ Fintype.card F ^ 4) :
    H.edgeFinset.card ^ 4 ≤ 165888 * Fintype.card F ^ 27 := by
  letI : Module.Finite F E := Module.Finite.of_finite
  have hrank : Module.finrank F E = 3 := by
    apply Nat.pow_right_injective (a := Fintype.card F)
      (by have h := Fintype.one_lt_card (α := F); omega)
    change Fintype.card F ^ Module.finrank F E = Fintype.card F ^ 3
    rw [← Module.card_eq_pow_finrank, hE]
  let d : ((F × F) × F) ≃ₗ[F] E := LinearEquiv.ofFinrankEq _ _ (by
    simp only [Module.finrank_prod, Module.finrank_self, hrank])
  apply thinning_of_coordinates p d.toEquiv (fun x => d (x,0))
    (d ((0,0),1)) _ H hH hfree _ hC
  · intro x s
    change d (x,s) = d (x,0) + s • d ((0,0),1)
    calc
      d (x,s) = d ((x,0) + s • ((0,0),1)) := by congr 1; simp
      _ = _ := by rw [map_add, map_smul]
  · simp [pow_two]

/-- Even arbitrary edge deletions cannot keep a fixed positive fraction of
the intended q^7 incidences for unbounded field order. -/
theorem cubic_size_budget (p : C → F × E)
    (hE : Fintype.card E = Fintype.card F ^ 3)
    (H : SimpleGraph (C ⊕ (E × F)))
    (hH : H ≤ Erdos714Coding.graph (fun c t => family (p c) t))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hC : Fintype.card C ≤ Fintype.card F ^ 4)
    (K : ℕ) (hdense : Fintype.card F ^ 7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have he := cubic_thinning p hE H hH hfree hC
  have h : Fintype.card F ^ 27 * Fintype.card F ≤
      Fintype.card F ^ 27 * (165888*K^4) := by
    calc
      _ = (Fintype.card F ^ 7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(165888*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (by positivity)

end Erdos714NormQuadraticCode

#print axioms Erdos714QuadraticProfileThinning.fourth_power_bound
#print axioms Erdos714NormQuadraticCode.quadratic_affine
#print axioms Erdos714NormQuadraticCode.affine_line
#print axioms Erdos714NormQuadraticCode.parallel_lines_thinning
#print axioms Erdos714NormQuadraticCode.thinning_of_coordinates

#print axioms Erdos714NormQuadraticCode.cubic_thinning
#print axioms Erdos714NormQuadraticCode.cubic_size_budget
