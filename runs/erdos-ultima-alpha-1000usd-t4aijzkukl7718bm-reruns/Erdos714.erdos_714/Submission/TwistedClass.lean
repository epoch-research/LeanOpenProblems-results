import Submission.EdgeAveraging

/-!
Twisted-conjugacy hosts: edge transitivity and an abelian-coboundary obstruction.
This is not a proof or disproof of the balanced Zarankiewicz conjecture.
-/

open SimpleGraph Classical

namespace Erdos714TwistedClass

variable {Γ : Type*} [Group Γ]

/-- The bipartite graph of the twisted conjugacy class of the identity. -/
def graph (σ : Γ →* Γ) : SimpleGraph (Γ ⊕ Γ) where
  Adj x y := match x,y with
    | .inl g, .inr h => ∃ k : Γ, g⁻¹*h = k⁻¹*σ k
    | .inr h, .inl g => ∃ k : Γ, g⁻¹*h = k⁻¹*σ k
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

lemma relative_transform (σ : Γ →* Γ) (p a g h : Γ) :
    (p*g*a)⁻¹*(p*h*σ a) = a⁻¹*(g⁻¹*h)*σ a := by group

/-- Twisted right translation, combined with ordinary left translation. -/
def transform (σ : Γ →* Γ) (p a : Γ) : graph σ ≃g graph σ where
  toEquiv := Equiv.sumCongr ((Equiv.mulLeft p).trans (Equiv.mulRight a))
    ((Equiv.mulLeft p).trans (Equiv.mulRight (σ a)))
  map_rel_iff' := by
    intro x y
    have hh (g h : Γ) :
        (∃ k, (p*g*a)⁻¹*(p*h*σ a) = k⁻¹*σ k) ↔ ∃ k, g⁻¹*h = k⁻¹*σ k := by
      rw [relative_transform]
      constructor
      · rintro ⟨k,hk⟩
        refine ⟨k*a⁻¹, ?_⟩
        have he := congrArg (fun z : Γ => a*z*(σ a)⁻¹) hk
        simp only [map_mul, map_inv, mul_inv_rev]
        calc
          g⁻¹*h = a*(k⁻¹*σ k)*(σ a)⁻¹ := by
            simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using he
          _ = _ := by group
      · rintro ⟨k,hk⟩
        refine ⟨k*a, ?_⟩
        rw [hk, map_mul]
        group
    cases x with
    | inl g =>
      cases y with
      | inl h => rfl
      | inr h => exact hh g h
    | inr h =>
      cases y with
      | inl g => exact hh g h
      | inr g => rfl

def canonicalEdge (σ : Γ →* Γ) : (graph σ).edgeSet :=
  ⟨s(Sum.inl 1, Sum.inr 1), by exact ⟨1, by simp⟩⟩

lemma cross_from_canonical (σ : Γ →* Γ) (g h : Γ)
    (hadj : (graph σ).Adj (.inl g) (.inr h)) :
    ∃ f : graph σ ≃g graph σ,
      Sym2.map f (canonicalEdge σ).val = s(Sum.inl g, Sum.inr h) := by
  obtain ⟨k,hk⟩ := hadj
  refine ⟨transform σ (g*k⁻¹) k, ?_⟩
  change s(Sum.inl (g*k⁻¹*1*k), Sum.inr (g*k⁻¹*1*σ k)) = s(Sum.inl g, Sum.inr h)
  have hh : g*k⁻¹*σ k = h := by rw [mul_assoc, ← hk]; group
  simp only [mul_one, inv_mul_cancel_right, hh]

lemma from_canonical (σ : Γ →* Γ) (e : (graph σ).edgeSet) :
    ∃ f : graph σ ≃g graph σ, f.mapEdgeSet (canonicalEdge σ) = e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
    cases x with
    | inl g =>
      cases y with
      | inl h => exact False.elim he
      | inr h =>
        obtain ⟨f,hf⟩ := cross_from_canonical σ g h he
        exact ⟨f, Subtype.ext hf⟩
    | inr h =>
      cases y with
      | inl g =>
        obtain ⟨f,hf⟩ := cross_from_canonical σ g h he
        refine ⟨f, Subtype.ext ?_⟩
        simpa only [Sym2.eq_swap] using hf
      | inr g => exact False.elim he

/-- Surjectivity of the twisting map is not needed for edge transitivity. -/
theorem edge_transitive (σ : Γ →* Γ) : Erdos714GraphAveraging.EdgeTransitive (graph σ) := by
  intro x y
  obtain ⟨fx,hx⟩ := from_canonical σ x
  obtain ⟨fy,hy⟩ := from_canonical σ y
  refine ⟨fy * fx⁻¹, ?_⟩
  change (Erdos714GraphAveraging.edgeAction (graph σ)) (fy*fx⁻¹) x = y
  rw [map_mul, map_inv]
  change fy.mapEdgeSet (fx.mapEdgeSet.symm x) = y
  rw [← hx, Equiv.symm_apply_apply]
  exact hy

/-- Any subgroup contained in the connection set supplies a complete bipartite graph. -/
def subgroupCopy (σ : Γ →* Γ) (U : Subgroup Γ)
    (hU : ∀ u ∈ U, ∃ k : Γ, u = k⁻¹*σ k) :
    Copy (completeBipartiteGraph U U) (graph σ) where
  toHom := {
    toFun := Sum.map Subtype.val Subtype.val
    map_rel' := by
      intro x y h
      cases x with
      | inl u =>
        cases y with
        | inl v => simp at h
        | inr v => exact hU _ (U.mul_mem (U.inv_mem u.property) v.property)
      | inr v =>
        cases y with
        | inl u => exact hU _ (U.mul_mem (U.inv_mem u.property) v.property)
        | inr u => simp at h }
  injective' := Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩

variable {A : Type*} [CommGroup A]

/-- On an abelian group, the coboundary map is a homomorphism. -/
def coboundary (τ : A →* A) : A →* A where
  toFun := fun a => a⁻¹*τ a
  map_one' := by simp
  map_mul' a b := by simp only [mul_inv_rev, map_mul]; ac_rfl

/-- Coboundaries in an invariant abelian subgroup lie in the ambient connection set. -/
theorem abelian_image (σ : Γ →* Γ) (τ : A →* A) (ι : A →* Γ)
    (hι : ∀ a, σ (ι a) = ι (τ a)) :
    ∀ u ∈ (ι.comp (coboundary τ)).range, ∃ k : Γ, u = k⁻¹*σ k := by
  intro u hu
  obtain ⟨a, rfl⟩ := hu
  refine ⟨ι a, ?_⟩
  change ι (a⁻¹*τ a) = (ι a)⁻¹*σ (ι a)
  rw [map_mul, map_inv, hι]

/-- The complete bipartite graph on the coboundary image embeds in the host. -/
def abelianCopy (σ : Γ →* Γ) (τ : A →* A) (ι : A →* Γ)
    (hι : ∀ a, σ (ι a) = ι (τ a)) :
    Copy (completeBipartiteGraph (ι.comp (coboundary τ)).range
      (ι.comp (coboundary τ)).range) (graph σ) :=
  subgroupCopy σ _ (abelian_image σ τ ι hι)

/-- No arbitrary edge thinning can avoid the usual biclique averaging bound. -/
theorem thinning_bound [Fintype Γ] (σ : Γ →* Γ) (τ : A →* A) (ι : A →* Γ)
    (hι : ∀ a, σ (ι a) = ι (τ a)) (H : SimpleGraph (Γ ⊕ Γ)) (r : ℕ)
    (hHG : H ≤ graph σ) (hH : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    Fintype.card (ι.comp (coboundary τ)).range ^ 2 * H.edgeFinset.card ≤
      extremalNumber (2*Fintype.card (ι.comp (coboundary τ)).range)
        (completeBipartiteGraph (Fin r) (Fin r)) * (graph σ).edgeFinset.card := by
  have h := Erdos714GraphAveraging.edge_transitive_bound
    (completeBipartiteGraph (Fin r) (Fin r)) H (graph σ)
    (completeBipartiteGraph (ι.comp (coboundary τ)).range (ι.comp (coboundary τ)).range)
    (abelianCopy σ τ ι hι) hHG hH (edge_transitive σ)
  simpa [Erdos714GraphAveraging.complete_bipartite_edges, Fintype.card_sum, pow_two, two_mul] using h

end Erdos714TwistedClass

#print axioms Erdos714TwistedClass.edge_transitive
#print axioms Erdos714TwistedClass.abelianCopy
#print axioms Erdos714TwistedClass.thinning_bound

namespace Erdos714TwistedField

variable {F : Type*} [Field F]

/-- The additive coboundary of a field endomorphism. -/
def difference (ρ : F →+* F) : F →+ F := ρ.toAddMonoidHom - AddMonoidHom.id F

@[simp] lemma difference_apply (ρ : F →+* F) (x : F) :
    difference ρ x = ρ x - x := rfl

/-- Two coboundary observations recover the original field element. -/
theorem difference_pair_injective (ρ : F →+* F) (a : F) (ha : ρ a ≠ a) :
    Function.Injective (fun x => (difference ρ x, difference ρ (a*x))) := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change ρ x - x = ρ y - y at h₁
  change ρ (a*x) - a*x = ρ (a*y) - a*y at h₂
  simp only [map_mul] at h₂
  have he : (ρ a-a)*(x-y) = 0 := by linear_combination h₂ - ρ a*h₁
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha))

/-- A nontrivial endomorphism of a finite field has a large coboundary image. -/
theorem difference_image_bound [Fintype F] (ρ : F →+* F) (a : F) (ha : ρ a ≠ a) :
    Fintype.card F ≤ (Fintype.card (difference ρ).range)^2 := by
  classical
  let f : F → (difference ρ).range × (difference ρ).range := fun x =>
    (⟨difference ρ x, ⟨x,rfl⟩⟩, ⟨difference ρ (a*x), ⟨a*x,rfl⟩⟩)
  have hf : Function.Injective f := by
    intro x y h
    apply difference_pair_injective ρ a ha
    exact congrArg (fun p : (difference ρ).range × (difference ρ).range => (p.1.val,p.2.val)) h
  simpa [Fintype.card_prod, pow_two] using Fintype.card_le_of_injective f hf

end Erdos714TwistedField

#print axioms Erdos714TwistedField.difference_pair_injective
#print axioms Erdos714TwistedField.difference_image_bound

namespace Erdos714TwistedSL2

open scoped MatrixGroups
open Erdos714TwistedField

variable {F : Type*} [Field F]

/-- The additive root subgroup, written as a multiplicative homomorphism. -/
def unipotent : Multiplicative F →* SL(2,F) where
  toFun x := ⟨!![1,Multiplicative.toAdd x; 0,1], by simp [Matrix.det_fin_two]⟩
  map_one' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]

lemma unipotent_injective : Function.Injective (unipotent (F := F)) := by
  intro x y h
  have he := congrArg (fun g : SL(2,F) => g 0 1) h
  exact he

/-- Entrywise application of the field endomorphism preserves the root subgroup. -/
lemma compatibility (ρ : F →+* F) (x : Multiplicative F) :
    Matrix.SpecialLinearGroup.map (n := Fin 2) ρ (unipotent x) =
      unipotent (ρ.toAddMonoidHom.toMultiplicative x) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, unipotent]

/-- The root-subgroup coboundaries inside `SL(2,F)`. -/
def image (ρ : F →+* F) : Subgroup SL(2,F) :=
  (unipotent.comp (difference ρ).toMultiplicative).range

lemma image_in_connection (ρ : F →+* F) :
    ∀ u ∈ image ρ, ∃ k : SL(2,F),
      u = k⁻¹ * Matrix.SpecialLinearGroup.map (n := Fin 2) ρ k := by
  intro u hu
  obtain ⟨x, rfl⟩ := hu
  refine ⟨unipotent x, ?_⟩
  change unipotent ((difference ρ).toMultiplicative x) =
    (unipotent x)⁻¹ * Matrix.SpecialLinearGroup.map (n := Fin 2) ρ (unipotent x)
  rw [compatibility, ← map_inv, ← map_mul]
  congr 1
  change ρ (Multiplicative.toAdd x) - Multiplicative.toAdd x =
    -Multiplicative.toAdd x + ρ (Multiplicative.toAdd x)
  abel

/-- A complete bipartite subgraph whose sides are the full additive-difference image. -/
def imageCopy (ρ : F →+* F) :
    Copy (completeBipartiteGraph (image ρ) (image ρ))
      (Erdos714TwistedClass.graph (Matrix.SpecialLinearGroup.map (n := Fin 2) ρ)) :=
  Erdos714TwistedClass.subgroupCopy _ _ (image_in_connection ρ)

/-- This biclique grows at least as the square root of the coefficient field. -/
theorem image_card_bound [Fintype F] (ρ : F →+* F) (a : F) (ha : ρ a ≠ a) :
    Fintype.card F ≤ (Fintype.card (image ρ))^2 := by
  classical
  let f : F → image ρ := fun x =>
    ⟨unipotent (Multiplicative.ofAdd (difference ρ x)), ⟨Multiplicative.ofAdd x, rfl⟩⟩
  have hpair : Function.Injective (fun x => (f x, f (a*x))) := by
    intro x y h
    apply difference_pair_injective ρ a ha
    apply Prod.ext
    · have he := congrArg (fun p : image ρ × image ρ => p.1.val) h
      exact unipotent_injective he
    · have he := congrArg (fun p : image ρ × image ρ => p.2.val) h
      exact unipotent_injective he
  simpa [Fintype.card_prod, pow_two] using
    Fintype.card_le_of_injective (fun x => (f x, f (a*x))) hpair


/-- Every sufficiently large coefficient field gives an actual forbidden biclique. -/
theorem not_free [Fintype F] (ρ : F →+* F) (a : F) (ha : ρ a ≠ a) (r : ℕ)
    (hF : (r-1)^2 < Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free
      (Erdos714TwistedClass.graph (Matrix.SpecialLinearGroup.map (n := Fin 2) ρ)) := by
  classical
  have hc : r ≤ Fintype.card (image ρ) := by
    by_contra! h
    have hle : Fintype.card (image ρ) ≤ r-1 := by omega
    have hs := Nat.pow_le_pow_left hle 2
    have hb := image_card_bound ρ a ha
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin r) (β := image ρ) (by simpa using hc)
  let c : Copy (completeBipartiteGraph (Fin r) (Fin r))
      (completeBipartiteGraph (image ρ) (image ρ)) := {
    toHom := {
      toFun := e.sumMap e
      map_rel' := by
        intro x y h
        cases x <;> cases y <;> simp_all }
    injective' := (e.sumMap e).injective }
  intro hfree
  exact hfree ⟨(imageCopy ρ).comp c⟩

/-- Arbitrary edge thinnings of the semilinear `SL(2)` host obey the grid bound. -/
theorem thinning_bound [Fintype F] (ρ : F →+* F) (H : SimpleGraph (SL(2,F) ⊕ SL(2,F)))
    (r : ℕ) (hHG : H ≤ Erdos714TwistedClass.graph (Matrix.SpecialLinearGroup.map (n := Fin 2) ρ))
    (hH : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    Fintype.card (image ρ)^2 * H.edgeFinset.card ≤
      extremalNumber (2*Fintype.card (image ρ)) (completeBipartiteGraph (Fin r) (Fin r)) *
        (Erdos714TwistedClass.graph (Matrix.SpecialLinearGroup.map (n := Fin 2) ρ)).edgeFinset.card := by
  classical
  have h := Erdos714GraphAveraging.edge_transitive_bound
    (completeBipartiteGraph (Fin r) (Fin r)) H
    (Erdos714TwistedClass.graph (Matrix.SpecialLinearGroup.map (n := Fin 2) ρ))
    (completeBipartiteGraph (image ρ) (image ρ)) (imageCopy ρ) hHG hH
    (Erdos714TwistedClass.edge_transitive _)
  simpa [Erdos714GraphAveraging.complete_bipartite_edges, Fintype.card_sum, pow_two, two_mul] using h

end Erdos714TwistedSL2

#print axioms Erdos714TwistedSL2.imageCopy
#print axioms Erdos714TwistedSL2.image_card_bound
#print axioms Erdos714TwistedSL2.thinning_bound

#print axioms Erdos714TwistedSL2.not_free
