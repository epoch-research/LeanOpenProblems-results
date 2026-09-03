import Submission.PrescribedCountableProperExtension
import Submission.AmalgamationCover

/-!
Literal extension using only the old boundary. This is a preservation
criterion, not a solution to Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595BoundaryExtension
open Erdos595FiniteAdapted Erdos595Work
open Erdos595PrescribedCountableProper (extend)
variable {V W X : Type*}

theorem extend_valid (G : SimpleGraph (V ⊕ W))
    (c : Sym2 V → ℕ) (d : Sym2 W → ℕ)
    (f : V → ℕ)
    (hf : ∀ a b w, G.Adj (.inl a) (.inl b) →
      G.Adj (.inl a) (.inr w) → G.Adj (.inl b) (.inr w) → f a ≠ f b)
    (hc : Valid (G.comap Sum.inl) c) (hd : Valid (G.comap Sum.inr) d) :
    Valid G (extend c d f) := by
  intro a b t hab hat hbt heq
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      cases t with
      | inl t => exact hc a b t hab hat hbt heq
      | inr t =>
        change c s(a,b) = 2 * f a + 1 ∧ c s(a,b) = 2 * f b + 1 at heq
        apply hf a b t hab hat hbt
        omega
    | inr b =>
      cases t with
      | inl t =>
        change 2 * f a + 1 = c s(a,t) ∧ 2 * f a + 1 = 2 * f t + 1 at heq
        apply hf a t b hat hab hbt.symm
        omega
      | inr t =>
        change 2 * f a + 1 = 2 * f a + 1 ∧ 2 * f a + 1 = 2 * d s(b,t) at heq
        omega
  | inr a =>
    cases b with
    | inl b =>
      cases t with
      | inl t =>
        change 2 * f b + 1 = 2 * f t + 1 ∧ 2 * f b + 1 = c s(b,t) at heq
        apply hf b t a hbt hab.symm hat.symm
        omega
      | inr t =>
        change 2 * f b + 1 = 2 * d s(a,t) ∧ 2 * f b + 1 = 2 * f b + 1 at heq
        omega
    | inr b =>
      cases t with
      | inl t =>
        change 2 * d s(a,b) = 2 * f t + 1 ∧ 2 * d s(a,b) = 2 * f t + 1 at heq
        omega
      | inr t =>
        change 2 * d s(a,b) = 2 * d s(a,t) ∧ 2 * d s(a,b) = 2 * d s(b,t) at heq
        exact hd a b t hab hat hbt ⟨by omega,by omega⟩

theorem exists_extension (G : SimpleGraph (V ⊕ W)) (c : Sym2 V → ℕ)
    (hc : Valid (G.comap Sum.inl) c)
    (f : V → ℕ)
    (hf : ∀ a b w, G.Adj (.inl a) (.inl b) →
      G.Adj (.inl a) (.inr w) → G.Adj (.inl b) (.inr w) → f a ≠ f b)
    (hnew : IsCountableUnionOfTriangleFree (G.comap Sum.inr)) :
    ∃ e : Sym2 (V ⊕ W) → ℕ, Valid G e ∧
      ∀ a b : V, e s(Sum.inl a,Sum.inl b) = c s(a,b) := by
  obtain ⟨d,hd⟩ := (countable_union_iff_edge_coloring _).mp hnew
  exact ⟨extend c d f,extend_valid G c d f hf hc hd,fun _ _ => rfl⟩

/-- The same result for an arbitrary induced embedding. The labeling only separates old adjacent
vertices that share a neighbor outside the old copy. -/
theorem along_embedding (H : SimpleGraph V) (G : SimpleGraph X)
    (f : H ↪g G) (c : Sym2 V → ℕ) (hc : Valid H c)
    (label : V → ℕ)
    (hlabel : ∀ a b w, w ∉ Set.range f → H.Adj a b →
      G.Adj (f a) w → G.Adj (f b) w → label a ≠ label b)
    (hG : IsCountableUnionOfTriangleFree G) :
    ∃ e : Sym2 X → ℕ, Valid G e ∧ ∀ a b, e s(f a,f b) = c s(a,b) := by
  classical
  let R : Set X := Set.range f
  let t : V ⊕ {x : X // x ∉ R} ≃ X :=
    (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl {x : X // x ∉ R})).trans
      (Equiv.Set.sumCompl R)
  have hleft : (G.comap t).comap Sum.inl = H := by
    ext a b
    exact f.map_rel_iff
  have hnew : IsCountableUnionOfTriangleFree ((G.comap t).comap Sum.inr) :=
    countable_union_of_hom (SimpleGraph.Hom.comap _ _)
      (countable_union_of_hom (SimpleGraph.Hom.comap _ _) hG)
  obtain ⟨e,he,hold⟩ := exists_extension (G.comap t) c
    (hleft.symm ▸ hc) label (by
      intro a b w hab haw hbw
      exact hlabel a b w.val w.property (hleft ▸ hab) haw hbw) hnew
  refine ⟨fun p => e (p.map t.symm),?_,?_⟩
  · intro a b z hab haz hbz hm
    apply he (t.symm a) (t.symm b) (t.symm z)
    · simpa only [SimpleGraph.comap_adj,t.apply_symm_apply] using hab
    · simpa only [SimpleGraph.comap_adj,t.apply_symm_apply] using haz
    · simpa only [SimpleGraph.comap_adj,t.apply_symm_apply] using hbz
    · exact hm
  · intro a b
    have ha : t.symm (f a) = Sum.inl a := t.symm_apply_apply (Sum.inl a)
    have hb : t.symm (f b) = Sum.inl b := t.symm_apply_apply (Sum.inl b)
    change e s(t.symm (f a),t.symm (f b)) = c s(a,b)
    rw [ha,hb]
    exact hold a b

/-- The boundary of an induced copy consists of its vertices that touch
some vertex outside that copy. -/
def boundary (H : SimpleGraph V) (G : SimpleGraph X) (f : H ↪g G) : Set V :=
  {a | ∃ w, w ∉ Set.range f ∧ G.Adj (f a) w}

theorem along_boundary (H : SimpleGraph V) (G : SimpleGraph X)
    (f : H ↪g G) (c : Sym2 V → ℕ) (hc : Valid H c)
    (hproper : Nonempty ((H.induce (boundary H G f)).Coloring ℕ))
    (hG : IsCountableUnionOfTriangleFree G) :
    ∃ e : Sym2 X → ℕ, Valid G e ∧ ∀ a b, e s(f a,f b) = c s(a,b) := by
  classical
  obtain ⟨k⟩ := hproper
  let label : V → ℕ := fun a => if h : a ∈ boundary H G f then k ⟨a,h⟩ else 0
  apply along_embedding H G f c hc label ?_ hG
  intro a b w hw hab haw hbw
  have ha : a ∈ boundary H G f := ⟨w,hw,haw⟩
  have hb : b ∈ boundary H G f := ⟨w,hw,hbw⟩
  simp only [label,dif_pos ha,dif_pos hb]
  exact k.valid hab

open Erdos595FiniteFolkmanAmalgamation
variable {A B I : Type*}

theorem amalgamation (H : SimpleGraph A) (K : SimpleGraph B)
    (D : Set A) (e : I → H.induce D ↪g K) (i₀ : I)
    (c : Sym2 A → ℕ) (hc : Valid H c)
    (hK : Nonempty (K.Coloring ℕ)) :
    ∃ d : Sym2 (Vertex D (B := B) (I := I)) → ℕ,
      Valid (graph H K D e) d ∧
      ∀ a b, d s(copy H K D e i₀ a,copy H K D e i₀ b) = c s(a,b) := by
  classical
  obtain ⟨k⟩ := hK
  have hcoverH := (countable_union_iff_edge_coloring H).mpr ⟨c,hc⟩
  have hcoverK : IsCountableUnionOfTriangleFree K := by
    apply countable_union_of_coloring K
    refine SimpleGraph.Coloring.mk (fun a n => if k a = n then 1 else 0) ?_
    intro a b hab he
    have hne := k.valid hab
    have hh := congrFun he (k a)
    simp [Ne.symm hne] at hh
  have hcover := Erdos595AmalgamationCover.countable_cover H K D e hcoverH hcoverK
  let label : A → ℕ := fun a => if h : a ∈ D then k (e i₀ ⟨a,h⟩) else 0
  apply along_embedding H (graph H K D e) (copyEmbedding H K D e i₀)
    c hc label ?_ hcover
  intro a b w hw hab haw hbw
  have memD (a : A) (haw : (graph H K D e).Adj (copy H K D e i₀ a) w) :
      a ∈ D := by
    by_contra ha
    rw [copy_of_not_mem H K D e i₀ a ha] at haw
    exact hw (neighbor_private H K D e haw)
  have ha := memD a haw
  have hb := memD b hbw
  simp only [label,dif_pos ha,dif_pos hb]
  exact k.valid ((e i₀).map_rel_iff.mpr hab)

#print axioms exists_extension
#print axioms along_embedding
#print axioms along_boundary
#print axioms amalgamation
end Erdos595BoundaryExtension
