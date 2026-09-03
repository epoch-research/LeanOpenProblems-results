import Submission.AffineLineColoring

/-!
Finite-field affine representations are compact. If the edges of every finite
induced subgraph can be labeled by vectors over one fixed finite field, with
each triangle labeled by three distinct collinear points, then the whole graph
has a countable triangle-free edge cover. The finite representation hypothesis
is NOT proved here, and this file does not settle Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595AffineCompactness
open Erdos595Work

universe u v w
variable {V : Type u} {K : Type v} [Field K]

/-- The displayed affine ratio is nondegenerate, and the two endpoints differ. -/
def Represents {E : Type*} [AddCommGroup E] [Module K E]
    (G : SimpleGraph V) (f : Sym2 V → E) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
    ∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧
      f s(a,c) = t • f s(a,b) + (1-t) • f s(b,c) ∧ f s(a,b) ≠ f s(b,c)

/-- This implication needs a countable field, not a finite one. -/
theorem cover_of_represents {E : Type*} [AddCommGroup E] [Module K E] [Countable K]
    (G : SimpleGraph V) (f : Sym2 V → E) (hf : Represents (K := K) G f) :
    IsCountableUnionOfTriangleFree G := by
  obtain ⟨c,hc⟩ := Erdos595AffineLine.coloring K E
  apply (countable_union_iff_edge_coloring G).mpr
  refine ⟨c ∘ f,?_⟩
  intro a b d hab had hbd he
  obtain ⟨t,ht0,ht1,hrel,hne⟩ := hf a b d hab had hbd
  exact hne (hc (f s(a,b)) (f s(b,d)) (f s(a,d)) t ht0 ht1 hrel he.2 he.1)

section Quotient
variable {J : Type*} (F : Filter J) (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]

/-- Quotienting the product by eventually-zero vectors retains the fixed scalars. -/
def zeroSubmodule : Submodule K (∀ j, E j) where
  carrier := {x | ∀ᶠ j in F, x j = 0}
  zero_mem' := Filter.Eventually.of_forall (fun _ => rfl)
  add_mem' := by
    intro x y hx hy
    filter_upwards [hx,hy] with j hx hy
    simp only [Pi.add_apply,hx,hy,add_zero]
  smul_mem' := by
    intro t x hx
    filter_upwards [hx] with j hx
    simp only [Pi.smul_apply,hx,smul_zero]

lemma quotient_eq (x y : ∀ j, E j) :
    (zeroSubmodule (K := K) F E).mkQ x = (zeroSubmodule (K := K) F E).mkQ y ↔
      ∀ᶠ j in F, x j = y j := by
  rw [Submodule.mkQ_apply,Submodule.mkQ_apply,Submodule.Quotient.eq]
  change (∀ᶠ j in F, (x-y) j = 0) ↔ _
  simp only [Pi.sub_apply,sub_eq_zero]
end Quotient

/-- Finite-dimensional finite-subgraph representations over ONE fixed finite
field suffice. There is no uniform dimension bound in this hypothesis. -/
theorem cover_of_finite_representations [Finite K] (G : SimpleGraph V)
    (h : ∀ S : Finset V, ∃ n : ℕ, ∃ f : Sym2 S → (Fin n → K),
      Represents (K := K) (G.induce (S : Set V)) f) :
    IsCountableUnionOfTriangleFree G := by
  classical
  choose n f hf using h
  let E (S : Finset V) := Fin (n S) → K
  let val : (S : Finset V) → Sym2 V → E S := fun S => Sym2.lift
    ⟨fun a b => if hab : a ∈ S ∧ b ∈ S then f S s(⟨a,hab.1⟩,⟨b,hab.2⟩) else 0,
      by
        intro a b
        by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
          simp [ha,hb,Sym2.eq_swap]⟩
  have val_mem (S : Finset V) (a b : V) (ha : a ∈ S) (hb : b ∈ S) :
      val S s(a,b) = f S s(⟨a,ha⟩,⟨b,hb⟩) := by
    simp only [val,Sym2.lift_mk,ha,hb,and_self,dif_pos]
  let U : Ultrafilter (Finset V) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset V)) ≤ atTop := Ultrafilter.of_le _
  have hmem (a : V) : ∀ᶠ S in (U : Filter (Finset V)), a ∈ S := by
    apply hU
    exact Filter.eventually_atTop.mpr ⟨{a},fun S hS => hS (by simp)⟩
  let N := zeroSubmodule (K := K) (U : Filter (Finset V)) E
  let lab : Sym2 V → (∀ S, E S) := fun e S => val S e
  let out : Sym2 V → ((∀ S, E S) ⧸ N) := fun e => N.mkQ (lab e)
  apply cover_of_represents (K := K) G out
  intro a b c hab hac hbc
  have hevent : ∀ᶠ S in (U : Filter (Finset V)), ∃ t : K,
      t ≠ 0 ∧ t ≠ 1 ∧ val S s(a,c) = t • val S s(a,b) + (1-t) • val S s(b,c) ∧
        val S s(a,b) ≠ val S s(b,c) := by
    filter_upwards [hmem a,hmem b,hmem c] with S ha hb hc
    simpa only [val_mem S a c ha hc,val_mem S a b ha hb,val_mem S b c hb hc]
      using hf S ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ hab hac hbc
  obtain ⟨t,ht⟩ := Ultrafilter.eventually_exists_iff.mp hevent
  have ht0 : t ≠ 0 := ht.exists.choose_spec.1
  have ht1 : t ≠ 1 := ht.exists.choose_spec.2.1
  refine ⟨t,ht0,ht1,?_,?_⟩
  · change N.mkQ (lab s(a,c)) = t • N.mkQ (lab s(a,b)) + (1-t) • N.mkQ (lab s(b,c))
    rw [← map_smul,← map_smul,← map_add]
    apply (quotient_eq (U : Filter (Finset V)) E _ _).mpr
    exact ht.mono (fun S hS => hS.2.2.1)
  · intro he
    have hEq := (quotient_eq (U : Filter (Finset V)) E (lab s(a,b)) (lab s(b,c))).mp he
    obtain ⟨S,hS,hE⟩ := (ht.and hEq).exists
    exact hS.2.2.2 hE

/-- A uniform finite-field existence theorem for finite K4-free graphs would
therefore disprove the main existential conjecture. That existence theorem
is an explicit hypothesis here, not a claimed result. -/
theorem universal_cover_of_finite_field [Finite K]
    (h : ∀ (A : Type u) [Finite A] (H : SimpleGraph A), H.CliqueFree 4 →
      ∃ n : ℕ, ∃ f : Sym2 A → (Fin n → K), Represents (K := K) H f)
    (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    IsCountableUnionOfTriangleFree G := by
  apply cover_of_finite_representations (K := K) G
  intro S
  apply h S (G.induce (S : Set V))
  exact hG.comap (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G)

#print axioms cover_of_represents
#print axioms cover_of_finite_representations
#print axioms universal_cover_of_finite_field
end Erdos595AffineCompactness
