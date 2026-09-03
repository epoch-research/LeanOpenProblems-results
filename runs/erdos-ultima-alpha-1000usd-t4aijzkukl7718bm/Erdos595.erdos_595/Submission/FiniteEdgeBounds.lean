import Submission.FinitePaletteCompactness

/-!
Compactness with edge-dependent finite bounds. This is stronger than merely
knowing that every finite induced subgraph has some finite coloring. No
construction of these bounds for arbitrary K4-free graphs is asserted.
-/

set_option autoImplicit false
open Set Filter SimpleGraph
namespace Erdos595FiniteEdgeBounds
open Erdos595Work

variable {V : Type*}

def Valid (G : SimpleGraph V) (c : Sym2 V → ℕ) : Prop :=
  ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
    ¬(c s(x,y) = c s(x,z) ∧ c s(x,y) = c s(y,z))

def Bounded (G : SimpleGraph V) (b : Sym2 V → ℕ) : Prop :=
  ∃ c : Sym2 V → ℕ, (∀ e, c e ≤ b e) ∧ Valid G c

/-- A single, edge-dependent finite bound works globally if it works on
every finite induced subgraph. The same `b` must be used throughout. -/
theorem compactness (G : SimpleGraph V) (b : Sym2 V → ℕ)
    (h : ∀ S : Finset V, Bounded (G.induce (S : Set V))
      (fun e => b (e.map Subtype.val))) : Bounded G b := by
  classical
  choose c hc hv using h
  let col : Finset V → Sym2 V → ℕ := fun S => Sym2.lift
    ⟨fun x y => if hxy : x ∈ S ∧ y ∈ S then c S s(⟨x,hxy.1⟩,⟨y,hxy.2⟩)
      else 0, by
      intro x y
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
        simp [hx,hy,Sym2.eq_swap]⟩
  have col_bound (S : Finset V) (e : Sym2 V) : col S e ≤ b e := by
    induction e using Sym2.inductionOn with
    | _ x y =>
      change (if hxy : x ∈ S ∧ y ∈ S then c S s(⟨x,hxy.1⟩,⟨y,hxy.2⟩)
        else 0) ≤ b s(x,y)
      split_ifs with hxy
      · exact hc S s(⟨x,hxy.1⟩,⟨y,hxy.2⟩)
      · exact Nat.zero_le _
  let U : Ultrafilter (Finset V) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset V)) ≤ atTop := Ultrafilter.of_le _
  have hmem (v : V) : ∀ᶠ S in (U : Filter (Finset V)), v ∈ S := by
    apply hU
    exact Filter.eventually_atTop.mpr ⟨{v},fun S hS => hS (by simp)⟩
  have hex (e : Sym2 V) : ∃ k : Fin (b e + 1),
      ∀ᶠ S in (U : Filter (Finset V)), col S e = k.val := by
    apply Ultrafilter.eventually_exists_iff.mp
    exact Filter.Eventually.of_forall fun S =>
      ⟨⟨col S e,Nat.lt_succ_of_le (col_bound S e)⟩,rfl⟩
  choose d hd using hex
  refine ⟨fun e => (d e).val,fun e => Nat.le_of_lt_succ (d e).isLt,?_⟩
  intro x y z hxy hxz hyz hm
  have he := (hd s(x,y)).and ((hd s(x,z)).and (hd s(y,z)))
  obtain ⟨S,hS,hcol⟩ := ((hmem x).and ((hmem y).and (hmem z)) |>.and he).exists
  have hx : x ∈ S := hS.1
  have hy : y ∈ S := hS.2.1
  have hz : z ∈ S := hS.2.2
  have h₁ : c S s(⟨x,hx⟩,⟨y,hy⟩) = (d s(x,y)).val := by
    simpa only [col,Sym2.lift_mk,hx,hy,and_self,dif_pos] using hcol.1
  have h₂ : c S s(⟨x,hx⟩,⟨z,hz⟩) = (d s(x,z)).val := by
    simpa only [col,Sym2.lift_mk,hx,hz,and_self,dif_pos] using hcol.2.1
  have h₃ : c S s(⟨y,hy⟩,⟨z,hz⟩) = (d s(y,z)).val := by
    simpa only [col,Sym2.lift_mk,hy,hz,and_self,dif_pos] using hcol.2.2
  exact hv S ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩ hxy hxz hyz
    ⟨h₁.trans (hm.1.trans h₂.symm),h₁.trans (hm.2.trans h₃.symm)⟩

/-- Restriction and the compactness theorem give an exact criterion for a
fixed bound assignment. -/
theorem compactness_iff (G : SimpleGraph V) (b : Sym2 V → ℕ) :
    Bounded G b ↔ ∀ S : Finset V, Bounded (G.induce (S : Set V))
      (fun e => b (e.map Subtype.val)) := by
  refine ⟨?_,compactness G b⟩
  rintro ⟨c,hc,hv⟩ S
  refine ⟨fun e => c (e.map Subtype.val),fun e => hc _,?_⟩
  intro x y z hxy hxz hyz hm
  exact hv x.val y.val z.val hxy hxz hyz hm

/-- Countable coverability is equivalent to the existence of coherent
finite bounds. The quantifier on `b` is BEFORE the finite-set quantifier. -/
theorem countable_cover_iff (G : SimpleGraph V) :
    IsCountableUnionOfTriangleFree G ↔
      ∃ b : Sym2 V → ℕ, ∀ S : Finset V, Bounded (G.induce (S : Set V))
        (fun e => b (e.map Subtype.val)) := by
  constructor
  · intro h
    obtain ⟨c,hc⟩ := (countable_union_iff_edge_coloring G).mp h
    exact ⟨c,(compactness_iff G c).mp ⟨c,fun _ => le_refl _,hc⟩⟩
  · rintro ⟨b,hb⟩
    obtain ⟨c,_,hc⟩ := compactness G b hb
    exact (countable_union_iff_edge_coloring G).mpr ⟨c,hc⟩

/-- A genuine obstruction defeats every proposed bound assignment on an
already finite induced subgraph. -/
theorem finite_obstruction (G : SimpleGraph V)
    (hG : ¬IsCountableUnionOfTriangleFree G) (b : Sym2 V → ℕ) :
    ∃ S : Finset V, ¬Bounded (G.induce (S : Set V))
      (fun e => b (e.map Subtype.val)) := by
  classical
  by_contra hn
  push_neg at hn
  exact hG ((countable_cover_iff G).mpr ⟨b,hn⟩)

#print axioms compactness
#print axioms countable_cover_iff
#print axioms finite_obstruction
end Erdos595FiniteEdgeBounds
