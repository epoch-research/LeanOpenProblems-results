import Submission.InfiniteTriangleRamsey
import Submission.FiniteFolkmanAmalgamation

/-!
An infinitary induced bipartite Ramsey lemma for the three-edge path.
The palette may have any cardinality. This is a genuine partite tool, but
it does not homogenize arbitrary infinite bipartite graphs or infinitely
many pairs of parts, and does not settle Erdős 595.
-/

open Set SimpleGraph
namespace Erdos595HalfGraphRamsey
open Erdos595InfiniteTriangleRamsey

universe u

variable {A : Type*} [LinearOrder A]

/-- The bipartite half-graph, with distinct left and right copies. -/
def halfGraph (A : Type*) [LinearOrder A] : SimpleGraph (A ⊕ A) where
  Adj
    | .inl a, .inr b => a < b
    | .inr b, .inl a => a < b
    | _, _ => False
  symm := by intro x y h; cases x <;> cases y <;> exact h
  loopless := by intro x h; cases x <;> exact h

/-- The host itself is bipartite, hence triangle-free. -/
theorem halfGraph_cliqueFree : (halfGraph A).CliqueFree 3 := by
  intro s hs
  obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  cases x <;> cases y <;> cases z <;>
    first | exact hxy | exact hxz | exact hyz

/-- Left 0--right 0--left 1--right 1, with the left labels reversed:
the three edges are L0-R0, L0-R1, L1-R1. -/
def path : SimpleGraph (Fin 2 ⊕ Fin 2) where
  Adj
    | .inl i, .inr j => i ≤ j
    | .inr j, .inl i => i ≤ j
    | _, _ => False
  symm := by intro x y h; cases x <;> cases y <;> exact h
  loopless := by intro x h; cases x <;> exact h

def pathMap (a b d : A) : Fin 2 ⊕ Fin 2 → A ⊕ A
  | .inl i => .inl (if i = 0 then a else b)
  | .inr j => .inr (if j = 0 then b else d)

lemma pathMap_injective {a b d : A} (hab : a < b) (hbd : b < d) :
    Function.Injective (pathMap a b d) := by
  intro x y he
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      fin_cases i <;> fin_cases j <;> simp_all [pathMap, hab.ne, hab.ne.symm]
    | inr j => simp [pathMap] at he
  | inr i =>
    cases y with
    | inl j => simp [pathMap] at he
    | inr j =>
      fin_cases i <;> fin_cases j <;> simp_all [pathMap, hbd.ne, hbd.ne.symm]

lemma pathMap_rel {a b d : A} (hab : a < b) (hbd : b < d)
    (x y : Fin 2 ⊕ Fin 2) :
    (halfGraph A).Adj (pathMap a b d x) (pathMap a b d y) ↔ path.Adj x y := by
  cases x with
  | inl i =>
    cases y with
    | inl j => simp [pathMap, halfGraph, path]
    | inr j =>
      fin_cases i <;> fin_cases j <;> simp [pathMap,halfGraph,path,hab,hbd,hab.trans hbd]
  | inr i =>
    cases y with
    | inl j =>
      fin_cases i <;> fin_cases j <;> simp [pathMap,halfGraph,path,hab,hbd,hab.trans hbd]
    | inr j => simp [pathMap, halfGraph, path]

def pathEmbedding {a b d : A} (hab : a < b) (hbd : b < d) : path ↪g halfGraph A where
  toFun := pathMap a b d
  inj' := pathMap_injective hab hbd
  map_rel_iff' := pathMap_rel hab hbd _ _

/-- The Erdős--Rado tree applies to ordered pairs directly; no symmetry
of the coloring is required in this version. -/
theorem ordered_triangle {C : Type*} [WellFoundedLT A]
    (hA : ∀ f : A → Code C, ¬Function.Injective f) (c : A → A → C) :
    ∃ a b d, a < b ∧ b < d ∧ c a b = c a d ∧ c a b = c b d := by
  classical
  by_contra hn
  have hc : Valid c := by
    intro a b d hab hbd he
    exact hn ⟨a,b,d,hab,hbd,he⟩
  exact hA (code c) (code_injective c hc)

/-- Three monochromatic ordered pairs give an induced, part-preserving
monochromatic copy of the three-edge path. -/
theorem mono_path_of_triple {C : Type*} (c : Sym2 (A ⊕ A) → C)
    {a b d : A} (hab : a < b) (hbd : b < d)
    (h₀ : c s(Sum.inl a,Sum.inr b) = c s(Sum.inl a,Sum.inr d))
    (h₁ : c s(Sum.inl a,Sum.inr b) = c s(Sum.inl b,Sum.inr d)) :
    ∀ x y, path.Adj x y →
      c s(pathEmbedding hab hbd x,pathEmbedding hab hbd y) = c s(Sum.inl a,Sum.inr b) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => exact hxy.elim
    | inr j =>
      fin_cases i <;> fin_cases j <;>
        simp_all [path,pathEmbedding,pathMap]
  | inr i =>
    cases y with
    | inl j =>
      fin_cases i <;> fin_cases j <;>
        simp_all [path,pathEmbedding,pathMap,Sym2.eq_swap]
    | inr j => exact hxy.elim

/-- First install a well order on a generic carrier; this avoids the
preexisting subset order on the final power-set carrier. -/
theorem host_from_noninjection {C : Type u} (B : Type u)
    (hB : ∀ f : B → Code C, ¬Function.Injective f) :
    ∃ (_ : LinearOrder B),
      (halfGraph B).CliqueFree 3 ∧
      ∀ c : Sym2 (B ⊕ B) → C, ∃ (f : path ↪g halfGraph B) (z : C),
        (∀ i, ∃ a, f (.inl i) = .inl a) ∧
        (∀ j, ∃ b, f (.inr j) = .inr b) ∧
        ∀ x y, path.Adj x y → c s(f x,f y) = z := by
  classical
  letI : LinearOrder B := IsWellOrder.linearOrder WellOrderingRel
  letI : WellFoundedLT B := ⟨(inferInstance : IsWellOrder B WellOrderingRel).wf⟩
  refine ⟨inferInstance,halfGraph_cliqueFree,?_⟩
  intro c
  obtain ⟨a,b,d,hab,hbd,h₀,h₁⟩ := ordered_triangle hB
    (fun a b => c s(Sum.inl a,Sum.inr b))
  refine ⟨pathEmbedding hab hbd,c s(Sum.inl a,Sum.inr b),?_,?_,?_⟩
  · intro i
    exact ⟨_,rfl⟩
  · intro j
    exact ⟨_,rfl⟩
  · exact mono_path_of_triple c hab hbd h₀ h₁

/-- An induced bipartite Ramsey host for P4 for an arbitrary palette.
The two parts of the copy land in the corresponding parts of the host. -/
theorem arbitrary_palette_path (C : Type u) :
    ∃ (B : Type u) (_ : LinearOrder B),
      (halfGraph B).CliqueFree 3 ∧
      ∀ c : Sym2 (B ⊕ B) → C, ∃ (f : path ↪g halfGraph B) (z : C),
        (∀ i, ∃ a, f (.inl i) = .inl a) ∧
        (∀ j, ∃ b, f (.inr j) = .inr b) ∧
        ∀ x y, path.Adj x y → c s(f x,f y) = z := by
  obtain ⟨o,ho⟩ := host_from_noninjection (Set (Code C))
    (fun f => Function.cantor_injective f)
  exact ⟨Set (Code C),o,ho⟩

/-- Free amalgamation upgrades the bipartite lemma to an arbitrary
K4-free ambient graph. Only the designated induced P4 is homogenized.
The ambient graph and palette can both be infinite. -/
theorem path_step {V C : Type u} (H : SimpleGraph V) (hH : H.CliqueFree 4)
    (D : Set V) (e : path ≃g H.induce D) :
    ∃ (W : Type u) (G : SimpleGraph W), G.CliqueFree 4 ∧
      ∀ c : Sym2 W → C, ∃ (f : H ↪g G) (z : C),
        ∀ x y : D, H.Adj x.val y.val → c s(f x.val,f y.val) = z := by
  classical
  obtain ⟨B,oB,hB,hRam⟩ := arbitrary_palette_path C
  letI : LinearOrder B := oB
  let K := halfGraph B
  let I := H.induce D ↪g K
  let G := Erdos595FiniteFolkmanAmalgamation.graph H K D (fun i : I => i)
  have hK : K.CliqueFree 4 := SimpleGraph.CliqueFree.mono (by decide : 3 ≤ 4) hB
  refine ⟨_,G,Erdos595FiniteFolkmanAmalgamation.cliqueFree H K D _ hH hK,?_⟩
  intro c
  let cK : Sym2 (B ⊕ B) → C := fun s => c (s.map Sum.inl)
  obtain ⟨g,z,_,_,hg⟩ := hRam cK
  let i : I := g.comp e.symm.toEmbedding
  let f := Erdos595FiniteFolkmanAmalgamation.copyEmbedding H K D (fun i : I => i) i
  refine ⟨f,z,?_⟩
  intro x y hxy
  have hexy : path.Adj (e.symm x) (e.symm y) := e.symm.map_rel_iff.mpr hxy
  have h := hg (e.symm x) (e.symm y) hexy
  change c s(Erdos595FiniteFolkmanAmalgamation.copy H K D (fun i : I => i) i x.val,
    Erdos595FiniteFolkmanAmalgamation.copy H K D (fun i : I => i) i y.val) = z
  rw [Erdos595FiniteFolkmanAmalgamation.copy_of_mem _ _ _ _ _ _ x.property,
    Erdos595FiniteFolkmanAmalgamation.copy_of_mem _ _ _ _ _ _ y.property]
  exact h

#print axioms halfGraph_cliqueFree
#print axioms arbitrary_palette_path
#print axioms path_step
end Erdos595HalfGraphRamsey
