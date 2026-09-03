import Submission.InfiniteTripleRamsey
import Submission.InfiniteBipartiteRamsey

/-!
Induced edge-Ramsey hosts for whole ordered shift graphs and arbitrary palettes.
The hosts are triangle-free, but the targets need not be bipartite: in particular
an induced five-cycle is covered by the theorem. This supplies one free-
amalgamation step, not a coherent infinite iteration or a solution to Erdos 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595InfiniteShiftRamsey
open Erdos595Work
universe u

abbrev Pair (A : Type u) [LinearOrder A] := {p : A × A // p.1 < p.2}

variable {A B : Type u} [LinearOrder A] [LinearOrder B]

def embedding (f : A ↪o B) : orderedShiftGraph A ↪g orderedShiftGraph B where
  toFun p := ⟨(f p.val.1,f p.val.2),f.strictMono p.property⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    exact Prod.ext (f.injective (congrArg Prod.fst he))
      (f.injective (congrArg Prod.snd he))
  map_rel_iff' := by
    intro p q
    change (f p.val.2 = f q.val.1 ∨ f q.val.2 = f p.val.1) ↔ _
    simp only [f.injective.eq_iff]
    rfl

/-- A single color on all increasing triples colors all shift edges alike. -/
lemma shift_mono {C : Type u} [Nonempty C] (c : Sym2 (Pair B) → C)
    (f : A ↪o B) (k : C)
    (h : ∀ a b d, ∀ hab : a < b, ∀ hbd : b < d,
      c s(⟨(f a,f b),f.strictMono hab⟩,⟨(f b,f d),f.strictMono hbd⟩) = k) :
    ∀ p q, (orderedShiftGraph A).Adj p q → c s(embedding f p,embedding f q) = k := by
  have forward (p q : Pair A) (he : p.val.2 = q.val.1) :
      c s(embedding f p,embedding f q) = k := by
    have hbd : p.val.2 < q.val.2 := he.symm ▸ q.property
    have hh := h p.val.1 p.val.2 q.val.2 p.property hbd
    change c s(⟨(f p.val.1,f p.val.2),f.strictMono p.property⟩,
      ⟨(f q.val.1,f q.val.2),f.strictMono q.property⟩) = k
    simpa only [he] using hh
  intro p q hpq
  rcases hpq with he | he
  · exact forward p q he
  · simpa only [Sym2.eq_swap] using forward q p he

/-- The target order can have arbitrary cardinality. No bound on the palette
is used. The embedding is induced, not merely a graph homomorphism. -/
theorem ramsey (A C : Type u) [LinearOrder A] [WellFoundedLT A] [Nonempty C] :
    ∃ (B : Type u) (_ : LinearOrder B) (_ : WellFoundedLT B),
      ∀ c : Sym2 (Pair B) → C, ∃ (f : A ↪o B) (k : C),
        ∀ p q, (orderedShiftGraph A).Adj p q →
          c s(embedding f p,embedding f q) = k := by
  classical
  obtain ⟨B,oB,wB,hB⟩ := Erdos595InfiniteTripleRamsey.triple_ramsey_host A C
  letI : LinearOrder B := oB
  letI : WellFoundedLT B := wB
  refine ⟨B,oB,wB,?_⟩
  intro c
  let d : B → B → B → C := fun a b t =>
    if h : a < b ∧ b < t then c s(⟨(a,b),h.1⟩,⟨(b,t),h.2⟩)
    else Classical.arbitrary C
  obtain ⟨f,k,hf⟩ := hB d
  refine ⟨f,k,shift_mono c f k ?_⟩
  intro a b t hab hbt
  have hh := hf a b t hab hbt
  have hpos : f a < f b ∧ f b < f t := ⟨f.strictMono hab,f.strictMono hbt⟩
  simpa only [d,dif_pos hpos] using hh

/-- A graph-valued formulation emphasizing that the Ramsey host itself is TF. -/
theorem graph_ramsey (A C : Type u) [LinearOrder A] [WellFoundedLT A] [Nonempty C] :
    ∃ (V : Type u) (K : SimpleGraph V), K.CliqueFree 3 ∧
      ∀ c : Sym2 V → C, ∃ (f : orderedShiftGraph A ↪g K) (k : C),
        ∀ p q, (orderedShiftGraph A).Adj p q → c s(f p,f q) = k := by
  obtain ⟨B,oB,wB,hB⟩ := ramsey A C
  letI : LinearOrder B := oB
  letI : WellFoundedLT B := wB
  refine ⟨Pair B,orderedShiftGraph B,orderedShiftGraph_cliqueFree B,?_⟩
  intro c
  obtain ⟨f,k,hf⟩ := hB c
  exact ⟨embedding f,k,hf⟩

/-- One whole induced shift subgraph can be homogenized in a K4-free extension.
This does not assert compatibility of the copies chosen by different steps. -/
theorem step (A C : Type u) [LinearOrder A] [WellFoundedLT A] [Nonempty C]
    {V : Type u} (H : SimpleGraph V) (hH : H.CliqueFree 4) (S : Set V)
    (e : orderedShiftGraph A ≃g H.induce S) :
    ∃ (W : Type u) (G : SimpleGraph W), G.CliqueFree 4 ∧
      ∀ c : Sym2 W → C, ∃ (f : H ↪g G) (k : C),
        ∀ x y : S, H.Adj x.val y.val → c s(f x.val,f y.val) = k := by
  obtain ⟨W,K,hK,hRam⟩ := graph_ramsey A C
  exact Erdos595InfiniteBipartite.step_of_ramsey (orderedShiftGraph A) K
    (hK.mono (by decide)) hRam H hH S e

/-- Any induced subgraph of a shift graph inherits such a Ramsey host. -/
theorem ramsey_of_embedding (A C : Type u) [LinearOrder A] [WellFoundedLT A]
    [Nonempty C] {U : Type u} (F : SimpleGraph U) (e : F ↪g orderedShiftGraph A) :
    ∃ (V : Type u) (K : SimpleGraph V), K.CliqueFree 3 ∧
      ∀ c : Sym2 V → C, ∃ (f : F ↪g K) (k : C),
        ∀ a b, F.Adj a b → c s(f a,f b) = k := by
  obtain ⟨V,K,hK,hRam⟩ := graph_ramsey A C
  refine ⟨V,K,hK,?_⟩
  intro c
  obtain ⟨f,k,hf⟩ := hRam c
  exact ⟨f.comp e,k,fun a b hab => hf (e a) (e b) (e.map_rel_iff.mpr hab)⟩

private def fivePairs : Fin 5 → Pair (Fin 5) :=
  ![⟨(0,1),by decide⟩,⟨(1,2),by decide⟩,⟨(2,3),by decide⟩,
    ⟨(3,4),by decide⟩,⟨(1,3),by decide⟩]

private instance : DecidableRel (orderedShiftGraph (Fin 5)).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private theorem fivePairs_injective : Function.Injective fivePairs := by decide +kernel

private theorem fivePairs_adj : ∀ i j,
    (orderedShiftGraph (Fin 5)).Adj (fivePairs i) (fivePairs j) ↔
      (cycleGraph 5).Adj i j := by decide +kernel

/-- The cycle uses four successive arcs and one shortcut arc. -/
def cycleFiveEmbedding : cycleGraph 5 ↪g orderedShiftGraph (Fin 5) where
  toFun := fivePairs
  inj' := fivePairs_injective
  map_rel_iff' := fivePairs_adj _ _

/-- A non-bipartite finite target has a triangle-free induced edge-Ramsey host,
even for an arbitrary infinite palette. No triangle is forced by this theorem. -/
theorem cycle_five_ramsey (C : Type) [Nonempty C] :
    ∃ (V : Type) (K : SimpleGraph V), K.CliqueFree 3 ∧
      ∀ c : Sym2 V → C, ∃ (f : cycleGraph 5 ↪g K) (k : C),
        ∀ a b, (cycleGraph 5).Adj a b → c s(f a,f b) = k :=
  ramsey_of_embedding (Fin 5) C (cycleGraph 5) cycleFiveEmbedding

#print axioms ramsey
#print axioms graph_ramsey
#print axioms step
#print axioms ramsey_of_embedding
#print axioms cycleFiveEmbedding
#print axioms cycle_five_ramsey
end Erdos595InfiniteShiftRamsey
