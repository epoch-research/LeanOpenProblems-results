import Submission.InfinitePairRamsey
import Submission.HalfGraphRamsey

/-!
Positive infinite-target bipartite Ramsey steps. Well-ordered half-graphs
and matchings of arbitrary cardinality have induced, part-preserving Ramsey
hosts for arbitrary palettes. This does not supply arbitrary infinite
bipartite targets or simultaneous infinitely many amalgamation stages.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595InfiniteBipartite
open Erdos595InfinitePairRamsey Erdos595HalfGraphRamsey
universe u

variable {A B : Type u} [LinearOrder A] [LinearOrder B]

def halfEmbedding (f : A ↪o B) : halfGraph A ↪g halfGraph B where
  toFun := Sum.map f f
  inj' := Sum.map_injective.mpr ⟨f.injective,f.injective⟩
  map_rel_iff' := by
    intro x y
    change (halfGraph B).Adj (Sum.map f f x) (Sum.map f f y) ↔ (halfGraph A).Adj x y
    cases x <;> cases y <;> simp [halfGraph]

/-- The ENTIRE well-ordered half-graph can be homogenized, not just P4. -/
theorem half_ramsey (A C : Type u) [LinearOrder A] [WellFoundedLT A] :
    ∃ (B : Type u) (_ : LinearOrder B),
      (halfGraph B).CliqueFree 3 ∧
      ∀ c : Sym2 (B ⊕ B) → C, ∃ (f : halfGraph A ↪g halfGraph B) (k : C),
        (∀ a, ∃ b, f (.inl a) = .inl b) ∧
        (∀ a, ∃ b, f (.inr a) = .inr b) ∧
        ∀ x y, (halfGraph A).Adj x y → c s(f x,f y) = k := by
  obtain ⟨B,oB,wB,hB⟩ := pair_ramsey_host A C
  letI : LinearOrder B := oB
  refine ⟨B,oB,halfGraph_cliqueFree,?_⟩
  intro c
  obtain ⟨f,k,hf⟩ := hB (fun a b => c s(Sum.inl a,Sum.inr b))
  refine ⟨halfEmbedding f,k,fun a => ⟨f a,rfl⟩,fun a => ⟨f a,rfl⟩,?_⟩
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl b => exact hxy.elim
    | inr b => exact hf a b hxy
  | inr a =>
    cases y with
    | inl b => simpa only [halfEmbedding,Sym2.eq_swap] using hf b a hxy
    | inr b => exact hxy.elim

/-- A TWO-coordinate ordered pair box, with arbitrary infinite target A.
The number of coordinates, unlike the target or palette, is finite. -/
theorem pair_box (A C : Type u) [LinearOrder A] [WellFoundedLT A] :
    ∃ (B D : Type u) (_ : LinearOrder B) (_ : LinearOrder D),
      ∀ c : B → B → D → D → C,
        ∃ (f : A ↪o B) (g : A ↪o D) (k : C),
          ∀ a b s t, a < b → s < t → c (f a) (f b) (g s) (g t) = k := by
  obtain ⟨B,oB,wB,hB⟩ := pair_ramsey_host A C
  obtain ⟨D,oD,wD,hD⟩ := pair_ramsey_host A (B → B → C)
  letI : LinearOrder B := oB
  letI : LinearOrder D := oD
  refine ⟨B,D,oB,oD,?_⟩
  intro c
  obtain ⟨g,z,hg⟩ := hD (fun s t a b => c a b s t)
  obtain ⟨f,k,hf⟩ := hB z
  refine ⟨f,g,k,?_⟩
  intro a b s t hab hst
  exact (congrFun (congrFun (hg s t hst) (f a)) (f b)).trans (hf a b hab)

def matching (A : Type u) : SimpleGraph (A ⊕ A) where
  Adj
    | .inl a,.inr b => a = b
    | .inr b,.inl a => a = b
    | _,_ => False
  symm := by intro x y h; cases x <;> cases y <;> exact h
  loopless := by intro x h; cases x <;> exact h

def intervalGraph (B D : Type u) [LinearOrder B] [LinearOrder D] :
    SimpleGraph ((B × D) ⊕ (B × D)) where
  Adj
    | .inl x,.inr y => x.1 < y.1 ∧ y.2 < x.2
    | .inr y,.inl x => x.1 < y.1 ∧ y.2 < x.2
    | _,_ => False
  symm := by intro x y h; cases x <;> cases y <;> exact h
  loopless := by intro x h; cases x <;> exact h

lemma intervalGraph_triangleFree (B D : Type u) [LinearOrder B] [LinearOrder D] :
    (intervalGraph B D).CliqueFree 3 := by
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  cases a <;> cases b <;> cases c <;>
    first | exact hab | exact hac | exact hbc

abbrev Double (A : Type u) := A ×ₗ Fin 2

def low (a : A) : Double A := toLex (a,0)
def high (a : A) : Double A := toLex (a,1)

lemma low_high_iff (a b : A) : low a < high b ↔ a ≤ b := by
  rw [Prod.Lex.lt_iff]
  change (a < b ∨ a = b ∧ (0 : Fin 2) < 1) ↔ a ≤ b
  simp [le_iff_lt_or_eq]

omit [LinearOrder A] in
lemma low_injective : Function.Injective (low (A := A)) := by
  intro a b h
  exact congrArg (fun x : Double A => (ofLex x).1) h

variable {D : Type u} [LinearOrder D]

def matchingEmbedding (f : Double A ↪o B) (g : Double A ↪o D) :
    matching A ↪g intervalGraph B D where
  toFun
    | .inl a => .inl (f (low a),g (high a))
    | .inr a => .inr (f (high a),g (low a))
  inj' := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        exact congrArg Sum.inl (low_injective
          (f.injective (congrArg Prod.fst (Sum.inl_injective h))))
      | inr b => cases h
    | inr a =>
      cases y with
      | inl b => cases h
      | inr b =>
        exact congrArg Sum.inr (low_injective
          (g.injective (congrArg Prod.snd (Sum.inr_injective h))))
  map_rel_iff' := by
    intro x y
    cases x <;> cases y <;>
      simp only [intervalGraph,matching,OrderEmbedding.lt_iff_lt,low_high_iff,le_antisymm_iff]

/-- Arbitrarily large induced MATCHINGS have bipartite Ramsey hosts, even
for infinite palettes. The host is not a matching. -/
theorem matching_ramsey_ordered (A C : Type u) [LinearOrder A] [WellFoundedLT A] :
    ∃ (V : Type u) (K : SimpleGraph (V ⊕ V)), K.CliqueFree 3 ∧
      ∀ c : Sym2 (V ⊕ V) → C, ∃ (e : matching A ↪g K) (k : C),
        (∀ a, ∃ b, e (.inl a) = .inl b) ∧
        (∀ a, ∃ b, e (.inr a) = .inr b) ∧
        ∀ x y, (matching A).Adj x y → c s(e x,e y) = k := by
  obtain ⟨B,D,oB,oD,h⟩ := pair_box (Double A) C
  letI : LinearOrder B := oB
  letI : LinearOrder D := oD
  refine ⟨B × D,intervalGraph B D,intervalGraph_triangleFree B D,?_⟩
  intro c
  obtain ⟨f,g,k,hfg⟩ := h (fun a b s t => c s(Sum.inl (a,t),Sum.inr (b,s)))
  let e := matchingEmbedding f g
  have he (a : A) : c s(e (.inl a),e (.inr a)) = k :=
    hfg (low a) (high a) (low a) (high a)
      ((low_high_iff a a).mpr le_rfl) ((low_high_iff a a).mpr le_rfl)
  refine ⟨e,k,fun a => ⟨_,rfl⟩,fun a => ⟨_,rfl⟩,?_⟩
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl b => exact hxy.elim
    | inr b => cases hxy; exact he a
  | inr a =>
    cases y with
    | inl b => cases hxy; simpa only [Sym2.eq_swap] using he a
    | inr b => exact hxy.elim

theorem matching_ramsey (A C : Type u) :
    ∃ (V : Type u) (K : SimpleGraph (V ⊕ V)), K.CliqueFree 3 ∧
      ∀ c : Sym2 (V ⊕ V) → C, ∃ (e : matching A ↪g K) (k : C),
        (∀ a, ∃ b, e (.inl a) = .inl b) ∧
        (∀ a, ∃ b, e (.inr a) = .inr b) ∧
        ∀ x y, (matching A).Adj x y → c s(e x,e y) = k := by
  classical
  letI : LinearOrder A := IsWellOrder.linearOrder WellOrderingRel
  letI : WellFoundedLT A := ⟨(inferInstance : IsWellOrder A WellOrderingRel).wf⟩
  exact matching_ramsey_ordered A C

/-- Free amalgamation over an arbitrary designated induced target. -/
theorem step_of_ramsey {T V W C : Type u} (P : SimpleGraph T) (K : SimpleGraph W)
    (hK : K.CliqueFree 4)
    (hRam : ∀ c : Sym2 W → C, ∃ (e : P ↪g K) (k : C),
      ∀ x y, P.Adj x y → c s(e x,e y) = k)
    (H : SimpleGraph V) (hH : H.CliqueFree 4) (S : Set V)
    (e : P ≃g H.induce S) :
    ∃ (U : Type u) (G : SimpleGraph U), G.CliqueFree 4 ∧
      ∀ c : Sym2 U → C, ∃ (f : H ↪g G) (k : C),
        ∀ x y : S, H.Adj x.val y.val → c s(f x.val,f y.val) = k := by
  classical
  let J := H.induce S ↪g K
  let G := Erdos595FiniteFolkmanAmalgamation.graph H K S (fun i : J => i)
  refine ⟨_,G,Erdos595FiniteFolkmanAmalgamation.cliqueFree H K S _ hH hK,?_⟩
  intro c
  obtain ⟨g,k,hg⟩ := hRam (fun s => c (s.map Sum.inl))
  let i : J := g.comp e.symm.toEmbedding
  let f := Erdos595FiniteFolkmanAmalgamation.copyEmbedding H K S (fun i : J => i) i
  refine ⟨f,k,?_⟩
  intro x y hxy
  have hh := hg (e.symm x) (e.symm y) (e.symm.map_rel_iff.mpr hxy)
  change c s(Erdos595FiniteFolkmanAmalgamation.copy H K S (fun i : J => i) i x.val,
    Erdos595FiniteFolkmanAmalgamation.copy H K S (fun i : J => i) i y.val) = k
  rw [Erdos595FiniteFolkmanAmalgamation.copy_of_mem _ _ _ _ _ _ x.property,
    Erdos595FiniteFolkmanAmalgamation.copy_of_mem _ _ _ _ _ _ y.property]
  exact hh

/-- Homogenization over an infinite designated half-graph preserves K4-freeness. -/
theorem half_step {V C : Type u} [WellFoundedLT A]
    (H : SimpleGraph V) (hH : H.CliqueFree 4) (S : Set V)
    (e : halfGraph A ≃g H.induce S) :
    ∃ (U : Type u) (G : SimpleGraph U), G.CliqueFree 4 ∧
      ∀ c : Sym2 U → C, ∃ (f : H ↪g G) (k : C),
        ∀ x y : S, H.Adj x.val y.val → c s(f x.val,f y.val) = k := by
  obtain ⟨B,oB,hB,hRam⟩ := half_ramsey A C
  letI : LinearOrder B := oB
  apply step_of_ramsey (halfGraph A) (halfGraph B) (hB.mono (by decide)) ?_ H hH S e
  intro c
  obtain ⟨f,k,_,_,hf⟩ := hRam c
  exact ⟨f,k,hf⟩

/-- Homogenization over an arbitrarily large induced matching. -/
theorem matching_step {T V C : Type u}
    (H : SimpleGraph V) (hH : H.CliqueFree 4) (S : Set V)
    (e : matching T ≃g H.induce S) :
    ∃ (U : Type u) (G : SimpleGraph U), G.CliqueFree 4 ∧
      ∀ c : Sym2 U → C, ∃ (f : H ↪g G) (k : C),
        ∀ x y : S, H.Adj x.val y.val → c s(f x.val,f y.val) = k := by
  obtain ⟨B,K,hK,hRam⟩ := matching_ramsey T C
  apply step_of_ramsey (matching T) K (hK.mono (by decide)) ?_ H hH S e
  intro c
  obtain ⟨f,k,_,_,hf⟩ := hRam c
  exact ⟨f,k,hf⟩

#print axioms half_step
#print axioms matching_step
#print axioms half_ramsey
#print axioms pair_box
#print axioms matching_ramsey
#print axioms step_of_ramsey
end Erdos595InfiniteBipartite
