import Submission.FixedFiniteReducedPower
import Submission.FiniteEdgeBounds

/-! Finite coordinate supports do not bound finite triangle-edge palettes.
This is an obstruction to a proposed proof method, not a settlement of Erdős 595. -/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595FixedPowerSupport
open Erdos595Work Erdos595FixedFiniteReducedPower
universe u
variable {V : Type u} (G : SimpleGraph V) (hG : G.CliqueFree 4)

/-- Coordinate-level adjacency for the canonical induced embedding is exact. -/
lemma coordinate_iff (v w : V) (S : Finset V) :
    (universal (S.card+1)).Adj (point G hG v S) (point G hG w S) ↔
      v ∈ S ∧ w ∈ S ∧ G.Adj v w := by
  classical
  change (universal (S.card+1)).Adj
    (localEmbedding G hG S (localPoint v S))
    (localEmbedding G hG S (localPoint w S)) ↔ _
  rw [(localEmbedding G hG S).map_rel_iff]
  by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
  · rw [localPoint_of_mem v S hv,localPoint_of_mem w S hw]
    simpa only [hv,hw,true_and] using
      (SimpleGraph.map_adj_apply (G := G.induce (S : Set V))
        (f := ⟨some,Option.some_injective S⟩) (a := ⟨v,hv⟩) (b := ⟨w,hw⟩))
  · simp only [localPoint, dif_pos hv, dif_neg hw]
    simp [localGraph,SimpleGraph.map_adj,hv,hw]
  · simp only [localPoint, dif_neg hv, dif_pos hw]
    simp [localGraph,SimpleGraph.map_adj,hv,hw]
  · simp only [localPoint, dif_neg hv, dif_neg hw]
    simp [localGraph,hv,hw]

omit G hG in
/-- A finite support certifies adjacency at every extending coordinate. -/
def Supports (x y : Carrier V) (T : Finset V) : Prop :=
  ∀ S, T ⊆ S → (universal (S.card+1)).Adj (x S) (y S)

lemma point_support_iff (v w : V) (T : Finset V) :
    Supports (point G hG v) (point G hG w) T ↔
      G.Adj v w ∧ v ∈ T ∧ w ∈ T := by
  constructor
  · intro h
    have hh := (coordinate_iff G hG v w T).mp (h T (fun _ hx => hx))
    exact ⟨hh.2.2,hh.1,hh.2.1⟩
  · rintro ⟨h,hv,hw⟩ S hS
    exact (coordinate_iff G hG v w S).mpr ⟨hS hv,hS hw,h⟩

lemma least_support [DecidableEq V] {v w : V} (h : G.Adj v w) :
    IsLeast {T : Finset V | Supports (point G hG v) (point G hG w) T} {v,w} := by
  classical
  constructor
  · exact (point_support_iff G hG v w _).mpr ⟨h,by simp,by simp⟩
  · intro T hT
    have hh := (point_support_iff G hG v w T).mp hT
    exact Finset.insert_subset_iff.mpr ⟨hh.2.1,Finset.singleton_subset_iff.mpr hh.2.2⟩

lemma least_support_card [DecidableEq V] {v w : V} (h : G.Adj v w) : ({v,w} : Finset V).card = 2 := by
  classical
  simp [h.ne]

/-- Keep only product edges admitting a support of size at most two. -/
def twoSupported (V : Type u) : SimpleGraph (Carrier V) where
  Adj x y := ∃ T : Finset V, T.card ≤ 2 ∧ Supports x y T
  symm := by
    intro x y h
    obtain ⟨T,hT,h⟩ := h
    exact ⟨T,hT,fun S hS => (h S hS).symm⟩
  loopless := by
    intro x h
    obtain ⟨T,_,h⟩ := h
    exact (h T (fun _ hx => hx)).ne rfl

omit G hG in
lemma twoSupported_le (V : Type u) : twoSupported V ≤ power V := by
  intro x y h
  obtain ⟨T,_,h⟩ := h
  exact Filter.eventually_atTop.mpr ⟨T,h⟩

/-- Even this restricted graph contains every K4-free graph on V inducedly. -/
noncomputable def twoEmbedding : G ↪g twoSupported V where
  toFun := point G hG
  inj' := (embedding G hG).injective
  map_rel_iff' := by
    intro v w
    constructor
    · intro h
      exact (embedding G hG).map_rel_iff.mp (twoSupported_le V h)
    · intro h
      classical
      exact ⟨{v,w},(least_support_card G h).le,(least_support G hG h).1⟩

omit G hG in
lemma twoSupported_cliqueFree (V : Type u) : (twoSupported V).CliqueFree 4 :=
  (power_cliqueFree V).anti (twoSupported_le V)

omit G hG in
/-- Size-two supports cannot yield a uniform finite edge palette, even when
V is countable. Finite Folkman obstructions already occur in the restriction. -/
theorem twoSupported_no_finite [Infinite V] :
    ¬Erdos595BadEdge.FiniteCover (twoSupported V) := by
  classical
  intro h
  obtain ⟨n,hn⟩ := Erdos595NoCountableK4Target.finiteCover_coloring h
  obtain ⟨A,hA,H,hH,hbad⟩ := Erdos595FiniteFolkman.finite_folkman (Option (Fin n))
  letI := hA
  letI := Fintype.ofFinite A
  haveI : Nonempty A := by
    cases isEmpty_or_nonempty A with
    | inl h => exact False.elim (hbad ⟨fun _ => none,fun a => isEmptyElim a⟩)
    | inr h => exact h
  let e : A ↪ V := (Fintype.equivFin A).toEmbedding.trans
    ((⟨Fin.val,Fin.val_injective⟩ : Fin (Fintype.card A) ↪ ℕ).trans (Infinite.natEmbedding V))
  let f := (twoEmbedding (H.map e) (SimpleGraph.cliqueFree_map_iff.mpr hH)).toHom.comp
    (SimpleGraph.Embedding.map e H).toHom
  exact hbad (hn.comap f)

omit G hG in
/-- Nevertheless, the countable-index case remains countably covered. -/
theorem twoSupported_countable [Countable V] :
    IsCountableUnionOfTriangleFree (twoSupported V) :=
  countable_union_of_hom (SimpleGraph.Hom.ofLE (twoSupported_le V)) (countable_base_cover)

omit G hG in
/-- The bounded-support restriction is still an exact normal form, not an
excluded family. Non-coverability for an uncountable V remains unresolved. -/
theorem conjecture_iff_twoSupported :
    (∃ (V : Type u) (_ : Infinite V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧ ¬IsCountableUnionOfTriangleFree G) ↔
    ∃ V : Type u, ¬IsCountableUnionOfTriangleFree (twoSupported V) := by
  constructor
  · rintro ⟨V,_,G,hG,hn⟩
    exact ⟨V,fun hc => hn (countable_union_of_hom (twoEmbedding G hG).toHom hc)⟩
  · rintro ⟨V,hn⟩
    exact ⟨Carrier V,Erdos595FiniteUltraproduct.infinite_of_no_cover _ hn,twoSupported V,twoSupported_cliqueFree V,hn⟩

omit G hG in
/-- A constant bound fails even in the size-two-support restriction. -/
theorem no_constant_bound [Infinite V] (n : ℕ) :
    ¬Erdos595FiniteEdgeBounds.Bounded (twoSupported V) (fun _ => n) := by
  classical
  rintro ⟨c,hb,hv⟩
  apply twoSupported_no_finite (V := V)
  let K : Fin (n+1) → SimpleGraph (Carrier V) := fun i =>
    { Adj x y := (twoSupported V).Adj x y ∧ c s(x,y) = i.val
      symm := fun _ _ h => ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
      loopless := fun _ h => h.1.ne rfl }
  refine ⟨n+1,K,?_,?_⟩
  · intro i t ht
    obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact hv x y z hxy.1 hxz.1 hyz.1
      ⟨hxy.2.trans hxz.2.symm,hxy.2.trans hyz.2.symm⟩
  · intro x y hxy
    exact ⟨⟨c s(x,y),Nat.lt_succ_of_le (hb _)⟩,hxy,rfl⟩

#print axioms coordinate_iff
#print axioms twoEmbedding
#print axioms twoSupported_no_finite
#print axioms twoSupported_countable
#print axioms conjecture_iff_twoSupported
#print axioms no_constant_bound
end Erdos595FixedPowerSupport
