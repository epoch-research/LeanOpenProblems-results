import Submission.FiniteUltraproductRepresentation
import Submission.CountableEdgeProduct
import Submission.NoCountableK4Target

/-!
A fixed sequence of finite K4-free graphs suffices for a reduced-power normal
form. The factors and the fine filter do not depend on the graph embedded.
This is an exact reduction, NOT a non-coverability theorem for the family.
-/
set_option autoImplicit false
open Set SimpleGraph Filter
namespace Erdos595FixedFiniteReducedPower
open Erdos595Work Erdos595FiniteUltraproduct
universe u

abbrev Template (n : ℕ) := {H : SimpleGraph (Fin n) // H.CliqueFree 4}
abbrev Vertex (n : ℕ) := Template n × Fin n

/-- Disjoint union of all labeled K4-free graphs on n vertices. -/
def universal (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := x.1 = y.1 ∧ x.1.val.Adj x.2 y.2
  symm := by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    simpa only [← h.1] using h.2.symm
  loopless := fun x h => h.2.ne rfl

instance (n : ℕ) : Finite (Vertex n) := inferInstanceAs (Finite (Template n × Fin n))

theorem universal_cliqueFree (n : ℕ) : (universal n).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have he (i j : Fin 4) (h : i ≠ j) := e.map_rel_iff.mpr h
  have h₁ : (e 0).1 = (e 1).1 := (he 0 1 (by decide)).1
  have h₂ : (e 0).1 = (e 2).1 := (he 0 2 (by decide)).1
  have h₃ : (e 0).1 = (e 3).1 := (he 0 3 (by decide)).1
  exact no_adj_common_neighbors (e 0).1.property
    (he 0 1 (by decide)).2 (he 0 2 (by decide)).2
    (by simpa only [← h₁] using (he 1 2 (by decide)).2) (he 0 3 (by decide)).2
    (by simpa only [← h₁] using (he 1 3 (by decide)).2)
    (by simpa only [← h₂] using (he 2 3 (by decide)).2)

/-- Universality at exactly the finite cardinal n. -/
noncomputable def finiteEmbedding {A : Type*} [Fintype A]
    (H : SimpleGraph A) (hH : H.CliqueFree 4) (n : ℕ) (hn : Fintype.card A = n) :
    H ↪g universal n := by
  let e : A ≃ Fin n := Fintype.equivFinOfCardEq hn
  let K := H.comap e.symm
  have hK : K.CliqueFree 4 := hH.comap (SimpleGraph.Embedding.comap e.symm.toEmbedding H)
  exact {
    toFun := fun a => (⟨K,hK⟩,e a)
    inj' := fun _ _ h => e.injective (congrArg Prod.snd h)
    map_rel_iff' := by intro a b; simp [universal,K] }

variable {V : Type u}

/-- A finite induced graph with one isolated default point. -/
def localGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph (Option S) :=
  (G.induce (S : Set V)).map ⟨some,Option.some_injective _⟩

lemma local_cliqueFree (G : SimpleGraph V) (hG : G.CliqueFree 4) (S : Finset V) :
    (localGraph G S).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have he (i j : Fin 4) (h : i ≠ j) := e.map_rel_iff.mpr h
  have hex (i : Fin 4) : ∃ a : S, e i = some a := by
    obtain ⟨j,hj⟩ := exists_ne i
    obtain ⟨a,b,hab,ha,hb⟩ := (SimpleGraph.map_adj _ _ _ _).mp (he i j hj.symm)
    exact ⟨a,ha.symm⟩
  choose a ha using hex
  have hAdj (i j : Fin 4) (h : i ≠ j) : G.Adj (a i).val (a j).val := by
    have hh := he i j h
    rw [ha i,ha j] at hh
    exact (SimpleGraph.map_adj_apply (G := G.induce (S : Set V))
      (f := ⟨some,Option.some_injective S⟩) (a := a i) (b := a j)).mp hh
  exact no_adj_common_neighbors hG (hAdj 0 1 (by decide)) (hAdj 0 2 (by decide))
    (hAdj 1 2 (by decide)) (hAdj 0 3 (by decide)) (hAdj 1 3 (by decide))
    (hAdj 2 3 (by decide))

noncomputable def localEmbedding (G : SimpleGraph V) (hG : G.CliqueFree 4) (S : Finset V) :
    localGraph G S ↪g universal (S.card + 1) := by
  classical
  exact finiteEmbedding _ (local_cliqueFree G hG S) _ (by simp)

noncomputable def localPoint (v : V) (S : Finset V) : Option S := by
  classical
  exact if h : v ∈ S then some ⟨v,h⟩ else none

lemma localPoint_of_mem (v : V) (S : Finset V) (h : v ∈ S) :
    localPoint v S = some ⟨v,h⟩ := by
  classical
  simp [localPoint,h]

/-- Both the sequence of factors and their size parameters are fixed. -/
abbrev Carrier (V : Type u) := (S : Finset V) → Vertex (S.card + 1)

def power (V : Type u) : SimpleGraph (Carrier V) :=
  Erdos595CompleteFilterProduct.graph (fine V) (fun S => universal (S.card + 1))

noncomputable def point (G : SimpleGraph V) (hG : G.CliqueFree 4) (v : V) : Carrier V :=
  fun S => localEmbedding G hG S (localPoint v S)

lemma point_adj_iff (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (F : Filter (Finset V)) [F.NeBot] (hF : F ≤ fine V) (v w : V) :
    (∀ᶠ S in F, (universal (S.card + 1)).Adj (point G hG v S) (point G hG w S)) ↔
      G.Adj v w := by
  classical
  have he := (eventually_contains F hF v).and (eventually_contains F hF w)
  have hr (S : Finset V) (hv : v ∈ S) (hw : w ∈ S) :
      (universal (S.card + 1)).Adj (point G hG v S) (point G hG w S) ↔ G.Adj v w := by
    dsimp only [point]
    rw [(localEmbedding G hG S).map_rel_iff]
    rw [localPoint_of_mem v S hv,localPoint_of_mem w S hw]
    exact SimpleGraph.map_adj_apply (G := G.induce (S : Set V))
  constructor
  · intro h
    obtain ⟨S,hS,h⟩ := (he.and h).exists
    exact (hr S hS.1 hS.2).mp h
  · intro h
    exact he.mono fun S hS => (hr S hS.1 hS.2).mpr h

noncomputable def embedding (G : SimpleGraph V) (hG : G.CliqueFree 4) : G ↪g power V where
  toFun := point G hG
  inj' := by
    classical
    intro v w h
    let S : Finset V := {v,w}
    have he := (localEmbedding G hG S).injective (congrFun h S)
    rw [localPoint_of_mem v S (by simp [S]),localPoint_of_mem w S (by simp [S])] at he
    exact congrArg Subtype.val (Option.some.inj he)
  map_rel_iff' := point_adj_iff G hG (fine V) le_rfl _ _

theorem power_cliqueFree (V : Type u) : (power V).CliqueFree 4 :=
  Erdos595CountableCoordinate.product_cliqueFree _ _ 4 (fun S => universal_cliqueFree (S.card + 1))

/-- Ordinary fine ULTRAPRODUCTS of the very same fixed sequence are also universal. -/
noncomputable def ultraEmbedding (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    G ↪g quotientGraph (fineUltra V : Filter (Finset V)) (fun S : Finset V => universal (S.card + 1)) where
  toFun v := (point G hG v : (fineUltra V : Filter (Finset V)).Product (fun S => Vertex (S.card + 1)))
  inj' := by
    classical
    intro v w h
    have he : ∀ᶠ S in (fineUltra V : Filter (Finset V)), point G hG v S = point G hG w S := Quotient.exact h
    obtain ⟨S,hv,hw,he⟩ := ((eventually_contains _ (fineUltra_le V) v).and
      ((eventually_contains _ (fineUltra_le V) w).and he)).exists
    have hh := (localEmbedding G hG S).injective he
    rw [localPoint_of_mem v S hv,localPoint_of_mem w S hw] at hh
    exact congrArg Subtype.val (Option.some.inj hh)
  map_rel_iff' := by
    intro v w
    exact (quotientGraph_adj (fineUltra V : Filter (Finset V))
      (fun S => universal (S.card + 1)) (point G hG v) (point G hG w)).trans
        (point_adj_iff G hG _ (fineUltra_le V) v w)

/-- This fixed family is equivalent to the original existence problem;
no member of it is proved non-coverable here. -/
theorem conjecture_iff_fixed_powers :
    (∃ (V : Type u) (_ : Infinite V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧ ¬IsCountableUnionOfTriangleFree G) ↔
    ∃ V : Type u, ¬IsCountableUnionOfTriangleFree (power V) := by
  constructor
  · rintro ⟨V,_,G,hG,hn⟩
    exact ⟨V,fun h => hn (countable_union_of_hom (embedding G hG).toHom h)⟩
  · rintro ⟨V,hn⟩
    exact ⟨Carrier V,infinite_of_no_cover _ hn,power V,power_cliqueFree V,hn⟩

/-- The countable-index part of this canonical family is already covered. -/
theorem countable_base_cover [Countable V] : IsCountableUnionOfTriangleFree (power V) := by
  apply Erdos595CountableEdgeProduct.countable_index_cover
  intro S
  classical
  letI := Fintype.ofFinite (Vertex (S.card + 1))
  exact Erdos595CompleteFilterProduct.cover_of_colorable _ (SimpleGraph.colorable_of_fintype _)

/-- For every infinite index carrier, this fixed power has NO finite edge
palette. For countable V this coexists with the preceding countable cover. -/
theorem no_finite_cover [Infinite V] : ¬Erdos595BadEdge.FiniteCover (power V) := by
  classical
  intro h
  obtain ⟨n,hn⟩ := Erdos595NoCountableK4Target.finiteCover_coloring h
  obtain ⟨A,hA,H,hH,hbad⟩ := Erdos595FiniteFolkman.finite_folkman (Option (Fin n))
  letI := hA
  letI := Fintype.ofFinite A
  haveI : Nonempty A := by
    cases isEmpty_or_nonempty A with
    | inl h =>
      exact False.elim (hbad ⟨fun _ => none,fun a => isEmptyElim a⟩)
    | inr h => exact h
  let e : A ↪ V := (Fintype.equivFin A).toEmbedding.trans
    ((⟨Fin.val,Fin.val_injective⟩ : Fin (Fintype.card A) ↪ ℕ).trans (Infinite.natEmbedding V))
  have hMap : (H.map e).CliqueFree 4 := SimpleGraph.cliqueFree_map_iff.mpr hH
  let f := (embedding (H.map e) hMap).toHom.comp (SimpleGraph.Embedding.map e H).toHom
  exact hbad (hn.comap f)

/-- Positivity of a countable sample, even without convergence, forces V countable. -/
theorem countable_of_positive_sample (F : Filter (Finset V)) [F.NeBot]
    (hF : F ≤ fine V) (s : ℕ → Finset V)
    (hs : (F ⊓ Filter.principal (Set.range s)).NeBot) : Countable V := by
  letI := hs
  have hc : (⋃ n, (s n : Set V)).Countable := Set.countable_iUnion fun n => (s n).countable_toSet
  have hu : (⋃ n, (s n : Set V)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    have hv : ∀ᶠ S in F ⊓ Filter.principal (Set.range s), v ∈ S :=
      (show F ⊓ Filter.principal (Set.range s) ≤ F from inf_le_left) (eventually_contains F hF v)
    have hr : ∀ᶠ S in F ⊓ Filter.principal (Set.range s), S ∈ Set.range s :=
      (show F ⊓ Filter.principal (Set.range s) ≤ Filter.principal (Set.range s) from inf_le_right)
        (Filter.mem_principal_self _)
    obtain ⟨S,hv,n,rfl⟩ := (hv.and hr).exists
    exact Set.mem_iUnion.mpr ⟨n,hv⟩
  rw [hu] at hc
  exact Set.countable_univ_iff.mp hc

#print axioms conjecture_iff_fixed_powers
#print axioms no_finite_cover
#print axioms ultraEmbedding
#print axioms countable_base_cover
#print axioms countable_of_positive_sample
end Erdos595FixedFiniteReducedPower
