import Submission.CountableCoordinateRepresentation
import Submission.SampledFilterProduct

/-!
Every graph embeds in a genuine ultraproduct of finite induced subgraphs.
For an infinite original vertex set the fine ultrafilter is necessarily
countably incomplete; for an uncountable vertex set it has no countable
sampling sequence. This reduction does not prove non-coverability.
-/

set_option autoImplicit false
open Set Filter SimpleGraph
namespace Erdos595FiniteUltraproduct

universe u
variable {V : Type u}

def fine (V : Type u) : Filter (Finset V) := atTop

instance : (fine V).NeBot := Filter.atTop_neBot

noncomputable def fineUltra (V : Type u) : Ultrafilter (Finset V) :=
  Ultrafilter.of (fine V)

lemma fineUltra_le (V : Type u) : (fineUltra V : Filter _) ≤ fine V :=
  Ultrafilter.of_le _

lemma eventually_contains (F : Filter (Finset V)) (hF : F ≤ fine V) (v : V) :
    ∀ᶠ S in F, v ∈ S := by
  classical
  apply hF
  exact Filter.eventually_atTop.mpr ⟨{v},fun S hS => hS (by simp)⟩

/-- Fine filters on finite subsets cannot be countably complete when the
underlying vertex set is infinite. -/
theorem not_countably_complete [Infinite V] (F : Filter (Finset V)) [F.NeBot]
    (hF : F ≤ fine V) : ¬CountableInterFilter F := by
  intro h
  letI := h
  let e : ℕ ↪ V := Infinite.natEmbedding V
  have he (n : ℕ) : ∀ᶠ S in F, e n ∈ S := eventually_contains F hF (e n)
  obtain ⟨S,hS⟩ := (eventually_countable_forall.mpr he).exists
  exact (Set.infinite_range_of_injective e.injective)
    (S.finite_toSet.subset (Set.range_subset_iff.mpr hS))

/-- Any sequence tending to a fine filter on finite subsets forces the
original vertex set to be countable. -/
theorem countable_of_sampler (F : Filter (Finset V)) (hF : F ≤ fine V)
    (s : ℕ → Finset V) (hs : Tendsto s atTop F) : Countable V := by
  have hcount : (⋃ n, (s n : Set V)).Countable :=
    Set.countable_iUnion fun n => (s n).countable_toSet
  have hu : (⋃ n, (s n : Set V)) = univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨n,hn⟩ := (hs.eventually (eventually_contains F hF v)).exists
    exact Set.mem_iUnion.mpr ⟨n,hn⟩
  rw [hu] at hcount
  exact Set.countable_univ_iff.mp hcount

def Carrier (v₀ : V) (S : Finset V) := {v : V // v ∈ (S : Set V) ∪ {v₀}}

instance (v₀ : V) (S : Finset V) : Finite (Carrier v₀ S) :=
  (S.finite_toSet.union (Set.finite_singleton v₀)).to_subtype

instance (v₀ : V) (S : Finset V) : Nonempty (Carrier v₀ S) :=
  ⟨⟨v₀,Or.inr rfl⟩⟩

noncomputable def project (v₀ v : V) (S : Finset V) : Carrier v₀ S := by
  classical
  exact if h : v ∈ S then ⟨v,Or.inl h⟩ else ⟨v₀,Or.inr rfl⟩

lemma project_of_mem (v₀ v : V) (S : Finset V) (h : v ∈ S) :
    (project v₀ v S).1 = v := by
  classical
  simp [project,h]

def coordinate (G : SimpleGraph V) (v₀ : V) (S : Finset V) :
    SimpleGraph (Carrier v₀ S) := G.comap Subtype.val

lemma coordinate_cliqueFree (G : SimpleGraph V) (v₀ : V) {n : ℕ}
    (hG : G.CliqueFree n) (S : Finset V) : (coordinate G v₀ S).CliqueFree n :=
  hG.comap (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G)

/-- The quotient graph uses representatives modulo eventual equality.
The next lemma verifies that its adjacency is the usual representative-
independent reduced-product relation. -/
noncomputable def quotientGraph {I : Type*} {A : I → Type*}
    (F : Filter I) [F.NeBot] (G : ∀ i, SimpleGraph (A i)) :
    SimpleGraph (F.Product A) :=
  (Erdos595CompleteFilterProduct.graph F G).comap Quotient.out

lemma quotientGraph_adj {I : Type*} {A : I → Type*} (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i)) (x y : ∀ i, A i) :
    (quotientGraph F G).Adj (x : F.Product A) (y : F.Product A) ↔
      ∀ᶠ i in F, (G i).Adj (x i) (y i) := by
  have hx : ∀ᶠ i in F, (Quotient.out (x : F.Product A)) i = x i := Quotient.mk_out (s := F.productSetoid A) x
  have hy : ∀ᶠ i in F, (Quotient.out (y : F.Product A)) i = y i := Quotient.mk_out (s := F.productSetoid A) y
  apply Filter.eventually_congr
  filter_upwards [hx,hy] with i hi hj
  rw [hi,hj]

lemma project_adj_iff (G : SimpleGraph V) (v₀ : V)
    (F : Filter (Finset V)) [F.NeBot] (hF : F ≤ fine V) (x y : V) :
    (quotientGraph F (coordinate G v₀)).Adj
      (project v₀ x : F.Product (Carrier v₀))
      (project v₀ y : F.Product (Carrier v₀)) ↔ G.Adj x y := by
  rw [quotientGraph_adj]
  have he := (eventually_contains F hF x).and (eventually_contains F hF y)
  constructor
  · intro h
    obtain ⟨S,hS,hxy⟩ := (he.and h).exists
    change G.Adj (project v₀ x S).1 (project v₀ y S).1 at hxy
    simpa only [project_of_mem v₀ x S hS.1,project_of_mem v₀ y S hS.2] using hxy
  · intro h
    filter_upwards [he] with S hS
    change G.Adj (project v₀ x S).1 (project v₀ y S).1
    simpa only [project_of_mem v₀ x S hS.1,project_of_mem v₀ y S hS.2] using h

noncomputable def embedding (G : SimpleGraph V) (v₀ : V)
    (F : Filter (Finset V)) [F.NeBot] (hF : F ≤ fine V) :
    G ↪g quotientGraph F (coordinate G v₀) where
  toFun x := (project v₀ x : F.Product (Carrier v₀))
  inj' := by
    intro x y hxy
    have he : ∀ᶠ S in F, project v₀ x S = project v₀ y S := Quotient.exact hxy
    obtain ⟨S,hS,ht⟩ := ((eventually_contains F hF x).and
      ((eventually_contains F hF y).and he)).exists
    have hv := congrArg Subtype.val ht.2
    simpa only [project_of_mem v₀ x S hS,project_of_mem v₀ y S ht.1] using hv
  map_rel_iff' := project_adj_iff G v₀ F hF _ _

lemma quotient_cliqueFree (G : SimpleGraph V) (v₀ : V)
    (F : Filter (Finset V)) [F.NeBot] {n : ℕ} (hG : G.CliqueFree n) :
    (quotientGraph F (coordinate G v₀)).CliqueFree n := by
  have h := Erdos595CountableCoordinate.product_cliqueFree F (coordinate G v₀) n
    (coordinate_cliqueFree G v₀ hG)
  exact h.comap (SimpleGraph.Embedding.comap ⟨Quotient.out,Quotient.out_injective⟩ _)

/-- Every hypothetical witness is retained in a finite-coordinate
ultraproduct over an ordinary fine ultrafilter. No countable completeness
of that ultrafilter is asserted. -/
theorem no_cover_preserved (G : SimpleGraph V) (v₀ : V)
    (hG : ¬Erdos595Work.IsCountableUnionOfTriangleFree G) :
    ¬Erdos595Work.IsCountableUnionOfTriangleFree
      (quotientGraph (fineUltra V : Filter _) (coordinate G v₀)) := by
  intro h
  exact hG (Erdos595Work.countable_union_of_hom
    (embedding G v₀ (fineUltra V : Filter _) (fineUltra_le V)).toHom h)

lemma infinite_of_no_cover (G : SimpleGraph V)
    (hG : ¬Erdos595Work.IsCountableUnionOfTriangleFree G) : Infinite V := by
  classical
  rcases finite_or_infinite V with h | h
  · letI := h
    letI := Fintype.ofFinite V
    apply False.elim
    apply hG
    apply Erdos595CompleteFilterProduct.cover_of_colorable (n := Fintype.card V)
    exact ⟨SimpleGraph.Coloring.mk (Fintype.equivFin V)
      (fun h he => h.ne ((Fintype.equivFin V).injective he))⟩
  · exact h

/-- A finite-ultraproduct normal form for the conjecture. The right-hand
side remains an existence assertion; the theorem supplies no witness to it. -/
theorem finite_ultraproduct_iff :
    (∃ (V : Type u) (_ : Infinite V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧ ¬Erdos595Work.IsCountableUnionOfTriangleFree G) ↔
    ∃ (I : Type u) (A : I → Type u) (U : Ultrafilter I)
      (H : ∀ i, SimpleGraph (A i)),
      (∀ i, Finite (A i)) ∧ (∀ i, (H i).CliqueFree 4) ∧
      ¬Erdos595Work.IsCountableUnionOfTriangleFree (quotientGraph (U : Filter I) H) := by
  constructor
  · rintro ⟨V,hV,G,hG,hcov⟩
    letI := hV
    let v₀ : V := Classical.arbitrary V
    exact ⟨Finset V,Carrier v₀,fineUltra V,coordinate G v₀,
      fun _ => inferInstance,coordinate_cliqueFree G v₀ hG,no_cover_preserved G v₀ hcov⟩
  · rintro ⟨I,A,U,H,hfin,hH,hcov⟩
    let P := quotientGraph (U : Filter I) H
    have hP : P.CliqueFree 4 := by
      have h := Erdos595CountableCoordinate.product_cliqueFree (U : Filter I) H 4 hH
      exact h.comap (SimpleGraph.Embedding.comap ⟨Quotient.out,Quotient.out_injective⟩ _)
    exact ⟨(U : Filter I).Product A,infinite_of_no_cover P hcov,P,hP,hcov⟩

#print axioms finite_ultraproduct_iff
#print axioms not_countably_complete
#print axioms countable_of_sampler
#print axioms quotientGraph_adj
#print axioms embedding
#print axioms quotient_cliqueFree
#print axioms no_cover_preserved
end Erdos595FiniteUltraproduct
