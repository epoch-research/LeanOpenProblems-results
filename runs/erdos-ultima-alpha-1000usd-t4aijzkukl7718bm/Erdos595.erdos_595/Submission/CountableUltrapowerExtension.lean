import Submission.CountableExtensionGraph
import Submission.CountableCoordinateRepresentation
import Submission.CountableProductObstruction
import Submission.FiniteFolkman

/-!
A continuum-sized K4-free graph with the countable one-point extension
property is still countably triangle-free edge-covered. The construction is
an ordinary nonprincipal ultrapower, not the mutual-Fubini extension.
This is an auxiliary limitation on the saturation route to Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595CountableUltrapower
open Erdos595CountableExtension

noncomputable def U : Ultrafilter ℕ := Ultrafilter.of atTop
lemma U_le : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _

abbrev Functions := ℕ → Vertex
abbrev Point := Filter.Germ (U : Filter ℕ) Vertex
abbrev mk (f : Functions) : Point := Quotient.mk _ f
noncomputable abbrev rep (p : Point) : Functions := Quotient.out p

def raw : SimpleGraph Functions :=
  Erdos595CompleteFilterProduct.graph (U : Filter ℕ) (fun _ => G)
noncomputable def graph : SimpleGraph Point := raw.comap rep

lemma rep_mk (f : Functions) : rep (mk f) =ᶠ[(U : Filter ℕ)] f :=
  Quotient.exact (Quotient.out_eq (mk f))

lemma adj_mk (f : Functions) (p : Point) :
    graph.Adj (mk f) p ↔ ∀ᶠ n in (U : Filter ℕ), G.Adj (f n) (rep p n) := by
  apply Filter.eventually_congr
  exact (rep_mk f).mono (fun n hn => by rw [hn])

lemma eventually_ne {p q : Point} (hpq : p ≠ q) :
    ∀ᶠ n in (U : Filter ℕ), rep p n ≠ rep q n := by
  apply Ultrafilter.eventually_not.mpr
  intro he
  have h : mk (rep p) = mk (rep q) := Quotient.sound he
  exact hpq ((Quotient.out_eq p).symm.trans (h.trans (Quotient.out_eq q)))

lemma graph_cliqueFree : graph.CliqueFree 4 := by
  have h : raw.CliqueFree 4 := Erdos595CountableCoordinate.product_cliqueFree
    (U : Filter ℕ) (fun _ => G) 4 (fun _ => G_cliqueFree)
  have hr : Function.Injective (rep : Point → Functions) := Quotient.out_injective
  exact h.comap (SimpleGraph.Embedding.comap ⟨rep,hr⟩ raw)

lemma graph_cover : Erdos595Work.IsCountableUnionOfTriangleFree graph :=
  Erdos595CountableProduct.quotient_pi_countable_cover (fun _ : ℕ => Vertex)
    (Filter.germSetoid (U : Filter ℕ) Vertex) graph

/-- Constants embed the original countable generic graph. -/
noncomputable def constantEmbedding : G ↪g graph where
  toFun := fun a => mk (fun _ => a)
  inj' := by
    intro a b h
    exact Filter.eventually_const.mp (show ∀ᶠ _n in (U : Filter ℕ), a = b from Quotient.exact h)
  map_rel_iff' := by
    intro a b
    change graph.Adj (mk (fun _ => a)) (mk (fun _ => b)) ↔ G.Adj a b
    rw [adj_mk]
    have he : (∀ᶠ n in (U : Filter ℕ), G.Adj a (rep (mk (fun _ => b)) n)) ↔ G.Adj a b := by
      calc
        _ ↔ ∀ᶠ _n in (U : Filter ℕ), G.Adj a b :=
          Filter.eventually_congr ((rep_mk (fun _ => b)).mono (fun n hn => by rw [hn]))
        _ ↔ _ := Filter.eventually_const
    exact he

instance : Infinite Point := Infinite.of_injective constantEmbedding constantEmbedding.injective

/-- Countable saturation does not turn countable coverability into finite
coverability, even for this one fixed graph. -/
theorem no_finite_coloring (C : Type) [Finite C] :
    ¬Erdos595FinitePalette.HasColoring graph C := by
  intro hc
  exact Erdos595FiniteFolkman.generic_no_finite_coloring C (hc.comap constantEmbedding.toHom)

section Requests
variable (v : ℕ → Point) (b : ℕ → Bool)

noncomputable def pos (m n : ℕ) : Finset Vertex :=
  ((Finset.range m).filter (fun i => b i = true)).image (fun i => rep (v i) n)
noncomputable def neg (m n : ℕ) : Finset Vertex :=
  ((Finset.range m).filter (fun i => b i = false)).image (fun i => rep (v i) n)

def Good (m n : ℕ) : Prop :=
  (G.induce (pos v b m n : Set Vertex)).CliqueFree 3 ∧
    Disjoint (pos v b m n) (neg v b m n)

lemma good_zero (n : ℕ) : Good v b 0 n := by
  constructor
  · simp only [pos,Finset.range_zero]
    exact SimpleGraph.cliqueFree_of_card_lt (by simp)
  · simp [pos,neg]

variable
  (htf : ∀ i j k, b i = true → b j = true → b k = true →
    ¬(graph.Adj (v i) (v j) ∧ graph.Adj (v i) (v k) ∧ graph.Adj (v j) (v k)))
  (hsep : ∀ i j, b i = true → b j = false → v i ≠ v j)

include htf hsep in
lemma good_eventually (m : ℕ) : ∀ᶠ n in (U : Filter ℕ), Good v b m n := by
  have htri (i j k : Fin m) : ∀ᶠ n in (U : Filter ℕ),
      b i = true → b j = true → b k = true →
      ¬(G.Adj (rep (v i) n) (rep (v j) n) ∧
        G.Adj (rep (v i) n) (rep (v k) n) ∧ G.Adj (rep (v j) n) (rep (v k) n)) := by
    by_cases hi : b i = true
    · by_cases hj : b j = true
      · by_cases hk : b k = true
        · have hn : ¬∀ᶠ n in (U : Filter ℕ),
              G.Adj (rep (v i) n) (rep (v j) n) ∧
              G.Adj (rep (v i) n) (rep (v k) n) ∧ G.Adj (rep (v j) n) (rep (v k) n) := by
            intro h
            exact htf i j k hi hj hk ⟨h.mono (fun _ => And.left),
              h.mono (fun _ => And.left ∘ And.right),h.mono (fun _ => And.right ∘ And.right)⟩
          exact (Ultrafilter.eventually_not.mpr hn).mono (fun _ h _ _ _ => h)
        · exact Filter.Eventually.of_forall (fun _ _ _ h => (hk h).elim)
      · exact Filter.Eventually.of_forall (fun _ _ h => (hj h).elim)
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  have hdiff (i j : Fin m) : ∀ᶠ n in (U : Filter ℕ),
      b i = true → b j = false → rep (v i) n ≠ rep (v j) n := by
    by_cases hi : b i = true
    · by_cases hj : b j = false
      · exact (eventually_ne (hsep i j hi hj)).mono (fun _ h _ _ => h)
      · exact Filter.Eventually.of_forall (fun _ _ h => (hj h).elim)
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  have hall := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr
    (fun j => Filter.eventually_all.mpr (htri i j)))
  have hdall := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hdiff i))
  filter_upwards [hall,hdall] with n hn hd
  constructor
  · intro s hs
    obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (show x.val ∈ ((Finset.range m).filter (fun i => b i = true)).image (fun i => rep (v i) n) from x.property)
    obtain ⟨j,hj,hf⟩ := Finset.mem_image.mp (show y.val ∈ ((Finset.range m).filter (fun i => b i = true)).image (fun i => rep (v i) n) from y.property)
    obtain ⟨k,hk,hg⟩ := Finset.mem_image.mp (show z.val ∈ ((Finset.range m).filter (fun i => b i = true)).image (fun i => rep (v i) n) from z.property)
    obtain ⟨him,hbi⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjm,hbj⟩ := Finset.mem_filter.mp hj
    obtain ⟨hkm,hbk⟩ := Finset.mem_filter.mp hk
    apply hn ⟨i,Finset.mem_range.mp him⟩ ⟨j,Finset.mem_range.mp hjm⟩
      ⟨k,Finset.mem_range.mp hkm⟩ hbi hbj hbk
    exact ⟨by simpa only [he,hf] using hxy,by simpa only [he,hg] using hxz,
      by simpa only [hf,hg] using hyz⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hj,hf⟩ := Finset.mem_image.mp hy
    obtain ⟨him,hbi⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjm,hbj⟩ := Finset.mem_filter.mp hj
    exact hd ⟨i,Finset.mem_range.mp him⟩ ⟨j,Finset.mem_range.mp hjm⟩ hbi hbj
      (he.trans hf.symm)

noncomputable def height (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun m => Good v b m n) n

lemma good_height (n : ℕ) : Good v b (height v b n) n := by
  classical
  exact Nat.findGreatest_spec (P := fun m => Good v b m n) (Nat.zero_le n) (good_zero v b n)

include htf hsep in
lemma height_eventually (m : ℕ) : ∀ᶠ n in (U : Filter ℕ), m ≤ height v b n := by
  classical
  filter_upwards [good_eventually v b htf hsep m,U_le (eventually_ge_atTop m)] with n hn hmn
  exact Nat.le_findGreatest hmn hn

include htf hsep in
/-- Every consistent countable list of adjacency and nonadjacency requests
with triangle-free positive part has a fresh realization. -/
theorem sequence_extension : ∃ p : Point, (∀ i, p ≠ v i) ∧
    (∀ i, b i = true → graph.Adj p (v i)) ∧
    (∀ i, b i = false → ¬graph.Adj p (v i)) := by
  classical
  have hex (n : ℕ) := finite_extension (pos v b (height v b n) n)
    (neg v b (height v b n) n) (good_height v b n).1 (good_height v b n).2
  choose f hf using hex
  have hm (i n : ℕ) (hi : i < height v b n) :
      rep (v i) n ∈ pos v b (height v b n) n ∪ neg v b (height v b n) n := by
    cases hb : b i
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hb⟩,rfl⟩
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hb⟩,rfl⟩
  refine ⟨mk f,?_,?_,?_⟩
  · intro i he
    have heq : f =ᶠ[(U : Filter ℕ)] rep (v i) :=
      (rep_mk f).symm.trans (he ▸ Filter.EventuallyEq.refl _ _)
    obtain ⟨n,hn,hn'⟩ := ((height_eventually v b htf hsep (i+1)).and heq).exists
    exact (hf n).1 (hn' ▸ hm i n (by omega))
  · intro i hi
    apply (adj_mk f (v i)).mpr
    filter_upwards [height_eventually v b htf hsep (i+1)] with n hn
    apply (hf n).2.1
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hi⟩,rfl⟩
  · intro i hi hadj
    have hh := (adj_mk f (v i)).mp hadj
    obtain ⟨n,hn,hadj'⟩ := ((height_eventually v b htf hsep (i+1)).and hh).exists
    apply (hf n).2.2 _ ?_ hadj'
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hi⟩,rfl⟩

end Requests

/-- The exact countable one-point extension property, including negative
requests and freshness. Only the positive induced graph must be triangle-free. -/
theorem countable_extension (S T : Set Point) (hS : S.Countable) (hT : T.Countable)
    (hST : Disjoint S T) (hTF : (graph.induce S).CliqueFree 3) :
    ∃ p : Point, p ∉ S ∪ T ∧ (∀ q ∈ S, graph.Adj p q) ∧ (∀ q ∈ T, ¬graph.Adj p q) := by
  classical
  by_cases hu : (S ∪ T).Nonempty
  · letI : Nonempty ↥(S ∪ T) := hu.to_subtype
    letI : Countable ↥(S ∪ T) := (hS.union hT).to_subtype
    obtain ⟨e,he⟩ := exists_surjective_nat ↥(S ∪ T)
    let v : ℕ → Point := fun i => (e i).val
    let b : ℕ → Bool := fun i => decide (v i ∈ S)
    have hb (i : ℕ) : b i = true ↔ v i ∈ S := by simp [b]
    have hb' (i : ℕ) : b i = false ↔ v i ∉ S := by simp [b]
    have ht : ∀ i j k, b i = true → b j = true → b k = true →
        ¬(graph.Adj (v i) (v j) ∧ graph.Adj (v i) (v k) ∧ graph.Adj (v j) (v k)) := by
      intro i j k hi hj hk hh
      exact hTF _ (SimpleGraph.is3Clique_triple_iff.mpr
        (show (graph.induce S).Adj ⟨v i,(hb i).mp hi⟩ ⟨v j,(hb j).mp hj⟩ ∧
          (graph.induce S).Adj ⟨v i,(hb i).mp hi⟩ ⟨v k,(hb k).mp hk⟩ ∧
          (graph.induce S).Adj ⟨v j,(hb j).mp hj⟩ ⟨v k,(hb k).mp hk⟩ from hh))
    have hs : ∀ i j, b i = true → b j = false → v i ≠ v j := by
      intro i j hi hj hij
      exact (hb' j).mp hj (hij ▸ (hb i).mp hi)
    obtain ⟨p,hp,hpos,hneg⟩ := sequence_extension v b ht hs
    refine ⟨p,?_,?_,?_⟩
    · intro hpu
      obtain ⟨i,hi⟩ := he ⟨p,hpu⟩
      exact hp i (congrArg Subtype.val hi).symm
    · intro q hq
      obtain ⟨i,hi⟩ := he ⟨q,Or.inl hq⟩
      have hv : v i = q := congrArg Subtype.val hi
      exact hv ▸ hpos i ((hb i).mpr (by simpa only [hv] using hq))
    · intro q hq
      obtain ⟨i,hi⟩ := he ⟨q,Or.inr hq⟩
      have hv : v i = q := congrArg Subtype.val hi
      have hn : v i ∉ S := by
        intro h
        exact Set.disjoint_left.mp hST (hv ▸ h) hq
      exact hv ▸ hneg i ((hb' i).mpr hn)
  · have hn (p : Point) : p ∉ S ∪ T := fun hp => hu ⟨p,hp⟩
    exact ⟨mk (fun _ => seed 0),hn _,fun q hq => (hn q (Or.inl hq)).elim,
      fun q hq => (hn q (Or.inr hq)).elim⟩

/-- A single covered K4-free graph has both exact countable neighborhood
extension and no finite edge palette. Neither property settles Erdős 595. -/
theorem covered_extension_graph :
    ∃ (A : Type) (_ : Infinite A) (H : SimpleGraph A),
      H.CliqueFree 4 ∧ Erdos595Work.IsCountableUnionOfTriangleFree H ∧
      (∀ (C : Type) (_ : Finite C), ¬Erdos595FinitePalette.HasColoring H C) ∧
      ∀ (S T : Set A), S.Countable → T.Countable → Disjoint S T →
        (H.induce S).CliqueFree 3 →
        ∃ p : A, p ∉ S ∪ T ∧ (∀ q ∈ S, H.Adj p q) ∧ (∀ q ∈ T, ¬H.Adj p q) := by
  exact ⟨Point,inferInstance,graph,graph_cliqueFree,graph_cover,
    fun C _ => no_finite_coloring C,countable_extension⟩

#print axioms covered_extension_graph
#print axioms countable_extension
#print axioms no_finite_coloring
#print axioms graph_cliqueFree
#print axioms graph_cover
#print axioms sequence_extension
end Erdos595CountableUltrapower
