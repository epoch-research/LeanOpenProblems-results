import FormalConjecturesUtil
import Submission.CompactSymmRootsAudit

/-! Bounded blow-ups can make every vertex unsafe to clone. This is a
structural reduction, not an extremal-rate transfer or a rationality proof. -/
open SimpleGraph Finset
namespace Erdos713CloneSaturation
open Erdos713Cloning

variable {V W : Type*}

def ambient (G : SimpleGraph V) (k : ℕ) : SimpleGraph (V × Fin (k+1)) :=
  G.comap Prod.fst

def subgraph (G : SimpleGraph V) (k : ℕ) (S : Finset (V × Fin (k+1))) :
    SimpleGraph S := (ambient G k).induce (↑S)

def HasBase {k : ℕ} (S : Finset (V × Fin (k+1))) : Prop :=
  ∀ v : V, (v,0) ∈ S

lemma base_copy (G : SimpleGraph V) (k : ℕ) (S : Finset (V × Fin (k+1)))
    (hS : HasBase S) : G ⊑ subgraph G k S := by
  refine ⟨⟨⟨fun v => ⟨(v,0),hS v⟩,fun h => h⟩,?_⟩⟩
  intro u v h
  exact congrArg (fun x : S => x.val.1) h

lemma degree_lower [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (S : Finset (V × Fin (k+1))) (hS : HasBase S) (x : S) :
    Nat.card (G.neighborSet x.val.1) ≤ Nat.card ((subgraph G k S).neighborSet x) := by
  classical
  let f : G.neighborSet x.val.1 → (subgraph G k S).neighborSet x :=
    fun v => ⟨⟨(v.val,0),hS v.val⟩,v.property⟩
  apply Nat.card_le_card_of_injective f
  intro u v h
  exact Subtype.ext (congrArg (fun y : (subgraph G k S).neighborSet x => y.val.val.1) h)

lemma missing_point [Fintype V] [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (G : SimpleGraph V)
    (hdeg : ∀ v, Fintype.card W ≤ Nat.card (G.neighborSet v))
    (S : Finset (V × Fin (Fintype.card W+1))) (hS : HasBase S)
    (hf : H.Free (subgraph G (Fintype.card W) S)) (x : S) :
    ∃ i : Fin (Fintype.card W+1), (x.val.1,i) ∉ S := by
  classical
  by_contra hn
  push_neg at hn
  let T : Finset S := univ.filter (fun y => y.val.1 = x.val.1)
  have htwin : ∀ y ∈ T,
      (subgraph G (Fintype.card W) S).neighborSet y =
        (subgraph G (Fintype.card W) S).neighborSet x := by
    intro y hy
    have he : y.val.1 = x.val.1 := (mem_filter.mp hy).2
    ext z
    change G.Adj y.val.1 z.val.1 ↔ G.Adj x.val.1 z.val.1
    rw [he]
  have hcard : Fintype.card W+1 ≤ T.card := by
    let f : Fin (Fintype.card W+1) → T := fun i =>
      ⟨⟨(x.val.1,i),hn i⟩,by simp [T]⟩
    have hi : Function.Injective f := by
      intro i j h
      exact congrArg (fun y : T => y.val.val.2) h
    have hc := Fintype.card_le_of_injective f hi
    simpa using hc
  rcases Erdos713CloneSymm.twins_card_or_degree hH hf T htwin with hc | hd
  · omega
  · have hdl := (hdeg x.val.1).trans (degree_lower G _ S hS x)
    omega

open scoped Classical in
noncomputable def insert_iso (G : SimpleGraph V) (k : ℕ) (S : Finset (V × Fin (k+1)))
    (x : S) (i : Fin (k+1)) (hi : (x.val.1,i) ∉ S) :
    clone (subgraph G k S) x ≃g subgraph G k (insert (x.val.1,i) S) := by
  classical
  let p : V × Fin (k+1) := (x.val.1,i)
  let f : Option S → (insert p S : Finset (V × Fin (k+1)))
    | none => ⟨p,mem_insert_self p S⟩
    | some y => ⟨y.val,mem_insert_of_mem y.property⟩
  have hinj : Function.Injective f := by
    rintro (a|a) (b|b) h
    · rfl
    · have he : p = b.val := congrArg Subtype.val h
      apply False.elim
      apply hi
      change p ∈ S
      rw [he]
      exact b.property
    · have he : a.val = p := congrArg Subtype.val h
      apply False.elim
      apply hi
      change p ∈ S
      rw [← he]
      exact a.property
    · apply congrArg some
      apply Subtype.ext
      exact congrArg (fun y : (insert p S : Finset (V × Fin (k+1))) => y.val) h
  have hsurj : Function.Surjective f := by
    intro y
    rcases mem_insert.mp y.property with hy | hy
    · exact ⟨none,Subtype.ext hy.symm⟩
    · exact ⟨some ⟨y.val,hy⟩,rfl⟩
  refine ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩,?_⟩
  rintro (a|a) (b|b) <;> exact Iff.rfl

/-- A bounded blow-up containing the original graph, with no safe full clone.
The output is not claimed to be extremal, or to satisfy extremal record bounds. -/
theorem exists_saturated [Fintype V] [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (G : SimpleGraph V) (hf : H.Free G)
    (hdeg : ∀ v, Fintype.card W ≤ Nat.card (G.neighborSet v)) :
    ∃ S : Finset (V × Fin (Fintype.card W+1)), HasBase S ∧
      H.Free (subgraph G (Fintype.card W) S) ∧
      G ⊑ subgraph G (Fintype.card W) S ∧
      S.card ≤ (Fintype.card W+1)*Fintype.card V ∧
      (∀ x : S, Nat.card (G.neighborSet x.val.1) ≤
        Nat.card ((subgraph G (Fintype.card W) S).neighborSet x)) ∧
      ∀ x : S, SingleFold H (subgraph G (Fintype.card W) S) x := by
  classical
  let k := Fintype.card W
  let S₀ : Finset (V × Fin (k+1)) := univ.filter (fun y => y.2 = 0)
  have hb₀ : HasBase S₀ := by intro v; simp [S₀]
  have hf₀ : H.Free (subgraph G k S₀) := by
    have hc : subgraph G k S₀ ⊑ G := by
      refine ⟨⟨⟨fun y => y.val.1,fun h => h⟩,?_⟩⟩
      intro u v h
      apply Subtype.ext
      apply Prod.ext h
      have hu : u.val.2 = 0 := (mem_filter.mp u.property).2
      have hv : v.val.2 = 0 := (mem_filter.mp v.property).2
      exact hu.trans hv.symm
    exact fun h => hf (h.trans hc)
  let F : Finset (Finset (V × Fin (k+1))) :=
    univ.filter (fun S => HasBase S ∧ H.Free (subgraph G k S))
  have hF : F.Nonempty := ⟨S₀,by simp only [F,mem_filter,mem_univ,true_and]; exact ⟨hb₀,hf₀⟩⟩
  obtain ⟨S,hSF,hmax⟩ := F.exists_max_image Finset.card hF
  have hS : HasBase S := (mem_filter.mp hSF).2.1
  have hfree : H.Free (subgraph G k S) := (mem_filter.mp hSF).2.2
  refine ⟨S,hS,hfree,base_copy G k S hS,?_,degree_lower G k S hS,?_⟩
  · have hs := S.card_le_univ
    simpa only [Fintype.card_prod,Fintype.card_fin,mul_comm] using hs
  · intro x
    apply fold_of_obstructed H (subgraph G k S) x hfree
    by_contra hsafe
    obtain ⟨i,hi⟩ := missing_point H hH G hdeg S hS hfree x
    let T := insert (x.val.1,i) S
    have hT : HasBase T := fun v => mem_insert_of_mem (hS v)
    have hfT : H.Free (subgraph G k T) := by
      intro hc
      exact hsafe (hc.trans ⟨(insert_iso G k S x i hi).symm.toCopy⟩)
    have hTF : T ∈ F := by
      simp only [F,mem_filter,mem_univ,true_and]
      exact ⟨hT,hfT⟩
    have hc := hmax T hTF
    have ht : T.card = S.card+1 := card_insert_of_notMem hi
    omega

lemma bipartite {G : SimpleGraph V} (hG : G.IsBipartite) (k : ℕ)
    (S : Finset (V × Fin (k+1))) : (subgraph G k S).IsBipartite :=
  hG.of_hom (show subgraph G k S →g G from ⟨fun x => x.val.1,fun h => h⟩)

lemma vertex_lower [Fintype V] {k : ℕ} {S : Finset (V × Fin (k+1))}
    (hS : HasBase S) : Fintype.card V ≤ S.card := by
  let f : V → S := fun v => ⟨(v,0),hS v⟩
  have hi : Function.Injective f := fun _ _ h => congrArg (fun y : S => y.val.1) h
  simpa using Fintype.card_le_of_injective f hi

lemma edge_lower [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (S : Finset (V × Fin (k+1))) (hS : HasBase S) :
    Nat.card G.edgeSet ≤ Nat.card (subgraph G k S).edgeSet := by
  obtain ⟨f⟩ := base_copy G k S hS
  exact Nat.card_le_card_of_injective f.mapEdgeSet f.mapEdgeSet.injective

lemma ambient_degree [Fintype V] (G : SimpleGraph V) (k : ℕ) (x : V × Fin (k+1)) :
    Nat.card ((ambient G k).neighborSet x) = Nat.card (G.neighborSet x.1)*(k+1) := by
  let f : (ambient G k).neighborSet x ≃ G.neighborSet x.1 × Fin (k+1) := {
    toFun := fun y => (⟨y.val.1,y.property⟩,y.val.2)
    invFun := fun y => ⟨(y.1.val,y.2),y.1.property⟩
    left_inv := fun y => by cases y; rfl
    right_inv := fun y => by cases y; rfl }
  simpa only [Nat.card_prod,Nat.card_fin] using Nat.card_congr f

lemma degree_upper [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (S : Finset (V × Fin (k+1))) (x : S) :
    Nat.card ((subgraph G k S).neighborSet x) ≤ Nat.card (G.neighborSet x.val.1)*(k+1) := by
  let f := (Copy.induce (ambient G k) (↑S)).mapNeighborSet x
  have h := Nat.card_le_card_of_injective f f.injective
  exact h.trans_eq (ambient_degree G k x.val)

lemma ambient_edges [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    Nat.card (ambient G k).edgeSet = (k+1)^2*Nat.card G.edgeSet := by
  classical
  have hg := G.sum_degrees_eq_twice_card_edges
  have ha := (ambient G k).sum_degrees_eq_twice_card_edges
  simp only [←card_neighborSet_eq_degree,edgeFinset_card,Fintype.card_eq_nat_card] at hg ha
  have hs : (∑ x : V × Fin (k+1), Nat.card ((ambient G k).neighborSet x)) =
      (k+1)^2 * ∑ v : V, Nat.card (G.neighborSet v) := by
    simp only [ambient_degree,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul]
    simp only [←Finset.mul_sum,←Finset.sum_mul]
    ring
  rw [ha,hg] at hs
  nlinarith only [hs]

lemma edge_upper [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (S : Finset (V × Fin (k+1))) :
    Nat.card (subgraph G k S).edgeSet ≤ (k+1)^2*Nat.card G.edgeSet := by
  let f := (Copy.induce (ambient G k) (↑S)).mapEdgeSet
  have h := Nat.card_le_card_of_injective f f.injective
  exact h.trans_eq (ambient_edges G k)

/-- Both sizes and edge counts stay within fixed factors; bipartiteness and
large minimum degree are preserved. No exact leading constant is asserted. -/
theorem exists_saturated_bounds [Fintype V] [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (G : SimpleGraph V) (hG : G.IsBipartite) (hf : H.Free G)
    (hdeg : ∀ v, Fintype.card W ≤ Nat.card (G.neighborSet v)) :
    ∃ S : Finset (V × Fin (Fintype.card W+1)), HasBase S ∧
      H.Free (subgraph G (Fintype.card W) S) ∧
      (subgraph G (Fintype.card W) S).IsBipartite ∧
      (Fintype.card V ≤ S.card ∧ S.card ≤ (Fintype.card W+1)*Fintype.card V) ∧
      (Nat.card G.edgeSet ≤ Nat.card (subgraph G (Fintype.card W) S).edgeSet ∧
        Nat.card (subgraph G (Fintype.card W) S).edgeSet ≤
          (Fintype.card W+1)^2*Nat.card G.edgeSet) ∧
      (∀ x : S, Nat.card (G.neighborSet x.val.1) ≤
        Nat.card ((subgraph G (Fintype.card W) S).neighborSet x) ∧
        Nat.card ((subgraph G (Fintype.card W) S).neighborSet x) ≤
          Nat.card (G.neighborSet x.val.1)*(Fintype.card W+1)) ∧
      ∀ x : S, SingleFold H (subgraph G (Fintype.card W) S) x := by
  obtain ⟨S,hS,hfree,_,hcard,hdegree,hfold⟩ := exists_saturated H hH G hf hdeg
  exact ⟨S,hS,hfree,bipartite hG _ S,⟨vertex_lower hS,hcard⟩,
    ⟨edge_lower G _ S hS,edge_upper G _ S⟩,
    fun x => ⟨hdegree x,degree_upper G _ S x⟩,hfold⟩

#print axioms exists_saturated
#print axioms ambient_edges
#print axioms exists_saturated_bounds
end Erdos713CloneSaturation
