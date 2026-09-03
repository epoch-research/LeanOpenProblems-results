import Submission.DoubleTripleAssembly
import Submission.MaximumCoreFamilies

/-! Extracting the six junctions from pairwise two-point contacts. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.DoubleTripleCertificates
open CycleSegments MaximumCoreFamilies
set_option maxHeartbeats 3000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma six_contact_vertices (S : Fin 3 → Set V)
    (h01 : (S 0 ∩ S 1).ncard = 2) (h02 : (S 0 ∩ S 2).ncard = 2)
    (h12 : (S 1 ∩ S 2).ncard = 2) (htriple : ∀ x, ¬ (x ∈ S 0 ∧ x ∈ S 1 ∧ x ∈ S 2)) :
    ∃ vertex : Fin 6 → V, Function.Injective vertex ∧
      (∀ k w, vertex w ∈ S k ↔ ∃ i, place k i = w) ∧
      (∀ k l, k ≠ l → ∀ x, x ∈ S k → x ∈ S l → ∃ w, vertex w = x) := by
  obtain ⟨a,b,hab,heab⟩ := Set.ncard_eq_two.mp h01
  obtain ⟨c,d,hcd,hecd⟩ := Set.ncard_eq_two.mp h02
  obtain ⟨e,f,hef,heef⟩ := Set.ncard_eq_two.mp h12
  have r01 (x : V) : (x ∈ S 0 ∧ x ∈ S 1) ↔ x = a ∨ x = b := by
    change x ∈ S 0 ∩ S 1 ↔ _
    rw [heab]
    simp
  have r02 (x : V) : (x ∈ S 0 ∧ x ∈ S 2) ↔ x = c ∨ x = d := by
    change x ∈ S 0 ∩ S 2 ↔ _
    rw [hecd]
    simp
  have r12 (x : V) : (x ∈ S 1 ∧ x ∈ S 2) ↔ x = e ∨ x = f := by
    change x ∈ S 1 ∩ S 2 ↔ _
    rw [heef]
    simp
  obtain ⟨ha0,ha1⟩ := (r01 a).mpr (Or.inl rfl)
  obtain ⟨hb0,hb1⟩ := (r01 b).mpr (Or.inr rfl)
  obtain ⟨hc0,hc2⟩ := (r02 c).mpr (Or.inl rfl)
  obtain ⟨hd0,hd2⟩ := (r02 d).mpr (Or.inr rfl)
  obtain ⟨he1,he2⟩ := (r12 e).mpr (Or.inl rfl)
  obtain ⟨hf1,hf2⟩ := (r12 f).mpr (Or.inr rfl)
  have ha2 : a ∉ S 2 := fun h => htriple a ⟨ha0,ha1,h⟩
  have hb2 : b ∉ S 2 := fun h => htriple b ⟨hb0,hb1,h⟩
  have hc1 : c ∉ S 1 := fun h => htriple c ⟨hc0,h,hc2⟩
  have hd1 : d ∉ S 1 := fun h => htriple d ⟨hd0,h,hd2⟩
  have he0 : e ∉ S 0 := fun h => htriple e ⟨h,he1,he2⟩
  have hf0 : f ∉ S 0 := fun h => htriple f ⟨h,hf1,hf2⟩
  let vertex : Fin 6 → V := ![a,b,c,d,e,f]
  refine ⟨vertex,?_,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [vertex]
  · intro k w
    fin_cases k <;> fin_cases w <;> simp_all [vertex,place,Fin.exists_fin_succ]
  · intro k l hkl x hx hy
    change ∃ w, ![a,b,c,d,e,f] w = x
    simp only [Fin.exists_fin_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.exists_fin_zero,or_false]
    fin_cases k <;> fin_cases l <;> simp_all only [ne_eq,not_true_eq_false]
    all_goals first
      | have h := (r01 x).mp ⟨hx,hy⟩; aesop
      | have h := (r01 x).mp ⟨hy,hx⟩; aesop
      | have h := (r02 x).mp ⟨hx,hy⟩; aesop
      | have h := (r02 x).mp ⟨hy,hx⟩; aesop
      | have h := (r12 x).mp ⟨hx,hy⟩; aesop
      | have h := (r12 x).mp ⟨hy,hx⟩; aesop

lemma two_contacts_at_least_four
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (h01 : ({x | x ∈ (C 0).support} ∩ {x | x ∈ (C 1).support}).ncard = 2)
    (h02 : ({x | x ∈ (C 0).support} ∩ {x | x ∈ (C 2).support}).ncard = 2)
    (h12 : ({x | x ∈ (C 1).support} ∩ {x | x ∈ (C 2).support}).ncard = 2)
    (htriple : ∀ x, ¬ (x ∈ (C 0).support ∧ x ∈ (C 1).support ∧ x ∈ (C 2).support))
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ 4 ≤ D.card := by
  obtain ⟨vertex,hi,hp,hm⟩ := six_contact_vertices (fun k => {x | x ∈ (C k).support}) h01 h02 h12 htriple
  exact contact_at_least_four vertex root C hC ⟨hi,hp,hm⟩ hdisC hcover

/-- In a maximum cycle decomposition, three pieces meeting pairwise in
exactly two vertices must have a common vertex. -/
lemma maximum_double_contacts_have_triple {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (hmem : ∀ k, (C k).toSubgraph ∈ D)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (h01 : ({x | x ∈ (C 0).support} ∩ {x | x ∈ (C 1).support}).ncard = 2)
    (h02 : ({x | x ∈ (C 0).support} ∩ {x | x ∈ (C 2).support}).ncard = 2)
    (h12 : ({x | x ∈ (C 1).support} ∩ {x | x ∈ (C 2).support}).ncard = 2) :
    ∃ x, x ∈ (C 0).support ∧ x ∈ (C 1).support ∧ x ∈ (C 2).support := by
  by_contra h
  have htriple : ∀ x, ¬ (x ∈ (C 0).support ∧ x ∈ (C 1).support ∧ x ∈ (C 2).support) :=
    fun x hx => h ⟨x,hx⟩
  let A := IndexedCycles.image root C
  have hAD : A ⊆ D := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact hmem i
  have hcard : A.card = 3 := by
    simpa using IndexedCycles.card root C hC hdisC
  obtain ⟨E,hE,hdE,hcE⟩ := two_contacts_at_least_four root (IndexedCycles.restrict root C)
    (IndexedCycles.restrict_cycle root C hC) (IndexedCycles.restrict_disjoint root C hdisC)
    (by simpa only [IndexedCycles.restrict_support] using h01)
    (by simpa only [IndexedCycles.restrict_support] using h02)
    (by simpa only [IndexedCycles.restrict_support] using h12)
    (by simpa only [IndexedCycles.restrict_support] using htriple)
    (IndexedCycles.restrict_cover root C)
  have hb := hD.subfamily_bound A hAD E hE hdE
  omega

lemma maximum_three_pieces_double_contacts {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (T : Fin 3 → G.Subgraph) (hT : Function.Injective T) (hmem : ∀ i, T i ∈ D)
    (h01 : ((T 0).verts ∩ (T 1).verts).ncard = 2)
    (h02 : ((T 0).verts ∩ (T 2).verts).ncard = 2)
    (h12 : ((T 1).verts ∩ (T 2).verts).ncard = 2) :
    ∃ x, x ∈ (T 0).verts ∧ x ∈ (T 1).verts ∧ x ∈ (T 2).verts := by
  have hw (i : Fin 3) : ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.toSubgraph = T i := by
    obtain ⟨v⟩ := (hD.1 (T i) (hmem i)).1.nonempty
    obtain ⟨p,hp,he⟩ := LongRing.regular_cycle_walk_at (T i)
      (hD.1 (T i) (hmem i)).1 (hD.1 (T i) (hmem i)).2 v.val v.property
    exact ⟨v.val,p,hp,he⟩
  choose root C hC he using hw
  have hs (i : Fin 3) : {x | x ∈ (C i).support} = (T i).verts := by
    ext x
    rw [Set.mem_setOf_eq,← Walk.mem_verts_toSubgraph,he i]
  have hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges := by
    intro i j hij
    apply List.disjoint_left.mpr
    intro e hei hej
    apply Set.disjoint_left.mp (hD.2.1.1 (hmem i) (hmem j) (fun h => hij (hT h)))
    · rw [← he i]
      exact (C i).mem_edges_toSubgraph.mpr hei
    · rw [← he j]
      exact (C j).mem_edges_toSubgraph.mpr hej
  obtain ⟨x,hx0,hx1,hx2⟩ := maximum_double_contacts_have_triple hD root C hC
    (fun i => (he i).symm ▸ hmem i) hd
    (by rw [hs 0,hs 1]; exact h01) (by rw [hs 0,hs 2]; exact h02)
    (by rw [hs 1,hs 2]; exact h12)
  exact ⟨x,hs 0 ▸ hx0,hs 1 ▸ hx1,hs 2 ▸ hx2⟩

lemma maximum_three_pieces_four_degree {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hdeg : ∀ x, G.degree x ≤ 4)
    (T : Fin 3 → G.Subgraph) (hT : Function.Injective T) (hmem : ∀ i, T i ∈ D) :
    ¬ (((T 0).verts ∩ (T 1).verts).ncard = 2 ∧
      ((T 0).verts ∩ (T 2).verts).ncard = 2 ∧
      ((T 1).verts ∩ (T 2).verts).ncard = 2) := by
  rintro ⟨h01,h02,h12⟩
  obtain ⟨x,hx0,hx1,hx2⟩ := maximum_three_pieces_double_contacts hD T hT hmem h01 h02 h12
  have hx (i : Fin 3) : x ∈ (T i).verts := by
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx2
  have hsub : Finset.univ.image T ⊆ D.filter (fun H => x ∈ H.verts) := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact Finset.mem_filter.mpr ⟨hmem i,hx i⟩
  have hlo : 3 ≤ (D.filter (fun H => x ∈ H.verts)).card := by
    have hb := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hT,Finset.card_univ,Fintype.card_fin] at hb
  have hi := piece_incidence_count hD.1 hD.2.1 x
  have hd := hdeg x
  omega

#print axioms maximum_three_pieces_four_degree
#print axioms maximum_three_pieces_double_contacts
#print axioms maximum_double_contacts_have_triple
#print axioms two_contacts_at_least_four
end Erdos184Work.DoubleTripleCertificates
