import Submission.Projection
import Submission.TourCover

/-! Extending an edge-bijective spanning cover by putting the remaining edges at chosen copies. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma degree_sup_of_edge_disjoint {V : Type*} [Fintype V] (A B : SimpleGraph V)
    (hd : Disjoint A.edgeSet B.edgeSet) (v : V) :
    (A ⊔ B).degree v = A.degree v + B.degree v := by
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]
  change (A.neighborSet v ∪ B.neighborSet v).ncard = _
  refine Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _)
  apply Set.disjoint_left.mpr
  intro w hwa hwb
  exact Set.disjoint_left.mp hd (show s(v, w) ∈ A.edgeSet from hwa)
    (show s(v, w) ∈ B.edgeSet from hwb)

lemma map_degree_image {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (s : V ↪ W) (v : V) : (G.map s).degree (s v) = G.degree v := by
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]
  have heq : (G.map s).neighborSet (s v) = s '' G.neighborSet v := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.map_adj, Set.mem_image]
    constructor
    · rintro ⟨x, y, hxy, hx, hy⟩
      obtain rfl := s.injective hx
      exact ⟨y, hxy, hy⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨v, y, hy, rfl, rfl⟩
  rw [heq, Set.ncard_image_of_injective _ s.injective]

lemma map_degree_outside_range {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (s : V ↪ W) (w : W) (hw : w ∉ Set.range s) :
    (G.map s).degree w = 0 := by
  apply ((G.map s).degree_eq_zero_iff_notMem_support w).mpr
  rintro ⟨y, x, z, hxz, hx, _⟩
  exact hw ⟨x, hx⟩

lemma even_sdiff_of_even {V : Type*} [Fintype V] {G R : SimpleGraph V}
    (hRG : R ≤ G) (heG : ∀ v, Even (G.degree v)) (heR : ∀ v, Even (R.degree v)) :
    ∀ v, Even ((G \ R).degree v) := by
  intro v
  rw [degree_sdiff_of_le hRG]
  obtain ⟨a, ha⟩ := heG v
  obtain ⟨b, hb⟩ := heR v
  exact ⟨a - b, by omega⟩

lemma extend_regular_two_cover {V W : Type*} [Fintype V] [Fintype W]
    (G R : SimpleGraph V) (hRG : R ≤ G)
    (heG : ∀ v, Even (G.degree v)) (heR : ∀ v, Even (R.degree v))
    (C : SimpleGraph W) (hr : C.IsRegularOfDegree 2) (f : C →g R)
    (hi : Set.InjOn (Sym2.map f) C.edgeSet)
    (hs : Set.SurjOn (Sym2.map f) C.edgeSet R.edgeSet)
    (hv : Function.Surjective f) :
    ∃ K : SimpleGraph W, C ≤ K ∧ (∀ w, Even (K.degree w)) ∧
      ∃ π : K →g G,
        Set.InjOn (Sym2.map π) K.edgeSet ∧
        Set.SurjOn (Sym2.map π) K.edgeSet G.edgeSet ∧
        ∃ B : Set W, Set.InjOn π Bᶜ ∧ (∀ w ∈ B, K.degree w = 2) ∧
          B.ncard + Fintype.card V = Fintype.card W := by
  let s : V ↪ W := ⟨Function.surjInv hv, (Function.rightInverse_surjInv hv).injective⟩
  have hsec (v : V) : f (s v) = v := Function.rightInverse_surjInv hv v
  have hsym (e : Sym2 V) : Sym2.map f (Sym2.map s e) = e := by
    induction e using Sym2.ind with
    | h x y => simp only [Sym2.map_pair_eq, hsec]
  let A := (G \ R).map s
  have hblue (e : Sym2 W) (he : e ∈ A.edgeSet) :
      (Sym2.map f e ∈ G.edgeSet ∧ Sym2.map f e ∉ R.edgeSet) ∧
        Sym2.map s (Sym2.map f e) = e := by
    change e ∈ ((G \ R).map s).edgeSet at he
    rw [SimpleGraph.edgeSet_map] at he
    obtain ⟨d, hd, rfl⟩ := he
    change (Sym2.map f (Sym2.map s d) ∈ G.edgeSet ∧
      Sym2.map f (Sym2.map s d) ∉ R.edgeSet) ∧
      Sym2.map s (Sym2.map f (Sym2.map s d)) = Sym2.map s d
    rw [hsym]
    exact ⟨by simpa only [SimpleGraph.edgeSet_sdiff, Set.mem_diff] using hd, rfl⟩
  have hdis : Disjoint C.edgeSet A.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heC heA
    exact (hblue e heA).1.2 (f.map_mem_edgeSet heC)
  have hdegA : ∀ w, Even (A.degree w) := by
    intro w
    by_cases hw : w ∈ Set.range s
    · obtain ⟨v, rfl⟩ := hw
      have hdeg := map_degree_image (G \ R) s v
      have he := even_sdiff_of_even hRG heG heR v
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdeg he ⊢
      rwa [hdeg]
    · have hzero := map_degree_outside_range (G \ R) s w hw
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hzero ⊢
      rw [hzero]
      decide
  let K := C ⊔ A
  have hdegree (w : W) : K.degree w = 2 + A.degree w := by
    have hh := degree_sup_of_edge_disjoint C A hdis w
    have hh' := hr w
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hh' ⊢
    rwa [hh'] at hh
  let π : K →g G := {
    toFun := f
    map_rel' := by
      intro x y hxy
      rcases hxy with hxy | hxy
      · exact hRG (f.map_adj hxy)
      · have hh := (hblue s(x, y) hxy).1.1
        exact hh }
  refine ⟨K, le_sup_left, ?_, π, ?_, ?_, (Set.range s)ᶜ, ?_, ?_, ?_⟩
  · intro w
    have hh : Even (K.degree w) := by rw [hdegree]; exact (by decide : Even (2 : ℕ)).add (hdegA w)
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hh
  · intro e he d hd hed
    change Sym2.map f e = Sym2.map f d at hed
    change e ∈ (C ⊔ A).edgeSet at he
    change d ∈ (C ⊔ A).edgeSet at hd
    rw [SimpleGraph.edgeSet_sup] at he hd
    rcases he with he | he <;> rcases hd with hd | hd
    · exact hi he hd hed
    · exact ((hblue d hd).1.2 (hed ▸ f.map_mem_edgeSet he)).elim
    · exact ((hblue e he).1.2 (hed.symm ▸ f.map_mem_edgeSet hd)).elim
    · rw [← (hblue e he).2, ← (hblue d hd).2, hed]
  · intro e he
    change ∃ d, d ∈ (C ⊔ A).edgeSet ∧ Sym2.map f d = e
    rw [SimpleGraph.edgeSet_sup]
    by_cases heR : e ∈ R.edgeSet
    · obtain ⟨d, hd, hde⟩ := hs heR
      exact ⟨d, Or.inl hd, hde⟩
    · refine ⟨Sym2.map s e, Or.inr ?_, hsym e⟩
      change Sym2.map s e ∈ ((G \ R).map s).edgeSet
      rw [SimpleGraph.edgeSet_map]
      refine ⟨e, ?_, rfl⟩
      rw [SimpleGraph.edgeSet_sdiff]
      exact ⟨he, heR⟩
  · intro x hx y hy hxy
    have hx' : x ∈ Set.range s := by simpa using hx
    have hy' : y ∈ Set.range s := by simpa using hy
    obtain ⟨a, rfl⟩ := hx'
    obtain ⟨b, rfl⟩ := hy'
    change f (s a) = f (s b) at hxy
    rw [hsec, hsec] at hxy
    rw [hxy]
  · intro w hw
    have hz := map_degree_outside_range (G \ R) s w hw
    have hh := hdegree w
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hz hh ⊢
    change Nat.card (A.neighborSet w) = 0 at hz
    simpa only [hz, add_zero] using hh
  · have hrange : (Set.range s).ncard = Fintype.card V := by
      rw [Set.ncard_range_of_injective s.injective, Nat.card_eq_fintype_card]
    have hh := Set.ncard_union_add_ncard_inter (Set.range s)ᶜ (Set.range s)
    simpa only [Set.compl_union_self, Set.compl_inter_self, Set.ncard_empty, add_zero,
      Set.ncard_univ, hrange, Nat.card_eq_fintype_card] using hh.symm

end Erdos184
