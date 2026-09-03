import Submission.MatchingIntegrated

/-! Independent cycle-visit suppression and positive shortest-cycle component surplus. -/
namespace Erdos583Work
/- Simultaneous suppression of independent degree-two vertices with distinct fresh shortcuts. -/
namespace IndependentSuppression
open SimpleGraph _root_.Erdos583Work _root_.Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*}

lemma adj_finset_sup (A : Finset V) (f : V → SimpleGraph V) (x y : V) :
    (A.sup f).Adj x y ↔ ∃ r ∈ A, (f r).Adj x y := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert r A hr ih => simp only [Finset.sup_insert,sup_adj,ih,Finset.mem_insert]; aesop

noncomputable def chords (A : Finset V) (a b : V → V) : SimpleGraph V :=
  A.sup fun r ↦ edge (a r) (b r)

noncomputable def spokes (A : Finset V) (a b : V → V) : SimpleGraph V :=
  A.sup fun r ↦ edge (a r) r ⊔ edge r (b r)

lemma chords_insert (A : Finset V) (r : V) (a b : V → V) :
    chords (insert r A) a b=edge (a r) (b r) ⊔ chords A a b := by
  simp only [chords,Finset.sup_insert]

lemma spokes_insert (A : Finset V) (r : V) (a b : V → V) :
    spokes (insert r A) a b=(edge (a r) r ⊔ edge r (b r)) ⊔ spokes A a b := by
  simp only [spokes,Finset.sup_insert]

lemma spokes_adj (A : Finset V) (a b : V → V) (x y : V) :
    (spokes A a b).Adj x y ↔ ∃ r ∈ A, (edge (a r) r).Adj x y ∨ (edge r (b r)).Adj x y := by
  exact adj_finset_sup A (fun r ↦ edge (a r) r ⊔ edge r (b r)) x y

lemma spokes_endpoint (A : Finset V) (a b : V → V) {x y : V}
    (h : (spokes A a b).Adj x y) : x ∈ A ∨ y ∈ A := by
  obtain ⟨r,hr,h|h⟩ := (spokes_adj A a b x y).mp h
  · rcases (edge_adj _ _ _ _).mp h with ⟨⟨_,rfl⟩|⟨rfl,_⟩,_⟩
    · exact Or.inr hr
    · exact Or.inl hr
  · rcases (edge_adj _ _ _ _).mp h with ⟨⟨rfl,_⟩|⟨_,rfl⟩,_⟩
    · exact Or.inl hr
    · exact Or.inr hr

lemma spokes_avoid (A : Finset V) (a b : V → V) {r : V} (hr : r ∉ A)
    (ha : ∀ s ∈ A, a s ≠ r) (hb : ∀ s ∈ A, b s ≠ r) : r ∉ (spokes A a b).support := by
  rintro ⟨x,hx⟩
  obtain ⟨s,hs,h|h⟩ := (spokes_adj A a b r x).mp hx
  · rcases (edge_adj _ _ _ _).mp h with ⟨⟨he,_⟩|⟨he,_⟩,_⟩
    · exact ha s hs he.symm
    · exact hr (he.symm ▸ hs)
  · rcases (edge_adj _ _ _ _).mp h with ⟨⟨he,_⟩|⟨he,_⟩,_⟩
    · exact hr (he.symm ▸ hs)
    · exact hb s hs he.symm

lemma expand_spokes [Fintype V] (A : Finset V) (a b : V → V) (H : SimpleGraph V)
    (ha : ∀ r ∈ A, a r ∉ A) (hb : ∀ r ∈ A, b r ∉ A)
    (hab : ∀ r ∈ A, a r ≠ b r)
    (hH : ∀ r ∈ A, r ∉ H.support)
    (hfresh : ∀ r ∈ A, ¬H.Adj (a r) (b r))
    (hinj : ∀ r ∈ A, ∀ s ∈ A, s(a r,b r)=s(a s,b s) → r=s)
    (D : Finset (H ⊔ chords A a b).Subgraph) (hD : GoodDecomposition (H ⊔ chords A a b) D) :
    ∃ E : Finset (H ⊔ spokes A a b).Subgraph,
      GoodDecomposition (H ⊔ spokes A a b) E ∧ E.card ≤ D.card := by
  induction A using Finset.induction_on generalizing H with
  | empty => simpa only [chords,spokes,Finset.sup_empty,sup_bot_eq] using ⟨D,hD,le_refl D.card⟩
  | @insert r A hr ih =>
    have hrA : r ∈ insert r A := Finset.mem_insert_self r A
    have haA (s) (hs : s ∈ A) : a s ∉ A := fun hh ↦ ha s (Finset.mem_insert_of_mem hs) (Finset.mem_insert_of_mem hh)
    have hbA (s) (hs : s ∈ A) : b s ∉ A := fun hh ↦ hb s (Finset.mem_insert_of_mem hs) (Finset.mem_insert_of_mem hh)
    have har : a r ≠ r := fun he ↦ ha r hrA (he.symm ▸ hrA)
    have hbr : b r ≠ r := fun he ↦ hb r hrA (he.symm ▸ hrA)
    have han (s) (hs : s ∈ A) : a s ≠ r := fun he ↦ ha s (Finset.mem_insert_of_mem hs) (he.symm ▸ hrA)
    have hbn (s) (hs : s ∈ A) : b s ≠ r := fun he ↦ hb s (Finset.mem_insert_of_mem hs) (he.symm ▸ hrA)
    let H0 := H ⊔ edge (a r) (b r)
    have hH0 (s) (hs : s ∈ A) : s ∉ H0.support := by
      rintro ⟨x,hx|hx⟩
      · exact hH s (Finset.mem_insert_of_mem hs) ⟨x,hx⟩
      · rcases (edge_adj _ _ _ _).mp hx with ⟨⟨he,_⟩|⟨he,_⟩,_⟩
        · exact ha r hrA (he ▸ Finset.mem_insert_of_mem hs)
        · exact hb r hrA (he ▸ Finset.mem_insert_of_mem hs)
    have hf0 (s) (hs : s ∈ A) : ¬H0.Adj (a s) (b s) := by
      rintro (hh|hh)
      · exact hfresh s (Finset.mem_insert_of_mem hs) hh
      · have he : s(a s,b s)=s(a r,b r) := by
          rcases (edge_adj _ _ _ _).mp hh with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
          · simp only [h1,h2]
          · simp only [h1,h2,Sym2.eq_swap]
        exact hr ((hinj s (Finset.mem_insert_of_mem hs) r hrA he) ▸ hs)
    have hex : ∃ D0 : Finset (H0 ⊔ chords A a b).Subgraph,
        GoodDecomposition (H0 ⊔ chords A a b) D0 ∧ D0.card ≤ D.card := by
      have he : H ⊔ chords (insert r A) a b=H0 ⊔ chords A a b := by
        rw [chords_insert]; exact (sup_assoc _ _ _).symm
      exact Eq.mp (congrArg (fun J : SimpleGraph V ↦ ∃ E : Finset J.Subgraph,
        GoodDecomposition J E ∧ E.card ≤ D.card) he) ⟨D,hD,le_refl _⟩
    obtain ⟨D0,hD0,hD0c⟩ := hex
    obtain ⟨E,hE,hEc⟩ := ih H0 haA hbA
      (fun s hs ↦ hab s (Finset.mem_insert_of_mem hs)) hH0 hf0
      (fun s hs t ht ↦ hinj s (Finset.mem_insert_of_mem hs) t (Finset.mem_insert_of_mem ht)) D0 hD0
    let J := H0 ⊔ spokes A a b
    let K := H ⊔ spokes (insert r A) a b
    have hKn : (edge (a r) r ⊔ edge r (b r)) ≤ K := by
      rw [show K=H ⊔ ((edge (a r) r ⊔ edge r (b r)) ⊔ spokes A a b) by dsimp only [K]; rw [spokes_insert]]
      exact le_sup_of_le_right le_sup_left
    have h1 : K.Adj (a r) r := hKn (Or.inl ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,har⟩))
    have h2 : K.Adj r (b r) := hKn (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hbr.symm⟩))
    let P : K.Walk (a r) (b r) := .cons h1 (.cons h2 .nil)
    have hp : P.IsPath := by simp [P,Walk.cons_isPath_iff,har,hbr.symm,hab r hrA]
    have hrJ : r ∉ J.support := by
      rintro ⟨x,(hx|hx)|hx⟩
      · exact hH r hrA ⟨x,hx⟩
      · rcases (edge_adj _ _ _ _).mp hx with ⟨⟨he,_⟩|⟨he,_⟩,_⟩
        · exact har he.symm
        · exact hbr he.symm
      · exact spokes_avoid A a b hr han hbn ⟨x,hx⟩
    have hpfr : ∀ x ∈ P.support, x ≠ a r → x ≠ b r → x ∉ J.support := by
      intro x hx hxa hxb
      have hx : x=r := by simpa [P,Walk.support,hxa,hxb] using hx
      exact hx ▸ hrJ
    have hbase : ¬(H ⊔ spokes A a b).Adj (a r) (b r) := by
      rintro (hh|hh)
      · exact hfresh r hrA hh
      · rcases spokes_endpoint A a b hh with hh|hh
        · exact ha r hrA (Finset.mem_insert_of_mem hh)
        · exact hb r hrA (Finset.mem_insert_of_mem hh)
    have hJ : J=(H ⊔ spokes A a b) ⊔ edge (a r) (b r) := by
      dsimp [J,H0]; ac_rfl
    have hK : K=(H ⊔ spokes A a b) ⊔ (edge (a r) r ⊔ edge r (b r)) := by
      dsimp only [K]; rw [spokes_insert]; ac_rfl
    have hPe : P.toSubgraph.edgeSet=(edge (a r) r ⊔ edge r (b r)).edgeSet := by
      rw [edgeSet_sup,edge_edgeSet_of_ne har,edge_edgeSet_of_ne hbr.symm]
      ext e; simp [P]
    have hcover : K.edgeSet=(J.edgeSet \ {s(a r,b r)}) ∪ P.toSubgraph.edgeSet := by
      rw [hJ,edgeSet_sup_edge_diff _ (hab r hrA) hbase,hPe,hK,edgeSet_sup]
    have heJ : J.Adj (a r) (b r) := Or.inl (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab r hrA⟩))
    obtain ⟨F,hF,hFc⟩ := hE.expand_edge heJ P hp hpfr hcover
    exact ⟨F,hF,hFc.trans (hEc.trans hD0c)⟩

lemma chords_support_outside (A : Finset V) (a b : V → V) (S : Set V)
    (ha : ∀ r ∈ A, a r ∉ S) (hb : ∀ r ∈ A, b r ∉ S) :
    (chords A a b).support ⊆ Sᶜ := by
  rintro x ⟨y,hxy⟩
  obtain ⟨r,hr,hxy⟩ := (adj_finset_sup A (fun r ↦ edge (a r) (b r)) x y).mp hxy
  rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨he,_⟩|⟨he,_⟩,_⟩
  · exact he ▸ ha r hr
  · exact he ▸ hb r hr

lemma compressed_support_connected (A : Finset V) (a b : V → V) (H : SimpleGraph V)
    (ha : ∀ r ∈ A, a r ∉ A) (hb : ∀ r ∈ A, b r ∉ A)
    (hab : ∀ r ∈ A, a r ≠ b r) (hH : ∀ r ∈ A, r ∉ H.support)
    (hc : SupportConnected (H ⊔ spokes A a b)) : SupportConnected (H ⊔ chords A a b) := by
  let F := H ⊔ spokes A a b
  let J := H ⊔ chords A a b
  let f : V → V := fun x ↦ if x ∈ A then a x else x
  have har (r) (hr : r ∈ A) : a r ≠ r := fun he ↦ ha r hr (he.symm ▸ hr)
  have hbr (r) (hr : r ∈ A) : b r ≠ r := fun he ↦ hb r hr (he.symm ▸ hr)
  have hed (r) (hr : r ∈ A) : J.Adj (a r) (b r) := by
    apply Or.inr
    apply (adj_finset_sup A (fun r ↦ edge (a r) (b r)) _ _).mpr
    exact ⟨r,hr,(edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab r hr⟩⟩
  have hfa (r) (hr : r ∈ A) : f (a r)=a r := if_neg (ha r hr)
  have hfb (r) (hr : r ∈ A) : f (b r)=b r := if_neg (hb r hr)
  have hfr (r) (hr : r ∈ A) : f r=a r := if_pos hr
  have hf (x y : V) (hxy : F.Adj x y) : J.Reachable (f x) (f y) := by
    rcases hxy with hxy|hxy
    · have hx : x ∉ A := fun hh ↦ hH x hh ⟨y,hxy⟩
      have hy : y ∉ A := fun hh ↦ hH y hh ⟨x,hxy.symm⟩
      simp only [f,if_neg hx,if_neg hy]
      exact (show J.Adj x y from Or.inl hxy).reachable
    · obtain ⟨r,hr,h|h⟩ := (spokes_adj A a b x y).mp hxy
      · rcases (edge_adj _ _ _ _).mp h with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
        · rw [h1,h2,hfa r hr,hfr r hr]
        · rw [h1,h2,hfa r hr,hfr r hr]
      · rcases (edge_adj _ _ _ _).mp h with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
        · rw [h1,h2,hfr r hr,hfb r hr]; exact (hed r hr).reachable
        · rw [h1,h2,hfr r hr,hfb r hr]; exact (hed r hr).reachable.symm
  have hout : J.support ⊆ (A : Set V)ᶜ := by
    rintro x ⟨y,hxy|hxy⟩
    · exact fun hx ↦ hH x hx ⟨y,hxy⟩
    · exact chords_support_outside A a b (A : Set V) ha hb ⟨y,hxy⟩
  have hsub : J.support ⊆ F.support := by
    rintro x ⟨y,hxy|hxy⟩
    · exact ⟨y,Or.inl hxy⟩
    · obtain ⟨r,hr,hxy⟩ := (adj_finset_sup A (fun r ↦ edge (a r) (b r)) x y).mp hxy
      have h1 : F.Adj (a r) r := Or.inr ((spokes_adj A a b _ _).mpr
        ⟨r,hr,Or.inl ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,har r hr⟩)⟩)
      have h2 : F.Adj (b r) r := Or.inr ((spokes_adj A a b _ _).mpr
        ⟨r,hr,Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl,rfl⟩,hbr r hr⟩)⟩)
      rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨rfl,_⟩|⟨rfl,_⟩,_⟩
      · exact ⟨r,h1⟩
      · exact ⟨r,h2⟩
  intro x hx y hy
  have hh := reachable_map_to_reachable f hf (hc x (hsub hx) y (hsub hy))
  have hxA : x ∉ A := hout hx
  have hyA : y ∉ A := hout hy
  simpa only [f,if_neg hxA,if_neg hyA] using hh

lemma compressed_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    [Fintype V] (A : Finset V) (a b : V → V) (H : SimpleGraph V) (S : Set V)
    (hAS : (A : Set V) ⊆ S) (hHS : H.support ⊆ Sᶜ)
    (ha : ∀ r ∈ A, a r ∉ S) (hb : ∀ r ∈ A, b r ∉ S)
    (hab : ∀ r ∈ A, a r ≠ b r)
    (hfresh : ∀ r ∈ A, ¬H.Adj (a r) (b r))
    (hinj : ∀ r ∈ A, ∀ s ∈ A, s(a r,b r)=s(a s,b s) → r=s)
    (hc : SupportConnected (H ⊔ spokes A a b)) (hsize : Sᶜ.ncard < n) :
    ∃ E : Finset (H ⊔ spokes A a b).Subgraph,
      GoodDecomposition (H ⊔ spokes A a b) E ∧ E.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ := by
  have haA (r) (hr : r ∈ A) : a r ∉ A := fun hh ↦ ha r hr (hAS hh)
  have hbA (r) (hr : r ∈ A) : b r ∉ A := fun hh ↦ hb r hr (hAS hh)
  have hH (r) (hr : r ∈ A) : r ∉ H.support := fun hh ↦ hHS hh (hAS hr)
  have hJ : (H ⊔ chords A a b).support ⊆ Sᶜ := by
    rintro x ⟨y,hxy|hxy⟩
    · exact hHS ⟨y,hxy⟩
    · exact chords_support_outside A a b S ha hb ⟨y,hxy⟩
  have hcard := Set.ncard_le_ncard hJ
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall (H ⊔ chords A a b)
    (compressed_support_connected A a b H haA hbA hab hH hc) (by omega)
  obtain ⟨E,hE,hEc⟩ := expand_spokes A a b H haA hbA hab hH hfresh hinj D hD
  refine ⟨E,hE,?_⟩
  rw [ceil_half] at hDc ⊢
  omega

end IndependentSuppression

/- Short-cycle closure and fresh shortcut edges at a shortest whole-cycle defect. -/
namespace CycleNeighborClosure
open SimpleGraph _root_.Erdos583Work _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.CycleEar
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {a : V}

lemma cycle_neighbor_pair [Fintype V] (C : G.Walk a a) (hC : C.IsCycle) {r u v : V}
    (hru : C.toSubgraph.Adj r u) (hrv : C.toSubgraph.Adj r v) (huv : u ≠ v) :
    C.toSubgraph.neighborSet r={u,v} := by
  have hn := hC.ncard_neighborSet_toSubgraph_eq_two (Walk.mem_support_of_adj_toSubgraph hru)
  apply (Set.eq_of_subset_of_ncard_le (show ({u,v} : Set V) ⊆ C.toSubgraph.neighborSet r from
    by intro x hx; rcases hx with rfl|rfl <;> assumption) ?_).symm
  rw [hn,Set.ncard_pair huv]

lemma cycle_support_of_closed (C : G.Walk a a) (S : Set V)
    {r : V} (hr : r ∈ C.support) (hrS : r ∈ S)
    (hclosed : ∀ x ∈ S, ∀ y, C.toSubgraph.Adj x y → y ∈ S) : C.toSubgraph.verts ⊆ S := by
  have step {x y : C.toSubgraph.verts} (P : C.toSubgraph.coe.Walk x y) : x.val ∈ S → y.val ∈ S := by
    induction P with
    | nil => exact id
    | @cons x y z h P ih => exact fun hx ↦ ih (hclosed x.val hx y.val h)
  intro x hx
  obtain ⟨P⟩ := C.toSubgraph_connected ⟨r,C.mem_verts_toSubgraph.mpr hr⟩ ⟨x,hx⟩
  exact step P hrS

lemma cycle_length_le_three_of_triangle [Fintype V] (C : G.Walk a a) (hC : C.IsCycle)
    {r u v : V} (hru : C.toSubgraph.Adj r u) (huv : C.toSubgraph.Adj u v)
    (hvr : C.toSubgraph.Adj v r) : C.length ≤ 3 := by
  have hN₁ := cycle_neighbor_pair C hC hru hvr.symm huv.ne
  have hN₂ := cycle_neighbor_pair C hC hru.symm huv hvr.ne.symm
  have hN₃ := cycle_neighbor_pair C hC hvr huv.symm hru.ne
  have hsub : C.toSubgraph.verts ⊆ ({r,u,v} : Set V) := by
    apply cycle_support_of_closed C _ (Walk.mem_support_of_adj_toSubgraph hru) (Or.inl rfl)
    intro x hx y hy
    rcases hx with hx|hx|hx
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet r at hy
      rw [hN₁] at hy
      exact Or.inr hy
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet u at hy
      rw [hN₂] at hy
      rcases hy with hy|hy
      · exact Or.inl hy
      · exact Or.inr (Or.inr hy)
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet v at hy
      rw [hN₃] at hy
      rcases hy with hy|hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
  have hb := Set.ncard_le_ncard hsub
  have hv : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  have hs := Set.ncard_insert_le r ({u,v} : Set V)
  have ht := Set.ncard_pair huv.ne
  omega

lemma cycle_length_le_four_of_common_neighbors [Fintype V] (C : G.Walk a a) (hC : C.IsCycle)
    {r s u v : V} (hrs : r ≠ s) (huv : u ≠ v)
    (hru : C.toSubgraph.Adj r u) (hrv : C.toSubgraph.Adj r v)
    (hsu : C.toSubgraph.Adj s u) (hsv : C.toSubgraph.Adj s v) : C.length ≤ 4 := by
  have hN₁ := cycle_neighbor_pair C hC hru hrv huv
  have hN₂ := cycle_neighbor_pair C hC hsu hsv huv
  have hN₃ := cycle_neighbor_pair C hC hru.symm hsu.symm hrs
  have hN₄ := cycle_neighbor_pair C hC hrv.symm hsv.symm hrs
  have hsub : C.toSubgraph.verts ⊆ ({r,s,u,v} : Set V) := by
    apply cycle_support_of_closed C _ (Walk.mem_support_of_adj_toSubgraph hru) (Or.inl rfl)
    intro x hx y hy
    rcases hx with hx|hx|hx|hx
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet r at hy
      rw [hN₁] at hy
      exact Or.inr (Or.inr hy)
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet s at hy
      rw [hN₂] at hy
      exact Or.inr (Or.inr hy)
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet u at hy
      rw [hN₃] at hy
      rcases hy with hy|hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
    · rw [hx] at hy
      change y ∈ C.toSubgraph.neighborSet v at hy
      rw [hN₄] at hy
      rcases hy with hy|hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
  have hb := Set.ncard_le_ncard hsub
  have hv : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  have hs₁ := Set.ncard_insert_le r ({s,u,v} : Set V)
  have hs₂ := Set.ncard_insert_le s ({u,v} : Set V)
  have hs₃ := Set.ncard_pair huv
  omega

lemma shortest_cycle_avoider_no_chord [Fintype V] {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hmin : ShortestCycle T C.length)
    {r u v : V} (hru : C.toSubgraph.Adj r u) (hrv : C.toSubgraph.Adj r v) (huv : u ≠ v)
    (hrP : r ∉ (T.walk j).support) : s(u,v) ∉ (T.walk j).edges := by
  intro he
  have hrC := Walk.mem_support_of_adj_toSubgraph hru
  let D := C.rotate hrC
  have hD : D.IsCycle := hC.rotate hrC
  have hDi : (T.walk i).toSubgraph=D.toSubgraph := hi.trans (C.toSubgraph_rotate hrC).symm
  have hDl : D.length=C.length := by
    have hh := congrArg Walk.length (C.take_spec hrC)
    simpa only [D,Walk.rotate,Walk.length_append,Nat.add_comm] using hh
  obtain ⟨x,y,hrx,hyr,R,hform⟩ := cycle_two_spokes D hD
  have hCf : (Walk.cons hrx (R.concat hyr)).IsCycle := hform ▸ hD
  have hif : (T.walk i).toSubgraph=(Walk.cons hrx (R.concat hyr)).toSubgraph := by rw [←hform]; exact hDi
  have hxC : C.toSubgraph.Adj r x := by
    rw [←C.toSubgraph_rotate hrC]
    change D.toSubgraph.Adj r x
    rw [hform]
    change s(r,x) ∈ (Walk.cons hrx (R.concat hyr)).toSubgraph.edgeSet
    rw [Walk.mem_edges_toSubgraph]
    simp
  have hyC : C.toSubgraph.Adj r y := by
    apply Subgraph.Adj.symm
    rw [←C.toSubgraph_rotate hrC]
    change D.toSubgraph.Adj y r
    rw [hform]
    change s(y,r) ∈ (Walk.cons hrx (R.concat hyr)).toSubgraph.edgeSet
    rw [Walk.mem_edges_toSubgraph]
    simp [Walk.concat_eq_append]
  have hRp : R.IsPath := ((Walk.cons_isCycle_iff _ _).mp hCf).1.of_append_left
  have hxy : x ≠ y := by
    intro heq
    subst y
    have hnil := (Walk.isPath_iff_eq_nil R).mp hRp
    have hl := hCf.three_le_length
    simp only [hnil,Walk.length_cons,Walk.length_concat,Walk.length_nil] at hl
    omega
  have hN := cycle_neighbor_pair C hC hru hrv huv
  have hx : x ∈ ({u,v} : Set V) := hN ▸ hxC
  have hy : y ∈ ({u,v} : Set V) := hN ▸ hyC
  have hpair : s(x,y)=s(u,v) := by
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · exact (hxy rfl).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (hxy rfl).elim
  have hedge : s(x,y) ∈ (T.walk j).edges := hpair.symm ▸ he
  have hxyG : G.Adj x y := (T.walk j).edges_subset_edgeSet hedge
  obtain ⟨U,E,hUs,hE,hUi,hlen⟩ := shorten_cycle_member T hs i j hij hrx hyr R hCf hif hxyG hedge hrP
  have hbound := hmin U hUs i x E hE hUi
  rw [←hform,hDl] at hlen
  omega

end CycleNeighborClosure

/- Removing a normal component leaves the distinguished member connected to every remaining member. -/
namespace NormalComponentComplement
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.MemberExpansion _root_.Erdos583Work.MemberComponents
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma outside_member_avoids (T : TrailFamily G k) (i : Fin k)
    (A : (normalGraph T i).ConnectedComponent) {j : Fin k}
    (hji : j ≠ i) (hjA : j ∉ componentMembers T i A) :
    Disjoint (T.walk j).toSubgraph.verts (selectedGraph T (componentMembers T i A)).support := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨y,l,hl,hxy⟩
  obtain ⟨hli,hlA⟩ := (mem_componentMembers T i l A).mp hl
  have he := same_component_of_intersection T i hji hli
    ((T.walk j).mem_verts_toSubgraph.mp hx) (Walk.mem_support_of_adj_toSubgraph hxy)
  exact hjA ((mem_componentMembers T i j A).mpr ⟨hji,he.trans hlA⟩)

lemma complement_adj_at (T : TrailFamily G k) (i : Fin k)
    (A : (normalGraph T i).ConnectedComponent) {x y : V}
    (hx : x ∈ (selectedGraph T (componentMembers T i A)).support) :
    (selectedGraph T (Finset.univ \ componentMembers T i A)).Adj x y ↔ (T.walk i).toSubgraph.Adj x y := by
  constructor
  · rintro ⟨j,hj,hxy⟩
    have hji : j=i := by
      by_contra hh
      exact Set.disjoint_left.mp (outside_member_avoids T i A hh (Finset.mem_sdiff.mp hj).2)
        ((T.walk j).toSubgraph.edge_vert hxy) hx
    subst j
    exact hxy
  · intro hxy
    exact ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,removed_not_mem T i A⟩,hxy⟩

lemma component_members_disjoint (T : TrailFamily G k) (i : Fin k)
    {A B : (normalGraph T i).ConnectedComponent} (hAB : A ≠ B) :
    Disjoint (componentMembers T i A) (componentMembers T i B) := by
  apply Finset.disjoint_left.mpr
  intro j hjA hjB
  obtain ⟨hji,hjA⟩ := (mem_componentMembers T i j A).mp hjA
  obtain ⟨_,hjB⟩ := (mem_componentMembers T i j B).mp hjB
  exact hAB (hjA.symm.trans hjB)

lemma complement_connected (T : TrailFamily G k) (hG : G.Connected) (i : Fin k)
    (hn : ∀ j, ¬(T.walk j).Nil) (A : (normalGraph T i).ConnectedComponent) :
    SupportConnected (selectedGraph T (Finset.univ \ componentMembers T i A)) := by
  let B := Finset.univ \ componentMembers T i A
  let F := selectedGraph T B
  have hiB : i ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,removed_not_mem T i A⟩
  have link (x : V) (hx : x ∈ F.support) : F.Reachable x (T.start i) := by
    obtain ⟨y,j,hj,hxy⟩ := hx
    by_cases hji : j=i
    · subst j
      exact selected_reachable T B i hiB (Walk.mem_support_of_adj_toSubgraph hxy) (T.walk i).start_mem_support
    · let C := (normalGraph T i).connectedComponentMk ⟨j,hji⟩
      have hjC : j ∈ componentMembers T i C := (mem_componentMembers T i j C).mpr ⟨hji,rfl⟩
      have hCA : C ≠ A := by
        rintro rfl
        exact (Finset.mem_sdiff.mp hj).2 hjC
      have hCB : componentMembers T i C ⊆ B := by
        intro l hl
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hlA ↦
          Finset.disjoint_left.mp (component_members_disjoint T i hCA) hl hlA⟩
      have hle : selectedGraph T (componentMembers T i C) ≤ F := CycleGroupDisjoint.selectedGraph_mono T hCB
      obtain ⟨z,hzi,hzC⟩ := component_meets_removed T hG i hn C
      have hxC : x ∈ (selectedGraph T (componentMembers T i C)).support := ⟨y,j,hjC,hxy⟩
      exact ((component_support_connected T i C x hxC z hzC).mono hle).trans
        (selected_reachable T B i hiB ((T.walk i).mem_verts_toSubgraph.mp hzi) (T.walk i).start_mem_support)
  intro x hx y hy
  exact (link x hx).trans (link y hy).symm

end NormalComponentComplement

/- Suppressing independent cycle visits repairs a zero-surplus normal component. -/
namespace ZeroComponentSuppression
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.MemberExpansion _root_.Erdos583Work.MemberNormalExpansion
open _root_.Erdos583Work.MemberComponents _root_.Erdos583Work.CycleEar _root_.Erdos583Work.BridgeGlue
open _root_.Erdos583Work.IndependentSuppression _root_.Erdos583Work.CycleNeighborClosure
open _root_.Erdos583Work.NormalComponentComplement
open scoped Classical
set_option maxHeartbeats 3000000

lemma independent_component_shortcuts {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k) (i : Fin k)
    {v : V} (C : G.Walk v v) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmin : ShortestCycle T C.length) (hlen : 4 < C.length)
    (A : (normalGraph T i).ConnectedComponent)
    (hInd : ∀ x ∈ (selectedGraph T (componentMembers T i A)).support,
      ∀ y ∈ (selectedGraph T (componentMembers T i A)).support, ¬C.toSubgraph.Adj x y) :
    let S := (selectedGraph T (componentMembers T i A)).support
    let F := selectedGraph T (Finset.univ \ componentMembers T i A)
    let H := within F Sᶜ
    ∃ R : Finset V, ∃ a b : V → V,
      (R : Set V) ⊆ S ∧
      (∀ r ∈ R, a r ∉ S) ∧ (∀ r ∈ R, b r ∉ S) ∧
      (∀ r ∈ R, a r ≠ b r) ∧ (∀ r ∈ R, ¬H.Adj (a r) (b r)) ∧
      (∀ r ∈ R, ∀ s ∈ R, s(a r,b r)=s(a s,b s) → r=s) ∧ F=H ⊔ spokes R a b := by
  let S := (selectedGraph T (componentMembers T i A)).support
  let F := selectedGraph T (Finset.univ \ componentMembers T i A)
  let H := within F Sᶜ
  let R := (C.toSubgraph.verts ∩ S).toFinset
  have hR (r : V) : r ∈ R ↔ r ∈ C.toSubgraph.verts ∧ r ∈ S := by simp only [R,Set.mem_toFinset,Set.mem_inter_iff]
  have hchoose (r : V) : ∃ a b, r ∈ R → a ≠ b ∧ C.toSubgraph.neighborSet r={a,b} := by
    by_cases hr : r ∈ R
    · obtain ⟨a,b,hab,hN⟩ := Set.ncard_eq_two.mp
        (hC.ncard_neighborSet_toSubgraph_eq_two (C.mem_verts_toSubgraph.mp ((hR r).mp hr).1))
      exact ⟨a,b,fun _ ↦ ⟨hab,hN⟩⟩
    · exact ⟨r,r,fun hh ↦ (hr hh).elim⟩
  choose a b hN using hchoose
  have hna (r : V) (hr : r ∈ R) : C.toSubgraph.Adj r (a r) := by
    change a r ∈ C.toSubgraph.neighborSet r
    rw [(hN r hr).2]
    exact Or.inl rfl
  have hnb (r : V) (hr : r ∈ R) : C.toSubgraph.Adj r (b r) := by
    change b r ∈ C.toSubgraph.neighborSet r
    rw [(hN r hr).2]
    exact Or.inr rfl
  have hAS : (R : Set V) ⊆ S := fun r hr ↦ ((hR r).mp hr).2
  have ha (r : V) (hr : r ∈ R) : a r ∉ S := fun hh ↦ hInd r (hAS hr) (a r) hh (hna r hr)
  have hb (r : V) (hr : r ∈ R) : b r ∉ S := fun hh ↦ hInd r (hAS hr) (b r) hh (hnb r hr)
  have hF (x : V) (hx : x ∈ S) (y : V) : F.Adj x y ↔ C.toSubgraph.Adj x y := by
    rw [complement_adj_at T i A hx,hi]
  have hfresh (r : V) (hr : r ∈ R) : ¬H.Adj (a r) (b r) := by
    intro hh
    obtain ⟨j,hj,hxy⟩ := hh.1
    have hji : j ≠ i := by
      intro he
      have hxyC : C.toSubgraph.Adj (a r) (b r) := by
        subst j
        exact hi ▸ hxy
      have hl := cycle_length_le_three_of_triangle C hC (hna r hr) hxyC (hnb r hr).symm
      omega
    have hrP : r ∉ (T.walk j).support := by
      intro hp
      exact Set.disjoint_left.mp (outside_member_avoids T i A hji (Finset.mem_sdiff.mp hj).2)
        ((T.walk j).mem_verts_toSubgraph.mpr hp) (hAS hr)
    exact shortest_cycle_avoider_no_chord T hs i j hji.symm C hC hi hmin (hna r hr) (hnb r hr)
      (hN r hr).1 hrP ((T.walk j).mem_edges_toSubgraph.mp hxy)
  have hinj (r : V) (hr : r ∈ R) (s : V) (hsR : s ∈ R)
      (he : s(a r,b r)=s(a s,b s)) : r=s := by
    by_contra hrs
    have hsa : C.toSubgraph.Adj s (a r) := by
      rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
      · rw [h1]; exact hna s hsR
      · rw [h1]; exact hnb s hsR
    have hsb : C.toSubgraph.Adj s (b r) := by
      rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
      · rw [h2]; exact hnb s hsR
      · rw [h2]; exact hna s hsR
    have hl := cycle_length_le_four_of_common_neighbors C hC hrs (hN r hr).1
      (hna r hr) (hnb r hr) hsa hsb
    omega
  have hform : F=H ⊔ spokes R a b := by
    ext x y
    constructor
    · intro hxy
      by_cases hx : x ∈ S
      · have hxC := (hF x hx y).mp hxy
        have hxR : x ∈ R := (hR x).mpr ⟨C.toSubgraph.edge_vert hxC,hx⟩
        have hy : y ∈ ({a x,b x} : Set V) := (hN x hxR).2 ▸ hxC
        apply Or.inr
        apply (spokes_adj R a b x y).mpr
        refine ⟨x,hxR,?_⟩
        rcases hy with hy|hy
        · exact Or.inl ((edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl,hy⟩,hxy.ne⟩)
        · exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,hy⟩,hxy.ne⟩)
      · by_cases hy : y ∈ S
        · have hyC := (hF y hy x).mp hxy.symm
          have hyR : y ∈ R := (hR y).mpr ⟨C.toSubgraph.edge_vert hyC,hy⟩
          have hx' : x ∈ ({a y,b y} : Set V) := (hN y hyR).2 ▸ hyC
          apply Or.inr
          apply (spokes_adj R a b x y).mpr
          refine ⟨y,hyR,?_⟩
          rcases hx' with hx'|hx'
          · exact Or.inl ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨hx',rfl⟩,hxy.ne⟩)
          · exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inr ⟨hx',rfl⟩,hxy.ne⟩)
        · exact Or.inl ⟨hxy,hx,hy⟩
    · rintro (hxy|hxy)
      · exact hxy.1
      · obtain ⟨r,hr,hxy|hxy⟩ := (spokes_adj R a b x y).mp hxy
        · have hh := ((hF r (hAS hr) (a r)).mpr (hna r hr)).symm
          rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
          · rw [h1,h2]; exact hh
          · rw [h1,h2]; exact hh.symm
        · have hh := (hF r (hAS hr) (b r)).mpr (hnb r hr)
          rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
          · rw [h1,h2]; exact hh
          · rw [h1,h2]; exact hh.symm
  exact ⟨R,a,b,hAS,ha,hb,fun r hr ↦ (hN r hr).1,hfresh,hinj,hform⟩

section Smallest
open VertexCritical CyclePrefixRepair CycleComponentBudget
variable {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {v : Fin n} (C : G.Walk v v) (hC : C.IsCycle)
  (hi : (T.walk i).toSubgraph=C.toSubgraph) (hmin : ShortestCycle T C.length)
include hsmall hG hfail hs hC hi hmin

lemma shortest_component_positive (A : (normalGraph T i).ConnectedComponent) :
    0 < componentSurplus T i A := by
  let B := componentMembers T i A
  let S := (selectedGraph T B).support
  let F := selectedGraph T (Finset.univ \ B)
  let H := within F Sᶜ
  by_contra hzero
  have hsize : S.ncard ≤ 2*B.card := Nat.sub_eq_zero_iff_le.mp (Nat.eq_zero_of_not_pos hzero)
  have hnp := cycle_member_not_path T i C hC hi
  have hm := maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,hnp⟩
  have hS : S.ncard=2*B.card := le_antisymm hsize (cycle_component_expands hsmall hG hfail T hs hm i C hC hi A)
  have horder : S.ncard < n := FreeTailAbsorption.small_normal_group_proper T i B (removed_not_mem T i A) hsize
  have hInd : ∀ x ∈ S, ∀ y ∈ S, ¬C.toSubgraph.Adj x y := by
    intro x hx y hy
    exact CycleEdgeAbsorption.small_group_cycle_independent hsmall hfail T hs i C hC hi B
      (removed_not_mem T i A) (component_support_connected T i A) horder hsize hx hy
  have hlen := HeptagonExclusion.whole_cycle_length_ge_eight hsmall hG hfail T hs hm i C hC hi
  obtain ⟨R,a,b,hAS,ha,hb,hab,hfresh,hinj,hform⟩ :=
    independent_component_shortcuts T hs i C hC hi hmin (by omega) A hInd
  have hSn : S.Nonempty := by
    obtain ⟨x,_,hx⟩ := component_meets_removed T hG i hn A
    exact ⟨x,hx⟩
  have hSum : S.ncard+Sᶜ.ncard=n := by simpa only [Nat.card_fin] using S.ncard_add_ncard_compl
  have hSp : 0 < S.ncard := hSn.ncard_pos
  have hFc := complement_connected T hG i hn A
  have hHS : H.support ⊆ Sᶜ := within_support F Sᶜ
  have hex : ∃ D : Finset F.Subgraph, GoodDecomposition F D ∧ D.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ := by
    obtain ⟨D,hD,hDc⟩ := compressed_partition hsmall R a b H S hAS hHS ha hb hab hfresh hinj
      (hform ▸ hFc) (by omega)
    exact Eq.mp (congrArg (fun J : SimpleGraph (Fin n) ↦ ∃ E : Finset J.Subgraph,
      GoodDecomposition J E ∧ E.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊) hform.symm) ⟨D,hD,hDc⟩
  obtain ⟨D,hD,hDc⟩ := hex
  have hp (j) (hj : j ∉ Finset.univ \ B) : (T.walk j).IsPath := by
    have hjB : j ∈ B := by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hj
    exact (T.one_defect_other_paths hs i hnp).2 j ((mem_componentMembers T i j A).mp hjB).1
  obtain ⟨E,hE,hEc⟩ := replace_selected T (Finset.univ \ B) hp D hD
  have hcard : (Finset.univ \ B).card=⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp only [Finset.card_univ,Fintype.card_fin]
  have hBc : B.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ B
  apply hfail
  refine ⟨E,hE,?_⟩
  rw [hcard] at hEc
  simp only [ceil_half,Fintype.card_fin] at hDc hEc hBc ⊢
  omega

lemma shortest_component_count_le_surplus :
    Nat.card (normalGraph T i).ConnectedComponent ≤ ∑ A, componentSurplus T i A := by
  rw [Nat.card_eq_fintype_card,←Finset.card_univ]
  calc
    _ = ∑ _A : (normalGraph T i).ConnectedComponent, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun A _ ↦ shortest_component_positive hsmall hG hfail T hs i C hC hi hmin A)

lemma shortest_component_count_le_two : Nat.card (normalGraph T i).ConnectedComponent ≤ 2 := by
  have hm := maximum_of_one_defect_failure hfail T hs
  exact (shortest_component_count_le_surplus hsmall hG hfail T hs i C hC hi hmin).trans
    (cycle_surplus_le_two hsmall hG hfail T hs hm i C hC hi)

lemma odd_shortest_component_count_le_one (ho : Odd n) : Nat.card (normalGraph T i).ConnectedComponent ≤ 1 := by
  have hm := maximum_of_one_defect_failure hfail T hs
  exact (shortest_component_count_le_surplus hsmall hG hfail T hs i C hC hi hmin).trans
    (odd_cycle_surplus_le_one hsmall hG hfail T hs hm i C hC hi ho)

lemma odd_shortest_normal_connected (ho : Odd n) :
    SupportConnected (selectedGraph T (Finset.univ.erase i)) := by
  haveI : Subsingleton (normalGraph T i).ConnectedComponent :=
    (Fintype.card_le_one_iff_subsingleton).mp (by simpa only [Nat.card_eq_fintype_card] using odd_shortest_component_count_le_one hsmall hG hfail T hs i C hC hi hmin ho)
  intro x hx y hy
  obtain ⟨u,j,hj,hxj⟩ := hx
  obtain ⟨w,l,hl,hyl⟩ := hy
  let A := (normalGraph T i).connectedComponentMk ⟨j,(Finset.mem_erase.mp hj).1⟩
  have hjA : j ∈ componentMembers T i A := (mem_componentMembers T i j A).mpr ⟨(Finset.mem_erase.mp hj).1,rfl⟩
  have hlA : l ∈ componentMembers T i A := (mem_componentMembers T i l A).mpr
    ⟨(Finset.mem_erase.mp hl).1,Subsingleton.elim _ _⟩
  have hsub : componentMembers T i A ⊆ Finset.univ.erase i := by
    intro q hq
    exact Finset.mem_erase.mpr ⟨((mem_componentMembers T i q A).mp hq).1,Finset.mem_univ _⟩
  exact (component_support_connected T i A x ⟨u,j,hjA,hxj⟩ y ⟨w,l,hlA,hyl⟩).mono
    (CycleGroupDisjoint.selectedGraph_mono T hsub)

lemma odd_shortest_normal_spanning (ho : Odd n) :
    (selectedGraph T (Finset.univ.erase i)).support=Set.univ := by
  have hm := maximum_of_one_defect_failure hfail T hs
  have hn := LowDegreeAdjacency.failure_order_ge_five hG hfail
  have hk : 2 ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [ceil_half,Fintype.card_fin]; omega
  haveI : Nontrivial (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j,hji⟩ := exists_ne i
  let A := (normalGraph T i).connectedComponentMk ⟨j,hji⟩
  have hpos := shortest_component_positive hsmall hG hfail T hs i C hC hi hmin A
  have hle : componentSurplus T i A ≤ ∑ B, componentSurplus T i B :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
  have hid := component_surplus_identity T i (cycle_component_expands hsmall hG hfail T hs hm i C hC hi)
  have hb : (selectedGraph T (Finset.univ.erase i)).support.ncard ≤ n := by
    simpa only [Nat.card_fin] using Set.ncard_le_card (selectedGraph T (Finset.univ.erase i)).support
  apply (Set.eq_univ_iff_ncard _).mpr
  simp only [Nat.card_fin]
  simp only [ceil_half,Fintype.card_fin] at hid
  obtain ⟨m,hmo⟩ := ho
  omega

omit hmin in
lemma exists_shortest_connected_spanning_normal (ho : Odd n) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∃ j r, ∃ D : G.Walk r r,
      U.score=T.score ∧ D.IsCycle ∧ (U.walk j).toSubgraph=D.toSubgraph ∧
      ShortestCycle U D.length ∧
      (∀ A : (normalGraph U j).ConnectedComponent, 0 < componentSurplus U j A) ∧
      SupportConnected (selectedGraph U (Finset.univ.erase j)) ∧
      (selectedGraph U (Finset.univ.erase j)).support=Set.univ := by
  obtain ⟨U,j,r,D,hUs,hD,hj,hshort⟩ := exists_shortest_cycle T i C hC hi
  have hUs' : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by rw [hUs]; exact hs
  exact ⟨U,j,r,D,hUs,hD,hj,hshort,
    shortest_component_positive hsmall hG hfail U hUs' j D hD hj hshort,
    odd_shortest_normal_connected hsmall hG hfail U hUs' j D hD hj hshort ho,
    odd_shortest_normal_spanning hsmall hG hfail U hUs' j D hD hj hshort ho⟩

end Smallest

end ZeroComponentSuppression

end Erdos583Work
