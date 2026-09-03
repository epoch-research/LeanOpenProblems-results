import Submission.MatchingIntegrated

/-! Simultaneous suppression of independent degree-two vertices with distinct fresh shortcuts. -/
namespace Erdos583IndependentSuppressionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
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

end Erdos583IndependentSuppressionDevelopment
