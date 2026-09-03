import Submission.LongLollipopEar

/-! Simultaneous expansion of distinct fresh shortcut edges into paths with
private internal vertices. No separation of the shortcuts among path members
is needed under the explicit privacy hypotheses. -/
namespace Erdos583PrivatePathExpansionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

variable {V I : Type*}

lemma adj_sup_finset (A : Finset I) (f : I → SimpleGraph V) (x y : V) :
    (A.sup f).Adj x y ↔ ∃ i ∈ A, (f i).Adj x y := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih => simp only [Finset.sup_insert,sup_adj,ih,Finset.mem_insert]; aesop

noncomputable def chords (A : Finset I) (a b : I → V) : SimpleGraph V :=
  A.sup fun i ↦ edge (a i) (b i)

noncomputable def arcs {G : SimpleGraph V} (A : Finset I) {a b : I → V}
    (P : ∀ i, G.Walk (a i) (b i)) : SimpleGraph V :=
  A.sup fun i ↦ (P i).toSubgraph.spanningCoe

lemma chords_adj (A : Finset I) (a b : I → V) (x y : V) :
    (chords A a b).Adj x y ↔ ∃ i ∈ A, (edge (a i) (b i)).Adj x y :=
  adj_sup_finset A _ x y

lemma arcs_adj {G : SimpleGraph V} (A : Finset I) {a b : I → V}
    (P : ∀ i, G.Walk (a i) (b i)) (x y : V) :
    (arcs A P).Adj x y ↔ ∃ i ∈ A, (P i).toSubgraph.Adj x y := adj_sup_finset A _ x y

lemma chords_insert (A : Finset I) (i : I) (a b : I → V) :
    chords (insert i A) a b=edge (a i) (b i) ⊔ chords A a b := by simp only [chords,Finset.sup_insert]

lemma arcs_insert {G : SimpleGraph V} (A : Finset I) (i : I) {a b : I → V}
    (P : ∀ i, G.Walk (a i) (b i)) :
    arcs (insert i A) P=(P i).toSubgraph.spanningCoe ⊔ arcs A P := by simp only [arcs,Finset.sup_insert]

lemma expand_private_paths [Fintype V] {G : SimpleGraph V}
    (A : Finset I) (a b : I → V) (P : ∀ i, G.Walk (a i) (b i))
    (H : SimpleGraph V) (S : Set V)
    (hp : ∀ i ∈ A, (P i).IsPath)
    (ha : ∀ i ∈ A, a i ∉ S) (hb : ∀ i ∈ A, b i ∉ S)
    (hab : ∀ i ∈ A, a i ≠ b i) (hH : H.support ⊆ Sᶜ)
    (hInt : ∀ i ∈ A, ∀ z ∈ (P i).support, z ≠ a i → z ≠ b i → z ∈ S)
    (hprivate : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ z ∈ (P i).support,
      z ≠ a i → z ≠ b i → z ∉ (P j).support)
    (hfresh : ∀ i ∈ A, ¬H.Adj (a i) (b i))
    (hinj : ∀ i ∈ A, ∀ j ∈ A, s(a i,b i)=s(a j,b j) → i=j)
    (hnoarc : ∀ i ∈ A, ∀ j ∈ A, s(a i,b i) ∉ (P j).edges)
    (D : Finset (H ⊔ chords A a b).Subgraph) (hD : GoodDecomposition (H ⊔ chords A a b) D) :
    ∃ E : Finset (H ⊔ arcs A P).Subgraph, GoodDecomposition (H ⊔ arcs A P) E ∧ E.card ≤ D.card := by
  induction A using Finset.induction_on generalizing H with
  | empty => simpa only [chords,arcs,Finset.sup_empty,sup_bot_eq] using ⟨D,hD,le_refl D.card⟩
  | @insert i A hi ih =>
    have hiA : i ∈ insert i A := Finset.mem_insert_self _ _
    let H0 := H ⊔ edge (a i) (b i)
    have hH0 : H0.support ⊆ Sᶜ := by
      rintro z ⟨w,hzw|hzw⟩
      · exact hH ⟨w,hzw⟩
      · rcases (edge_adj _ _ _ _).mp hzw with ⟨⟨hz,_⟩|⟨hz,_⟩,_⟩
        · exact hz ▸ ha i hiA
        · exact hz ▸ hb i hiA
    have hf0 (j) (hj : j ∈ A) : ¬H0.Adj (a j) (b j) := by
      rintro (hh|hh)
      · exact hfresh j (Finset.mem_insert_of_mem hj) hh
      · have he : s(a j,b j)=s(a i,b i) := by
          rcases (edge_adj _ _ _ _).mp hh with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
          · simp only [h1,h2]
          · simp only [h1,h2,Sym2.eq_swap]
        exact hi ((hinj j (Finset.mem_insert_of_mem hj) i hiA he) ▸ hj)
    have hex : ∃ D0 : Finset (H0 ⊔ chords A a b).Subgraph,
        GoodDecomposition (H0 ⊔ chords A a b) D0 ∧ D0.card ≤ D.card := by
      have he : H ⊔ chords (insert i A) a b=H0 ⊔ chords A a b := by rw [chords_insert]; exact (sup_assoc _ _ _).symm
      exact Eq.mp (congrArg (fun J : SimpleGraph V ↦ ∃ E : Finset J.Subgraph,
        GoodDecomposition J E ∧ E.card ≤ D.card) he) ⟨D,hD,le_refl _⟩
    obtain ⟨D0,hD0,hD0c⟩ := hex
    obtain ⟨E,hE,hEc⟩ := ih H0
      (fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hb j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hab j (Finset.mem_insert_of_mem hj)) hH0
      (fun j hj ↦ hInt j (Finset.mem_insert_of_mem hj))
      (fun j hj l hl ↦ hprivate j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl)) hf0
      (fun j hj l hl ↦ hinj j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl))
      (fun j hj l hl ↦ hnoarc j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl)) D0 hD0
    let J := H0 ⊔ arcs A P
    let K := H ⊔ arcs (insert i A) P
    have hPK : (P i).toSubgraph.spanningCoe ≤ K := by
      intro x y hxy
      exact Or.inr ((arcs_adj _ _ _ _).mpr ⟨i,hiA,hxy⟩)
    have hPi : ∀ e ∈ (P i).edges, e ∈ K.edgeSet := fun e he ↦
      edgeSet_mono hPK ((P i).mem_edges_toSubgraph.mpr he)
    let Q := (P i).transfer K hPi
    have hQ : Q.IsPath := (hp i hiA).transfer hPi
    have hQe : Q.toSubgraph.edgeSet=(P i).toSubgraph.edgeSet := by
      simp only [Q,Walk.edgeSet_toSubgraph,Walk.edges_transfer]
    have hbase : ¬(H ⊔ arcs A P).Adj (a i) (b i) := by
      rintro (hh|hh)
      · exact hfresh i hiA hh
      · obtain ⟨j,hj,hij⟩ := (arcs_adj A P _ _).mp hh
        exact hnoarc i hiA j (Finset.mem_insert_of_mem hj) ((P j).mem_edges_toSubgraph.mp hij)
    have hfr : ∀ z ∈ Q.support, z ≠ a i → z ≠ b i → z ∉ J.support := by
      intro z hz hza hzb ⟨w,hw⟩
      have hzP : z ∈ (P i).support := by simpa only [Q,Walk.support_transfer] using hz
      have hzS := hInt i hiA z hzP hza hzb
      rcases hw with (hw|hw)|hw
      · exact hH ⟨w,hw⟩ hzS
      · rcases (edge_adj _ _ _ _).mp hw with ⟨⟨hz,_⟩|⟨hz,_⟩,_⟩
        · exact hza hz
        · exact hzb hz
      · obtain ⟨j,hj,hzj⟩ := (arcs_adj A P _ _).mp hw
        exact hprivate i hiA j (Finset.mem_insert_of_mem hj) (fun he ↦ hi (he.symm ▸ hj))
          z hzP hza hzb (Walk.mem_support_of_adj_toSubgraph hzj)
    have hJ : J=(H ⊔ arcs A P) ⊔ edge (a i) (b i) := by dsimp [J,H0]; ac_rfl
    have hK : K=(H ⊔ arcs A P) ⊔ (P i).toSubgraph.spanningCoe := by
      dsimp only [K]; rw [arcs_insert]; ac_rfl
    have hcover : K.edgeSet=(J.edgeSet \ {s(a i,b i)}) ∪ Q.toSubgraph.edgeSet := by
      rw [hJ,edgeSet_sup_edge_diff _ (hab i hiA) hbase,hQe,hK,edgeSet_sup]
      rfl
    have heJ : J.Adj (a i) (b i) := Or.inl (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab i hiA⟩))
    obtain ⟨F,hF,hFc⟩ := hE.expand_edge heJ Q hQ hfr hcover
    exact ⟨F,hF,hFc.trans (hEc.trans hD0c)⟩


lemma chords_support_outside (A : Finset I) (a b : I → V) (S : Set V)
    (ha : ∀ i ∈ A, a i ∉ S) (hb : ∀ i ∈ A, b i ∉ S) :
    (chords A a b).support ⊆ Sᶜ := by
  rintro x ⟨y,hxy⟩
  obtain ⟨i,hi,hxy⟩ := (chords_adj A a b x y).mp hxy
  rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨hx,_⟩|⟨hx,_⟩,_⟩
  · exact hx ▸ ha i hi
  · exact hx ▸ hb i hi

lemma compressed_support_connected {G : SimpleGraph V}
    (A : Finset I) (a b : I → V) (P : ∀ i, G.Walk (a i) (b i)) (H : SimpleGraph V) (S : Set V)
    (ha : ∀ i ∈ A, a i ∉ S) (hb : ∀ i ∈ A, b i ∉ S)
    (hab : ∀ i ∈ A, a i ≠ b i) (hH : H.support ⊆ Sᶜ)
    (hInt : ∀ i ∈ A, ∀ z ∈ (P i).support, z ≠ a i → z ≠ b i → z ∈ S)
    (hprivate : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ z ∈ (P i).support,
      z ≠ a i → z ≠ b i → z ∉ (P j).support)
    (hc : SupportConnected (H ⊔ arcs A P)) : SupportConnected (H ⊔ chords A a b) := by
  let F := H ⊔ arcs A P
  let J := H ⊔ chords A a b
  let Internal (z : V) : Prop := ∃ i ∈ A, z ∈ (P i).support ∧ z ≠ a i ∧ z ≠ b i
  let f (z : V) : V := if hh : Internal z then a (Classical.choose hh) else z
  have hout (z : V) (hz : z ∉ S) : f z=z := by
    have hn : ¬Internal z := by
      rintro ⟨i,hi,hzi,hza,hzb⟩
      exact hz (hInt i hi z hzi hza hzb)
    exact dif_neg hn
  have hinside (i : I) (hi : i ∈ A) (z : V) (hz : z ∈ (P i).support)
      (hza : z ≠ a i) (hzb : z ≠ b i) : f z=a i := by
    have he : Internal z := ⟨i,hi,hz,hza,hzb⟩
    have hch := Classical.choose_spec he
    have hsame : Classical.choose he=i := by
      by_contra hne
      exact hprivate i hi (Classical.choose he) hch.1 (fun h ↦ hne h.symm) z hz hza hzb hch.2.1
    simp only [f,dif_pos he,hsame]
  have hendpoint (i : I) (hi : i ∈ A) (z : V) (hz : z ∈ (P i).support) :
      f z=a i ∨ f z=b i := by
    by_cases hza : z=a i
    · subst z; exact Or.inl (hout _ (ha i hi))
    by_cases hzb : z=b i
    · subst z; exact Or.inr (hout _ (hb i hi))
    exact Or.inl (hinside i hi z hz hza hzb)
  have hedge (i : I) (hi : i ∈ A) : J.Adj (a i) (b i) :=
    Or.inr ((chords_adj A a b _ _).mpr ⟨i,hi,(edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab i hi⟩⟩)
  have hf (x y : V) (hxy : F.Adj x y) : J.Reachable (f x) (f y) := by
    rcases hxy with hxy|hxy
    · rw [hout x (hH ⟨y,hxy⟩),hout y (hH ⟨x,hxy.symm⟩)]
      exact (show J.Adj x y from Or.inl hxy).reachable
    · obtain ⟨i,hi,hxy⟩ := (arcs_adj A P x y).mp hxy
      have hx := hendpoint i hi x (Walk.mem_support_of_adj_toSubgraph hxy)
      have hy := hendpoint i hi y (Walk.mem_support_of_adj_toSubgraph hxy.symm)
      rcases hx with hx|hx <;> rcases hy with hy|hy <;> rw [hx,hy]
      · exact (hedge i hi).reachable
      · exact (hedge i hi).reachable.symm
  have hJS : J.support ⊆ Sᶜ := by
    rintro x ⟨y,hxy|hxy⟩
    · exact hH ⟨y,hxy⟩
    · exact chords_support_outside A a b S ha hb ⟨y,hxy⟩
  have hsub : J.support ⊆ F.support := by
    rintro x ⟨y,hxy|hxy⟩
    · exact ⟨y,Or.inl hxy⟩
    · obtain ⟨i,hi,hxy⟩ := (chords_adj A a b x y).mp hxy
      have hn : ¬(P i).Nil := Walk.not_nil_of_ne (hab i hi)
      have hnr : ¬(P i).reverse.Nil := Walk.not_nil_of_ne (hab i hi).symm
      have haF : a i ∈ F.support := ⟨(P i).snd,Or.inr ((arcs_adj A P _ _).mpr
        ⟨i,hi,(P i).toSubgraph_adj_snd hn⟩)⟩
      have hbF : b i ∈ F.support := ⟨(P i).reverse.snd,Or.inr ((arcs_adj A P _ _).mpr
        ⟨i,hi,by simpa only [Walk.toSubgraph_reverse] using (P i).reverse.toSubgraph_adj_snd hnr⟩)⟩
      rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨hx,_⟩|⟨hx,_⟩,_⟩
      · exact hx ▸ haF
      · exact hx ▸ hbF
  intro x hx y hy
  have hh := reachable_map_to_reachable f hf (hc x (hsub hx) y (hsub hy))
  rwa [hout x (hJS hx),hout y (hJS hy)] at hh

lemma compressed_private_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    [Fintype V] {G : SimpleGraph V}
    (A : Finset I) (a b : I → V) (P : ∀ i, G.Walk (a i) (b i)) (H : SimpleGraph V) (S : Set V)
    (hp : ∀ i ∈ A, (P i).IsPath)
    (ha : ∀ i ∈ A, a i ∉ S) (hb : ∀ i ∈ A, b i ∉ S)
    (hab : ∀ i ∈ A, a i ≠ b i) (hH : H.support ⊆ Sᶜ)
    (hInt : ∀ i ∈ A, ∀ z ∈ (P i).support, z ≠ a i → z ≠ b i → z ∈ S)
    (hprivate : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ z ∈ (P i).support,
      z ≠ a i → z ≠ b i → z ∉ (P j).support)
    (hfresh : ∀ i ∈ A, ¬H.Adj (a i) (b i))
    (hinj : ∀ i ∈ A, ∀ j ∈ A, s(a i,b i)=s(a j,b j) → i=j)
    (hnoarc : ∀ i ∈ A, ∀ j ∈ A, s(a i,b i) ∉ (P j).edges)
    (hc : SupportConnected (H ⊔ arcs A P)) (hsize : Sᶜ.ncard < n) :
    ∃ E : Finset (H ⊔ arcs A P).Subgraph, GoodDecomposition (H ⊔ arcs A P) E ∧
      E.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ := by
  have hJ : (H ⊔ chords A a b).support ⊆ Sᶜ := by
    rintro x ⟨y,hxy|hxy⟩
    · exact hH ⟨y,hxy⟩
    · exact chords_support_outside A a b S ha hb ⟨y,hxy⟩
  have hcard := Set.ncard_le_ncard hJ
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall (H ⊔ chords A a b)
    (compressed_support_connected A a b P H S ha hb hab hH hInt hprivate hc) (by omega)
  obtain ⟨E,hE,hEc⟩ := expand_private_paths A a b P H S hp ha hb hab hH hInt hprivate hfresh hinj hnoarc D hD
  refine ⟨E,hE,?_⟩
  rw [ceil_half] at hDc ⊢
  omega

end Erdos583PrivatePathExpansionDevelopment
