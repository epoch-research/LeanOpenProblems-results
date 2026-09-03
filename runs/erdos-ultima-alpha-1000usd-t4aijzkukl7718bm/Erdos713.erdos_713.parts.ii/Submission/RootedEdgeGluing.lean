import FormalConjecturesUtil
import Submission.CompactCoherentEdgesAudit

/-! Edge gluing preserves oriented rooted bounds under explicit rooted
hypotheses for both pieces. Edge roles need not be aligned by automorphisms. -/
open SimpleGraph Filter Asymptotics Finset
namespace Erdos713RootedEdges
open Erdos713EdgeAttachments Erdos713RootPower Erdos713Rate

lemma exists_disjoint_petal {A W V : Type*} [Fintype W] {F : SimpleGraph A}
    {H : SimpleGraph W} {G : SimpleGraph V} {x y : A} {p q : V}
    (P : Erdos713EdgeFan.Packing F G x y p q (Fintype.card W+1)) (f : H.Copy G) :
    ∃ i, ∀ a, (a ≠ x ∧ a ≠ y) → ∀ b, P.copies i a ≠ f b := by
  classical
  by_contra hh
  push_neg at hh
  choose a ha b hab using hh
  have hinj : Function.Injective b := by
    intro i j hij
    by_contra hne
    exact P.disjoint i j hne (a i) (a j) (ha i) (ha j)
      ((hab i).trans ((congrArg f hij).trans (hab j).symm))
  have hc := Fintype.card_le_of_injective b hinj
  simp only [Fintype.card_fin] at hc
  omega

lemma rooted_copy_of_packing {A W V : Type*} [Fintype W] {F : SimpleGraph A}
    {H : SimpleGraph W} {G : SimpleGraph V} {x y : A} {u v : W} {p q : V}
    (P : Erdos713EdgeFan.Packing F G x y p q (Fintype.card W+1)) (f : H.Copy G)
    (hu : f u = p) (hv : f v = q) :
    ∃ g : (paste F x y H u v).Copy G, g (.inl u) = p := by
  obtain ⟨i,hi⟩ := exists_disjoint_petal P f
  exact ⟨extendCopy f u v (P.copies i) ((P.left i).trans hu.symm)
    ((P.right i).trans hv.symm) (fun a b => hi a.val a.prop b),hu⟩

lemma rooted_blockers {A W V : Type*} [Fintype A] [Fintype W]
    (F : SimpleGraph A) (x y : A) (H : SimpleGraph W) (u v : W)
    (G : SimpleGraph V) (S : Set V)
    (hroot : ∀ f : (paste F x y H u v).Copy G, f (.inl u) ∉ S) :
    ∀ p q, ∃ B : Finset V, p ∉ B ∧ q ∉ B ∧
      B.card ≤ (Fintype.card W+1)*Fintype.card A ∧
      (p ∈ S →
        (∀ f : F.Copy G, f x = p → f y = q → ∃ a, (a ≠ x ∧ a ≠ y) ∧ f a ∈ B) ∨
        (∀ f : H.Copy G, f u = p → f v = q → False)) := by
  classical
  intro p q
  by_cases hp : p ∈ S
  · rcases Erdos713EdgeFan.packing_or_blocker F G x y p q (Fintype.card W+1) with hP | hB
    · obtain ⟨P⟩ := hP
      refine ⟨∅,by simp,by simp,by simp,fun _ => Or.inr ?_⟩
      intro f hu hv
      obtain ⟨g,hg⟩ := rooted_copy_of_packing P f hu hv
      exact hroot g (hg.symm ▸ hp)
    · obtain ⟨B,hp,hq,hc,hB⟩ := hB
      exact ⟨B,hp,hq,hc,fun _ => Or.inl hB⟩
  · exact ⟨∅,by simp,by simp,by simp,fun hp' => (hp hp').elim⟩

/-- Keep the edges whose orientation from S satisfies P. -/
def branch {V : Type*} (G : SimpleGraph V) (S : Set V) (P : V → V → Prop) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((u ∈ S ∧ P u v) ∨ (v ∈ S ∧ P v u))
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless _ h := G.loopless _ h.1

lemma branch_le {V : Type*} (G : SimpleGraph V) (S : Set V) (P : V → V → Prop) :
    branch G S P ≤ G := fun _ _ h => h.1

lemma branch_property {V : Type*} {G : SimpleGraph V} {S : Set V} {P : V → V → Prop}
    (hB : G.IsBipartiteWith S Sᶜ) {u v : V} (hu : u ∈ S) (h : (branch G S P).Adj u v) :
    P u v := by
  rcases h.2 with ⟨_,hP⟩ | ⟨hv,_⟩
  · exact hP
  · exact (hB.mem_of_mem_adj hu h.1 hv).elim

lemma branch_bipartite {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hB : G.IsBipartiteWith S Sᶜ) (P : V → V → Prop) :
    (branch G S P).IsBipartiteWith S Sᶜ :=
  ⟨hB.1,by intro u v h; exact hB.2 h.1⟩

lemma branch_edge_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V}
    (hB : G.IsBipartiteWith S Sᶜ) (P : V → V → Prop) :
    Nat.card G.edgeSet ≤ Nat.card (branch G S P).edgeSet +
      Nat.card (branch G S (fun u v => ¬ P u v)).edgeSet := by
  classical
  simp only [← Fintype.card_eq_nat_card,← edgeFinset_card]
  apply (card_le_card (show G.edgeFinset ⊆
    (branch G S P).edgeFinset ∪ (branch G S (fun u v => ¬ P u v)).edgeFinset from ?_)).trans
      (card_union_le _ _)
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : G.Adj u v := by simpa using he
    rcases hB.2 huv with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · by_cases hP : P u v <;> simp [branch,huv,hu,hP]
    · by_cases hP : P v u <;> simp [branch,huv,hv,hP]

/-- This theorem assumes BOTH rooted upper bounds. It does not identify
ordinary and rooted thresholds for arbitrary graphs. Only the fresh piece
needs to have no isolated vertices. -/
lemma root_bound {A W : Type*} [Fintype A] [Fintype W]
    {F : SimpleGraph A} {x y : A} (hxy : F.Adj x y)
    (hNoIso : ∀ a, ∃ b, F.Adj a b) {H : SimpleGraph W} {u v : W} (huv : H.Adj u v)
    {r : ℝ} (hF : RootPowerBound F x r) (hH : RootPowerBound H u r) :
    RootPowerBound (paste F x y H u v) (.inl u) r := by
  classical
  obtain ⟨C,hC,hF⟩ := hF
  obtain ⟨D,hD,hH⟩ := hH
  let k : ℕ := (Fintype.card W+1)*Fintype.card A
  let L : ℕ := 2^(2*k+2)
  refine ⟨(L : ℝ)*(C+D),by positivity,?_⟩
  intro n G S hBip hroot
  choose B hb₀ hb₁ hk hB using rooted_blockers F x y H u v G S hroot
  let P : Fin n → Fin n → Prop := fun p q =>
    ∀ f : F.Copy G, f x = p → f y = q → ∃ a, (a ≠ x ∧ a ≠ y) ∧ f a ∈ B p q
  have hkeep (σ : Fin n → Bool) :
      ((Erdos713EdgeFan.keep G B σ).edgeFinset.card : ℝ) ≤ (C+D)*(n : ℝ)^r := by
    let K := Erdos713EdgeFan.keep G B σ
    have hKB : K.IsBipartiteWith S Sᶜ := ⟨hBip.1,by intro p q h; exact hBip.2 h.1⟩
    have hRootF (f : F.Copy (branch K S P)) : f x ∉ S := by
      intro hf
      let fK : F.Copy K := (Copy.ofLE _ _ (branch_le K S P)).comp f
      let g : F.Copy G := (Copy.ofLE _ _ (Erdos713EdgeFan.keep_le G B σ)).comp fK
      have hP : P (g x) (g y) := branch_property hKB hf (f.toHom.map_adj hxy)
      obtain ⟨a,_,ha⟩ := hP g rfl rfl
      have hfalse : σ (g a) = false := (fK.toHom.map_adj hxy).2.2.2.1 (g a) ha
      obtain ⟨b,hab⟩ := hNoIso a
      have htrue : σ (g a) = true := (fK.toHom.map_adj hab).2.1
      exact Bool.noConfusion (htrue.symm.trans hfalse)
    have hRootH (f : H.Copy (branch K S (fun p q => ¬ P p q))) : f u ∉ S := by
      intro hf
      let fK : H.Copy K := (Copy.ofLE _ _ (branch_le K S _)).comp f
      let g : H.Copy G := (Copy.ofLE _ _ (Erdos713EdgeFan.keep_le G B σ)).comp fK
      have hnP : ¬ P (g u) (g v) := branch_property hKB hf (f.toHom.map_adj huv)
      rcases hB (g u) (g v) hf with hP | hNoH
      · exact hnP hP
      · exact hNoH g rfl rfl
    have h₁ := hF n (branch K S P) S (branch_bipartite hKB P) hRootF
    have h₂ := hH n (branch K S (fun p q => ¬ P p q)) S (branch_bipartite hKB _) hRootH
    have hs : (Nat.card K.edgeSet : ℝ) ≤ (Nat.card (branch K S P).edgeSet : ℝ) +
        (Nat.card (branch K S (fun p q => ¬ P p q)).edgeSet : ℝ) := by
      exact_mod_cast branch_edge_bound hKB P
    simp only [edgeFinset_card,Fintype.card_eq_nat_card]
    change (Nat.card K.edgeSet : ℝ) ≤ _
    nlinarith
  have hh := Erdos713EdgeFan.real_edges_le_of_keep_bound G B k ((C+D)*(n : ℝ)^r)
    (fun p q => ⟨hb₀ p q,hb₁ p q⟩) hk (by positivity) hkeep
  simpa only [L,edgeFinset_card,Fintype.card_eq_nat_card,mul_assoc] using hh

lemma root_rate {A W : Type*} [Fintype A] [Fintype W]
    {F : SimpleGraph A} {x y : A} (hxy : F.Adj x y)
    (hNoIso : ∀ a, ∃ b, F.Adj a b) {H : SimpleGraph W} {u v : W} (huv : H.Adj u v)
    {a b : ℝ} (hF : HasRootRate F x a) (hH : HasRootRate H u b) :
    HasRootRate (paste F x y H u v) (.inl u) (max a b) := by
  refine ⟨hF.one_le.trans (le_max_left _ _),
    root_bound hxy hNoIso huv (hF.upper.mono (le_max_left _ _))
      (hH.upper.mono (le_max_right _ _)),?_⟩
  intro r hr hR
  apply max_le
  · have hR' : RootPowerBound (paste F x y H u v) ((petalCopy F hxy H huv) x) r := by
      change RootPowerBound (paste F x y H u v) (petalMap x y u v x) r
      simpa only [petalMap,dif_pos rfl] using hR
    exact hF.lower r hr (hR'.of_copy (petalCopy F hxy H huv) x)
  · exact hH.lower r hr (hR.of_copy (oldCopy F x y H u v) u)

lemma rate {A W : Type*} [Fintype A] [Fintype W]
    {F : SimpleGraph A} {x y : A} (hxy : F.Adj x y)
    (hNoIso : ∀ a, ∃ b, F.Adj a b) {H : SimpleGraph W} {u v : W} (huv : H.Adj u v)
    {a b : ℝ} (hF : HasRate F a) (hH : HasRate H b)
    (hRF : RootPowerBound F x a) (hRH : RootPowerBound H u b) :
    HasRate (paste F x y H u v) (max a b) := by
  refine ⟨hF.one_le.trans (le_max_left _ _),
    (root_bound hxy hNoIso huv (hRF.mono (le_max_left _ _))
      (hRH.mono (le_max_right _ _))).upper,?_⟩
  intro r hr hR
  exact max_le
    (hF.lower r hr ((extremal_mono_bigO ⟨petalCopy F hxy H huv⟩).trans hR))
    (hH.lower r hr ((extremal_mono_bigO ⟨oldCopy F x y H u v⟩).trans hR))

lemma rooted_rate {A W : Type*} [Fintype A] [Fintype W]
    {F : SimpleGraph A} {x y : A} (hxy : F.Adj x y) (hFConn : F.Connected)
    {H : SimpleGraph W} {u v : W} (huv : H.Adj u v) (hHConn : H.Connected)
    (hF : Erdos713ActualBlocks.RootedRate F) (hH : Erdos713ActualBlocks.RootedRate H) :
    Erdos713ActualBlocks.RootedRate (paste F x y H u v) := by
  obtain ⟨a,hFa,hRF⟩ := hF
  obtain ⟨b,hHb,hRH⟩ := hH
  letI : Nontrivial A := ⟨⟨x,y,hxy.ne⟩⟩
  have hNoIso := hFConn.preconnected.exists_adj_of_nontrivial
  apply Erdos713ActualBlocks.RootedRate.of_one_root
    (paste_connected hxy hFConn hHConn huv) (.inl u) (r := max a b)
  · simpa only [Rat.cast_max] using rate hxy hNoIso huv hFa hHb (hRF x) (hRH u)
  · simpa only [Rat.cast_max] using root_bound hxy hNoIso huv
      ((hRF x).mono (le_max_left _ (b : ℝ))) ((hRH u).mono (le_max_right (a : ℝ) _))

/-- Unlike the earlier aligned-embedding argument, this corollary assumes
rooted base data and does not require edge alignability. -/
lemma built_root_bounds {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hFConn : F.Connected)
    {H : SimpleGraph W} {u v : W} (h : Erdos713EdgeAttachments.Built F x y H u v)
    {r : ℝ} (hR : ∀ z, RootPowerBound F z r) : ∀ z, RootPowerBound H z r := by
  letI : Nontrivial A := ⟨⟨x,y,hxy.ne⟩⟩
  have hNoIso := hFConn.preconnected.exists_adj_of_nontrivial
  induction h with
  | base => exact hR
  | @step W _ H a b h u v huv ih =>
    intro z
    have hb := root_bound hxy hNoIso huv (hR x) (ih u)
    exact hb.of_reachable ((paste_connected hxy hFConn (h.connected hxy hFConn) huv) _ z)

lemma built_rate {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hFConn : F.Connected)
    {H : SimpleGraph W} {u v : W} (h : Erdos713EdgeAttachments.Built F x y H u v)
    {r : ℝ} (hRate : HasRate F r) (hR : ∀ z, RootPowerBound F z r) : HasRate H r := by
  refine ⟨hRate.one_le,(built_root_bounds hxy hFConn h hR u).upper,?_⟩
  intro a ha hA
  exact hRate.lower a ha ((extremal_mono_bigO h.contains).trans hA)

lemma sandwich_rooted_rate {A T : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hFConn : F.Connected) (hF : Erdos713ActualBlocks.RootedRate F)
    {J : SimpleGraph T} (h : Erdos713EdgeAttachments.Sandwich F x y J) :
    Erdos713ActualBlocks.RootedRate J := by
  obtain ⟨W,H,u,v,h,hlo,hhi⟩ := h
  obtain ⟨r,hRate,hR⟩ := hF
  obtain ⟨f⟩ := hhi
  refine ⟨r,⟨hRate.one_le,(extremal_mono_bigO ⟨f⟩).trans
    (built_rate hxy hFConn h hRate hR).upper,?_⟩,
    fun z => (built_root_bounds hxy hFConn h hR (f z)).of_copy f z⟩
  intro a ha hA
  exact hRate.lower a ha ((extremal_mono_bigO hlo).trans hA)

/-- Finite mixtures of small-shore core pieces glued along arbitrary edges.
There is no common base graph or alignment assumption. -/
inductive MixedBuilt : {W : Type} → SimpleGraph W → Prop
  | base {W : Type} [Fintype W] (F : SimpleGraph W) (S : Set W)
      (hConn : F.Connected) (hB : F.IsBipartiteWith S Sᶜ) (hS : Nat.card S ≤ 3)
      (hd : ∀ z, 2 ≤ Nat.card (F.neighborSet z)) : MixedBuilt F
  | iso {A W : Type} {F : SimpleGraph A} {H : SimpleGraph W}
      (e : H ≃g F) (h : MixedBuilt F) : MixedBuilt H
  | join {A W : Type} [Fintype A] [Fintype W]
      {F : SimpleGraph A} {H : SimpleGraph W} (hF : MixedBuilt F) (hH : MixedBuilt H)
      (x y : A) (u v : W) (hxy : F.Adj x y) (huv : H.Adj u v) :
      MixedBuilt (paste F x y H u v)

lemma MixedBuilt.connected {W : Type} {H : SimpleGraph W} (h : MixedBuilt H) : H.Connected := by
  induction h with
  | base F S hConn hB hS hd => exact hConn
  | iso e h ih => exact ih.map e.symm.toHom e.symm.toEquiv.surjective
  | join hF hH x y u v hxy huv ihF ihH => exact paste_connected hxy ihF ihH huv

lemma MixedBuilt.isBipartite {W : Type} {H : SimpleGraph W} (h : MixedBuilt H) : H.IsBipartite := by
  induction h with
  | base F S hConn hB hS hd => exact hB.isBipartite
  | iso e h ih => exact ih.of_hom e.toHom
  | join hF hH x y u v hxy huv ihF ihH => exact paste_isBipartite hxy ihF ihH huv

lemma MixedBuilt.rooted_rate {W : Type} {H : SimpleGraph W} (h : MixedBuilt H) :
    Erdos713ActualBlocks.RootedRate H := by
  induction h with
  | base F S hConn hB hS hd =>
    letI := hConn.nonempty
    exact small_core F S hB hS hd
  | iso e h ih => exact ih.of_iso e
  | join hF hH x y u v hxy huv ihF ihH =>
    exact Erdos713RootedEdges.rooted_rate hxy hF.connected huv hH.connected ihF ihH

lemma MixedBuilt.rational {W : Type} {H : SimpleGraph W} (h : MixedBuilt H)
    {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (hAsymptotic : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr,_⟩ := h.rooted_rate
  exact ⟨r,hr.unique (rate_of_asymptotic hα hc hAsymptotic)⟩

lemma block_rates_of_mixed_blocks {W : Type} [Fintype W] (G : SimpleGraph W)
    (h : ∀ S : Set W, Erdos713Blocks.IsBlock G S → 3 ≤ Nat.card S →
      Erdos713CycleAssembly.Piece (G.induce S) ∨ MixedBuilt (G.induce S)) :
    Erdos713ActualBlocks.BlockRates G := by
  classical
  intro S hS hCyc
  rcases h S hS hCyc with hOld | hNew
  · letI := hS.connected.nonempty
    exact hOld.rooted_rate (hS.noCut.min_degree hS.connected
      (by simpa only [Fintype.card_eq_nat_card] using hCyc))
  · exact hNew.rooted_rate

#print axioms exists_disjoint_petal
#print axioms rooted_blockers
#print axioms branch_edge_bound
#print axioms root_bound
#print axioms root_rate
#print axioms rate
#print axioms rooted_rate
#print axioms sandwich_rooted_rate
#print axioms MixedBuilt.rooted_rate
#print axioms block_rates_of_mixed_blocks
end Erdos713RootedEdges
