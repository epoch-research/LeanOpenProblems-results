import Submission.MultiForestAbsorption
import Submission.LinearFamilyEfficient

/-!
The k+1 prescribed-forest allowance in MultiForestAbsorption is sharp: k
marked spanning trees do not in general complete k+2 prescribed forests.
This is an obstruction to that proof mechanism, not to Erdős 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ForestResourceSharpness

variable {V I : Type*} [Fintype V] [Fintype I]

/-- Each nonempty prescribed parity at a vertex consumes a different marked
edge. Covering all marked edges is not needed for this necessary condition. -/
lemma degree_resource_bound (R : SimpleGraph V) (X : I → SimpleGraph V) (v : V)
    (hsub : ∀ i, X i ≤ R)
    (hdis : Pairwise (fun i j => Disjoint (X i).edgeSet (X j).edgeSet))
    (hpos : ∀ i, 0 < (X i).degree v) : Fintype.card I ≤ R.degree v := by
  have hex (i : I) : ∃ w, (X i).Adj v w :=
    (degree_pos_iff_nonempty (G := X i) (v := v)).mp (hpos i)
  choose w hw using hex
  let f : I → R.neighborSet v := fun i => ⟨w i,hsub i (hw i)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have heq : w i = w j := congrArg Subtype.val hij
    exact Set.disjoint_left.mp (hdis hne)
      (show s(v,w i) ∈ (X i).edgeSet from hw i)
      (show s(v,w i) ∈ (X j).edgeSet from heq.symm ▸ hw j)
  simpa only [card_neighborSet_eq_degree] using Fintype.card_le_of_injective f hinj

lemma no_completion_of_degree_deficit (R : SimpleGraph V)
    (B : I → SimpleGraph V) (v : V)
    (hB : ∀ i, (B i).degree v = 1) (hsmall : R.degree v < Fintype.card I) :
    ¬ ∃ X : I → SimpleGraph V,
      (∀ i, X i ≤ R) ∧
      Pairwise (fun i j => Disjoint (X i).edgeSet (X j).edgeSet) ∧
      (∀ i x, Even ((X i).degree x + (B i).degree x)) := by
  rintro ⟨X,hsub,hdis,he⟩
  have hp (i : I) : 0 < (X i).degree v := by
    have hh := he i v
    rw [hB] at hh
    rw [Nat.even_iff] at hh
    omega
  exact (not_lt_of_ge (degree_resource_bound R X v hsub hdis hp)) hsmall

open LinearFamilyGap LinearFamilyGap.Efficient
variable {q : ℕ} [NeZero q]

abbrev Vert (q : ℕ) := Fin 6 × ZMod q
abbrev TreeIndex (q : ℕ) := {t : ZMod q // t ≠ 0}
abbrev ForestIndex (q : ℕ) := Option (ZMod q)

def root : Vert q := (0,0)
def tip (t : ZMod q) : Vert q := next t root
def cut (t : ZMod q) : Sym2 (Vert q) := s(root,tip t)
def path (t : ZMod q) : SimpleGraph (Vert q) := (F t).deleteEdges {cut t}
def red : SimpleGraph (Vert q) := ⨆ t : TreeIndex q, path t.val

def blue : ForestIndex q → SimpleGraph (Vert q)
  | none => path 0
  | some t => edge root (tip t)

lemma root_tip (t : ZMod q) : (F t).Adj root (tip t) := Or.inl rfl
lemma root_prev (t : ZMod q) : (F t).Adj root (prev t root) :=
  Or.inr (next_prev t root)

lemma path_le (t : ZMod q) : path t ≤ F t := deleteEdges_le _
lemma blue_le_cycle : ∀ i : ForestIndex q, blue i ≤ F (i.getD 0)
  | none => path_le 0
  | some t => (edge_le_iff (F t)).mpr (Or.inr (root_tip t))

lemma cut_not_mem_path (t : ZMod q) : cut t ∉ (path t).edgeSet := by
  rw [path,edgeSet_deleteEdges]
  simp

lemma path_tree (t : ZMod q) : (path t).IsTree := by
  have hcyc : (F t).IsCycles := by
    intro v hv
    have hh := F_regular t v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using hh
  have hconn : (path t).Connected := by
    apply (F_connected t).connected_delete_edge_of_not_isBridge
    intro hb
    exact (isBridge_iff.mp hb).2 (hcyc.reachable_deleteEdges (root_tip t))
  refine ⟨hconn,?_⟩
  exact proper_cycle_subgraph_acyclic (P t) (P_cycles t).1 (P_cycles t).2
    (path t) (path_le t) (cut t) (root_tip t) (cut_not_mem_path t)

lemma path_root_adj (t : ZMod q) (w : Vert q) :
    (path t).Adj root w ↔ w = prev t root := by
  rw [path,deleteEdges_adj]
  have hn := neighbors t (root (q := q))
  have htne : tip t ≠ prev t root := next_ne_prev t root
  have htip : root (q := q) ≠ tip t := (next_ne t root).symm
  have hprev : root (q := q) ≠ prev t root := (root_prev t).ne
  constructor
  · rintro ⟨h,he⟩
    have hw : w ∈ (F t).neighborSet root := h
    rw [hn] at hw
    rcases hw with hw | hw
    · exact (he (by simp [cut,tip,hw])).elim
    · exact hw
  · rintro rfl
    refine ⟨root_prev t,?_⟩
    simp only [Set.mem_singleton_iff,cut,Sym2.eq_iff]
    rintro (⟨_,h⟩ | ⟨h,_⟩)
    · exact htne h.symm
    · exact htip h

lemma path_root_degree (t : ZMod q) : (path t).degree root = 1 := by
  have hn : (path t).neighborSet root = {prev t root} := by
    ext w
    exact path_root_adj t w
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,hn]
  simp

lemma edge_root_degree (t : ZMod q) : (edge root (tip t)).degree root = 1 := by
  have hn : (edge root (tip t)).neighborSet root = {tip t} := by
    ext w
    simp only [mem_neighborSet,edge_adj,Set.mem_singleton_iff]
    have hne : root (q := q) ≠ tip t := (next_ne t root).symm
    aesop
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,hn]
  simp

lemma blue_root_degree (i : ForestIndex q) : (blue i).degree root = 1 := by
  cases i with
  | none => exact path_root_degree 0
  | some t =>
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using edge_root_degree t

lemma blue_forest (i : ForestIndex q) : (blue i).IsAcyclic := by
  cases i with
  | none => exact (path_tree 0).IsAcyclic
  | some t =>
    apply proper_cycle_subgraph_acyclic (P t) (P_cycles t).1 (P_cycles t).2
      (blue (some t)) (blue_le_cycle (some t)) s(root,prev t root) (root_prev t)
    intro h
    have hh := (edge_adj _ _ _ _).mp h
    have hn := next_ne_prev t (root (q := q))
    have hp := (root_prev t).ne
    rcases hh.1 with ⟨_,hh⟩ | ⟨hh,_⟩
    · exact hn hh.symm
    · exact (next_ne t root) hh.symm

lemma paths_disjoint : Pairwise (fun t u : ZMod q =>
    Disjoint (path t).edgeSet (path u).edgeSet) := by
  intro t u hne
  apply Set.disjoint_left.mpr
  intro e ht hu
  induction e using Sym2.ind with
  | h a b => exact hne (edge_parameter (path_le t ht) (path_le u hu))

lemma red_le : red (q := q) ≤ G (ZMod q) := by
  apply iSup_le
  intro t
  exact (path_le t.val).trans (F_le t.val)

lemma red_root_degree : (red (q := q)).degree root = Fintype.card (TreeIndex q) := by
  let f : TreeIndex q → (red (q := q)).neighborSet root := fun t =>
    ⟨prev t.val root, (le_iSup (fun s : TreeIndex q => path s.val) t)
      ((path_root_adj t.val _).mpr rfl)⟩
  have hi : Function.Injective f := by
    intro t u h
    apply Subtype.ext
    have heq : prev t.val root = prev u.val root := congrArg Subtype.val h
    exact edge_parameter (root_prev t.val) (heq.symm ▸ root_prev u.val)
  have hs : Function.Surjective f := by
    rintro ⟨w,hw⟩
    obtain ⟨t,ht⟩ := iSup_adj.mp hw
    refine ⟨t,?_⟩
    apply Subtype.ext
    exact ((path_root_adj t.val w).mp ht).symm
  simpa only [card_neighborSet_eq_degree] using (Fintype.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm

lemma treeIndex_card : Fintype.card (TreeIndex q) = q-1 := by
  have h := Fintype.card_subtype_compl (fun t : ZMod q => t = 0)
  simp only [Fintype.card_unique,ZMod.card] at h
  simpa only [TreeIndex] using h

lemma forestIndex_card : Fintype.card (ForestIndex q) = q+1 := by
  simp [ForestIndex,ZMod.card]

lemma no_completion :
    ¬ ∃ X : ForestIndex q → SimpleGraph (Vert q),
      (∀ i, X i ≤ red) ∧
      Pairwise (fun i j => Disjoint (X i).edgeSet (X j).edgeSet) ∧
      (∀ i x, Even ((X i).degree x + (blue i).degree x)) := by
  apply no_completion_of_degree_deficit red blue root blue_root_degree
  rw [red_root_degree,treeIndex_card,forestIndex_card]
  omega

lemma blue_some_edge {t : ZMod q} {e : Sym2 (Vert q)}
    (h : e ∈ (blue (some t)).edgeSet) : e = cut t := by
  have he : (blue (some t)).edgeSet = {cut t} :=
    edge_edgeSet_of_ne (root_tip t).ne
  rwa [he,Set.mem_singleton_iff] at h

lemma blue_pairwise : Pairwise (fun i j : ForestIndex q =>
    Disjoint (blue i).edgeSet (blue j).edgeSet) := by
  intro i j hne
  apply Set.disjoint_left.mpr
  intro e hi hj
  cases i with
  | none =>
    cases j with
    | none => exact hne rfl
    | some t =>
      have he := blue_some_edge hj
      rw [he] at hi
      have ht : (F 0).Adj root (tip t) := path_le 0 hi
      have h0 : (0 : ZMod q) = t := edge_parameter ht (root_tip t)
      subst t
      exact cut_not_mem_path 0 hi
  | some t =>
    cases j with
    | none =>
      have he := blue_some_edge hi
      rw [he] at hj
      have ht : (F 0).Adj root (tip t) := path_le 0 hj
      have h0 : (0 : ZMod q) = t := edge_parameter ht (root_tip t)
      subst t
      exact cut_not_mem_path 0 hj
    | some u =>
      have he : cut t = cut u := (blue_some_edge hi).symm.trans (blue_some_edge hj)
      have ht : (cut t) ∈ (F t).edgeSet := root_tip t
      have hu : (cut u) ∈ (F u).edgeSet := root_tip u
      rw [← he] at hu
      exact hne (congrArg some (edge_parameter ht hu))

lemma blue_disjoint_red (i : ForestIndex q) :
    Disjoint (blue i).edgeSet (red (q := q)).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e hb hr
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨t,ht⟩ := iSup_adj.mp hr
    cases i with
    | none =>
      have heq : (0 : ZMod q) = t.val := edge_parameter (path_le 0 hb) (path_le t.val ht)
      exact t.property heq.symm
    | some u =>
      have heq : u = t.val := edge_parameter (blue_le_cycle (some u) hb) (path_le t.val ht)
      subst u
      have he := blue_some_edge hb
      have hm : s(a,b) ∈ (path t.val).edgeSet := ht
      exact cut_not_mem_path t.val (he ▸ hm)

lemma blue_le_complement (i : ForestIndex q) : blue i ≤ G (ZMod q) \ red := by
  intro a b h
  refine ⟨F_le (i.getD 0) (blue_le_cycle i h),?_⟩
  intro hr
  exact Set.disjoint_left.mp (blue_disjoint_red i)
    (show s(a,b) ∈ (blue i).edgeSet from h) hr

lemma blue_cover (a b : Vert q) :
    (G (ZMod q) \ red).Adj a b ↔ ∃ i : ForestIndex q, (blue i).Adj a b := by
  constructor
  · rintro ⟨hg,hr⟩
    obtain ⟨t,ht⟩ := edge_covered a b hg
    by_cases he : s(a,b) = cut t
    · refine ⟨some t,?_⟩
      apply (adj_edge root (tip t)).mpr
      exact ⟨he.symm,hg.ne⟩
    · have hp : (path t).Adj a b := deleteEdges_adj.mpr
        ⟨ht,by simpa only [Set.mem_singleton_iff] using he⟩
      by_cases h0 : t = 0
      · subst t
        exact ⟨none,hp⟩
      · exact (hr ((le_iSup (fun u : TreeIndex q => path u.val) ⟨t,h0⟩) hp)).elim
  · rintro ⟨i,hi⟩
    exact blue_le_complement i hi

lemma graph_even : ∀ v, Even ((G (ZMod q)).degree v) := by
  intro v
  have hh := graph_regular (ZMod q) v
  rw [ZMod.card] at hh
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
  rw [hh]
  exact even_two_mul q

/-- All k, not a finite test: k marked spanning trees may fail to complete
k+2 prescribed forests, even though their union is an even simple graph. -/
theorem sharpness (k : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (G R : SimpleGraph W)
      (S : Fin k → SimpleGraph W) (B : Fin (k+2) → SimpleGraph W),
      G.Connected ∧ (∀ v, Even (G.degree v)) ∧ R ≤ G ∧
      (∀ i, (S i).IsTree ∧ S i ≤ R) ∧
      Pairwise (fun i j => Disjoint (S i).edgeSet (S j).edgeSet) ∧
      (∀ i, (B i).IsAcyclic) ∧
      Pairwise (fun i j => Disjoint (B i).edgeSet (B j).edgeSet) ∧
      (∀ a b, (G \ R).Adj a b ↔ ∃ i, (B i).Adj a b) ∧
      (¬ ∃ X : Fin (k+2) → SimpleGraph W,
        (∀ i, X i ≤ R) ∧
        Pairwise (fun i j => Disjoint (X i).edgeSet (X j).edgeSet) ∧
        (∀ i v, Even ((X i).degree v + (B i).degree v))) := by
  let q := k+1
  haveI : NeZero q := ⟨by dsimp [q]; omega⟩
  let et : Fin k ≃ TreeIndex q := Fintype.equivOfCardEq (by
    simp [q])
  let eb : Fin (k+2) ≃ ForestIndex q := Fintype.equivOfCardEq (by
    simp [q,add_assoc])
  refine ⟨Vert q,inferInstance,G (ZMod q),red,
    (fun i => path (et i).val),(fun i => blue (eb i)),
    (F_connected 0).mono (F_le 0),graph_even,red_le,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨path_tree (et i).val,le_iSup (fun t : TreeIndex q => path t.val) (et i)⟩
  · intro i j hij
    exact paths_disjoint (fun h => hij (et.injective (Subtype.ext h)))
  · intro i
    exact blue_forest (eb i)
  · intro i j hij
    exact blue_pairwise (fun h => hij (eb.injective h))
  · intro a b
    rw [blue_cover]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨eb.symm j,by simpa only [Equiv.apply_symm_apply] using hj⟩
    · rintro ⟨i,hi⟩
      exact ⟨eb i,hi⟩
  · rintro ⟨X,hsub,hdis,he⟩
    apply no_completion (q := q)
    refine ⟨(fun j => X (eb.symm j)),(fun j => hsub (eb.symm j)),?_,?_⟩
    · intro i j hij
      exact hdis (fun h => hij (eb.symm.injective h))
    · intro i v
      have hh := he (eb.symm i) v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Equiv.apply_symm_apply] using hh

/-- A graph whose edges all meet one vertex is a forest. -/
lemma acyclic_of_all_edges_meet (A : SimpleGraph V) (v : V)
    (hstar : ∀ a b, A.Adj a b → a = v ∨ b = v) : A.IsAcyclic := by
  have hlow (w : V) (hw : w ≠ v) : A.degree w ≤ 1 := by
    have hs : A.neighborSet w ⊆ {v} := by
      intro z hz
      exact (hstar w z hz).resolve_left hw
    have hh := Set.ncard_le_ncard hs
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq,Set.ncard_singleton] using hh
  intro u p hp
  have hhigh (w : V) (hw : w ∈ p.support) : 2 ≤ A.degree w := by
    have h2 : p.toSubgraph.degree w = 2 := by
      rw [Subgraph.degree,← Nat.card_eq_fintype_card]
      exact hp.ncard_neighborSet_toSubgraph_eq_two hw
    have hh := p.toSubgraph.degree_le w
    simp only [Subgraph.degree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      at h2 hh ⊢
    omega
  have huv : u = v := by
    by_contra hn
    have := hlow u hn
    have := hhigh u p.start_mem_support
    omega
  subst u
  have hsn := Walk.adj_snd hp.not_nil
  have hsm := List.mem_of_mem_tail (Walk.snd_mem_tail_support hp.not_nil)
  have := hhigh p.snd hsm
  have := hlow p.snd hsn.ne.symm
  omega

lemma blue_remainder_forest :
    (((G (ZMod q)) \ red) \ path 0).IsAcyclic := by
  apply acyclic_of_all_edges_meet _ (root (q := q))
  intro a b hab
  obtain ⟨i,hi⟩ := (blue_cover a b).mp hab.1
  cases i with
  | none => exact (hab.2 hi).elim
  | some t =>
    have hh := (edge_adj _ _ _ _).mp hi
    exact hh.1.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)

/-- The failed prescribed partition is not a failure of marked hitting:
for q>1 a different parity split does give a marked-hitting decomposition. -/
lemma hitting_decomposition (hq : 1 < q) :
    ∃ D : Finset (G (ZMod q)).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (G (ZMod q)) D ∧
      (∀ H ∈ D, (H.edgeSet ∩ (red (q := q)).edgeSet).Nonempty) ∧
      D.card ≤ (red (q := q)).edgeFinset.card := by
  have hn : 0 < Fintype.card (TreeIndex q) := by rw [treeIndex_card]; omega
  obtain ⟨t⟩ := Fintype.card_pos_iff.mp hn
  have hconn : (red (q := q)).Connected :=
    (path_tree t.val).isConnected.mono (le_iSup (fun t : TreeIndex q => path t.val) t)
  exact TwoForestAbsorption.hitting_of_two_forests (G (ZMod q)) red (path 0)
    red_le hconn graph_even (blue_le_complement none) (path_tree 0).IsAcyclic
    blue_remainder_forest

end Erdos184.ForestResourceSharpness
