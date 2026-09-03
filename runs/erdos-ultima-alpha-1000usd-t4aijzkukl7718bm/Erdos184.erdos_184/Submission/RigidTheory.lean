import Submission.Work

/-! Auxiliary rigidity theory for cycle-and-edge decompositions.
This file proves the linear bound for even rigid graphs, not the original conjecture. -/


/-! Source block: ChordalIncidence. -/

/-! Incidence counting through conformal chordal primal graphs.
These are auxiliary graph-theoretic lemmas, not a settlement of Erdős 184. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.ChordalIncidence
set_option maxHeartbeats 1000000

variable {V I : Type*}

/-- The primal graph of a family of finite vertex sets. -/
def primal (E : I → Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ i, x ∈ E i ∧ y ∈ E i
  symm := by rintro x y ⟨h,i,hx,hy⟩; exact ⟨h.symm,i,hy,hx⟩
  loopless := by intro x h; exact h.1 rfl

/-- An induced six-cycle in the incidence graph, expressed without walks. -/
def IncidenceTriangle (E : I → Finset V) : Prop :=
  ∃ i j k : I, ∃ x y z : V,
    x ∈ E i ∧ y ∈ E i ∧ z ∉ E i ∧
    y ∈ E j ∧ z ∈ E j ∧ x ∉ E j ∧
    z ∈ E k ∧ x ∈ E k ∧ y ∉ E k

/-- Every clique in the supported primal graph is contained in a piece. -/
def Conformal (E : I → Finset V) : Prop :=
  ∀ C : Finset V, C.Nonempty → (∀ x ∈ C, ∃ i, x ∈ E i) →
    (primal E).IsClique C → ∃ i, C ⊆ E i

lemma piece_clique (E : I → Finset V) (i : I) : (primal E).IsClique (E i) := by
  intro x hx y hy hxy
  exact ⟨hxy,i,hx,hy⟩

lemma conformal_of_no_incidenceTriangle [DecidableEq V] (E : I → Finset V)
    (hno : ¬ IncidenceTriangle E) : Conformal E := by
  intro C hC hsupp hcl
  by_contra hbad
  let P : Finset V → Prop := fun S => S ⊆ C ∧ ¬ ∃ i, S ⊆ E i
  obtain ⟨S,hS,hmin⟩ := exists_minimalFor_of_wellFoundedLT P Finset.card ⟨C,Finset.Subset.refl _,hbad⟩
  have hSC : S ⊆ C := hS.1
  have hSb : ¬ ∃ i, S ⊆ E i := hS.2
  obtain ⟨c,hc⟩ := hC
  obtain ⟨i₀,hi₀⟩ := hsupp c hc
  have hproper (T : Finset V) (hTS : T ⊆ S) (hlt : T.card < S.card) : ∃ i, T ⊆ E i := by
    by_contra hb
    have hm := hmin ⟨hTS.trans hSC,hb⟩ hlt.le
    omega
  have hSne : S.Nonempty := by
    by_contra hn
    have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hSb
    exact ⟨i₀,by simp [hz]⟩
  obtain ⟨x,hx⟩ := hSne
  have hcover (v : V) (hv : v ∈ S) : ∃ i, S.erase v ⊆ E i ∧ v ∉ E i := by
    obtain ⟨i,hi⟩ := hproper (S.erase v) (Finset.erase_subset _ _) (Finset.card_erase_lt_of_mem hv)
    refine ⟨i,hi,?_⟩
    intro hvi
    apply hSb
    refine ⟨i,?_⟩
    intro w hw
    by_cases hwv : w = v
    · simpa [hwv] using hvi
    · exact hi (Finset.mem_erase.mpr ⟨hwv,hw⟩)
  obtain ⟨ix,hix,hxix⟩ := hcover x hx
  have htwo : ∃ y ∈ S, y ≠ x := by
    by_contra hn
    push_neg at hn
    apply hSb
    obtain ⟨i,hi⟩ := hsupp x (hSC hx)
    refine ⟨i,?_⟩
    intro y hy
    have hxy : y = x := hn y hy
    simpa [hxy] using hi
  obtain ⟨y,hy,hyx⟩ := htwo
  obtain ⟨i,hxi,hyi⟩ := (hcl (hSC hx) (hSC hy) hyx.symm).2
  have hthird : ∃ z ∈ S, z ∉ E i := by
    by_contra hn
    push_neg at hn
    exact hSb ⟨i,hn⟩
  obtain ⟨z,hz,hzi⟩ := hthird
  have hzx : z ≠ x := by rintro rfl; exact hzi hxi
  have hzy : z ≠ y := by rintro rfl; exact hzi hyi
  obtain ⟨iy,hiy,hyiy⟩ := hcover y hy
  obtain ⟨iz,hiz,hziz⟩ := hcover z hz
  apply hno
  refine ⟨iz,ix,iy,x,y,z,?_,?_,hziz,?_,?_,hxix,?_,?_,hyiy⟩
  · exact hiz (Finset.mem_erase.mpr ⟨hzx.symm,hx⟩)
  · exact hiz (Finset.mem_erase.mpr ⟨hzy.symm,hy⟩)
  · exact hix (Finset.mem_erase.mpr ⟨hyx,hy⟩)
  · exact hix (Finset.mem_erase.mpr ⟨hzx,hz⟩)
  · exact hiy (Finset.mem_erase.mpr ⟨hzy,hz⟩)
  · exact hiy (Finset.mem_erase.mpr ⟨hyx.symm,hx⟩)

/-- Reachability with all vertices of the witnessing walk in a prescribed set. -/
def ReachIn (G : SimpleGraph V) (U : Set V) (a b : V) : Prop :=
  ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∈ U

lemma ReachIn.refl {G : SimpleGraph V} {U : Set V} {a : V} (ha : a ∈ U) : ReachIn G U a a :=
  ⟨.nil,by simpa using ha⟩

lemma ReachIn.left_mem {G : SimpleGraph V} {U : Set V} {a b : V}
    (h : ReachIn G U a b) : a ∈ U := by
  obtain ⟨p,hp⟩ := h
  exact hp a p.start_mem_support

lemma ReachIn.right_mem {G : SimpleGraph V} {U : Set V} {a b : V}
    (h : ReachIn G U a b) : b ∈ U := by
  obtain ⟨p,hp⟩ := h
  exact hp b p.end_mem_support

lemma ReachIn.symm {G : SimpleGraph V} {U : Set V} {a b : V}
    (h : ReachIn G U a b) : ReachIn G U b a := by
  obtain ⟨p,hp⟩ := h
  refine ⟨p.reverse,?_⟩
  simpa only [Walk.support_reverse,List.mem_reverse] using hp

lemma ReachIn.mono {G : SimpleGraph V} {U T : Set V} {a b : V}
    (h : ReachIn G U a b) (hUT : U ⊆ T) : ReachIn G T a b := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,fun x hx => hUT (hp x hx)⟩

lemma ReachIn.trans {G : SimpleGraph V} {U : Set V} {a b c : V}
    (hab : ReachIn G U a b) (hbc : ReachIn G U b c) : ReachIn G U a c := by
  obtain ⟨p,hp⟩ := hab
  obtain ⟨q,hq⟩ := hbc
  refine ⟨p.append q,?_⟩
  intro x hx
  rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
  · exact hp x hx
  · exact hq x hx

lemma ReachIn.of_adj {G : SimpleGraph V} {U : Set V} {a b : V}
    (hab : G.Adj a b) (ha : a ∈ U) (hb : b ∈ U) : ReachIn G U a b := by
  refine ⟨hab.toWalk,?_⟩
  simpa only [Adj.toWalk,Walk.support_cons,Walk.support_nil,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using
    (show ∀ x, x = a ∨ x = b → x ∈ U from fun x hx => hx.elim (fun h => h ▸ ha) (fun h => h ▸ hb))

/-- A walk has no graph edges between its vertices other than its own edges. -/
def InducedWalk {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Prop :=
  ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → s(x,y) ∈ p.edges

lemma consecutive_mem_edges {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (i : ℕ) (hi : i < p.length) :
    s(p.getVert i,p.getVert (i+1)) ∈ p.edges := by
  induction p generalizing i with
  | nil => simp at hi
  | @cons a b c hab p ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [Walk.getVert_cons_succ,Walk.edges_cons]
      exact List.mem_cons_of_mem _ (ih i (by simpa using hi))

lemma ReachIn.exists_induced_path [DecidableEq V] {G : SimpleGraph V} {U : Set V} {a b : V}
    (h : ReachIn G U a b) :
    ∃ p : G.Walk a b, (∀ x ∈ p.support, x ∈ U) ∧ p.IsPath ∧ InducedWalk p := by
  let P : G.Walk a b → Prop := fun p => ∀ x ∈ p.support, x ∈ U
  obtain ⟨p,hp,hmin⟩ := exists_minimalFor_of_wellFoundedLT P Walk.length h
  have hpath : p.IsPath := by
    have hb : P p.bypass := fun x hx => hp x (p.support_bypass_subset hx)
    have he : p.bypass = p := p.bypass_eq_self_of_length_le (hmin hb p.length_bypass_le)
    rw [← he]
    exact p.bypass_isPath
  refine ⟨p,hp,hpath,?_⟩
  have forward (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i < j)
      (hadj : G.Adj (p.getVert i) (p.getVert j)) :
      s(p.getVert i,p.getVert j) ∈ p.edges := by
    by_cases heq : j = i+1
    · subst j
      exact consecutive_mem_edges p i (by omega)
    have hgap : i+1 < j := by omega
    let q : G.Walk a b := (p.take i).append (Walk.cons hadj (p.drop j))
    have hq : P q := by
      intro x hx
      rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
      · apply hp x
        rw [Walk.take_support_eq_support_take_succ] at hx
        exact List.mem_of_mem_take hx
      · rcases List.mem_cons.mp hx with he | hx
        · subst x
          exact hp _ (p.getVert_mem_support i)
        · apply hp x
          rw [Walk.drop_support_eq_support_drop_min] at hx
          exact List.mem_of_mem_drop hx
    have hlen : q.length < p.length := by
      simp only [q,Walk.length_append,Walk.take_length,Walk.length_cons,Walk.drop_length,
        Nat.min_eq_left hi]
      omega
    have hm := hmin hq hlen.le
    omega
  intro x hx y hy hxy
  obtain ⟨i,rfl,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  obtain ⟨j,rfl,hj⟩ := Walk.mem_support_iff_exists_getVert.mp hy
  rcases lt_trichotomy i j with hij | hij | hij
  · exact forward i j hi hj hij hxy
  · subst j
    exact (hxy.ne rfl).elim
  · have he := forward j i hj hi hij hxy.symm
    simpa only [Sym2.eq_swap] using he

/-- Induced cycles in a chordal graph are cliques (and hence triangles). -/
def Chordal (G : SimpleGraph V) : Prop :=
  ∀ a (p : G.Walk a a), p.IsCycle → InducedWalk p →
    G.IsClique {x | x ∈ p.support}

lemma Chordal.adj_of_two_induced_paths {G : SimpleGraph V} (hch : Chordal G)
    {a b : V} (hab : a ≠ b) (p q : G.Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (hpi : InducedWalk p) (hqi : InducedWalk q)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b)
    (hcross : ∀ x ∈ p.support, ∀ y ∈ q.support,
      x ≠ a → x ≠ b → y ≠ a → y ≠ b → ¬ G.Adj x y) : G.Adj a b := by
  by_contra hnot
  have hedges : p.edges.Disjoint q.reverse.edges := by
    apply List.disjoint_left.mpr
    intro e hep heq
    rw [Walk.edges_reverse,List.mem_reverse] at heq
    induction e using Sym2.ind with | h x y =>
      have hx := hinter x (p.fst_mem_support_of_mem_edges hep) (q.fst_mem_support_of_mem_edges heq)
      have hy := hinter y (p.snd_mem_support_of_mem_edges hep) (q.snd_mem_support_of_mem_edges heq)
      have he := p.adj_of_mem_edges hep
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact he.ne rfl
      · exact hnot he
      · exact hnot he.symm
      · exact he.ne rfl
  have hcy : (p.append q.reverse).IsCycle := append_isCycle_of_support_inter hp hq.reverse hab hedges (by
    intro x hxp hxq
    exact hinter x hxp (by simpa only [Walk.support_reverse,List.mem_reverse] using hxq))
  have hsupport (x : V) : x ∈ (p.append q.reverse).support ↔ x ∈ p.support ∨ x ∈ q.support := by
    simp only [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse]
  have hboth (x : V) (hx : x = a ∨ x = b) : x ∈ p.support ∧ x ∈ q.support := by
    rcases hx with rfl | rfl <;> simp
  have hmix (x : V) (hx : x ∈ p.support) (y : V) (hy : y ∈ q.support) (hxy : G.Adj x y) :
      s(x,y) ∈ p.edges ∨ s(x,y) ∈ q.edges := by
    by_cases hxe : x = a ∨ x = b
    · exact Or.inr (hqi x (hboth x hxe).2 y hy hxy)
    by_cases hye : y = a ∨ y = b
    · exact Or.inl (hpi x hx y (hboth y hye).1 hxy)
    exact (hcross x hx y hy (fun h => hxe (Or.inl h)) (fun h => hxe (Or.inr h))
      (fun h => hye (Or.inl h)) (fun h => hye (Or.inr h)) hxy).elim
  have hci : InducedWalk (p.append q.reverse) := by
    intro x hx y hy hxy
    rw [Walk.edges_append,List.mem_append,Walk.edges_reverse,List.mem_reverse]
    rcases (hsupport x).mp hx with hx | hx <;> rcases (hsupport y).mp hy with hy | hy
    · exact Or.inl (hpi x hx y hy hxy)
    · exact hmix x hx y hy hxy
    · simpa only [Sym2.eq_swap] using hmix y hy x hx hxy.symm
    · exact Or.inr (hqi x hx y hy hxy)
  have hc := hch a (p.append q.reverse) hcy hci
  apply hnot
  exact hc (by simp) ((hsupport b).mpr (Or.inl p.end_mem_support)) hab

lemma Chordal.adj_of_separated_paths [DecidableEq V] {G : SimpleGraph V} (hch : Chordal G)
    (A B : Set V) (hdis : Disjoint A B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    {a b : V} (hab : a ≠ b)
    (hp : ReachIn G (A ∪ {a,b}) a b) (hq : ReachIn G (B ∪ {a,b}) a b) : G.Adj a b := by
  obtain ⟨p,hpU,hp,hpi⟩ := hp.exists_induced_path
  obtain ⟨q,hqU,hq,hqi⟩ := hq.exists_induced_path
  apply hch.adj_of_two_induced_paths hab p q hp hq hpi hqi
  · intro x hxp hxq
    have hxA := hpU x hxp
    have hxB := hqU x hxq
    rcases hxA with hxA | hxA
    · rcases hxB with hxB | hxB
      · exact (Set.disjoint_left.mp hdis hxA hxB).elim
      · simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hxB
    · simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hxA
  · intro x hx y hy hxa hxb hya hyb
    apply hcross x _ y _
    · exact (hpU x hx).resolve_right (by simpa using And.intro hxa hxb)
    · exact (hqU y hy).resolve_right (by simpa using And.intro hya hyb)

lemma ReachIn.pair_adj {G : SimpleGraph V} {a b : V} (hab : a ≠ b)
    (h : ReachIn G {a,b} a b) : G.Adj a b := by
  obtain ⟨p,hp⟩ := h
  cases p with
  | nil => exact (hab rfl).elim
  | @cons _ c _ hac p =>
    have hc := hp c (by simp)
    rcases Set.mem_insert_iff.mp hc with hc | hc
    · subst c
      exact (hac.ne rfl).elim
    · have hc' : c = b := Set.mem_singleton_iff.mp hc
      simpa only [hc'] using hac

lemma ReachIn.in_component [DecidableEq V] {G : SimpleGraph V} {U : Set V} {a b : V}
    (h : ReachIn G U a b) : ReachIn G {x | ReachIn G U a x} a b := by
  obtain ⟨p,hp⟩ := h
  refine ⟨p,?_⟩
  intro x hx
  refine ⟨p.takeUntil x hx,?_⟩
  exact fun y hy => hp y (Walk.support_takeUntil_subset _ _ hy)

lemma ReachIn.through_connected {G : SimpleGraph V} {A : Set V}
    (hconn : ∀ x ∈ A, ∀ y ∈ A, ReachIn G A x y) {s t : V}
    (hs : ∃ x ∈ A, G.Adj s x) (ht : ∃ x ∈ A, G.Adj t x) :
    ReachIn G (A ∪ {s,t}) s t := by
  obtain ⟨x,hx,hsx⟩ := hs
  obtain ⟨y,hy,hty⟩ := ht
  have h1 := ReachIn.of_adj hsx (show s ∈ A ∪ {s,t} by simp) (Or.inl hx)
  have h2 := (hconn x hx y hy).mono (Set.subset_union_left : A ⊆ A ∪ {s,t})
  have h3 := ReachIn.of_adj hty.symm (Or.inl hy) (show t ∈ A ∪ {s,t} by simp)
  exact (h1.trans h2).trans h3

lemma neighbor_of_restored_vertex [DecidableEq V] {G : SimpleGraph V}
    (U S : Finset V) {a b s : V} (ha : a ∈ U \ S)
    (hnot : ¬ ReachIn G (U \ S : Finset V) a b)
    (hrest : ReachIn G (U \ S.erase s : Finset V) a b) :
    ∃ x, ReachIn G (U \ S : Finset V) a x ∧ G.Adj s x := by
  obtain ⟨p,hp⟩ := hrest
  let A : Set V := {x | ReachIn G (U \ S : Finset V) a x}
  have haA : a ∈ A := ReachIn.refl ha
  obtain ⟨d,hd,hdA,hdnA⟩ := p.exists_boundary_dart A haA hnot
  have hdU := hp d.snd (p.dart_snd_mem_support_of_mem_darts hd)
  have hds : d.snd = s := by
    by_contra hn
    have hdW : d.snd ∈ U \ S := by
      obtain ⟨hdU,hdS⟩ := Finset.mem_sdiff.mp hdU
      refine Finset.mem_sdiff.mpr ⟨hdU,?_⟩
      intro hs
      exact hdS (Finset.mem_erase.mpr ⟨hn,hs⟩)
    apply hdnA
    exact hdA.trans (ReachIn.of_adj d.adj hdA.right_mem hdW)
  refine ⟨d.fst,hdA,?_⟩
  simpa only [hds] using d.adj.symm

lemma two_neighbors_exhaust [Fintype V] {G : SimpleGraph V}
    (hdeg : ∀ v, G.degree v ≤ 2) {x a b : V} (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) {y : V} (hxy : G.Adj x y) : y = a ∨ y = b := by
  classical
  by_contra hn
  have hya : y ≠ a := fun h => hn (Or.inl h)
  have hyb : y ≠ b := fun h => hn (Or.inr h)
  have hsub : ({a,b,y} : Finset V) ⊆ G.neighborFinset x := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  have ht : ({a,b,y} : Finset V).card = 3 := by simp [hab,hya.symm,hyb.symm]
  have hd := hdeg x
  rw [ht,G.card_neighborFinset_eq_degree] at hc
  omega

lemma connected_degree_two_triangle_complete [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    G.IsClique Set.univ := by
  classical
  let S : Set V := {a,b,c}
  have hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S := by
    intro x hx y hxy
    simp only [S,Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · exact (two_neighbors_exhaust hdeg hbc.ne hab hca.symm hxy).elim
        (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
    · exact (two_neighbors_exhaust hdeg hca.ne.symm hab.symm hbc hxy).elim
        Or.inl (fun h => Or.inr (Or.inr h))
    · exact (two_neighbors_exhaust hdeg hab.ne hca hbc.symm hxy).elim
        Or.inl (fun h => Or.inr (Or.inl h))
  have hfull : ∀ x, x ∈ S := by
    intro x
    by_contra hx
    obtain ⟨p⟩ := hconn a x
    obtain ⟨d,_,hd,hnd⟩ := p.exists_boundary_dart S (by simp [S]) hx
    exact hnd (hclosed d.fst hd d.snd d.adj)
  intro x _ y _ hxy
  have hx := hfull x
  have hy := hfull y
  simp only [S,Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first | exact (hxy rfl).elim | exact hab | exact hab.symm | exact hbc | exact hbc.symm | exact hca | exact hca.symm

lemma induced_cycle_triangle_complete [Fintype V] {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) (hpi : InducedWalk p)
    {x y z : V} (hx : x ∈ p.support) (hy : y ∈ p.support) (hz : z ∈ p.support)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) :
    G.IsClique {v | v ∈ p.support} := by
  have hreg := cycle_coe_regular G hp
  let x' : p.toSubgraph.verts := ⟨x,p.mem_verts_toSubgraph.mpr hx⟩
  let y' : p.toSubgraph.verts := ⟨y,p.mem_verts_toSubgraph.mpr hy⟩
  let z' : p.toSubgraph.verts := ⟨z,p.mem_verts_toSubgraph.mpr hz⟩
  have hxy' : p.toSubgraph.coe.Adj x' y' := p.mem_edges_toSubgraph.mpr (hpi x hx y hy hxy)
  have hyz' : p.toSubgraph.coe.Adj y' z' := p.mem_edges_toSubgraph.mpr (hpi y hy z hz hyz)
  have hzx' : p.toSubgraph.coe.Adj z' x' := p.mem_edges_toSubgraph.mpr (hpi z hz x hx hzx)
  have hdeg : ∀ v, p.toSubgraph.coe.degree v ≤ 2 := by
    intro v
    have hv := hreg.2 v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hv ⊢
    omega
  have hcomp := connected_degree_two_triangle_complete hreg.1
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hcomp hdeg
  have hcomp := hcomp hdeg hxy' hyz' hzx'
  intro u hu v hv huv
  let u' : p.toSubgraph.verts := ⟨u,p.mem_verts_toSubgraph.mpr hu⟩
  let v' : p.toSubgraph.verts := ⟨v,p.mem_verts_toSubgraph.mpr hv⟩
  exact p.toSubgraph.adj_sub (hcomp (show u' ∈ Set.univ from Set.mem_univ _)
    (show v' ∈ Set.univ from Set.mem_univ _) (fun h => huv (congrArg Subtype.val h)))

/-- A strong Berge cycle, represented by its cyclic sequence of vertices and
by a piece for each cycle edge. Each selected piece contains exactly the two
endpoints of that edge among the selected vertices. -/
def IncidenceCycle (E : I → Finset V) : Prop :=
  ∃ a, ∃ p : (primal E).Walk a a, p.IsCycle ∧
    ∃ label : {e : Sym2 V // e ∈ p.edges} → I,
      ∀ e x, x ∈ p.support → (x ∈ E (label e) ↔ x ∈ e.val)

/-- The incidence condition automatically makes the selected pieces distinct. -/
lemma incidence_label_injective {E : I → Finset V} {a : V}
    (p : (primal E).Walk a a) (label : {e : Sym2 V // e ∈ p.edges} → I)
    (hl : ∀ e x, x ∈ p.support → (x ∈ E (label e) ↔ x ∈ e.val)) :
    Function.Injective label := by
  intro e f hef
  apply Subtype.ext
  apply Sym2.ext
  intro x
  constructor
  · intro hx
    have hxp := Walk.mem_support_of_mem_edges e.property hx
    apply (hl f x hxp).mp
    rw [← hef]
    exact (hl e x hxp).mpr hx
  · intro hx
    have hxp := Walk.mem_support_of_mem_edges f.property hx
    apply (hl e x hxp).mp
    rw [hef]
    exact (hl f x hxp).mpr hx

set_option linter.unusedSimpArgs false in
lemma IncidenceTriangle.incidenceCycle (E : I → Finset V)
    (h : IncidenceTriangle E) : IncidenceCycle E := by
  classical
  obtain ⟨i,j,k,x,y,z,hxi,hyi,hzni,hyj,hzj,hxnj,hzk,hxk,hynk⟩ := h
  have hxy : x ≠ y := by rintro rfl; exact hxnj hyj
  have hyz : y ≠ z := by rintro rfl; exact hzni hyi
  have hzx : z ≠ x := by rintro rfl; exact hzni hxi
  have hyx := hxy.symm
  have hzy := hyz.symm
  have hxz := hzx.symm
  have ha : (primal E).Adj x y := ⟨hxy,i,hxi,hyi⟩
  have hb : (primal E).Adj y z := ⟨hyz,j,hyj,hzj⟩
  have hc : (primal E).Adj z x := ⟨hzx,k,hzk,hxk⟩
  let p : (primal E).Walk x x := .cons ha (.cons hb (.cons hc .nil))
  have hp : p.IsCycle := by
    dsimp only [p]
    rw [Walk.cons_isCycle_iff]
    simp [Walk.isPath_def,hxy,hyz,hzx,hxy.symm,hzx.symm]
  let label : {e : Sym2 V // e ∈ p.edges} → I := fun e =>
    if e.val = s(x,y) then i else if e.val = s(y,z) then j else k
  refine ⟨x,p,hp,label,?_⟩
  rintro ⟨e,he⟩ w hw
  simp only [p,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [p,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases he with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl
  all_goals simp_all [label,Sym2.eq_iff,Sym2.mem_iff]

lemma no_incidenceCycle_subfamily (E : I → Finset V) (hno : ¬ IncidenceCycle E)
    (A : Finset I) : ¬ IncidenceCycle (fun i : A => E i.val) := by
  rintro ⟨a,p,hp,label,hl⟩
  have hle : primal (fun i : A => E i.val) ≤ primal E := by
    rintro x y ⟨hxy,i,hx,hy⟩
    exact ⟨hxy,i.val,hx,hy⟩
  let q := p.mapLe hle
  have heq : q.edges = p.edges := Walk.edges_mapLe_eq_edges _ _
  let label' : {e : Sym2 V // e ∈ q.edges} → I :=
    fun e => (label ⟨e.val,heq ▸ e.property⟩).val
  apply hno
  refine ⟨a,q,hp.mapLe hle,label',?_⟩
  intro e x hx
  apply hl ⟨e.val,heq ▸ e.property⟩ x
  simpa only [q,Walk.support_mapLe_eq_support] using hx

lemma incidenceCycle_of_induced_nonclique [Fintype V] (E : I → Finset V)
    {a : V} (p : (primal E).Walk a a) (hp : p.IsCycle) (hpi : InducedWalk p)
    (hnot : ¬ (primal E).IsClique {x | x ∈ p.support}) : IncidenceCycle E := by
  classical
  have covers (e : {e : Sym2 V // e ∈ p.edges}) : ∃ i, ∀ x ∈ e.val, x ∈ E i := by
    obtain ⟨e,he⟩ := e
    induction e using Sym2.ind with | h x y =>
      obtain ⟨i,hxi,hyi⟩ := (p.adj_of_mem_edges he).2
      refine ⟨i,?_⟩
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact hxi
      · exact hyi
  choose label hl using covers
  refine ⟨a,p,hp,label,?_⟩
  intro e x hx
  refine ⟨?_,hl e x⟩
  intro hxi
  by_contra hxe
  obtain ⟨e,he⟩ := e
  induction e using Sym2.ind with | h y z =>
    have hy : y ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hz : z ∈ p.support := p.snd_mem_support_of_mem_edges he
    have hyi := hl ⟨s(y,z),he⟩ y (by simp)
    have hzi := hl ⟨s(y,z),he⟩ z (by simp)
    have hxy : x ≠ y := by intro h; apply hxe; simp [h]
    have hxz : x ≠ z := by intro h; apply hxe; simp [h]
    have hadjxy : (primal E).Adj x y := ⟨hxy,label ⟨s(y,z),he⟩,hxi,hyi⟩
    have hadjzx : (primal E).Adj z x := ⟨hxz.symm,label ⟨s(y,z),he⟩,hzi,hxi⟩
    exact hnot (induced_cycle_triangle_complete p hp hpi hx hy hz hadjxy (p.adj_of_mem_edges he) hadjzx)

lemma primal_chordal_of_no_incidenceCycle [Fintype V] (E : I → Finset V)
    (hno : ¬ IncidenceCycle E) : Chordal (primal E) := by
  intro a p hp hpi
  by_contra hn
  exact hno (incidenceCycle_of_induced_nonclique E p hp hpi hn)

/-- A vertex is simplicial in the subgraph induced on `U`. -/
def SimplicialOn (G : SimpleGraph V) (U : Finset V) (v : V) : Prop :=
  G.IsClique {x | x ∈ U ∧ G.Adj v x}

/-- The clique-separator characterization used in the finite elimination argument. -/
def CliqueCutProperty [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ U : Finset V, ¬ G.IsClique U →
    ∃ A B : Finset V,
      A ∪ B = U ∧ (A \ B).Nonempty ∧ (B \ A).Nonempty ∧
      G.IsClique (↑(A ∩ B) : Set V) ∧
      ∀ a ∈ A \ B, ∀ b ∈ B \ A, ¬ G.Adj a b

lemma Chordal.cliqueCutProperty [DecidableEq V] {G : SimpleGraph V}
    (hch : Chordal G) : CliqueCutProperty G := by
  intro U hU
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩,hab,hnadj⟩ := G.not_isClique_iff.mp hU
  have hne : a ≠ b := fun h => hab (Subtype.ext h)
  let P : Finset V → Prop := fun S =>
    S ⊆ U ∧ a ∉ S ∧ b ∉ S ∧ ¬ ReachIn G (U \ S : Finset V) a b
  have hP : P (U \ {a,b}) := by
    refine ⟨Finset.sdiff_subset,by simp,by simp,?_⟩
    intro hr
    apply hnadj
    apply ReachIn.pair_adj hne
    apply hr.mono
    intro x hx
    obtain ⟨hxU,hxS⟩ := Finset.mem_sdiff.mp hx
    by_contra hn
    apply hxS
    exact Finset.mem_sdiff.mpr ⟨hxU,by simpa using hn⟩
  obtain ⟨S,hS,hmin⟩ := exists_minimalFor_of_wellFoundedLT P Finset.card ⟨U \ {a,b},hP⟩
  obtain ⟨hSU,haS,hbS,hnot⟩ := hS
  have haW : a ∈ U \ S := Finset.mem_sdiff.mpr ⟨ha,haS⟩
  have hbW : b ∈ U \ S := Finset.mem_sdiff.mpr ⟨hb,hbS⟩
  have hrestore (s : V) (hs : s ∈ S) : ReachIn G (U \ S.erase s : Finset V) a b := by
    by_contra hr
    have ht : P (S.erase s) := ⟨(Finset.erase_subset _ _).trans hSU,
      (fun h => haS (Finset.mem_of_mem_erase h)),
      (fun h => hbS (Finset.mem_of_mem_erase h)),hr⟩
    have hlt := Finset.card_erase_lt_of_mem hs
    have hm := hmin ht hlt.le
    omega
  let A : Set V := {x | ReachIn G (U \ S : Finset V) a x}
  let B : Set V := {x | ReachIn G (U \ S : Finset V) b x}
  have haA : a ∈ A := ReachIn.refl haW
  have hbB : b ∈ B := ReachIn.refl hbW
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact hnot (hxA.trans hxB.symm)
  have hcrossAB : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
    intro x hx y hy hxy
    have hxy' := ReachIn.of_adj hxy hx.right_mem hy.right_mem
    exact hnot ((hx.trans hxy').trans hy.symm)
  have hAconn : ∀ x ∈ A, ∀ y ∈ A, ReachIn G A x y := by
    intro x hx y hy
    exact hx.in_component.symm.trans hy.in_component
  have hBconn : ∀ x ∈ B, ∀ y ∈ B, ReachIn G B x y := by
    intro x hx y hy
    exact hx.in_component.symm.trans hy.in_component
  have hnA (s : V) (hs : s ∈ S) : ∃ x ∈ A, G.Adj s x :=
    neighbor_of_restored_vertex U S haW hnot (hrestore s hs)
  have hnB (s : V) (hs : s ∈ S) : ∃ x ∈ B, G.Adj s x :=
    neighbor_of_restored_vertex U S hbW (fun h => hnot h.symm) (hrestore s hs).symm
  have hScl : G.IsClique S := by
    intro s hs t ht hst
    exact hch.adj_of_separated_paths A B hAB hcrossAB hst
      (ReachIn.through_connected hAconn (hnA s hs) (hnA t ht))
      (ReachIn.through_connected hBconn (hnB s hs) (hnB t ht))
  let F : Finset V := U.filter (fun x => x ∈ A)
  have hFU : F ⊆ U := Finset.filter_subset _ _
  have hFS : Disjoint F S := by
    apply Finset.disjoint_left.mpr
    intro x hx hs
    have hxA := (Finset.mem_filter.mp hx).2
    exact (Finset.mem_sdiff.mp hxA.right_mem).2 hs
  have haF : a ∈ F := Finset.mem_filter.mpr ⟨ha,haA⟩
  have hbF : b ∉ F := fun h => hnot (Finset.mem_filter.mp h).2
  refine ⟨F ∪ S,U \ F,?_,?_,?_,?_,?_⟩
  · ext x
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro ((hx | hx) | hx)
      · exact hFU hx
      · exact hSU hx
      · exact hx.1
    · intro hx
      by_cases hxF : x ∈ F
      · exact Or.inl (Or.inl hxF)
      · exact Or.inr ⟨hx,hxF⟩
  · exact ⟨a,Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ haF,
      fun h => (Finset.mem_sdiff.mp h).2 haF⟩⟩
  · exact ⟨b,Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hb,hbF⟩,
      fun h => (Finset.mem_union.mp h).elim hbF hbS⟩⟩
  · apply hScl.subset
    intro x hx
    obtain ⟨hxL,hxR⟩ := Finset.mem_inter.mp hx
    exact (Finset.mem_union.mp hxL).resolve_left (Finset.mem_sdiff.mp hxR).2
  · intro x hx y hy hxy
    obtain ⟨hxL,hxnR⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyR,hynL⟩ := Finset.mem_sdiff.mp hy
    have hxU : x ∈ U := (Finset.mem_union.mp hxL).elim (fun h => hFU h) (fun h => hSU h)
    have hxF : x ∈ F := by
      by_contra hn
      exact hxnR (Finset.mem_sdiff.mpr ⟨hxU,hn⟩)
    have hxA := (Finset.mem_filter.mp hxF).2
    have hyW : y ∈ U \ S := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hyR).1,
      fun h => hynL (Finset.mem_union_right _ h)⟩
    have hyA := hxA.trans (ReachIn.of_adj hxy hxA.right_mem hyW)
    exact (Finset.mem_sdiff.mp hyR).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hyW).1,hyA⟩)

lemma simplicialOn_of_clique (G : SimpleGraph V) (U : Finset V)
    (hU : G.IsClique U) (v : V) : SimplicialOn G U v :=
  hU.subset (fun _ h => h.1)

lemma simplicialOn_extend [DecidableEq V] {G : SimpleGraph V}
    {A B U : Finset V} (hU : A ∪ B = U)
    (hcross : ∀ a ∈ A \ B, ∀ b ∈ B \ A, ¬ G.Adj a b)
    {v : V} (hv : v ∈ A \ B) (hvA : SimplicialOn G A v) : SimplicialOn G U v := by
  have hn (x : V) (hx : x ∈ U) (hvx : G.Adj v x) : x ∈ A := by
    rw [← hU] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hx
    · by_contra hnx
      exact hcross v hv x (Finset.mem_sdiff.mpr ⟨hx,hnx⟩) hvx
  intro x hx y hy hxy
  exact hvA ⟨hn x hx.1 hx.2,hx.2⟩ ⟨hn y hy.1 hy.2,hy.2⟩ hxy

/-- Dirac's separator induction, in the form that avoids any prescribed clique. -/
lemma CliqueCutProperty.exists_simplicial_outside [DecidableEq V]
    {G : SimpleGraph V} (hcut : CliqueCutProperty G)
    (U K : Finset V) (hKU : K ⊆ U) (hK : G.IsClique K) (hUK : (U \ K).Nonempty) :
    ∃ v ∈ U \ K, SimplicialOn G U v := by
  have main : ∀ n : ℕ, ∀ U K : Finset V, U.card = n → K ⊆ U →
      G.IsClique K → (U \ K).Nonempty → ∃ v ∈ U \ K, SimplicialOn G U v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U K hn hKU hK hUK
      by_cases hUcl : G.IsClique U
      · obtain ⟨v,hv⟩ := hUK
        exact ⟨v,hv,simplicialOn_of_clique G U hUcl v⟩
      obtain ⟨A,B,hAB,hA,hB,hS,hcross⟩ := hcut U hUcl
      have hAU : A ⊆ U := hAB ▸ Finset.subset_union_left
      have hBU : B ⊆ U := hAB ▸ Finset.subset_union_right
      have hAc : A.card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hAU,?_⟩
        intro he
        obtain ⟨b,hb⟩ := hB
        exact (Finset.mem_sdiff.mp hb).2 (he.symm ▸ hBU (Finset.mem_sdiff.mp hb).1)
      have hBc : B.card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hBU,?_⟩
        intro he
        obtain ⟨a,ha⟩ := hA
        exact (Finset.mem_sdiff.mp ha).2 (he.symm ▸ hAU (Finset.mem_sdiff.mp ha).1)
      have hAS : (A \ (A ∩ B)).Nonempty := by simpa using hA
      have hBS : (B \ (A ∩ B)).Nonempty := by simpa [Finset.inter_comm] using hB
      obtain ⟨a,ha,has⟩ := ih A.card hAc A (A ∩ B) rfl Finset.inter_subset_left hS hAS
      obtain ⟨b,hb,hbs⟩ := ih B.card hBc B (A ∩ B) rfl Finset.inter_subset_right hS hBS
      have ha' : a ∈ A \ B := by simpa using ha
      have hb' : b ∈ B \ A := by simpa [Finset.inter_comm] using hb
      have hau : a ∈ U := hAU (Finset.mem_sdiff.mp ha').1
      have hbu : b ∈ U := hBU (Finset.mem_sdiff.mp hb').1
      have hane : a ≠ b := by
        intro he
        exact (Finset.mem_sdiff.mp ha').2 (he.symm ▸ (Finset.mem_sdiff.mp hb').1)
      have haS : SimplicialOn G U a := simplicialOn_extend hAB hcross ha' has
      have hbS : SimplicialOn G U b := simplicialOn_extend (by simpa [Finset.union_comm] using hAB)
        (fun x hx y hy hxy => hcross y hy x hx hxy.symm) hb' hbs
      by_cases hak : a ∈ K
      · have hbk : b ∉ K := fun hbk => hcross a ha' b hb' (hK hak hbk hane)
        exact ⟨b,Finset.mem_sdiff.mpr ⟨hbu,hbk⟩,hbS⟩
      · exact ⟨a,Finset.mem_sdiff.mpr ⟨hau,hak⟩,haS⟩
  exact main U.card U K rfl hKU hK hUK

lemma CliqueCutProperty.exists_simplicial [DecidableEq V]
    {G : SimpleGraph V} (hcut : CliqueCutProperty G)
    (U : Finset V) (hU : U.Nonempty) : ∃ v ∈ U, SimplicialOn G U v := by
  simpa using hcut.exists_simplicial_outside U ∅ (Finset.empty_subset _) (by simp) (by simpa using hU)

lemma exists_private_vertex [DecidableEq V] [Fintype I] [Nonempty I]
    (E : I → Finset V) (hsize : ∀ i, 3 ≤ (E i).card)
    (hinter : ∀ i j, i ≠ j → (E i ∩ E j).card ≤ 2)
    (hcon : Conformal E) (hcut : CliqueCutProperty (primal E)) :
    ∃ v : V, ∃ i : I, v ∈ E i ∧ ∀ j, v ∈ E j → j = i := by
  let U : Finset V := Finset.univ.biUnion E
  have hEU (i : I) : E i ⊆ U := Finset.subset_biUnion_of_mem E (Finset.mem_univ i)
  have hUsupp (x : V) (hx : x ∈ U) : ∃ i, x ∈ E i := by
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    exact ⟨i,hi⟩
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hEne : (E i₀).Nonempty := Finset.card_pos.mp (by have := hsize i₀; omega)
  have hUne : U.Nonempty := hEne.mono (hEU i₀)
  obtain ⟨v,hv,hvs⟩ := hcut.exists_simplicial U hUne
  let T : Finset V := insert v (U.filter ((primal E).Adj v))
  have hTU : T ⊆ U := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv
    · exact (Finset.mem_filter.mp hx).1
  have hTcl : (primal E).IsClique T := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have hy' := Finset.mem_of_mem_insert_of_ne hy hxy.symm
      exact (Finset.mem_filter.mp hy').2
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact (Finset.mem_filter.mp hx).2.symm
    · exact hvs (Finset.mem_filter.mp hx) (Finset.mem_filter.mp hy) hxy
  obtain ⟨i,hi⟩ := hcon T (Finset.insert_nonempty _ _) (fun x hx => hUsupp x (hTU hx)) hTcl
  have hvi : v ∈ E i := hi (Finset.mem_insert_self _ _)
  refine ⟨v,i,hvi,?_⟩
  intro j hvj
  have hji : E j ⊆ E i := by
    intro x hx
    apply hi
    by_cases hxv : x = v
    · exact Finset.mem_insert.mpr (Or.inl hxv)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨hEU j hx,⟨(fun he => hxv he.symm),j,hvj,hx⟩⟩))
  by_contra hne
  have hb := hinter j i hne
  rw [Finset.inter_eq_left.mpr hji] at hb
  have hs := hsize j
  omega

lemma no_incidenceTriangle_subfamily (E : I → Finset V) (hno : ¬ IncidenceTriangle E)
    (A : Finset I) : ¬ IncidenceTriangle (fun i : A => E i.val) := by
  rintro ⟨i,j,k,x,y,z,h⟩
  exact hno ⟨i.val,j.val,k.val,x,y,z,h⟩

/-- The counting step is a finite induction: a private vertex is charged to
its unique piece and disappears from the remaining union. -/
lemma card_le_union_of_private_vertices [DecidableEq V] [DecidableEq I]
    (E : I → Finset V) (D : Finset I)
    (hprivate : ∀ A ⊆ D, A.Nonempty →
      ∃ i ∈ A, ∃ v ∈ E i, ∀ j ∈ A, v ∈ E j → j = i) :
    D.card ≤ (D.biUnion E).card := by
  have general : ∀ n : ℕ, ∀ A : Finset I, A.card = n →
      (∀ B ⊆ A, B.Nonempty →
        ∃ j ∈ B, ∃ v ∈ E j, ∀ k ∈ B, v ∈ E k → k = j) →
      A.card ≤ (A.biUnion E).card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      intro A hn hp
      by_cases hA : A.Nonempty
      · obtain ⟨j,hj,v,hv,hu⟩ := hp A (Finset.Subset.refl _) hA
        have hc : (A.erase j).card < n := (Finset.card_erase_lt_of_mem hj).trans_eq hn
        have hb := ihn _ hc (A.erase j) rfl (fun B hBA hB => hp B
          (hBA.trans (Finset.erase_subset _ _)) hB)
        have hvU : v ∈ A.biUnion E := Finset.mem_biUnion.mpr ⟨j,hj,hv⟩
        have hsub : (A.erase j).biUnion E ⊆ (A.biUnion E).erase v := by
          intro x hx
          obtain ⟨k,hk,hxk⟩ := Finset.mem_biUnion.mp hx
          have hkA := (Finset.mem_erase.mp hk).2
          have hxv : x ≠ v := by
            rintro rfl
            exact (Finset.mem_erase.mp hk).1 (hu k hkA hxk)
          exact Finset.mem_erase.mpr ⟨hxv,Finset.mem_biUnion.mpr ⟨k,hkA,hxk⟩⟩
        have hle := Finset.card_le_card hsub
        have hca := Finset.card_erase_add_one hj
        have hcu := Finset.card_erase_add_one hvU
        omega
      · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
        simp [hAe]
  exact general _ _ rfl hprivate

/-- No incidence triangles supply conformality. The remaining chordality
hypothesis is kept explicit here for every subfamily. -/
lemma card_le_union_of_hereditary_clique_cuts [DecidableEq V] [DecidableEq I]
    (E : I → Finset V) (D : Finset I)
    (hsize : ∀ i ∈ D, 3 ≤ (E i).card)
    (hinter : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → (E i ∩ E j).card ≤ 2)
    (hno : ¬ IncidenceTriangle E)
    (hcut : ∀ A ⊆ D, CliqueCutProperty (primal (fun i : A => E i.val))) :
    D.card ≤ (D.biUnion E).card := by
  apply card_le_union_of_private_vertices E D
  intro A hAD hA
  letI : Nonempty A := hA.to_subtype
  obtain ⟨v,i,hvi,hunique⟩ := exists_private_vertex (fun i : A => E i.val)
    (fun i => hsize i.val (hAD i.property))
    (fun i j hij => hinter i.val (hAD i.property) j.val (hAD j.property)
      (fun he => hij (Subtype.ext he)))
    (conformal_of_no_incidenceTriangle _ (no_incidenceTriangle_subfamily E hno A))
    (hcut A hAD)
  refine ⟨i.val,i.property,v,hvi,?_⟩
  intro j hj hvj
  exact congrArg Subtype.val (hunique ⟨j,hj⟩ hvj)

/-- The required finite incidence-counting theorem. No hypothesis about
rigidity or minimality is implicit in this statement. -/
lemma card_le_union_of_no_incidenceCycle [Fintype V] [DecidableEq V] [DecidableEq I]
    (E : I → Finset V) (D : Finset I)
    (hsize : ∀ i ∈ D, 3 ≤ (E i).card)
    (hinter : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → (E i ∩ E j).card ≤ 2)
    (hno : ¬ IncidenceCycle E) : D.card ≤ (D.biUnion E).card := by
  apply card_le_union_of_hereditary_clique_cuts E D hsize hinter
    (fun h => hno (h.incidenceCycle E))
  intro A _
  exact (primal_chordal_of_no_incidenceCycle _ (no_incidenceCycle_subfamily E hno A)).cliqueCutProperty

noncomputable def pieceVertices [Fintype V] {G : SimpleGraph V} (D : Finset G.Subgraph) :
    D → Finset V := fun H => H.val.verts.toFinset

lemma cycle_family_card_le_support [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hinter : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → (H.verts ∩ K.verts).ncard ≤ 2)
    (hno : ¬ IncidenceCycle (pieceVertices D)) : D.card ≤ G.support.ncard := by
  classical
  have hsize (H : D) : 3 ≤ (pieceVertices D H).card := by
    obtain ⟨v⟩ := (hD H.val H.property).1.nonempty
    have hd := H.val.coe.degree_lt_card_verts v
    have hr := (hD H.val H.property).2 v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hr
    simp only [pieceVertices,Set.toFinset_card,← Nat.card_eq_fintype_card]
    omega
  have hpair (H K : D) (hne : H ≠ K) :
      (pieceVertices D H ∩ pieceVertices D K).card ≤ 2 := by
    have hp := hinter H.val H.property K.val K.property (fun h => hne (Subtype.ext h))
    simpa only [pieceVertices,← Set.toFinset_inter,Set.toFinset_card,← Nat.card_eq_fintype_card] using hp
  have hc := card_le_union_of_no_incidenceCycle (pieceVertices D) Finset.univ
    (fun H _ => hsize H) (fun H _ K _ => hpair H K) hno
  have hsub : Finset.univ.biUnion (pieceVertices D) ⊆ G.support.toFinset := by
    intro x hx
    obtain ⟨H,_,hxH⟩ := Finset.mem_biUnion.mp hx
    have hxH : x ∈ H.val.verts := Set.mem_toFinset.mp hxH
    let v : H.val.verts := ⟨x,hxH⟩
    have hr := (hD H.val H.property).2 v
    have hpos : 0 < H.val.coe.degree v := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hr ⊢
      omega
    obtain ⟨y,hxy⟩ := (H.val.coe.degree_pos_iff_exists_adj v).mp hpos
    apply Set.mem_toFinset.mpr
    exact ⟨y.val,H.val.adj_sub hxy⟩
  have hs := Finset.card_le_card hsub
  simp only [Finset.card_univ,Fintype.card_coe] at hc
  simp only [Set.toFinset_card,← Nat.card_eq_fintype_card] at hs
  exact hc.trans hs

lemma rigid_number_bound_of_no_incidenceCycle [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D)
    (hno : ¬ IncidenceCycle (pieceVertices D)) : Critical.number G ≤ G.support.ncard := by
  rw [← hrig D hD hdec]
  apply cycle_family_card_le_support D hD _ hno
  intro H hH K hK hne
  exact hrig.intersection_le_two D hD hdec H K hH hK hne

#print axioms IncidenceTriangle.incidenceCycle
#print axioms no_incidenceCycle_subfamily
#print axioms card_le_union_of_no_incidenceCycle
#print axioms cycle_family_card_le_support
#print axioms rigid_number_bound_of_no_incidenceCycle
#print axioms primal_chordal_of_no_incidenceCycle
#print axioms ReachIn.exists_induced_path
#print axioms Chordal.cliqueCutProperty
#print axioms conformal_of_no_incidenceTriangle
#print axioms CliqueCutProperty.exists_simplicial_outside
#print axioms exists_private_vertex
#print axioms card_le_union_of_hereditary_clique_cuts
end Erdos184Work.ChordalIncidence

/-! Source block: PathSubstitution. -/

/-! Lifting paths and cycles through an internally disjoint family of paths.
This is infrastructure for cycle-junction recombination, not a proof of the conjecture. -/

open SimpleGraph
namespace Erdos184Work.PathSubstitution

variable {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}

structure Model (H : SimpleGraph W) (G : SimpleGraph V) where
  vertex : W → V
  injective : Function.Injective vertex
  path {a b : W} : H.Adj a b → G.Walk (vertex a) (vertex b)
  isPath {a b : W} (h : H.Adj a b) : (path h).IsPath
  vertex_mem {a b : W} (h : H.Adj a b) (x : W) :
    vertex x ∈ (path h).support ↔ x = a ∨ x = b
  edge_disjoint {a b c d : W} (h : H.Adj a b) (h' : H.Adj c d)
    (hne : s(a,b) ≠ s(c,d)) : (path h).edges.Disjoint (path h').edges
  support_inter {a b c d : W} (h : H.Adj a b) (h' : H.Adj c d)
    (hne : s(a,b) ≠ s(c,d)) (x : V) :
    x ∈ (path h).support → x ∈ (path h').support → x = vertex a ∨ x = vertex b

namespace Model
variable (M : Model H G)

def bind (M : Model H G) {a b : W} : H.Walk a b → G.Walk (M.vertex a) (M.vertex b)
  | .nil => .nil
  | .cons h p => (M.path h).append (bind M p)

lemma vertex_mem_bind {a b x : W} (p : H.Walk a b) :
    M.vertex x ∈ (M.bind p).support ↔ x ∈ p.support := by
  induction p with
  | nil => simp [bind,M.injective.eq_iff]
  | @cons a b c h p ih =>
    simp only [bind,Walk.mem_support_append_iff,M.vertex_mem,ih,
      Walk.support_cons,List.mem_cons]
    have hb : b ∈ p.support := p.start_mem_support
    aesop

lemma mem_edges_bind {a b : W} (p : H.Walk a b) (e : Sym2 V) :
    e ∈ (M.bind p).edges ↔ ∃ d ∈ p.darts, e ∈ (M.path d.adj).edges := by
  induction p with
  | nil => simp [bind]
  | @cons a b c h p ih =>
    simp [bind,ih]

lemma path_bind_edges_disjoint {a b c d : W} (h : H.Adj a b) (p : H.Walk c d)
    (hne : s(a,b) ∉ p.edges) : (M.path h).edges.Disjoint (M.bind p).edges := by
  apply List.disjoint_left.mpr
  intro e he hp
  obtain ⟨d,hd,hed⟩ := (M.mem_edges_bind p e).mp hp
  have hdiff : s(a,b) ≠ d.edge := by
    intro heq
    apply hne
    rw [heq]
    exact List.mem_map_of_mem hd
  exact List.disjoint_left.mp (M.edge_disjoint h d.adj hdiff) he hed

lemma path_bind_support_inter {a b c d : W} (h : H.Adj a b) (p : H.Walk c d)
    (hne : s(a,b) ∉ p.edges) (x : V)
    (hx : x ∈ (M.path h).support) (hxp : x ∈ (M.bind p).support) :
    x = M.vertex a ∨ x = M.vertex b := by
  induction p with
  | @nil c =>
    have hxc : x = M.vertex c := by simpa only [bind,Walk.support_nil,List.mem_singleton] using hxp
    rw [hxc] at hx ⊢
    exact ((M.vertex_mem h c).mp hx).imp (congrArg M.vertex) (congrArg M.vertex)
  | @cons c d e h' p ih =>
    simp only [Walk.edges_cons,List.mem_cons,not_or] at hne
    rcases (Walk.mem_support_append_iff _ _).mp hxp with hx' | hxp
    · exact M.support_inter h h' hne.1 x hx hx'
    · exact ih hne.2 hxp

lemma bind_isPath {a b : W} {p : H.Walk a b} (hp : p.IsPath) : (M.bind p).IsPath := by
  induction p with
  | nil => exact Walk.IsPath.nil
  | @cons a b c h p ih =>
    have hp' := Walk.cons_isPath_iff h p |>.mp hp
    apply append_isPath_of_support_inter (M.isPath h) (ih hp'.1)
    intro x hx hxq
    have hne : s(a,b) ∉ p.edges := by
      intro he
      exact hp'.2 (p.fst_mem_support_of_mem_edges he)
    rcases M.path_bind_support_inter h p hne x hx hxq with hx | hx
    · exact (hp'.2 ((M.vertex_mem_bind p).mp (hx ▸ hxq))).elim
    · exact hx

lemma bind_isCycle {a : W} {p : H.Walk a a} (hp : p.IsCycle) : (M.bind p).IsCycle := by
  cases p with
  | nil => exact (hp.not_nil Walk.Nil.nil).elim
  | @cons a b c h p =>
    have hp' := (Walk.cons_isCycle_iff p h).mp hp
    apply append_isCycle_of_support_inter (M.isPath h) (M.bind_isPath hp'.1)
      (fun he => h.ne (M.injective he)) (M.path_bind_edges_disjoint h p hp'.2)
    exact M.path_bind_support_inter h p hp'.2

#print axioms bind_isPath
#print axioms bind_isCycle
end Model

/-- A labelled multigraph whose edges are realized by internally disjoint paths.
The labels allow two different paths to have the same pair of endpoints. -/
structure Family (J W : Type*) (G : SimpleGraph V) where
  vertex : W → V
  injective : Function.Injective vertex
  src : J → W
  dst : J → W
  ne : ∀ j, src j ≠ dst j
  path (j : J) : G.Walk (vertex (src j)) (vertex (dst j))
  isPath : ∀ j, (path j).IsPath
  vertex_mem : ∀ j x, vertex x ∈ (path j).support ↔ x = src j ∨ x = dst j
  edge_disjoint : ∀ i j, i ≠ j → (path i).edges.Disjoint (path j).edges
  support_inter : ∀ i j, i ≠ j → ∀ x,
    x ∈ (path i).support → x ∈ (path j).support → x = vertex (src i) ∨ x = vertex (dst i)

namespace Family
variable {J : Type*} (F : Family J W G)

lemma endpoint_of_src {j : J} {a b : W} (he : s(F.src j,F.dst j) = s(a,b))
    (ha : F.src j = a) : F.dst j = b := by
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact h2
  · exact h2.trans (ha.symm.trans h1)

lemma endpoints_of_not_src {j : J} {a b : W} (he : s(F.src j,F.dst j) = s(a,b))
    (ha : F.src j ≠ a) : F.dst j = a ∧ F.src j = b := by
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact (ha h1).elim
  · exact ⟨h2,h1⟩

noncomputable def oriented (j : J) (a b : W) (he : s(F.src j,F.dst j) = s(a,b)) :
    G.Walk (F.vertex a) (F.vertex b) := by
  classical
  exact if ha : F.src j = a then
    (F.path j).copy (congrArg F.vertex ha) (congrArg F.vertex (F.endpoint_of_src he ha))
  else
    (F.path j).reverse.copy (congrArg F.vertex (F.endpoints_of_not_src he ha).1)
      (congrArg F.vertex (F.endpoints_of_not_src he ha).2)

lemma oriented_isPath (j : J) (a b : W) (he : s(F.src j,F.dst j) = s(a,b)) :
    (F.oriented j a b he).IsPath := by
  classical
  unfold oriented
  split_ifs <;> simp only [Walk.isPath_copy]
  · exact F.isPath j
  · exact (F.isPath j).reverse

lemma mem_oriented_support (j : J) (a b : W) (he : s(F.src j,F.dst j) = s(a,b)) (x : V) :
    x ∈ (F.oriented j a b he).support ↔ x ∈ (F.path j).support := by
  classical
  unfold oriented
  split_ifs <;> simp

lemma mem_oriented_edges (j : J) (a b : W) (he : s(F.src j,F.dst j) = s(a,b)) (e : Sym2 V) :
    e ∈ (F.oriented j a b he).edges ↔ e ∈ (F.path j).edges := by
  classical
  unfold oriented
  split_ifs <;> simp

noncomputable def model (H : SimpleGraph W) (route : H.Dart → J)
    (ends : ∀ d, s(F.src (route d),F.dst (route d)) = d.edge) : Model H G where
  vertex := F.vertex
  injective := F.injective
  path {a b} h := F.oriented (route ⟨(a,b),h⟩) a b (ends _)
  isPath h := F.oriented_isPath _ _ _ _
  vertex_mem {a b} h x := by
    rw [F.mem_oriented_support,F.vertex_mem]
    have he := congrArg (fun e : Sym2 W => x ∈ e) (ends ⟨(a,b),h⟩)
    simpa only [Dart.edge,Sym2.mem_iff] using iff_of_eq he
  edge_disjoint {a b c d} h h' hne := by
    have hr : route ⟨(a,b),h⟩ ≠ route ⟨(c,d),h'⟩ := by
      intro he
      apply hne
      exact (ends ⟨(a,b),h⟩).symm.trans ((congrArg (fun j => s(F.src j,F.dst j)) he).trans (ends ⟨(c,d),h'⟩))
    apply List.disjoint_left.mpr
    intro e he1 he2
    exact List.disjoint_left.mp (F.edge_disjoint _ _ hr)
      ((F.mem_oriented_edges _ _ _ _ _).mp he1) ((F.mem_oriented_edges _ _ _ _ _).mp he2)
  support_inter {a b c d} h h' hne x hx hx' := by
    have hr : route ⟨(a,b),h⟩ ≠ route ⟨(c,d),h'⟩ := by
      intro he
      apply hne
      exact (ends ⟨(a,b),h⟩).symm.trans ((congrArg (fun j => s(F.src j,F.dst j)) he).trans (ends ⟨(c,d),h'⟩))
    have hm := F.support_inter _ _ hr x ((F.mem_oriented_support _ _ _ _ _).mp hx)
      ((F.mem_oriented_support _ _ _ _ _).mp hx')
    rcases Sym2.eq_iff.mp (ends ⟨(a,b),h⟩) with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · simpa only [h1,h2] using hm
    · simpa only [h1,h2,or_comm] using hm

lemma mem_model_bind_edges (H : SimpleGraph W) (route : H.Dart → J)
    (ends : ∀ d, s(F.src (route d),F.dst (route d)) = d.edge)
    {a b : W} (p : H.Walk a b) (e : Sym2 V) :
    e ∈ ((F.model H route ends).bind p).edges ↔
      ∃ j ∈ p.darts.map route, e ∈ (F.path j).edges := by
  rw [Model.mem_edges_bind]
  simp only [model,F.mem_oriented_edges,List.mem_map]
  constructor
  · rintro ⟨d,hd,he⟩
    exact ⟨route d,⟨d,hd,rfl⟩,he⟩
  · rintro ⟨j,⟨d,hd,rfl⟩,he⟩
    exact ⟨d,hd,he⟩

lemma model_binds_disjoint (H₁ H₂ : SimpleGraph W) (r₁ : H₁.Dart → J) (r₂ : H₂.Dart → J)
    (he₁ : ∀ d, s(F.src (r₁ d),F.dst (r₁ d)) = d.edge)
    (he₂ : ∀ d, s(F.src (r₂ d),F.dst (r₂ d)) = d.edge)
    {a b c d : W} (p : H₁.Walk a b) (q : H₂.Walk c d)
    (hdis : (p.darts.map r₁).Disjoint (q.darts.map r₂)) :
    ((F.model H₁ r₁ he₁).bind p).edges.Disjoint ((F.model H₂ r₂ he₂).bind q).edges := by
  apply List.disjoint_left.mpr
  intro e hep heq
  obtain ⟨i,hi,hei⟩ := (F.mem_model_bind_edges _ _ _ _ _).mp hep
  obtain ⟨j,hj,hej⟩ := (F.mem_model_bind_edges _ _ _ _ _).mp heq
  have hij : i ≠ j := by rintro rfl; exact List.disjoint_left.mp hdis hi hj
  exact List.disjoint_left.mp (F.edge_disjoint i j hij) hei hej

lemma number_le_two_lifted_cycles [Fintype V]
    (H₁ H₂ : SimpleGraph W) (r₁ : H₁.Dart → J) (r₂ : H₂.Dart → J)
    (he₁ : ∀ d, s(F.src (r₁ d),F.dst (r₁ d)) = d.edge)
    (he₂ : ∀ d, s(F.src (r₂ d),F.dst (r₂ d)) = d.edge)
    {a b : W} (p : H₁.Walk a a) (q : H₂.Walk b b) (hp : p.IsCycle) (hq : q.IsCycle)
    (hdis : (p.darts.map r₁).Disjoint (q.darts.map r₂))
    (hroutes : ∀ j, j ∈ p.darts.map r₁ ∨ j ∈ q.darts.map r₂)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply LocalObstruction.number_le_two_cycles
    ((F.model H₁ r₁ he₁).bind p) ((F.model H₂ r₂ he₂).bind q)
    ((F.model H₁ r₁ he₁).bind_isCycle hp) ((F.model H₂ r₂ he₂).bind_isCycle hq)
    (F.model_binds_disjoint H₁ H₂ r₁ r₂ he₁ he₂ p q hdis)
  intro x y
  constructor
  · intro hxy
    obtain ⟨j,hj⟩ := hcover x y hxy
    rcases hroutes j with hr | hr
    · exact Or.inl ((F.mem_model_bind_edges _ _ _ _ _).mpr ⟨j,hr,hj⟩)
    · exact Or.inr ((F.mem_model_bind_edges _ _ _ _ _).mpr ⟨j,hr,hj⟩)
  · rintro (he | he)
    · exact Walk.adj_of_mem_edges _ he
    · exact Walk.adj_of_mem_edges _ he

#print axioms number_le_two_lifted_cycles
#print axioms model
#print axioms model_binds_disjoint
end Family
end Erdos184Work.PathSubstitution

/-! Source block: ThreeCycleKernels. -/

/-! Two-cycle decompositions of the four alternating three-cycle junction kernels,
including arbitrary internally disjoint path replacements. -/

open SimpleGraph
namespace Erdos184Work.ThreeCycleKernels
open PathSubstitution
namespace DoubleTriangle
def src : Fin 6 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 2
def dst : Fin 6 → Fin 3
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | 4 => 2
  | 5 => 1

def redEdges : Finset (Sym2 (Fin 3)) :=
  {s(0,1), s(1,2), s(2,0)}
def redGraph : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 6 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,2) then 4 else 3
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 :=
  .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 2 by decide) (.cons (show redGraph.Adj 2 0 by decide) (.nil)))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 3)) :=
  {s(0,1), s(1,2), s(2,0)}
def blueGraph : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 6 :=
  if d.edge = s(0,1) then 1 else
  if d.edge = s(1,2) then 5 else 2
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 :=
  .cons (show blueGraph.Adj 0 1 by decide) (.cons (show blueGraph.Adj 1 2 by decide) (.cons (show blueGraph.Adj 2 0 by decide) (.nil)))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 6) (Fin 3) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end DoubleTriangle

namespace MatchedFour
def src : Fin 8 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 0
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | 7 => 3
def dst : Fin 8 → Fin 4
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 3
  | 5 => 0
  | 6 => 3
  | 7 => 2

def redEdges : Finset (Sym2 (Fin 4)) :=
  {s(0,1), s(1,2), s(2,3), s(3,0)}
def redGraph : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 8 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,2) then 1 else
  if d.edge = s(2,3) then 6 else 5
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 :=
  .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 2 by decide) (.cons (show redGraph.Adj 2 3 by decide) (.cons (show redGraph.Adj 3 0 by decide) (.nil))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 4)) :=
  {s(0,1), s(1,3), s(3,2), s(2,0)}
def blueGraph : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 8 :=
  if d.edge = s(0,1) then 3 else
  if d.edge = s(1,3) then 4 else
  if d.edge = s(3,2) then 7 else 2
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 :=
  .cons (show blueGraph.Adj 0 1 by decide) (.cons (show blueGraph.Adj 1 3 by decide) (.cons (show blueGraph.Adj 3 2 by decide) (.cons (show blueGraph.Adj 2 0 by decide) (.nil))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 8) (Fin 4) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end MatchedFour

namespace CompleteFive
def src : Fin 10 → Fin 5
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 3
  | 4 => 0
  | 5 => 1
  | 6 => 4
  | 7 => 2
  | 8 => 3
  | 9 => 4
def dst : Fin 10 → Fin 5
  | 0 => 2
  | 1 => 1
  | 2 => 3
  | 3 => 0
  | 4 => 1
  | 5 => 4
  | 6 => 0
  | 7 => 3
  | 8 => 4
  | 9 => 2

def redEdges : Finset (Sym2 (Fin 5)) :=
  {s(0,1), s(1,2), s(2,3), s(3,4), s(4,0)}
def redGraph : SimpleGraph (Fin 5) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 10 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,2) then 1 else
  if d.edge = s(2,3) then 7 else
  if d.edge = s(3,4) then 8 else 6
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 :=
  .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 2 by decide) (.cons (show redGraph.Adj 2 3 by decide) (.cons (show redGraph.Adj 3 4 by decide) (.cons (show redGraph.Adj 4 0 by decide) (.nil)))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 5)) :=
  {s(0,2), s(2,4), s(4,1), s(1,3), s(3,0)}
def blueGraph : SimpleGraph (Fin 5) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 10 :=
  if d.edge = s(0,2) then 0 else
  if d.edge = s(2,4) then 9 else
  if d.edge = s(4,1) then 5 else
  if d.edge = s(1,3) then 2 else 3
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 :=
  .cons (show blueGraph.Adj 0 2 by decide) (.cons (show blueGraph.Adj 2 4 by decide) (.cons (show blueGraph.Adj 4 1 by decide) (.cons (show blueGraph.Adj 1 3 by decide) (.cons (show blueGraph.Adj 3 0 by decide) (.nil)))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 10) (Fin 5) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end CompleteFive

namespace Octahedron
def src : Fin 12 → Fin 6
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 3
  | 4 => 0
  | 5 => 4
  | 6 => 1
  | 7 => 5
  | 8 => 2
  | 9 => 4
  | 10 => 3
  | 11 => 5
def dst : Fin 12 → Fin 6
  | 0 => 2
  | 1 => 1
  | 2 => 3
  | 3 => 0
  | 4 => 4
  | 5 => 1
  | 6 => 5
  | 7 => 0
  | 8 => 4
  | 9 => 3
  | 10 => 5
  | 11 => 2

def redEdges : Finset (Sym2 (Fin 6)) :=
  {s(0,2), s(2,1), s(1,4), s(4,3), s(3,5), s(5,0)}
def redGraph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 12 :=
  if d.edge = s(0,2) then 0 else
  if d.edge = s(2,1) then 1 else
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,3) then 9 else
  if d.edge = s(3,5) then 10 else 7
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 :=
  .cons (show redGraph.Adj 0 2 by decide) (.cons (show redGraph.Adj 2 1 by decide) (.cons (show redGraph.Adj 1 4 by decide) (.cons (show redGraph.Adj 4 3 by decide) (.cons (show redGraph.Adj 3 5 by decide) (.cons (show redGraph.Adj 5 0 by decide) (.nil))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 6)) :=
  {s(0,3), s(3,1), s(1,5), s(5,2), s(2,4), s(4,0)}
def blueGraph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 12 :=
  if d.edge = s(0,3) then 3 else
  if d.edge = s(3,1) then 2 else
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,2) then 11 else
  if d.edge = s(2,4) then 8 else 4
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 :=
  .cons (show blueGraph.Adj 0 3 by decide) (.cons (show blueGraph.Adj 3 1 by decide) (.cons (show blueGraph.Adj 1 5 by decide) (.cons (show blueGraph.Adj 5 2 by decide) (.cons (show blueGraph.Adj 2 4 by decide) (.cons (show blueGraph.Adj 4 0 by decide) (.nil))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Octahedron

end Erdos184Work.ThreeCycleKernels

/-! Source block: RigidSwitching. -/

/-! Exact two-cycle switches and their constraints in rigid even graphs.
The minimal-core rigidity implication is not assumed or proved here. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.RigidSwitching
open Critical EvenCore MaximumCycles Rigidity
set_option maxHeartbeats 1500000

variable {V : Type*} {G : SimpleGraph V}

lemma rigid_subfamily_number [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v)) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hpD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    number (subfamilyGraph D) = D.card := by
  have hlo := card_le_number_of_hereditary_minimal
    ((rigid_iff_hereditarily_evenMinimal heven).mp hrig) D hD hpD
  have hcover := (subfamilyGraph_edges D).symm
  have hlow := Subfamilies.lowerFamily_property IsCycleOrEdge D hcover
    (fun H hH => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hD H hH))
  have hdec := Subfamilies.lowerFamily_decomposition D hcover hpD
  have hhi := number_le (Subfamilies.lowerFamily D hcover) hlow hdec
  rw [Subfamilies.lowerFamily_card] at hhi
  exact le_antisymm hhi hlo

lemma rigid_subfamily [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v)) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hpD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    CycleRigid (subfamilyGraph D) := by
  have he := cycle_subfamily_even D hD hpD
  apply hrig.mono heven (subfamilyGraph_le D)
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he v

lemma rigid_pair_intersection_le_two [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    (H K : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hd : Disjoint H.edgeSet K.edgeSet) : (H.verts ∩ K.verts).ncard ≤ 2 := by
  have hHK : H ≠ K := by
    intro heq
    obtain ⟨e,he⟩ := cycle_piece_edgeSet_nonempty H hH
    exact Set.disjoint_left.mp hd he (heq ▸ he)
  let D : Finset G.Subgraph := {H,K}
  have hD : ∀ L ∈ D, L.coe.Connected ∧ L.coe.IsRegularOfDegree 2 := by
    intro L hL
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hL
    rcases hL with rfl | rfl
    · exact hH
    · exact hK
  have hpD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun L => L.edgeSet) := by
    intro A hA B hB hne
    simp only [D,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hne rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hne rfl).elim
  have hnum := rigid_subfamily_number hrig heven D hD hpD
  have hrigR := rigid_subfamily hrig heven D hD hpD
  have hR : subfamilyGraph D = H.spanningCoe ⊔ K.spanningCoe := by simp [subfamilyGraph,D]
  rw [hR] at hnum hrigR
  have hcard : D.card = 2 := by simp [D,hHK]
  by_contra! hbig
  obtain ⟨E,hE,hdE,hcE⟩ := two_cycles_exchange H K hH hK hd (by omega)
  have he := hrigR E
  simp only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at he hE
  have he := he hE hdE
  omega

lemma support_inter_of_append_isCycle {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (hc : (p.append q).IsCycle) (x : V) (hxp : x ∈ p.support) (hxq : x ∈ q.support) :
    x = u ∨ x = v := by
  have hn := hc.support_nodup
  rw [Walk.tail_support_append,List.nodup_append] at hn
  by_contra hx
  have hxu : x ≠ u := fun h => hx (Or.inl h)
  have hxv : x ≠ v := fun h => hx (Or.inr h)
  have hp : x ∈ p.support.tail := by
    rw [p.support_eq_cons,List.mem_cons] at hxp
    exact hxp.resolve_left hxu
  have hq : x ∈ q.support.tail := by
    rw [q.support_eq_cons,List.mem_cons] at hxq
    exact hxq.resolve_left hxv
  exact hn.2.2 x hp x hq rfl

/-- Two internally disjoint paths obtained by cutting a cycle at distinct vertices. -/
structure CyclePaths {u : V} (c : G.Walk u u) (v : V) where
  left : G.Walk u v
  right : G.Walk u v
  left_path : left.IsPath
  right_path : right.IsPath
  edges_disjoint : left.edges.Disjoint right.edges
  edges_cover : ∀ e, (e ∈ left.edges ∨ e ∈ right.edges) ↔ e ∈ c.edges
  support_cover : ∀ x, (x ∈ left.support ∨ x ∈ right.support) ↔ x ∈ c.support
  support_inter : ∀ x, x ∈ left.support → x ∈ right.support → x = u ∨ x = v

lemma exists_cyclePaths {u v : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v ∈ c.support) (huv : u ≠ v) : Nonempty (CyclePaths c v) := by
  classical
  let p := c.takeUntil v hv
  let q := (c.dropUntil v hv).reverse
  have heq : p.append q.reverse = c := by simp [p,q,Walk.take_spec]
  refine ⟨⟨p,q,hc.isPath_takeUntil hv,(cycle_dropUntil_isPath hc hv huv).reverse,?_,?_,?_,?_⟩⟩
  · simpa only [p,q,Walk.edges_reverse,List.disjoint_reverse_right] using
      hc.isTrail.disjoint_edges_takeUntil_dropUntil hv
  · intro e
    calc
      _ ↔ e ∈ (p.append q.reverse).edges := by
        simp only [Walk.edges_append,List.mem_append,Walk.edges_reverse,List.mem_reverse]
      _ ↔ e ∈ c.edges := by rw [heq]
  · intro x
    calc
      _ ↔ x ∈ (p.append q.reverse).support := by
        simp only [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse]
      _ ↔ x ∈ c.support := by rw [heq]
  · intro x hxp hxq
    apply support_inter_of_append_isCycle (heq ▸ hc) x hxp
    simpa only [Walk.support_reverse,List.mem_reverse] using hxq

namespace CyclePaths
variable {u v : V} {c : G.Walk u u}

def swap (P : CyclePaths c v) : CyclePaths c v where
  left := P.right
  right := P.left
  left_path := P.right_path
  right_path := P.left_path
  edges_disjoint := P.edges_disjoint.symm
  edges_cover e := by simpa only [or_comm] using P.edges_cover e
  support_cover x := by simpa only [or_comm] using P.support_cover x
  support_inter x hx hy := P.support_inter x hy hx

lemma left_support_subset (P : CyclePaths c v) : P.left.support ⊆ c.support :=
  fun _ h => (P.support_cover _).mp (Or.inl h)
lemma right_support_subset (P : CyclePaths c v) : P.right.support ⊆ c.support :=
  fun _ h => (P.support_cover _).mp (Or.inr h)
lemma left_edges_subset (P : CyclePaths c v) : P.left.edges ⊆ c.edges :=
  fun _ h => (P.edges_cover _).mp (Or.inl h)
lemma right_edges_subset (P : CyclePaths c v) : P.right.edges ⊆ c.edges :=
  fun _ h => (P.edges_cover _).mp (Or.inr h)

lemma exists_left_through (P : CyclePaths c v) {x : V} (hx : x ∈ c.support) :
    ∃ Q : CyclePaths c v, x ∈ Q.left.support := by
  rcases (P.support_cover x).mpr hx with hx | hx
  · exact ⟨P,hx⟩
  · exact ⟨P.swap,hx⟩
end CyclePaths

lemma switch_cyclePaths {u v : V} {c d : G.Walk u u} (huv : u ≠ v)
    (P : CyclePaths c v) (Q : CyclePaths d v) (hd : c.edges.Disjoint d.edges)
    (hinter : ∀ x, x ∈ c.support → x ∈ d.support → x = u ∨ x = v) :
    (P.left.append Q.left.reverse).IsCycle ∧
    (P.right.append Q.right.reverse).IsCycle ∧
    (P.left.append Q.left.reverse).edges.Disjoint (P.right.append Q.right.reverse).edges ∧
    (∀ e, (e ∈ (P.left.append Q.left.reverse).edges ∨
      e ∈ (P.right.append Q.right.reverse).edges) ↔ e ∈ c.edges ∨ e ∈ d.edges) := by
  have hpr : P.left.edges.Disjoint Q.left.edges := by
    apply List.disjoint_left.mpr
    intro e he1 he2
    exact List.disjoint_left.mp hd (P.left_edges_subset he1) (Q.left_edges_subset he2)
  have hps : P.left.edges.Disjoint Q.right.edges := by
    apply List.disjoint_left.mpr
    intro e he1 he2
    exact List.disjoint_left.mp hd (P.left_edges_subset he1) (Q.right_edges_subset he2)
  have hqr : P.right.edges.Disjoint Q.left.edges := by
    apply List.disjoint_left.mpr
    intro e he1 he2
    exact List.disjoint_left.mp hd (P.right_edges_subset he1) (Q.left_edges_subset he2)
  have hqs : P.right.edges.Disjoint Q.right.edges := by
    apply List.disjoint_left.mpr
    intro e he1 he2
    exact List.disjoint_left.mp hd (P.right_edges_subset he1) (Q.right_edges_subset he2)
  refine ⟨?_,?_,?_,?_⟩
  · apply append_isCycle_of_support_inter P.left_path Q.left_path.reverse huv
      (by simpa only [Walk.edges_reverse,List.disjoint_reverse_right] using hpr)
    intro x hx hy
    exact hinter x (P.left_support_subset hx) (Q.left_support_subset (by simpa using hy))
  · apply append_isCycle_of_support_inter P.right_path Q.right_path.reverse huv
      (by simpa only [Walk.edges_reverse,List.disjoint_reverse_right] using hqs)
    intro x hx hy
    exact hinter x (P.right_support_subset hx) (Q.right_support_subset (by simpa using hy))
  · simp only [Walk.edges_append,Walk.edges_reverse,List.disjoint_append_left,List.disjoint_append_right,
      List.disjoint_reverse_left,List.disjoint_reverse_right]
    exact ⟨⟨P.edges_disjoint,hqr.symm⟩,⟨hps,Q.edges_disjoint⟩⟩
  · intro e
    simp only [Walk.edges_append,List.mem_append,Walk.edges_reverse,List.mem_reverse]
    rw [← P.edges_cover e,← Q.edges_cover e]
    tauto

lemma two_cycle_switch_through {u v x y : V} (c d : G.Walk u u)
    (hc : c.IsCycle) (hd : d.IsCycle) (huv : u ≠ v)
    (hvc : v ∈ c.support) (hvd : v ∈ d.support)
    (hdis : c.edges.Disjoint d.edges)
    (hinter : ∀ z, z ∈ c.support → z ∈ d.support → z = u ∨ z = v)
    (hx : x ∈ c.support) (hy : y ∈ d.support) :
    ∃ r s : G.Walk u u, r.IsCycle ∧ s.IsCycle ∧ r.edges.Disjoint s.edges ∧
      (∀ e, (e ∈ r.edges ∨ e ∈ s.edges) ↔ e ∈ c.edges ∨ e ∈ d.edges) ∧
      x ∈ r.support ∧ y ∈ r.support := by
  obtain ⟨P⟩ := exists_cyclePaths c hc hvc huv
  obtain ⟨Q⟩ := exists_cyclePaths d hd hvd huv
  obtain ⟨P,hxP⟩ := P.exists_left_through hx
  obtain ⟨Q,hyQ⟩ := Q.exists_left_through hy
  obtain ⟨hr,hs,hdis',hcover⟩ := switch_cyclePaths huv P Q hdis hinter
  refine ⟨P.left.append Q.left.reverse,P.right.append Q.right.reverse,hr,hs,hdis',hcover,?_,?_⟩
  · exact (Walk.mem_support_append_iff _ _).mpr (Or.inl hxP)
  · exact (Walk.mem_support_append_iff _ _).mpr (Or.inr (by simpa using hyQ))

lemma rigid_no_three_common_vertices [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v)) {u v : V}
    (p : G.Walk u u) (q : G.Walk v v) (hp : p.IsCycle) (hq : q.IsCycle)
    (hd : p.edges.Disjoint q.edges) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxp : x ∈ p.support) (hyp : y ∈ p.support) (hzp : z ∈ p.support)
    (hxq : x ∈ q.support) (hyq : y ∈ q.support) (hzq : z ∈ q.support) : False := by
  have hdis : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e hep heq
    exact List.disjoint_left.mp hd (p.mem_edges_toSubgraph.mp hep) (q.mem_edges_toSubgraph.mp heq)
  have hi := rigid_pair_intersection_le_two hrig heven p.toSubgraph q.toSubgraph
    (cycle_coe_regular G hp) (cycle_coe_regular G hq) hdis
  have hs : ({x,y,z} : Set V) ⊆ p.toSubgraph.verts ∩ q.toSubgraph.verts := by
    intro w hw
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨p.mem_verts_toSubgraph.mpr hxp,q.mem_verts_toSubgraph.mpr hxq⟩
    · exact ⟨p.mem_verts_toSubgraph.mpr hyp,q.mem_verts_toSubgraph.mpr hyq⟩
    · exact ⟨p.mem_verts_toSubgraph.mpr hzp,q.mem_verts_toSubgraph.mpr hzq⟩
  have hl := Set.ncard_le_ncard hs
  have ht : ({x,y,z} : Set V).ncard = 3 := by simp [hxy,hxz,hyz]
  omega

/-- If the third cycle meets the second and avoids both switching vertices,
it cannot meet either arc of the first cycle twice in a rigid graph. -/
lemma rigid_arc_contact_subsingleton [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    {u v w : V} {c d : G.Walk u u} {t : G.Walk w w}
    (hd : d.IsCycle) (ht : t.IsCycle) (huv : u ≠ v) (hvd : v ∈ d.support)
    (P : CyclePaths c v)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hinter : ∀ x, x ∈ c.support → x ∈ d.support → x = u ∨ x = v)
    (hut : u ∉ t.support) (hvt : v ∉ t.support)
    (hmeet : ∃ y, y ∈ d.support ∧ y ∈ t.support) :
    ({x | x ∈ P.left.support ∧ x ∈ t.support} : Set V).Subsingleton := by
  obtain ⟨y,hyd,hyt⟩ := hmeet
  obtain ⟨Q⟩ := exists_cyclePaths d hd hvd huv
  obtain ⟨Q,hyQ⟩ := Q.exists_left_through hyd
  obtain ⟨hr,_,_,hcover⟩ := switch_cyclePaths huv P Q hcd hinter
  let r := P.left.append Q.left.reverse
  have hrt : r.edges.Disjoint t.edges := by
    apply List.disjoint_left.mpr
    intro e her het
    rcases (hcover e).mp (Or.inl her) with hec | hed
    · exact List.disjoint_left.mp hct hec het
    · exact List.disjoint_left.mp hdt hed het
  have hdist (x : V) (hxc : x ∈ c.support) (hxt : x ∈ t.support) : x ≠ y := by
    intro he
    have hxd : x ∈ d.support := he.symm ▸ hyd
    rcases hinter x hxc hxd with he | he
    · exact hut (he ▸ hxt)
    · exact hvt (he ▸ hxt)
  intro x hx z hz
  by_contra hxz
  have hxr : x ∈ r.support := (Walk.mem_support_append_iff _ _).mpr (Or.inl hx.1)
  have hzr : z ∈ r.support := (Walk.mem_support_append_iff _ _).mpr (Or.inl hz.1)
  have hyr : y ∈ r.support := (Walk.mem_support_append_iff _ _).mpr (Or.inr (by simpa using hyQ))
  exact rigid_no_three_common_vertices hrig heven r t hr ht hrt hxz
    (hdist x (P.left_support_subset hx.1) hx.2) (hdist z (P.left_support_subset hz.1) hz.2)
    hxr hzr hyr hx.2 hz.2 hyt

lemma rigid_contacts_alternate [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    {u v w : V} {c d : G.Walk u u} {t : G.Walk w w}
    (hd : d.IsCycle) (ht : t.IsCycle) (huv : u ≠ v) (hvd : v ∈ d.support)
    (P : CyclePaths c v)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hinter : ∀ x, x ∈ c.support → x ∈ d.support → x = u ∨ x = v)
    (hut : u ∉ t.support) (hvt : v ∉ t.support)
    (hmeet : ∃ y, y ∈ d.support ∧ y ∈ t.support)
    {x z : V} (hxz : x ≠ z) (hxc : x ∈ c.support) (hzc : z ∈ c.support)
    (hxt : x ∈ t.support) (hzt : z ∈ t.support) :
    (x ∈ P.left.support ∧ z ∈ P.right.support) ∨
      (z ∈ P.left.support ∧ x ∈ P.right.support) := by
  have hl := rigid_arc_contact_subsingleton hrig heven hd ht huv hvd P hcd hct hdt hinter hut hvt hmeet
  have hr := rigid_arc_contact_subsingleton hrig heven hd ht huv hvd P.swap hcd hct hdt hinter hut hvt hmeet
  rcases (P.support_cover x).mpr hxc with hx | hx <;>
    rcases (P.support_cover z).mpr hzc with hz | hz
  · exact (hxz (hl ⟨hx,hxt⟩ ⟨hz,hzt⟩)).elim
  · exact Or.inl ⟨hx,hz⟩
  · exact Or.inr ⟨hz,hx⟩
  · exact (hxz (hr ⟨hx,hxt⟩ ⟨hz,hzt⟩)).elim

#print axioms rigid_no_three_common_vertices
#print axioms rigid_arc_contact_subsingleton
#print axioms rigid_contacts_alternate
#print axioms rigid_subfamily_number
#print axioms rigid_pair_intersection_le_two
#print axioms exists_cyclePaths
#print axioms two_cycle_switch_through
end Erdos184Work.RigidSwitching

/-! Source block: CycleSegments. -/

/-! Building path-substitution models from segments of edge-disjoint cycles. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleSegments
open PathSubstitution RigidSwitching
set_option maxHeartbeats 1500000

variable {V W J K : Type*} {G : SimpleGraph V}

lemma support_subset_of_edges_subset {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (hp : ¬ p.Nil) (he : p.edges ⊆ q.edges) : p.support ⊆ q.support := by
  intro x hx
  obtain ⟨e,hep,hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hp).mp hx
  exact Walk.mem_support_of_mem_edges (he hep) hxe

lemma paths_in_cycle_support_inter [Fintype V]
    {u a b d e : V} (c : G.Walk u u) (hc : c.IsCycle)
    (p : G.Walk a b) (q : G.Walk d e) (hp : p.IsPath) (hq : ¬ q.Nil)
    (hpc : p.edges ⊆ c.edges) (hqc : q.edges ⊆ c.edges)
    (hpq : p.edges.Disjoint q.edges) (x : V) (hxp : x ∈ p.support) (hxq : x ∈ q.support) :
    x = a ∨ x = b := by
  by_contra hx
  have hxa : x ≠ a := fun h => hx (Or.inl h)
  have hxb : x ≠ b := fun h => hx (Or.inr h)
  obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp hxp
  have hi0 : i ≠ 0 := by rintro rfl; exact hxa (by simpa using hi.symm)
  have hil' : i < p.length := by
    by_contra hn
    have he : i = p.length := by omega
    exact hxb (by simpa [he] using hi.symm)
  obtain ⟨e,heq,hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hq).mp hxq
  obtain ⟨y,hey⟩ := Sym2.mem_iff_exists.mp hxe
  subst e
  have hxc : x ∈ c.support := c.fst_mem_support_of_mem_edges (hqc heq)
  have hcardp : (p.toSubgraph.neighborSet x).ncard = 2 := by
    rw [← hi]
    exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil'
  have hcardc := hc.ncard_neighborSet_toSubgraph_eq_two hxc
  have hsub : p.toSubgraph.neighborSet x ⊆ c.toSubgraph.neighborSet x := by
    intro z hz
    exact c.mem_edges_toSubgraph.mpr (hpc (p.mem_edges_toSubgraph.mp (show s(x,z) ∈ p.toSubgraph.edgeSet from hz)))
  have hEq : p.toSubgraph.neighborSet x = c.toSubgraph.neighborSet x :=
    Set.eq_of_subset_of_ncard_le hsub (by omega)
  have hyc : y ∈ c.toSubgraph.neighborSet x := c.mem_edges_toSubgraph.mpr (hqc heq)
  have hyp : y ∈ p.toSubgraph.neighborSet x := hEq ▸ hyc
  exact List.disjoint_left.mp hpq (p.mem_edges_toSubgraph.mp hyp) heq

/-- Only edge partition data are needed: degree two on each original cycle
forces the required internal vertex disjointness automatically. -/
noncomputable def family_of_cycle_segments [Fintype V]
    (vertex : W → V) (hinj : Function.Injective vertex) (src dst : J → W)
    (hne : ∀ j, src j ≠ dst j)
    (P : ∀ j, G.Walk (vertex (src j)) (vertex (dst j)))
    (hP : ∀ j, (P j).IsPath)
    (root : K → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (color : J → K) (hPC : ∀ j, (P j).edges ⊆ (C (color j)).edges)
    (hdis : ∀ i j, i ≠ j → (P i).edges.Disjoint (P j).edges)
    (hincident : ∀ w k, vertex w ∈ (C k).support →
      ∃ j, color j = k ∧ (w = src j ∨ w = dst j))
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support →
      ∃ w, vertex w = x) : Family J W G := by
  have hnotnil (j : J) : ¬ (P j).Nil := Walk.not_nil_of_ne (fun h => hne j (hinj h))
  have hsupport (j : J) : (P j).support ⊆ (C (color j)).support :=
    support_subset_of_edges_subset _ _ (hnotnil j) (hPC j)
  have hsame (i j : J) (hij : i ≠ j) (hcolor : color i = color j) (x : V)
      (hxi : x ∈ (P i).support) (hxj : x ∈ (P j).support) :
      x = vertex (src i) ∨ x = vertex (dst i) := by
    apply paths_in_cycle_support_inter (C (color i)) (hC _) (P i) (P j) (hP i) (hnotnil j)
      (hPC i) _ (hdis i j hij) x hxi hxj
    have he := congrArg (fun k => (C k).edges) hcolor.symm
    intro e hep
    dsimp only at he
    rw [← he]
    exact hPC j hep
  have hvmem (j : J) (w : W) : vertex w ∈ (P j).support ↔ w = src j ∨ w = dst j := by
    constructor
    · intro hw
      obtain ⟨i,hcolor,hwi⟩ := hincident w (color j) (hsupport j hw)
      by_cases hij : j = i
      · simpa only [← hij] using hwi
      have hwiP : vertex w ∈ (P i).support := by
        rcases hwi with rfl | rfl <;> simp
      exact (hsame j i hij hcolor.symm (vertex w) hw hwiP).imp (fun h => hinj h) (fun h => hinj h)
    · rintro (rfl | rfl) <;> simp
  refine ⟨vertex,hinj,src,dst,hne,P,hP,hvmem,hdis,?_⟩
  intro i j hij x hxi hxj
  by_cases hcolor : color i = color j
  · exact hsame i j hij hcolor x hxi hxj
  · obtain ⟨w,rfl⟩ := hmeet (color i) (color j) hcolor x (hsupport i hxi) (hsupport j hxj)
    exact ((hvmem i w).mp hxi).imp (congrArg vertex) (congrArg vertex)

lemma disjoint_mono {α : Type*} {A B C D : List α} (h : C.Disjoint D) (hA : A ⊆ C) (hB : B ⊆ D) :
    A.Disjoint B := by
  apply List.disjoint_left.mpr
  intro x hx hy
  exact List.disjoint_left.mp h (hA hx) (hB hy)

structure PathParts {u v : V} (p : G.Walk u v) (w : V) where
  first : G.Walk u w
  last : G.Walk w v
  first_path : first.IsPath
  last_path : last.IsPath
  edges_disjoint : first.edges.Disjoint last.edges
  edges_cover : ∀ e, (e ∈ first.edges ∨ e ∈ last.edges) ↔ e ∈ p.edges

lemma exists_pathParts {u v w : V} (p : G.Walk u v) (hp : p.IsPath) (hw : w ∈ p.support) :
    Nonempty (PathParts p w) := by
  refine ⟨⟨p.takeUntil w hw,p.dropUntil w hw,hp.takeUntil hw,hp.dropUntil hw,
    hp.isTrail.disjoint_edges_takeUntil_dropUntil hw,?_⟩⟩
  intro e
  rw [← List.mem_append,← Walk.edges_append,Walk.take_spec]

namespace PathParts
variable {u v w : V} {p : G.Walk u v}
lemma first_edges_subset (P : PathParts p w) : P.first.edges ⊆ p.edges :=
  fun e he => (P.edges_cover e).mp (Or.inl he)
lemma last_edges_subset (P : PathParts p w) : P.last.edges ⊆ p.edges :=
  fun e he => (P.edges_cover e).mp (Or.inr he)
end PathParts

/-- A finite collection of paths partitioning one cycle. -/
structure Segmentation {u : V} (c : G.Walk u u) (vertex : W → V) (src dst : J → W) where
  path : ∀ j, G.Walk (vertex (src j)) (vertex (dst j))
  isPath : ∀ j, (path j).IsPath
  disjoint : ∀ i j, i ≠ j → (path i).edges.Disjoint (path j).edges
  cover : ∀ e, e ∈ c.edges ↔ ∃ j, e ∈ (path j).edges

namespace Segmentation
variable {u : V} {c : G.Walk u u} {vertex : W → V} {src dst : J → W}
lemma edges_subset (S : Segmentation c vertex src dst) (j : J) : (S.path j).edges ⊆ c.edges :=
  fun e he => (S.cover e).mpr ⟨j,he⟩
end Segmentation

def src2 : Fin 2 → Fin 2 := ![0,1]
def dst2 : Fin 2 → Fin 2 := ![1,0]
def src3 : Fin 3 → Fin 3 := ![0,1,2]
def dst3 : Fin 3 → Fin 3 := ![1,2,0]
def src4 : Fin 4 → Fin 4 := ![0,1,2,3]
def dst4 : Fin 4 → Fin 4 := ![1,2,3,0]

lemma two_segments {u v : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v ∈ c.support) (huv : u ≠ v) :
    Nonempty (Segmentation c ![u,v] src2 dst2) := by
  obtain ⟨P⟩ := exists_cyclePaths c hc hv huv
  let paths : ∀ i : Fin 2, G.Walk (![u,v] (src2 i)) (![u,v] (dst2 i)) :=
    Fin.cases P.left (Fin.cases P.right.reverse (fun i => Fin.elim0 i))
  refine ⟨⟨paths,?_,?_,?_⟩⟩
  · intro i
    fin_cases i
    · exact P.left_path
    · exact P.right_path.reverse
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change P.left.edges.Disjoint P.right.reverse.edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_right] using P.edges_disjoint
    · change P.right.reverse.edges.Disjoint P.left.edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left] using P.edges_disjoint.symm
    · exact (hij rfl).elim
  · intro e
    rw [Fin.exists_fin_two]
    change e ∈ c.edges ↔ e ∈ P.left.edges ∨ e ∈ P.right.reverse.edges
    simpa only [Walk.edges_reverse,List.mem_reverse] using (P.edges_cover e).symm

lemma three_segments {u v w : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v ∈ c.support) (hw : w ∈ c.support) (huv : u ≠ v) :
    Nonempty (Segmentation c ![u,v,w] src3 dst3) := by
  obtain ⟨P⟩ := exists_cyclePaths c hc hv huv
  obtain ⟨P,hwP⟩ := P.exists_left_through hw
  obtain ⟨L⟩ := exists_pathParts P.left P.left_path hwP
  let paths : ∀ i : Fin 3, G.Walk (![u,v,w] (src3 i)) (![u,v,w] (dst3 i)) :=
    Fin.cases P.right (Fin.cases L.last.reverse (Fin.cases L.first.reverse (fun i => Fin.elim0 i)))
  have h01 : P.right.edges.Disjoint L.last.edges :=
    disjoint_mono P.edges_disjoint.symm (List.Subset.refl _) L.last_edges_subset
  have h02 : P.right.edges.Disjoint L.first.edges :=
    disjoint_mono P.edges_disjoint.symm (List.Subset.refl _) L.first_edges_subset
  have h12 : L.last.edges.Disjoint L.first.edges := L.edges_disjoint.symm
  refine ⟨⟨paths,?_,?_,?_⟩⟩
  · intro i
    fin_cases i
    · exact P.right_path
    · exact L.last_path.reverse
    · exact L.first_path.reverse
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change (P.right).edges.Disjoint (L.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h01
    · change (P.right).edges.Disjoint (L.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h02
    · change (L.last.reverse).edges.Disjoint (P.right).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h01.symm
    · exact (hij rfl).elim
    · change (L.last.reverse).edges.Disjoint (L.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h12
    · change (L.first.reverse).edges.Disjoint (P.right).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h02.symm
    · change (L.first.reverse).edges.Disjoint (L.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h12.symm
    · exact (hij rfl).elim
  · intro e
    rw [Fin.exists_fin_succ,Fin.exists_fin_two]
    change e ∈ c.edges ↔ e ∈ P.right.edges ∨ e ∈ L.last.reverse.edges ∨ e ∈ L.first.reverse.edges
    simp only [Walk.edges_reverse,List.mem_reverse]
    rw [← P.edges_cover e,← L.edges_cover e]
    tauto

lemma four_segments_of_paths {u v x y : V} {c : G.Walk u u}
    (P : CyclePaths c v) (hx : x ∈ P.left.support) (hy : y ∈ P.right.support) :
    Nonempty (Segmentation c ![u,x,v,y] src4 dst4) := by
  obtain ⟨L⟩ := exists_pathParts P.left P.left_path hx
  obtain ⟨R⟩ := exists_pathParts P.right P.right_path hy
  let paths : ∀ i : Fin 4, G.Walk (![u,x,v,y] (src4 i)) (![u,x,v,y] (dst4 i)) :=
    Fin.cases L.first (Fin.cases L.last (Fin.cases R.last.reverse
      (Fin.cases R.first.reverse (fun i => Fin.elim0 i))))
  have h01 : L.first.edges.Disjoint L.last.edges := L.edges_disjoint
  have h02 : L.first.edges.Disjoint R.last.edges :=
    disjoint_mono P.edges_disjoint L.first_edges_subset R.last_edges_subset
  have h03 : L.first.edges.Disjoint R.first.edges :=
    disjoint_mono P.edges_disjoint L.first_edges_subset R.first_edges_subset
  have h12 : L.last.edges.Disjoint R.last.edges :=
    disjoint_mono P.edges_disjoint L.last_edges_subset R.last_edges_subset
  have h13 : L.last.edges.Disjoint R.first.edges :=
    disjoint_mono P.edges_disjoint L.last_edges_subset R.first_edges_subset
  have h23 : R.last.edges.Disjoint R.first.edges := R.edges_disjoint.symm
  refine ⟨⟨paths,?_,?_,?_⟩⟩
  · intro i
    fin_cases i
    · exact L.first_path
    · exact L.last_path
    · exact R.last_path.reverse
    · exact R.first_path.reverse
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change (L.first).edges.Disjoint (L.last).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h01
    · change (L.first).edges.Disjoint (R.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h02
    · change (L.first).edges.Disjoint (R.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h03
    · change (L.last).edges.Disjoint (L.first).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h01.symm
    · exact (hij rfl).elim
    · change (L.last).edges.Disjoint (R.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h12
    · change (L.last).edges.Disjoint (R.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h13
    · change (R.last.reverse).edges.Disjoint (L.first).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h02.symm
    · change (R.last.reverse).edges.Disjoint (L.last).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h12.symm
    · exact (hij rfl).elim
    · change (R.last.reverse).edges.Disjoint (R.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h23
    · change (R.first.reverse).edges.Disjoint (L.first).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h03.symm
    · change (R.first.reverse).edges.Disjoint (L.last).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h13.symm
    · change (R.first.reverse).edges.Disjoint (R.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h23.symm
    · exact (hij rfl).elim
  · intro e
    rw [Fin.exists_fin_succ,Fin.exists_fin_succ,Fin.exists_fin_two]
    change e ∈ c.edges ↔ e ∈ L.first.edges ∨ e ∈ L.last.edges ∨
      e ∈ R.last.reverse.edges ∨ e ∈ R.first.reverse.edges
    simp only [Walk.edges_reverse,List.mem_reverse]
    rw [← P.edges_cover e,← L.edges_cover e,← R.edges_cover e]
    tauto

lemma four_segments_of_rigid [Fintype V] (hrig : Rigidity.CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    {u v w : V} {c d : G.Walk u u} {t : G.Walk w w}
    (hc : c.IsCycle) (hd : d.IsCycle) (ht : t.IsCycle) (huv : u ≠ v)
    (hvc : v ∈ c.support) (hvd : v ∈ d.support)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hinter : ∀ x, x ∈ c.support → x ∈ d.support → x = u ∨ x = v)
    (hut : u ∉ t.support) (hvt : v ∉ t.support)
    (hmeet : ∃ y, y ∈ d.support ∧ y ∈ t.support)
    {x z : V} (hxz : x ≠ z) (hxc : x ∈ c.support) (hzc : z ∈ c.support)
    (hxt : x ∈ t.support) (hzt : z ∈ t.support) :
    Nonempty (Segmentation c ![u,x,v,z] src4 dst4) := by
  obtain ⟨P⟩ := exists_cyclePaths c hc hvc huv
  have ha := rigid_contacts_alternate hrig heven hd ht huv hvd P hcd hct hdt hinter hut hvt hmeet
    hxz hxc hzc hxt hzt
  rcases ha with ⟨hx,hz⟩ | ⟨hz,hx⟩
  · exact four_segments_of_paths P hx hz
  · exact four_segments_of_paths P.swap hx hz

/-- Relabel the edges of a path model; parallel edges remain distinct labels. -/
noncomputable def reindexFamily {J' : Type*} (F : Family J W G) (e : J' ≃ J) : Family J' W G where
  vertex := F.vertex
  injective := F.injective
  src := F.src ∘ e
  dst := F.dst ∘ e
  ne j := F.ne (e j)
  path j := F.path (e j)
  isPath j := F.isPath (e j)
  vertex_mem j := F.vertex_mem (e j)
  edge_disjoint i j hij := F.edge_disjoint (e i) (e j) (fun h => hij (e.injective h))
  support_inter i j hij := F.support_inter (e i) (e j) (fun h => hij (e.injective h))

/-- Assemble local cycle segmentations into a single labelled path model.
The global junction list contains every intersection of different cycles. -/
noncomputable def assemble_segments [Fintype V]
    (m : K → ℕ) (vertex : W → V) (hinj : Function.Injective vertex)
    (place : ∀ k, Fin (m k) → W) (src dst : ∀ k, Fin (m k) → Fin (m k))
    (hne : ∀ k i, place k (src k i) ≠ place k (dst k i))
    (hsrc : ∀ k, Function.Surjective (src k))
    (root : K → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (src k) (dst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support →
      ∃ w, vertex w = x) : Family (Σ k, Fin (m k)) W G := by
  let src' : (Σ k, Fin (m k)) → W := fun j => place j.1 (src j.1 j.2)
  let dst' : (Σ k, Fin (m k)) → W := fun j => place j.1 (dst j.1 j.2)
  let P : ∀ j : (Σ k, Fin (m k)), G.Walk (vertex (src' j)) (vertex (dst' j)) :=
    fun j => (S j.1).path j.2
  apply family_of_cycle_segments vertex hinj src' dst' (fun j => hne j.1 j.2)
    P (fun j => (S j.1).isPath j.2) root C hC Sigma.fst (fun j => (S j.1).edges_subset j.2)
    _ _ hmeet
  · rintro ⟨k,i⟩ ⟨l,j⟩ hij
    by_cases hkl : k = l
    · subst l
      exact (S k).disjoint i j (fun he => hij (by cases he; rfl))
    · exact disjoint_mono (hdisC k l hkl) ((S k).edges_subset i) ((S l).edges_subset j)
  · intro w k hw
    obtain ⟨i,hi⟩ := hpoints w k hw
    obtain ⟨j,hj⟩ := hsrc k i
    refine ⟨⟨k,j⟩,rfl,Or.inl ?_⟩
    change w = place k (src k j)
    rw [hj,hi]

lemma assemble_segments_src [Fintype V]
    (m : K → ℕ) (vertex : W → V) (hinj : Function.Injective vertex)
    (place : ∀ k, Fin (m k) → W) (src dst : ∀ k, Fin (m k) → Fin (m k))
    (hne : ∀ k i, place k (src k i) ≠ place k (dst k i))
    (hsrc : ∀ k, Function.Surjective (src k))
    (root : K → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (src k) (dst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (j : Σ k, Fin (m k)) :
    (assemble_segments m vertex hinj place src dst hne hsrc root C hC S hdisC hpoints hmeet).src j =
      place j.1 (src j.1 j.2) := rfl

lemma assemble_segments_cover [Fintype V]
    (m : K → ℕ) (vertex : W → V) (hinj : Function.Injective vertex)
    (place : ∀ k, Fin (m k) → W) (src dst : ∀ k, Fin (m k) → Fin (m k))
    (hne : ∀ k i, place k (src k i) ≠ place k (dst k i))
    (hsrc : ∀ k, Function.Surjective (src k))
    (root : K → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (src k) (dst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) :
    ∀ x y, G.Adj x y → ∃ j,
      s(x,y) ∈ ((assemble_segments m vertex hinj place src dst hne hsrc root C hC S hdisC hpoints hmeet).path j).edges := by
  intro x y hxy
  obtain ⟨k,hk⟩ := hcover x y hxy
  obtain ⟨j,hj⟩ := (S k).cover s(x,y) |>.mp hk
  exact ⟨⟨k,j⟩,hj⟩

#print axioms assemble_segments
#print axioms assemble_segments_cover
#print axioms three_segments
#print axioms four_segments_of_paths
#print axioms four_segments_of_rigid
#print axioms paths_in_cycle_support_inter
#print axioms family_of_cycle_segments
#print axioms two_segments
end Erdos184Work.CycleSegments

/-! Source block: JunctionAssembly. -/

/-! Assembling the four canonical three-cycle junction models from local cycle segments. -/

open SimpleGraph
namespace Erdos184Work.ThreeCycleKernels
open PathSubstitution CycleSegments
namespace DoubleTriangle
abbrev sizes : Fin 3 → ℕ := ![2,2,2]
def place : (k : Fin 3) → Fin (sizes k) → Fin 3
  | 0 => ![0,1]
  | 1 => ![0,2]
  | 2 => ![1,2]
def localSrc : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => src2
  | 1 => src2
  | 2 => src2
def localDst : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => dst2
  | 1 => dst2
  | 2 => dst2
lemma local_ne : ∀ k i, place k (localSrc k i) ≠ place k (localDst k i) := by decide
lemma local_src_surjective : ∀ k, Function.Surjective (localSrc k) := by
  intro k i
  fin_cases k <;> refine ⟨i,?_⟩ <;> fin_cases i <;> rfl
def location : Fin 6 → (Σ k : Fin 3, Fin (sizes k))
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨0,⟨1,by decide⟩⟩
  | 2 => ⟨1,⟨0,by decide⟩⟩
  | 3 => ⟨1,⟨1,by decide⟩⟩
  | 4 => ⟨2,⟨0,by decide⟩⟩
  | 5 => ⟨2,⟨1,by decide⟩⟩
lemma location_bijective : Function.Bijective location := by decide
noncomputable def locationEquiv := Equiv.ofBijective location location_bijective

lemma assembled_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 3 → V) (hinj : Function.Injective vertex)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  let F := assemble_segments sizes vertex hinj place localSrc localDst local_ne local_src_surjective
    root C hC S hdisC hpoints hmeet
  apply subdivision_number_le_two (reindexFamily F locationEquiv)
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · intro x y hxy
    obtain ⟨j,hj⟩ := assemble_segments_cover sizes vertex hinj place localSrc localDst local_ne local_src_surjective
      root C hC S hdisC hpoints hmeet hcover x y hxy
    refine ⟨locationEquiv.symm j,?_⟩
    change s(x,y) ∈ (F.path (locationEquiv (locationEquiv.symm j))).edges
    have he := congrArg (fun j => (F.path j).edges) (locationEquiv.apply_symm_apply j)
    dsimp only at he
    rw [he]
    exact hj

#print axioms assembled_number_le_two
end DoubleTriangle

namespace MatchedFour
abbrev sizes : Fin 3 → ℕ := ![3,3,2]
def place : (k : Fin 3) → Fin (sizes k) → Fin 4
  | 0 => ![0,1,2]
  | 1 => ![0,1,3]
  | 2 => ![2,3]
def localSrc : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => src3
  | 1 => src3
  | 2 => src2
def localDst : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => dst3
  | 1 => dst3
  | 2 => dst2
lemma local_ne : ∀ k i, place k (localSrc k i) ≠ place k (localDst k i) := by decide
lemma local_src_surjective : ∀ k, Function.Surjective (localSrc k) := by
  intro k i
  fin_cases k <;> refine ⟨i,?_⟩ <;> fin_cases i <;> rfl
def location : Fin 8 → (Σ k : Fin 3, Fin (sizes k))
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨0,⟨1,by decide⟩⟩
  | 2 => ⟨0,⟨2,by decide⟩⟩
  | 3 => ⟨1,⟨0,by decide⟩⟩
  | 4 => ⟨1,⟨1,by decide⟩⟩
  | 5 => ⟨1,⟨2,by decide⟩⟩
  | 6 => ⟨2,⟨0,by decide⟩⟩
  | 7 => ⟨2,⟨1,by decide⟩⟩
lemma location_bijective : Function.Bijective location := by decide
noncomputable def locationEquiv := Equiv.ofBijective location location_bijective

lemma assembled_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 4 → V) (hinj : Function.Injective vertex)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  let F := assemble_segments sizes vertex hinj place localSrc localDst local_ne local_src_surjective
    root C hC S hdisC hpoints hmeet
  apply subdivision_number_le_two (reindexFamily F locationEquiv)
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · intro x y hxy
    obtain ⟨j,hj⟩ := assemble_segments_cover sizes vertex hinj place localSrc localDst local_ne local_src_surjective
      root C hC S hdisC hpoints hmeet hcover x y hxy
    refine ⟨locationEquiv.symm j,?_⟩
    change s(x,y) ∈ (F.path (locationEquiv (locationEquiv.symm j))).edges
    have he := congrArg (fun j => (F.path j).edges) (locationEquiv.apply_symm_apply j)
    dsimp only at he
    rw [he]
    exact hj

#print axioms assembled_number_le_two
end MatchedFour

namespace CompleteFive
abbrev sizes : Fin 3 → ℕ := ![4,3,3]
def place : (k : Fin 3) → Fin (sizes k) → Fin 5
  | 0 => ![0,2,1,3]
  | 1 => ![0,1,4]
  | 2 => ![2,3,4]
def localSrc : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => src4
  | 1 => src3
  | 2 => src3
def localDst : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => dst4
  | 1 => dst3
  | 2 => dst3
lemma local_ne : ∀ k i, place k (localSrc k i) ≠ place k (localDst k i) := by decide
lemma local_src_surjective : ∀ k, Function.Surjective (localSrc k) := by
  intro k i
  fin_cases k <;> refine ⟨i,?_⟩ <;> fin_cases i <;> rfl
def location : Fin 10 → (Σ k : Fin 3, Fin (sizes k))
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨0,⟨1,by decide⟩⟩
  | 2 => ⟨0,⟨2,by decide⟩⟩
  | 3 => ⟨0,⟨3,by decide⟩⟩
  | 4 => ⟨1,⟨0,by decide⟩⟩
  | 5 => ⟨1,⟨1,by decide⟩⟩
  | 6 => ⟨1,⟨2,by decide⟩⟩
  | 7 => ⟨2,⟨0,by decide⟩⟩
  | 8 => ⟨2,⟨1,by decide⟩⟩
  | 9 => ⟨2,⟨2,by decide⟩⟩
lemma location_bijective : Function.Bijective location := by decide
noncomputable def locationEquiv := Equiv.ofBijective location location_bijective

lemma assembled_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 5 → V) (hinj : Function.Injective vertex)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  let F := assemble_segments sizes vertex hinj place localSrc localDst local_ne local_src_surjective
    root C hC S hdisC hpoints hmeet
  apply subdivision_number_le_two (reindexFamily F locationEquiv)
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · intro x y hxy
    obtain ⟨j,hj⟩ := assemble_segments_cover sizes vertex hinj place localSrc localDst local_ne local_src_surjective
      root C hC S hdisC hpoints hmeet hcover x y hxy
    refine ⟨locationEquiv.symm j,?_⟩
    change s(x,y) ∈ (F.path (locationEquiv (locationEquiv.symm j))).edges
    have he := congrArg (fun j => (F.path j).edges) (locationEquiv.apply_symm_apply j)
    dsimp only at he
    rw [he]
    exact hj

#print axioms assembled_number_le_two
end CompleteFive

namespace Octahedron
abbrev sizes : Fin 3 → ℕ := ![4,4,4]
def place : (k : Fin 3) → Fin (sizes k) → Fin 6
  | 0 => ![0,2,1,3]
  | 1 => ![0,4,1,5]
  | 2 => ![2,4,3,5]
def localSrc : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => src4
  | 1 => src4
  | 2 => src4
def localDst : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => dst4
  | 1 => dst4
  | 2 => dst4
lemma local_ne : ∀ k i, place k (localSrc k i) ≠ place k (localDst k i) := by decide
lemma local_src_surjective : ∀ k, Function.Surjective (localSrc k) := by
  intro k i
  fin_cases k <;> refine ⟨i,?_⟩ <;> fin_cases i <;> rfl
def location : Fin 12 → (Σ k : Fin 3, Fin (sizes k))
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨0,⟨1,by decide⟩⟩
  | 2 => ⟨0,⟨2,by decide⟩⟩
  | 3 => ⟨0,⟨3,by decide⟩⟩
  | 4 => ⟨1,⟨0,by decide⟩⟩
  | 5 => ⟨1,⟨1,by decide⟩⟩
  | 6 => ⟨1,⟨2,by decide⟩⟩
  | 7 => ⟨1,⟨3,by decide⟩⟩
  | 8 => ⟨2,⟨0,by decide⟩⟩
  | 9 => ⟨2,⟨1,by decide⟩⟩
  | 10 => ⟨2,⟨2,by decide⟩⟩
  | 11 => ⟨2,⟨3,by decide⟩⟩
lemma location_bijective : Function.Bijective location := by decide
noncomputable def locationEquiv := Equiv.ofBijective location location_bijective

lemma assembled_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 6 → V) (hinj : Function.Injective vertex)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  let F := assemble_segments sizes vertex hinj place localSrc localDst local_ne local_src_surjective
    root C hC S hdisC hpoints hmeet
  apply subdivision_number_le_two (reindexFamily F locationEquiv)
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · intro x y hxy
    obtain ⟨j,hj⟩ := assemble_segments_cover sizes vertex hinj place localSrc localDst local_ne local_src_surjective
      root C hC S hdisC hpoints hmeet hcover x y hxy
    refine ⟨locationEquiv.symm j,?_⟩
    change s(x,y) ∈ (F.path (locationEquiv (locationEquiv.symm j))).edges
    have he := congrArg (fun j => (F.path j).edges) (locationEquiv.apply_symm_apply j)
    dsimp only at he
    rw [he]
    exact hj

#print axioms assembled_number_le_two
end Octahedron

end Erdos184Work.ThreeCycleKernels

/-! Source block: ContactLayouts. -/

/-! Extracting the canonical junction layouts from unrooted cycle contacts. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleSegments
open RigidSwitching
set_option maxHeartbeats 1500000
variable {V W J : Type*} {G : SimpleGraph V}

/-- Segmentation depends on the edges, not on the root of the closed walk. -/
def Segmentation.transfer {a b : V} {c : G.Walk a a} {d : G.Walk b b}
    {vertex : W → V} {src dst : J → W} (S : Segmentation c vertex src dst)
    (he : ∀ e, e ∈ c.edges ↔ e ∈ d.edges) : Segmentation d vertex src dst where
  path := S.path
  isPath := S.isPath
  disjoint := S.disjoint
  cover e := (he e).symm.trans (S.cover e)

lemma two_segments_any {a u v : V} (c : G.Walk a a) (hc : c.IsCycle)
    (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v) :
    Nonempty (Segmentation c ![u,v] src2 dst2) := by
  obtain ⟨S⟩ := two_segments (c.rotate hu) (hc.rotate hu)
    ((c.mem_support_rotate_iff hu).mpr hv) huv
  exact ⟨S.transfer (fun e => (c.rotate_edges hu).mem_iff)⟩

lemma three_segments_any {a u v w : V} (c : G.Walk a a) (hc : c.IsCycle)
    (hu : u ∈ c.support) (hv : v ∈ c.support) (hw : w ∈ c.support) (huv : u ≠ v) :
    Nonempty (Segmentation c ![u,v,w] src3 dst3) := by
  obtain ⟨S⟩ := three_segments (c.rotate hu) (hc.rotate hu)
    ((c.mem_support_rotate_iff hu).mpr hv) ((c.mem_support_rotate_iff hu).mpr hw) huv
  exact ⟨S.transfer (fun e => (c.rotate_edges hu).mem_iff)⟩

lemma four_segments_of_rigid_any [Fintype V] (hrig : Rigidity.CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    {a b w u v x z : V} {c : G.Walk a a} {d : G.Walk b b} {t : G.Walk w w}
    (hc : c.IsCycle) (hd : d.IsCycle) (ht : t.IsCycle) (huv : u ≠ v)
    (huc : u ∈ c.support) (hud : u ∈ d.support)
    (hvc : v ∈ c.support) (hvd : v ∈ d.support)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hinter : ∀ y, y ∈ c.support → y ∈ d.support → y = u ∨ y = v)
    (hut : u ∉ t.support) (hvt : v ∉ t.support)
    (hmeet : ∃ y, y ∈ d.support ∧ y ∈ t.support)
    (hxz : x ≠ z) (hxc : x ∈ c.support) (hzc : z ∈ c.support)
    (hxt : x ∈ t.support) (hzt : z ∈ t.support) :
    Nonempty (Segmentation c ![u,x,v,z] src4 dst4) := by
  have ec (e) : e ∈ (c.rotate huc).edges ↔ e ∈ c.edges := (c.rotate_edges huc).mem_iff
  have ed (e) : e ∈ (d.rotate hud).edges ↔ e ∈ d.edges := (d.rotate_edges hud).mem_iff
  have sc (y) : y ∈ (c.rotate huc).support ↔ y ∈ c.support := c.mem_support_rotate_iff huc
  have sd (y) : y ∈ (d.rotate hud).support ↔ y ∈ d.support := d.mem_support_rotate_iff hud
  obtain ⟨S⟩ := four_segments_of_rigid hrig heven (hc.rotate huc) (hd.rotate hud) ht huv
    ((sc v).mpr hvc) ((sd v).mpr hvd)
    (disjoint_mono hcd (fun e => (ec e).mp) (fun e => (ed e).mp))
    (disjoint_mono hct (fun e => (ec e).mp) (List.Subset.refl _))
    (disjoint_mono hdt (fun e => (ed e).mp) (List.Subset.refl _))
    (fun y hy hz => hinter y ((sc y).mp hy) ((sd y).mp hz)) hut hvt
    (hmeet.imp (fun y h => ⟨(sd y).mpr h.1,h.2⟩)) hxz ((sc x).mpr hxc) ((sc z).mpr hzc) hxt hzt
  exact ⟨S.transfer ec⟩

#print axioms four_segments_of_rigid_any
end Erdos184Work.CycleSegments

namespace Erdos184Work.CycleSegments
variable {V W K : Type*} {G : SimpleGraph V}

/-- An injective list of all junction vertices, with their exact piece incidences. -/
structure ContactLayout (m : K → ℕ) (place : ∀ k, Fin (m k) → W)
    (vertex : W → V) (root : K → V) (C : ∀ k, G.Walk (root k) (root k)) : Prop where
  injective : Function.Injective vertex
  points : ∀ k w, vertex w ∈ (C k).support ↔ ∃ i, place k i = w
  meet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x

namespace ContactLayout
variable {m : K → ℕ} {place : ∀ k, Fin (m k) → W}
    {vertex : W → V} {root : K → V} {C : ∀ k, G.Walk (root k) (root k)}
    (L : ContactLayout m place vertex root C)
include L
lemma mem {k : K} {w : W} (h : ∃ i, place k i = w) : vertex w ∈ (C k).support :=
  (L.points k w).mpr h
lemma not_mem {k : K} {w : W} (h : ¬ ∃ i, place k i = w) : vertex w ∉ (C k).support :=
  fun hw => h ((L.points k w).mp hw)
lemma ne {w z : W} (h : w ≠ z) : vertex w ≠ vertex z := fun he => h (L.injective he)
lemma inter_two {k l : K} {u v : W} (hkl : k ≠ l)
    (h : ∀ w, (∃ i, place k i = w) → (∃ j, place l j = w) → w = u ∨ w = v)
    (x : V) (hx : x ∈ (C k).support) (hy : x ∈ (C l).support) :
    x = vertex u ∨ x = vertex v := by
  obtain ⟨w,rfl⟩ := L.meet k l hkl x hx hy
  exact (h w ((L.points k w).mp hx) ((L.points l w).mp hy)).imp (congrArg vertex) (congrArg vertex)
end ContactLayout
end Erdos184Work.CycleSegments
-- Generated layout extraction
namespace Erdos184Work.ThreeCycleKernels
open CycleSegments
set_option maxHeartbeats 1500000
namespace DoubleTriangle
lemma contact_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (vertex : Fin 3 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout sizes place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  have hs0 : Nonempty (Segmentation (C 0) (vertex ∘ place 0) (localSrc 0) (localDst 0)) := by
    have hv : vertex ∘ place 0 = ![vertex 0,vertex 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 0) ![vertex 0,vertex 1] src2 dst2)
    exact two_segments_any (C 0) (hC 0) (L.mem (k := 0) (w := 0) (by decide)) (L.mem (k := 0) (w := 1) (by decide)) (L.ne (by decide : (0 : Fin 3) ≠ 1))
  have hs1 : Nonempty (Segmentation (C 1) (vertex ∘ place 1) (localSrc 1) (localDst 1)) := by
    have hv : vertex ∘ place 1 = ![vertex 0,vertex 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 1) ![vertex 0,vertex 2] src2 dst2)
    exact two_segments_any (C 1) (hC 1) (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 1) (w := 2) (by decide)) (L.ne (by decide : (0 : Fin 3) ≠ 2))
  have hs2 : Nonempty (Segmentation (C 2) (vertex ∘ place 2) (localSrc 2) (localDst 2)) := by
    have hv : vertex ∘ place 2 = ![vertex 1,vertex 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 2) ![vertex 1,vertex 2] src2 dst2)
    exact two_segments_any (C 2) (hC 2) (L.mem (k := 2) (w := 1) (by decide)) (L.mem (k := 2) (w := 2) (by decide)) (L.ne (by decide : (1 : Fin 3) ≠ 2))
  obtain ⟨S0⟩ := hs0
  obtain ⟨S1⟩ := hs1
  obtain ⟨S2⟩ := hs2
  let S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k) :=
    Fin.cases S0 (Fin.cases S1 (Fin.cases S2 (fun i => Fin.elim0 i)))
  exact assembled_number_le_two vertex L.injective root C hC S hdisC
    (fun w k => (L.points k w).mp) L.meet hcover
#print axioms contact_number_le_two
end DoubleTriangle

namespace MatchedFour
lemma contact_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (vertex : Fin 4 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout sizes place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  have hs0 : Nonempty (Segmentation (C 0) (vertex ∘ place 0) (localSrc 0) (localDst 0)) := by
    have hv : vertex ∘ place 0 = ![vertex 0,vertex 1,vertex 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 0) ![vertex 0,vertex 1,vertex 2] src3 dst3)
    exact three_segments_any (C 0) (hC 0) (L.mem (k := 0) (w := 0) (by decide)) (L.mem (k := 0) (w := 1) (by decide)) (L.mem (k := 0) (w := 2) (by decide)) (L.ne (by decide : (0 : Fin 4) ≠ 1))
  have hs1 : Nonempty (Segmentation (C 1) (vertex ∘ place 1) (localSrc 1) (localDst 1)) := by
    have hv : vertex ∘ place 1 = ![vertex 0,vertex 1,vertex 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 1) ![vertex 0,vertex 1,vertex 3] src3 dst3)
    exact three_segments_any (C 1) (hC 1) (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 1) (w := 1) (by decide)) (L.mem (k := 1) (w := 3) (by decide)) (L.ne (by decide : (0 : Fin 4) ≠ 1))
  have hs2 : Nonempty (Segmentation (C 2) (vertex ∘ place 2) (localSrc 2) (localDst 2)) := by
    have hv : vertex ∘ place 2 = ![vertex 2,vertex 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 2) ![vertex 2,vertex 3] src2 dst2)
    exact two_segments_any (C 2) (hC 2) (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide)) (L.ne (by decide : (2 : Fin 4) ≠ 3))
  obtain ⟨S0⟩ := hs0
  obtain ⟨S1⟩ := hs1
  obtain ⟨S2⟩ := hs2
  let S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k) :=
    Fin.cases S0 (Fin.cases S1 (Fin.cases S2 (fun i => Fin.elim0 i)))
  exact assembled_number_le_two vertex L.injective root C hC S hdisC
    (fun w k => (L.points k w).mp) L.meet hcover
#print axioms contact_number_le_two
end MatchedFour

namespace CompleteFive
lemma contact_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (vertex : Fin 5 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout sizes place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  have hs0 : Nonempty (Segmentation (C 0) (vertex ∘ place 0) (localSrc 0) (localDst 0)) := by
    have hv : vertex ∘ place 0 = ![vertex 0,vertex 2,vertex 1,vertex 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 0) ![vertex 0,vertex 2,vertex 1,vertex 3] src4 dst4)
    exact four_segments_of_rigid_any hrig heven (hC 0) (hC 1) (hC 2)
      (L.ne (by decide : (0 : Fin 5) ≠ 1))
      (L.mem (k := 0) (w := 0) (by decide)) (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 0) (w := 1) (by decide)) (L.mem (k := 1) (w := 1) (by decide))
      (hdisC 0 1 (by decide)) (hdisC 0 2 (by decide)) (hdisC 1 2 (by decide))
      (L.inter_two (k := 0) (l := 1) (u := 0) (v := 1) (by decide) (by decide))
      (L.not_mem (k := 2) (w := 0) (by decide)) (L.not_mem (k := 2) (w := 1) (by decide))
      ⟨vertex 4,(L.mem (k := 1) (w := 4) (by decide)),(L.mem (k := 2) (w := 4) (by decide))⟩
      (L.ne (by decide : (2 : Fin 5) ≠ 3))
      (L.mem (k := 0) (w := 2) (by decide)) (L.mem (k := 0) (w := 3) (by decide)) (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide))
  have hs1 : Nonempty (Segmentation (C 1) (vertex ∘ place 1) (localSrc 1) (localDst 1)) := by
    have hv : vertex ∘ place 1 = ![vertex 0,vertex 1,vertex 4] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 1) ![vertex 0,vertex 1,vertex 4] src3 dst3)
    exact three_segments_any (C 1) (hC 1) (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 1) (w := 1) (by decide)) (L.mem (k := 1) (w := 4) (by decide)) (L.ne (by decide : (0 : Fin 5) ≠ 1))
  have hs2 : Nonempty (Segmentation (C 2) (vertex ∘ place 2) (localSrc 2) (localDst 2)) := by
    have hv : vertex ∘ place 2 = ![vertex 2,vertex 3,vertex 4] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 2) ![vertex 2,vertex 3,vertex 4] src3 dst3)
    exact three_segments_any (C 2) (hC 2) (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide)) (L.mem (k := 2) (w := 4) (by decide)) (L.ne (by decide : (2 : Fin 5) ≠ 3))
  obtain ⟨S0⟩ := hs0
  obtain ⟨S1⟩ := hs1
  obtain ⟨S2⟩ := hs2
  let S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k) :=
    Fin.cases S0 (Fin.cases S1 (Fin.cases S2 (fun i => Fin.elim0 i)))
  exact assembled_number_le_two vertex L.injective root C hC S hdisC
    (fun w k => (L.points k w).mp) L.meet hcover
#print axioms contact_number_le_two
end CompleteFive

namespace Octahedron
lemma contact_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (vertex : Fin 6 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout sizes place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  have hs0 : Nonempty (Segmentation (C 0) (vertex ∘ place 0) (localSrc 0) (localDst 0)) := by
    have hv : vertex ∘ place 0 = ![vertex 0,vertex 2,vertex 1,vertex 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 0) ![vertex 0,vertex 2,vertex 1,vertex 3] src4 dst4)
    exact four_segments_of_rigid_any hrig heven (hC 0) (hC 1) (hC 2)
      (L.ne (by decide : (0 : Fin 6) ≠ 1))
      (L.mem (k := 0) (w := 0) (by decide)) (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 0) (w := 1) (by decide)) (L.mem (k := 1) (w := 1) (by decide))
      (hdisC 0 1 (by decide)) (hdisC 0 2 (by decide)) (hdisC 1 2 (by decide))
      (L.inter_two (k := 0) (l := 1) (u := 0) (v := 1) (by decide) (by decide))
      (L.not_mem (k := 2) (w := 0) (by decide)) (L.not_mem (k := 2) (w := 1) (by decide))
      ⟨vertex 4,(L.mem (k := 1) (w := 4) (by decide)),(L.mem (k := 2) (w := 4) (by decide))⟩
      (L.ne (by decide : (2 : Fin 6) ≠ 3))
      (L.mem (k := 0) (w := 2) (by decide)) (L.mem (k := 0) (w := 3) (by decide)) (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide))
  have hs1 : Nonempty (Segmentation (C 1) (vertex ∘ place 1) (localSrc 1) (localDst 1)) := by
    have hv : vertex ∘ place 1 = ![vertex 0,vertex 4,vertex 1,vertex 5] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 1) ![vertex 0,vertex 4,vertex 1,vertex 5] src4 dst4)
    exact four_segments_of_rigid_any hrig heven (hC 1) (hC 0) (hC 2)
      (L.ne (by decide : (0 : Fin 6) ≠ 1))
      (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 0) (w := 0) (by decide)) (L.mem (k := 1) (w := 1) (by decide)) (L.mem (k := 0) (w := 1) (by decide))
      (hdisC 1 0 (by decide)) (hdisC 1 2 (by decide)) (hdisC 0 2 (by decide))
      (L.inter_two (k := 1) (l := 0) (u := 0) (v := 1) (by decide) (by decide))
      (L.not_mem (k := 2) (w := 0) (by decide)) (L.not_mem (k := 2) (w := 1) (by decide))
      ⟨vertex 2,(L.mem (k := 0) (w := 2) (by decide)),(L.mem (k := 2) (w := 2) (by decide))⟩
      (L.ne (by decide : (4 : Fin 6) ≠ 5))
      (L.mem (k := 1) (w := 4) (by decide)) (L.mem (k := 1) (w := 5) (by decide)) (L.mem (k := 2) (w := 4) (by decide)) (L.mem (k := 2) (w := 5) (by decide))
  have hs2 : Nonempty (Segmentation (C 2) (vertex ∘ place 2) (localSrc 2) (localDst 2)) := by
    have hv : vertex ∘ place 2 = ![vertex 2,vertex 4,vertex 3,vertex 5] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 2) ![vertex 2,vertex 4,vertex 3,vertex 5] src4 dst4)
    exact four_segments_of_rigid_any hrig heven (hC 2) (hC 0) (hC 1)
      (L.ne (by decide : (2 : Fin 6) ≠ 3))
      (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 0) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide)) (L.mem (k := 0) (w := 3) (by decide))
      (hdisC 2 0 (by decide)) (hdisC 2 1 (by decide)) (hdisC 0 1 (by decide))
      (L.inter_two (k := 2) (l := 0) (u := 2) (v := 3) (by decide) (by decide))
      (L.not_mem (k := 1) (w := 2) (by decide)) (L.not_mem (k := 1) (w := 3) (by decide))
      ⟨vertex 0,(L.mem (k := 0) (w := 0) (by decide)),(L.mem (k := 1) (w := 0) (by decide))⟩
      (L.ne (by decide : (4 : Fin 6) ≠ 5))
      (L.mem (k := 2) (w := 4) (by decide)) (L.mem (k := 2) (w := 5) (by decide)) (L.mem (k := 1) (w := 4) (by decide)) (L.mem (k := 1) (w := 5) (by decide))
  obtain ⟨S0⟩ := hs0
  obtain ⟨S1⟩ := hs1
  obtain ⟨S2⟩ := hs2
  let S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k) :=
    Fin.cases S0 (Fin.cases S1 (Fin.cases S2 (fun i => Fin.elim0 i)))
  exact assembled_number_le_two vertex L.injective root C hC S hdisC
    (fun w k => (L.points k w).mp) L.meet hcover
#print axioms contact_number_le_two
end Octahedron

end Erdos184Work.ThreeCycleKernels

/-! Source block: IndexedCycles. -/

/-! Indexed cycle unions and restriction to their edges. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.IndexedCycles
open MaximumCycles RigidSwitching
set_option maxHeartbeats 1500000
variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V}

noncomputable def image (root : I → V) (C : ∀ i, G.Walk (root i) (root i)) : Finset G.Subgraph :=
  Finset.univ.image (fun i => (C i).toSubgraph)

variable (root : I → V) (C : ∀ i, G.Walk (root i) (root i))
    (hC : ∀ i, (C i).IsCycle) (hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges)

include hC in
lemma regular : ∀ H ∈ image root C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  rintro H hH
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
  exact cycle_coe_regular G (hC i)

include hd in
lemma disjoint : Set.PairwiseDisjoint (image root C : Set G.Subgraph) (fun H => H.edgeSet) := by
  intro H hH K hK hne
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
  apply Set.disjoint_left.mpr
  intro e he hf
  exact List.disjoint_left.mp (hd i j (fun he => hne (by subst j; rfl)))
    ((C i).mem_edges_toSubgraph.mp he) ((C j).mem_edges_toSubgraph.mp hf)

include hC hd in
lemma injective : Function.Injective (fun i => (C i).toSubgraph) := by
  intro i j he
  dsimp only at he
  have heE := congrArg (fun H : G.Subgraph => H.edgeSet) he
  dsimp only at heE
  by_contra hne
  have hnon := (hC i).not_nil
  have hmem : s(root i,(C i).snd) ∈ (C i).toSubgraph.edgeSet := (C i).toSubgraph_adj_snd hnon
  exact List.disjoint_left.mp (hd i j hne) ((C i).mem_edges_toSubgraph.mp hmem)
    ((C j).mem_edges_toSubgraph.mp (by rw [← heE]; exact hmem))

include hC hd in
lemma card : (image root C).card = Fintype.card I := by
  rw [image,Finset.card_image_of_injective _ (injective root C hC hd),Finset.card_univ]

include hC hd in
lemma number (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v)) :
    Critical.number (subfamilyGraph (image root C)) = Fintype.card I := by
  rw [rigid_subfamily_number hrig heven (image root C) (regular root C hC) (disjoint root C hd),
    card root C hC hd]

include hC hd in
lemma even : ∀ v, Even ((subfamilyGraph (image root C)).degree v) :=
  cycle_subfamily_even (image root C) (regular root C hC) (disjoint root C hd)

include hC hd in
lemma rigid (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v)) :
    Rigidity.CycleRigid (subfamilyGraph (image root C)) :=
  rigid_subfamily hrig heven (image root C) (regular root C hC) (disjoint root C hd)

lemma edges (e : Sym2 V) : e ∈ (subfamilyGraph (image root C)).edgeSet ↔ ∃ i, e ∈ (C i).edges := by
  rw [subfamilyGraph_edges]
  simp only [Set.mem_iUnion,exists_prop,image,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨H,⟨i,rfl⟩,he⟩
    exact ⟨i,(C i).mem_edges_toSubgraph.mp he⟩
  · rintro ⟨i,he⟩
    exact ⟨(C i).toSubgraph,⟨i,rfl⟩,(C i).mem_edges_toSubgraph.mpr he⟩

lemma edges_subset (i : I) : ∀ e ∈ (C i).edges, e ∈ (subfamilyGraph (image root C)).edgeSet :=
  fun e he => (edges root C e).mpr ⟨i,he⟩

noncomputable def restrict (i : I) : (subfamilyGraph (image root C)).Walk (root i) (root i) :=
  (C i).transfer _ (edges_subset root C i)

lemma restrict_edges (i : I) : (restrict root C i).edges = (C i).edges := Walk.edges_transfer _ _
lemma restrict_support (i : I) : (restrict root C i).support = (C i).support := Walk.support_transfer _ _
include hC in
lemma restrict_cycle (i : I) : (restrict root C i).IsCycle := (hC i).transfer _
include hd in
lemma restrict_disjoint : ∀ i j, i ≠ j → (restrict root C i).edges.Disjoint (restrict root C j).edges := by
  simpa only [restrict_edges] using hd
lemma restrict_cover : ∀ x y, (subfamilyGraph (image root C)).Adj x y →
    ∃ i, s(x,y) ∈ (restrict root C i).edges := by
  intro x y hxy
  simpa only [restrict_edges] using (edges root C s(x,y)).mp hxy

include hC hd in
lemma number_of_cover (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (hcover : ∀ x y, G.Adj x y → ∃ i, s(x,y) ∈ (C i).edges) :
    Critical.number G = Fintype.card I := by
  have heq : subfamilyGraph (image root C) = G := by
    apply le_antisymm (subfamilyGraph_le _)
    intro x y hxy
    exact (edges root C s(x,y)).mpr (hcover x y hxy)
  rw [← heq]
  exact number root C hC hd hrig heven

#print axioms number_of_cover
#print axioms restrict_cycle
end Erdos184Work.IndexedCycles

/-! Source block: TriangleContacts. -/

/-! Strong three-cycle contact rings cannot occur in an even rigid graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.TriangleContacts
open RigidSwitching CycleSegments
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma intersection_eq_pair (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {a b x : V} (c : G.Walk a a) (d : G.Walk b b) (hc : c.IsCycle) (hd : d.IsCycle)
    (hdis : c.edges.Disjoint d.edges) (hxc : x ∈ c.support) (hxd : x ∈ d.support) :
    ∃ y, ∀ z, (z ∈ c.support ∧ z ∈ d.support) ↔ z = x ∨ z = y := by
  by_cases hh : ∃ y, y ∈ c.support ∧ y ∈ d.support ∧ y ≠ x
  · obtain ⟨y,hyc,hyd,hyx⟩ := hh
    refine ⟨y,fun z => ⟨?_,?_⟩⟩
    · rintro ⟨hzc,hzd⟩
      by_contra hn
      push_neg at hn
      exact rigid_no_three_common_vertices hrig heven c d hc hd hdis hyx.symm hn.1.symm hn.2.symm
        hxc hyc hzc hxd hyd hzd
    · rintro (rfl | rfl)
      · exact ⟨hxc,hxd⟩
      · exact ⟨hyc,hyd⟩
  · refine ⟨x,fun z => ⟨?_,?_⟩⟩
    · intro hz
      by_cases he : z = x
      · exact Or.inl he
      · exact (hh ⟨z,hz.1,hz.2,he⟩).elim
    · rintro (rfl | rfl) <;> exact ⟨hxc,hxd⟩

lemma common_vertex_impossible (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {a b c₀ u v x y : V} (c : G.Walk a a) (d : G.Walk b b) (t : G.Walk c₀ c₀)
    (hc : c.IsCycle) (hd : d.IsCycle) (ht : t.IsCycle)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (huc : u ∈ c.support) (hud : u ∈ d.support) (hut : u ∈ t.support)
    (hvc : v ∈ c.support) (hvd : v ∈ d.support) (hvt : v ∉ t.support)
    (hxc : x ∈ c.support) (hxt : x ∈ t.support) (hxd : x ∉ d.support)
    (hyd : y ∈ d.support) (hyt : y ∈ t.support) (hyc : y ∉ c.support) : False := by
  have huv : u ≠ v := fun he => hvt (he ▸ hut)
  have hinter (z) (hzc : z ∈ c.support) (hzd : z ∈ d.support) : z = u ∨ z = v := by
    by_contra hn
    push_neg at hn
    exact rigid_no_three_common_vertices hrig heven c d hc hd hcd huv hn.1.symm hn.2.symm
      huc hvc hzc hud hvd hzd
  have ec (e) : e ∈ (c.rotate huc).edges ↔ e ∈ c.edges := (c.rotate_edges huc).mem_iff
  have ed (e) : e ∈ (d.rotate hud).edges ↔ e ∈ d.edges := (d.rotate_edges hud).mem_iff
  obtain ⟨r,s,hr,hs,hrs,hcover,hxr,hyr⟩ := two_cycle_switch_through
    (c.rotate huc) (d.rotate hud) (hc.rotate huc) (hd.rotate hud) huv
    ((c.mem_support_rotate_iff huc).mpr hvc) ((d.mem_support_rotate_iff hud).mpr hvd)
    (disjoint_mono hcd (fun e => (ec e).mp) (fun e => (ed e).mp))
    (fun z hz hz' => hinter z ((c.mem_support_rotate_iff huc).mp hz) ((d.mem_support_rotate_iff hud).mp hz'))
    ((c.mem_support_rotate_iff huc).mpr hxc) ((d.mem_support_rotate_iff hud).mpr hyd)
  have hrt : r.edges.Disjoint t.edges := by
    apply List.disjoint_left.mpr
    intro e her het
    rcases (hcover e).mp (Or.inl her) with he | he
    · exact List.disjoint_left.mp hct ((ec e).mp he) het
    · exact List.disjoint_left.mp hdt ((ed e).mp he) het
  exact rigid_no_three_common_vertices hrig heven r t hr ht hrt
    (fun h : u = x => hxd (h ▸ hud)) (fun h : u = y => hyc (h ▸ huc))
    (fun h : x = y => hxd (h.symm ▸ hyd)) r.start_mem_support hxr hyr hut hxt hyt

abbrev first : Fin 3 → Fin 3 := ![0,0,1]
abbrev second : Fin 3 → Fin 3 := ![1,2,2]
abbrev missing : Fin 3 → Fin 3 := ![2,1,0]

lemma point_incidence (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (p : Fin 3 → Fin 2 → V)
    (hp : ∀ g x, (x ∈ (C (first g)).support ∧ x ∈ (C (second g)).support) ↔ x = p g 0 ∨ x = p g 1)
    (hnt : ∀ x, ¬ (x ∈ (C 0).support ∧ x ∈ (C 1).support ∧ x ∈ (C 2).support)) :
    ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g := by
  intro g i k
  have hb := (hp g (p g i)).mpr (by fin_cases i <;> simp)
  have hn : p g i ∉ (C (missing g)).support := by
    intro hm
    apply hnt (p g i)
    fin_cases g
    · exact ⟨hb.1,hb.2,hm⟩
    · exact ⟨hb.1,hm,hb.2⟩
    · exact ⟨hm,hb.1,hb.2⟩
  constructor
  · intro hk he
    exact hn (he ▸ hk)
  · intro hk
    have hh : ∀ g k, k ≠ missing g → k = first g ∨ k = second g := by decide
    rcases hh g k hk with rfl | rfl
    · exact hb.1
    · exact hb.2

lemma point_meet (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (p : Fin 3 → Fin 2 → V)
    (hp : ∀ g x, (x ∈ (C (first g)).support ∧ x ∈ (C (second g)).support) ↔ x = p g 0 ∨ x = p g 1) :
    ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x := by
  intro k l hkl x hx hy
  have hcase : ∀ k l, k ≠ l → ∃ g, (k = first g ∧ l = second g) ∨ (l = first g ∧ k = second g) := by decide
  obtain ⟨g,hg⟩ := hcase k l hkl
  have hi : x = p g 0 ∨ x = p g 1 := by
    apply (hp g x).mp
    rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hx,hy⟩
    · exact ⟨hy,hx⟩
  exact hi.elim (fun h => ⟨g,0,h.symm⟩) (fun h => ⟨g,1,h.symm⟩)

lemma point_ne_of_group_ne (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    {g h : Fin 3} {i j : Fin 2} (hgh : g ≠ h) : p g i ≠ p h j := by
  intro he
  have hinj : Function.Injective missing := by decide
  have hg := (hi g i (missing h)).mpr (fun h => hgh (hinj h).symm)
  rw [he] at hg
  exact (hi h j (missing h)).mp hg rfl

#print axioms common_vertex_impossible
end Erdos184Work.TriangleContacts

/-! Source block: TrianglePatterns. -/

/-! Exhaustive classification by the three pair-contact multiplicities, each one or two. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.TriangleContacts
open CycleSegments ThreeCycleKernels
set_option maxHeartbeats 1500000
set_option linter.unusedVariables false
lemma pattern_000 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 = p 0 1)
    (h1 : p 1 0 = p 1 1)
    (h2 : p 2 0 = p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![0,1,2] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 3 → V := ![p 0 0,p 1 0,p 2 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · rfl
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨0,h0⟩
    · exact ⟨1,rfl⟩
    · exact ⟨1,h1⟩
    · exact ⟨2,rfl⟩
    · exact ⟨2,h2⟩
  have L : ContactLayout DoubleTriangle.sizes DoubleTriangle.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, DoubleTriangle.place 0 j = 0
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, DoubleTriangle.place 0 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, DoubleTriangle.place 0 j = 2
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, DoubleTriangle.place 1 j = 0
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, DoubleTriangle.place 1 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, DoubleTriangle.place 1 j = 2
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, DoubleTriangle.place 2 j = 0
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, DoubleTriangle.place 2 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, DoubleTriangle.place 2 j = 2
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply DoubleTriangle.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_000

lemma pattern_001 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 = p 0 1)
    (h1 : p 1 0 = p 1 1)
    (h2 : p 2 0 ≠ p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![1,2,0] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 4 → V := ![p 2 0,p 2 1,p 0 0,p 1 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 2 0 = p 2 1 at he
      exact (h2 he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 2 0 at he
      exact (h2 he.symm).elim
    · rfl
    · change p 2 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · rfl
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨2,rfl⟩
    · exact ⟨2,h0⟩
    · exact ⟨3,rfl⟩
    · exact ⟨3,h1⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  have L : ContactLayout MatchedFour.sizes MatchedFour.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 0 j = 0
        rw [hi]
        decide
      · change p 2 1 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 0 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 0 j = 2
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 0 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 0
        rw [hi]
        decide
      · change p 2 1 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 2
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 2 j = 0
        rw [hi]
        decide
      · change p 2 1 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 2 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 2 j = 2
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 2 j = 3
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply MatchedFour.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_001

lemma pattern_010 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 = p 0 1)
    (h1 : p 1 0 ≠ p 1 1)
    (h2 : p 2 0 = p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![0,2,1] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 4 → V := ![p 1 0,p 1 1,p 0 0,p 2 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 1 0 = p 1 1 at he
      exact (h1 he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 1 0 at he
      exact (h1 he.symm).elim
    · rfl
    · change p 1 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · rfl
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨2,rfl⟩
    · exact ⟨2,h0⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨3,h2⟩
  have L : ContactLayout MatchedFour.sizes MatchedFour.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 3
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 3
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 2 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 2 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 2 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 2 j = 3
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply MatchedFour.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_010

lemma pattern_011 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 = p 0 1)
    (h1 : p 1 0 ≠ p 1 1)
    (h2 : p 2 0 ≠ p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![2,0,1] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 5 → V := ![p 1 0,p 1 1,p 2 0,p 2 1,p 0 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 1 0 = p 1 1 at he
      exact (h1 he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 1 0 at he
      exact (h1 he.symm).elim
    · rfl
    · change p 1 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · rfl
    · change p 2 0 = p 2 1 at he
      exact (h2 he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 2 0 at he
      exact (h2 he.symm).elim
    · rfl
    · change p 2 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨4,rfl⟩
    · exact ⟨4,h0⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  have L : ContactLayout CompleteFive.sizes CompleteFive.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 0 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 0 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 0 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 0 j = 3
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 0 j = 4
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 3
        rw [hi]
        decide
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 4
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 2 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 2 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 2 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 2 j = 3
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 2 j = 4
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply CompleteFive.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_011

lemma pattern_100 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 ≠ p 0 1)
    (h1 : p 1 0 = p 1 1)
    (h2 : p 2 0 = p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![0,1,2] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 4 → V := ![p 0 0,p 0 1,p 1 0,p 2 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 0 0 = p 0 1 at he
      exact (h0 he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 0 0 at he
      exact (h0 he.symm).elim
    · rfl
    · change p 0 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · rfl
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨2,h1⟩
    · exact ⟨3,rfl⟩
    · exact ⟨3,h2⟩
  have L : ContactLayout MatchedFour.sizes MatchedFour.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 3
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 1 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 1 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 1 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 1 j = 3
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 2 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 2 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 2 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 2 j = 3
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply MatchedFour.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_100

lemma pattern_101 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 ≠ p 0 1)
    (h1 : p 1 0 = p 1 1)
    (h2 : p 2 0 ≠ p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![1,0,2] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 5 → V := ![p 0 0,p 0 1,p 2 0,p 2 1,p 1 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 0 0 = p 0 1 at he
      exact (h0 he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 0 0 at he
      exact (h0 he.symm).elim
    · rfl
    · change p 0 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · rfl
    · change p 2 0 = p 2 1 at he
      exact (h2 he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 2 0 at he
      exact (h2 he.symm).elim
    · rfl
    · change p 2 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨4,h1⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  have L : ContactLayout CompleteFive.sizes CompleteFive.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 0 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 0 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 0 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 0 j = 3
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 0 j = 4
        rw [hi]
        decide
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 3
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 4
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 3
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 4
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply CompleteFive.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_101

lemma pattern_110 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 ≠ p 0 1)
    (h1 : p 1 0 ≠ p 1 1)
    (h2 : p 2 0 = p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![0,1,2] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 5 → V := ![p 0 0,p 0 1,p 1 0,p 1 1,p 2 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 0 0 = p 0 1 at he
      exact (h0 he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 0 0 at he
      exact (h0 he.symm).elim
    · rfl
    · change p 0 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · rfl
    · change p 1 0 = p 1 1 at he
      exact (h1 he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 1 0 at he
      exact (h1 he.symm).elim
    · rfl
    · change p 1 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨4,h2⟩
  have L : ContactLayout CompleteFive.sizes CompleteFive.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 0 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 0 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 0 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 0 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 0 j = 4
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 1 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 1 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 1 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 1 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 1 j = 4
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 4
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply CompleteFive.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_110

lemma pattern_111 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 ≠ p 0 1)
    (h1 : p 1 0 ≠ p 1 1)
    (h2 : p 2 0 ≠ p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![0,1,2] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 6 → V := ![p 0 0,p 0 1,p 1 0,p 1 1,p 2 0,p 2 1]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 0 0 = p 0 1 at he
      exact (h0 he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 0 0 at he
      exact (h0 he.symm).elim
    · rfl
    · change p 0 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · rfl
    · change p 1 0 = p 1 1 at he
      exact (h1 he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 1 0 at he
      exact (h1 he.symm).elim
    · rfl
    · change p 1 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · rfl
    · change p 2 0 = p 2 1 at he
      exact (h2 he).elim
    · change p 2 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 2 0 at he
      exact (h2 he.symm).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨5,rfl⟩
  have L : ContactLayout Octahedron.sizes Octahedron.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 4
        rw [hi]
        decide
      · change p 2 1 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 5
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 4
        rw [hi]
        decide
      · change p 2 1 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 5
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 4
        rw [hi]
        decide
      · change p 2 1 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 5
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply Octahedron.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_111

lemma patterns_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    : Critical.number G ≤ 2 := by
  by_cases h0 : p 0 0 = p 0 1
  · by_cases h1 : p 1 0 = p 1 1
    · by_cases h2 : p 2 0 = p 2 1
      · exact pattern_000 hrig heven root C hC hd hcover p hi hm h0 h1 h2
      · exact pattern_001 hrig heven root C hC hd hcover p hi hm h0 h1 h2
    · by_cases h2 : p 2 0 = p 2 1
      · exact pattern_010 hrig heven root C hC hd hcover p hi hm h0 h1 h2
      · exact pattern_011 hrig heven root C hC hd hcover p hi hm h0 h1 h2
  · by_cases h1 : p 1 0 = p 1 1
    · by_cases h2 : p 2 0 = p 2 1
      · exact pattern_100 hrig heven root C hC hd hcover p hi hm h0 h1 h2
      · exact pattern_101 hrig heven root C hC hd hcover p hi hm h0 h1 h2
    · by_cases h2 : p 2 0 = p 2 1
      · exact pattern_110 hrig heven root C hC hd hcover p hi hm h0 h1 h2
      · exact pattern_111 hrig heven root C hC hd hcover p hi hm h0 h1 h2
#print axioms patterns_bound
end Erdos184Work.TriangleContacts

/-! Source block: TriangleExclusion. -/

/-! The strong incidence-triangle obstruction for rigid cycle families. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.TriangleContacts
open CycleSegments RigidSwitching
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma no_triangle_of_cover (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    {x y z : V}
    (hx0 : x ∈ (C 0).support) (hx1 : x ∈ (C 1).support) (hx2 : x ∉ (C 2).support)
    (hy0 : y ∈ (C 0).support) (hy2 : y ∈ (C 2).support) (hy1 : y ∉ (C 1).support)
    (hz1 : z ∈ (C 1).support) (hz2 : z ∈ (C 2).support) (hz0 : z ∉ (C 0).support) : False := by
  have hnt (u) : ¬ (u ∈ (C 0).support ∧ u ∈ (C 1).support ∧ u ∈ (C 2).support) := by
    rintro ⟨hu0,hu1,hu2⟩
    exact common_vertex_impossible hrig heven (C 0) (C 1) (C 2) (hC 0) (hC 1) (hC 2)
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide))
      hu0 hu1 hu2 hx0 hx1 hx2 hy0 hy2 hy1 hz1 hz2 hz0
  obtain ⟨a,ha⟩ := intersection_eq_pair hrig heven (C 0) (C 1) (hC 0) (hC 1) (hd 0 1 (by decide)) hx0 hx1
  obtain ⟨b,hb⟩ := intersection_eq_pair hrig heven (C 0) (C 2) (hC 0) (hC 2) (hd 0 2 (by decide)) hy0 hy2
  obtain ⟨c,hc⟩ := intersection_eq_pair hrig heven (C 1) (C 2) (hC 1) (hC 2) (hd 1 2 (by decide)) hz1 hz2
  let p : Fin 3 → Fin 2 → V := ![![x,a],![y,b],![z,c]]
  have hp : ∀ g u, (u ∈ (C (first g)).support ∧ u ∈ (C (second g)).support) ↔ u = p g 0 ∨ u = p g 1 := by
    intro g u
    fin_cases g
    · exact ha u
    · exact hb u
    · exact hc u
  have hle := patterns_bound hrig heven root C hC hd hcover p
    (point_incidence root C p hp hnt) (point_meet root C p hp)
  have heq := IndexedCycles.number_of_cover root C hC hd hrig heven hcover
  norm_num at heq
  omega

lemma no_triangle (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    {x y z : V}
    (hx0 : x ∈ (C 0).support) (hx1 : x ∈ (C 1).support) (hx2 : x ∉ (C 2).support)
    (hy0 : y ∈ (C 0).support) (hy2 : y ∈ (C 2).support) (hy1 : y ∉ (C 1).support)
    (hz1 : z ∈ (C 1).support) (hz2 : z ∈ (C 2).support) (hz0 : z ∉ (C 0).support) : False := by
  apply no_triangle_of_cover (IndexedCycles.rigid root C hC hd hrig heven)
    (IndexedCycles.even root C hC hd) root (IndexedCycles.restrict root C)
    (IndexedCycles.restrict_cycle root C hC) (IndexedCycles.restrict_disjoint root C hd)
    (IndexedCycles.restrict_cover root C)
    (x := x) (y := y) (z := z)
  all_goals (simp only [IndexedCycles.restrict_support]; assumption)

lemma no_three_cycle_ring (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {a b c₀ x y z : V} (c : G.Walk a a) (d : G.Walk b b) (t : G.Walk c₀ c₀)
    (hc : c.IsCycle) (hd : d.IsCycle) (ht : t.IsCycle)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hxc : x ∈ c.support) (hxd : x ∈ d.support) (hxt : x ∉ t.support)
    (hyc : y ∈ c.support) (hyt : y ∈ t.support) (hyd : y ∉ d.support)
    (hzd : z ∈ d.support) (hzt : z ∈ t.support) (hzc : z ∉ c.support) : False := by
  let root : Fin 3 → V := ![a,b,c₀]
  let C : ∀ k, G.Walk (root k) (root k) :=
    Fin.cases c (Fin.cases d (Fin.cases t (fun i => Fin.elim0 i)))
  have hC : ∀ k, (C k).IsCycle := by
    intro k
    fin_cases k
    · exact hc
    · exact hd
    · exact ht
  have hdis : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact (hkl rfl).elim
    · exact hcd
    · exact hct
    · exact hcd.symm
    · exact (hkl rfl).elim
    · exact hdt
    · exact hct.symm
    · exact hdt.symm
    · exact (hkl rfl).elim
  exact no_triangle hrig heven root C hC hdis hxc hxd hxt hyc hyt hyd hzd hzt hzc

#print axioms no_triangle
#print axioms no_three_cycle_ring
end Erdos184Work.TriangleContacts

namespace Erdos184Work.TriangleContacts
open ChordalIncidence
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma no_subgraph_ring (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (H K L : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hL : L.coe.Connected ∧ L.coe.IsRegularOfDegree 2)
    (hHK : Disjoint H.edgeSet K.edgeSet) (hHL : Disjoint H.edgeSet L.edgeSet) (hKL : Disjoint K.edgeSet L.edgeSet)
    {x y z : V}
    (hxH : x ∈ H.verts) (hxK : x ∈ K.verts) (hxL : x ∉ L.verts)
    (hyH : y ∈ H.verts) (hyL : y ∈ L.verts) (hyK : y ∉ K.verts)
    (hzK : z ∈ K.verts) (hzL : z ∈ L.verts) (hzH : z ∉ H.verts) : False := by
  obtain ⟨c,hc,hcH⟩ := LongRing.regular_cycle_walk_at H hH.1 hH.2 x hxH
  obtain ⟨d,hd,hdK⟩ := LongRing.regular_cycle_walk_at K hK.1 hK.2 x hxK
  obtain ⟨t,ht,htL⟩ := LongRing.regular_cycle_walk_at L hL.1 hL.2 y hyL
  have sc (w) : w ∈ c.support ↔ w ∈ H.verts := by rw [← Walk.mem_verts_toSubgraph,hcH]
  have sd (w) : w ∈ d.support ↔ w ∈ K.verts := by rw [← Walk.mem_verts_toSubgraph,hdK]
  have st (w) : w ∈ t.support ↔ w ∈ L.verts := by rw [← Walk.mem_verts_toSubgraph,htL]
  have ec (e) : e ∈ c.edges ↔ e ∈ H.edgeSet := by rw [← Walk.mem_edges_toSubgraph,hcH]
  have ed (e) : e ∈ d.edges ↔ e ∈ K.edgeSet := by rw [← Walk.mem_edges_toSubgraph,hdK]
  have et (e) : e ∈ t.edges ↔ e ∈ L.edgeSet := by rw [← Walk.mem_edges_toSubgraph,htL]
  apply no_three_cycle_ring hrig heven c d t hc hd ht
    (List.disjoint_left.mpr (fun e he hf => Set.disjoint_left.mp hHK ((ec e).mp he) ((ed e).mp hf)))
    (List.disjoint_left.mpr (fun e he hf => Set.disjoint_left.mp hHL ((ec e).mp he) ((et e).mp hf)))
    (List.disjoint_left.mpr (fun e he hf => Set.disjoint_left.mp hKL ((ed e).mp he) ((et e).mp hf)))
    ((sc x).mpr hxH) ((sd x).mpr hxK) (fun h => hxL ((st x).mp h))
    ((sc y).mpr hyH) ((st y).mpr hyL) (fun h => hyK ((sd y).mp h))
    ((sd z).mpr hzK) ((st z).mpr hzL) (fun h => hzH ((sc z).mp h))

lemma no_incidenceTriangle (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    ¬ IncidenceTriangle (pieceVertices D) := by
  rintro ⟨i,j,k,x,y,z,hxi,hyi,hzi,hyj,hzj,hxj,hzk,hxk,hyk⟩
  simp only [pieceVertices,Set.mem_toFinset] at hxi hyi hzi hyj hzj hxj hzk hxk hyk
  have hij : i.val ≠ j.val := fun h => hxj (h ▸ hxi)
  have hik : i.val ≠ k.val := fun h => hyk (h ▸ hyi)
  have hjk : j.val ≠ k.val := fun h => hxj (h.symm ▸ hxk)
  exact no_subgraph_ring hrig heven i.val j.val k.val
    (hD i.val i.property) (hD j.val j.property) (hD k.val k.property)
    (hd i.property j.property hij) (hd i.property k.property hik) (hd j.property k.property hjk)
    hyi hyj hyk hxi hxk hxj hzj hzk hzi

lemma conformal (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    Conformal (pieceVertices D) :=
  conformal_of_no_incidenceTriangle _ (no_incidenceTriangle hrig heven D hD hd)

#print axioms no_incidenceTriangle
#print axioms conformal
end Erdos184Work.TriangleContacts

/-! Source block: RingIndices. -/

/-! Index manipulations for cyclic cycle-contact families. -/
open SimpleGraph
namespace Erdos184Work.RingIndices
set_option maxHeartbeats 1000000

abbrev skipOne {n : ℕ} : Fin (n+3) → Fin (n+4) := (1 : Fin (n+4)).succAbove

lemma skipOne_zero (n : ℕ) : skipOne (0 : Fin (n+3)) = 0 := rfl
lemma skipOne_one (n : ℕ) : skipOne (1 : Fin (n+3)) = 2 := by simp [skipOne]
lemma skipOne_ne_one {n : ℕ} (i : Fin (n+3)) : skipOne i ≠ 1 := Fin.succAbove_ne _ _

lemma skipOne_injective (n : ℕ) : Function.Injective (@skipOne n) :=
  Fin.succAbove_right_injective

lemma skipOne_val {n : ℕ} (i : Fin (n+3)) :
    (skipOne i).val = if i.val = 0 then 0 else i.val + 1 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩
  · rfl
  · simp [skipOne]

lemma skipOne_add_one {n : ℕ} (i : Fin (n+3)) (hi : i ≠ 0) :
    skipOne (i+1) = skipOne i + 1 := by
  apply Fin.ext
  have hi0 : i.val ≠ 0 := by simpa using hi
  simp only [skipOne_val,Fin.val_add_eq_ite,Fin.val_one]
  split_ifs <;> omega

lemma skipOne_eq_zero_iff {n : ℕ} (i : Fin (n+3)) : skipOne i = 0 ↔ i = 0 := by
  rw [← skipOne_zero n, (skipOne_injective n).eq_iff]
lemma skipOne_eq_two_iff {n : ℕ} (i : Fin (n+3)) : skipOne i = 2 ↔ i = 1 := by
  rw [← skipOne_one n, (skipOne_injective n).eq_iff]

lemma next_ne (n : ℕ) (i : Fin (n+3)) : i + 1 ≠ i := by
  intro h
  have he : (1 : Fin (n+3)) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa using h)
  exact Fin.zero_ne_one he.symm

#print axioms skipOne_add_one
end Erdos184Work.RingIndices

/-! Source block: CycleRings. -/

/-! Strong cyclic incidence patterns among edge-disjoint cycles. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleRings
open RingIndices RigidSwitching
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- There are `n+3` cycles, so the three-cycle case is the induction base. -/
structure Ring (G : SimpleGraph V) (n : ℕ) where
  vertex : Fin (n+3) → V
  injective : Function.Injective vertex
  piece : Fin (n+3) → G.Subgraph
  cycle : ∀ i, (piece i).coe.Connected ∧ (piece i).coe.IsRegularOfDegree 2
  disjoint : ∀ i j, i ≠ j → Disjoint (piece i).edgeSet (piece j).edgeSet
  incidence : ∀ i j, vertex i ∈ (piece j).verts ↔ i = j ∨ i = j+1

namespace Ring
variable {n : ℕ} (R : Ring G n)

def rotate (R : Ring G n) (o : Fin (n+3)) : Ring G n where
  vertex i := R.vertex (i+o)
  injective := fun _ _ h => add_right_cancel (R.injective h)
  piece i := R.piece (i+o)
  cycle i := R.cycle (i+o)
  disjoint i j hij := R.disjoint (i+o) (j+o) (fun h => hij (add_right_cancel h))
  incidence i j := by
    rw [R.incidence]
    have he : j+o+1 = j+1+o := by ac_rfl
    rw [he]
    simp only [add_right_cancel_iff]

lemma first_mem (i : Fin (n+3)) : R.vertex i ∈ (R.piece i).verts :=
  (R.incidence i i).mpr (Or.inl rfl)
lemma last_mem (i : Fin (n+3)) : R.vertex (i+1) ∈ (R.piece i).verts :=
  (R.incidence (i+1) i).mpr (Or.inr rfl)

lemma no_base (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (R : Ring G 0) : False := by
  apply TriangleContacts.no_subgraph_ring hrig heven (R.piece 0) (R.piece 1) (R.piece 2)
    (R.cycle 0) (R.cycle 1) (R.cycle 2)
    (R.disjoint 0 1 (by decide)) (R.disjoint 0 2 (by decide)) (R.disjoint 1 2 (by decide))
    (x := R.vertex 1) (y := R.vertex 0) (z := R.vertex 2)
  all_goals simp only [R.incidence]; decide

end Ring

/-- A two-cycle switch can retain any chosen contact on either original piece. -/
lemma switch_subgraphs (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (H K : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hdis : Disjoint H.edgeSet K.edgeSet)
    {u v x y : V} (huv : u ≠ v)
    (huH : u ∈ H.verts) (huK : u ∈ K.verts) (hvH : v ∈ H.verts) (hvK : v ∈ K.verts)
    (hx : x ∈ H.verts) (hy : y ∈ K.verts) :
    ∃ A : G.Subgraph, (A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      x ∈ A.verts ∧ y ∈ A.verts ∧ A.verts ⊆ H.verts ∪ K.verts ∧ A.edgeSet ⊆ H.edgeSet ∪ K.edgeSet := by
  obtain ⟨c,hc,hcH⟩ := LongRing.regular_cycle_walk_at H hH.1 hH.2 u huH
  obtain ⟨d,hd,hdK⟩ := LongRing.regular_cycle_walk_at K hK.1 hK.2 u huK
  have sc (w) : w ∈ c.support ↔ w ∈ H.verts := by rw [← Walk.mem_verts_toSubgraph,hcH]
  have sd (w) : w ∈ d.support ↔ w ∈ K.verts := by rw [← Walk.mem_verts_toSubgraph,hdK]
  have ec (e) : e ∈ c.edges ↔ e ∈ H.edgeSet := by rw [← Walk.mem_edges_toSubgraph,hcH]
  have ed (e) : e ∈ d.edges ↔ e ∈ K.edgeSet := by rw [← Walk.mem_edges_toSubgraph,hdK]
  have hcd : c.edges.Disjoint d.edges := List.disjoint_left.mpr
    (fun e he hf => Set.disjoint_left.mp hdis ((ec e).mp he) ((ed e).mp hf))
  have hinter (z) (hzC : z ∈ c.support) (hzD : z ∈ d.support) : z = u ∨ z = v := by
    by_contra hn
    push_neg at hn
    exact rigid_no_three_common_vertices hrig heven c d hc hd hcd huv hn.1.symm hn.2.symm
      ((sc u).mpr huH) ((sc v).mpr hvH) hzC ((sd u).mpr huK) ((sd v).mpr hvK) hzD
  obtain ⟨a,b,ha,hb,hab,hcover,hxa,hya⟩ := two_cycle_switch_through c d hc hd huv
    ((sc v).mpr hvH) ((sd v).mpr hvK) hcd hinter ((sc x).mpr hx) ((sd y).mpr hy)
  refine ⟨a.toSubgraph,cycle_coe_regular G ha,a.mem_verts_toSubgraph.mpr hxa,a.mem_verts_toSubgraph.mpr hya,?_,?_⟩
  · intro z hz
    have hz' := a.mem_verts_toSubgraph.mp hz
    obtain ⟨e,hea,hze⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil ha.not_nil).mp hz'
    rcases (hcover e).mp (Or.inl hea) with he | he
    · exact Or.inl ((sc z).mp (Walk.mem_support_of_mem_edges he hze))
    · exact Or.inr ((sd z).mp (Walk.mem_support_of_mem_edges he hze))
  · intro e he
    exact ((hcover e).mp (Or.inl (a.mem_edges_toSubgraph.mp he))).imp ((ec e).mp) ((ed e).mp)

#print axioms switch_subgraphs
#print axioms Ring.no_base
end Erdos184Work.CycleRings

namespace Erdos184Work.CycleRings
open RingIndices
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Ring.shorten_at_zero {n : ℕ} (R : Ring G (n+1))
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {u : V} (hu0 : u ∈ (R.piece 0).verts) (hu1 : u ∈ (R.piece 1).verts)
    (hu : u ≠ R.vertex 1) : Nonempty (Ring G n) := by
  have hv0 : R.vertex 1 ∈ (R.piece 0).verts := by simpa using R.last_mem 0
  have hv2 : R.vertex 2 ∈ (R.piece 1).verts := by simpa using R.last_mem 1
  obtain ⟨A,hA,hxA,hyA,hverts,hedges⟩ := switch_subgraphs hrig heven (R.piece 0) (R.piece 1)
    (R.cycle 0) (R.cycle 1) (R.disjoint 0 1 (by simp)) hu hu0 hu1 hv0 (R.first_mem 1)
    (R.first_mem 0) hv2
  have hdisA (i : Fin (n+3)) (hi : i ≠ 0) : Disjoint A.edgeSet (R.piece (skipOne i)).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hf
    rcases hedges he with he | he
    · exact Set.disjoint_left.mp (R.disjoint 0 (skipOne i)
        (fun h => hi ((skipOne_eq_zero_iff i).mp h.symm))) he hf
    · exact Set.disjoint_left.mp (R.disjoint 1 (skipOne i) (skipOne_ne_one i).symm) he hf
  have hincA (i : Fin (n+3)) : R.vertex (skipOne i) ∈ A.verts ↔ i = 0 ∨ i = 1 := by
    constructor
    · intro hi
      rcases hverts hi with hi | hi
      · rcases (R.incidence (skipOne i) 0).mp hi with he | he
        · exact Or.inl ((skipOne_eq_zero_iff i).mp he)
        · exact (skipOne_ne_one i (by simpa using he)).elim
      · rcases (R.incidence (skipOne i) 1).mp hi with he | he
        · exact (skipOne_ne_one i he).elim
        · exact Or.inr ((skipOne_eq_two_iff i).mp (by simpa using he))
    · rintro (rfl | rfl)
      · simpa only [skipOne_zero] using hxA
      · simpa only [skipOne_one] using hyA
  refine ⟨{
    vertex := fun i => R.vertex (skipOne i)
    injective := fun _ _ h => skipOne_injective n (R.injective h)
    piece := fun i => if i = 0 then A else R.piece (skipOne i)
    cycle := ?_
    disjoint := ?_
    incidence := ?_
  }⟩
  · intro i
    have hA' := hA
    have hR' := R.cycle (skipOne i)
    simp only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hA' hR' ⊢
    by_cases hi : i = 0
    · have he : (if i = 0 then A else R.piece (skipOne i)) = A := if_pos hi
      exact (congrArg (fun H : G.Subgraph => H.coe.Connected ∧ ∀ v, Nat.card (H.coe.neighborSet v) = 2) he).mpr hA'
    · have he : (if i = 0 then A else R.piece (skipOne i)) = R.piece (skipOne i) := if_neg hi
      exact (congrArg (fun H : G.Subgraph => H.coe.Connected ∧ ∀ v, Nat.card (H.coe.neighborSet v) = 2) he).mpr hR' 
  · intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := hij.symm
      simpa only [if_pos rfl,if_neg hj] using hdisA j hj
    · by_cases hj : j = 0
      · subst j
        simpa only [if_pos rfl,if_neg hi] using (hdisA i hi).symm
      · simp only [if_neg hi,if_neg hj]
        exact R.disjoint (skipOne i) (skipOne j) (fun h => hij (skipOne_injective n h))
  · intro i j
    by_cases hj : j = 0
    · subst j
      simpa only [if_pos rfl,zero_add] using hincA i
    · simp only [if_neg hj,R.incidence,← skipOne_add_one j hj,(skipOne_injective n).eq_iff]

#print axioms Ring.shorten_at_zero
end Erdos184Work.CycleRings

/-! Source block: RingChords. -/

/-! Shortening a contact ring across a vertex met only at the ends of an interval. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.RingIndices
set_option maxHeartbeats 1500000

abbrev initial {m n : ℕ} (h : m+3 < n+3) : Fin (m+3) → Fin (n+3) := Fin.castLE (Nat.le_of_lt h)

lemma initial_incidence_nonzero {m n : ℕ} (h : m+3 < n+3) (i j : Fin (m+3)) (hi : i ≠ 0) :
    (initial h i = initial h j ∨ initial h i = initial h j + 1) ↔ i = j ∨ i = j+1 := by
  have hi0 : i.val ≠ 0 := by simpa using hi
  simp only [Fin.ext_iff,Fin.val_add_eq_ite,Fin.val_one,initial,Fin.val_castLE]
  split_ifs <;> omega

lemma initial_vertex_internal {m : ℕ} (j : Fin (m+3)) (hj : j ≠ 0) :
    ∃ i : Fin (m+3), 0 < i.val ∧ i.val < m+2 ∧ (j = i ∨ j = i+1) := by
  have hj0 : j.val ≠ 0 := by simpa using hj
  let i : Fin (m+3) := ⟨if j.val = 1 then 1 else j.val-1,by split_ifs <;> omega⟩
  refine ⟨i,?_,?_,?_⟩
  · dsimp [i]
    split_ifs <;> omega
  · dsimp [i]
    split_ifs <;> omega
  · simp only [Fin.ext_iff,Fin.val_add_eq_ite,Fin.val_one,i]
    split_ifs <;> omega

lemma zero_incidence (n : ℕ) (i : Fin (n+3)) :
    (0 = i ∨ (0 : Fin (n+3)) = i+1) ↔ i = 0 ∨ i = Fin.last (n+2) := by
  have hil := i.isLt
  simp only [Fin.ext_iff,Fin.val_add_eq_ite,Fin.val_one,Fin.val_zero,Fin.val_last]
  split_ifs <;> (try simp only [or_false]) <;> omega

#print axioms initial_incidence_nonzero
#print axioms initial_vertex_internal
end Erdos184Work.RingIndices

namespace Erdos184Work.CycleRings
open RingIndices
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Ring.shorten_at (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {n : ℕ} (R : Ring G (n+1)) (i : Fin (n+4)) {u : V}
    (hu0 : u ∈ (R.piece i).verts) (hu1 : u ∈ (R.piece (i+1)).verts)
    (hu : u ≠ R.vertex (i+1)) : Nonempty (Ring G n) := by
  apply (R.rotate i).shorten_at_zero hrig heven (u := u)
  · simpa only [Ring.rotate,zero_add] using hu0
  · simpa only [Ring.rotate,add_comm 1 i] using hu1
  · simpa only [Ring.rotate,add_comm 1 i] using hu

lemma Ring.adjacent_intersection (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {n : ℕ} (R : Ring G (n+1)) (hno : ¬ Nonempty (Ring G n))
    (i : Fin (n+4)) (u : V) (hu0 : u ∈ (R.piece i).verts) (hu1 : u ∈ (R.piece (i+1)).verts) :
    u = R.vertex (i+1) := by
  by_contra hu
  exact hno (R.shorten_at hrig heven i hu0 hu1 hu)

lemma Ring.shorten_chord {m n : ℕ} (R : Ring G n) (h : m+3 < n+3) {w : V}
    (hw0 : w ∈ (R.piece (initial h 0)).verts)
    (hwend : w ∈ (R.piece (initial h (Fin.last (m+2)))).verts)
    (havoid : ∀ i : Fin (m+3), 0 < i.val → i.val < m+2 → w ∉ (R.piece (initial h i)).verts) :
    Nonempty (Ring G m) := by
  have hwne (j : Fin (m+3)) (hj : j ≠ 0) : w ≠ R.vertex (initial h j) := by
    obtain ⟨i,hi0,hie,hi⟩ := initial_vertex_internal j hj
    have hv : R.vertex (initial h j) ∈ (R.piece (initial h i)).verts :=
      (R.incidence _ _).mpr ((initial_incidence_nonzero h j i hj).mpr hi)
    intro he
    exact havoid i hi0 hie (he.symm ▸ hv)
  have hwi (i : Fin (m+3)) : w ∈ (R.piece (initial h i)).verts ↔ i = 0 ∨ i = Fin.last (m+2) := by
    constructor
    · intro hw
      by_cases hi0 : i = 0
      · exact Or.inl hi0
      by_cases hie : i = Fin.last (m+2)
      · exact Or.inr hie
      have h0 : i.val ≠ 0 := by simpa using hi0
      have hend : i.val ≠ m+2 := by simpa only [Fin.ext_iff,Fin.val_last] using hie
      exact (havoid i (by omega) (by omega) hw).elim
    · rintro (rfl | rfl)
      · exact hw0
      · exact hwend
  refine ⟨{
    vertex := fun i => if i = 0 then w else R.vertex (initial h i)
    injective := ?_
    piece := fun i => R.piece (initial h i)
    cycle := fun i => R.cycle (initial h i)
    disjoint := fun i j hij => R.disjoint _ _ (fun he => hij (Fin.castLE_injective _ he))
    incidence := ?_
  }⟩
  · intro i j he
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · exact hj.symm
      · simp only [if_pos rfl,if_neg hj] at he
        exact (hwne j hj he).elim
    · by_cases hj : j = 0
      · subst j
        simp only [if_pos rfl,if_neg hi] at he
        exact (hwne i hi he.symm).elim
      · simp only [if_neg hi,if_neg hj] at he
        exact Fin.castLE_injective _ (R.injective he)
  · intro i j
    by_cases hi : i = 0
    · subst i
      simp only [ite_true,hwi,zero_incidence]
    · simp only [if_neg hi,R.incidence,initial_incidence_nonzero h i j hi]

#print axioms Ring.shorten_at
#print axioms Ring.shorten_chord
end Erdos184Work.CycleRings

/-! Source block: MinimalRings. -/

/-! A shortest strong contact ring has only its prescribed singleton intersections. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleRings
open RingIndices
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}

/-- The only intersections are the designated junctions of consecutive pieces. -/
def Ring.Clean (R : Ring G n) : Prop :=
  ∀ i j, i ≠ j → ∀ x, x ∈ (R.piece i).verts → x ∈ (R.piece j).verts →
    (j = i+1 ∧ x = R.vertex j) ∨ (i = j+1 ∧ x = R.vertex i)

lemma Ring.no_chord (R : Ring G n)
    (hsmall : ∀ m < n, ¬ Nonempty (Ring G m))
    (hadj : ∀ i x, x ∈ (R.piece i).verts → x ∈ (R.piece (i+1)).verts → x = R.vertex (i+1))
    (i j : Fin (n+3)) (hij : i ≠ j) (hnext : j ≠ i+1) (hprev : i ≠ j+1)
    (x : V) (hxi : x ∈ (R.piece i).verts) (hxj : x ∈ (R.piece j).verts) : False := by
  let T := R.rotate i
  let q : Fin (n+3) := j-i
  have hqi : q+i = j := sub_add_cancel j i
  have hq0 : q ≠ 0 := by
    intro he
    rw [he,zero_add] at hqi
    exact hij hqi
  have hq1 : q ≠ 1 := by
    intro he
    rw [he,add_comm 1 i] at hqi
    exact hnext hqi.symm
  have hqnext : q+1 ≠ 0 := by
    intro he
    apply hprev
    calc
      i = (q+1)+i := by rw [he,zero_add]
      _ = j+1 := by rw [add_right_comm,hqi]
  have hqbound : q.val+1 < n+3 := by
    by_contra hn
    apply hqnext
    apply Fin.ext
    simp only [Fin.val_add_eq_ite,Fin.val_one,Fin.val_zero]
    split_ifs <;> omega
  have hx0 : x ∈ (T.piece 0).verts := by simpa only [T,Ring.rotate,zero_add] using hxi
  have hxq : x ∈ (T.piece q).verts := by simpa only [T,Ring.rotate,hqi] using hxj
  have hxnot1 : x ∉ (T.piece 1).verts := by
    intro hx1
    have hx1' : x ∈ (R.piece (i+1)).verts := by simpa only [T,Ring.rotate,add_comm 1 i] using hx1
    have he := hadj i x hxi hx1'
    have heT : x = T.vertex 1 := by simpa only [T,Ring.rotate,add_comm 1 i] using he
    rw [heT] at hxq
    rcases (T.incidence 1 q).mp hxq with he | he
    · exact hq1 he.symm
    · have he' : q+1 = 0+1 := by simpa using he.symm
      exact hq0 (add_right_cancel he')
  let S : Finset (Fin (n+3)) := Finset.univ.filter (fun k => k ≠ 0 ∧ x ∈ (T.piece k).verts)
  have hqS : q ∈ S := by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hq0,hxq⟩
  have hSne : S.Nonempty := ⟨q,hqS⟩
  let k := S.min' hSne
  have hkS : k ∈ S := Finset.min'_mem _ _
  have hk : k ≠ 0 ∧ x ∈ (T.piece k).verts := (Finset.mem_filter.mp hkS).2
  have hkq : k ≤ q := Finset.min'_le S q hqS
  have hk1 : k ≠ 1 := fun he => hxnot1 (he ▸ hk.2)
  have hk0v : k.val ≠ 0 := by simpa using hk.1
  have hk1v : k.val ≠ 1 := by
    intro he
    apply hk1
    exact Fin.ext (by simpa using he)
  have hkqv : k.val ≤ q.val := hkq
  have hk2 : 2 ≤ k.val := by omega
  let m := k.val-2
  have hm : m+3 < n+3 := by dsimp [m]; omega
  have heend : initial hm (Fin.last (m+2)) = k := by
    apply Fin.ext
    simp only [initial,Fin.val_castLE,Fin.val_last]
    dsimp [m]
    omega
  have hwend : x ∈ (T.piece (initial hm (Fin.last (m+2)))).verts := by rw [heend]; exact hk.2
  have havoid (l : Fin (m+3)) (hl0 : 0 < l.val) (hle : l.val < m+2) :
      x ∉ (T.piece (initial hm l)).verts := by
    intro hxl
    have hlne : initial hm l ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      simp only [initial,Fin.val_castLE,Fin.val_zero] at hv
      omega
    have hlS : initial hm l ∈ S := by
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hlne,hxl⟩
    have hkle : k.val ≤ l.val := Finset.min'_le S (initial hm l) hlS
    dsimp [m] at hle
    omega
  exact hsmall m (by dsimp [m]; omega) (T.shorten_chord hm hx0 hwend havoid)

lemma Ring.clean_of_no_shorter (R : Ring G n)
    (hsmall : ∀ m < n, ¬ Nonempty (Ring G m))
    (hadj : ∀ i x, x ∈ (R.piece i).verts → x ∈ (R.piece (i+1)).verts → x = R.vertex (i+1)) : R.Clean := by
  intro i j hij x hxi hxj
  by_cases hn : j = i+1
  · subst j
    exact Or.inl ⟨rfl,hadj i x hxi hxj⟩
  by_cases hp : i = j+1
  · subst i
    exact Or.inr ⟨rfl,hadj j x hxj hxi⟩
  exact (R.no_chord hsmall hadj i j hij hn hp x hxi hxj).elim

#print axioms Ring.no_chord
#print axioms Ring.clean_of_no_shorter
end Erdos184Work.CycleRings

/-! Source block: CleanRings. -/

/-! Excluding clean contact rings by the established clean-chain theorem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleRings
open RingIndices MaximumCycles Subfamilies LongRing RigidSwitching
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma rigid_linear_no_core (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (hl : LinearIntersections D) (hDne : D.Nonempty) (S : Set V)
    (hcycle : ∀ H ∈ D, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ u ∈ H.verts ∧ v ∈ H.verts)
    (hvertex : ∀ v ∈ S, ∃ H ∈ D, ∃ K ∈ D, H ≠ K ∧ v ∈ H.verts ∧ v ∈ K.verts) : False := by
  let hcover := (subfamilyGraph_edges D).symm
  let E := lowerFamily D hcover
  have hE : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp hH
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD K.val K.property
  have hvalid : ∀ H ∈ E, IsCycleOrEdge H.coe := by
    intro H hH
    exact Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hE H hH)
  have hnum := rigid_subfamily_number hrig heven D hD hd
  have hEcard : E.card = D.card := lowerFamily_card D hcover
  have hmin : ∀ F : Finset (subfamilyGraph D).Subgraph,
      (∀ H ∈ F, IsCycleOrEdge H.coe) → IsDecomposition (subfamilyGraph D) F → E.card ≤ F.card := by
    intro F hF hf
    rw [hEcard,← hnum]
    exact Critical.number_le F hF hf
  have hEne : E.Nonempty := Finset.card_pos.mp (by rw [hEcard]; exact Finset.card_pos.mpr hDne)
  apply minimal_linear_no_core E hvalid (lowerFamily_decomposition D hcover hd) (lowerFamily_linear D hcover hl)
    (fun H hH => regular_cycle_walk_at H (hE H hH).1 (hE H hH).2)
    hmin E S (Finset.Subset.refl _) hEne
  · intro H hH
    obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp hH
    exact hcycle K.val K.property
  · intro v hv
    obtain ⟨H,hH,K,hK,hHK,hvH,hvK⟩ := hvertex v hv
    refine ⟨lowerPiece D hcover ⟨H,hH⟩,Finset.mem_image.mpr ⟨⟨H,hH⟩,Finset.mem_univ _,rfl⟩,
      lowerPiece D hcover ⟨K,hK⟩,Finset.mem_image.mpr ⟨⟨K,hK⟩,Finset.mem_univ _,rfl⟩,?_,hvH,hvK⟩
    intro he
    exact hHK (congrArg Subtype.val (lowerPiece_injective D hcover he))

lemma two_next_ne (n : ℕ) (i : Fin (n+3)) : i+1+1 ≠ i := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_add_eq_ite,Fin.val_one] at he
  split_ifs at he <;> omega

lemma Ring.piece_injective {n : ℕ} (R : Ring G n) : Function.Injective R.piece := by
  intro i j he
  by_contra hij
  obtain ⟨e,heP⟩ := cycle_piece_edgeSet_nonempty (R.piece i) (R.cycle i)
  have heE := congrArg (fun H : G.Subgraph => H.edgeSet) he
  dsimp only at heE
  exact Set.disjoint_left.mp (R.disjoint i j hij) heP (by rw [← heE]; exact heP)

lemma Ring.Clean.linear {n : ℕ} {R : Ring G n} (hc : R.Clean) :
    LinearIntersections (Finset.univ.image R.piece) := by
  intro H hH K hK hHK x hxH y hyH hxK hyK
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
  have hij : i ≠ j := fun he => hHK (congrArg R.piece he)
  rcases hc i j hij x hxH hxK with ⟨hji,hx⟩ | ⟨hij',hx⟩
  · rcases hc i j hij y hyH hyK with ⟨_,hy⟩ | ⟨hij',hy⟩
    · exact hx.trans hy.symm
    · exact (two_next_ne n i (by rw [← hji,← hij'])).elim
  · rcases hc i j hij y hyH hyK with ⟨hji,hy⟩ | ⟨_,hy⟩
    · exact (two_next_ne n i (by rw [← hji,← hij'])).elim
    · exact hx.trans hy.symm

lemma Ring.Clean.impossible {n : ℕ} {R : Ring G n} (hc : R.Clean)
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v)) : False := by
  let D := Finset.univ.image R.piece
  have hmem (i) : R.piece i ∈ D := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact R.cycle i
  have hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    change H ∈ Finset.univ.image R.piece at hH
    change K ∈ Finset.univ.image R.piece at hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
    exact R.disjoint i j (fun he => hne (congrArg R.piece he))
  apply rigid_linear_no_core hrig heven D hD hd hc.linear ⟨R.piece 0,hmem 0⟩ (Set.range R.vertex)
  · intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact ⟨R.vertex i,⟨i,rfl⟩,R.vertex (i+1),⟨i+1,rfl⟩,
      fun he => next_ne n i (R.injective he).symm,R.first_mem i,R.last_mem i⟩
  · rintro v ⟨i,rfl⟩
    refine ⟨R.piece i,hmem i,R.piece (i-1),hmem (i-1),?_,R.first_mem i,?_⟩
    · intro he
      exact next_ne n (i-1) ((sub_add_cancel i 1).trans (R.piece_injective he))
    · simpa only [sub_add_cancel] using R.last_mem (i-1)

lemma no_ring (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v)) :
    ∀ n, ¬ Nonempty (Ring G n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rintro ⟨R⟩
    cases n with
    | zero => exact R.no_base hrig heven
    | succ n =>
      have hadj := R.adjacent_intersection hrig heven (ih n (by omega))
      exact (R.clean_of_no_shorter ih hadj).impossible hrig heven

#print axioms Ring.Clean.impossible
#print axioms no_ring
end Erdos184Work.CycleRings

/-! Source block: RigidBound. -/

/-! A linear bound for even cycle-rigid graphs. Minimal-core rigidity is not assumed. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleRings
open ChordalIncidence
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma ring_of_incidence_walk (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    {a : V} (p : (primal (pieceVertices D)).Walk a a) (hp : p.IsCycle)
    (label : {e : Sym2 V // e ∈ p.edges} → D)
    (hl : ∀ e x, x ∈ p.support → (x ∈ pieceVertices D (label e) ↔ x ∈ e.val))
    {n : ℕ} (hlen : p.length = n+3) : Nonempty (Ring G n) := by
  let vertex : Fin (n+3) → V := fun i => p.getVert i.val
  have hinj : Function.Injective vertex := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length-1; omega)
      (by change j.val ≤ p.length-1; omega) he
  have hnext (i : Fin (n+3)) : vertex (i+1) = p.getVert (i.val+1) := by
    dsimp only [vertex]
    rw [Fin.val_add_eq_ite,Fin.val_one]
    split_ifs with hi
    · have he : i.val+1 = p.length := by omega
      have he0 : i.val+1-(n+3) = 0 := by omega
      rw [he0,he,Walk.getVert_zero,Walk.getVert_length]
    · rfl
  have hedge (i : Fin (n+3)) : s(vertex i,vertex (i+1)) ∈ p.edges := by
    rw [hnext]
    exact consecutive_mem_edges p i.val (by omega)
  let edge (i : Fin (n+3)) : {e : Sym2 V // e ∈ p.edges} := ⟨s(vertex i,vertex (i+1)),hedge i⟩
  have einj : Function.Injective edge := by
    intro i j he
    have he' : s(vertex i,vertex (i+1)) = s(vertex j,vertex (j+1)) := congrArg Subtype.val he
    rcases Sym2.eq_iff.mp he' with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · exact hinj hi
    · have hi' := hinj hi
      have hj' := hinj hj
      exact (two_next_ne n i (by rw [hj',← hi'])).elim
  have linj := incidence_label_injective p label hl
  refine ⟨{
    vertex := vertex
    injective := hinj
    piece := fun i => (label (edge i)).val
    cycle := fun i => hD _ (label (edge i)).property
    disjoint := ?_
    incidence := ?_
  }⟩
  · intro i j hij
    exact hd (label (edge i)).property (label (edge j)).property
      (fun he => hij (einj (linj (Subtype.ext he))))
  · intro i j
    have hmem : vertex i ∈ p.support := p.getVert_mem_support i.val
    have he := hl (edge j) (vertex i) hmem
    simpa only [pieceVertices,Set.mem_toFinset,edge,Sym2.mem_iff,hinj.eq_iff] using he

lemma no_incidenceCycle (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    ¬ IncidenceCycle (pieceVertices D) := by
  rintro ⟨a,p,hp,label,hl⟩
  have hlen : p.length = (p.length-3)+3 := by have := hp.three_le_length; omega
  exact no_ring hrig heven _ (ring_of_incidence_walk D hD hd p hp label hl hlen)

lemma rigid_number_le_support (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v)) :
    Critical.number G ≤ G.support.ncard := by
  obtain ⟨D,hD,hdec,_⟩ := Rigidity.minimum_cycles heven
  exact rigid_number_bound_of_no_incidenceCycle hrig D hD hdec (no_incidenceCycle hrig heven D hD hdec.1)

#print axioms ring_of_incidence_walk
#print axioms no_incidenceCycle
#print axioms rigid_number_le_support
end Erdos184Work.CycleRings
