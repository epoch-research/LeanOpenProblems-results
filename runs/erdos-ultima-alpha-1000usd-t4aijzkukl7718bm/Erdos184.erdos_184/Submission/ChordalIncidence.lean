import Submission.Work

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
