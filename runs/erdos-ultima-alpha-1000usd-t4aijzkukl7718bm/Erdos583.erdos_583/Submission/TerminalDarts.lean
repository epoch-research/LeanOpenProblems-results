import Submission.Work

/-! Endpoint-tail preservation in rooted all-odd exchanges.
This local development does not assert a terminal-spoke cardinal bound. -/

open SimpleGraph Erdos583Work
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583Work.DoubleEscape Erdos583Work.MultipleEscape
namespace Erdos583TerminalDartsDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma realize_escape_orbit_with_tails {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (f : V → V) (hf : Set.InjOn f (B.erase v : Set V))
    (htf : ∀ w : B, w.val ≠ v → f w.val = (R.tail w).penultimate)
    (hx : (R.tail ⟨v,R.root_mem⟩).snd ∉ (B.erase v).image f)
    (N : ℕ)
    (hexit : f^[N] (R.tail ⟨v,R.root_mem⟩).snd ∉ B.erase v)
    (hprev : ∀ n < N, f^[n] (R.tail ⟨v,R.root_mem⟩).snd ∈ B.erase v) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧
      (S.tail ⟨v,S.root_mem⟩).snd = f^[N] (R.tail ⟨v,R.root_mem⟩).snd ∧
      (S.tail ⟨v,S.root_mem⟩).snd ∉ B ∧ AgreesOutside S R ∧
      ∀ z : B, z.val ≠ v →
        (∀ m < N, z.val ≠ f^[m] (R.tail ⟨v,R.root_mem⟩).snd) →
          S.tail z = R.tail z := by
  classical
  let x := (R.tail ⟨v,R.root_mem⟩).snd
  have hinj := iterate_injective_before_exit (B.erase v) f hf x hx N hprev
  have hreach : ∀ n ≤ N, ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧
      (S.tail ⟨v,S.root_mem⟩).snd = f^[n] x ∧
      (∀ z : B, z.val ≠ v → (∀ m < n, z.val ≠ f^[m] x) → S.tail z = R.tail z) ∧
      AgreesOutside S R := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨R, rfl, rfl, (fun _ _ _ ↦ rfl), agreesOutside_refl R⟩
    | succ n ih =>
      intro hn
      obtain ⟨S, hscore, hfirst, htail, htrack⟩ := ih (by omega)
      have hw := hprev n (by omega)
      obtain ⟨hwv, hwB⟩ := Finset.mem_erase.mp hw
      let w : B := ⟨f^[n] x, hwB⟩
      have hunprocessed : ∀ m < n, w.val ≠ f^[m] x := by
        intro m hm he
        have hh := hinj n m (by omega) (by omega) he
        omega
      have htw : S.tail w = R.tail w := htail w hwv hunprocessed
      have hstep : ∃ S' : RootedTailSystem G k v B,
          S'.system.score = S.system.score ∧
          (S'.tail ⟨v,S'.root_mem⟩).snd = (S.tail w).penultimate ∧
          (∀ z : B, z.val ≠ v → z ≠ w → S'.tail z = S.tail z) ∧ AgreesOutside S' S := by
        cases hc : S.tail ⟨v,S.root_mem⟩ with
        | nil => exact (S.root_nonempty (hc ▸ Walk.Nil.nil)).elim
        | @cons _ u _ h p =>
          have huw : u = w.val := by simpa only [hc, Walk.snd_cons] using hfirst
          subst u
          exact pivot_tracked S w h p hc
      obtain ⟨S', hs', hf', ht', htr'⟩ := hstep
      refine ⟨S', hs'.trans hscore, ?_, ?_, agreesOutside_trans htr' htrack⟩
      · rw [hf', htw, Function.iterate_succ_apply']
        exact (htf w hwv).symm
      · intro z hzv hz
        have hzw : z ≠ w := fun he ↦ hz n (by omega) (congrArg Subtype.val he)
        exact (ht' z hzv hzw).trans (htail z hzv (fun m hm ↦ hz m (by omega)))
  obtain ⟨S, hs, hfirst, htail, htrack⟩ := hreach N le_rfl
  refine ⟨S, hs, hfirst, ?_, htrack, htail⟩
  intro hB
  have hvne : (S.tail ⟨v,S.root_mem⟩).snd ≠ v :=
    ((S.tail ⟨v,S.root_mem⟩).adj_snd S.root_nonempty).ne.symm
  exact hexit (Finset.mem_erase.mpr ⟨hfirst ▸ hvne, hfirst ▸ hB⟩)

lemma iterate_avoids_fixed_before_exit {α : Type*} [DecidableEq α]
    (A : Finset α) (f : α → α) (hf : Set.InjOn f (A : Set α))
    (x : α) (hx : x ∉ A.image f) (N : ℕ)
    (hprev : ∀ m < N, f^[m] x ∈ A) {z : α} (hz : f z = z) :
    ∀ m < N, z ≠ f^[m] x := by
  intro m hm he
  have hinj := iterate_injective_before_exit A f hf x hx N hprev
  have heq : f^[m+1] x = f^[m] x := by
    rw [Function.iterate_succ_apply', ← he, hz]
  have hh := hinj (m+1) m (by omega) (by omega) heq
  omega

lemma iterate_neighbors_before_exit {V : Type*} {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (f : V → V)
    (htf : ∀ w : B, w.val ≠ v → f w.val = (R.tail w).penultimate)
    (N : ℕ) (hprev : ∀ m < N, f^[m] (R.tail ⟨v,R.root_mem⟩).snd ∈ B.erase v) :
    ∀ m ≤ N, G.Adj v (f^[m] (R.tail ⟨v,R.root_mem⟩).snd) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact (R.tail ⟨v,R.root_mem⟩).adj_snd R.root_nonempty
  | succ m _ =>
    intro hm
    obtain ⟨hwv, hwB⟩ := Finset.mem_erase.mp (hprev m (by omega))
    rw [Function.iterate_succ_apply', htf ⟨_,hwB⟩ hwv]
    exact ((R.tail ⟨_,hwB⟩).adj_penultimate (Walk.not_nil_of_ne hwv)).symm

/-- Tails at non-neighbors of the root, and direct one-edge tails to the root,
can all be kept simultaneously throughout the pivot orbit. -/
lemma expose_escape_preserving_tails {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧
      (S.tail ⟨v,S.root_mem⟩).snd ∉ B ∧ AgreesOutside S R ∧
      ∀ z : B, z.val ≠ v →
        (¬G.Adj v z.val ∨ (R.tail z).penultimate = z.val) →
          S.tail z = R.tail z := by
  classical
  obtain ⟨f,hf,htf,hx,_⟩ := successor_data R
  obtain ⟨N,hexit,hprev⟩ := exists_first_exit_of_injective_successor
    (B.erase v) f hf (R.tail ⟨v,R.root_mem⟩).snd hx
  obtain ⟨S,hs,_,he,ht,htail⟩ :=
    realize_escape_orbit_with_tails R f hf htf hx N hexit hprev
  refine ⟨S,hs,he,ht,?_⟩
  intro z hz hprot
  apply htail z hz
  rcases hprot with hnon | hfix
  · intro m hm heq
    apply hnon
    rw [heq]
    exact iterate_neighbors_before_exit R f htf N hprev m (by omega)
  · exact iterate_avoids_fixed_before_exit (B.erase v) f hf _ hx N hprev
      ((htf z hz).trans hfix)

/-- A tail can be used as a literal initial segment of its endpoint-owning
member, regardless of which orientation was stored in the system. -/
lemma tail_partner {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (z : B) :
    ∃ i : Fin k, i ∈ R.active ∧ ∃ w : B, z ≠ w ∧
      ((R.system.start i = z.val ∧ R.system.finish i = w.val) ∨
       (R.system.start i = w.val ∧ R.system.finish i = z.val)) ∧
      (R.system.walk i).toSubgraph = (R.tail z).toSubgraph ⊔ (R.tail w).toSubgraph := by
  obtain ⟨⟨i,b⟩,he⟩ := R.system.endpoint_bijective.2 z.val
  cases b
  · have hz : R.system.finish i = z.val := he
    have hi := (R.finish_mem i).mp (hz.symm ▸ z.property)
    let w : B := ⟨R.system.start i,(R.start_mem i).mpr hi⟩
    have hzw : z ≠ w := fun h ↦ R.system.endpoints_ne i
      ((congrArg Subtype.val h).symm.trans hz.symm)
    refine ⟨i,hi,w,hzw,Or.inr ⟨rfl,hz⟩,?_⟩
    have heq : (⟨R.system.finish i,(R.finish_mem i).mpr hi⟩ : B) = z := Subtype.ext hz
    rw [R.decomp i hi,heq,sup_comm]
  · have hz : R.system.start i = z.val := he
    have hi := (R.start_mem i).mp (hz.symm ▸ z.property)
    let w : B := ⟨R.system.finish i,(R.finish_mem i).mpr hi⟩
    have hzw : z ≠ w := fun h ↦ R.system.endpoints_ne i
      (hz.trans (congrArg Subtype.val h))
    refine ⟨i,hi,w,hzw,Or.inl ⟨hz,rfl⟩,?_⟩
    have heq : (⟨R.system.start i,(R.start_mem i).mpr hi⟩ : B) = z := Subtype.ext hz
    rw [R.decomp i hi,heq]

lemma tail_is_member_prefix {V : Type*} {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B) (z : B) :
    ∃ b, ∃ q : G.Walk v b,
      ((R.tail z).append q).IsTrail ∧ IsMember R.system ((R.tail z).append q) := by
  obtain ⟨i,hi,w,hzw,hends,he⟩ := tail_partner R z
  refine ⟨w.val,(R.tail w).reverse,?_,i,hends,?_⟩
  · apply trail_append_of_disjoint (R.trail z) (R.trail w).reverse
    simpa only [Walk.toSubgraph_reverse] using R.disjoint hzw
  · simpa only [Walk.toSubgraph_append,Walk.toSubgraph_reverse] using he

/-- Reorienting arbitrary indexed members does not change any endpoint-to-root
tail. This helper exposes both endpoint formulas, not just the subgraphs. -/
lemma orient_with_tails {V : Type*} {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (eps : Fin k → Bool) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ S.tail = R.tail ∧ S.active = R.active ∧
      ∀ i, S.system.start i = (if eps i then R.system.finish i else R.system.start i) ∧
        S.system.finish i = (if eps i then R.system.start i else R.system.finish i) ∧
        (S.system.walk i).toSubgraph = (R.system.walk i).toSubgraph := by
  classical
  obtain ⟨T,hs,ht⟩ := R.system.orient eps
  have ha (i : Fin k) : T.start i ∈ B ↔ i ∈ R.active := by
    rw [(ht i).1]
    split_ifs <;> first | exact R.finish_mem i | exact R.start_mem i
  have hb (i : Fin k) : T.finish i ∈ B ↔ i ∈ R.active := by
    rw [(ht i).2.1]
    split_ifs <;> first | exact R.start_mem i | exact R.finish_mem i
  have hd (i : Fin k) (hi : i ∈ R.active) : (T.walk i).toSubgraph =
      (R.tail ⟨T.start i,(ha i).mpr hi⟩).toSubgraph ⊔
      (R.tail ⟨T.finish i,(hb i).mpr hi⟩).toSubgraph := by
    rw [(ht i).2.2,R.decomp i hi]
    by_cases he : eps i = true
    · have h1 : (⟨T.start i,(ha i).mpr hi⟩ : B) =
          ⟨R.system.finish i,(R.finish_mem i).mpr hi⟩ := by
        apply Subtype.ext
        simpa [he] using (ht i).1
      have h2 : (⟨T.finish i,(hb i).mpr hi⟩ : B) =
          ⟨R.system.start i,(R.start_mem i).mpr hi⟩ := by
        apply Subtype.ext
        simpa [he] using (ht i).2.1
      rw [h1,h2,sup_comm]
    · have h1 : (⟨T.start i,(ha i).mpr hi⟩ : B) =
          ⟨R.system.start i,(R.start_mem i).mpr hi⟩ := by
        apply Subtype.ext
        simpa [he] using (ht i).1
      have h2 : (⟨T.finish i,(hb i).mpr hi⟩ : B) =
          ⟨R.system.finish i,(R.finish_mem i).mpr hi⟩ := by
        apply Subtype.ext
        simpa [he] using (ht i).2.1
      rw [h1,h2]
  let S : RootedTailSystem G k v B :=
    { system := T, active := R.active, root_mem := R.root_mem,
      tail := R.tail, trail := R.trail, disjoint := R.disjoint,
      start_mem := ha, finish_mem := hb, decomp := hd,
      outside := by
        intro i hi
        rw [← Walk.mem_verts_toSubgraph,(ht i).2.2,Walk.mem_verts_toSubgraph]
        exact R.outside i hi
      root_nonempty := R.root_nonempty }
  exact ⟨S,hs,rfl,rfl,ht⟩

/-- The final slide preserves every other endpoint-labelled member, and the
shortened donor itself is retained as an undirected member. -/
lemma escape_slide_with_members {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) {y : V}
    (h : G.Adj (T.start i) y) (p : G.Walk y (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support)
    (havoid : T.start i ∉ (T.walk (NormalTrailSystem.owner T y)).support) :
    ∃ S : NormalTrailSystem G k, S.score = T.score + 1 ∧ IsMember S p ∧
      ∀ l, l ≠ i → l ≠ NormalTrailSystem.owner T y →
        S.start l = T.start l ∧ S.finish l = T.finish l ∧
        (S.walk l).toSubgraph = (T.walk l).toSubgraph := by
  classical
  let j := NormalTrailSystem.owner T y
  have hjown := NormalTrailSystem.owner_spec T y
  have hij : i ≠ j := by
    intro hh
    apply havoid
    change T.start i ∈ (T.walk j).support
    rw [← hh]
    exact (T.walk i).start_mem_support
  obtain ⟨U,hUs,hUj,hUl,hUe⟩ := orient_receiver T j y hjown
  obtain ⟨hi,hi'⟩ := hUl i hij
  have h' : G.Adj (U.start i) (U.start j) := by rw [hi,hUj]; exact h
  let pU := p.copy hUj.symm hi'.symm
  have hform : Walk.cons h' pU = (Walk.cons h p).copy hi.symm hi'.symm :=
    cons_copy_vertices h p hi.symm hUj.symm hi'.symm h'
  have hpU : (Walk.cons h' pU).IsTrail := by rw [hform]; simpa using hp
  have heU : (U.walk i).toSubgraph = (Walk.cons h' pU).toSubgraph := by
    rw [hform,NormalTrailSystem.walk_copy_subgraph,hUe,he]
  have hvU : U.start i ∈ pU.support := by simpa [pU,hi] using hv
  have havoidU : U.start i ∉ (U.walk j).support := by
    rw [hi,← Walk.mem_verts_toSubgraph,hUe,Walk.mem_verts_toSubgraph]
    exact havoid
  obtain ⟨S,hSi,_,hSl,hSa,hSb,hs⟩ := slide_oriented U i j hij h' pU hpU heU
  rw [cons_ncard_of_mem h' pU hvU,cons_ncard_of_notMem h' (U.walk j) havoidU] at hs
  refine ⟨S,by omega,?_,?_⟩
  · refine ⟨i,Or.inl ⟨?_,?_⟩,?_⟩
    · simp only [hSa,Equiv.swap_apply_left,hUj]
    · rw [hSb,hi']
    · rw [hSi,NormalTrailSystem.walk_copy_subgraph]
  · intro l hli hlj
    change l ≠ j at hlj
    refine ⟨?_,?_,(hSl l hli hlj).trans (hUe l)⟩
    · simp only [hSa,Equiv.swap_apply_of_ne_of_ne hli hlj,(hUl l hlj).1]
    · rw [hSb,(hUl l hlj).2]

/-- Finishing the exchange preserves every nonroot endpoint tail as a literal
prefix, even when its containing member or its opposite endpoint changes. -/
lemma finish_exposed_with_tails {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (hesc : (R.tail ⟨v,R.root_mem⟩).snd ∉ B) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∀ z : B, z.val ≠ v → ∃ b, ∃ q : G.Walk v b,
        ((R.tail z).append q).IsTrail ∧ IsMember T ((R.tail z).append q) := by
  classical
  obtain ⟨S,hs,ht,htrack,i,hi⟩ := orient_root_start_tracked R
  have hia : i ∈ S.active := (S.start_mem i).mp (hi.symm ▸ S.root_mem)
  let a : B := ⟨S.system.start i,(S.start_mem i).mpr hia⟩
  let b : B := ⟨S.system.finish i,(S.finish_mem i).mpr hia⟩
  have ha : a = ⟨v,S.root_mem⟩ := Subtype.ext hi
  have hab : a ≠ b := fun h ↦ S.system.endpoints_ne i (congrArg Subtype.val h)
  have hd : Disjoint (S.tail a).toSubgraph.edgeSet (S.tail b).reverse.toSubgraph.edgeSet := by
    simpa only [Walk.toSubgraph_reverse] using S.disjoint hab
  have hp := trail_append_of_disjoint (S.trail a) (S.trail b).reverse hd
  have he : (S.system.walk i).toSubgraph = ((S.tail a).append (S.tail b).reverse).toSubgraph := by
    rw [Walk.toSubgraph_append,Walk.toSubgraph_reverse]
    exact S.decomp i hia
  have hnil : ¬(S.tail a).Nil := ha.symm ▸ S.root_nonempty
  let C := S.tail a
  let h := C.adj_snd hnil
  let p := C.tail.append (S.tail b).reverse
  have hform : Walk.cons h p = C.append (S.tail b).reverse :=
    congrArg (fun z : G.Walk a.val v ↦ z.append (S.tail b).reverse) (C.cons_tail_eq hnil)
  have hv : S.system.start i ∈ p.support := by
    rw [hi]
    exact (Walk.mem_support_append_iff _ _).mpr (Or.inl C.tail.end_mem_support)
  have hfirst : C.snd = (R.tail ⟨v,R.root_mem⟩).snd := by
    change (S.tail a).snd = _
    rw [ha,ht]
  have hesc' : C.snd ∉ B := hfirst.symm ▸ hesc
  let j := NormalTrailSystem.owner S.system C.snd
  have hj : j ∉ S.active := fun hh ↦ hesc' ((S.mem_ends_iff_owner_active C.snd).mpr hh)
  have hout : S.system.start i ∉ (S.system.walk j).support := by
    rw [hi]
    exact S.outside j hj
  have hhp : (Walk.cons h p).IsTrail := by rw [hform]; exact hp
  obtain ⟨T,hT,hm,hother⟩ := escape_slide_with_members S.system i h p
    hhp (by rw [hform]; exact he) hv hout
  refine ⟨T,by omega,?_⟩
  intro z hz
  obtain ⟨l,hl,w,hzw,hends,hlg⟩ := tail_partner S z
  by_cases hli : l = i
  · subst l
    have hzb : z = b := by
      apply Subtype.ext
      rcases hends with he | he
      · exact (hz (he.1.symm.trans hi)).elim
      · exact he.2.symm
    subst z
    refine ⟨C.snd,C.tail.reverse,?_,?_⟩
    · have hh := hhp.of_cons.reverse
      simpa only [p,Walk.reverse_append,Walk.reverse_reverse,ht] using hh
    · have hh := isMember_reverse hm
      simpa only [p,Walk.reverse_append,Walk.reverse_reverse,ht] using hh
  · have hlj : l ≠ j := fun heq ↦ hj (heq ▸ hl)
    obtain ⟨hla,hlb,hle⟩ := hother l hli hlj
    refine ⟨w.val,(S.tail w).reverse,?_,l,?_,?_⟩
    · rw [← ht]
      apply trail_append_of_disjoint (S.trail z) (S.trail w).reverse
      simpa only [Walk.toSubgraph_reverse] using S.disjoint hzw
    · simpa only [hla,hlb] using hends
    · rw [hle,hlg,Walk.toSubgraph_append,Walk.toSubgraph_reverse,ht]

/-- Rooted strict improvement with simultaneous endpoint-tail protection. -/
lemma improve_preserving_tails {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∀ z : B, z.val ≠ v →
        (¬G.Adj v z.val ∨ (R.tail z).penultimate = z.val) →
        ∃ b, ∃ q : G.Walk v b,
          ((R.tail z).append q).IsTrail ∧ IsMember T ((R.tail z).append q) := by
  obtain ⟨S,hs,he,_,htail⟩ := expose_escape_preserving_tails R
  obtain ⟨T,hT,hpre⟩ := finish_exposed_with_tails S he
  refine ⟨T,by omega,?_⟩
  intro z hz hp
  simpa only [htail z hz hp] using hpre z hz

end Erdos583TerminalDartsDevelopment
