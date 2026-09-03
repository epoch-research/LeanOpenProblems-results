import Submission.Work

/-! Rooted tail exposure using distinct selected labels only. No endpoint
bijection or ambient path-system normalization is assumed here. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization Erdos583Work.DoubleEscape
namespace Erdos583DistinctTailsDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

structure TailFamily {V : Type*} (G : SimpleGraph V) (v : V) (B : Finset V) where
  root_mem : v ∈ B
  tail : ∀ w : B, G.Walk w.val v
  trail : ∀ w, (tail w).IsTrail
  disjoint : Pairwise fun w z ↦ Disjoint (tail w).toSubgraph.edgeSet (tail z).toSubgraph.edgeSet
  root_nonempty : ¬(tail ⟨v, root_mem⟩).Nil

/-- A permutation of selected labels, preserving each selected slot's vertex
set and the entire edge union. Unselected tails can be left untouched. -/
def Rearranged {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    (S R : TailFamily G v B) : Prop :=
  ∃ e : B ≃ B,
    (∀ w, (S.tail (e w)).toSubgraph.verts = (R.tail w).toSubgraph.verts) ∧
    ∀ d, (∃ w, d ∈ (S.tail w).toSubgraph.edgeSet) ↔
      ∃ w, d ∈ (R.tail w).toSubgraph.edgeSet

lemma rearranged_refl {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    (R : TailFamily G v B) : Rearranged R R := ⟨Equiv.refl _, fun _ ↦ rfl, fun _ ↦ Iff.rfl⟩

lemma rearranged_trans {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    {S R T : TailFamily G v B} (hSR : Rearranged S R) (hRT : Rearranged R T) :
    Rearranged S T := by
  obtain ⟨e, hv, he⟩ := hSR
  obtain ⟨f, hw, hf⟩ := hRT
  exact ⟨f.trans e, fun w ↦ (hv (f w)).trans (hw w), fun d ↦ (he d).trans (hf d)⟩

lemma pivot {V : Type*} [Fintype V] {G : SimpleGraph V} {v : V} {B : Finset V}
    (R : TailFamily G v B) (w : B) (h : G.Adj v w.val)
    (p : G.Walk w.val v) (hroot : R.tail ⟨v, R.root_mem⟩ = Walk.cons h p) :
    ∃ S : TailFamily G v B,
      Rearranged S R ∧
      (S.tail ⟨v, S.root_mem⟩).snd = (R.tail w).penultimate ∧
      ∀ z : B, z.val ≠ v → z ≠ w → S.tail z = R.tail z := by
  classical
  let r : B := ⟨v, R.root_mem⟩
  have hrw : r ≠ w := fun hh ↦ h.ne (congrArg Subtype.val hh)
  have hp : (Walk.cons h p).IsTrail := hroot ▸ R.trail r
  have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet (R.tail w).toSubgraph.edgeSet :=
    hroot ▸ R.disjoint hrw
  obtain ⟨hp', hw', hpw, hu, _, _⟩ :=
    trail_endpoint_slide h p (R.tail w) hp (R.trail w) hd p.end_mem_support
  let q : ∀ z : B, G.Walk z.val v :=
    Function.update (Function.update R.tail r (Walk.cons h (R.tail w)).reverse) w p
  have hqr : q r = (Walk.cons h (R.tail w)).reverse := by simp [q, hrw]
  have hqw : q w = p := by simp [q]
  have hqz (z : B) (hzr : z ≠ r) (hzw : z ≠ w) : q z = R.tail z := by simp [q, hzr, hzw]
  have hpair : (q r).toSubgraph.edgeSet ∪ (q w).toSubgraph.edgeSet =
      (R.tail r).toSubgraph.edgeSet ∪ (R.tail w).toSubgraph.edgeSet := by
    rw [hqr, hqw, Walk.toSubgraph_reverse, hroot]
    rw [Set.union_comm]
    exact hu.symm
  have hq : ∀ z, (q z).IsTrail := by
    intro z
    by_cases hzr : z = r
    · subst z; rw [hqr]; exact hw'.reverse
    · by_cases hzw : z = w
      · subst z; rw [hqw]; exact hp'
      · rw [hqz z hzr hzw]; exact R.trail z
  have hcross (z : B) (hzr : z ≠ r) (hzw : z ≠ w) :
      Disjoint ((q r).toSubgraph.edgeSet ∪ (q w).toSubgraph.edgeSet) (q z).toSubgraph.edgeSet := by
    rw [hpair, hqz z hzr hzw]
    exact disjoint_sup_left.mpr ⟨R.disjoint hzr.symm, R.disjoint hzw.symm⟩
  have hqq : Pairwise fun z t ↦ Disjoint (q z).toSubgraph.edgeSet (q t).toSubgraph.edgeSet := by
    intro z t hzt
    by_cases hzr : z = r
    · subst z
      by_cases htw : t = w
      · subst t; rw [hqr, hqw, Walk.toSubgraph_reverse]; exact hpw.symm
      · exact (disjoint_sup_left.mp (hcross t hzt.symm htw)).1
    · by_cases hzw : z = w
      · subst z
        by_cases htr : t = r
        · subst t; rw [hqr, hqw, Walk.toSubgraph_reverse]; exact hpw
        · exact (disjoint_sup_left.mp (hcross t htr hzt.symm)).2
      · by_cases htr : t = r
        · subst t; exact (disjoint_sup_left.mp (hcross z hzr hzw)).1.symm
        · by_cases htw : t = w
          · subst t; exact (disjoint_sup_left.mp (hcross z hzr hzw)).2.symm
          · rw [hqz z hzr hzw, hqz t htr htw]; exact R.disjoint hzt
  have hU (d : Sym2 V) : (∃ z, d ∈ (q z).toSubgraph.edgeSet) ↔
      ∃ z, d ∈ (R.tail z).toSubgraph.edgeSet := by
    constructor
    · rintro ⟨z, hz⟩
      by_cases hzr : z = r
      · subst z
        have hh : d ∈ (R.tail r).toSubgraph.edgeSet ∪ (R.tail w).toSubgraph.edgeSet :=
          hpair ▸ Or.inl hz
        exact hh.elim (fun he ↦ ⟨r, he⟩) (fun he ↦ ⟨w, he⟩)
      · by_cases hzw : z = w
        · subst z
          have hh : d ∈ (R.tail r).toSubgraph.edgeSet ∪ (R.tail w).toSubgraph.edgeSet :=
            hpair ▸ Or.inr hz
          exact hh.elim (fun he ↦ ⟨r, he⟩) (fun he ↦ ⟨w, he⟩)
        · exact ⟨z, by simpa only [hqz z hzr hzw] using hz⟩
    · rintro ⟨z, hz⟩
      by_cases hzr : z = r
      · subst z
        have hh : d ∈ (q r).toSubgraph.edgeSet ∪ (q w).toSubgraph.edgeSet := hpair.symm ▸ Or.inl hz
        exact hh.elim (fun he ↦ ⟨r, he⟩) (fun he ↦ ⟨w, he⟩)
      · by_cases hzw : z = w
        · subst z
          have hh : d ∈ (q r).toSubgraph.edgeSet ∪ (q w).toSubgraph.edgeSet := hpair.symm ▸ Or.inr hz
          exact hh.elim (fun he ↦ ⟨r, he⟩) (fun he ↦ ⟨w, he⟩)
        · exact ⟨z, by simpa only [hqz z hzr hzw] using hz⟩
  let e := Equiv.swap v w.val
  have heB (x : V) : e x ∈ B ↔ x ∈ B := by
    by_cases hxv : x = v
    · subst x; simp [e, R.root_mem, w.property]
    · by_cases hxw : x = w.val
      · subst x; simp [e, R.root_mem, w.property]
      · simp [e, Equiv.swap_apply_of_ne_of_ne hxv hxw]
  have heout (x : V) (hx : x ∉ B) : e x = x :=
    Equiv.swap_apply_of_ne_of_ne (fun h ↦ hx (h ▸ R.root_mem)) (fun h ↦ hx (h ▸ w.property))
  have hV (z : B) : (q ⟨e z.val, (heB z.val).mpr z.property⟩).toSubgraph.verts =
      (R.tail z).toSubgraph.verts := by
    by_cases hzr : z = r
    · subst z
      have hez : (⟨e r.val, (heB r.val).mpr r.property⟩ : B) = w := by
        apply Subtype.ext; simp [e, r]
      rw [hez, hqw, hroot]
      exact (cons_into_root_verts h p).symm
    · by_cases hzw : z = w
      · subst z
        have hez : (⟨e w.val, (heB w.val).mpr w.property⟩ : B) = r := by
          apply Subtype.ext; simp [e, r]
        rw [hez, hqr, Walk.toSubgraph_reverse]
        exact cons_into_root_verts h (R.tail w)
      · have hez : (⟨e z.val, (heB z.val).mpr z.property⟩ : B) = z := by
          apply Subtype.ext
          exact Equiv.swap_apply_of_ne_of_ne (fun hh ↦ hzr (Subtype.ext hh))
            (fun hh ↦ hzw (Subtype.ext hh))
        rw [hez, hqz z hzr hzw]
  have hne : ¬(q ⟨v, R.root_mem⟩).Nil := by rw [hqr]; simp
  let S : TailFamily G v B :=
    { root_mem := R.root_mem, tail := q, trail := hq, disjoint := hqq, root_nonempty := hne }
  have hSR : Rearranged S R := by
    refine ⟨e.subtypeEquiv (fun x ↦ (heB x).symm), ?_, hU⟩
    exact hV
  refine ⟨S, hSR, ?_, ?_⟩
  · change (q r).snd = (R.tail w).penultimate
    rw [hqr, Walk.snd_reverse, Walk.penultimate_cons_of_not_nil]
    exact Walk.not_nil_of_ne h.ne.symm
  · intro z hzv hzw
    exact hqz z (fun hh ↦ hzv (congrArg Subtype.val hh)) hzw

lemma successor_data {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    (R : TailFamily G v B) :
    ∃ f : V → V, Set.InjOn f (B.erase v : Set V) ∧
      (∀ w : B, w.val ≠ v → f w.val = (R.tail w).penultimate) ∧
      (R.tail ⟨v,R.root_mem⟩).snd ∉ (B.erase v).image f ∧
      (R.tail ⟨v,R.root_mem⟩).penultimate ∉ (B.erase v).image f := by
  classical
  let f (w : V) := if hw : w ∈ B then (R.tail ⟨w,hw⟩).penultimate else w
  have hf : Set.InjOn f (B.erase v : Set V) := by
    intro w hw z hz he
    obtain ⟨hwv, hwB⟩ := Finset.mem_erase.mp hw
    obtain ⟨hzv, hzB⟩ := Finset.mem_erase.mp hz
    have he' : (R.tail ⟨w,hwB⟩).penultimate = (R.tail ⟨z,hzB⟩).penultimate := by
      simpa only [f, dif_pos hwB, dif_pos hzB] using he
    by_contra hwz
    have hi : (⟨w,hwB⟩ : B) ≠ ⟨z,hzB⟩ := fun h ↦ hwz (congrArg Subtype.val h)
    have h1 : s((R.tail ⟨w,hwB⟩).penultimate,v) ∈ (R.tail ⟨w,hwB⟩).toSubgraph.edgeSet :=
      (R.tail ⟨w,hwB⟩).toSubgraph_adj_penultimate (Walk.not_nil_of_ne hwv)
    have h2 : s((R.tail ⟨z,hzB⟩).penultimate,v) ∈ (R.tail ⟨z,hzB⟩).toSubgraph.edgeSet :=
      (R.tail ⟨z,hzB⟩).toSubgraph_adj_penultimate (Walk.not_nil_of_ne hzv)
    rw [he'] at h1
    exact Set.disjoint_left.mp (R.disjoint hi) h1 h2
  have havoid (z : V) (hz : s(v,z) ∈ (R.tail ⟨v,R.root_mem⟩).toSubgraph.edgeSet) :
      z ∉ (B.erase v).image f := by
    intro hh
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hh
    obtain ⟨hwv,hwB⟩ := Finset.mem_erase.mp hw
    have he' : (R.tail ⟨w,hwB⟩).penultimate = z := by simpa only [f,dif_pos hwB] using he
    have h2 : s(v,(R.tail ⟨w,hwB⟩).penultimate) ∈ (R.tail ⟨w,hwB⟩).toSubgraph.edgeSet :=
      ((R.tail ⟨w,hwB⟩).toSubgraph_adj_penultimate (Walk.not_nil_of_ne hwv)).symm
    rw [he'] at h2
    exact Set.disjoint_left.mp (R.disjoint (fun h ↦ hwv (congrArg Subtype.val h).symm)) hz h2
  refine ⟨f,hf,fun w _ ↦ dif_pos w.property,?_,?_⟩
  · exact havoid _ ((R.tail ⟨v,R.root_mem⟩).toSubgraph_adj_snd R.root_nonempty)
  · exact havoid _ ((R.tail ⟨v,R.root_mem⟩).toSubgraph_adj_penultimate R.root_nonempty).symm

lemma realize_escape_orbit {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} {B : Finset V} (R : TailFamily G v B)
    (f : V → V) (hf : Set.InjOn f (B.erase v : Set V))
    (htf : ∀ w : B, w.val ≠ v → f w.val = (R.tail w).penultimate)
    (hx : (R.tail ⟨v,R.root_mem⟩).snd ∉ (B.erase v).image f)
    (N : ℕ)
    (hexit : f^[N] (R.tail ⟨v,R.root_mem⟩).snd ∉ B.erase v)
    (hprev : ∀ n < N, f^[n] (R.tail ⟨v,R.root_mem⟩).snd ∈ B.erase v) :
    ∃ S : TailFamily G v B, Rearranged S R ∧
      (S.tail ⟨v,S.root_mem⟩).snd = f^[N] (R.tail ⟨v,R.root_mem⟩).snd ∧
      (S.tail ⟨v,S.root_mem⟩).snd ∉ B := by
  classical
  let x := (R.tail ⟨v,R.root_mem⟩).snd
  let A := B.erase v
  have hinj := iterate_injective_before_exit A f hf x hx N hprev
  have hreach : ∀ n ≤ N, ∃ S : TailFamily G v B,
      Rearranged S R ∧
      (S.tail ⟨v,S.root_mem⟩).snd = f^[n] x ∧
      ∀ z : B, z.val ≠ v → (∀ m < n, z.val ≠ f^[m] x) → S.tail z = R.tail z := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨R, rearranged_refl R, rfl, fun _ _ _ ↦ rfl⟩
    | succ n ih =>
      intro hn
      obtain ⟨S, hscore, hfirst, htail⟩ := ih (by omega)
      have hw := hprev n (by omega)
      obtain ⟨hwv, hwB⟩ := Finset.mem_erase.mp hw
      let w : B := ⟨f^[n] x, hwB⟩
      have hunprocessed : ∀ m < n, w.val ≠ f^[m] x := by
        intro m hm he
        have hh := hinj n m (by omega) (by omega) he
        omega
      have htw : S.tail w = R.tail w := htail w hwv hunprocessed
      have hstep : ∃ S' : TailFamily G v B,
          Rearranged S' S ∧
          (S'.tail ⟨v,S'.root_mem⟩).snd = (S.tail w).penultimate ∧
          ∀ z : B, z.val ≠ v → z ≠ w → S'.tail z = S.tail z := by
        cases hc : S.tail ⟨v,S.root_mem⟩ with
        | nil => exact (S.root_nonempty (hc ▸ Walk.Nil.nil)).elim
        | @cons _ u _ h p =>
          have huw : u = w.val := by simpa only [hc, Walk.snd_cons] using hfirst
          subst u
          exact pivot S w h p hc
      obtain ⟨S', hs', hf', ht'⟩ := hstep
      refine ⟨S', rearranged_trans hs' hscore, ?_, ?_⟩
      · rw [hf', htw, Function.iterate_succ_apply']
        exact (htf w hwv).symm
      · intro z hzv hz
        have hzw : z ≠ w := fun he ↦ hz n (by omega) (congrArg Subtype.val he)
        exact (ht' z hzv hzw).trans (htail z hzv (fun m hm ↦ hz m (by omega)))
  obtain ⟨S, hs, hfirst, _⟩ := hreach N le_rfl
  refine ⟨S, hs, hfirst, ?_⟩
  intro hB
  have hvne : (S.tail ⟨v,S.root_mem⟩).snd ≠ v :=
    ((S.tail ⟨v,S.root_mem⟩).adj_snd S.root_nonempty).ne.symm
  exact hexit (Finset.mem_erase.mpr ⟨hfirst ▸ hvne, hfirst ▸ hB⟩)


lemma replace_root {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    (R : TailFamily G v B) (C : G.Walk v v) (ht : C.IsTrail)
    (he : C.toSubgraph = (R.tail ⟨v,R.root_mem⟩).toSubgraph) (hn : ¬C.Nil) :
    ∃ S : TailFamily G v B, Rearranged S R ∧ S.tail ⟨v,S.root_mem⟩ = C ∧
      ∀ w : B, w.val ≠ v → S.tail w = R.tail w := by
  classical
  let r : B := ⟨v,R.root_mem⟩
  let q := Function.update R.tail r C
  have hqr : q r = C := by simp [q]
  have hq (w : B) (hw : w ≠ r) : q w = R.tail w := by simp [q,hw]
  have heq (w : B) : (q w).toSubgraph = (R.tail w).toSubgraph := by
    by_cases hw : w = r
    · subst w; rw [hqr]; exact he
    · rw [hq w hw]
  let S : TailFamily G v B :=
    { root_mem := R.root_mem, tail := q,
      trail := by
        intro w
        by_cases hw : w = r
        · subst w; rw [hqr]; exact ht
        · rw [hq w hw]; exact R.trail w
      disjoint := by
        intro w z hwz
        rw [heq w,heq z]
        exact R.disjoint hwz
      root_nonempty := by change ¬(q r).Nil; rw [hqr]; exact hn }
  refine ⟨S, ⟨Equiv.refl _, ?_, ?_⟩, hqr, ?_⟩
  · intro w
    exact congrArg (fun H : G.Subgraph ↦ H.verts) (heq w)
  · intro d
    change (∃ w, d ∈ (q w).toSubgraph.edgeSet) ↔ _
    simp only [heq]
  · intro w hw
    exact hq w (fun hh ↦ hw (congrArg Subtype.val hh))

lemma neighbor_outside_successor_image {V : Type*} {G : SimpleGraph V}
    {v : V} {B : Finset V} (R : TailFamily G v B)
    (f : V → V) (hf : ∀ w : B, w.val ≠ v → f w.val = (R.tail w).penultimate)
    (z : V) (hz : (R.tail ⟨v,R.root_mem⟩).toSubgraph.Adj v z) :
    z ∉ (B.erase v).image f := by
  classical
  intro hh
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hh
  obtain ⟨hwv,hwB⟩ := Finset.mem_erase.mp hw
  have he' : (R.tail ⟨w,hwB⟩).penultimate = z := (hf ⟨w,hwB⟩ hwv).symm.trans he
  have hedge : s(v,(R.tail ⟨w,hwB⟩).penultimate) ∈ (R.tail ⟨w,hwB⟩).toSubgraph.edgeSet :=
    ((R.tail ⟨w,hwB⟩).toSubgraph_adj_penultimate (Walk.not_nil_of_ne hwv)).symm
  rw [he'] at hedge
  exact Set.disjoint_left.mp (R.disjoint (fun h ↦ hwv (congrArg Subtype.val h).symm)) hz hedge

lemma many_distinct_escapes {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} {B : Finset V} (R : TailFamily G v B) :
    ∃ E : Finset V, E.card = ((R.tail ⟨v,R.root_mem⟩).toSubgraph.neighborSet v).ncard ∧
      ∀ z ∈ E, z ∉ B ∧ ∃ S : TailFamily G v B,
        Rearranged S R ∧ (S.tail ⟨v,S.root_mem⟩).snd = z := by
  classical
  let A := B.erase v
  let N := (R.tail ⟨v,R.root_mem⟩).toSubgraph.neighborSet v
  obtain ⟨f,hf,htf,_,_⟩ := successor_data R
  have hstart (z : N) : z.val ∉ A.image f := neighbor_outside_successor_image R f htf z.val z.property
  have hex (z : N) : ∃ n : ℕ, f^[n] z.val ∉ A ∧ ∀ m < n, f^[m] z.val ∈ A :=
    exists_first_exit_of_injective_successor A f hf z.val (hstart z)
  choose n hn hprev using hex
  let exit (z : N) := f^[n z] z.val
  have hinj : Function.Injective exit := by
    intro z w he
    apply Subtype.ext
    exact starts_eq_of_iterate_eq A f hf z.val w.val (hstart z) (hstart w)
      (n z) (n w) (hprev z) (hprev w) he
  have hreach (z : N) : exit z ∉ B ∧ ∃ S : TailFamily G v B,
      Rearranged S R ∧ (S.tail ⟨v,S.root_mem⟩).snd = exit z := by
    obtain ⟨C,hC,hCe,hCn,hCz⟩ := MultipleEscape.closed_trail_first_at_neighbor (R.tail ⟨v,R.root_mem⟩) (R.trail _) z.property
    obtain ⟨R',hR',hroot,htail⟩ := replace_root R C hC hCe hCn
    have hfirst : (R'.tail ⟨v,R'.root_mem⟩).snd = z.val := by rw [hroot,hCz]
    have htf' (w : B) (hw : w.val ≠ v) : f w.val = (R'.tail w).penultimate := by
      rw [htail w hw]; exact htf w hw
    obtain ⟨S,hS,hSfirst,hSout⟩ := realize_escape_orbit R' f hf htf'
      (by rw [hfirst]; exact hstart z) (n z) (by rw [hfirst]; exact hn z)
      (by rw [hfirst]; exact hprev z)
    have hsnd : (S.tail ⟨v,S.root_mem⟩).snd = exit z := by rw [hSfirst,hfirst]
    exact ⟨hsnd ▸ hSout,S,rearranged_trans hS hR',hsnd⟩
  refine ⟨Finset.univ.image exit,?_,?_⟩
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ]
    exact Nat.card_eq_fintype_card.symm
  · intro z hz
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hz
    exact hreach w


/-- Two separately realized neighboring exits for a simple closed root tail. -/
lemma two_distinct_escapes_of_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} {B : Finset V} (R : TailFamily G v B)
    (hc : (R.tail ⟨v,R.root_mem⟩).IsCycle) :
    ∃ x y, x ≠ y ∧ G.Adj v x ∧ G.Adj v y ∧
      (x ∉ B ∧ ∃ S : TailFamily G v B, Rearranged S R ∧
        (S.tail ⟨v,S.root_mem⟩).snd = x) ∧
      (y ∉ B ∧ ∃ S : TailFamily G v B, Rearranged S R ∧
        (S.tail ⟨v,S.root_mem⟩).snd = y) := by
  classical
  obtain ⟨E,hE,hreach⟩ := many_distinct_escapes R
  have htwo : E.card = 2 := hE.trans
    (hc.ncard_neighborSet_toSubgraph_eq_two (R.tail ⟨v,R.root_mem⟩).start_mem_support)
  obtain ⟨x,y,hxy,hE'⟩ := Finset.card_eq_two.mp htwo
  have hx := hreach x (by rw [hE']; simp)
  have hy := hreach y (by rw [hE']; simp)
  have ha (z : V) (hz : ∃ S : TailFamily G v B, Rearranged S R ∧
      (S.tail ⟨v,S.root_mem⟩).snd = z) : G.Adj v z := by
    obtain ⟨S,_,hs⟩ := hz
    rw [← hs]
    exact (S.tail ⟨v,S.root_mem⟩).adj_snd S.root_nonempty
  exact ⟨x,y,hxy,ha x hx.2,ha y hy.2,hx,hy⟩

/-- A nonempty closed root trail already supplies two distinct exits;
simplicity of that closed trail is not needed. -/
lemma two_distinct_escapes {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} {B : Finset V} (R : TailFamily G v B) :
    ∃ x y, x ≠ y ∧ G.Adj v x ∧ G.Adj v y ∧
      (x ∉ B ∧ ∃ S : TailFamily G v B, Rearranged S R ∧
        (S.tail ⟨v,S.root_mem⟩).snd = x) ∧
      (y ∉ B ∧ ∃ S : TailFamily G v B, Rearranged S R ∧
        (S.tail ⟨v,S.root_mem⟩).snd = y) := by
  classical
  obtain ⟨E,hE,hreach⟩ := many_distinct_escapes R
  let C := R.tail ⟨v,R.root_mem⟩
  have hsub : {C.snd,C.penultimate} ⊆ C.toSubgraph.neighborSet v := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact C.toSubgraph_adj_snd R.root_nonempty
    · rw [Set.mem_singleton_iff.mp hz]
      exact (C.toSubgraph_adj_penultimate R.root_nonempty).symm
  have hc : 2 ≤ (C.toSubgraph.neighborSet v).ncard := by
    have hh := Set.ncard_le_ncard hsub
    simpa only [Set.ncard_pair
      (closed_trail_snd_ne_penultimate C (R.trail _) R.root_nonempty)] using hh
  have htwo : 1 < E.card := by
    rw [hE]
    change 1 < (C.toSubgraph.neighborSet v).ncard
    omega
  obtain ⟨x,hxE,y,hyE,hxy⟩ := Finset.one_lt_card.mp htwo
  have hx := hreach x hxE
  have hy := hreach y hyE
  have ha (z : V) (hz : ∃ S : TailFamily G v B, Rearranged S R ∧
      (S.tail ⟨v,S.root_mem⟩).snd = z) : G.Adj v z := by
    obtain ⟨S,_,hs⟩ := hz
    rw [← hs]
    exact (S.tail ⟨v,S.root_mem⟩).adj_snd S.root_nonempty
  exact ⟨x,y,hxy,ha x hx.2,ha y hy.2,hx,hy⟩

/-- The final finite closure argument: a nonempty family of roots, each with
two distinct neighboring roots in Z, forces a cycle entirely in Z. -/
lemma cycle_of_two_zero_successors {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Z : Set V) (W : V → Prop) (hw : ∃ r, W r)
    (hnext : ∀ r, W r → ∃ x y, x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧
      x ∈ Z ∧ y ∈ Z ∧ W x ∧ W y) : ¬(G.induce Z).IsAcyclic := by
  classical
  let S : Set Z := {v | W v.val}
  let H := (G.induce Z).induce S
  have hone : Nonempty S := by
    obtain ⟨r,hr⟩ := hw
    obtain ⟨x,y,_,_,_,hx,_,hWx,_⟩ := hnext r hr
    exact ⟨⟨⟨x,hx⟩,hWx⟩⟩
  have htwo (b : S) : ∃ x y : S, x ≠ y ∧ H.Adj b x ∧ H.Adj b y := by
    obtain ⟨x,y,hxy,hbx,hby,hx,hy,hWx,hWy⟩ := hnext b.val.val b.property
    exact ⟨⟨⟨x,hx⟩,hWx⟩,⟨⟨y,hy⟩,hWy⟩,
      fun hh ↦ hxy (congrArg (fun z : S ↦ z.val.val) hh),hbx,hby⟩
  have he : ∃ a b, H.Adj a b := by
    obtain ⟨a⟩ := hone
    obtain ⟨b,c,_,hab,_⟩ := htwo a
    exact ⟨a,b,hab⟩
  have hstep : ∀ {a b}, H.Adj a b → ∃ c, H.Adj b c ∧ c ≠ a := by
    intro a b _
    obtain ⟨x,y,hxy,hbx,hby⟩ := htwo b
    by_cases hx : x = a
    · exact ⟨y,hby,fun hy ↦ hxy (hx.trans hy.symm)⟩
    · exact ⟨x,hbx,hx⟩
  intro hacyc
  exact TokenObstruction.cycle_of_no_dead_end H he hstep (hacyc.induce S)

end Erdos583DistinctTailsDevelopment
