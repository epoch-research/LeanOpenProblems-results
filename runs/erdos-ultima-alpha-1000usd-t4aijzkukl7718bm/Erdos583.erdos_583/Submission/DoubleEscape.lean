import Submission.Work

/-! Two distinct escape routes for a rooted tail exchange. -/

open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization
namespace Erdos583DoubleEscapeDevelopment
open scoped Classical

set_option maxHeartbeats 1200000

/-- Two successor chains starting outside the partial image cannot meet before
or at their first exits, unless their starting points coincide. -/
lemma starts_eq_of_iterate_eq {α : Type*} [DecidableEq α]
    (A : Finset α) (f : α → α) (hf : Set.InjOn f (A : Set α))
    (x y : α) (hx : x ∉ A.image f) (hy : y ∉ A.image f)
    (n m : ℕ) (hn : ∀ i < n, f^[i] x ∈ A) (hm : ∀ j < m, f^[j] y ∈ A)
    (he : f^[n] x = f^[m] y) : x = y := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact he
    | succ m =>
      apply False.elim
      apply hx
      refine Finset.mem_image.mpr ⟨f^[m] y, hm m (by omega), ?_⟩
      simpa only [Function.iterate_zero_apply, Function.iterate_succ_apply'] using he.symm
  | succ n ih =>
    cases m with
    | zero =>
      apply False.elim
      apply hy
      refine Finset.mem_image.mpr ⟨f^[n] x, hn n (by omega), ?_⟩
      simpa only [Function.iterate_zero_apply, Function.iterate_succ_apply'] using he
    | succ m =>
      apply ih m (fun i hi ↦ hn i (by omega)) (fun j hj ↦ hm j (by omega))
      apply hf (hn n (by omega)) (hm m (by omega))
      simpa only [Function.iterate_succ_apply'] using he

/-- Reversing the closed root tail changes no member of the original system. -/
lemma reverse_root_tracked {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) :
    ∃ S : RootedTailSystem G k v B,
      S.system = R.system ∧
      S.tail ⟨v,S.root_mem⟩ = (R.tail ⟨v,R.root_mem⟩).reverse ∧
      (∀ w : B, w.val ≠ v → S.tail w = R.tail w) ∧ AgreesOutside S R := by
  classical
  let r : B := ⟨v,R.root_mem⟩
  let q := Function.update R.tail r (R.tail r).reverse
  have hqr : q r = (R.tail r).reverse := by simp [q]
  have hq (w : B) (hw : w ≠ r) : q w = R.tail w := by simp [q,hw]
  have he (w : B) : (q w).toSubgraph = (R.tail w).toSubgraph := by
    by_cases hw : w = r
    · subst w; rw [hqr,Walk.toSubgraph_reverse]
    · rw [hq w hw]
  let S : RootedTailSystem G k v B :=
    { system := R.system, active := R.active, root_mem := R.root_mem,
      tail := q,
      trail := by
        intro w
        by_cases hw : w = r
        · subst w; rw [hqr]; exact (R.trail r).reverse
        · rw [hq w hw]; exact R.trail w
      disjoint := by
        intro w z hwz
        rw [he w,he z]
        exact R.disjoint hwz
      start_mem := R.start_mem, finish_mem := R.finish_mem,
      decomp := by intro i hi; rw [he,he]; exact R.decomp i hi
      outside := R.outside,
      root_nonempty := by
        change ¬(q r).Nil
        rw [hqr,Walk.nil_reverse]
        exact R.root_nonempty }
  refine ⟨S,rfl,hqr,?_,rfl,fun _ _ ↦ ⟨rfl,rfl,rfl⟩⟩
  intro w hw
  exact hq w (fun he ↦ hw (congrArg Subtype.val he))

/-- An explicitly chosen nonrepeating successor orbit can be realized by
score-preserving pivots, with every outside member unchanged. -/
lemma realize_escape_orbit {V : Type*} [Fintype V] {G : SimpleGraph V}
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
      (S.tail ⟨v,S.root_mem⟩).snd ∉ B ∧ AgreesOutside S R := by
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
  obtain ⟨S, hs, hfirst, _, htrack⟩ := hreach N le_rfl
  refine ⟨S, hs, hfirst, ?_, htrack⟩
  intro hB
  have hvne : (S.tail ⟨v,S.root_mem⟩).snd ≠ v :=
    ((S.tail ⟨v,S.root_mem⟩).adj_snd S.root_nonempty).ne.symm
  exact hexit (Finset.mem_erase.mpr ⟨hfirst ▸ hvne, hfirst ▸ hB⟩)

/-- The nonroot tails define an injective partial successor. Both neighbors
of the closed root tail lie outside its image. -/
lemma successor_data {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) :
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

/-- The two orientations of the closed root tail expose distinct escape vertices. -/
lemma two_distinct_escapes {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B) :
    ∃ S T : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ T.system.score = R.system.score ∧
      (S.tail ⟨v,S.root_mem⟩).snd ∉ B ∧ (T.tail ⟨v,T.root_mem⟩).snd ∉ B ∧
      (S.tail ⟨v,S.root_mem⟩).snd ≠ (T.tail ⟨v,T.root_mem⟩).snd ∧
      AgreesOutside S R ∧ AgreesOutside T R := by
  classical
  obtain ⟨f,hf,htf,hx,hy⟩ := successor_data R
  let x := (R.tail ⟨v,R.root_mem⟩).snd
  let y := (R.tail ⟨v,R.root_mem⟩).penultimate
  have hxy : x ≠ y := closed_trail_snd_ne_penultimate _ (R.trail _) R.root_nonempty
  obtain ⟨N,hexit,hprev⟩ := exists_first_exit_of_injective_successor (B.erase v) f hf x hx
  obtain ⟨M,hexit',hprev'⟩ := exists_first_exit_of_injective_successor (B.erase v) f hf y hy
  have hdistinct : f^[N] x ≠ f^[M] y := fun he ↦ hxy
    (starts_eq_of_iterate_eq (B.erase v) f hf x y hx hy N M hprev hprev' he)
  obtain ⟨S,hS,hSfirst,hSout,hStrack⟩ := realize_escape_orbit R f hf htf hx N hexit hprev
  obtain ⟨R',hR',hroot,htail,htrack⟩ := reverse_root_tracked R
  have hfirst : (R'.tail ⟨v,R'.root_mem⟩).snd = y := by rw [hroot,Walk.snd_reverse]
  have htf' (w : B) (hw : w.val ≠ v) : f w.val = (R'.tail w).penultimate := by
    rw [htail w hw]; exact htf w hw
  obtain ⟨T,hT,hTfirst,hTout,hTtrack⟩ := realize_escape_orbit R' f hf htf'
    (by rw [hfirst]; exact hy) M (by rw [hfirst]; exact hexit')
    (by rw [hfirst]; exact hprev')
  refine ⟨S,T,hS,?_,hSout,hTout,?_,hStrack,agreesOutside_trans hTtrack htrack⟩
  · rw [hT,hR']
  · rw [hSfirst,hTfirst,hfirst]
    exact hdistinct

/-- A rooted exchange can expose an escape avoiding any one prescribed vertex. -/
lemma expose_escape_avoiding {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B) (z : V) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ (S.tail ⟨v,S.root_mem⟩).snd ∉ B ∧
      (S.tail ⟨v,S.root_mem⟩).snd ≠ z ∧ AgreesOutside S R := by
  obtain ⟨S,T,hS,hT,hSout,hTout,hne,hStrack,hTtrack⟩ := two_distinct_escapes R
  by_cases hz : (S.tail ⟨v,S.root_mem⟩).snd = z
  · exact ⟨T,hT,hTout,fun he ↦ hne (hz.trans he.symm),hTtrack⟩
  · exact ⟨S,hS,hSout,hz,hStrack⟩

/-- A strict rooted repair can preserve any one outside member as a prefix,
without a special root-edge hypothesis. -/
lemma repair_protected_any {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (l : Fin k) (hl : l ∉ R.active)
    (r : G.Walk (R.system.start l) (R.system.finish l)) (hr : r.IsTrail)
    (hre : (R.system.walk l).toSubgraph = r.toSubgraph) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∃ t, ∃ q : G.Walk (R.system.finish l) t,
        (r.append q).IsTrail ∧ IsMember T (r.append q) := by
  classical
  obtain ⟨S,hs,hesc,havoid,htrack⟩ := expose_escape_avoiding R (R.system.start l)
  obtain ⟨ha,hb,he⟩ := htrack.2 l hl
  let rS := r.copy ha.symm hb.symm
  have hrS : rS.IsTrail := by simpa [rS] using hr
  have hrSe : (S.system.walk l).toSubgraph = rS.toSubgraph := by
    rw [NormalTrailSystem.walk_copy_subgraph]
    exact he.trans hre
  have hprot : (S.tail ⟨v,S.root_mem⟩).snd ≠ S.system.start l := by simpa [ha] using havoid
  obtain ⟨T,hT,t,q,hq,hm⟩ := finish_exposed_protected S l (htrack.1.symm ▸ hl) rS hrS hrSe hesc hprot
  obtain ⟨q',hq',hm'⟩ := extension_of_copy r ha.symm hb.symm q hq hm
  exact ⟨T,by omega,t,q',hq',hm'⟩

end Erdos583DoubleEscapeDevelopment
