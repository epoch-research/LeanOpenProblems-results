import Submission.Work

/-! Indexed vertex-set tracking through rooted pivots and repairs. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization
namespace Erdos583VertexTrackingDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

def SameVertices {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (S T : NormalTrailSystem G k) : Prop :=
  ∀ i, (S.walk i).toSubgraph.verts = (T.walk i).toSubgraph.verts

lemma sameVertices_trans {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {S T U : NormalTrailSystem G k} (hST : SameVertices S T) (hTU : SameVertices T U) :
    SameVertices S U := fun i ↦ (hST i).trans (hTU i)

lemma rebuild_vertices {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (e : V ≃ V)
    (heB : ∀ x, e x ∈ B ↔ x ∈ B) (heout : ∀ x, x ∉ B → e x = x)
    (q : ∀ w : B, G.Walk w.val v) (hq : ∀ w, (q w).IsTrail)
    (hqq : Pairwise fun w z ↦ Disjoint (q w).toSubgraph.edgeSet (q z).toSubgraph.edgeSet)
    (hU : ∀ d, (∃ w, d ∈ (q w).toSubgraph.edgeSet) ↔ ∃ w, d ∈ (R.tail w).toSubgraph.edgeSet)
    (hverts : ∀ w : B, (q ⟨e w.val, (heB w.val).mpr w.property⟩).toSubgraph.verts =
      (R.tail w).toSubgraph.verts)
    (hne : ¬(q ⟨v, R.root_mem⟩).Nil) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ S.tail = q ∧ AgreesOutside S R ∧ SameVertices S.system R.system := by
  classical
  let a (i : Fin k) := e (R.system.start i)
  let b (i : Fin k) := e (R.system.finish i)
  have ha (i : Fin k) : a i ∈ B ↔ i ∈ R.active := (heB _).trans (R.start_mem i)
  have hb (i : Fin k) : b i ∈ B ↔ i ∈ R.active := (heB _).trans (R.finish_mem i)
  have hp (i : Fin k) : ∃ p : G.Walk (a i) (b i), p.IsTrail ∧
      (∀ hi : i ∈ R.active, p.toSubgraph =
        (q ⟨a i, (ha i).mpr hi⟩).toSubgraph ⊔ (q ⟨b i, (hb i).mpr hi⟩).toSubgraph) ∧
      (i ∉ R.active → p.toSubgraph = (R.system.walk i).toSubgraph) := by
    by_cases hi : i ∈ R.active
    · let A : B := ⟨a i, (ha i).mpr hi⟩
      let Z : B := ⟨b i, (hb i).mpr hi⟩
      have hAZ : A ≠ Z := fun hh ↦ R.system.endpoints_ne i
        (e.injective (congrArg Subtype.val hh))
      refine ⟨(q A).append (q Z).reverse, ?_, ?_, fun hn ↦ (hn hi).elim⟩
      · apply trail_append_of_disjoint (hq A) (hq Z).reverse
        simpa using hqq hAZ
      · intro _
        simp [A, Z]
    · have hai : a i = R.system.start i := heout _ (fun h ↦ hi ((R.start_mem i).mp h))
      have hbi : b i = R.system.finish i := heout _ (fun h ↦ hi ((R.finish_mem i).mp h))
      refine ⟨(R.system.walk i).copy hai.symm hbi.symm, by simpa using R.system.isTrail i,
        fun hh ↦ (hi hh).elim, fun _ ↦ ?_⟩
      exact NormalTrailSystem.walk_copy_subgraph _ _ _
  choose p hp hpA hpO using hp
  have hcross (w : B) (i : Fin k) (hi : i ∉ R.active) :
      Disjoint (q w).toSubgraph.edgeSet (p i).toSubgraph.edgeSet := by
    rw [hpO i hi]
    apply Set.disjoint_left.mpr
    intro d hd hdi
    obtain ⟨z, hz⟩ := (hU d).mp ⟨w, hd⟩
    exact Set.disjoint_left.mp (R.tail_disjoint_outside z i hi) hz hdi
  have hdis : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet := by
    intro i j hij
    by_cases hi : i ∈ R.active
    · rw [hpA i hi, Subgraph.edgeSet_sup]
      by_cases hj : j ∈ R.active
      · rw [hpA j hj, Subgraph.edgeSet_sup]
        apply disjoint_sup_left.mpr
        constructor <;> apply disjoint_sup_right.mpr
        · constructor
          · apply hqq
            intro hh
            apply hij
            exact endpoint_index_eq R.system (Or.inl rfl)
              (Or.inl (e.injective (congrArg Subtype.val hh)))
          · apply hqq
            intro hh
            apply hij
            exact endpoint_index_eq R.system (Or.inl rfl)
              (Or.inr (e.injective (congrArg Subtype.val hh)))
        · constructor
          · apply hqq
            intro hh
            apply hij
            exact endpoint_index_eq R.system (Or.inr rfl)
              (Or.inl (e.injective (congrArg Subtype.val hh)))
          · apply hqq
            intro hh
            apply hij
            exact endpoint_index_eq R.system (Or.inr rfl)
              (Or.inr (e.injective (congrArg Subtype.val hh)))
      · exact disjoint_sup_left.mpr ⟨hcross _ j hj, hcross _ j hj⟩
    · by_cases hj : j ∈ R.active
      · rw [hpA j hj, Subgraph.edgeSet_sup]
        exact disjoint_sup_right.mpr ⟨(hcross _ i hi).symm, (hcross _ i hi).symm⟩
      · rw [hpO i hi, hpO j hj]
        exact R.system.disjoint hij
  have hends : Function.Bijective (fun x : Fin k × Bool ↦ if x.2 then a x.1 else b x.1) := by
    have hf : (fun x : Fin k × Bool ↦ if x.2 then a x.1 else b x.1) =
        e ∘ (fun x : Fin k × Bool ↦ if x.2 then R.system.start x.1 else R.system.finish x.1) := by
      funext x
      rcases x with ⟨i, c⟩
      cases c <;> rfl
    rw [hf]
    exact e.bijective.comp R.system.endpoint_bijective
  have hqmember (w : B) : ∃ i, ∃ hi : i ∈ R.active,
      (q w).toSubgraph ≤ (p i).toSubgraph := by
    obtain ⟨⟨i, c⟩, hc⟩ := hends.2 w.val
    cases c
    · have hh : b i = w.val := hc
      have hi := (hb i).mp (hh.symm ▸ w.property)
      refine ⟨i, hi, ?_⟩
      rw [hpA i hi]
      have he : (⟨b i, (hb i).mpr hi⟩ : B) = w := Subtype.ext hh
      rw [he]
      exact le_sup_right
    · have hh : a i = w.val := hc
      have hi := (ha i).mp (hh.symm ▸ w.property)
      refine ⟨i, hi, ?_⟩
      rw [hpA i hi]
      have he : (⟨a i, (ha i).mpr hi⟩ : B) = w := Subtype.ext hh
      rw [he]
      exact le_sup_left
  have hcover (d : Sym2 V) : d ∈ G.edgeSet ↔ ∃ i, d ∈ (p i).toSubgraph.edgeSet := by
    constructor
    · intro hd
      obtain ⟨i, hi⟩ := (R.system.cover d).mp hd
      by_cases hia : i ∈ R.active
      · rw [R.decomp i hia, Subgraph.edgeSet_sup] at hi
        have hu : ∃ w, d ∈ (R.tail w).toSubgraph.edgeSet :=
          hi.elim (fun h ↦ ⟨_, h⟩) (fun h ↦ ⟨_, h⟩)
        obtain ⟨w, hw⟩ := (hU d).mpr hu
        obtain ⟨j, _, hj⟩ := hqmember w
        exact ⟨j, Subgraph.edgeSet_mono hj hw⟩
      · exact ⟨i, (hpO i hia).symm ▸ hi⟩
    · rintro ⟨i, hi⟩
      exact (p i).toSubgraph.edgeSet_subset hi
  have hV (i : Fin k) : (p i).toSubgraph.verts = (R.system.walk i).toSubgraph.verts := by
    by_cases hi : i ∈ R.active
    · rw [hpA i hi, R.decomp i hi, Subgraph.verts_sup, Subgraph.verts_sup]
      exact congrArg₂ (· ∪ ·) (hverts ⟨_, (R.start_mem i).mpr hi⟩)
        (hverts ⟨_, (R.finish_mem i).mpr hi⟩)
    · rw [hpO i hi]
  let T : NormalTrailSystem G k :=
    { start := a, finish := b, walk := p, isTrail := hp,
      endpoint_bijective := hends, disjoint := hdis, cover := hcover }
  let S : RootedTailSystem G k v B :=
    { system := T, active := R.active, root_mem := R.root_mem,
      tail := q, trail := hq, disjoint := hqq,
      start_mem := ha, finish_mem := hb, decomp := hpA,
      outside := by
        intro i hi
        have hv := R.outside i hi
        change v ∉ (p i).support
        rw [← Walk.mem_verts_toSubgraph, hV, Walk.mem_verts_toSubgraph]
        exact hv
      root_nonempty := hne }
  refine ⟨S, ?_, rfl, ⟨rfl, ?_⟩, hV⟩
  · unfold NormalTrailSystem.score
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg Set.ncard (hV i)
  intro i hi
  refine ⟨heout _ (fun h ↦ hi ((R.start_mem i).mp h)),
    heout _ (fun h ↦ hi ((R.finish_mem i).mp h)), hpO i hi⟩

lemma pivot_vertices {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (w : B) (h : G.Adj v w.val)
    (p : G.Walk w.val v) (hroot : R.tail ⟨v, R.root_mem⟩ = Walk.cons h p) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧
      (S.tail ⟨v, S.root_mem⟩).snd = (R.tail w).penultimate ∧
      (∀ z : B, z.val ≠ v → z ≠ w → S.tail z = R.tail z) ∧ AgreesOutside S R ∧ SameVertices S.system R.system := by
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
  obtain ⟨S, hscore, htail, htrack, hVs⟩ := rebuild_vertices R e heB heout q hq hqq hU hV hne
  refine ⟨S, hscore, ?_, ?_, htrack, hVs⟩
  · rw [htail, hqr, Walk.snd_reverse, Walk.penultimate_cons_of_not_nil]
    exact Walk.not_nil_of_ne h.ne.symm
  · intro z hzv hzw
    rw [htail, hqz z (fun hh ↦ hzv (congrArg Subtype.val hh)) hzw]

lemma expose_escape_vertices {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (Z : Set V)
    (hZfirst : (R.tail ⟨v,R.root_mem⟩).snd ∉ Z)
    (hZedge : ∀ z ∈ Z, s(v,z) ∈ (R.tail ⟨v,R.root_mem⟩).toSubgraph.edgeSet) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ (S.tail ⟨v, S.root_mem⟩).snd ∉ B ∧
      (S.tail ⟨v,S.root_mem⟩).snd ∉ Z ∧ AgreesOutside S R ∧ SameVertices S.system R.system := by
  classical
  let A := B.erase v
  let f (w : V) := if hw : w ∈ B then (R.tail ⟨w,hw⟩).penultimate else w
  let x := (R.tail ⟨v,R.root_mem⟩).snd
  have hf : Set.InjOn f (A : Set V) := by
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
  have hx : x ∉ A.image f := by
    intro hh
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hh
    obtain ⟨hwv, hwB⟩ := Finset.mem_erase.mp hw
    have he' : (R.tail ⟨w,hwB⟩).penultimate = x := by simpa only [f, dif_pos hwB] using he
    have h1 : s(v,x) ∈ (R.tail ⟨v,R.root_mem⟩).toSubgraph.edgeSet :=
      (R.tail ⟨v,R.root_mem⟩).toSubgraph_adj_snd R.root_nonempty
    have h2 : s(v,(R.tail ⟨w,hwB⟩).penultimate) ∈ (R.tail ⟨w,hwB⟩).toSubgraph.edgeSet :=
      ((R.tail ⟨w,hwB⟩).toSubgraph_adj_penultimate (Walk.not_nil_of_ne hwv)).symm
    rw [he'] at h2
    exact Set.disjoint_left.mp (R.disjoint (fun h ↦ hwv (congrArg Subtype.val h).symm)) h1 h2
  have hfZ (w : V) (hw : w ∈ A) : f w ∉ Z := by
    obtain ⟨hwv, hwB⟩ := Finset.mem_erase.mp hw
    intro hz
    have he : f w = (R.tail ⟨w,hwB⟩).penultimate := dif_pos hwB
    have h1 := hZedge (f w) hz
    have h2 : s(v,f w) ∈ (R.tail ⟨w,hwB⟩).toSubgraph.edgeSet := by
      rw [he]
      exact ((R.tail ⟨w,hwB⟩).toSubgraph_adj_penultimate (Walk.not_nil_of_ne hwv)).symm
    exact Set.disjoint_left.mp (R.disjoint (fun h ↦ hwv (congrArg Subtype.val h).symm)) h1 h2
  obtain ⟨N, hexit, hprev⟩ := exists_first_exit_of_injective_successor A f hf x hx
  have hinj := iterate_injective_before_exit A f hf x hx N hprev
  have hreach : ∀ n ≤ N, ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧
      (S.tail ⟨v,S.root_mem⟩).snd = f^[n] x ∧
      (∀ z : B, z.val ≠ v → (∀ m < n, z.val ≠ f^[m] x) → S.tail z = R.tail z) ∧
      AgreesOutside S R ∧ SameVertices S.system R.system := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨R, rfl, rfl, (fun _ _ _ ↦ rfl), agreesOutside_refl R, (fun _ ↦ rfl)⟩
    | succ n ih =>
      intro hn
      obtain ⟨S, hscore, hfirst, htail, htrack,hVs⟩ := ih (by omega)
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
          (∀ z : B, z.val ≠ v → z ≠ w → S'.tail z = S.tail z) ∧ AgreesOutside S' S ∧ SameVertices S'.system S.system := by
        cases hc : S.tail ⟨v,S.root_mem⟩ with
        | nil => exact (S.root_nonempty (hc ▸ Walk.Nil.nil)).elim
        | @cons _ u _ h p =>
          have huw : u = w.val := by simpa only [hc, Walk.snd_cons] using hfirst
          subst u
          exact pivot_vertices S w h p hc
      obtain ⟨S', hs', hf', ht', htr',hVs'⟩ := hstep
      refine ⟨S', hs'.trans hscore, ?_, ?_, agreesOutside_trans htr' htrack,sameVertices_trans hVs' hVs⟩
      · rw [hf', htw, Function.iterate_succ_apply']
        change (R.tail ⟨f^[n] x,hwB⟩).penultimate =
          if h : f^[n] x ∈ B then (R.tail ⟨f^[n] x,h⟩).penultimate else f^[n] x
        rw [dif_pos hwB]
      · intro z hzv hz
        have hzw : z ≠ w := fun he ↦ hz n (by omega) (congrArg Subtype.val he)
        exact (ht' z hzv hzw).trans (htail z hzv (fun m hm ↦ hz m (by omega)))
  obtain ⟨S, hs, hfirst, _, htrack,hVs⟩ := hreach N le_rfl
  refine ⟨S, hs, ?_, ?_, htrack,hVs⟩
  · intro hB
    have hvne : (S.tail ⟨v,S.root_mem⟩).snd ≠ v :=
      ((S.tail ⟨v,S.root_mem⟩).adj_snd S.root_nonempty).ne.symm
    exact hexit (Finset.mem_erase.mpr ⟨hfirst ▸ hvne, hfirst ▸ hB⟩)
  rw [hfirst]
  cases N with
  | zero => exact hZfirst
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact hfZ _ (hprev n (by omega))

lemma orient_root_start_vertices {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ S.tail = R.tail ∧ AgreesOutside S R ∧
      (∃ i, S.system.start i = v) ∧ SameVertices S.system R.system := by
  classical
  let eps (i : Fin k) := decide (R.system.finish i = v)
  obtain ⟨T, hs, ht⟩ := R.system.orient eps
  have ha (i : Fin k) : T.start i ∈ B ↔ i ∈ R.active := by
    rw [(ht i).1]
    split_ifs <;> first | exact R.finish_mem i | exact R.start_mem i
  have hb (i : Fin k) : T.finish i ∈ B ↔ i ∈ R.active := by
    rw [(ht i).2.1]
    split_ifs <;> first | exact R.start_mem i | exact R.finish_mem i
  have hd (i : Fin k) (hi : i ∈ R.active) : (T.walk i).toSubgraph =
      (R.tail ⟨T.start i, (ha i).mpr hi⟩).toSubgraph ⊔
      (R.tail ⟨T.finish i, (hb i).mpr hi⟩).toSubgraph := by
    rw [(ht i).2.2, R.decomp i hi]
    by_cases he : eps i = true
    · have h1 : (⟨T.start i, (ha i).mpr hi⟩ : B) =
          ⟨R.system.finish i, (R.finish_mem i).mpr hi⟩ := by
        apply Subtype.ext; simpa [he] using (ht i).1
      have h2 : (⟨T.finish i, (hb i).mpr hi⟩ : B) =
          ⟨R.system.start i, (R.start_mem i).mpr hi⟩ := by
        apply Subtype.ext; simpa [he] using (ht i).2.1
      rw [h1, h2, sup_comm]
    · have h1 : (⟨T.start i, (ha i).mpr hi⟩ : B) =
          ⟨R.system.start i, (R.start_mem i).mpr hi⟩ := by
        apply Subtype.ext; simpa [he] using (ht i).1
      have h2 : (⟨T.finish i, (hb i).mpr hi⟩ : B) =
          ⟨R.system.finish i, (R.finish_mem i).mpr hi⟩ := by
        apply Subtype.ext; simpa [he] using (ht i).2.1
      rw [h1, h2]
  let S : RootedTailSystem G k v B :=
    { system := T, active := R.active, root_mem := R.root_mem,
      tail := R.tail, trail := R.trail, disjoint := R.disjoint,
      start_mem := ha, finish_mem := hb, decomp := hd,
      outside := by
        intro i hi
        rw [← Walk.mem_verts_toSubgraph, (ht i).2.2, Walk.mem_verts_toSubgraph]
        exact R.outside i hi
      root_nonempty := R.root_nonempty }
  refine ⟨S, hs, rfl, ⟨rfl,?_⟩, ?_,fun i ↦ congrArg Subgraph.verts (ht i).2.2⟩
  · intro i hi
    have hfin : R.system.finish i ≠ v := fun hh ↦
      hi ((R.finish_mem i).mp (hh.symm ▸ R.root_mem))
    exact ⟨by simpa [eps,hfin] using (ht i).1,
      by simpa [eps,hfin] using (ht i).2.1,(ht i).2.2⟩
  let i := NormalTrailSystem.owner R.system v
  rcases NormalTrailSystem.owner_spec R.system v with hv | hv
  · have hn : R.system.finish i ≠ v := fun he ↦ R.system.endpoints_ne i (hv.symm.trans he.symm)
    exact ⟨i, by simpa [S, eps, hn] using (ht i).1.trans (by simpa [eps, hn] using hv.symm)⟩
  · have hv' : R.system.finish i = v := hv.symm
    refine ⟨i, ?_⟩
    change T.start i = v
    rw [(ht i).1]
    simp [eps, hv']

lemma escape_slide_vertices {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) {y : V}
    (h : G.Adj (T.start i) y) (p : G.Walk y (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support)
    (havoid : T.start i ∉ (T.walk (NormalTrailSystem.owner T y)).support) :
    ∃ S : NormalTrailSystem G k, S.score = T.score + 1 ∧
      (∀ l, l ≠ i → l ≠ NormalTrailSystem.owner T y →
        (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      ∀ l, l ≠ NormalTrailSystem.owner T y →
        (S.walk l).toSubgraph.verts = (T.walk l).toSubgraph.verts := by
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
  obtain ⟨S,hSi,_,hSl,_,_,hs⟩ := slide_oriented U i j hij h' pU hpU heU
  rw [cons_ncard_of_mem h' pU hvU,cons_ncard_of_notMem h' (U.walk j) havoidU] at hs
  refine ⟨S,by omega,(fun l hli hlj ↦ (hSl l hli hlj).trans (hUe l)),?_⟩
  intro l hlj
  by_cases hli : l=i
  · subst l
    rw [hSi,←hUe i,heU,cons_verts]
    exact (Set.insert_eq_of_mem (pU.mem_verts_toSubgraph.mpr hvU)).symm
  · rw [hSl l hli hlj,hUe]

lemma finish_exposed_vertices {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (hesc : (R.tail ⟨v,R.root_mem⟩).snd ∉ B) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∃ j : Fin k, j ∉ R.active ∧
        (∀ l, l ∉ R.active → l ≠ j → (T.walk l).toSubgraph = (R.system.walk l).toSubgraph) ∧
        ∀ l, l ≠ j → (T.walk l).toSubgraph.verts = (R.system.walk l).toSubgraph.verts := by
  classical
  obtain ⟨S,hs,ht,htrack,⟨i,hi⟩,hVs⟩ := orient_root_start_vertices R
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
  obtain ⟨T,hT,hTl,hTv⟩ := escape_slide_vertices S.system i h p
    (by rw [hform]; exact hp) (by rw [hform]; exact he) hv hout
  have hjR : j ∉ R.active := htrack.1 ▸ hj
  refine ⟨T,by omega,j,hjR,?_,?_⟩
  · intro l hl hlj
    have hli : l ≠ i := fun hh ↦ hl (hh ▸ (htrack.1 ▸ hia))
    exact (hTl l hli hlj).trans ((htrack.2 l hl).2.2)

  · intro l hlj
    exact (hTv l hlj).trans (hVs l)


/-- Rooted repair preserves every active indexed vertex set. Only one outside
member gains a vertex, and every other outside subgraph remains unchanged. -/
lemma repair_active_vertices {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∃ j : Fin k, j ∉ R.active ∧
        (∀ l, l ∉ R.active → l ≠ j → (T.walk l).toSubgraph = (R.system.walk l).toSubgraph) ∧
        ∀ l, l ≠ j → (T.walk l).toSubgraph.verts = (R.system.walk l).toSubgraph.verts := by
  obtain ⟨S,hs,hesc,_,htrack,hVs⟩ := expose_escape_vertices R ∅ (by simp) (by simp)
  obtain ⟨T,hT,j,hj,hTe,hTv⟩ := finish_exposed_vertices S hesc
  refine ⟨T,by omega,j,htrack.1 ▸ hj,?_,fun l hlj ↦ (hTv l hlj).trans (hVs l)⟩
  intro l hl hlj
  exact (hTe l (htrack.1.symm ▸ hl) hlj).trans ((htrack.2 l hl).2.2)

lemma walk_vertex_has_subgraph_neighbor {V : Type*} {G : SimpleGraph V} {a b x : V}
    (p : G.Walk a b) (hn : ¬p.Nil) (hx : x ∈ p.toSubgraph.verts) :
    ∃ y, p.toSubgraph.Adj x y := by
  have hx' := p.mem_verts_toSubgraph.mp hx
  obtain ⟨e,he,hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hn).mp hx'
  induction e using Sym2.ind with
  | h u v =>
    have huv : p.toSubgraph.Adj u v := p.mem_edges_toSubgraph.mpr he
    have hxuv : x=u ∨ x=v := by simpa using hxe
    rcases hxuv with rfl | rfl
    · exact ⟨v,huv⟩
    · exact ⟨u,huv.symm⟩

/-- On the vertex set of an induced two-edge path, every nonempty walk spanning
all three vertices has exactly that subgraph. No traversal uniqueness is needed. -/
lemma chordless_three_verts_determine {V : Type*} {G : SimpleGraph V}
    {a v b u w : V} (hav : G.Adj a v) (hvb : G.Adj v b) (hab : ¬G.Adj a b)
    (p : G.Walk u w) (hn : ¬p.Nil)
    (he : p.toSubgraph.verts = (G.subgraphOfAdj hav ⊔ G.subgraphOfAdj hvb).verts) :
    p.toSubgraph = G.subgraphOfAdj hav ⊔ G.subgraphOfAdj hvb := by
  have hmem (x : V) : x ∈ p.toSubgraph.verts ↔ x=a ∨ x=v ∨ x=b := by
    rw [he]
    simp only [Subgraph.verts_sup,subgraphOfAdj_verts,Set.mem_union,Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  have hav' : p.toSubgraph.Adj a v := by
    obtain ⟨t,ht⟩ := walk_vertex_has_subgraph_neighbor p hn ((hmem a).mpr (Or.inl rfl))
    rcases (hmem t).mp (p.toSubgraph.edge_vert ht.symm) with rfl | rfl | rfl
    · exact (ht.ne rfl).elim
    · exact ht
    · exact (hab (p.toSubgraph.adj_sub ht)).elim
  have hvb' : p.toSubgraph.Adj v b := by
    obtain ⟨t,ht⟩ := walk_vertex_has_subgraph_neighbor p hn ((hmem b).mpr (Or.inr (Or.inr rfl)))
    rcases (hmem t).mp (p.toSubgraph.edge_vert ht.symm) with rfl | rfl | rfl
    · exact (hab (p.toSubgraph.adj_sub ht.symm)).elim
    · exact ht.symm
    · exact (ht.ne rfl).elim
  apply le_antisymm
  · refine ⟨fun x hx ↦ he ▸ hx,?_⟩
    intro x y hxy
    have hx := (hmem x).mp (p.toSubgraph.edge_vert hxy)
    have hy := (hmem y).mp (p.toSubgraph.edge_vert hxy.symm)
    have hGxy := p.toSubgraph.adj_sub hxy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp_all [Subgraph.sup_adj,subgraphOfAdj_adj,adj_comm]
  · exact sup_le (subgraphOfAdj_le_of_adj _ hav') (subgraphOfAdj_le_of_adj _ hvb')

/-- An internal chordless three-vertex member survives a rooted repair in full,
although it is active and passes through the defect root. -/
lemma repair_chordless_three_path {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (l : Fin k) (hl : l ∈ R.active) {a b : V}
    (hav : G.Adj a v) (hvb : G.Adj v b) (hab : ¬G.Adj a b)
    (he : (R.system.walk l).toSubgraph = G.subgraphOfAdj hav ⊔ G.subgraphOfAdj hvb) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      (T.walk l).toSubgraph = (R.system.walk l).toSubgraph := by
  obtain ⟨T,hT,j,hj,_,hTv⟩ := repair_active_vertices R
  have hlj : l ≠ j := fun hh ↦ hj (hh ▸ hl)
  refine ⟨T,hT,?_⟩
  rw [he]
  apply chordless_three_verts_determine hav hvb hab (T.walk l)
    (Walk.not_nil_of_ne (T.endpoints_ne l))
  rw [hTv l hlj,he]

end Erdos583VertexTrackingDevelopment
