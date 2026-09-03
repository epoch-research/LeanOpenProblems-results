import Submission.Work

/-! Tracking a shortened member through a rooted exchange. This is intermediate
work toward simplicity of maximum-score normal trail systems. -/

open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
namespace Erdos583InternalDevelopment

set_option maxHeartbeats 1200000

/-- The active index set agrees, and every outside member keeps its endpoints
and its whole subgraph. -/
def AgreesOutside {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (S R : RootedTailSystem G k v B) : Prop :=
  S.active = R.active ∧ ∀ i, i ∉ R.active →
    S.system.start i = R.system.start i ∧ S.system.finish i = R.system.finish i ∧
    (S.system.walk i).toSubgraph = (R.system.walk i).toSubgraph

lemma agreesOutside_refl {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) : AgreesOutside R R := ⟨rfl, fun _ _ ↦ ⟨rfl,rfl,rfl⟩⟩

lemma agreesOutside_trans {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    {S R T : RootedTailSystem G k v B} (hSR : AgreesOutside S R)
    (hRT : AgreesOutside R T) : AgreesOutside S T := by
  refine ⟨hSR.1.trans hRT.1, ?_⟩
  intro i hi
  have h1 := hSR.2 i (hRT.1.symm ▸ hi)
  have h2 := hRT.2 i hi
  exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

/-- Rebuild the active members after relabelling their endpoints and replacing
the tail partition. Per-index vertex-set preservation gives exact score preservation. -/
lemma rebuild_tracked {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (e : V ≃ V)
    (heB : ∀ x, e x ∈ B ↔ x ∈ B) (heout : ∀ x, x ∉ B → e x = x)
    (q : ∀ w : B, G.Walk w.val v) (hq : ∀ w, (q w).IsTrail)
    (hqq : Pairwise fun w z ↦ Disjoint (q w).toSubgraph.edgeSet (q z).toSubgraph.edgeSet)
    (hU : ∀ d, (∃ w, d ∈ (q w).toSubgraph.edgeSet) ↔ ∃ w, d ∈ (R.tail w).toSubgraph.edgeSet)
    (hverts : ∀ w : B, (q ⟨e w.val, (heB w.val).mpr w.property⟩).toSubgraph.verts =
      (R.tail w).toSubgraph.verts)
    (hne : ¬(q ⟨v, R.root_mem⟩).Nil) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ S.tail = q ∧ AgreesOutside S R := by
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
  refine ⟨S, ?_, rfl, rfl, ?_⟩
  · unfold NormalTrailSystem.score
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg Set.ncard (hV i)
  intro i hi
  refine ⟨heout _ (fun h ↦ hi ((R.start_mem i).mp h)),
    heout _ (fun h ↦ hi ((R.finish_mem i).mp h)), hpO i hi⟩
/-
  unfold NormalTrailSystem.score
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg Set.ncard (hV i)
-/

/-- A uniform pivot: transpose the root and the first neighbor among the
endpoint labels, and exchange their tails after moving the first edge. It also
handles the case in which the two labels belong to the same original member. -/
lemma pivot_tracked {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (w : B) (h : G.Adj v w.val)
    (p : G.Walk w.val v) (hroot : R.tail ⟨v, R.root_mem⟩ = Walk.cons h p) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧
      (S.tail ⟨v, S.root_mem⟩).snd = (R.tail w).penultimate ∧
      (∀ z : B, z.val ≠ v → z ≠ w → S.tail z = R.tail z) ∧ AgreesOutside S R := by
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
  obtain ⟨S, hscore, htail, htrack⟩ := rebuild_tracked R e heB heout q hq hqq hU hV hne
  refine ⟨S, hscore, ?_, ?_, htrack⟩
  · rw [htail, hqr, Walk.snd_reverse, Walk.penultimate_cons_of_not_nil]
    exact Walk.not_nil_of_ne h.ne.symm
  · intro z hzv hzw
    rw [htail, hqz z (fun hh ↦ hzv (congrArg Subtype.val hh)) hzw]


/-- Repeated score-preserving pivots expose a first neighbor outside the blocked
endpoint set. The induction preserves the exact original unprocessed tails. -/
lemma expose_escape_tracked {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (Z : Set V)
    (hZfirst : (R.tail ⟨v,R.root_mem⟩).snd ∉ Z)
    (hZedge : ∀ z ∈ Z, s(v,z) ∈ (R.tail ⟨v,R.root_mem⟩).toSubgraph.edgeSet) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ (S.tail ⟨v, S.root_mem⟩).snd ∉ B ∧
      (S.tail ⟨v,S.root_mem⟩).snd ∉ Z ∧ AgreesOutside S R := by
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
        change (R.tail ⟨f^[n] x,hwB⟩).penultimate =
          if h : f^[n] x ∈ B then (R.tail ⟨f^[n] x,h⟩).penultimate else f^[n] x
        rw [dif_pos hwB]
      · intro z hzv hz
        have hzw : z ≠ w := fun he ↦ hz n (by omega) (congrArg Subtype.val he)
        exact (ht' z hzv hzw).trans (htail z hzv (fun m hm ↦ hz m (by omega)))
  obtain ⟨S, hs, hfirst, _, htrack⟩ := hreach N le_rfl
  refine ⟨S, hs, ?_, ?_, htrack⟩
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
/-
  intro hB
  have hvne : (S.tail ⟨v,S.root_mem⟩).snd ≠ v :=
    ((S.tail ⟨v,S.root_mem⟩).adj_snd S.root_nonempty).ne.symm
  exact hexit (Finset.mem_erase.mpr ⟨hfirst ▸ hvne, hfirst ▸ hB⟩)

-/

lemma walk_heq_copy {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (p : G.Walk a b) (ha : a = c) (hb : b = d) : HEq (p.copy ha hb) p := by
  subst c d
  rfl

lemma walk_snd_copy {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (p : G.Walk a b) (ha : a = c) (hb : b = d) : (p.copy ha hb).snd = p.snd := by
  subst c d
  rfl

lemma closed_trail_snd_ne_penultimate {V : Type*} {G : SimpleGraph V} {v : V}
    (C : G.Walk v v) (hc : C.IsTrail) (hn : ¬C.Nil) : C.snd ≠ C.penultimate := by
  cases C with
  | nil => exact (hn Walk.Nil.nil).elim
  | @cons _ w _ h p =>
    have hp := (Walk.isTrail_cons h p).mp hc
    have hpn : ¬p.Nil := Walk.not_nil_of_ne h.ne.symm
    simp only [Walk.snd_cons, Walk.penultimate_cons_of_not_nil h p hpn]
    intro he
    apply hp.2
    apply p.mem_edges_toSubgraph.mp
    have hh := (p.toSubgraph_adj_penultimate hpn).symm
    rw [← he] at hh
    exact hh

/-- Replace one traversal by a representative of exactly the same subgraph. -/
lemma replace_member {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k)
    (p : G.Walk (T.start i) (T.finish i)) (hp : p.IsTrail)
    (he : p.toSubgraph = (T.walk i).toSubgraph) :
    ∃ S : NormalTrailSystem G k, S.start = T.start ∧ S.finish = T.finish ∧
      S.score = T.score ∧ (∀ j, (S.walk j).toSubgraph = (T.walk j).toSubgraph) ∧
      HEq (S.walk i) p := by
  classical
  let q := Function.update T.walk i p
  have hqi : q i = p := by simp [q]
  have hpart (j : Fin k) : (q j).toSubgraph = (T.walk j).toSubgraph := by
    by_cases hji : j = i
    · subst j; rw [hqi, he]
    · simp [q, hji]
  let R : NormalTrailSystem G k :=
    { start := T.start, finish := T.finish, walk := q,
      isTrail := by
        intro j
        by_cases hj : j=i
        · subst j; rw [hqi]; exact hp
        · simpa [q, hj] using T.isTrail j
      endpoint_bijective := T.endpoint_bijective
      disjoint := by intro j l hjl; rw [hpart j, hpart l]; exact T.disjoint hjl
      cover := by intro e; simp_rw [hpart]; exact T.cover e }
  refine ⟨R, rfl, rfl, ?_, hpart, heq_of_eq hqi⟩
  unfold NormalTrailSystem.score
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun K : G.Subgraph ↦ K.verts.ncard) (hpart j)

lemma replace_two_starts_tracked {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i j : Fin k) (hij : i ≠ j)
    (p : G.Walk (T.start j) (T.finish i)) (q : G.Walk (T.start i) (T.finish j))
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hpq : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet)
    (hu : p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) :
    ∃ S : NormalTrailSystem G k,
      (S.walk i).toSubgraph = p.toSubgraph ∧
      (S.walk j).toSubgraph = q.toSubgraph ∧
      (∀ l, l ≠ i → l ≠ j → (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      S.start = (fun l ↦ T.start (Equiv.swap i j l)) ∧ S.finish = T.finish ∧
      S.score + (T.walk i).toSubgraph.verts.ncard + (T.walk j).toSubgraph.verts.ncard =
        T.score + p.toSubgraph.verts.ncard + q.toSubgraph.verts.ncard := by
  classical
  let a : Fin k → V := fun l ↦ T.start (Equiv.swap i j l)
  have hwalk (l : Fin k) : ∃ r : G.Walk (a l) (T.finish l), r.IsTrail ∧
      r.toSubgraph = if l=i then p.toSubgraph else if l=j then q.toSubgraph else (T.walk l).toSubgraph := by
    by_cases hli : l = i
    · subst l
      rw [show a i = T.start j by simp [a]]
      simp only [↓reduceIte]
      exact ⟨p, hp, rfl⟩
    · by_cases hlj : l = j
      · subst l
        rw [show a j = T.start i by simp [a]]
        simp only [if_neg hij.symm, ↓reduceIte]
        exact ⟨q, hq, rfl⟩
      · have ha : a l = T.start l := by simp [a, Equiv.swap_apply_of_ne_of_ne hli hlj]
        rw [ha]
        simp only [if_neg hli, if_neg hlj]
        exact ⟨T.walk l, T.isTrail l, rfl⟩
  choose r hr hre using hwalk
  have hri : (r i).toSubgraph = p.toSubgraph := by simpa using hre i
  have hrj : (r j).toSubgraph = q.toSubgraph := by simpa [hij.symm] using hre j
  have hrl (l : Fin k) (hli : l ≠ i) (hlj : l ≠ j) :
      (r l).toSubgraph = (T.walk l).toSubgraph := by simpa [hli, hlj] using hre l
  have hcross (l : Fin k) (hli : l ≠ i) (hlj : l ≠ j) :
      Disjoint (p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet) (T.walk l).toSubgraph.edgeSet := by
    rw [hu]
    exact disjoint_sup_left.mpr ⟨T.disjoint hli.symm, T.disjoint hlj.symm⟩
  have hdis : Pairwise fun l m ↦ Disjoint (r l).toSubgraph.edgeSet (r m).toSubgraph.edgeSet := by
    intro l m hlm
    by_cases hli : l = i
    · subst l
      rw [hri]
      by_cases hmj : m = j
      · subst m; rw [hrj]; exact hpq
      · rw [hrl m hlm.symm hmj]
        exact (disjoint_sup_left.mp (hcross m hlm.symm hmj)).1
    · by_cases hlj : l = j
      · subst l
        rw [hrj]
        by_cases hmi : m = i
        · subst m; rw [hri]; exact hpq.symm
        · rw [hrl m hmi hlm.symm]
          exact (disjoint_sup_left.mp (hcross m hmi hlm.symm)).2
      · rw [hrl l hli hlj]
        by_cases hmi : m = i
        · subst m; rw [hri]
          exact (disjoint_sup_left.mp (hcross l hli hlj)).1.symm
        · by_cases hmj : m = j
          · subst m; rw [hrj]
            exact (disjoint_sup_left.mp (hcross l hli hlj)).2.symm
          · rw [hrl m hmi hmj]
            exact T.disjoint hlm
  have hcover (e : Sym2 V) : e ∈ G.edgeSet ↔ ∃ l, e ∈ (r l).toSubgraph.edgeSet := by
    constructor
    · intro he
      obtain ⟨l, hl⟩ := (T.cover e).mp he
      by_cases hli : l = i
      · subst l
        have hh : e ∈ p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet := hu.symm ▸ Or.inl hl
        exact hh.elim (fun h ↦ ⟨i, hri.symm ▸ h⟩) (fun h ↦ ⟨j, hrj.symm ▸ h⟩)
      · by_cases hlj : l = j
        · subst l
          have hh : e ∈ p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet := hu.symm ▸ Or.inr hl
          exact hh.elim (fun h ↦ ⟨i, hri.symm ▸ h⟩) (fun h ↦ ⟨j, hrj.symm ▸ h⟩)
        · exact ⟨l, (hrl l hli hlj).symm ▸ hl⟩
    · rintro ⟨l, hl⟩
      exact (r l).toSubgraph.edgeSet_subset hl
  let S : NormalTrailSystem G k :=
    { start := a
      finish := T.finish
      walk := r
      isTrail := hr
      endpoint_bijective := NormalTrailSystem.permute_starts_bijective T.start T.finish T.endpoint_bijective (Equiv.swap i j)
      disjoint := hdis
      cover := hcover }
  refine ⟨S, hri, hrj, hrl, rfl, rfl, ?_⟩
  have hsum : ∑ l ∈ (Finset.univ.erase i).erase j, (S.walk l).toSubgraph.verts.ncard =
      ∑ l ∈ (Finset.univ.erase i).erase j, (T.walk l).toSubgraph.verts.ncard := by
    apply Finset.sum_congr rfl
    intro l hl
    obtain ⟨hlj, hl⟩ := Finset.mem_erase.mp hl
    have hli := (Finset.mem_erase.mp hl).1
    change (r l).toSubgraph.verts.ncard = _
    rw [hrl l hli hlj]
  have hS := NormalTrailSystem.sum_extract_two (fun l ↦ (S.walk l).toSubgraph.verts.ncard) i j hij
  have hT := NormalTrailSystem.sum_extract_two (fun l ↦ (T.walk l).toSubgraph.verts.ncard) i j hij
  change S.score = (r i).toSubgraph.verts.ncard + (r j).toSubgraph.verts.ncard + _ at hS
  rw [hri, hrj, hsum] at hS
  change T.score = _ at hT
  dsimp only at hS hT
  omega

lemma of_closed_prefix {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i₀ : Fin k)
    (C : G.Walk (T.start i₀) (T.start i₀)) (q : G.Walk (T.start i₀) (T.finish i₀))
    (he : (T.walk i₀).toSubgraph = (C.append q).toSubgraph)
    (ht : (C.append q).IsTrail) (hC : ¬C.Nil) :
    ∃ B : Finset V, ∃ R : RootedTailSystem G k (T.start i₀) B, R.system = T ∧
      R.tail ⟨T.start i₀, R.root_mem⟩ = C := by
  classical
  let v := T.start i₀
  let I := NormalTrailSystem.containing T v
  let B := NormalTrailSystem.blockedVertices T v
  have hia (j : Fin k) : j ∈ I ↔ v ∈ (T.walk j).support := by simp [I, NormalTrailSystem.containing]
  have ha (j : Fin k) : T.start j ∈ B ↔ j ∈ I := by
    have ho : NormalTrailSystem.owner T (T.start j) = j :=
      (NormalTrailSystem.endpoint_iff_owner T _ _).mp (Or.inl rfl)
    rw [show B = NormalTrailSystem.blockedVertices T v from rfl,
      NormalTrailSystem.mem_blocked_iff, ho, hia]
  have hb (j : Fin k) : T.finish j ∈ B ↔ j ∈ I := by
    have ho : NormalTrailSystem.owner T (T.finish j) = j :=
      (NormalTrailSystem.endpoint_iff_owner T _ _).mp (Or.inr rfl)
    rw [show B = NormalTrailSystem.blockedVertices T v from rfl,
      NormalTrailSystem.mem_blocked_iff, ho, hia]
  have hi₀ : i₀ ∈ I := (hia i₀).mpr (T.walk i₀).start_mem_support
  let j₀ : I := ⟨i₀,hi₀⟩
  have hcuts (j : I) : ∃ L : G.Walk (T.start j.val) v,
      ∃ Q : G.Walk (T.finish j.val) v,
        (L.append Q.reverse).IsTrail ∧
        (T.walk j.val).toSubgraph = (L.append Q.reverse).toSubgraph ∧
        (j = j₀ → HEq L C) := by
    by_cases hj : j = j₀
    · subst j
      refine ⟨C, q.reverse, ?_, ?_, fun _ ↦ HEq.rfl⟩
      · simpa only [Walk.reverse_reverse] using ht
      · simpa only [Walk.reverse_reverse] using he
    · refine ⟨(T.walk j.val).takeUntil v ((hia j.val).mp j.property),
        ((T.walk j.val).dropUntil v ((hia j.val).mp j.property)).reverse, ?_, ?_,
        fun hh ↦ (hj hh).elim⟩
      · simpa using T.isTrail j.val
      · simp
  choose L Q htrail hc hLroot using hcuts
  have hLC : L j₀ = C := eq_of_heq (hLroot j₀ rfl)
  have hn : ¬(L j₀).Nil := hLC.symm ▸ hC
  have hpart (j : I) : (T.walk j.val).toSubgraph = (L j).toSubgraph ⊔ (Q j).toSubgraph := by
    rw [hc j, Walk.toSubgraph_append, Walk.toSubgraph_reverse]
  have htr (j : I) : (L j).IsTrail ∧ (Q j).IsTrail ∧
      Disjoint (L j).toSubgraph.edgeSet (Q j).toSubgraph.edgeSet := by
    have ht : ((L j).append (Q j).reverse).IsTrail := htrail j
    refine ⟨ht.of_append_left, ?_, ?_⟩
    · simpa only [Walk.reverse_isTrail_iff] using ht.of_append_right
    · simpa only [Walk.toSubgraph_reverse] using append_trail_disjoint ht
  let F (x : I × Bool) : B := ⟨if x.2 then T.start x.1.val else T.finish x.1.val, by
    cases h : x.2
    · simpa only [h, Bool.false_eq_true, ↓reduceIte] using (hb x.1.val).mpr x.1.property
    · simpa only [h, ↓reduceIte] using (ha x.1.val).mpr x.1.property⟩
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      have hh : (x.1.val,x.2) = (y.1.val,y.2) :=
        T.endpoint_bijective.1 (congrArg Subtype.val hxy)
      exact Prod.ext (Subtype.ext (congrArg (fun z : Fin k × Bool ↦ z.1) hh))
        (congrArg (fun z : Fin k × Bool ↦ z.2) hh)
    · intro z
      obtain ⟨⟨j,c⟩, he⟩ := T.endpoint_bijective.2 z.val
      have hj : j ∈ I := by
        cases c
        · have he' : T.finish j = z.val := he
          exact (hb j).mp (he'.symm ▸ z.property)
        · have he' : T.start j = z.val := he
          exact (ha j).mp (he'.symm ▸ z.property)
      exact ⟨(⟨j,hj⟩,c), Subtype.ext he⟩
  let E : I × Bool ≃ B := Equiv.ofBijective F hF
  let slot (x : I × Bool) : G.Walk (E x).val v := by
    rcases x with ⟨j,c⟩
    cases c
    · exact Q j
    · exact L j
  have hslot (x : I × Bool) : (slot x).IsTrail := by
    rcases x with ⟨j,c⟩
    cases c
    · exact (htr j).2.1
    · exact (htr j).1
  have hle (x : I × Bool) : (slot x).toSubgraph ≤ (T.walk x.1.val).toSubgraph := by
    rw [hpart]
    rcases x with ⟨j,c⟩
    cases c
    · exact le_sup_right
    · exact le_sup_left
  have hdis : Pairwise fun x y ↦ Disjoint (slot x).toSubgraph.edgeSet (slot y).toSubgraph.edgeSet := by
    intro x y hxy
    by_cases hij : x.1 = y.1
    · rcases x with ⟨j,c⟩
      rcases y with ⟨l,d⟩
      dsimp only at hij
      subst l
      cases c <;> cases d
      · exact (hxy rfl).elim
      · exact (htr j).2.2.symm
      · exact (htr j).2.2
      · exact (hxy rfl).elim
    · have hv : x.1.val ≠ y.1.val := fun h ↦ hij (Subtype.ext h)
      exact (T.disjoint hv).mono (Subgraph.edgeSet_mono (hle x)) (Subgraph.edgeSet_mono (hle y))
  let tail (z : B) : G.Walk z.val v :=
    (slot (E.symm z)).copy (congrArg Subtype.val (E.apply_symm_apply z)) rfl
  have htail (x : I × Bool) : (tail (E x)).toSubgraph = (slot x).toSubgraph := by
    dsimp only [tail]
    rw [NormalTrailSystem.walk_copy_subgraph]
    exact congrArg (fun y : I × Bool ↦ (slot y).toSubgraph) (E.symm_apply_apply x)
  have htail' (z : B) : (tail z).toSubgraph = (slot (E.symm z)).toSubgraph :=
    NormalTrailSystem.walk_copy_subgraph _ _ _
  have ht (z : B) : (tail z).IsTrail := by
    simpa only [tail, Walk.isTrail_copy] using hslot (E.symm z)
  have hd : Pairwise fun z t ↦ Disjoint (tail z).toSubgraph.edgeSet (tail t).toSubgraph.edgeSet := by
    intro z t hzt
    rw [htail' z, htail' t]
    exact hdis (fun hh ↦ hzt (E.symm.injective hh))
  have hroot : v ∈ B := NormalTrailSystem.self_mem_blocked T v
  have hrootTail : (tail ⟨v,hroot⟩).toSubgraph = (L j₀).toSubgraph := htail (j₀,true)
  have hrootne : ¬(tail ⟨v,hroot⟩).Nil := by
    intro hh
    have hedge : s(v,(L j₀).snd) ∈ (L j₀).toSubgraph.edgeSet :=
      (L j₀).toSubgraph_adj_snd hn
    rw [← hrootTail] at hedge
    rw [hh.eq_nil] at hedge
    simp at hedge
  let R : RootedTailSystem G k v B :=
    { system := T, active := I, root_mem := hroot, tail := tail, trail := ht, disjoint := hd,
      start_mem := ha, finish_mem := hb,
      decomp := by
        intro j hj
        have hL : (tail ⟨T.start j, (ha j).mpr hj⟩).toSubgraph = (L ⟨j,hj⟩).toSubgraph :=
          htail (⟨j,hj⟩,true)
        have hQ : (tail ⟨T.finish j, (hb j).mpr hj⟩).toSubgraph = (Q ⟨j,hj⟩).toSubgraph :=
          htail (⟨j,hj⟩,false)
        rw [hL, hQ]
        exact hpart ⟨j,hj⟩
      outside := fun j hj hvj ↦ hj ((hia j).mpr hvj),
      root_nonempty := hrootne }
  refine ⟨B, R, rfl, ?_⟩
  change tail ⟨v,hroot⟩ = C
  have hE : E (j₀,true) = ⟨v,hroot⟩ := rfl
  have hsym : E.symm ⟨v,hroot⟩ = (j₀,true) := by rw [← hE, E.symm_apply_apply]
  have hh : HEq (tail ⟨v,hroot⟩) (slot (j₀,true)) := by
    dsimp only [tail]
    have hcopy : HEq ((slot (E.symm ⟨v,hroot⟩)).copy
        (congrArg Subtype.val (E.apply_symm_apply ⟨v,hroot⟩)) rfl)
        (slot (E.symm ⟨v,hroot⟩)) := by
      apply walk_heq_copy
    apply hcopy.trans
    have hh : ∀ x y : I × Bool, x = y → HEq (slot x) (slot y) := by
      intro x y hxy
      subst y
      rfl
    exact hh _ _ hsym
  exact (eq_of_heq hh).trans hLC


/-- An undirected member, allowing an alternative traversal of its subgraph. -/
def IsMember {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) {a b : V} (p : G.Walk a b) : Prop :=
  ∃ i, ((T.start i = a ∧ T.finish i = b) ∨ (T.start i = b ∧ T.finish i = a)) ∧
    (T.walk i).toSubgraph = p.toSubgraph

lemma isMember_walk {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) : IsMember T (T.walk i) :=
  ⟨i, Or.inl ⟨rfl,rfl⟩, rfl⟩

lemma member_orient {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : NormalTrailSystem G k} {a b : V} {p : G.Walk a b} (hm : IsMember T p) :
    ∃ S : NormalTrailSystem G k, S.score = T.score ∧
      ∃ i, S.start i = a ∧ S.finish i = b ∧ (S.walk i).toSubgraph = p.toSubgraph := by
  classical
  obtain ⟨i, hi, he⟩ := hm
  rcases hi with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact ⟨T,rfl,i,ha,hb,he⟩
  · obtain ⟨S, hs, hS⟩ := T.orient (fun j ↦ decide (j=i))
    refine ⟨S,hs,i,?_,?_,(hS i).2.2.trans he⟩
    · simpa using (hS i).1.trans (by simp [hb])
    · simpa using (hS i).2.1.trans (by simp [ha])

lemma member_no_repeated_start {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : NormalTrailSystem G k} (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    {a w b : V} (h : G.Adj a w) (p : G.Walk w b)
    (hp : (Walk.cons h p).IsTrail) (hm : IsMember T (Walk.cons h p)) : a ∉ p.support := by
  classical
  intro hv
  obtain ⟨S, hs, i, ha, hb, he⟩ := member_orient hm
  subst a b
  let C := Walk.cons h (p.takeUntil (S.start i) hv)
  let q := p.dropUntil (S.start i) hv
  have hform : C.append q = Walk.cons h p := by simp [C,q]
  obtain ⟨B,R,hR,_⟩ := of_closed_prefix S i C q (by rw [hform]; exact he)
    (by rw [hform]; exact hp) (by simp [C])
  obtain ⟨U, hu⟩ := R.improve
  have hh : S.score < U.score := hR ▸ hu
  exact (not_lt_of_ge (hmax U)) (hs ▸ hh)

lemma cons_verts {V : Type*} {G : SimpleGraph V} {a b c : V}
    (h : G.Adj a b) (p : G.Walk b c) :
    (Walk.cons h p).toSubgraph.verts = insert a p.toSubgraph.verts := by
  ext x
  simp only [Walk.mem_verts_toSubgraph, Walk.support_cons, List.mem_cons, Set.mem_insert_iff]

lemma cons_ncard_of_mem {V : Type*} {G : SimpleGraph V} {a b c : V}
    (h : G.Adj a b) (p : G.Walk b c) (hv : a ∈ p.support) :
    (Walk.cons h p).toSubgraph.verts.ncard = p.toSubgraph.verts.ncard := by
  rw [cons_verts, Set.insert_eq_of_mem (p.mem_verts_toSubgraph.mpr hv)]

lemma cons_ncard_of_notMem {V : Type*} [Fintype V] {G : SimpleGraph V} {a b c : V}
    (h : G.Adj a b) (p : G.Walk b c) (hv : a ∉ p.support) :
    (Walk.cons h p).toSubgraph.verts.ncard = p.toSubgraph.verts.ncard + 1 := by
  rw [cons_verts, Set.ncard_insert_of_notMem (by simpa using hv)]

lemma trail_slide_data {V : Type*} {G : SimpleGraph V}
    {v w b c : V} (h : G.Adj v w) (p : G.Walk w b) (q : G.Walk w c)
    (hp : (Walk.cons h p).IsTrail) (hq : q.IsTrail)
    (hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet q.toSubgraph.edgeSet) :
    p.IsTrail ∧ (Walk.cons h q).IsTrail ∧
      Disjoint p.toSubgraph.edgeSet (Walk.cons h q).toSubgraph.edgeSet ∧
      ((Walk.cons h p).toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet =
        p.toSubgraph.edgeSet ∪ (Walk.cons h q).toSubgraph.edgeSet) := by
  have hp' := (Walk.isTrail_cons h p).mp hp
  have hnotq : s(v,w) ∉ q.edges := by
    intro he
    exact Set.disjoint_left.mp hd
      ((Walk.cons h p).mem_edges_toSubgraph.mpr (by simp)) (q.mem_edges_toSubgraph.mpr he)
  refine ⟨hp'.1, (Walk.isTrail_cons h q).mpr ⟨hq,hnotq⟩, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e he heq
    have hep := p.mem_edges_toSubgraph.mp he
    have heq' := (Walk.cons h q).mem_edges_toSubgraph.mp heq
    simp only [Walk.edges_cons, List.mem_cons] at heq'
    rcases heq' with rfl | heq'
    · exact hp'.2 hep
    · exact Set.disjoint_left.mp hd
        ((Walk.cons h p).mem_edges_toSubgraph.mpr (by simp [hep]))
        (q.mem_edges_toSubgraph.mpr heq')
  · ext e
    simp only [Set.mem_union, Walk.mem_edges_toSubgraph, Walk.edges_cons, List.mem_cons]
    exact or_assoc.trans or_left_comm

lemma slide_oriented {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph) :
    ∃ S : NormalTrailSystem G k,
      (S.walk i).toSubgraph = p.toSubgraph ∧
      (S.walk j).toSubgraph = (Walk.cons h (T.walk j)).toSubgraph ∧
      (∀ l, l ≠ i → l ≠ j → (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      S.start = (fun l ↦ T.start (Equiv.swap i j l)) ∧ S.finish = T.finish ∧
      S.score + (Walk.cons h p).toSubgraph.verts.ncard + (T.walk j).toSubgraph.verts.ncard =
        T.score + p.toSubgraph.verts.ncard + (Walk.cons h (T.walk j)).toSubgraph.verts.ncard := by
  have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet (T.walk j).toSubgraph.edgeSet :=
    he ▸ T.disjoint hij
  obtain ⟨hp',hq',hd',hu⟩ := trail_slide_data h p (T.walk j) hp (T.isTrail j) hd
  obtain ⟨S,hSi,hSj,hSl,hSa,hSb,hs⟩ := replace_two_starts_tracked T i j hij p
    (Walk.cons h (T.walk j)) hp' hq' hd' (by rw [he]; exact hu.symm)
  refine ⟨S,hSi,hSj,hSl,hSa,hSb,?_⟩
  simpa only [he] using hs

lemma escape_slide_protected {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i l : Fin k) (hil : i ≠ l) {y : V}
    (h : G.Adj (T.start i) y) (p : G.Walk y (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support)
    (havoid : T.start i ∉ (T.walk (NormalTrailSystem.owner T y)).support)
    (hyw : y ≠ T.start l)
    (r : G.Walk (T.start l) (T.finish l)) (hr : r.IsTrail)
    (hre : (T.walk l).toSubgraph = r.toSubgraph) :
    ∃ S : NormalTrailSystem G k, S.score = T.score + 1 ∧
      ∃ t, ∃ q : G.Walk (T.finish l) t, (r.append q).IsTrail ∧ IsMember S (r.append q) := by
  classical
  let j := NormalTrailSystem.owner T y
  change T.start i ∉ (T.walk j).support at havoid
  have hown : y = T.start j ∨ y = T.finish j := NormalTrailSystem.owner_spec T y
  have hij : i ≠ j := by
    intro hh
    apply havoid
    rw [← hh]
    exact (T.walk i).start_mem_support
  clear_value j
  rcases hown with hw | hw
  · subst y
    have hlj : l ≠ j := fun hh ↦ hyw (congrArg T.start hh.symm)
    obtain ⟨S,hSi,hSj,hSl,hSa,hSb,hs⟩ := slide_oriented T i j hij h p hp he
    rw [cons_ncard_of_mem h p hv, cons_ncard_of_notMem h (T.walk j) havoid] at hs
    refine ⟨S,by omega,T.finish l,Walk.nil,?_,?_⟩
    · simpa using hr
    · refine ⟨l,Or.inl ⟨?_,?_⟩,?_⟩
      · simp only [hSa, Equiv.swap_apply_of_ne_of_ne hil.symm hlj]
      · rw [hSb]
      · simpa using (hSl l hil.symm hlj).trans hre
  · have hw' : y = T.finish j := hw
    obtain ⟨U,hscore,hU⟩ := T.orient (fun m ↦ decide (m=j))
    have hi : U.start i = T.start i := by simpa [hij] using (hU i).1
    have hi' : U.finish i = T.finish i := by simpa [hij] using (hU i).2.1
    have hj : U.start j = y := by simpa [hw'] using (hU j).1
    have hj' : U.finish j = T.start j := by simpa using (hU j).2.1
    let q₀ := (T.walk j).reverse.copy hw'.symm rfl
    have hq₀ : q₀.IsTrail := by simpa [q₀] using (T.isTrail j).reverse
    have hq₀e : q₀.toSubgraph = (T.walk j).toSubgraph := by
      rw [NormalTrailSystem.walk_copy_subgraph, Walk.toSubgraph_reverse]
    have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet q₀.toSubgraph.edgeSet := by
      rw [hq₀e, ← he]
      exact T.disjoint hij
    obtain ⟨hp',hQ,hd',hu⟩ := trail_slide_data h p q₀ hp hq₀ hd
    let Q := Walk.cons h q₀
    let P' := p.copy hj.symm hi'.symm
    let Q' := Q.copy hi.symm hj'.symm
    have hPe : P'.toSubgraph = p.toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
    have hQe : Q'.toSubgraph = Q.toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
    obtain ⟨S,hSi,hSj,hSl,hSa,hSb,hs⟩ := replace_two_starts_tracked U i j hij P' Q'
      (by simpa [P'] using hp') (by simpa [Q',Q] using hQ)
      (by rw [hPe,hQe]; exact hd')
      (by rw [hPe,hQe,(hU i).2.2,(hU j).2.2,he,← hq₀e]; exact hu.symm)
    rw [(hU i).2.2,(hU j).2.2,hscore,hPe,hQe,he,← hq₀e] at hs
    have hvq : T.start i ∉ q₀.support := by simpa [q₀] using havoid
    have hqcard := cons_ncard_of_notMem h q₀ hvq
    have hpcard := cons_ncard_of_mem h p hv
    have hss : S.score = T.score + 1 := by change _ = _ at hqcard; dsimp only [Q] at hs; omega
    refine ⟨S,hss,?_⟩
    by_cases hlj : l=j
    · subst l
      have hb : G.Adj (T.finish j) (T.start i) := hw' ▸ h.symm
      let e : G.Walk (T.finish j) (T.start i) := Walk.cons hb Walk.nil
      have hdre : Disjoint r.toSubgraph.edgeSet e.toSubgraph.edgeSet := by
        rw [← hre]
        apply Set.disjoint_left.mpr
        intro d hdj hde
        have hed : d = s(T.finish j,T.start i) := by simpa [e] using hde
        subst d
        have hdi : s(T.finish j,T.start i) ∈ (T.walk i).toSubgraph.edgeSet := by
          rw [he, ← hw']
          simpa only [Walk.snd_cons] using ((Walk.cons h p).toSubgraph_adj_snd (by simp)).symm
        exact Set.disjoint_left.mp (T.disjoint hij) hdi hdj
      refine ⟨T.start i,e,trail_append_of_disjoint hr (by simp [e]) hdre,j,
        Or.inr ⟨?_,?_⟩,?_⟩
      · simp only [hSa, Equiv.swap_apply_right, hi]
      · rw [hSb,hj']
      · rw [hSj,hQe]
        change (Walk.cons h q₀).toSubgraph = (r.append e).toSubgraph
        rw [Walk.toSubgraph, hq₀e, hre, Walk.toSubgraph_append]
        have hee : e.toSubgraph = G.subgraphOfAdj h := by
          simp only [e, Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
          subst y
          exact subgraphOfAdj_symm _
        rw [hee,sup_comm]
    · refine ⟨T.finish l,Walk.nil,by simpa using hr,l,Or.inl ⟨?_,?_⟩,?_⟩
      · simp only [hSa, Equiv.swap_apply_of_ne_of_ne hil.symm hlj]
        simpa [hlj] using (hU l).1
      · rw [hSb]
        simpa [hlj] using (hU l).2.1
      · simpa using (hSl l hil.symm hlj).trans ((hU l).2.2.trans hre)
lemma orient_root_start_tracked {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ S.tail = R.tail ∧ AgreesOutside S R ∧
      ∃ i, S.system.start i = v := by
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
  refine ⟨S, hs, rfl, ⟨rfl,?_⟩, ?_⟩
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


lemma member_copy {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : NormalTrailSystem G k} {a b a' b' : V} {p : G.Walk a b}
    (hm : IsMember T p) (ha : a=a') (hb : b=b') : IsMember T (p.copy ha hb) := by
  subst a' b'
  exact hm

lemma extension_of_copy {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : NormalTrailSystem G k} {a b a' b' t : V} (p : G.Walk a b)
    (ha : a=a') (hb : b=b') (q : G.Walk b' t)
    (ht : ((p.copy ha hb).append q).IsTrail)
    (hm : IsMember T ((p.copy ha hb).append q)) :
    ∃ q' : G.Walk b t, (p.append q').IsTrail ∧ IsMember T (p.append q') := by
  subst a' b'
  exact ⟨q,ht,hm⟩

/-- Finish an exposed rooted exchange while preserving a protected outside
member as a prefix. Only an edge at its far endpoint may be appended. -/
lemma finish_exposed_protected {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (l : Fin k) (hl : l ∉ R.active)
    (r : G.Walk (R.system.start l) (R.system.finish l)) (hr : r.IsTrail)
    (hre : (R.system.walk l).toSubgraph = r.toSubgraph)
    (hesc : (R.tail ⟨v,R.root_mem⟩).snd ∉ B)
    (hprotect : (R.tail ⟨v,R.root_mem⟩).snd ≠ R.system.start l) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∃ t, ∃ q : G.Walk (R.system.finish l) t,
        (r.append q).IsTrail ∧ IsMember T (r.append q) := by
  classical
  obtain ⟨S,hs,ht,htrack,i,hi⟩ := orient_root_start_tracked R
  have hia : i ∈ S.active := (S.start_mem i).mp (hi.symm ▸ S.root_mem)
  have hli : l ∉ S.active := htrack.1.symm ▸ hl
  have hil : i ≠ l := fun hh ↦ hli (hh ▸ hia)
  obtain ⟨hla,hlb,hle⟩ := htrack.2 l hl
  let rS := r.copy hla.symm hlb.symm
  have hrS : rS.IsTrail := by simpa [rS] using hr
  have hrSe : (S.system.walk l).toSubgraph = rS.toSubgraph := by
    rw [NormalTrailSystem.walk_copy_subgraph]
    exact hle.trans hre
  let a : B := ⟨S.system.start i,(S.start_mem i).mpr hia⟩
  let b : B := ⟨S.system.finish i,(S.finish_mem i).mpr hia⟩
  have ha : a = ⟨v,S.root_mem⟩ := Subtype.ext hi
  have hab : a ≠ b := fun h ↦ S.system.endpoints_ne i (congrArg Subtype.val h)
  have hd : Disjoint (S.tail a).toSubgraph.edgeSet (S.tail b).reverse.toSubgraph.edgeSet := by
    simpa only [Walk.toSubgraph_reverse] using S.disjoint hab
  have hp := trail_append_of_disjoint (S.trail a) (S.trail b).reverse hd
  have he : (S.system.walk i).toSubgraph = ((S.tail a).append (S.tail b).reverse).toSubgraph := by
    rw [Walk.toSubgraph_append, Walk.toSubgraph_reverse]
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
  have hesc' : C.snd ∉ B := by
    change (S.tail a).snd ∉ B
    rw [ha,ht]
    exact hesc
  have hprotect' : C.snd ≠ S.system.start l := by
    rw [hla]
    change (S.tail a).snd ≠ R.system.start l
    rw [ha,ht]
    exact hprotect
  have hout : S.system.start i ∉ (S.system.walk (NormalTrailSystem.owner S.system C.snd)).support := by
    rw [hi]
    exact S.outside _ (fun hh ↦ hesc' ((S.mem_ends_iff_owner_active C.snd).mpr hh))
  obtain ⟨T,hT,t,q,hq,hm⟩ := escape_slide_protected S.system i l hil h p
    (by rw [hform]; exact hp) (by rw [hform]; exact he) hv hout hprotect' rS hrS hrSe
  obtain ⟨q',hq',hm'⟩ := extension_of_copy r hla.symm hlb.symm q hq hm
  exact ⟨T,by omega,t,q',hq',hm'⟩

lemma repair_protected {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (l : Fin k) (hl : l ∉ R.active)
    (r : G.Walk (R.system.start l) (R.system.finish l)) (hr : r.IsTrail)
    (hre : (R.system.walk l).toSubgraph = r.toSubgraph)
    (hfirst : (R.tail ⟨v,R.root_mem⟩).snd ≠ R.system.start l)
    (hedge : s(v,R.system.start l) ∈ (R.tail ⟨v,R.root_mem⟩).toSubgraph.edgeSet) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∃ t, ∃ q : G.Walk (R.system.finish l) t,
        (r.append q).IsTrail ∧ IsMember T (r.append q) := by
  classical
  obtain ⟨S,hs,hesc,havoid,htrack⟩ := expose_escape_tracked R {R.system.start l}
    (by simpa using hfirst) (by intro z hz; simpa only [Set.mem_singleton_iff.mp hz] using hedge)
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

lemma isMember_reverse {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : NormalTrailSystem G k} {a b : V} {p : G.Walk a b}
    (hm : IsMember T p) : IsMember T p.reverse := by
  obtain ⟨i,hi,he⟩ := hm
  refine ⟨i,?_,by simpa using he⟩
  exact hi.elim (fun h ↦ Or.inr h) (fun h ↦ Or.inl h)

lemma member_no_closed_prefix {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : NormalTrailSystem G k} (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    {a b : V} (C : G.Walk a a) (q : G.Walk a b)
    (hp : (C.append q).IsTrail) (hm : IsMember T (C.append q)) : C.Nil := by
  by_contra hn
  obtain ⟨S,hs,i,ha,hb,he⟩ := member_orient hm
  subst a b
  obtain ⟨B,R,hR,_⟩ := of_closed_prefix S i C q he hp hn
  obtain ⟨U,hu⟩ := R.improve
  have hh : S.score < U.score := hR ▸ hu
  exact (not_lt_of_ge (hmax U)) (hs ▸ hh)

lemma root_mem_of_active {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (i : Fin k) (hi : i ∈ R.active) :
    v ∈ (R.system.walk i).support := by
  rw [← Walk.mem_verts_toSubgraph, R.decomp i hi, Subgraph.verts_sup]
  exact Or.inl ((R.tail _).mem_verts_toSubgraph.mpr (R.tail _).end_mem_support)

/-- Advance the start of a maximal-score member by one edge, permitting a new
extension at its far end. A blocked slide loses one incidence, which a protected
rooted exchange restores without undoing the advance. -/
lemma shorten_oriented {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph) :
    ∃ U : NormalTrailSystem G k, U.score = T.score ∧
      ∃ t, ∃ q : G.Walk (T.finish i) t, (p.append q).IsTrail ∧ IsMember U (p.append q) := by
  classical
  have hm : IsMember T (Walk.cons h p) := ⟨i,Or.inl ⟨rfl,rfl⟩,he⟩
  have hnot := member_no_repeated_start hmax h p hp hm
  obtain ⟨S,hSi,hSj,hSl,hSa,hSb,hs⟩ := slide_oriented T i j hij h p hp he
  have hai : S.start i = T.start j := by simp [hSa]
  have haj : S.start j = T.start i := by simp [hSa]
  have hbi : S.finish i = T.finish i := congrFun hSb i
  have hbj : S.finish j = T.finish j := congrFun hSb j
  have hpcard := cons_ncard_of_notMem h p hnot
  have hp' := (Walk.isTrail_cons h p).mp hp |>.1
  by_cases hv : T.start i ∈ (T.walk j).support
  · have hqcard := cons_ncard_of_mem h (T.walk j) hv
    have hscore : S.score + 1 = T.score := by omega
    let C₀ := Walk.cons h ((T.walk j).takeUntil (T.start i) hv)
    let q₀ := (T.walk j).dropUntil (T.start i) hv
    have hform : C₀.append q₀ = Walk.cons h (T.walk j) := by simp [C₀,q₀]
    have hslide : (Walk.cons h (T.walk j)).IsTrail :=
      (trail_slide_data h p (T.walk j) hp (T.isTrail j) (he ▸ T.disjoint hij)).2.1
    have hCq : (C₀.append q₀).IsTrail := hform.symm ▸ hslide
    have hC : C₀.IsTrail := hCq.of_append_left
    have hCn : ¬C₀.Nil := by simp [C₀]
    have hCdis : Disjoint C₀.reverse.toSubgraph.edgeSet q₀.toSubgraph.edgeSet := by
      rw [Walk.toSubgraph_reverse]
      exact append_trail_disjoint hCq
    have hrev : (C₀.reverse.append q₀).IsTrail :=
      trail_append_of_disjoint hC.reverse hCq.of_append_right hCdis
    let C := C₀.reverse.copy haj.symm haj.symm
    let q := q₀.copy haj.symm hbj.symm
    have hCeq : C.toSubgraph = C₀.toSubgraph := by
      rw [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]
    have hqeq : q.toSubgraph = q₀.toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
    have hrep : (S.walk j).toSubgraph = (C.append q).toSubgraph := by
      rw [hSj,←hform,Walk.toSubgraph_append,Walk.toSubgraph_append,hCeq,hqeq]
    have hrepTrail : (C.append q).IsTrail := by
      simpa only [C,q,Walk.append_copy_copy,Walk.isTrail_copy] using hrev
    obtain ⟨B,R,hR,hroot⟩ := of_closed_prefix S j C q hrep hrepTrail
      (by simpa only [C,Walk.nil_copy,Walk.nil_reverse] using hCn)
    have hlout : i ∉ R.active := by
      intro hi
      have hh := root_mem_of_active R i hi
      rw [hR,← Walk.mem_verts_toSubgraph,hSi,Walk.mem_verts_toSubgraph,haj] at hh
      exact hnot hh
    have hRa : R.system.start i = T.start j := by rw [hR,hai]
    have hRb : R.system.finish i = T.finish i := by rw [hR,hbi]
    let r := p.copy hRa.symm hRb.symm
    have hr : r.IsTrail := by simpa [r] using hp'
    have hre : (R.system.walk i).toSubgraph = r.toSubgraph := by
      rw [NormalTrailSystem.walk_copy_subgraph,hR,hSi]
    have hfirst : (R.tail ⟨S.start j,R.root_mem⟩).snd ≠ R.system.start i := by
      rw [hroot,walk_snd_copy,Walk.snd_reverse,hRa]
      simpa only [C₀,Walk.snd_cons] using (closed_trail_snd_ne_penultimate C₀ hC hCn).symm
    have hedge : s(S.start j,R.system.start i) ∈ (R.tail ⟨S.start j,R.root_mem⟩).toSubgraph.edgeSet := by
      rw [hroot,hCeq,hRa,haj]
      simpa only [C₀,Walk.snd_cons] using C₀.toSubgraph_adj_snd hCn
    obtain ⟨U,hU,t,e,ht,hm⟩ := repair_protected R i hlout r hr hre hfirst hedge
    obtain ⟨e',ht',hm'⟩ := extension_of_copy p hRa.symm hRb.symm e ht hm
    refine ⟨U,?_,t,e',ht',hm'⟩
    rw [hR] at hU
    omega
  · have hqcard := cons_ncard_of_notMem h (T.walk j) hv
    refine ⟨S,by omega,T.finish i,Walk.nil,by simpa using hp',?_⟩
    refine ⟨i,Or.inl ⟨hai,hbi⟩,?_⟩
    simpa using hSi

lemma cons_copy_vertices {V : Type*} {G : SimpleGraph V}
    {a w b a' w' b' : V} (h : G.Adj a w) (p : G.Walk w b)
    (ha : a=a') (hw : w=w') (hb : b=b') (h' : G.Adj a' w') :
    Walk.cons h' (p.copy hw hb) = (Walk.cons h p).copy ha hb := by
  subst a' w' b'
  rfl

lemma orient_receiver {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (j : Fin k) (y : V)
    (hy : y = T.start j ∨ y = T.finish j) :
    ∃ S : NormalTrailSystem G k, S.score = T.score ∧ S.start j = y ∧
      (∀ i, i ≠ j → S.start i = T.start i ∧ S.finish i = T.finish i) ∧
      ∀ i, (S.walk i).toSubgraph = (T.walk i).toSubgraph := by
  classical
  rcases hy with hy | hy
  · exact ⟨T,rfl,hy.symm,(fun _ _ ↦ ⟨rfl,rfl⟩),fun _ ↦ rfl⟩
  · obtain ⟨S,hs,hS⟩ := T.orient (fun i ↦ decide (i=j))
    refine ⟨S,hs,?_,?_,fun i ↦ (hS i).2.2⟩
    · simpa [hy] using (hS j).1
    · intro i hi
      exact ⟨by simpa [hi] using (hS i).1,by simpa [hi] using (hS i).2.1⟩

lemma shorten_member {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    {a y b : V} (h : G.Adj a y) (p : G.Walk y b) (hpn : ¬p.Nil)
    (hp : (Walk.cons h p).IsTrail) (hm : IsMember T (Walk.cons h p)) :
    ∃ U : NormalTrailSystem G k, U.score = T.score ∧
      ∃ t, ∃ q : G.Walk b t, (p.append q).IsTrail ∧ IsMember U (p.append q) := by
  classical
  have hyb : y ≠ b := by
    intro hh
    subst y
    have hrev := isMember_reverse hm
    rw [Walk.reverse_cons] at hrev
    have hprev : (p.reverse.append (Walk.cons h.symm Walk.nil)).IsTrail := by
      simpa only [Walk.reverse_cons] using hp.reverse
    have hn := member_no_closed_prefix hmax p.reverse (Walk.cons h.symm Walk.nil) hprev hrev
    exact hpn (by simpa using hn)
  obtain ⟨S,hs,i,ha,hb,he⟩ := member_orient hm
  subst a b
  let j := NormalTrailSystem.owner S y
  have hjown : y = S.start j ∨ y = S.finish j := NormalTrailSystem.owner_spec S y
  have hij : i ≠ j := by
    intro hh
    rw [←hh] at hjown
    exact hjown.elim h.ne.symm hyb
  obtain ⟨U,hUs,hUj,hUi,hUe⟩ := orient_receiver S j y hjown
  obtain ⟨hi,hi'⟩ := hUi i hij
  have h' : G.Adj (U.start i) (U.start j) := by rw [hi,hUj]; exact h
  let pU := p.copy hUj.symm hi'.symm
  have hform : Walk.cons h' pU = (Walk.cons h p).copy hi.symm hi'.symm :=
    cons_copy_vertices h p hi.symm hUj.symm hi'.symm h'
  have hpU : (Walk.cons h' pU).IsTrail := by rw [hform]; simpa using hp
  have heU : (U.walk i).toSubgraph = (Walk.cons h' pU).toSubgraph := by
    rw [hform,NormalTrailSystem.walk_copy_subgraph,hUe,he]
  have hUmax : ∀ R : NormalTrailSystem G k, R.score ≤ U.score := by
    intro R
    rw [hUs,hs]
    exact hmax R
  obtain ⟨R,hR,t,q,hq,hmq⟩ := shorten_oriented U hUmax i j hij h' pU hpU heU
  obtain ⟨q',hq',hmq'⟩ := extension_of_copy p hUj.symm hi'.symm q hq hmq
  exact ⟨R,hR.trans (hUs.trans hs),t,q',hq',hmq'⟩

/-- Descent on the prefix before a nonempty closed segment. The ambient
maximal-score normal system may change at each descent step. -/
lemma no_closed_segment {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {a v : V} (A : G.Walk a v) :
    ∀ (T : NormalTrailSystem G k), (∀ S : NormalTrailSystem G k, S.score ≤ T.score) →
      ∀ {b : V} (C : G.Walk v v) (B : G.Walk v b), ¬C.Nil →
        (A.append (C.append B)).IsTrail → IsMember T (A.append (C.append B)) → False := by
  induction A with
  | nil =>
    intro T hmax b C B hC hp hm
    exact hC (member_no_closed_prefix hmax C B hp hm)
  | @cons a w v h A ih =>
    intro T hmax b C B hC hp hm
    let p := A.append (C.append B)
    have hpn : ¬p.Nil := by
      intro hn
      have hl : p.length = 0 := Walk.nil_iff_length_eq.mp hn
      have hc : C.length ≠ 0 := fun hh ↦ hC (by rw [Walk.length_eq_zero_iff.mp hh]; exact Walk.Nil.nil)
      simp only [p,Walk.length_append] at hl
      omega
    obtain ⟨S,hs,t,q,hq,hmq⟩ := shorten_member T hmax h p hpn hp hm
    have hSmax : ∀ U : NormalTrailSystem G k, U.score ≤ S.score := by
      intro U; rw [hs]; exact hmax U
    apply ih S hSmax C (B.append q) hC
    · simpa only [p,Walk.append_assoc] using hq
    · simpa only [p,Walk.append_assoc] using hmq

lemma walk_not_path_has_closed_segment {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ¬p.IsPath) :
    ∃ v, ∃ A : G.Walk a v, ∃ C : G.Walk v v, ∃ B : G.Walk v b,
      ¬C.Nil ∧ p = A.append (C.append B) := by
  classical
  induction p with
  | nil => exact (hp Walk.IsPath.nil).elim
  | @cons a w b h p ih =>
    by_cases ha : a ∈ p.support
    · refine ⟨a,Walk.nil,Walk.cons h (p.takeUntil a ha),p.dropUntil a ha,by simp,?_⟩
      simp
    · have hnp : ¬p.IsPath := fun hh ↦ hp ((Walk.cons_isPath_iff h p).mpr ⟨hh,ha⟩)
      obtain ⟨v,A,C,B,hC,he⟩ := ih hnp
      exact ⟨v,Walk.cons h A,C,B,hC,by simp only [Walk.cons_append,←he]⟩

/-- Every member of a globally maximum-incidence normal trail system is a
simple path. The proof allows the endpoint pairing to change. -/
lemma max_score_isPath {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    (i : Fin k) : (T.walk i).IsPath := by
  by_contra hn
  obtain ⟨v,A,C,B,hC,he⟩ := walk_not_path_has_closed_segment (T.walk i) hn
  exact no_closed_segment A T hmax C B hC (he ▸ T.isTrail i)
    (he ▸ isMember_walk T i)

/-- The all-odd simple-path decomposition theorem, obtained by maximizing the
incidence score over normal trail systems and allowing global rearrangements. -/
lemma all_odd_path_partition {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ho : ∀ v, Odd (G.degree v)) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card = Fintype.card V := by
  classical
  obtain ⟨k,hk,⟨T⟩⟩ := all_odd_normal_trail_system G ho
  obtain ⟨S,hS⟩ := T.exists_max_score
  obtain ⟨D,hD,hcard⟩ := S.path_decomposition (max_score_isPath S hS)
  exact ⟨D,hD,by omega⟩

end Erdos583InternalDevelopment
