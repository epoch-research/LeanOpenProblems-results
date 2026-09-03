import Submission.Work

/-! Rooted endpoint-to-root cuts for the normal-trail exchange argument.
This development does not yet settle the general path-decomposition conjecture. -/

open SimpleGraph Erdos583Work
namespace Erdos583RootedDevelopment

set_option maxHeartbeats 1200000

/-- The members visiting v are represented by edge-disjoint endpoint-to-v tails.
The tail labelled v is a nonempty closed prefix. The ordered tails, rather than
arbitrary Euler traversals of their subgraphs, are retained as data. -/
structure RootedTailSystem {V : Type*} (G : SimpleGraph V) (k : ℕ) (v : V) (B : Finset V) where
  system : NormalTrailSystem G k
  active : Finset (Fin k)
  root_mem : v ∈ B
  tail : ∀ w : B, G.Walk w.val v
  trail : ∀ w, (tail w).IsTrail
  disjoint : Pairwise fun w z ↦ Disjoint (tail w).toSubgraph.edgeSet (tail z).toSubgraph.edgeSet
  start_mem : ∀ i, system.start i ∈ B ↔ i ∈ active
  finish_mem : ∀ i, system.finish i ∈ B ↔ i ∈ active
  decomp : ∀ i (hi : i ∈ active), (system.walk i).toSubgraph =
    (tail ⟨system.start i, (start_mem i).mpr hi⟩).toSubgraph ⊔
    (tail ⟨system.finish i, (finish_mem i).mpr hi⟩).toSubgraph
  outside : ∀ i, i ∉ active → v ∉ (system.walk i).support
  root_nonempty : ¬(tail ⟨v, root_mem⟩).Nil

namespace RootedTailSystem

lemma tail_in_member {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (w : B) :
    ∃ i, ∃ _hi : i ∈ R.active, (R.tail w).toSubgraph ≤ (R.system.walk i).toSubgraph := by
  obtain ⟨⟨i, b⟩, he⟩ := R.system.endpoint_bijective.2 w.val
  cases b
  · have he' : R.system.finish i = w.val := he
    have hi : i ∈ R.active := (R.finish_mem i).mp (he'.symm ▸ w.property)
    refine ⟨i, hi, ?_⟩
    rw [R.decomp i hi]
    have hw : (⟨R.system.finish i, (R.finish_mem i).mpr hi⟩ : B) = w := Subtype.ext he'
    rw [hw]
    exact le_sup_right
  · have he' : R.system.start i = w.val := he
    have hi : i ∈ R.active := (R.start_mem i).mp (he'.symm ▸ w.property)
    refine ⟨i, hi, ?_⟩
    rw [R.decomp i hi]
    have hw : (⟨R.system.start i, (R.start_mem i).mpr hi⟩ : B) = w := Subtype.ext he'
    rw [hw]
    exact le_sup_left

lemma tail_disjoint_outside {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (w : B) (i : Fin k) (hi : i ∉ R.active) :
    Disjoint (R.tail w).toSubgraph.edgeSet (R.system.walk i).toSubgraph.edgeSet := by
  obtain ⟨j, hj, hle⟩ := R.tail_in_member w
  have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
  exact (R.system.disjoint hji).mono_left (Subgraph.edgeSet_mono hle)

lemma mem_ends_iff_owner_active {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (w : V) :
    w ∈ B ↔ NormalTrailSystem.owner R.system w ∈ R.active := by
  rcases NormalTrailSystem.owner_spec R.system w with hw | hw
  · conv_lhs => rw [hw]
    exact R.start_mem _
  · conv_lhs => rw [hw]
    exact R.finish_mem _

lemma endpoint_index_eq {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) {w : V} {i j : Fin k}
    (hi : w = T.start i ∨ w = T.finish i) (hj : w = T.start j ∨ w = T.finish j) : i = j :=
  ((NormalTrailSystem.endpoint_iff_owner T w i).mp hi).symm.trans
    ((NormalTrailSystem.endpoint_iff_owner T w j).mp hj)

/-- Rebuild the active members after relabelling their endpoints and replacing
the tail partition. Per-index vertex-set preservation gives exact score preservation. -/
lemma rebuild {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (e : V ≃ V)
    (heB : ∀ x, e x ∈ B ↔ x ∈ B) (heout : ∀ x, x ∉ B → e x = x)
    (q : ∀ w : B, G.Walk w.val v) (hq : ∀ w, (q w).IsTrail)
    (hqq : Pairwise fun w z ↦ Disjoint (q w).toSubgraph.edgeSet (q z).toSubgraph.edgeSet)
    (hU : ∀ d, (∃ w, d ∈ (q w).toSubgraph.edgeSet) ↔ ∃ w, d ∈ (R.tail w).toSubgraph.edgeSet)
    (hverts : ∀ w : B, (q ⟨e w.val, (heB w.val).mpr w.property⟩).toSubgraph.verts =
      (R.tail w).toSubgraph.verts)
    (hne : ¬(q ⟨v, R.root_mem⟩).Nil) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ S.tail = q := by
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
  refine ⟨S, ?_, rfl⟩
  unfold NormalTrailSystem.score
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg Set.ncard (hV i)


lemma cons_into_root_verts {V : Type*} {G : SimpleGraph V} {v w : V}
    (h : G.Adj v w) (p : G.Walk w v) :
    (Walk.cons h p).toSubgraph.verts = p.toSubgraph.verts := by
  ext x
  simp only [Walk.mem_verts_toSubgraph, Walk.support_cons, List.mem_cons]
  exact or_iff_right_of_imp (fun hx ↦ hx ▸ p.end_mem_support)

/-- A uniform pivot: transpose the root and the first neighbor among the
endpoint labels, and exchange their tails after moving the first edge. It also
handles the case in which the two labels belong to the same original member. -/
lemma pivot {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (w : B) (h : G.Adj v w.val)
    (p : G.Walk w.val v) (hroot : R.tail ⟨v, R.root_mem⟩ = Walk.cons h p) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧
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
  obtain ⟨S, hscore, htail⟩ := R.rebuild e heB heout q hq hqq hU hV hne
  refine ⟨S, hscore, ?_, ?_⟩
  · rw [htail, hqr, Walk.snd_reverse, Walk.penultimate_cons_of_not_nil]
    exact Walk.not_nil_of_ne h.ne.symm
  · intro z hzv hzw
    rw [htail, hqz z (fun hh ↦ hzv (congrArg Subtype.val hh)) hzw]


/-- Iteration from a point outside the image of an injective partial successor
has no repetitions before its first exit. -/
lemma iterate_injective_before_exit {α : Type*} [DecidableEq α]
    (A : Finset α) (f : α → α) (hf : Set.InjOn f (A : Set α))
    (x : α) (hx : x ∉ A.image f) (N : ℕ) (hN : ∀ n < N, f^[n] x ∈ A) :
    ∀ m n, m ≤ N → n ≤ N → f^[m] x = f^[n] x → m = n := by
  intro m
  induction m with
  | zero =>
    intro n _ hn he
    cases n with
    | zero => rfl
    | succ n =>
      have hh := hN n (by omega)
      apply False.elim
      apply hx
      refine Finset.mem_image.mpr ⟨f^[n] x, hh, ?_⟩
      simpa only [Function.iterate_zero_apply, Function.iterate_succ_apply'] using he.symm
  | succ m ih =>
    intro n hm hn he
    cases n with
    | zero =>
      apply False.elim
      apply hx
      refine Finset.mem_image.mpr ⟨f^[m] x, hN m (by omega), ?_⟩
      simpa only [Function.iterate_zero_apply, Function.iterate_succ_apply'] using he
    | succ n =>
      apply congrArg Nat.succ
      apply ih n (by omega) (by omega)
      apply hf (hN m (by omega)) (hN n (by omega))
      simpa only [Function.iterate_succ_apply'] using he

/-- Repeated score-preserving pivots expose a first neighbor outside the blocked
endpoint set. The induction preserves the exact original unprocessed tails. -/
lemma expose_escape {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ (S.tail ⟨v, S.root_mem⟩).snd ∉ B := by
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
  obtain ⟨N, hexit, hprev⟩ := exists_first_exit_of_injective_successor A f hf x hx
  have hinj := iterate_injective_before_exit A f hf x hx N hprev
  have hreach : ∀ n ≤ N, ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧
      (S.tail ⟨v,S.root_mem⟩).snd = f^[n] x ∧
      ∀ z : B, z.val ≠ v → (∀ m < n, z.val ≠ f^[m] x) → S.tail z = R.tail z := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨R, rfl, rfl, fun _ _ _ ↦ rfl⟩
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
      have hstep : ∃ S' : RootedTailSystem G k v B,
          S'.system.score = S.system.score ∧
          (S'.tail ⟨v,S'.root_mem⟩).snd = (S.tail w).penultimate ∧
          ∀ z : B, z.val ≠ v → z ≠ w → S'.tail z = S.tail z := by
        cases hc : S.tail ⟨v,S.root_mem⟩ with
        | nil => exact (S.root_nonempty (hc ▸ Walk.Nil.nil)).elim
        | @cons _ u _ h p =>
          have huw : u = w.val := by simpa only [hc, Walk.snd_cons] using hfirst
          subst u
          exact S.pivot w h p hc
      obtain ⟨S', hs', hf', ht'⟩ := hstep
      refine ⟨S', hs'.trans hscore, ?_, ?_⟩
      · rw [hf', htw, Function.iterate_succ_apply']
        change (R.tail ⟨f^[n] x,hwB⟩).penultimate =
          if h : f^[n] x ∈ B then (R.tail ⟨f^[n] x,h⟩).penultimate else f^[n] x
        rw [dif_pos hwB]
      · intro z hzv hz
        have hzw : z ≠ w := fun he ↦ hz n (by omega) (congrArg Subtype.val he)
        exact (ht' z hzv hzw).trans (htail z hzv (fun m hm ↦ hz m (by omega)))
  obtain ⟨S, hs, hfirst, _⟩ := hreach N le_rfl
  refine ⟨S, hs, ?_⟩
  intro hB
  have hvne : (S.tail ⟨v,S.root_mem⟩).snd ≠ v :=
    ((S.tail ⟨v,S.root_mem⟩).adj_snd S.root_nonempty).ne.symm
  exact hexit (Finset.mem_erase.mpr ⟨hfirst ▸ hvne, hfirst ▸ hB⟩)


lemma orient_root_start {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ S.tail = R.tail ∧ ∃ i, S.system.start i = v := by
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
  refine ⟨S, hs, rfl, ?_⟩
  let i := NormalTrailSystem.owner R.system v
  rcases NormalTrailSystem.owner_spec R.system v with hv | hv
  · have hn : R.system.finish i ≠ v := fun he ↦ R.system.endpoints_ne i (hv.symm.trans he.symm)
    exact ⟨i, by simpa [S, eps, hn] using (ht i).1.trans (by simpa [eps, hn] using hv.symm)⟩
  · have hv' : R.system.finish i = v := hv.symm
    refine ⟨i, ?_⟩
    change T.start i = v
    rw [(ht i).1]
    simp [eps, hv']

/-- A representative of one member can be used for a strict escape slide;
only its subgraph, not its original traversal order, needs to agree. -/
lemma improve_representative {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) {w : V}
    (h : G.Adj (T.start i) w) (p : G.Walk w (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support)
    (havoid : T.start i ∉ (T.walk (NormalTrailSystem.owner T w)).support) :
    ∃ S : NormalTrailSystem G k, T.score < S.score := by
  classical
  let q := Function.update T.walk i (Walk.cons h p)
  have hqi : q i = Walk.cons h p := by simp [q]
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
  have hs : R.score = T.score := by
    unfold NormalTrailSystem.score
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun K : G.Subgraph ↦ K.verts.ncard) (hpart j)
  have ho : R.start i ∉ (R.walk (NormalTrailSystem.owner R w)).support := by
    change T.start i ∉ (q (NormalTrailSystem.owner T w)).support
    rw [← Walk.mem_verts_toSubgraph, hpart, Walk.mem_verts_toSubgraph]
    exact havoid
  obtain ⟨S, hS⟩ := R.improve_of_escape_slide i h p hqi hv ho
  exact ⟨S, hs ▸ hS⟩

/-- A rooted normal system with a nonempty root tail can be strictly improved.
This is the global endpoint-repetition exchange, not an internal-loop theorem. -/
lemma improve {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) :
    ∃ T : NormalTrailSystem G k, R.system.score < T.score := by
  obtain ⟨R₁, hs₁, hescape⟩ := R.expose_escape
  obtain ⟨S, hs₂, ht, i, hi⟩ := R₁.orient_root_start
  have hesc : (S.tail ⟨v,S.root_mem⟩).snd ∉ B := by simpa only [ht] using hescape
  have hia : i ∈ S.active := (S.start_mem i).mp (hi.symm ▸ S.root_mem)
  let a : B := ⟨S.system.start i, (S.start_mem i).mpr hia⟩
  let b : B := ⟨S.system.finish i, (S.finish_mem i).mpr hia⟩
  have ha : a = ⟨v,S.root_mem⟩ := Subtype.ext hi
  have hab : a ≠ b := fun h ↦ S.system.endpoints_ne i (congrArg Subtype.val h)
  have hd : Disjoint (S.tail a).toSubgraph.edgeSet (S.tail b).reverse.toSubgraph.edgeSet := by
    simpa only [Walk.toSubgraph_reverse] using S.disjoint hab
  have hp := trail_append_of_disjoint (S.trail a) (S.trail b).reverse hd
  have he : (S.system.walk i).toSubgraph = ((S.tail a).append (S.tail b).reverse).toSubgraph := by
    rw [Walk.toSubgraph_append, Walk.toSubgraph_reverse]
    exact S.decomp i hia
  have hnil : ¬(S.tail a).Nil := ha.symm ▸ S.root_nonempty
  have hesc' : (S.tail a).snd ∉ B := by rw [ha]; exact hesc
  have hout : ∀ w, w ∉ B → v ∉ (S.system.walk (NormalTrailSystem.owner S.system w)).support := by
    intro w hw
    exact S.outside _ (fun hh ↦ hw ((S.mem_ends_iff_owner_active w).mpr hh))
  have hgain : ∃ T : NormalTrailSystem G k, S.system.score < T.score := by
    let C := S.tail a
    let h := C.adj_snd hnil
    have hform : Walk.cons h (C.tail.append (S.tail b).reverse) = C.append (S.tail b).reverse :=
      congrArg (fun z : G.Walk a.val v ↦ z.append (S.tail b).reverse) (C.cons_tail_eq hnil)
    have hv : S.system.start i ∈ (C.tail.append (S.tail b).reverse).support := by
      rw [hi]
      exact (Walk.mem_support_append_iff _ _).mpr (Or.inl C.tail.end_mem_support)
    apply improve_representative S.system i h (C.tail.append (S.tail b).reverse)
    · rw [hform]; exact hp
    · rw [hform]; exact he
    · exact hv
    · rw [hi]
      exact hout C.snd hesc'
  obtain ⟨T, hT⟩ := hgain
  exact ⟨T, (hs₂.trans hs₁) ▸ hT⟩


lemma append_trail_disjoint {V : Type*} {G : SimpleGraph V} {a b c : V}
    {p : G.Walk a b} {q : G.Walk b c} (hpq : (p.append q).IsTrail) :
    Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet := by
  rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append] at hpq
  apply Set.disjoint_left.mpr
  intro e hp hq
  exact hpq.2.2 e (p.mem_edges_toSubgraph.mp hp) e (q.mem_edges_toSubgraph.mp hq) rfl

/-- Construct the rooted cuts from an actual repeated starting endpoint. -/
lemma of_repeated_start {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i₀ : Fin k) {w : V}
    (h : G.Adj (T.start i₀) w) (p : G.Walk w (T.finish i₀))
    (he : T.walk i₀ = Walk.cons h p) (hv : T.start i₀ ∈ p.support) :
    ∃ B : Finset V, ∃ R : RootedTailSystem G k (T.start i₀) B, R.system = T := by
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
        T.walk j.val = L.append Q.reverse ∧ (j = j₀ → ¬L.Nil) := by
    by_cases hj : j = j₀
    · subst j
      refine ⟨Walk.cons h (p.takeUntil v hv), (p.dropUntil v hv).reverse, ?_, ?_⟩
      · simp only [Walk.reverse_reverse, Walk.cons_append, Walk.take_spec]
        exact he
      · intro _; simp
    · refine ⟨(T.walk j.val).takeUntil v ((hia j.val).mp j.property),
        ((T.walk j.val).dropUntil v ((hia j.val).mp j.property)).reverse, ?_,
        fun hh ↦ (hj hh).elim⟩
      simp
  choose L Q hc hn using hcuts
  have hpart (j : I) : (T.walk j.val).toSubgraph = (L j).toSubgraph ⊔ (Q j).toSubgraph := by
    rw [hc j, Walk.toSubgraph_append, Walk.toSubgraph_reverse]
  have htr (j : I) : (L j).IsTrail ∧ (Q j).IsTrail ∧
      Disjoint (L j).toSubgraph.edgeSet (Q j).toSubgraph.edgeSet := by
    have ht : ((L j).append (Q j).reverse).IsTrail := hc j ▸ T.isTrail j.val
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
      (L j₀).toSubgraph_adj_snd (hn j₀ rfl)
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
  exact ⟨B, R, rfl⟩

/-- A repeated starting endpoint admits a global strict improvement, even when
its initial edge is blocked and even when intermediate endpoints share a member. -/
lemma improve_of_repeated_start {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) {w : V}
    (h : G.Adj (T.start i) w) (p : G.Walk w (T.finish i))
    (he : T.walk i = Walk.cons h p) (hv : T.start i ∈ p.support) :
    ∃ S : NormalTrailSystem G k, T.score < S.score := by
  obtain ⟨B, R, hR⟩ := of_repeated_start T i h p he hv
  obtain ⟨S, hS⟩ := R.improve
  exact ⟨S, hR ▸ hS⟩

lemma max_score_no_repeated_start {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    (i : Fin k) {w : V} (h : G.Adj (T.start i) w) (p : G.Walk w (T.finish i))
    (he : T.walk i = Walk.cons h p) : T.start i ∉ p.support := by
  intro hv
  obtain ⟨S, hs⟩ := improve_of_repeated_start T i h p he hv
  exact (not_lt_of_ge (hmax S)) hs

end RootedTailSystem
end Erdos583RootedDevelopment
