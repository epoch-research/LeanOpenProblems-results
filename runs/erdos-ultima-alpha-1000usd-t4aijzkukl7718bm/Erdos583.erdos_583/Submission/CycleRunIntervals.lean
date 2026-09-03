import Submission.PathIntervals
import Submission.PrivatePathExpansion

/-! Ordered cycle intervals and the private interiors of maximal runs through a set. -/
namespace Erdos583CycleRunIntervalsDevelopment
open SimpleGraph Erdos583Work
open Erdos583PathIntervalsDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} {G : SimpleGraph V} {r b : V}

lemma cycle_append_comm {u v : V} (P : G.Walk u v) (Q : G.Walk v u)
    (hc : (P.append Q).IsCycle) : (Q.append P).IsCycle := by
  have htrail : (Q.append P).IsTrail := trail_append_of_disjoint hc.isTrail.of_append_right
    hc.isTrail.of_append_left (RootedTailSystem.append_trail_disjoint hc.isTrail).symm
  have hnil : ¬(Q.append P).Nil := by
    rw [Walk.not_nil_iff_lt_length,Walk.length_append]
    have hh := hc.three_le_length
    rw [Walk.length_append] at hh
    omega
  refine ⟨⟨htrail,?_⟩,?_⟩
  · exact fun h ↦ hnil (h ▸ Walk.Nil.nil)
  · have hh := hc.support_nodup
    rw [Walk.tail_support_append] at hh ⊢
    exact List.nodup_append_comm.mp hh

lemma cycle_getVert_eq (C : G.Walk r r) (hc : C.IsCycle) {i j : ℕ}
    (hi : i ≤ C.length) (hj : j ≤ C.length) :
    C.getVert i=C.getVert j ↔ i=j ∨ (i=0 ∧ j=C.length) ∨ (i=C.length ∧ j=0) := by
  constructor
  · intro he
    by_cases hi0 : i=0
    · subst i
      have hh := (hc.getVert_endpoint_iff hj).mp (by simpa only [Walk.getVert_zero] using he.symm)
      rcases hh with h|h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl ⟨rfl,h⟩)
    by_cases hj0 : j=0
    · subst j
      have hh := (hc.getVert_endpoint_iff hi).mp (by simpa only [Walk.getVert_zero] using he)
      exact Or.inr (Or.inr ⟨hh.resolve_left hi0,rfl⟩)
    exact Or.inl (hc.getVert_injOn ⟨by omega,hi⟩ ⟨by omega,hj⟩ he)
  · rintro (rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp

lemma cycle_interval_complement (C : G.Walk r r) (hc : C.IsCycle)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ C.length) :
    ((interval C i j hij).append ((C.drop j).append (C.take i))).IsCycle ∧
      ((interval C i j hij).append ((C.drop j).append (C.take i))).toSubgraph=C.toSubgraph ∧
      r ∈ ((C.drop j).append (C.take i)).support := by
  have hc' : ((C.take i).append ((interval C i j hij).append (C.drop j))).IsCycle :=
    (split_interval C hij hj) ▸ hc
  have hh := cycle_append_comm _ _ hc'
  rw [←Walk.append_assoc] at hh
  refine ⟨hh,?_,?_⟩
  · have he := congrArg Walk.toSubgraph (split_interval C hij hj)
    simp only [Walk.toSubgraph_append] at he ⊢
    rw [he]
    ac_rfl
  · rw [Walk.mem_support_append_iff]
    exact Or.inl (C.drop j).end_mem_support

lemma cycle_interval_path (C : G.Walk r r) (hc : C.IsCycle)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ C.length) (hne : C.getVert i ≠ C.getVert j) :
    (interval C i j hij).IsPath :=
  (cycle_interval_complement C hc hij hj).1.isPath_of_append_left (Walk.not_nil_of_ne hne.symm)

/-- A run has outside endpoints, at least one inside vertex, and no outside vertex in its interior. -/
def Run (C : G.Walk r b) (S : Set V) (i j : ℕ) : Prop :=
  i+2 ≤ j ∧ j ≤ C.length ∧ C.getVert i ∉ S ∧ C.getVert j ∉ S ∧
    ∀ m, i < m → m < j → C.getVert m ∈ S

lemma Run.endpoint_ne (C : G.Walk r r) (hc : C.IsCycle) (S : Set V)
    {i j t : ℕ} (h : Run C S i j) (ht0 : 0 < t) (htN : t < C.length) (ht : C.getVert t ∉ S) :
    C.getVert i ≠ C.getVert j := by
  intro he
  rcases (cycle_getVert_eq C hc (by have := h.2.1; have := h.1; omega) h.2.1).mp he with he|⟨hi,hj⟩|⟨hi,hj⟩
  · have := h.1; omega
  · exact ht (h.2.2.2.2 t (by omega) (by omega))
  · have := h.1; have := h.2.1; omega

lemma Run.internal_mem (C : G.Walk r b) (S : Set V) {i j : ℕ} (h : Run C S i j)
    {z : V} (hz : z ∈ (interval C i j (by have := h.1; omega)).support)
    (hzi : z ≠ C.getVert i) (hzj : z ≠ C.getVert j) : z ∈ S := by
  obtain ⟨m,him,hmj,rfl⟩ := (interval_support C (by have := h.1; omega) h.2.1 z).mp hz
  have hmi : m ≠ i := fun hh ↦ hzi (congrArg C.getVert hh)
  have hmj' : m ≠ j := fun hh ↦ hzj (congrArg C.getVert hh)
  exact h.2.2.2.2 m (by omega) (by omega)

lemma Run.intervals_ordered (C : G.Walk r b) (S : Set V) {i j l m : ℕ}
    (h : Run C S i j) (h' : Run C S l m) : (i=l ∧ j=m) ∨ j ≤ l ∨ m ≤ i := by
  have h1 := h.1
  have h2 := h'.1
  have hil : ¬(i < l ∧ l < j) := fun hh ↦ h'.2.2.1 (h.2.2.2.2 l hh.1 hh.2)
  have hli : ¬(l < i ∧ i < m) := fun hh ↦ h.2.2.1 (h'.2.2.2.2 i hh.1 hh.2)
  have hjm : ¬(i < m ∧ m < j) := fun hh ↦ h'.2.2.2.1 (h.2.2.2.2 m hh.1 hh.2)
  have hmj : ¬(l < j ∧ j < m) := fun hh ↦ h.2.2.2.1 (h'.2.2.2.2 j hh.1 hh.2)
  omega

lemma Run.private (C : G.Walk r r) (hc : C.IsCycle) (S : Set V) (hr : r ∉ S)
    {i j l m : ℕ} (h : Run C S i j) (h' : Run C S l m) (hne : ¬(i=l ∧ j=m))
    {z : V} (hz : z ∈ (interval C i j (by have := h.1; omega)).support)
    (hzi : z ≠ C.getVert i) (hzj : z ≠ C.getVert j) :
    z ∉ (interval C l m (by have := h'.1; omega)).support := by
  intro hz'
  have hzS := h.internal_mem C S hz hzi hzj
  have hzr : z ≠ r := fun hh ↦ hr (hh ▸ hzS)
  obtain ⟨p,hip,hpj,hzp⟩ := (interval_support C (by have := h.1; omega) h.2.1 z).mp hz
  obtain ⟨q,hlq,hqm,hzq⟩ := (interval_support C (by have := h'.1; omega) h'.2.1 z).mp hz'
  have hpq : p=q := by
    have hh := (cycle_getVert_eq C hc (hpj.trans h.2.1) (hqm.trans h'.2.1)).mp (hzp.symm.trans hzq)
    rcases hh with hh|⟨rfl,_⟩|⟨rfl,_⟩
    · exact hh
    · exact (hzr (by simpa only [Walk.getVert_zero] using hzp)).elim
    · exact (hzr (by simpa only [Walk.getVert_length] using hzp)).elim
  have hpi : p ≠ i := fun hh ↦ hzi (hh ▸ hzp)
  have hpj' : p ≠ j := fun hh ↦ hzj (hh ▸ hzp)
  have ho := (h.intervals_ordered C S h').resolve_left hne
  omega

lemma Run.shortcuts_injective (C : G.Walk r r) (hc : C.IsCycle) (S : Set V)
    {t u : ℕ} (ht0 : 0 < t) (htu : t < u) (huN : u < C.length)
    (ht : C.getVert t ∉ S) (hu : C.getVert u ∉ S)
    {i j l m : ℕ} (h : Run C S i j) (h' : Run C S l m)
    (he : s(C.getVert i,C.getVert j)=s(C.getVert l,C.getVert m)) : i=l ∧ j=m := by
  have hi := h.1
  have hj := h.2.1
  have hl := h'.1
  have hm := h'.2.1
  have hit : ¬(i < t ∧ t < j) := fun hh ↦ ht (h.2.2.2.2 t hh.1 hh.2)
  have hiu : ¬(i < u ∧ u < j) := fun hh ↦ hu (h.2.2.2.2 u hh.1 hh.2)
  have hlt : ¬(l < t ∧ t < m) := fun hh ↦ ht (h'.2.2.2.2 t hh.1 hh.2)
  have hlu : ¬(l < u ∧ u < m) := fun hh ↦ hu (h'.2.2.2.2 u hh.1 hh.2)
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
  · have h1' := (cycle_getVert_eq C hc (by omega) (by omega)).mp h1
    have h2' := (cycle_getVert_eq C hc hj hm).mp h2
    omega
  · have h1' := (cycle_getVert_eq C hc (by omega) hm).mp h1
    have h2' := (cycle_getVert_eq C hc hj (by omega)).mp h2
    omega

lemma Run.shortcut_not_cycle_edge (C : G.Walk r r) (hc : C.IsCycle) (S : Set V)
    {t u : ℕ} (ht0 : 0 < t) (htu : t < u) (huN : u < C.length)
    (ht : C.getVert t ∉ S) (hu : C.getVert u ∉ S)
    {i j : ℕ} (h : Run C S i j) : s(C.getVert i,C.getVert j) ∉ C.edges := by
  intro he
  obtain ⟨q,hq,he⟩ := (edges_positions C _).mp he
  have hi := h.1
  have hj := h.2.1
  have hit : ¬(i < t ∧ t < j) := fun hh ↦ ht (h.2.2.2.2 t hh.1 hh.2)
  have hiu : ¬(i < u ∧ u < j) := fun hh ↦ hu (h.2.2.2.2 u hh.1 hh.2)
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
  · have h1' := (cycle_getVert_eq C hc (by omega) (by omega)).mp h1
    have h2' := (cycle_getVert_eq C hc hj (by omega)).mp h2
    omega
  · have h1' := (cycle_getVert_eq C hc (by omega) (by omega)).mp h1
    have h2' := (cycle_getVert_eq C hc hj (by omega)).mp h2
    omega

lemma exists_run_at_edge (C : G.Walk r r) (S : Set V) (hr : r ∉ S) {q : ℕ}
    (hq : q < C.length) (hinside : C.getVert q ∈ S ∨ C.getVert (q+1) ∈ S) :
    ∃ i j, Run C S i j ∧ i ≤ q ∧ q < j := by
  let Out (i : ℕ) : Prop := C.getVert i ∉ S
  have hzero : Out 0 := by simpa only [Out,Walk.getVert_zero] using hr
  have hlast : Out C.length := by simpa only [Out,Walk.getVert_length] using hr
  let i := Nat.findGreatest Out q
  have hi : i ≤ q := Nat.findGreatest_le q
  have hio : Out i := Nat.findGreatest_spec (Nat.zero_le q) hzero
  have hex : ∃ j, q+1 ≤ j ∧ j ≤ C.length ∧ Out j := ⟨C.length,by omega,le_rfl,hlast⟩
  let j := Nat.find hex
  obtain ⟨hqj,hjN,hjo⟩ : q+1 ≤ j ∧ j ≤ C.length ∧ Out j := Nat.find_spec hex
  have hij : i+2 ≤ j := by
    by_contra hh
    have hie : i=q := by omega
    have hje : j=q+1 := by omega
    rcases hinside with h|h
    · exact hio (hie ▸ h)
    · exact hjo (hje ▸ h)
  refine ⟨i,j,⟨hij,hjN,hio,hjo,?_⟩,hi,by omega⟩
  intro m him hmj
  by_contra hm
  by_cases hmq : m ≤ q
  · exact Nat.findGreatest_is_greatest him hmq hm
  · exact Nat.find_min hex hmj ⟨by omega,by omega,hm⟩

abbrev RunIndex (C : G.Walk r b) :=
  {p : Fin (C.length+1) × Fin (C.length+1) // p.1.val+2 ≤ p.2.val}

noncomputable def runs (C : G.Walk r b) (S : Set V) : Finset (RunIndex C) :=
  Finset.univ.filter fun p ↦ Run C S p.val.1.val p.val.2.val

def runStart (C : G.Walk r b) (p : RunIndex C) : V := C.getVert p.val.1.val

def runFinish (C : G.Walk r b) (p : RunIndex C) : V := C.getVert p.val.2.val

def runPath (C : G.Walk r b) (p : RunIndex C) : G.Walk (runStart C p) (runFinish C p) :=
  interval C p.val.1.val p.val.2.val (by have := p.property; omega)

lemma mem_runs (C : G.Walk r b) (S : Set V) (p : RunIndex C) :
    p ∈ runs C S ↔ Run C S p.val.1.val p.val.2.val := by simp only [runs,Finset.mem_filter,Finset.mem_univ,true_and]

lemma runPath_edges_subset (C : G.Walk r b) (p : RunIndex C) :
    (runPath C p).toSubgraph.edgeSet ⊆ C.toSubgraph.edgeSet :=
  interval_edges_subset C (by have := p.property; omega) (by have := p.val.2.isLt; omega)

lemma runs_cover_inside_edges (C : G.Walk r r) (S : Set V) (hr : r ∉ S)
    {x y : V} (hxy : C.toSubgraph.Adj x y) (hS : x ∈ S ∨ y ∈ S) :
    ∃ p ∈ runs C S, (runPath C p).toSubgraph.Adj x y := by
  obtain ⟨q,hq,he⟩ := (edges_positions C s(x,y)).mp (C.mem_edges_toSubgraph.mp hxy)
  have hinside : C.getVert q ∈ S ∨ C.getVert (q+1) ∈ S := by
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hS
    · exact hS.symm
  obtain ⟨i,j,hij,hiq,hqj⟩ := exists_run_at_edge C S hr hq hinside
  let p : RunIndex C := ⟨⟨⟨i,by have := hij.1; have := hij.2.1; omega⟩,
    ⟨j,by have := hij.2.1; omega⟩⟩,hij.1⟩
  refine ⟨p,(mem_runs C S p).mpr hij,?_⟩
  change s(x,y) ∈ (interval C i j (by have := hij.1; omega)).toSubgraph.edgeSet
  exact (interval_edges C (by have := hij.1; omega) hij.2.1 s(x,y)).mpr ⟨q,hiq,hqj,he⟩

lemma two_ordered_outside_marks [Fintype V] (C : G.Walk r r) (S : Set V)
    (hr : r ∉ S) (hsize : 3 ≤ (C.toSubgraph.verts \ S).ncard) :
    ∃ t u : ℕ, 0 < t ∧ t < u ∧ u < C.length ∧ C.getVert t ∉ S ∧ C.getVert u ∉ S := by
  let R := C.toSubgraph.verts \ S
  have hrR : r ∈ R := ⟨C.start_mem_verts_toSubgraph,hr⟩
  have hcard : 1 < (R \ {r}).ncard := by
    rw [Set.ncard_diff_singleton_of_mem hrR]
    change 3 ≤ R.ncard at hsize
    omega
  obtain ⟨x,y,hx,hy,hxy⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hcard
  obtain ⟨i,hix,hiN⟩ := C.mem_support_iff_exists_getVert.mp (C.mem_verts_toSubgraph.mp hx.1.1)
  obtain ⟨j,hjy,hjN⟩ := C.mem_support_iff_exists_getVert.mp (C.mem_verts_toSubgraph.mp hy.1.1)
  have hi0 : i ≠ 0 := by rintro rfl; exact hx.2 (by simpa using hix.symm)
  have hj0 : j ≠ 0 := by rintro rfl; exact hy.2 (by simpa using hjy.symm)
  have hiN' : i ≠ C.length := by rintro rfl; exact hx.2 (by simpa using hix.symm)
  have hjN' : j ≠ C.length := by rintro rfl; exact hy.2 (by simpa using hjy.symm)
  have hij : i ≠ j := fun hh ↦ hxy (hix.symm.trans ((congrArg C.getVert hh).trans hjy))
  have hiS : C.getVert i ∉ S := hix ▸ hx.1.2
  have hjS : C.getVert j ∉ S := hjy ▸ hy.1.2
  rcases lt_or_gt_of_ne hij with h|h
  · exact ⟨i,j,by omega,h,by omega,hiS,hjS⟩
  · exact ⟨j,i,by omega,h,by omega,hjS,hiS⟩

end Erdos583CycleRunIntervalsDevelopment
