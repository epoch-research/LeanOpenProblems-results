import Submission.LongTailEar

/-! Maximal runs through a set along a simple path, with retained endpoints. -/
namespace Erdos583PathRunIntervalsDevelopment
open SimpleGraph Erdos583Work
open Erdos583CycleRunIntervalsDevelopment Erdos583PathIntervalsDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} {G : SimpleGraph V} {a b : V}

lemma run_endpoint_ne (P : G.Walk a b) (hp : P.IsPath) (S : Set V) {i j : ℕ}
    (h : Run P S i j) : P.getVert i ≠ P.getVert j := by
  intro he
  have hi := h.1
  have hj := h.2.1
  have hh := hp.getVert_injOn (show i ≤ P.length by omega) hj he
  omega

lemma run_private (P : G.Walk a b) (hp : P.IsPath) (S : Set V) {i j l m : ℕ}
    (h : Run P S i j) (h' : Run P S l m) (hne : ¬(i=l ∧ j=m))
    {z : V} (hz : z ∈ (interval P i j (by have := h.1; omega)).support)
    (hzi : z ≠ P.getVert i) (hzj : z ≠ P.getVert j) :
    z ∉ (interval P l m (by have := h'.1; omega)).support := by
  intro hz'
  obtain ⟨p,hip,hpj,hzp⟩ := (interval_support P (by have := h.1; omega) h.2.1 z).mp hz
  obtain ⟨q,hlq,hqm,hzq⟩ := (interval_support P (by have := h'.1; omega) h'.2.1 z).mp hz'
  have hpq := hp.getVert_injOn (hpj.trans h.2.1) (hqm.trans h'.2.1) (hzp.symm.trans hzq)
  have hpi : p ≠ i := fun hh ↦ hzi (hh ▸ hzp)
  have hpj' : p ≠ j := fun hh ↦ hzj (hh ▸ hzp)
  have ho := (h.intervals_ordered P S h').resolve_left hne
  omega

lemma run_shortcuts_injective (P : G.Walk a b) (hp : P.IsPath) (S : Set V) {i j l m : ℕ}
    (h : Run P S i j) (h' : Run P S l m)
    (he : s(P.getVert i,P.getVert j)=s(P.getVert l,P.getVert m)) : i=l ∧ j=m := by
  have hi := h.1
  have hj := h.2.1
  have hl := h'.1
  have hm := h'.2.1
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
  · exact ⟨hp.getVert_injOn (show i ≤ P.length by omega) (show l ≤ P.length by omega) h1,hp.getVert_injOn hj hm h2⟩
  · have h1' := hp.getVert_injOn (show i ≤ P.length by omega) hm h1
    have h2' := hp.getVert_injOn hj (show l ≤ P.length by omega) h2
    omega

lemma run_shortcut_not_path_edge (P : G.Walk a b) (hp : P.IsPath) (S : Set V) {i j : ℕ}
    (h : Run P S i j) : s(P.getVert i,P.getVert j) ∉ P.edges := by
  intro he
  obtain ⟨q,hq,he⟩ := (edges_positions P _).mp he
  have hi := h.1
  have hj := h.2.1
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
  · have h1' := hp.getVert_injOn (show i ≤ P.length by omega) (show q ≤ P.length by omega) h1
    have h2' := hp.getVert_injOn hj (show q+1 ≤ P.length by omega) h2
    omega
  · have h1' := hp.getVert_injOn (show i ≤ P.length by omega) (show q+1 ≤ P.length by omega) h1
    have h2' := hp.getVert_injOn hj (show q ≤ P.length by omega) h2
    omega

lemma exists_path_run_at_edge (C : G.Walk a b) (S : Set V) (ha : a ∉ S) (hb : b ∉ S) {q : ℕ}
    (hq : q < C.length) (hinside : C.getVert q ∈ S ∨ C.getVert (q+1) ∈ S) :
    ∃ i j, Run C S i j ∧ i ≤ q ∧ q < j := by
  let Out (i : ℕ) : Prop := C.getVert i ∉ S
  have hzero : Out 0 := by simpa only [Out,Walk.getVert_zero] using ha
  have hlast : Out C.length := by simpa only [Out,Walk.getVert_length] using hb
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

lemma path_runs_cover_inside_edges (C : G.Walk a b) (S : Set V) (ha : a ∉ S) (hb : b ∉ S)
    {x y : V} (hxy : C.toSubgraph.Adj x y) (hS : x ∈ S ∨ y ∈ S) :
    ∃ p ∈ runs C S, (runPath C p).toSubgraph.Adj x y := by
  obtain ⟨q,hq,he⟩ := (edges_positions C s(x,y)).mp (C.mem_edges_toSubgraph.mp hxy)
  have hinside : C.getVert q ∈ S ∨ C.getVert (q+1) ∈ S := by
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hS
    · exact hS.symm
  obtain ⟨i,j,hij,hiq,hqj⟩ := exists_path_run_at_edge C S ha hb hq hinside
  let p : RunIndex C := ⟨⟨⟨i,by have := hij.1; have := hij.2.1; omega⟩,
    ⟨j,by have := hij.2.1; omega⟩⟩,hij.1⟩
  refine ⟨p,(mem_runs C S p).mpr hij,?_⟩
  change s(x,y) ∈ (interval C i j (by have := hij.1; omega)).toSubgraph.edgeSet
  exact (interval_edges C (by have := hij.1; omega) hij.2.1 s(x,y)).mpr ⟨q,hiq,hqj,he⟩

end Erdos583PathRunIntervalsDevelopment
