import Submission.ArcAdjoint

/-!
A structural investigation of triangle fibers joined by matchings over a
triangle-free index graph. This file is auxiliary to Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595MatchingBundle
open Erdos595ArcAdjoint

variable {V I : Type*} (H : SimpleGraph V) (B : SimpleGraph I)
    (π : V → I) (κ : V → Fin 3)

structure Assumptions : Prop where
  injective : Function.Injective (fun v => (π v,κ v))
  cross : ∀ {a b}, H.Adj a b → π a ≠ π b → B.Adj (π a) (π b)
  matching : ∀ {a b c}, H.Adj a b → H.Adj a c → π a ≠ π b → π b = π c → b = c
  triangleFree : B.CliqueFree 3

variable (h : Assumptions H B π κ)

include h in
lemma coord_ne {a b : V} (hab : a ≠ b) (he : π a = π b) : κ a ≠ κ b := by
  intro hk
  exact hab (h.injective (Prod.ext he hk))

include h in
lemma triangle_fiber {a b c : V} (hab : H.Adj a b) (hac : H.Adj a c)
    (hbc : H.Adj b c) : π a = π b ∧ π a = π c := by
  classical
  by_cases hab' : π a = π b
  · refine ⟨hab',?_⟩
    by_contra hac'
    exact hab.ne (h.matching hac.symm hbc.symm (Ne.symm hac') hab')
  by_cases hac' : π a = π c
  · exact (hac.ne (h.matching hab.symm hbc (Ne.symm hab') hac')).elim
  by_cases hbc' : π b = π c
  · exact (hbc.ne (h.matching hab hac hab' hbc')).elim
  exact (h.triangleFree _ (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨h.cross hab hab',h.cross hac hac',h.cross hbc hbc'⟩)).elim

include h in
/-- Two distinct vertices in one three-point fiber have at most one common neighbor. -/
lemma common_unique {a b c d : V} (hab : a ≠ b) (hf : π a = π b)
    (hac : H.Adj a c) (hbc : H.Adj b c)
    (had : H.Adj a d) (hbd : H.Adj b d) : c = d := by
  classical
  have hfc : π c = π a := by
    by_contra hn
    exact hab (h.matching hac.symm hbc.symm hn hf)
  have hfd : π d = π a := by
    by_contra hn
    exact hab (h.matching had.symm hbd.symm hn hf)
  have hk₁ := coord_ne H B π κ h hab hf
  have hk₂ := coord_ne H B π κ h hac.ne hfc.symm
  have hk₃ := coord_ne H B π κ h hbc.ne (hf.symm.trans hfc.symm)
  have hk₄ := coord_ne H B π κ h had.ne hfd.symm
  have hk₅ := coord_ne H B π κ h hbd.ne (hf.symm.trans hfd.symm)
  apply h.injective
  apply Prod.ext (hfc.trans hfd.symm)
  have ha := (κ a).isLt
  have hb := (κ b).isLt
  have hc := (κ c).isLt
  have hd := (κ d).isLt
  simp only [ne_eq,Fin.ext_iff] at hk₁ hk₂ hk₃ hk₄ hk₅ ⊢
  omega

abbrev Left (p : Biclique H) : Set V := p.val.1
abbrev Right (p : Biclique H) : Set V := p.val.2

def Star (p : Biclique H) : Prop :=
  (∃ a, Left H p = {a}) ∨ (∃ a, Right H p = {a})

lemma left_right_disjoint (p : Biclique H) {v : V}
    (ha : v ∈ Left H p) (hb : v ∈ Right H p) : False :=
  H.loopless v (p.property v ha v hb)

include h in
/-- Non-star bicliques have at most one vertex of each fiber on either side. -/
lemma side_injective {p : Biclique H} (hp : ¬Star H p)
    (ha : (Left H p).Nonempty) (hb : (Right H p).Nonempty) :
    Set.InjOn π (Left H p) ∧ Set.InjOn π (Right H p) := by
  constructor
  · intro a ha' b hb' he
    by_contra hn
    obtain ⟨c,hc⟩ := hb
    apply hp
    right
    refine ⟨c,Set.eq_singleton_iff_unique_mem.mpr ⟨hc,?_⟩⟩
    intro d hd
    exact common_unique H B π κ h hn he
      (p.property _ ha' _ hd) (p.property _ hb' _ hd)
      (p.property _ ha' _ hc) (p.property _ hb' _ hc)
  · intro a ha' b hb' he
    by_contra hn
    obtain ⟨c,hc⟩ := ha
    apply hp
    left
    refine ⟨c,Set.eq_singleton_iff_unique_mem.mpr ⟨hc,?_⟩⟩
    intro d hd
    exact common_unique H B π κ h hn he
      (p.property _ hd _ ha').symm (p.property _ hd _ hb').symm
      (p.property _ hc _ ha').symm (p.property _ hc _ hb').symm

/-- The six directed witnesses in a right-adjoint triangle. -/
structure Six (p q r : Biclique H) where
  x : V
  y : V
  z : V
  x' : V
  y' : V
  z' : V
  hx : x ∈ Right H p ∧ x ∈ Left H q
  hy : y ∈ Right H q ∧ y ∈ Left H r
  hz : z ∈ Right H r ∧ z ∈ Left H p
  hx' : x' ∈ Right H q ∧ x' ∈ Left H p
  hy' : y' ∈ Right H r ∧ y' ∈ Left H q
  hz' : z' ∈ Right H p ∧ z' ∈ Left H r

noncomputable def six {p q r : Biclique H}
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r)
    (hqr : (right H).Adj q r) : Six H p q r where
  x := hpq.1.choose
  y := hqr.1.choose
  z := hpr.2.choose
  x' := hpq.2.choose
  y' := hqr.2.choose
  z' := hpr.1.choose
  hx := hpq.1.choose_spec
  hy := hqr.1.choose_spec
  hz := hpr.2.choose_spec
  hx' := hpq.2.choose_spec
  hy' := hqr.2.choose_spec
  hz' := hpr.1.choose_spec

variable {p q r : Biclique H} (s : Six H p q r)

lemma Six.tri : H.Adj s.x s.y ∧ H.Adj s.x s.z ∧ H.Adj s.y s.z :=
  ⟨q.property _ s.hx.2 _ s.hy.1,(p.property _ s.hz.2 _ s.hx.1).symm,
    r.property _ s.hy.2 _ s.hz.1⟩

lemma Six.tri' : H.Adj s.x' s.y' ∧ H.Adj s.x' s.z' ∧ H.Adj s.y' s.z' :=
  ⟨(q.property _ s.hy'.2 _ s.hx'.1).symm,p.property _ s.hx'.2 _ s.hz'.1,
    (r.property _ s.hz'.2 _ s.hy'.1).symm⟩

include h in
lemma Six.fibers : (π s.x = π s.y ∧ π s.x = π s.z) ∧
    (π s.x' = π s.y' ∧ π s.x' = π s.z') :=
  ⟨triangle_fiber H B π κ h (s.tri H).1 (s.tri H).2.1 (s.tri H).2.2,
    triangle_fiber H B π κ h (s.tri' H).1 (s.tri' H).2.1 (s.tri' H).2.2⟩

include h in
/-- A non-star in a triangle forces the two witness cycles into distinct fibers. -/
lemma different_fibers (hp : ¬Star H p) : π s.x ≠ π s.x' := by
  intro he
  have hf := s.fibers H B π κ h
  have hi := side_injective H B π κ h hp ⟨s.z,s.hz.2⟩ ⟨s.x,s.hx.1⟩
  have hxz : s.z = s.x' := hi.1 s.hz.2 s.hx'.2 (hf.1.2.symm.trans he)
  have hxz' : s.x = s.z' := hi.2 s.hx.1 s.hz'.1 (he.trans hf.2.2)
  have hyy : s.y = s.y' := common_unique H B π κ h (s.tri H).2.1.ne hf.1.2
    (s.tri H).1 (s.tri H).2.2.symm
    (hxz' ▸ (s.tri' H).2.2.symm) (hxz ▸ (s.tri' H).1)
  exact left_right_disjoint H q (hyy ▸ s.hy'.2) s.hy.1


include h in
lemma prism_sides {a b c d : V} (hp : ¬Star H p)
    (ha : a ∈ Left H p) (hb : b ∈ Left H p)
    (hc : c ∈ Right H p) (hd : d ∈ Right H p)
    (hac : π a = π c) (hbd : π b = π d) (hab : π a ≠ π b) :
    Left H p = {a,b} ∧ Right H p = {c,d} := by
  classical
  have hi := side_injective H B π κ h hp ⟨a,ha⟩ ⟨c,hc⟩
  have hedge : B.Adj (π a) (π b) := by
    rw [hbd]
    exact h.cross (p.property a ha d hd) (hbd ▸ hab)
  have left_fiber (v : V) (hv : v ∈ Left H p) : π v = π a ∨ π v = π b := by
    by_cases h₁ : π v = π a
    · exact Or.inl h₁
    by_cases h₂ : π v = π b
    · exact Or.inr h₂
    apply False.elim
    apply h.triangleFree
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hedge,
      by rw [hac]; exact h.cross (p.property _ hv _ hc).symm (Ne.symm (hac ▸ h₁)),
      by rw [hbd]; exact h.cross (p.property _ hv _ hd).symm (Ne.symm (hbd ▸ h₂))⟩
  have right_fiber (v : V) (hv : v ∈ Right H p) : π v = π c ∨ π v = π d := by
    by_cases h₁ : π v = π c
    · exact Or.inl h₁
    by_cases h₂ : π v = π d
    · exact Or.inr h₂
    apply False.elim
    apply h.triangleFree
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hedge,
      h.cross (p.property _ ha _ hv) (Ne.symm (hac.symm ▸ h₁)),
      h.cross (p.property _ hb _ hv) (Ne.symm (hbd.symm ▸ h₂))⟩
  constructor
  · ext v
    constructor
    · intro hv
      rcases left_fiber v hv with hv' | hv'
      · exact Or.inl (hi.1 hv ha hv')
      · exact Or.inr (hi.1 hv hb hv')
    · intro hv
      rcases hv with rfl | rfl <;> assumption
  · ext v
    constructor
    · intro hv
      rcases right_fiber v hv with hv' | hv'
      · exact Or.inl (hi.2 hv hc hv')
      · exact Or.inr (hi.2 hv hd hv')
    · intro hv
      rcases hv with rfl | rfl <;> assumption

noncomputable def center (p : Biclique H) (hp : Star H p) : V :=
  (show ∃ v, Left H p = {v} ∨ Right H p = {v} from
    hp.elim (fun ⟨v,hv⟩ => ⟨v,Or.inl hv⟩) (fun ⟨v,hv⟩ => ⟨v,Or.inr hv⟩)).choose

lemma center_spec (p : Biclique H) (hp : Star H p) :
    Left H p = {center H p hp} ∨ Right H p = {center H p hp} :=
  (show ∃ v, Left H p = {v} ∨ Right H p = {v} from
    hp.elim (fun ⟨v,hv⟩ => ⟨v,Or.inl hv⟩) (fun ⟨v,hv⟩ => ⟨v,Or.inr hv⟩)).choose_spec

include s in
lemma centers_ne (hp : Star H p) (hq : Star H q) : center H p hp ≠ center H q hq := by
  intro he
  have hx := s.hx
  have hy := s.hy
  have hz := s.hz
  have hx' := s.hx'
  have hy' := s.hy'
  have hz' := s.hz'
  rcases center_spec H p hp with hp' | hp' <;>
    rcases center_spec H q hq with hq' | hq'
  · have hxe : s.x = center H p hp := by simpa only [hq',Set.mem_singleton_iff,← he] using hx.2
    exact left_right_disjoint H p (by simp [hp',hxe]) hx.1
  · have hze : s.z = center H p hp := by simpa only [hp',Set.mem_singleton_iff] using hz.2
    have hye : s.y = center H p hp := by simpa only [hq',Set.mem_singleton_iff,← he] using hy.1
    exact left_right_disjoint H r (hze ▸ hye ▸ hy.2) hz.1
  · have hze : s.z' = center H p hp := by simpa only [hp',Set.mem_singleton_iff] using hz'.1
    have hye : s.y' = center H p hp := by simpa only [hq',Set.mem_singleton_iff,← he] using hy'.2
    exact left_right_disjoint H r hz'.2 (hze ▸ hye ▸ hy'.1)
  · have hxe : s.x' = center H p hp := by simpa only [hq',Set.mem_singleton_iff,← he] using hx'.1
    exact left_right_disjoint H p hx'.2 (by simp [hp',hxe])

lemma center_fiber {a b : V} (hp : Star H p) (ha : a ∈ Left H p)
    (hb : b ∈ Right H p) (he : π a = π b) : π (center H p hp) = π a := by
  rcases center_spec H p hp with hc | hc
  · have hca : a = center H p hp := by simpa only [hc,Set.mem_singleton_iff] using ha
    exact congrArg π hca.symm
  · have hcb : b = center H p hp := by simpa only [hc,Set.mem_singleton_iff] using hb
    exact (congrArg π hcb.symm).trans he.symm

variable [LinearOrder I]

def PairLeft (p : Biclique H) : Prop := ∃ a b, Left H p = {a,b}

noncomputable def profile (p : Biclique H) : Set (Fin 3) := by
  classical
  exact if hp : PairLeft H p then
    κ '' {v | (v ∈ Left H p ∨ v ∈ Right H p) ∧
      π v = min (π hp.choose) (π hp.choose_spec.choose)} else ∅

lemma profile_eq {a b : V} (ha : Left H p = {a,b}) : profile H π κ p =
    κ '' {v | (v ∈ Left H p ∨ v ∈ Right H p) ∧ π v = min (π a) (π b)} := by
  classical
  have hp : PairLeft H p := ⟨a,b,ha⟩
  have he : {hp.choose,hp.choose_spec.choose} = ({a,b} : Set V) :=
    hp.choose_spec.choose_spec.symm.trans ha
  have hm : min (π hp.choose) (π hp.choose_spec.choose) = min (π a) (π b) := by
    rcases Set.pair_eq_pair_iff.mp he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact congrArg₂ min (congrArg π h₁) (congrArg π h₂)
    · exact (congrArg₂ min (congrArg π h₁) (congrArg π h₂)).trans (min_comm _ _)
  simp only [profile,dif_pos hp,hm]

lemma profile_left {a b c d : V} (ha : Left H p = {a,b}) (hb : Right H p = {c,d})
    (hac : π a = π c) (hbd : π b = π d) (hab : π a < π b) :
    profile H π κ p = {κ a,κ c} := by
  rw [profile_eq H π κ ha]
  have hca : π c = π a := hac.symm
  have hda : π d ≠ π a := by rw [← hbd]; exact hab.ne.symm
  have hba : π b ≠ π a := hab.ne.symm
  have hs : {v | (v ∈ Left H p ∨ v ∈ Right H p) ∧ π v = min (π a) (π b)} =
      ({a,c} : Set V) := by
    ext v
    simp only [ha,hb,Set.mem_setOf_eq,Set.mem_insert_iff,Set.mem_singleton_iff,min_eq_left hab.le]
    constructor
    · rintro ⟨(rfl | rfl) | (rfl | rfl),hv⟩
      · exact Or.inl rfl
      · exact (hba hv).elim
      · exact Or.inr rfl
      · exact (hda hv).elim
    · rintro (rfl | rfl) <;> simp [hca]
  rw [hs,Set.image_pair]

lemma profile_right {a b c d : V} (ha : Left H p = {a,b}) (hb : Right H p = {c,d})
    (hac : π a = π c) (hbd : π b = π d) (hab : π b < π a) :
    profile H π κ p = {κ b,κ d} := by
  apply profile_left H π κ (a := b) (b := a) (c := d) (d := c)
    (ha.trans (Set.pair_comm _ _)) (hb.trans (Set.pair_comm _ _)) hbd hac hab

noncomputable def code (p : Biclique H) : Fin 3 ⊕ Set (Fin 3) := by
  classical
  exact if hp : Star H p then Sum.inl (κ (center H p hp)) else Sum.inr (profile H π κ p)

include h in
lemma code_ne (hpq : (right H).Adj p q) (hpr : (right H).Adj p r)
    (hqr : (right H).Adj q r) : code H π κ p ≠ code H π κ q := by
  classical
  let s := six H hpq hpr hqr
  have ht := s.tri H
  have ht' := s.tri' H
  have hf := s.fibers H B π κ h
  intro he
  by_cases hp : Star H p <;> by_cases hq : Star H q
  · simp only [code,dif_pos hp,dif_pos hq,Sum.inl.injEq] at he
    have hpf := center_fiber H π hp s.hz.2 s.hx.1 hf.1.2.symm
    have hqf := center_fiber H π hq s.hx.2 s.hy.1 hf.1.1
    exact coord_ne H B π κ h (centers_ne H s hp hq)
      ((hpf.trans hf.1.2.symm).trans hqf.symm) he
  · simp only [code,dif_pos hp,dif_neg hq,Sum.inl_ne_inr] at he
  · simp only [code,dif_neg hp,dif_pos hq,Sum.inr_ne_inl] at he
  · simp only [code,dif_neg hp,dif_neg hq,Sum.inr.injEq] at he
    have hdiff := different_fibers H B π κ h s hp
    have hpairs := prism_sides H B π κ h hp s.hz.2 s.hx'.2 s.hx.1 s.hz'.1
      hf.1.2.symm hf.2.2 (hf.1.2.symm ▸ hdiff)
    have qpairs := prism_sides H B π κ h hq s.hx.2 s.hy'.2 s.hy.1 s.hx'.1
      hf.1.1 hf.2.1.symm (hf.2.1 ▸ hdiff)
    rcases lt_or_gt_of_ne hdiff with hlt | hgt
    · rw [profile_left H π κ hpairs.1 hpairs.2 hf.1.2.symm hf.2.2 (hf.1.2 ▸ hlt),
        profile_left H π κ qpairs.1 qpairs.2 hf.1.1 hf.2.1.symm (hf.2.1 ▸ hlt)] at he
      have hz : κ s.z ∈ ({κ s.x,κ s.y} : Set (Fin 3)) := he ▸ Set.mem_insert _ _
      rcases hz with hz | hz
      · exact coord_ne H B π κ h ht.2.1.ne.symm hf.1.2.symm hz
      · exact coord_ne H B π κ h ht.2.2.ne.symm (hf.1.2.symm.trans hf.1.1) hz
    · rw [profile_right H π κ hpairs.1 hpairs.2 hf.1.2.symm hf.2.2 (hf.1.2 ▸ hgt),
        profile_right H π κ qpairs.1 qpairs.2 hf.1.1 hf.2.1.symm (hf.2.1 ▸ hgt)] at he
      have hz : κ s.z' ∈ ({κ s.y',κ s.x'} : Set (Fin 3)) := he ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
      rcases hz with hz | hz
      · exact coord_ne H B π κ h ht'.2.2.ne.symm (hf.2.2.symm.trans hf.2.1) hz
      · exact coord_ne H B π κ h ht'.2.1.ne.symm hf.2.2.symm hz

include h in
/-- A finite vertex labeling makes all triangles of the first right adjoint rainbow. -/
theorem right_rainbow {p q r : Biclique H} (hpq : (right H).Adj p q)
    (hpr : (right H).Adj p r) (hqr : (right H).Adj q r) :
    code H π κ p ≠ code H π κ q ∧ code H π κ p ≠ code H π κ r ∧
      code H π κ q ≠ code H π κ r :=
  ⟨code_ne H B π κ h hpq hpr hqr,code_ne H B π κ h hpr hpq hqr.symm,
    code_ne H B π κ h hqr hpq.symm hpr.symm⟩

include h in
/-- The full SECOND right adjoint is covered, with no bound on the index cardinality. -/
theorem second_right_cover : Erdos595Work.IsCountableUnionOfTriangleFree (right (right H)) :=
  right_cover_of_rainbow (right H) (code H π κ) (fun _ _ _ => right_rainbow H B π κ h)


omit [LinearOrder I] in
include h in
/-- The bundle hypotheses themselves imply K4-freeness of the base. -/
theorem base_cliqueFree_four : H.CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have ha : ∀ i j : Fin 4, i ≠ j → H.Adj (e i) (e j) :=
    fun _ _ hij => e.map_rel_iff.mpr hij
  have hf := (triangle_fiber H B π κ h
    (ha 0 1 (by decide)) (ha 0 2 (by decide)) (ha 1 2 (by decide))).1
  have he := common_unique H B π κ h (ha 0 1 (by decide)).ne hf
    (ha 0 2 (by decide)) (ha 1 2 (by decide))
    (ha 0 3 (by decide)) (ha 1 3 (by decide))
  exact (ha 2 3 (by decide)).ne he

section Concrete
variable (σ : I → I → (Fin 3 ≃ Fin 3))

/-- Put a triangle at each index and an arbitrary perfect matching on each
index edge. The chosen linear order specifies which permutation is used. -/
def bundle : SimpleGraph (I × Fin 3) where
  Adj a b := (a.1 = b.1 ∧ a.2 ≠ b.2) ∨
    (a.1 < b.1 ∧ B.Adj a.1 b.1 ∧ σ a.1 b.1 a.2 = b.2) ∨
    (b.1 < a.1 ∧ B.Adj b.1 a.1 ∧ σ b.1 a.1 b.2 = a.2)
  symm := by
    intro a b h
    rcases h with ⟨he,hn⟩ | h | h
    · exact Or.inl ⟨he.symm,hn.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := by
    intro a h
    rcases h with ⟨_,h⟩ | ⟨h,_,_⟩ | ⟨h,_,_⟩
    · exact h rfl
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h

lemma bundle_adj_lt {i j : I} {a b : Fin 3} (hij : i < j) :
    (bundle B σ).Adj (i,a) (j,b) ↔ B.Adj i j ∧ σ i j a = b := by
  change ((i = j ∧ a ≠ b) ∨ (i < j ∧ B.Adj i j ∧ σ i j a = b) ∨
    (j < i ∧ B.Adj j i ∧ σ j i b = a)) ↔ _
  simp only [hij.ne,hij,not_lt_of_gt hij,false_and,true_and,false_or,or_false]

lemma bundle_assumptions (hB : B.CliqueFree 3) :
    Assumptions (bundle B σ) B Prod.fst Prod.snd := by
  refine ⟨fun _ _ h => h,?_,?_,hB⟩
  · intro a b hab hne
    rcases hab with ⟨he,_⟩ | ⟨_,hab,_⟩ | ⟨_,hba,_⟩
    · exact (hne he).elim
    · exact hab
    · exact hba.symm
  · rintro ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ hab hac hij hjk
    change j = k at hjk
    subst k
    change i ≠ j at hij
    apply congrArg (fun x => (j,x))
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ((bundle_adj_lt B σ hlt).mp hab).2.symm.trans
        ((bundle_adj_lt B σ hlt).mp hac).2
    · exact (σ j i).injective
        (((bundle_adj_lt B σ hgt).mp hab.symm).2.trans
          ((bundle_adj_lt B σ hgt).mp hac.symm).2.symm)

/-- All choices of matching permutations are covered, not only the
previously considered two-transposition or single-cone cases. -/
theorem matching_bundle_second_right_cover (hB : B.CliqueFree 3) :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (right (bundle B σ))) :=
  second_right_cover (bundle B σ) B Prod.fst Prod.snd (bundle_assumptions B σ hB)

theorem matching_bundle_cliqueFree (hB : B.CliqueFree 3) :
    (bundle B σ).CliqueFree 4 :=
  base_cliqueFree_four (bundle B σ) B Prod.fst Prod.snd (bundle_assumptions B σ hB)
end Concrete

#print axioms right_rainbow
#print axioms second_right_cover
#print axioms matching_bundle_second_right_cover
#print axioms matching_bundle_cliqueFree
end Erdos595MatchingBundle
