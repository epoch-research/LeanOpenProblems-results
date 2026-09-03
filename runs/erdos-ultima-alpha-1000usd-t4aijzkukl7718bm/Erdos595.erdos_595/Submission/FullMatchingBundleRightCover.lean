import Submission.MatchingBundleRightCover

/-!
A two-internal-fiber covering criterion, and its application to full matching
bundles whose triangles stay in their fibers. This is not a settlement of
Erdős 595: partial matchings need not satisfy the criterion.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FullMatchingBundle
open Erdos595ArcAdjoint Erdos595MatchingBundle

variable {V I : Type*} (H : SimpleGraph V) (π : V → I) (κ : V → Fin 3)

structure Core : Prop where
  injective : Function.Injective (fun v => (π v,κ v))
  matching : ∀ {a b c}, H.Adj a b → H.Adj a c → π a ≠ π b → π b = π c → b = c
  triangle_fiber : ∀ {a b c}, H.Adj a b → H.Adj a c → H.Adj b c →
    π a = π b ∧ π a = π c

variable (h : Core H π κ)

include h in
lemma coord_ne {a b : V} (hab : a ≠ b) (he : π a = π b) : κ a ≠ κ b := by
  intro hk
  exact hab (h.injective (Prod.ext he hk))


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
  have hk₁ := coord_ne H π κ h hab hf
  have hk₂ := coord_ne H π κ h hac.ne hfc.symm
  have hk₃ := coord_ne H π κ h hbc.ne (hf.symm.trans hfc.symm)
  have hk₄ := coord_ne H π κ h had.ne hfd.symm
  have hk₅ := coord_ne H π κ h hbd.ne (hf.symm.trans hfd.symm)
  apply h.injective
  apply Prod.ext (hfc.trans hfd.symm)
  have ha := (κ a).isLt
  have hb := (κ b).isLt
  have hc := (κ c).isLt
  have hd := (κ d).isLt
  simp only [ne_eq,Fin.ext_iff] at hk₁ hk₂ hk₃ hk₄ hk₅ ⊢
  omega


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
    exact common_unique H π κ h hn he
      (p.property _ ha' _ hd) (p.property _ hb' _ hd)
      (p.property _ ha' _ hc) (p.property _ hb' _ hc)
  · intro a ha' b hb' he
    by_contra hn
    obtain ⟨c,hc⟩ := ha
    apply hp
    left
    refine ⟨c,Set.eq_singleton_iff_unique_mem.mpr ⟨hc,?_⟩⟩
    intro d hd
    exact common_unique H π κ h hn he
      (p.property _ hd _ ha').symm (p.property _ hd _ hb').symm
      (p.property _ hc _ ha').symm (p.property _ hc _ hb').symm


variable {p q r : Biclique H} (s : Six H p q r)

include h in
lemma fibers : (π s.x = π s.y ∧ π s.x = π s.z) ∧
    (π s.x' = π s.y' ∧ π s.x' = π s.z') :=
  ⟨h.triangle_fiber (s.tri H).1 (s.tri H).2.1 (s.tri H).2.2,
    h.triangle_fiber (s.tri' H).1 (s.tri' H).2.1 (s.tri' H).2.2⟩

include h in
/-- A non-star in a triangle forces the two witness cycles into distinct fibers. -/
lemma different_fibers (hp : ¬Star H p) : π s.x ≠ π s.x' := by
  intro he
  have hf := fibers H π κ h s
  have hi := side_injective H π κ h hp ⟨s.z,s.hz.2⟩ ⟨s.x,s.hx.1⟩
  have hxz : s.z = s.x' := hi.1 s.hz.2 s.hx'.2 (hf.1.2.symm.trans he)
  have hxz' : s.x = s.z' := hi.2 s.hx.1 s.hz'.1 (he.trans hf.2.2)
  have hyy : s.y = s.y' := common_unique H π κ h (s.tri H).2.1.ne hf.1.2
    (s.tri H).1 (s.tri H).2.2.symm
    (hxz' ▸ (s.tri' H).2.2.symm) (hxz ▸ (s.tri' H).1)
  exact left_right_disjoint H q (hyy ▸ s.hy'.2) s.hy.1



/-- A fiber is internal to a biclique when both sides meet it. -/
def Internal (p : Biclique H) (i : I) : Prop :=
  (∃ a ∈ Left H p, π a = i) ∧ ∃ b ∈ Right H p, π b = i

def TwoInternal : Prop :=
  ∀ p : Biclique H, ∀ i j k, Internal H π p i → Internal H π p j → Internal H π p k →
    i = j ∨ i = k ∨ j = k

/-- Remove side vertices whose fiber does not meet the opposite side. -/
def trim (p : Biclique H) : Biclique H :=
  ⟨({a | a ∈ Left H p ∧ ∃ b ∈ Right H p, π a = π b},
    {b | b ∈ Right H p ∧ ∃ a ∈ Left H p, π b = π a}),
    fun _ ha _ hb => p.property _ ha.1 _ hb.1⟩

include h in
def trim_six : Six H (trim H π p) (trim H π q) (trim H π r) := by
  have hf := fibers H π κ h s
  refine ⟨s.x,s.y,s.z,s.x',s.y',s.z',?_,?_,?_,?_,?_,?_⟩
  · exact ⟨⟨s.hx.1,s.z,s.hz.2,hf.1.2⟩,⟨s.hx.2,s.y,s.hy.1,hf.1.1⟩⟩
  · exact ⟨⟨s.hy.1,s.x,s.hx.2,hf.1.1.symm⟩,
      ⟨s.hy.2,s.z,s.hz.1,hf.1.1.symm.trans hf.1.2⟩⟩
  · exact ⟨⟨s.hz.1,s.y,s.hy.2,hf.1.2.symm.trans hf.1.1⟩,
      ⟨s.hz.2,s.x,s.hx.1,hf.1.2.symm⟩⟩
  · exact ⟨⟨s.hx'.1,s.y',s.hy'.2,hf.2.1⟩,⟨s.hx'.2,s.z',s.hz'.1,hf.2.2⟩⟩
  · exact ⟨⟨s.hy'.1,s.z',s.hz'.2,hf.2.1.symm.trans hf.2.2⟩,
      ⟨s.hy'.2,s.x',s.hx'.1,hf.2.1.symm⟩⟩
  · exact ⟨⟨s.hz'.1,s.x',s.hx'.2,hf.2.2.symm⟩,
      ⟨s.hz'.2,s.y',s.hy'.1,hf.2.2.symm.trans hf.2.1⟩⟩

lemma star_internal_unique (hp : Star H p) {i j : I}
    (hi : Internal H π p i) (hj : Internal H π p j) : i = j := by
  rcases hp with ⟨a,ha⟩ | ⟨b,hb⟩
  · obtain ⟨v,hv,hvi⟩ := hi.1
    obtain ⟨w,hw,hwj⟩ := hj.1
    have hva : v = a := by simpa only [ha,Set.mem_singleton_iff] using hv
    have hwa : w = a := by simpa only [ha,Set.mem_singleton_iff] using hw
    exact hvi.symm.trans ((congrArg π (hva.trans hwa.symm)).trans hwj)
  · obtain ⟨v,hv,hvi⟩ := hi.2
    obtain ⟨w,hw,hwj⟩ := hj.2
    have hvb : v = b := by simpa only [hb,Set.mem_singleton_iff] using hv
    have hwb : w = b := by simpa only [hb,Set.mem_singleton_iff] using hw
    exact hvi.symm.trans ((congrArg π (hvb.trans hwb.symm)).trans hwj)

lemma trim_internal {v : V} (hv : v ∈ Left H (trim H π p) ∨ v ∈ Right H (trim H π p)) :
    Internal H π p (π v) := by
  rcases hv with ⟨hv,w,hw,he⟩ | ⟨hv,w,hw,he⟩
  · exact ⟨⟨v,hv,rfl⟩,⟨w,hw,he.symm⟩⟩
  · exact ⟨⟨w,hw,he.symm⟩,⟨v,hv,rfl⟩⟩

include h in
lemma trim_support (h₂ : TwoInternal H π) {v : V}
    (hv : v ∈ Left H (trim H π p) ∨ v ∈ Right H (trim H π p)) :
    π v = π s.x ∨ π v = π s.x' := by
  classical
  have hf := fibers H π κ h s
  have hi : Internal H π p (π s.x) :=
    ⟨⟨s.z,s.hz.2,hf.1.2.symm⟩,⟨s.x,s.hx.1,rfl⟩⟩
  have hj : Internal H π p (π s.x') :=
    ⟨⟨s.x',s.hx'.2,rfl⟩,⟨s.z',s.hz'.1,hf.2.2.symm⟩⟩
  have hk := trim_internal H π hv
  by_cases he : π s.x = π s.x'
  · have hp : Star H p := by
      by_contra hn
      exact different_fibers H π κ h s hn he
    exact Or.inl (star_internal_unique H π hp hk hi)
  · rcases h₂ p _ _ _ hi hj hk with hn | hn | hn
    · exact (he hn).elim
    · exact Or.inl hn.symm
    · exact Or.inr hn.symm

def rotate : Six H q r p where
  x := s.y
  y := s.z
  z := s.x
  x' := s.y'
  y' := s.z'
  z' := s.x'
  hx := s.hy
  hy := s.hz
  hz := s.hx
  hx' := s.hy'
  hy' := s.hz'
  hz' := s.hx'

/-- The single-edge index graph, also valid when the two indices coincide. -/
def indexPair (i j : I) : SimpleGraph I where
  Adj a b := a ≠ b ∧ (a = i ∨ a = j) ∧ (b = i ∨ b = j)
  symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := fun _ h => h.1 rfl

lemma indexPair_triangleFree (i j : I) : (indexPair i j).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
  rcases hab.2.1 with rfl | rfl <;> rcases hab.2.2 with rfl | rfl <;>
    rcases hac.2.2 with rfl | rfl <;> first | exact hab.1 rfl | exact hac.1 rfl | exact hbc.1 rfl

def localGraph (i j : I) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ (π a = i ∨ π a = j) ∧ (π b = i ∨ π b = j)
  symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := fun _ h => H.loopless _ h.1

include h in
lemma local_assumptions (i j : I) :
    Erdos595MatchingBundle.Assumptions (localGraph H π i j) (indexPair i j) π κ :=
  ⟨h.injective,fun hab hn => ⟨hn,hab.2⟩,
    fun hab hac hn he => h.matching hab.1 hac.1 hn he,indexPair_triangleFree i j⟩

def supportedBiclique (p : Biclique H) (i j : I)
    (hp : ∀ v, v ∈ Left H p ∨ v ∈ Right H p → π v = i ∨ π v = j) :
    Biclique (localGraph H π i j) :=
  ⟨p.val,fun a ha b hb => ⟨p.property _ ha _ hb,hp a (Or.inl ha),hp b (Or.inr hb)⟩⟩

variable [LinearOrder I]

include h in
/-- Trimming yields a finite rainbow vertex label on the first right graph. -/
theorem trim_rainbow (h₂ : TwoInternal H π) {p q r : Biclique H}
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r) (hqr : (right H).Adj q r) :
    code H π κ (trim H π p) ≠ code H π κ (trim H π q) ∧
    code H π κ (trim H π p) ≠ code H π κ (trim H π r) ∧
    code H π κ (trim H π q) ≠ code H π κ (trim H π r) := by
  let s := six H hpq hpr hqr
  have hf := fibers H π κ h s
  have hs := trim_six H π κ h s
  have sp : ∀ v, v ∈ Left H (trim H π p) ∨ v ∈ Right H (trim H π p) →
      π v = π s.x ∨ π v = π s.x' := fun _ => trim_support H π κ h s h₂
  have sq : ∀ v, v ∈ Left H (trim H π q) ∨ v ∈ Right H (trim H π q) →
      π v = π s.x ∨ π v = π s.x' := by
    intro v hv
    have ht := trim_support H π κ h (rotate H s) h₂ hv
    simpa only [rotate,← hf.1.1,← hf.2.1] using ht
  have sr : ∀ v, v ∈ Left H (trim H π r) ∨ v ∈ Right H (trim H π r) →
      π v = π s.x ∨ π v = π s.x' := by
    intro v hv
    have ht := trim_support H π κ h (rotate H (rotate H s)) h₂ hv
    simpa only [rotate,← hf.1.2,← hf.2.2] using ht
  let P := supportedBiclique H π (trim H π p) (π s.x) (π s.x') sp
  let Q := supportedBiclique H π (trim H π q) (π s.x) (π s.x') sq
  let R := supportedBiclique H π (trim H π r) (π s.x) (π s.x') sr
  have hpq' : (right (localGraph H π (π s.x) (π s.x'))).Adj P Q :=
    ⟨⟨hs.x,hs.hx⟩,⟨hs.x',hs.hx'⟩⟩
  have hpr' : (right (localGraph H π (π s.x) (π s.x'))).Adj P R :=
    ⟨⟨hs.z',hs.hz'⟩,⟨hs.z,hs.hz⟩⟩
  have hqr' : (right (localGraph H π (π s.x) (π s.x'))).Adj Q R :=
    ⟨⟨hs.y,hs.hy⟩,⟨hs.y',hs.hy'⟩⟩
  exact right_rainbow (localGraph H π (π s.x) (π s.x')) (indexPair (π s.x) (π s.x'))
    π κ (local_assumptions H π κ h _ _) hpq' hpr' hqr'

include h in
/-- At most two internal fibers per biclique suffice; the index graph need not be TF. -/
theorem second_right_cover (h₂ : TwoInternal H π) :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (right H)) :=
  right_cover_of_rainbow (right H) (fun p => code H π κ (trim H π p))
    (fun _ _ _ => trim_rainbow H π κ h h₂)


section Concrete
variable (B : SimpleGraph I) (σ : I → I → (Fin 3 ≃ Fin 3))

lemma full_matching {a b c : I × Fin 3}
    (hab : (bundle B σ).Adj a b) (hac : (bundle B σ).Adj a c)
    (hne : a.1 ≠ b.1) (he : b.1 = c.1) : b = c := by
  rcases a with ⟨i,a⟩
  rcases b with ⟨j,b⟩
  rcases c with ⟨k,c⟩
  change j = k at he
  subst k
  change i ≠ j at hne
  apply congrArg (fun x => (j,x))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ((bundle_adj_lt B σ hlt).mp hab).2.symm.trans
      ((bundle_adj_lt B σ hlt).mp hac).2
  · exact (σ j i).injective (((bundle_adj_lt B σ hgt).mp hab.symm).2.trans
      ((bundle_adj_lt B σ hgt).mp hac.symm).2.symm)

private lemma third_exists : ∀ a b : Fin 3, a ≠ b → ∃ c, c ≠ a ∧ c ≠ b := by
  decide +kernel

private lemma third_unique : ∀ a b c d : Fin 3, a ≠ b → c ≠ a → c ≠ b →
    d ≠ a → d ≠ b → c = d := by decide +kernel

private lemma third_map (e : Fin 3 ≃ Fin 3) {a b c a' b' c' : Fin 3}
    (ha : e a = a') (hb : e b = b') (hab : a' ≠ b')
    (hca : c ≠ a) (hcb : c ≠ b) (hca' : c' ≠ a') (hcb' : c' ≠ b') : e c = c' := by
  apply third_unique a' b' (e c) c' hab _ _ hca' hcb'
  · exact fun he => hca (e.injective (he.trans ha.symm))
  · exact fun he => hcb (e.injective (he.trans hb.symm))

/-- In a full matching on two three-point fibers, the third matched pair
is forced by any two matched pairs. This fails for partial matchings. -/
lemma thirds_adj {i j : I} {a b c a' b' c' : Fin 3} (hij : i ≠ j)
    (ha : (bundle B σ).Adj (i,a) (j,a')) (hb : (bundle B σ).Adj (i,b) (j,b'))
    (hab : a ≠ b) (hab' : a' ≠ b') (hca : c ≠ a) (hcb : c ≠ b)
    (hca' : c' ≠ a') (hcb' : c' ≠ b') : (bundle B σ).Adj (i,c) (j,c') := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h₁ := (bundle_adj_lt B σ hlt).mp ha
    have h₂ := (bundle_adj_lt B σ hlt).mp hb
    exact (bundle_adj_lt B σ hlt).mpr
      ⟨h₁.1,third_map (σ i j) h₁.2 h₂.2 hab' hca hcb hca' hcb'⟩
  · have h₁ := (bundle_adj_lt B σ hgt).mp ha.symm
    have h₂ := (bundle_adj_lt B σ hgt).mp hb.symm
    exact ((bundle_adj_lt B σ hgt).mpr
      ⟨h₁.1,third_map (σ j i) h₁.2 h₂.2 hab hca' hcb' hca hcb⟩).symm

private lemma internal_coordinates (p : Biclique (bundle B σ)) (i : I)
    (hi : Internal (bundle B σ) Prod.fst p i) :
    (∃ a, (i,a) ∈ Left (bundle B σ) p) ∧ ∃ b, (i,b) ∈ Right (bundle B σ) p := by
  obtain ⟨⟨⟨j,a⟩,ha,hj⟩,⟨⟨k,b⟩,hb,hk⟩⟩ := hi
  change j = i at hj
  change k = i at hk
  subst j
  subst k
  exact ⟨⟨a,ha⟩,⟨b,hb⟩⟩

variable (htri : ∀ {a b c : I × Fin 3}, (bundle B σ).Adj a b →
  (bundle B σ).Adj a c → (bundle B σ).Adj b c → a.1 = b.1 ∧ a.1 = c.1)

include htri in
lemma full_core : Core (bundle B σ) Prod.fst Prod.snd :=
  ⟨fun _ _ he => he,full_matching B σ,htri⟩

include htri in
/-- Three internal fibers force a triangle of the three remaining vertices. -/
theorem full_twoInternal : TwoInternal (bundle B σ) Prod.fst := by
  intro p i j k hi hj hk
  by_cases hij : i = j
  · exact Or.inl hij
  by_cases hik : i = k
  · exact Or.inr (Or.inl hik)
  by_cases hjk : j = k
  · exact Or.inr (Or.inr hjk)
  obtain ⟨⟨a₀,ha₀⟩,⟨b₀,hb₀⟩⟩ := internal_coordinates B σ p i hi
  obtain ⟨⟨a₁,ha₁⟩,⟨b₁,hb₁⟩⟩ := internal_coordinates B σ p j hj
  obtain ⟨⟨a₂,ha₂⟩,⟨b₂,hb₂⟩⟩ := internal_coordinates B σ p k hk
  have hab₀ : a₀ ≠ b₀ := fun he => (p.property _ ha₀ _ hb₀).ne (congrArg (fun x => (i,x)) he)
  have hab₁ : a₁ ≠ b₁ := fun he => (p.property _ ha₁ _ hb₁).ne (congrArg (fun x => (j,x)) he)
  have hab₂ : a₂ ≠ b₂ := fun he => (p.property _ ha₂ _ hb₂).ne (congrArg (fun x => (k,x)) he)
  obtain ⟨c₀,hca₀,hcb₀⟩ := third_exists a₀ b₀ hab₀
  obtain ⟨c₁,hca₁,hcb₁⟩ := third_exists a₁ b₁ hab₁
  obtain ⟨c₂,hca₂,hcb₂⟩ := third_exists a₂ b₂ hab₂
  have h₀₁ : (bundle B σ).Adj (i,c₀) (j,c₁) :=
    thirds_adj B σ hij (p.property _ ha₀ _ hb₁) (p.property _ ha₁ _ hb₀).symm
      hab₀ hab₁.symm hca₀ hcb₀ hcb₁ hca₁
  have h₀₂ : (bundle B σ).Adj (i,c₀) (k,c₂) :=
    thirds_adj B σ hik (p.property _ ha₀ _ hb₂) (p.property _ ha₂ _ hb₀).symm
      hab₀ hab₂.symm hca₀ hcb₀ hcb₂ hca₂
  have h₁₂ : (bundle B σ).Adj (j,c₁) (k,c₂) :=
    thirds_adj B σ hjk (p.property _ ha₁ _ hb₂) (p.property _ ha₂ _ hb₁).symm
      hab₁ hab₂.symm hca₁ hcb₁ hcb₂ hca₂
  exact (hij (htri h₀₁ h₀₂ h₁₂).1).elim

include htri in
/-- The index graph may now have triangles. It is enough that the full
matching bundle has no triangles outside its designated fibers. -/
theorem full_matching_second_right_cover :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (right (bundle B σ))) :=
  second_right_cover (bundle B σ) Prod.fst Prod.snd (full_core B σ htri)
    (full_twoInternal B σ htri)
end Concrete

#print axioms trim_rainbow
#print axioms second_right_cover
#print axioms full_twoInternal
#print axioms full_matching_second_right_cover
end Erdos595FullMatchingBundle
