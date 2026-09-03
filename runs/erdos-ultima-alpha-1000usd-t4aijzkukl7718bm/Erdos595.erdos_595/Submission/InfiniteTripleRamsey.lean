import Submission.InfinitePairRamsey

/-!
An infinite-target ordered triple Ramsey theorem. Its predecessor tree
records all increasing pairs of earlier predecessors. This theorem places
no forbidden-clique restriction on the Ramsey host.
-/
set_option autoImplicit false
open Set
namespace Erdos595InfiniteTripleRamsey
universe u
variable {V C : Type u} [LinearOrder V] [WellFoundedLT V]
    (c : V → V → V → C)

noncomputable def pred : V → Set V :=
  wellFounded_lt.fix (fun v rec => {a | ∃ h : a < v,
    ∀ s ∈ rec a h, ∀ t ∈ rec a h, s < t → c s t a = c s t v})

lemma mem_pred {a v : V} : a ∈ pred c v ↔ a < v ∧
    ∀ s ∈ pred c a, ∀ t ∈ pred c a, s < t → c s t a = c s t v := by
  rw [pred,WellFounded.fix_eq]
  constructor <;> rintro ⟨h,hh⟩ <;> exact ⟨h,hh⟩

lemma pred_lt {a v : V} (h : a ∈ pred c v) : a < v := (mem_pred c).mp h |>.1
lemma pred_agree {a v s t : V} (h : a ∈ pred c v)
    (hs : s ∈ pred c a) (ht : t ∈ pred c a) (hst : s < t) :
    c s t a = c s t v := (mem_pred c).mp h |>.2 s hs t ht hst
lemma not_mem_pred (v : V) : v ∉ pred c v := fun h => lt_irrefl _ (pred_lt c h)

lemma pred_trans {v : V} : ∀ {a b : V}, a ∈ pred c v → b ∈ pred c a → b ∈ pred c v := by
  induction v using (wellFounded_lt (α := V)).induction with
  | h v ih =>
    intro a b hav hba
    refine (mem_pred c).mpr ⟨(pred_lt c hba).trans (pred_lt c hav),?_⟩
    intro s hs t ht hst
    exact (pred_agree c hba hs ht hst).trans
      (pred_agree c hav (ih a (pred_lt c hav) hba hs)
        (ih a (pred_lt c hav) hba ht) hst)

lemma separation {a v : V} (hav : a < v) (h : a ∉ pred c v) :
    ∃ t s, t ∈ pred c a ∧ t ∈ pred c v ∧ s ∈ pred c a ∧ s < t ∧
      c s t a ≠ c s t v := by
  classical
  have hex : ∃ t, t ∈ pred c a ∧ ∃ s ∈ pred c a, s < t ∧ c s t a ≠ c s t v := by
    by_contra hn
    push_neg at hn
    apply h ((mem_pred c).mpr ⟨hav,?_⟩)
    intro s hs t ht hst
    exact hn t ht s hs hst
  obtain ⟨t,⟨ht,s,hs,hst,hd⟩,hm⟩ := wellFounded_lt.has_min
    {t | t ∈ pred c a ∧ ∃ s ∈ pred c a, s < t ∧ c s t a ≠ c s t v} hex
  refine ⟨t,s,ht,?_,hs,hst,hd⟩
  refine (mem_pred c).mpr ⟨(pred_lt c ht).trans hav,?_⟩
  intro x hx y hy hxy
  have hxa : x ∈ pred c a := pred_trans c ht hx
  have hya : y ∈ pred c a := pred_trans c ht hy
  have he : c x y a = c x y v := by
    by_contra hn
    exact hm y ⟨hya,x,hxa,hxy,hn⟩ (pred_lt c hy)
  exact (pred_agree c ht hx hy hxy).trans he

lemma pred_chain {v : V} : ∀ {a b : V}, a ∈ pred c v → b ∈ pred c v →
    a < b → a ∈ pred c b := by
  induction v using (wellFounded_lt (α := V)).induction with
  | h v ih =>
    intro a b ha hb hab
    by_contra hn
    obtain ⟨t,s,hta,htb,hsa,hst,hd⟩ := separation c hab hn
    have hst' : s ∈ pred c t := ih a (pred_lt c ha) hsa hta hst
    have hsb : s ∈ pred c b := pred_trans c htb hst'
    exact hd ((pred_agree c ha hsa hta hst).trans
      (pred_agree c hb hsb htb hst).symm)

lemma vertex_eq_of_pred_eq {a b : V} (hp : pred c a = pred c b)
    (hc : ∀ s ∈ pred c a, ∀ t ∈ pred c a, s < t → c s t a = c s t b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · have ha : a ∈ pred c b := (mem_pred c).mpr ⟨h,hc⟩
    exact (not_mem_pred c a (hp ▸ ha)).elim
  · exact h
  · have hb : b ∈ pred c a := (mem_pred c).mpr ⟨h,fun s hs t ht hst =>
      (hc s (hp.symm ▸ hs) t (hp.symm ▸ ht) hst).symm⟩
    exact (not_mem_pred c b (hp.symm ▸ hb)).elim

lemma paths_rigid {v w : V} (f : pred c v → pred c w)
    (hsur : Function.Surjective f)
    (hord : ∀ a b, (f a).val < (f b).val ↔ a.val < b.val)
    (hcol : ∀ a b, c (f a).val (f b).val w = c a.val b.val v) :
    ∀ a, (f a).val = a.val := by
  have hmain : ∀ a (ha : a ∈ pred c v), (f ⟨a,ha⟩).val = a := by
    intro a
    induction a using (wellFounded_lt (α := V)).induction with
    | h a ih =>
      intro ha
      let b := f ⟨a,ha⟩
      have hp : pred c a = pred c b.val := by
        ext t
        constructor
        · intro ht
          have htv := pred_trans c ha ht
          have hft := ih t (pred_lt c ht) htv
          have hlt : (f ⟨t,htv⟩).val < b.val :=
            (hord ⟨t,htv⟩ ⟨a,ha⟩).mpr (pred_lt c ht)
          rw [hft] at hlt
          have htw : t ∈ pred c w := hft ▸ (f ⟨t,htv⟩).property
          exact pred_chain c htw b.property hlt
        · intro ht
          have htw := pred_trans c b.property ht
          obtain ⟨d,hd⟩ := hsur ⟨t,htw⟩
          have hlt : d.val < a := (hord d ⟨a,ha⟩).mp (by
            change (f d).val < b.val
            rw [hd]
            exact pred_lt c ht)
          have he := ih d.val hlt d.property
          have hdt : d.val = t := he.symm.trans (congrArg Subtype.val hd)
          have hda : d.val ∈ pred c a := pred_chain c d.property ha hlt
          exact hdt ▸ hda
      have hc : ∀ s ∈ pred c a, ∀ t ∈ pred c a, s < t →
          c s t a = c s t b.val := by
        intro s hs t ht hst
        have hsv := pred_trans c ha hs
        have htv := pred_trans c ha ht
        have hfs := ih s (pred_lt c hs) hsv
        have hft := ih t (pred_lt c ht) htv
        have he := hcol ⟨s,hsv⟩ ⟨t,htv⟩
        rw [hfs,hft] at he
        exact (pred_agree c ha hs ht hst).trans
          (he.symm.trans (pred_agree c b.property (hp ▸ hs) (hp ▸ ht) hst).symm)
      exact (vertex_eq_of_pred_eq c hp hc).symm
  exact fun a => hmain a.val a.property

abbrev TreeCode (T C : Type u) := Set T × Set (T × T) × Set (T × T × C)
variable {T : Type u}

noncomputable def treeCode (e : ∀ v, pred c v ↪ T) (v : V) : TreeCode T C :=
  (Set.range (e v),
    {ij | ∃ a b : pred c v, e v a = ij.1 ∧ e v b = ij.2 ∧ a.val < b.val},
    {ijk | ∃ a b : pred c v, e v a = ijk.1 ∧ e v b = ijk.2.1 ∧ c a.val b.val v = ijk.2.2})

lemma treeCode_order (e : ∀ v, pred c v ↪ T) (v : V) (a b : pred c v) :
    (e v a,e v b) ∈ (treeCode c e v).2.1 ↔ a.val < b.val := by
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩
    simpa only [(e v).injective hx,(e v).injective hy] using hxy
  · exact fun h => ⟨a,b,rfl,rfl,h⟩

lemma treeCode_color (e : ∀ v, pred c v ↪ T) (v : V) (a b : pred c v) (k : C) :
    (e v a,e v b,k) ∈ (treeCode c e v).2.2 ↔ c a.val b.val v = k := by
  constructor
  · rintro ⟨x,y,hx,hy,hc⟩
    simpa only [(e v).injective hx,(e v).injective hy] using hc
  · exact fun h => ⟨a,b,rfl,rfl,h⟩

theorem treeCode_injective (e : ∀ v, pred c v ↪ T) :
    Function.Injective (treeCode c e) := by
  classical
  intro v w he
  have hset : (treeCode c e v).1 = (treeCode c e w).1 := congrArg Prod.fst he
  have hrel : (treeCode c e v).2.1 = (treeCode c e w).2.1 :=
    congrArg (fun z => z.2.1) he
  have hcol : (treeCode c e v).2.2 = (treeCode c e w).2.2 :=
    congrArg (fun z => z.2.2) he
  have hex : ∀ a : pred c v, ∃ b : pred c w, e w b = e v a := by
    intro a
    have ha : e v a ∈ (treeCode c e v).1 := ⟨a,rfl⟩
    rw [hset] at ha
    exact ha
  choose f hf using hex
  have hsur : Function.Surjective f := by
    intro b
    have hb : e w b ∈ (treeCode c e w).1 := ⟨b,rfl⟩
    rw [← hset] at hb
    obtain ⟨a,ha⟩ := hb
    exact ⟨a,(e w).injective ((hf a).trans ha)⟩
  have hord : ∀ a b, (f a).val < (f b).val ↔ a.val < b.val := by
    intro a b
    rw [← treeCode_order c e w (f a) (f b),hf a,hf b,← hrel]
    exact treeCode_order c e v a b
  have hc : ∀ a b, c (f a).val (f b).val w = c a.val b.val v := by
    intro a b
    apply (treeCode_color c e w (f a) (f b) _).mp
    rw [hf a,hf b,← hcol]
    exact (treeCode_color c e v a b _).mpr rfl
  have hid := paths_rigid c f hsur hord hc
  have hp : pred c v = pred c w := by
    ext a
    constructor
    · intro ha
      have hh : (f ⟨a,ha⟩).val = a := hid ⟨a,ha⟩
      exact hh ▸ (f ⟨a,ha⟩).property
    · intro ha
      obtain ⟨b,hb⟩ := hsur ⟨a,ha⟩
      have hh : b.val = a := (hid b).symm.trans (congrArg Subtype.val hb)
      exact hh ▸ b.property
  apply vertex_eq_of_pred_eq c hp
  intro a ha b hb _
  have hh := hc ⟨a,ha⟩ ⟨b,hb⟩
  rw [hid ⟨a,ha⟩,hid ⟨b,hb⟩] at hh
  exact hh.symm

theorem exists_long_branch {A : Type u} [LinearOrder A] [WellFoundedLT A]
    (hV : ¬Nonempty (V ↪ TreeCode A C)) :
    ∃ v, Nonempty (A ↪o pred c v) := by
  classical
  by_contra hn
  have he : ∀ v, Nonempty (pred c v ↪ A) := by
    intro v
    rcases InitialSeg.total (fun x y : A => x < y)
      (fun x y : pred c v => x < y) with f | f
    · apply False.elim
      apply hn
      exact ⟨v,⟨OrderEmbedding.ofStrictMono f (fun _ _ h => f.map_rel_iff.mpr h)⟩⟩
    · exact ⟨f.toRelEmbedding.toEmbedding⟩
  let e := fun v => (he v).some
  exact hV ⟨⟨treeCode c e,treeCode_injective c e⟩⟩

theorem end_homogeneous_of_noninjection (A C V : Type u)
    [LinearOrder A] [WellFoundedLT A] (hV : ¬Nonempty (V ↪ TreeCode A C)) :
    ∃ (_ : LinearOrder V) (_ : WellFoundedLT V),
      ∀ c : V → V → V → C, ∃ (f : A ↪o V) (d : A → A → C),
        ∀ a b t, a < b → b < t → c (f a) (f b) (f t) = d a b := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  letI : WellFoundedLT V := ⟨(inferInstance : IsWellOrder V WellOrderingRel).wf⟩
  refine ⟨inferInstance,inferInstance,?_⟩
  intro c
  obtain ⟨v,⟨f⟩⟩ := exists_long_branch c hV
  let g : A ↪o V := OrderEmbedding.ofStrictMono (fun a => (f a).val)
    (fun _ _ h => f.strictMono h)
  refine ⟨g,fun a b => c (g a) (g b) v,?_⟩
  intro a b t hab hbt
  exact pred_agree c (f t).property
    (pred_chain c (f a).property (f t).property (f.strictMono (hab.trans hbt)))
    (pred_chain c (f b).property (f t).property (f.strictMono hbt)) (f.strictMono hab)

theorem end_homogeneous_host (A C : Type u) [LinearOrder A] [WellFoundedLT A] :
    ∃ (V : Type u) (_ : LinearOrder V) (_ : WellFoundedLT V),
      ∀ c : V → V → V → C, ∃ (f : A ↪o V) (d : A → A → C),
        ∀ a b t, a < b → b < t → c (f a) (f b) (f t) = d a b := by
  obtain ⟨o,w,h⟩ := end_homogeneous_of_noninjection A C (Set (TreeCode A C)) (by
    rintro ⟨e⟩
    exact Function.cantor_injective e e.injective)
  exact ⟨_,o,w,h⟩

/-- The target can have any well-ordered cardinality, not merely finite size. -/
theorem triple_ramsey_host (A C : Type u) [LinearOrder A] [WellFoundedLT A] :
    ∃ (V : Type u) (_ : LinearOrder V) (_ : WellFoundedLT V),
      ∀ c : V → V → V → C, ∃ (f : A ↪o V) (k : C),
        ∀ a b t, a < b → b < t → c (f a) (f b) (f t) = k := by
  obtain ⟨X,oX,wX,hX⟩ := Erdos595InfinitePairRamsey.pair_ramsey_host A C
  letI : LinearOrder X := oX
  letI : WellFoundedLT X := wX
  obtain ⟨V,oV,wV,hV⟩ := end_homogeneous_host X C
  letI : LinearOrder V := oV
  letI : WellFoundedLT V := wV
  refine ⟨V,oV,wV,?_⟩
  intro c
  obtain ⟨f,d,hd⟩ := hV c
  obtain ⟨e,k,he⟩ := hX d
  exact ⟨e.trans f,k,fun a b t hab hbt =>
    (hd _ _ _ (e.strictMono hab) (e.strictMono hbt)).trans (he _ _ hab)⟩

#print axioms pred_chain
#print axioms treeCode_injective
#print axioms triple_ramsey_host
end Erdos595InfiniteTripleRamsey
