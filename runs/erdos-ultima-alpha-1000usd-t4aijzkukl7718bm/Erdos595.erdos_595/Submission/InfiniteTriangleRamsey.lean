import Submission.Work

/-!
An Erdős--Rado tree for edge colorings of a complete graph with no
monochromatic triangle. Colors are injective along each branch, and the
colored order type of a branch determines its vertex. This supplies an
infinite-palette Ramsey tool; it is not a K4-free construction.
-/

open Set SimpleGraph
namespace Erdos595InfiniteTriangleRamsey

variable {V C : Type*} [LinearOrder V] [WellFoundedLT V]
variable (c : V → V → C)

/-- The canonical predecessor tree, built in the ambient well order. -/
noncomputable def pred : V → Set V :=
  wellFounded_lt.fix (fun v rec => {u | ∃ h : u < v,
    ∀ w ∈ rec u h, c w u = c w v})

lemma mem_pred {u v : V} : u ∈ pred c v ↔
    u < v ∧ ∀ w ∈ pred c u, c w u = c w v := by
  rw [pred,WellFounded.fix_eq]
  constructor <;> rintro ⟨h,hh⟩ <;> exact ⟨h,hh⟩

lemma pred_lt {u v : V} (h : u ∈ pred c v) : u < v := (mem_pred c).mp h |>.1
lemma pred_agree {u v : V} (h : u ∈ pred c v) {w : V} (hw : w ∈ pred c u) :
    c w u = c w v := (mem_pred c).mp h |>.2 w hw
lemma not_mem_pred (v : V) : v ∉ pred c v := fun h => lt_irrefl _ (pred_lt c h)

lemma pred_trans {v : V} : ∀ {u w : V}, u ∈ pred c v → w ∈ pred c u → w ∈ pred c v := by
  induction v using (wellFounded_lt (α := V)).induction with
  | h v ih =>
    intro u w huv hwu
    refine (mem_pred c).mpr ⟨(pred_lt c hwu).trans (pred_lt c huv),?_⟩
    intro t ht
    exact (pred_agree c hwu ht).trans
      (pred_agree c huv (ih u (pred_lt c huv) hwu ht))

/-- If an earlier vertex is not an ancestor, the first disagreement is a
common ancestor of the two vertices. -/
lemma separation {u v : V} (huv : u < v) (h : u ∉ pred c v) :
    ∃ w, w ∈ pred c u ∧ w ∈ pred c v ∧ c w u ≠ c w v := by
  classical
  have hex : ∃ w ∈ pred c u, c w u ≠ c w v := by
    by_contra hn
    push_neg at hn
    exact h ((mem_pred c).mpr ⟨huv,hn⟩)
  obtain ⟨w,⟨hw,hd⟩,hm⟩ := wellFounded_lt.has_min
    {w | w ∈ pred c u ∧ c w u ≠ c w v} hex
  refine ⟨w,hw,?_,hd⟩
  refine (mem_pred c).mpr ⟨(pred_lt c hw).trans huv,?_⟩
  intro t ht
  have htu : t ∈ pred c u := pred_trans c hw ht
  have he : c t u = c t v := by
    by_contra hn
    exact hm t ⟨htu,hn⟩ (pred_lt c ht)
  exact (pred_agree c hw ht).trans he

lemma pred_chain {u w v : V} (hu : u ∈ pred c v) (hw : w ∈ pred c v)
    (huw : u < w) : u ∈ pred c w := by
  by_contra hn
  obtain ⟨t,htu,htw,hd⟩ := separation c huw hn
  exact hd ((pred_agree c hu htu).trans (pred_agree c hw htw).symm)

lemma pred_initial {u v w : V} (hu : u ∈ pred c v) :
    w ∈ pred c u ↔ w ∈ pred c v ∧ w < u :=
  ⟨fun h => ⟨pred_trans c hu h,pred_lt c h⟩,
    fun h => pred_chain c h.1 hu h.2⟩

/-- Two vertices cannot have the same predecessor set with identical
edge colors from all those predecessors. -/
lemma vertex_eq_of_pred_eq {u v : V} (hp : pred c u = pred c v)
    (hc : ∀ w ∈ pred c u, c w u = c w v) : u = v := by
  rcases lt_trichotomy u v with h | h | h
  · have hu : u ∈ pred c v := (mem_pred c).mpr ⟨h,hc⟩
    exact (not_mem_pred c u (hp ▸ hu)).elim
  · exact h
  · have hv : v ∈ pred c u := (mem_pred c).mpr ⟨h,fun w hw =>
      (hc w (hp.symm ▸ hw)).symm⟩
    exact (not_mem_pred c v (hp.symm ▸ hv)).elim

/-- No monochromatic triangle in increasing order. -/
def Valid : Prop := ∀ a b d, a < b → b < d →
  ¬(c a b = c a d ∧ c a b = c b d)

lemma colors_injective (hc : Valid c) (v : V) :
    Function.Injective (fun u : pred c v => c u.val v) := by
  intro a b he
  apply Subtype.ext
  rcases lt_trichotomy a.val b.val with hab | hab | hab
  · have hp := pred_chain c a.property b.property hab
    have hh := pred_agree c b.property hp
    exact (hc a b v hab (pred_lt c b.property) ⟨hh,hh.trans he⟩).elim
  · exact hab
  · have hp := pred_chain c b.property a.property hab
    have hh := pred_agree c a.property hp
    exact (hc b a v hab (pred_lt c a.property) ⟨hh,hh.trans he.symm⟩).elim

/-- A color-preserving order isomorphism between branches is pointwise the
identity. This is the rigidity needed to encode vertices by colored paths. -/
lemma paths_rigid {v w : V} (f : pred c v → pred c w)
    (hsur : Function.Surjective f)
    (hord : ∀ a b, (f a).val < (f b).val ↔ a.val < b.val)
    (hcol : ∀ a, c (f a).val w = c a.val v) :
    ∀ a, (f a).val = a.val := by
  have hmain : ∀ u (hu : u ∈ pred c v), (f ⟨u,hu⟩).val = u := by
    intro u
    induction u using (wellFounded_lt (α := V)).induction with
    | h u ih =>
      intro hu
      let a : pred c v := ⟨u,hu⟩
      let b := f a
      have hp : pred c u = pred c b.val := by
        ext t
        constructor
        · intro ht
          have htv := pred_trans c hu ht
          have hft := ih t (pred_lt c ht) htv
          have hlt : (f ⟨t,htv⟩).val < b.val :=
            (hord ⟨t,htv⟩ a).mpr (pred_lt c ht)
          rw [hft] at hlt
          have htw : t ∈ pred c w := hft ▸ (f ⟨t,htv⟩).property
          exact pred_chain c htw b.property hlt
        · intro ht
          have htw := pred_trans c b.property ht
          obtain ⟨d,hd⟩ := hsur ⟨t,htw⟩
          have hlt : d.val < u := (hord d a).mp (by
            change (f d).val < b.val
            rw [hd]
            exact pred_lt c ht)
          have he := ih d.val hlt d.property
          have hdt : d.val = t := he.symm.trans (congrArg Subtype.val hd)
          have hdu : d.val ∈ pred c u := pred_chain c d.property hu hlt
          exact hdt ▸ hdu
      have hcolor : ∀ t ∈ pred c u, c t u = c t b.val := by
        intro t ht
        have htv := pred_trans c hu ht
        have hft := ih t (pred_lt c ht) htv
        have htB : t ∈ pred c b.val := hp ▸ ht
        have he := hcol ⟨t,htv⟩
        rw [hft] at he
        exact (pred_agree c hu ht).trans
          (he.symm.trans (pred_agree c b.property htB).symm)
      exact (vertex_eq_of_pred_eq c hp hcolor).symm
  exact fun a => hmain a.val a.property

abbrev Code (C : Type*) := Set C × Set (C × C)

noncomputable def code (v : V) : Code C :=
  (Set.range (fun a : pred c v => c a.val v),
    {ij | ∃ a b : pred c v, c a.val v = ij.1 ∧ c b.val v = ij.2 ∧ a.val < b.val})

lemma code_order (hc : Valid c) (v : V) (a b : pred c v) :
    (c a.val v,c b.val v) ∈ (code c v).2 ↔ a.val < b.val := by
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩
    have hxa := colors_injective c hc v hx
    have hyb := colors_injective c hc v hy
    simpa only [hxa,hyb] using hxy
  · exact fun h => ⟨a,b,rfl,rfl,h⟩

/-- The colored predecessor order completely determines the vertex. -/
theorem code_injective (hc : Valid c) : Function.Injective (code c) := by
  classical
  intro v w he
  have hset : (code c v).1 = (code c w).1 := congrArg Prod.fst he
  have hrel : (code c v).2 = (code c w).2 := congrArg Prod.snd he
  have hex : ∀ a : pred c v, ∃ b : pred c w, c b.val w = c a.val v := by
    intro a
    have ha : c a.val v ∈ (code c v).1 := ⟨a,rfl⟩
    rw [hset] at ha
    exact ha
  choose f hf using hex
  have hsur : Function.Surjective f := by
    intro b
    have hb : c b.val w ∈ (code c w).1 := ⟨b,rfl⟩
    rw [← hset] at hb
    obtain ⟨a,ha⟩ := hb
    refine ⟨a,colors_injective c hc w ?_⟩
    exact (hf a).trans ha
  have hord : ∀ a b, (f a).val < (f b).val ↔ a.val < b.val := by
    intro a b
    rw [← code_order c hc w (f a) (f b),hf a,hf b,← hrel]
    exact code_order c hc v a b
  have hid := paths_rigid c f hsur hord hf
  have hp : pred c v = pred c w := by
    ext u
    constructor
    · intro hu
      have hh : (f ⟨u,hu⟩).val = u := hid ⟨u,hu⟩
      exact hh ▸ (f ⟨u,hu⟩).property
    · intro hu
      obtain ⟨a,ha⟩ := hsur ⟨u,hu⟩
      have heq : a.val = u := (hid a).symm.trans (congrArg Subtype.val ha)
      exact heq ▸ a.property
  apply vertex_eq_of_pred_eq c hp
  intro u hu
  have hh := hf ⟨u,hu⟩
  rw [hid ⟨u,hu⟩] at hh
  exact hh.symm

#print axioms pred_trans
#print axioms paths_rigid
#print axioms code_injective
end Erdos595InfiniteTriangleRamsey


namespace Erdos595InfiniteTriangleRamsey

variable {C : Type*}

private def pack (p : Code C) : Set (C ⊕ C × C) :=
  {x | match x with | .inl a => a ∈ p.1 | .inr ab => ab ∈ p.2}

private lemma pack_injective : Function.Injective (pack (C := C)) := by
  intro p q he
  apply Prod.ext
  · ext a
    exact Set.ext_iff.mp he (.inl a)
  · ext ab
    exact Set.ext_iff.mp he (.inr ab)

/-- A branch code over a countable alphabet can be encoded by a binary sequence. -/
theorem binary_encoding_code [Countable C] :
    ∃ f : Code C → ℕ → Fin 2, Function.Injective f := by
  classical
  obtain ⟨enc,henc⟩ := exists_injective_nat (C ⊕ C × C)
  let f : Code C → ℕ → Fin 2 := fun p n => if n ∈ enc '' pack p then 1 else 0
  refine ⟨f,?_⟩
  intro p q he
  apply pack_injective
  apply Set.image_injective.mpr henc
  ext n
  have hn := congrFun he n
  constructor
  · intro hp
    by_contra hq
    simp only [f,if_pos hp,if_neg hq] at hn
    exact (by decide : (1 : Fin 2) ≠ 0) hn
  · intro hq
    by_contra hp
    simp only [f,if_neg hp,if_pos hq] at hn
    exact (by decide : (0 : Fin 2) ≠ 1) hn

/-- The unrestricted palette bound, before encoding countable colors. -/
theorem complete_no_mono_code {V : Type*} (c : Sym2 V → C)
    (hc : ∀ a b d, a ≠ b → a ≠ d → b ≠ d →
      ¬(c s(a,b) = c s(a,d) ∧ c s(a,b) = c s(b,d))) :
    ∃ f : V → Code C, Function.Injective f := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  letI : WellFoundedLT V := ⟨(inferInstance : IsWellOrder V WellOrderingRel).wf⟩
  let d : V → V → C := fun a b => c s(a,b)
  have hd : Valid d := fun a b t hab hbt => hc a b t hab.ne (hab.trans hbt).ne hbt.ne
  exact ⟨code d,code_injective d hd⟩

/-- Sharp cardinal upper bound in encoding form: a complete graph with a
countable edge palette and no monochromatic triangle has at most continuum
many vertices. No measurability or definability assumption on the coloring. -/
theorem complete_no_mono_binary {V : Type*} [Countable C]
    (c : Sym2 V → C)
    (hc : ∀ a b d, a ≠ b → a ≠ d → b ≠ d →
      ¬(c s(a,b) = c s(a,d) ∧ c s(a,b) = c s(b,d))) :
    ∃ f : V → ℕ → Fin 2, Function.Injective f := by
  obtain ⟨f,hf⟩ := complete_no_mono_code c hc
  obtain ⟨enc,henc⟩ := binary_encoding_code (C := C)
  exact ⟨enc ∘ f,henc.comp hf⟩

/-- Exact covering criterion for complete graphs, stated without cardinal
universe lifts. In particular, the continuum bound cannot be improved. -/
theorem complete_cover_iff_binary {V : Type*} :
    Erdos595Work.IsCountableUnionOfTriangleFree (⊤ : SimpleGraph V) ↔
      ∃ f : V → ℕ → Fin 2, Function.Injective f := by
  constructor
  · intro h
    obtain ⟨c,hc⟩ := (Erdos595Work.countable_union_iff_edge_coloring _).mp h
    exact complete_no_mono_binary c hc
  · rintro ⟨f,hf⟩
    exact Erdos595Work.countable_union_of_binary_encoding _ f hf

/-- A triangle Ramsey graph for ANY prescribed palette, using Cantor's
explicit power-set enlargement. This graph is complete, not K4-free. -/
theorem arbitrary_palette_triangle_ramsey (C : Type*) :
    ∀ c : Sym2 (Set (Code C)) → C, ∃ a b d,
      a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c s(a,b) = c s(a,d) ∧ c s(a,b) = c s(b,d) := by
  classical
  intro c
  by_contra hn
  have hc : ∀ a b d, a ≠ b → a ≠ d → b ≠ d →
      ¬(c s(a,b) = c s(a,d) ∧ c s(a,b) = c s(b,d)) := by
    intro a b d hab had hbd he
    exact hn ⟨a,b,d,hab,had,hbd,he⟩
  obtain ⟨f,hf⟩ := complete_no_mono_code c hc
  exact Function.cantor_injective f hf

/-- The complete graph on the power set of the binary sequences does not
admit a countable triangle-free edge cover. It contains K4, so is not a
witness for the original conjecture. -/
theorem large_complete_no_cover :
    ¬Erdos595Work.IsCountableUnionOfTriangleFree
      (⊤ : SimpleGraph (Set (ℕ → Fin 2))) := by
  intro h
  obtain ⟨f,hf⟩ := complete_cover_iff_binary.mp h
  exact Function.cantor_injective f hf

#print axioms binary_encoding_code
#print axioms complete_no_mono_binary
#print axioms complete_cover_iff_binary
#print axioms arbitrary_palette_triangle_ramsey
#print axioms large_complete_no_cover
end Erdos595InfiniteTriangleRamsey
