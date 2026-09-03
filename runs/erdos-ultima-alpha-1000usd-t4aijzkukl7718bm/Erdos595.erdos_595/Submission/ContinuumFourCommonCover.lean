import Submission.FourCycleCommonCover

/-! A continuum-bound strengthening of the four-cycle common-neighborhood criterion.
This is an auxiliary result, not a settlement of the original conjecture. -/
set_option autoImplicit false
open Set SimpleGraph Cardinal FirstOrder
open scoped Classical
namespace Erdos595ContinuumFourCommon
open Erdos595Work Erdos595RankEdgeCover
open Erdos595FourCycleCommon

private def fouraryLanguage : Language where
  Functions n := {_k : Set ℕ // n = 4}
  Relations _ := Empty

private lemma language_card : #(Σ n, fouraryLanguage.Functions n) ≤ continuum := by
  have h : Function.Injective (fun x : Σ n, fouraryLanguage.Functions n => x.2.val) := by
    rintro ⟨n,k,hn⟩ ⟨m,l,hm⟩ he
    change n = 4 at hn
    change m = 4 at hm
    subst n; subst m
    cases he
    rfl
  exact (Cardinal.mk_le_of_injective h).trans_eq (by simp only [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0])

private def fouraryStructure {V : Type} (f : Set ℕ → V → V → V → V → V) : fouraryLanguage.Structure V where
  funMap := fun {n} s x => by
    obtain ⟨k,rfl⟩ := s
    exact f k (x 0) (x 1) (x 2) (x 3)
  RelMap := fun r => Empty.elim r

section Closure
variable {V : Type} (f : Set ℕ → V → V → V → V → V)

private abbrev cl (S : Set V) : @fouraryLanguage.Substructure V (fouraryStructure f) :=
  @Language.Substructure.closure fouraryLanguage V (fouraryStructure f) S

private lemma cl_subset (S : Set V) : S ⊆ cl f S := by
  letI := fouraryStructure f
  exact Language.Substructure.subset_closure

private lemma cl_mono {S T : Set V} (h : S ⊆ T) : cl f S ≤ cl f T := by
  letI := fouraryStructure f
  exact Language.Substructure.closure_mono h

private lemma cl_fun {S : Set V} (k : Set ℕ) {a b c d : V}
    (ha : a ∈ cl f S) (hb : b ∈ cl f S) (hc : c ∈ cl f S) (hd : d ∈ cl f S) :
    f k a b c d ∈ cl f S := by
  letI := fouraryStructure f
  have h := (cl f S).fun_mem (⟨k,rfl⟩ : fouraryLanguage.Functions 4)
    ![a,b,c,d] (by intro i; fin_cases i <;> assumption)
  exact h

private lemma cl_card (S : Set V) : #(cl f S) ≤ max continuum #S := by
  letI := fouraryStructure f
  have h := Language.Substructure.lift_card_closure_le (L := fouraryLanguage) (s := S)
  simp only [Cardinal.lift_id] at h
  exact h.trans (max_le (aleph0_le_continuum.trans (le_max_left _ _)) (by
    calc
      #S + #(Σ n, fouraryLanguage.Functions n)
        ≤ max continuum #S + max continuum #S :=
          add_le_add (le_max_right _ _) (language_card.trans (le_max_left _ _))
      _ = max continuum #S := Cardinal.add_eq_self
        (aleph0_le_continuum.trans (le_max_left _ _))))

private lemma cl_Iio [LinearOrder V] (a : V) {v : V} (hv : v ∈ cl f (Iio a)) :
    ∃ b < a, v ∈ cl f (Iic b) := by
  letI := fouraryStructure f
  refine Language.Substructure.closure_induction (p := fun v => ∃ b < a, v ∈ cl f (Iic b)) hv ?_ ?_
  · intro x hx
    exact ⟨x,hx,cl_subset f _ (le_refl x)⟩
  · intro n s x ih
    obtain ⟨k,rfl⟩ := s
    obtain ⟨b,hb,hxb⟩ := ih 0
    obtain ⟨c,hc,hxc⟩ := ih 1
    obtain ⟨d,hd,hxd⟩ := ih 2
    obtain ⟨e,he,hxe⟩ := ih 3
    refine ⟨max (max b c) (max d e),max_lt (max_lt hb hc) (max_lt hd he),?_⟩
    apply cl_fun f k
    · exact cl_mono f (Iic_subset_Iic.mpr ((le_max_left b c).trans (le_max_left _ _))) hxb
    · exact cl_mono f (Iic_subset_Iic.mpr ((le_max_right b c).trans (le_max_left _ _))) hxc
    · exact cl_mono f (Iic_subset_Iic.mpr ((le_max_left d e).trans (le_max_right _ _))) hxd
    · exact cl_mono f (Iic_subset_Iic.mpr ((le_max_right d e).trans (le_max_right _ _))) hxe


section Ranks
variable [LinearOrder V] [WellFoundedLT V]

private noncomputable def rank (v : V) : V :=
  wellFounded_lt.min {a | v ∈ cl f (Iic a)} ⟨v,cl_subset f _ (le_refl v)⟩

private lemma rank_mem (v : V) : v ∈ cl f (Iic (rank f v)) :=
  wellFounded_lt.min_mem {a | v ∈ cl f (Iic a)} ⟨v,cl_subset f _ (le_refl v)⟩

private lemma rank_not_mem (v : V) : v ∉ cl f (Iio (rank f v)) := by
  intro hv
  obtain ⟨b,hb,hbv⟩ := cl_Iio f (rank f v) hv
  exact wellFounded_lt.not_lt_min {a | v ∈ cl f (Iic a)}
    ⟨v,cl_subset f _ (le_refl v)⟩ hbv hb

private lemma rank_lt_mem {v a : V} (h : rank f v < a) : v ∈ cl f (Iio a) :=
  cl_mono f (Iic_subset_Iio.mpr h) (rank_mem f v)

end Ranks
end Closure

section Graphs
variable {V : Type} (G : SimpleGraph V)

def ContinuumFourCommon : Prop :=
  ∀ a b c d, Cycle4 G a b c d → #(common4 G a b c d) ≤ continuum

variable (hG : ContinuumFourCommon G)

private noncomputable def code (a b c d : V) (h : Cycle4 G a b c d) :
    common4 G a b c d ↪ Set ℕ :=
  (Cardinal.lift_mk_le'.mp (by
    simpa only [Cardinal.lift_uzero,Cardinal.mk_set_nat] using hG a b c d h)).some

private noncomputable def enumeration (k : Set ℕ) (a b c d : V) : V :=
  if h : Cycle4 G a b c d then
    if hv : ∃ v : common4 G a b c d, code G hG a b c d h v = k then hv.choose.val else a
  else a

private lemma common_mem_cl {S : Set V} {a b c d v : V} (hcycle : Cycle4 G a b c d)
    (ha : a ∈ cl (enumeration G hG) S) (hb : b ∈ cl (enumeration G hG) S)
    (hc : c ∈ cl (enumeration G hG) S) (hd : d ∈ cl (enumeration G hG) S)
    (hv : v ∈ common4 G a b c d) : v ∈ cl (enumeration G hG) S := by
  let k := code G hG a b c d hcycle ⟨v,hv⟩
  have hk : ∃ w : common4 G a b c d, code G hG a b c d hcycle w = k := ⟨⟨v,hv⟩,rfl⟩
  have he : enumeration G hG k a b c d = v := by
    rw [enumeration,dif_pos hcycle,dif_pos hk]
    exact congrArg Subtype.val ((code G hG a b c d hcycle).injective hk.choose_spec)
  rw [← he]
  exact cl_fun _ k ha hb hc hd

include hG in
private lemma cover_small_initials [LinearOrder V] [WellFoundedLT V]
    (κ : Cardinal) (hκ : continuum < κ) (hi : ∀ a : V, #(Iic a) < κ)
    (ih : ∀ S : Set V, #S < κ → IsCountableUnionOfTriangleFree (G.induce S)) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let f := enumeration G hG
  apply cover_of_rank G (rank f)
  · intro v
    apply Erdos595CountableCodegree.coloring_nat_of_countable_common_neighbors
    intro a c hac
    apply Set.Subsingleton.countable
    intro b hb d hd
    by_contra hbd
    have ha' : (a : V) ≠ c := fun he => hac (Subtype.ext he)
    have hb' : (b : V) ≠ d := fun he => hbd (Subtype.ext he)
    apply rank_not_mem f v
    apply common_mem_cl G hG (a := a) (b := b) (c := c) (d := d)
    · exact ⟨ha',hb',hb.1,hb.2.symm,hd.2,hd.1.symm⟩
    · exact rank_lt_mem f a.property.2
    · exact rank_lt_mem f b.property.2
    · exact rank_lt_mem f c.property.2
    · exact rank_lt_mem f d.property.2
    · exact ⟨a.property.1.symm,b.property.1.symm,c.property.1.symm,d.property.1.symm⟩
  · intro a
    apply ih
    have hs : {v | rank f v = a} ⊆ (cl f (Iic a) : Set V) := by
      intro v hv
      change rank f v = a at hv
      rw [← hv]
      exact rank_mem f v
    exact (Cardinal.mk_le_mk_of_subset hs).trans_lt
      ((cl_card f (Iic a)).trans_lt (max_lt hκ (hi a)))

lemma ContinuumFourCommon.comap {W : Type} {G : SimpleGraph V}
    (hG : ContinuumFourCommon G) (e : W → V) (he : Function.Injective e) :
    ContinuumFourCommon (G.comap e) := by
  intro a b c d h
  have h' : Cycle4 G (e a) (e b) (e c) (e d) :=
    ⟨he.ne h.1,he.ne h.2.1,h.2.2⟩
  let f : common4 (G.comap e) a b c d ↪ common4 G (e a) (e b) (e c) (e d) :=
    ⟨fun v => ⟨e v,v.property⟩,fun x y hxy => Subtype.ext (he (congrArg Subtype.val hxy))⟩
  exact (Cardinal.mk_le_of_injective f.injective).trans (hG _ _ _ _ h')

end Graphs

private theorem cardinal_cover (κ : Cardinal) :
    ∀ (V : Type) (G : SimpleGraph V), #V = κ →
      ContinuumFourCommon G → IsCountableUnionOfTriangleFree G := by
  classical
  induction κ using Cardinal.lt_wf.induction with
  | h κ ih =>
    intro V G hcard hG
    by_cases hκ : κ ≤ continuum
    · have he : Nonempty (V ↪ (ℕ → Fin 2)) := Cardinal.lift_mk_le'.mp (by
        simpa only [Cardinal.mk_arrow,Cardinal.mk_fin,Cardinal.mk_nat,
          Cardinal.lift_uzero,Nat.cast_ofNat,Cardinal.two_power_aleph0] using hcard.le.trans hκ)
      obtain ⟨e⟩ := he
      exact countable_union_of_binary_encoding G e e.injective
    · have hκ' : continuum < κ := lt_of_not_ge hκ
      let I := κ.ord.ToType
      let e : V ≃ I := (Cardinal.eq.mp (hcard.trans (Cardinal.mk_ord_toType κ).symm)).some
      let H : SimpleGraph I := G.comap e.symm
      have hH : ContinuumFourCommon H := hG.comap e.symm e.symm.injective
      have hI : ∀ a : I, #(Iic a) < κ := by
        intro a
        have hs : Iic a = insert a (Iio a) := by ext x; simp [le_iff_lt_or_eq,eq_comm]
        rw [hs]
        exact Cardinal.mk_insert_le.trans_lt (Cardinal.add_lt_of_lt (aleph0_le_continuum.trans hκ'.le)
          (Cardinal.mk_Iio_ord_toType a) (Cardinal.one_lt_aleph0.trans_le (aleph0_le_continuum.trans hκ'.le)))
      have hcov := cover_small_initials H hH κ hκ' hI (by
        intro S hS
        exact ih #S hS S (H.induce S) rfl (hH.comap Subtype.val Subtype.val_injective))
      let F : G →g H :=
        { toFun := e
          map_rel' := by
            intro a b hab
            simpa only [H,SimpleGraph.comap_adj,e.symm_apply_apply] using hab }
      exact countable_union_of_hom F hcov

/-- If each four-cycle has at most continuum many common neighbors, the graph is a
countable union of triangle-free graphs. No clique hypothesis is required. -/
theorem countable_cover {V : Type} (G : SimpleGraph V) (hG : ContinuumFourCommon G) :
    IsCountableUnionOfTriangleFree G := cardinal_cover #V V G rfl hG

/-- A non-coverable graph has a four-cycle with MORE than continuum common neighbors. -/
theorem large_common4_of_no_cover {V : Type} (G : SimpleGraph V)
    (hG : ¬IsCountableUnionOfTriangleFree G) :
    ∃ a b c d, Cycle4 G a b c d ∧ continuum < #(common4 G a b c d) := by
  by_contra h
  push_neg at h
  exact hG (countable_cover G h)

#print axioms countable_cover
#print axioms large_common4_of_no_cover
end Erdos595ContinuumFourCommon
