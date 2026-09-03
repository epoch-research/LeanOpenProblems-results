import Submission.CountableCodegreeColoring
import Submission.RankEdgeCover

/-! A countable-cover criterion using common neighborhoods of four-cycles.
This is an auxiliary result, not a settlement of the original conjecture. -/
set_option autoImplicit false
open Set SimpleGraph Cardinal FirstOrder
open scoped Classical
namespace Erdos595FourCycleCommon
open Erdos595Work Erdos595RankEdgeCover
universe u

private def fouraryLanguage : Language where
  Functions n := {_k : ℕ // n = 4}
  Relations _ := Empty

private instance : Countable (Σ n, fouraryLanguage.Functions n) := by
  change Countable (Σ n : ℕ, {_k : ℕ // n = 4})
  infer_instance

private def fouraryStructure {V : Type u} (f : ℕ → V → V → V → V → V) : fouraryLanguage.Structure V where
  funMap := fun {n} s x => by
    obtain ⟨k,rfl⟩ := s
    exact f k (x 0) (x 1) (x 2) (x 3)
  RelMap := fun r => Empty.elim r

section Closure
variable {V : Type u} (f : ℕ → V → V → V → V → V)

private abbrev cl (S : Set V) : @fouraryLanguage.Substructure V (fouraryStructure f) :=
  @Language.Substructure.closure fouraryLanguage V (fouraryStructure f) S

private lemma cl_subset (S : Set V) : S ⊆ cl f S := by
  letI := fouraryStructure f
  exact Language.Substructure.subset_closure

private lemma cl_mono {S T : Set V} (h : S ⊆ T) : cl f S ≤ cl f T := by
  letI := fouraryStructure f
  exact Language.Substructure.closure_mono h

private lemma cl_fun {S : Set V} (k : ℕ) {a b c d : V}
    (ha : a ∈ cl f S) (hb : b ∈ cl f S) (hc : c ∈ cl f S) (hd : d ∈ cl f S) :
    f k a b c d ∈ cl f S := by
  letI := fouraryStructure f
  have h := (cl f S).fun_mem (⟨k,rfl⟩ : fouraryLanguage.Functions 4)
    ![a,b,c,d] (by intro i; fin_cases i <;> assumption)
  exact h

private lemma cl_card (S : Set V) : #(cl f S) ≤ max ℵ₀ #S := by
  letI := fouraryStructure f
  have h := Language.Substructure.lift_card_closure_le (L := fouraryLanguage) (s := S)
  have hc : Cardinal.lift.{u} #(Σ n, fouraryLanguage.Functions n) ≤ ℵ₀ :=
    Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0
  simp only [Cardinal.lift_uzero] at h
  exact h.trans (max_le (le_max_left _ _) (by
    calc
      #S + Cardinal.lift.{u} #(Σ n, fouraryLanguage.Functions n)
        ≤ max ℵ₀ #S + max ℵ₀ #S := add_le_add (le_max_right _ _) (hc.trans (le_max_left _ _))
      _ = max ℵ₀ #S := Cardinal.add_eq_self (le_max_left _ _)))

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
variable {V : Type u} (G : SimpleGraph V)

/-- Four distinct vertices spanning a cycle; chords are permitted. -/
def Cycle4 (a b c d : V) : Prop :=
  a ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

def common4 (a b c d : V) : Set V :=
  {v | G.Adj a v ∧ G.Adj b v ∧ G.Adj c v ∧ G.Adj d v}

def CountableFourCommon : Prop :=
  ∀ a b c d, Cycle4 G a b c d → (common4 G a b c d).Countable

variable (hG : CountableFourCommon G)

private noncomputable def enumeration (k : ℕ) (a b c d : V) : V :=
  if h : Cycle4 G a b c d then Set.enumerateCountable (hG a b c d h) a k else a

private lemma common_mem_cl {S : Set V} {a b c d v : V} (hcycle : Cycle4 G a b c d)
    (ha : a ∈ cl (enumeration G hG) S) (hb : b ∈ cl (enumeration G hG) S)
    (hc : c ∈ cl (enumeration G hG) S) (hd : d ∈ cl (enumeration G hG) S)
    (hv : v ∈ common4 G a b c d) : v ∈ cl (enumeration G hG) S := by
  obtain ⟨k,hk⟩ := Set.subset_range_enumerate (hG a b c d hcycle) a hv
  have he : enumeration G hG k a b c d = v := by
    simpa only [enumeration,dif_pos hcycle] using hk
  rw [← he]
  exact cl_fun _ k ha hb hc hd

include hG in
private lemma cover_small_initials [LinearOrder V] [WellFoundedLT V]
    (κ : Cardinal.{u}) (hκ : ℵ₀ < κ) (hi : ∀ a : V, #(Iic a) < κ)
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

lemma CountableFourCommon.comap {W : Type u} {G : SimpleGraph V}
    (hG : CountableFourCommon G) (e : W → V) (he : Function.Injective e) :
    CountableFourCommon (G.comap e) := by
  intro a b c d h
  have h' : Cycle4 G (e a) (e b) (e c) (e d) :=
    ⟨he.ne h.1,he.ne h.2.1,h.2.2⟩
  exact (hG _ _ _ _ h').preimage he

end Graphs

private theorem cardinal_cover (κ : Cardinal.{u}) :
    ∀ (V : Type u) (G : SimpleGraph V), #V = κ →
      CountableFourCommon G → IsCountableUnionOfTriangleFree G := by
  classical
  induction κ using Cardinal.lt_wf.induction with
  | h κ ih =>
    intro V G hcard hG
    by_cases hκ : κ ≤ ℵ₀
    · haveI : Countable V := Cardinal.mk_le_aleph0_iff.mp (hcard.le.trans hκ)
      apply countable_union_of_countable_common_neighbors
      intro a b hab
      exact Set.to_countable _
    · have hκ' : ℵ₀ < κ := lt_of_not_ge hκ
      let I := κ.ord.ToType
      let e : V ≃ I := (Cardinal.eq.mp (hcard.trans (Cardinal.mk_ord_toType κ).symm)).some
      let H : SimpleGraph I := G.comap e.symm
      have hH : CountableFourCommon H := hG.comap e.symm e.symm.injective
      have hI : ∀ a : I, #(Iic a) < κ := by
        intro a
        have hs : Iic a = insert a (Iio a) := by ext x; simp [le_iff_lt_or_eq,eq_comm]
        rw [hs]
        exact Cardinal.mk_insert_le.trans_lt (Cardinal.add_lt_of_lt hκ'.le
          (Cardinal.mk_Iio_ord_toType a) (Cardinal.one_lt_aleph0.trans hκ'))
      have hcov := cover_small_initials H hH κ hκ' hI (by
        intro S hS
        exact ih #S hS S (H.induce S) rfl (hH.comap Subtype.val Subtype.val_injective))
      let F : G →g H :=
        { toFun := e
          map_rel' := by
            intro a b hab
            simpa only [H,SimpleGraph.comap_adj,e.symm_apply_apply] using hab }
      exact countable_union_of_hom F hcov

/-- If each four-cycle has countably many common neighbors, the graph is a
countable union of triangle-free graphs. No clique hypothesis is required. -/
theorem countable_cover {V : Type u} (G : SimpleGraph V) (hG : CountableFourCommon G) :
    IsCountableUnionOfTriangleFree G := cardinal_cover #V V G rfl hG

/-- Any failure of the cover criterion is witnessed by an actual four-cycle
with uncountably many common neighbors. -/
theorem uncountable_common4_of_no_cover {V : Type u} (G : SimpleGraph V)
    (hG : ¬IsCountableUnionOfTriangleFree G) :
    ∃ a b c d, Cycle4 G a b c d ∧ ¬(common4 G a b c d).Countable := by
  by_contra h
  push_neg at h
  exact hG (countable_cover G h)

/-- In a K4-free graph, a four-cycle and two distinct common neighbors form
an induced octahedron, not merely a non-induced multipartite subgraph. -/
theorem octahedron_of_two_common {V : Type u} {G : SimpleGraph V} (hG : G.CliqueFree 4)
    {a b c d x y : V} (hcycle : Cycle4 G a b c d)
    (hx : x ∈ common4 G a b c d) (hy : y ∈ common4 G a b c d) (hxy : x ≠ y) :
    Nonempty (completeEquipartiteGraph 3 2 ↪g G) := by
  classical
  obtain ⟨hac,hbd,hab,hbc,hcd,hda⟩ := hcycle
  obtain ⟨hax,hbx,hcx,hdx⟩ := hx
  obtain ⟨hay,hby,hcy,hdy⟩ := hy
  have hnac : ¬G.Adj a c := no_adj_common_neighbors hG hbx hab.symm hax.symm hbc hcx.symm
  have hnbd : ¬G.Adj b d := no_adj_common_neighbors hG hax hab hbx.symm hda.symm hdx.symm
  have hnxy : ¬G.Adj x y := no_adj_common_neighbors hG hab hax hbx hay hby
  let f : Fin 3 × Fin 2 → V := fun p => ![![a,c],![b,d],![x,y] ] p.1 p.2
  have hf : ∀ p q, G.Adj (f p) (f q) ↔ p.1 ≠ q.1 := by
    rintro ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all [f,SimpleGraph.adj_comm]
  have hi : Function.Injective f := by
    rintro ⟨i,j⟩ ⟨k,l⟩ he
    have hik : i = k := by
      by_contra hik
      exact ((hf (i,j) (k,l)).mpr hik).ne he
    subst k
    have hjl : j = l := by
      fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all [f,eq_comm]
    subst l
    rfl
  exact ⟨{ toFun := f, inj' := hi, map_rel_iff' := hf _ _ }⟩

/-- Every K4-free counterexample contains an induced octahedron. -/
theorem octahedron_of_no_cover {V : Type u} {G : SimpleGraph V} (hG : G.CliqueFree 4)
    (hn : ¬IsCountableUnionOfTriangleFree G) :
    Nonempty (completeEquipartiteGraph 3 2 ↪g G) := by
  obtain ⟨a,b,c,d,hc,hnc⟩ := uncountable_common4_of_no_cover G hn
  have hs : ¬(common4 G a b c d).Subsingleton := fun h => hnc h.countable
  rw [Set.not_subsingleton_iff] at hs
  obtain ⟨x,hx,y,hy,hxy⟩ := hs
  exact octahedron_of_two_common hG hc hx hy hxy

/-- Consequently octahedron-free K4-free graphs are always covered. -/
theorem cover_of_no_octahedron {V : Type u} {G : SimpleGraph V} (hG : G.CliqueFree 4)
    (hn : ¬Nonempty (completeEquipartiteGraph 3 2 ↪g G)) :
    IsCountableUnionOfTriangleFree G := by
  by_contra h
  exact hn (octahedron_of_no_cover hG h)

#print axioms countable_cover
#print axioms uncountable_common4_of_no_cover
#print axioms octahedron_of_two_common
#print axioms octahedron_of_no_cover
#print axioms cover_of_no_octahedron
end Erdos595FourCycleCommon
