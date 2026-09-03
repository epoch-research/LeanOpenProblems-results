import FormalConjecturesUtil

/-!
Countably many common neighbors for every distinct pair imply a countable
proper vertex coloring. Auxiliary to the investigation of Erdős 595.
-/

set_option autoImplicit false
open Set SimpleGraph Cardinal FirstOrder
open scoped Classical

namespace Erdos595CountableCodegree
universe u

private def binaryLanguage : Language where
  Functions n := {_k : ℕ // n = 2}
  Relations _ := Empty

private instance : Countable (Σ n, binaryLanguage.Functions n) := by
  change Countable (Σ n : ℕ, {_k : ℕ // n = 2})
  infer_instance

private def binaryStructure {V : Type u} (f : ℕ → V → V → V) : binaryLanguage.Structure V where
  funMap := fun {n} s x => by
    obtain ⟨k,rfl⟩ := s
    exact f k (x 0) (x 1)
  RelMap := fun r => Empty.elim r

section Closure
variable {V : Type u} (f : ℕ → V → V → V)

private abbrev cl (S : Set V) : @binaryLanguage.Substructure V (binaryStructure f) :=
  @Language.Substructure.closure binaryLanguage V (binaryStructure f) S

private lemma cl_subset (S : Set V) : S ⊆ cl f S := by
  letI := binaryStructure f
  exact Language.Substructure.subset_closure

private lemma cl_mono {S T : Set V} (h : S ⊆ T) : cl f S ≤ cl f T := by
  letI := binaryStructure f
  exact Language.Substructure.closure_mono h

private lemma cl_fun {S : Set V} (k : ℕ) {x y : V}
    (hx : x ∈ cl f S) (hy : y ∈ cl f S) : f k x y ∈ cl f S := by
  letI := binaryStructure f
  have h := (cl f S).fun_mem (⟨k,rfl⟩ : binaryLanguage.Functions 2)
    ![x,y] (by intro i; fin_cases i <;> assumption)
  exact h

private lemma cl_card (S : Set V) : #(cl f S) ≤ max ℵ₀ #S := by
  letI := binaryStructure f
  have h := Language.Substructure.lift_card_closure_le (L := binaryLanguage) (s := S)
  have hc : Cardinal.lift.{u} #(Σ n, binaryLanguage.Functions n) ≤ ℵ₀ :=
    Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0
  simp only [Cardinal.lift_uzero] at h
  exact h.trans (max_le (le_max_left _ _) (by
    calc
      #S + Cardinal.lift.{u} #(Σ n, binaryLanguage.Functions n)
        ≤ max ℵ₀ #S + max ℵ₀ #S := add_le_add (le_max_right _ _) (hc.trans (le_max_left _ _))
      _ = max ℵ₀ #S := Cardinal.add_eq_self (le_max_left _ _)))

private lemma cl_Iio [LinearOrder V] (a : V) {v : V} (hv : v ∈ cl f (Iio a)) :
    ∃ b < a, v ∈ cl f (Iic b) := by
  letI := binaryStructure f
  refine Language.Substructure.closure_induction (p := fun v => ∃ b < a, v ∈ cl f (Iic b)) hv ?_ ?_
  · intro x hx
    exact ⟨x,hx,cl_subset f _ (le_refl x)⟩
  · intro n s x ih
    obtain ⟨k,rfl⟩ := s
    obtain ⟨b,hb,hxb⟩ := ih 0
    obtain ⟨c,hc,hxc⟩ := ih 1
    refine ⟨max b c,max_lt hb hc,?_⟩
    exact cl_fun f k (cl_mono f (Iic_subset_Iic.mpr (le_max_left b c)) hxb)
      (cl_mono f (Iic_subset_Iic.mpr (le_max_right b c)) hxc)


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

section Incoming
variable {V I : Type u} [LinearOrder I] [WellFoundedLT I]
    (G : SimpleGraph V) (r : V → I)

private noncomputable def height : V → ℕ :=
  (InvImage.wf r wellFounded_lt).fix (fun v rec =>
    if h : ∃ w, G.Adj v w ∧ r w < r v then
      rec h.choose h.choose_spec.2 + 1 else 0)

private lemma height_eq (v : V) : height G r v =
    if h : ∃ w, G.Adj v w ∧ r w < r v then height G r h.choose + 1 else 0 := by
  rw [height,WellFounded.fix_eq]

private lemma height_ne
    (hu : ∀ v a b, G.Adj v a → G.Adj v b → r a < r v → r b < r v → a = b)
    {v w : V} (hvw : G.Adj v w) (hr : r w < r v) : height G r v ≠ height G r w := by
  classical
  have hex : ∃ w, G.Adj v w ∧ r w < r v := ⟨w,hvw,hr⟩
  rw [height_eq G r v,dif_pos hex]
  have he : hex.choose = w := hu v _ _ hex.choose_spec.1 hvw hex.choose_spec.2 hr
  rw [he]
  omega

/-- Color each rank separately and combine it with the height of the unique
lower-rank neighbor. The rank set can have arbitrary cardinality. -/
theorem coloring_of_rank
    (hu : ∀ v a b, G.Adj v a → G.Adj v b → r a < r v → r b < r v → a = b)
    (hc : ∀ i, Nonempty ((G.induce {v | r v = i}).Coloring ℕ)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  let c := fun i => (hc i).some
  have transport (i j : I) (hij : i = j) (v : V) (hi : r v = i) (hj : r v = j) :
      c i ⟨v,hi⟩ = c j ⟨v,hj⟩ := by
    cases hij
    rfl
  let code : V → ℕ × ℕ := fun v => (c (r v) ⟨v,rfl⟩,height G r v)
  let col : G.Coloring (ℕ × ℕ) := SimpleGraph.Coloring.mk code (by
    intro v w hvw he
    have hheight := congrArg Prod.snd he
    rcases lt_trichotomy (r v) (r w) with h | h | h
    · exact height_ne G r hu hvw.symm h hheight.symm
    · have hcolor := congrArg Prod.fst he
      have h' : c (r v) ⟨v,rfl⟩ = c (r v) ⟨w,h.symm⟩ :=
        hcolor.trans (transport (r w) (r v) h.symm w rfl h.symm)
      exact (c (r v)).valid (show (G.induce {x | r x = r v}).Adj
        ⟨v,rfl⟩ ⟨w,h.symm⟩ from hvw) h'
    · exact height_ne G r hu hvw h hheight)
  exact ⟨G.recolorOfEmbedding ⟨Encodable.encode,Encodable.encode_injective⟩ col⟩

end Incoming

section Codegree
variable {V : Type u} (G : SimpleGraph V)
    (hG : ∀ a b, a ≠ b → (G.commonNeighbors a b).Countable)

private noncomputable def enumeration (k : ℕ) (a b : V) : V :=
  if h : a ≠ b then Set.enumerateCountable (hG a b h) a k else a

private lemma enumeration_spec {a b v : V} (hne : a ≠ b)
    (hv : v ∈ G.commonNeighbors a b) : ∃ k, enumeration G hG k a b = v := by
  obtain ⟨k,hk⟩ := Set.subset_range_enumerate (hG a b hne) a hv
  exact ⟨k,by simpa only [enumeration,dif_pos hne] using hk⟩

private lemma common_mem_cl {S : Set V} {a b v : V} (hne : a ≠ b)
    (ha : a ∈ cl (enumeration G hG) S) (hb : b ∈ cl (enumeration G hG) S)
    (hav : G.Adj a v) (hbv : G.Adj b v) : v ∈ cl (enumeration G hG) S := by
  obtain ⟨k,rfl⟩ := enumeration_spec G hG hne ⟨hav,hbv⟩
  exact cl_fun _ k ha hb

include hG in
private lemma coloring_small_initials [LinearOrder V] [WellFoundedLT V]
    (κ : Cardinal.{u}) (hκ : ℵ₀ < κ) (hi : ∀ a : V, #(Iic a) < κ)
    (ih : ∀ S : Set V, #S < κ → Nonempty ((G.induce S).Coloring ℕ)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  let f := enumeration G hG
  apply coloring_of_rank G (rank f)
  · intro v a b hva hvb ha hb
    by_contra hab
    exact rank_not_mem f v (common_mem_cl G hG hab
      (rank_lt_mem f ha) (rank_lt_mem f hb) hva.symm hvb.symm)
  · intro a
    apply ih
    have hs : {v | rank f v = a} ⊆ (cl f (Iic a) : Set V) := by
      intro v hv
      change rank f v = a at hv
      rw [← hv]
      exact rank_mem f v
    exact (Cardinal.mk_le_mk_of_subset hs).trans_lt
      ((cl_card f (Iic a)).trans_lt (max_lt hκ (hi a)))

end Codegree

private theorem cardinal_coloring (κ : Cardinal.{u}) :
    ∀ (V : Type u) (G : SimpleGraph V), #V = κ →
      (∀ a b, a ≠ b → (G.commonNeighbors a b).Countable) →
        Nonempty (G.Coloring ℕ) := by
  classical
  induction κ using Cardinal.lt_wf.induction with
  | h κ ih =>
    intro V G hcard hG
    by_cases hκ : κ ≤ ℵ₀
    · haveI : Countable V := Cardinal.mk_le_aleph0_iff.mp (hcard.le.trans hκ)
      letI : Encodable V := Encodable.ofCountable V
      exact ⟨SimpleGraph.Coloring.mk Encodable.encode
        (fun h he => h.ne (Encodable.encode_injective he))⟩
    · have hκ' : ℵ₀ < κ := lt_of_not_ge hκ
      let I := κ.ord.ToType
      let e : V ≃ I := (Cardinal.eq.mp (hcard.trans (Cardinal.mk_ord_toType κ).symm)).some
      let H : SimpleGraph I := G.comap e.symm
      have hH : ∀ a b : I, a ≠ b → (H.commonNeighbors a b).Countable := by
        intro a b hab
        exact (hG (e.symm a) (e.symm b) (e.symm.injective.ne hab)).preimage e.symm.injective
      have hI : ∀ a : I, #(Iic a) < κ := by
        intro a
        have hs : Iic a = insert a (Iio a) := by ext x; simp [le_iff_lt_or_eq,eq_comm]
        rw [hs]
        exact Cardinal.mk_insert_le.trans_lt (Cardinal.add_lt_of_lt hκ'.le
          (Cardinal.mk_Iio_ord_toType a) (Cardinal.one_lt_aleph0.trans hκ'))
      obtain ⟨c⟩ := coloring_small_initials H hH κ hκ' hI (by
        intro S hS
        apply ih #S hS S (H.induce S) rfl
        intro a b hab
        exact (hH a b (fun he => hab (Subtype.ext he))).preimage Subtype.val_injective)
      exact ⟨SimpleGraph.Coloring.mk (fun v => c (e v)) (by
        intro v w hvw
        exact c.valid (by simpa only [H,SimpleGraph.comap_adj,e.symm_apply_apply] using hvw))⟩

/-- Countable codegrees for all distinct pairs imply countable vertex chromatic number. -/
theorem coloring_nat_of_countable_common_neighbors {V : Type u} (G : SimpleGraph V)
    (hG : ∀ a b, a ≠ b → (G.commonNeighbors a b).Countable) :
    Nonempty (G.Coloring ℕ) := cardinal_coloring #V V G rfl hG

#print axioms coloring_nat_of_countable_common_neighbors

end Erdos595CountableCodegree
