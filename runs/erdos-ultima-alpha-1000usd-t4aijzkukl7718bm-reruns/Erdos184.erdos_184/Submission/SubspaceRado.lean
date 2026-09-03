import FormalConjecturesUtil

/-!
Finite independent transversals of vector sets over an infinite field.
This is an auxiliary linear-algebra result, not a cycle-decomposition bound.
-/

open Module
open scoped Classical
namespace Erdos184.SubspaceRado

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

lemma finrank_adjoin_le (W : Submodule K M) (x : M) :
    finrank K ↥(W ⊔ K ∙ x) ≤ finrank K W + 1 := by
  have hr : finrank K ↥(K ∙ x) ≤ 1 := by
    by_cases hx : x = 0
    · subst x; rw [Submodule.span_zero_singleton, finrank_bot]; omega
    · rw [finrank_span_singleton hx]
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (K ∙ x)
  omega

lemma finrank_adjoin_of_notMem (W : Submodule K M) {x : M} (hx : x ∉ W) :
    finrank K ↥(W ⊔ K ∙ x) = finrank K W + 1 := by
  have hs : W < W ⊔ K ∙ x := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro he
    exact hx (he ▸ (show x ∈ W ⊔ K ∙ x from
      (le_sup_right : K ∙ x ≤ W ⊔ K ∙ x) (Submodule.mem_span_singleton_self x)))
  have hl := Submodule.finrank_lt_finrank_of_lt hs
  have hu := finrank_adjoin_le W x
  omega

/-- Relative finite Hall rank inequalities admit subspace representatives.
The auxiliary subspace `W` is carried through the induction. -/
theorem exists_subspace_representatives [Infinite K]
    (s : Finset ι) (U : ι → Submodule K M) (W : Submodule K M)
    (h : ∀ t ⊆ s, finrank K W + t.card ≤ finrank K ↥(W ⊔ t.sup U)) :
    ∃ v : ι → M, (∀ i ∈ s, v i ∈ U i) ∧
      finrank K W + s.card ≤ finrank K ↥(W ⊔ s.sup (fun i => K ∙ v i)) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    refine ⟨fun _ => 0, by simp, ?_⟩
    rw [Finset.sup_empty, sup_bot_eq, Finset.card_empty, Nat.add_zero]
  | @insert a s ha ih =>
    let T : Finset (Finset ι) := s.powerset.filter
      (fun t => finrank K ↥(W ⊔ t.sup U) = finrank K W + t.card)
    have hT : ∀ t ∈ T, ¬ U a ≤ W ⊔ t.sup U := by
      intro t ht hle
      obtain ⟨hts, htight⟩ := Finset.mem_filter.mp ht
      have hts' : t ⊆ s := Finset.mem_powerset.mp hts
      have hat : a ∉ t := fun hat => ha (hts' hat)
      have hh := h (insert a t) (Finset.insert_subset_insert a hts')
      rw [Finset.card_insert_of_notMem hat, Finset.sup_insert] at hh
      have he : W ⊔ (U a ⊔ t.sup U) = W ⊔ t.sup U := by
        apply le_antisymm
        · exact sup_le le_sup_left (sup_le hle le_sup_right)
        · exact sup_le le_sup_left (le_trans le_sup_right le_sup_right)
      rw [he, htight] at hh
      omega
    let P : T → Submodule K (U a) := fun t => (W ⊔ t.val.sup U).comap (U a).subtype
    have hP : ∀ t, P t ≠ ⊤ := by
      intro t he
      apply hT t.val t.property
      intro y hy
      have hm : (⟨y, hy⟩ : U a) ∈ P t := by rw [he]; trivial
      exact hm
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hP
    have havoid : ∀ t ∈ T, (x : M) ∉ W ⊔ t.sup U := by
      intro t ht hm
      exact hx ⟨t, ht⟩ hm
    have hzero : (∅ : Finset ι) ∈ T := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.empty_subset s), ?_⟩
      rw [Finset.sup_empty, sup_bot_eq, Finset.card_empty, Nat.add_zero]
    have hxW : (x : M) ∉ W := by simpa using havoid ∅ hzero
    let W' : Submodule K M := W ⊔ K ∙ (x : M)
    have hr : finrank K W' = finrank K W + 1 := finrank_adjoin_of_notMem W hxW
    have htail : ∀ t ⊆ s, finrank K W' + t.card ≤ finrank K ↥(W' ⊔ t.sup U) := by
      intro t hts
      have hbase := h t (hts.trans (Finset.subset_insert a s))
      have he : W' ⊔ t.sup U = (W ⊔ t.sup U) ⊔ K ∙ (x : M) := by
        dsimp [W']; ac_rfl
      rw [hr, he]
      by_cases ht : finrank K ↥(W ⊔ t.sup U) = finrank K W + t.card
      · have hm : t ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hts, ht⟩
        rw [finrank_adjoin_of_notMem _ (havoid t hm), ht]
        omega
      · have hmono := Submodule.finrank_mono
          (le_sup_left : W ⊔ t.sup U ≤ (W ⊔ t.sup U) ⊔ K ∙ (x : M))
        omega
    obtain ⟨v, hv, hdim⟩ := ih W' htail
    refine ⟨Function.update v a (x : M), ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa using x.property
      · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)] using hv i hi
    · have hs : s.sup (fun i => K ∙ Function.update v a (x : M) i) =
          s.sup (fun i => K ∙ v i) := by
        apply Finset.sup_congr rfl
        intro i hi
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
      rw [Finset.card_insert_of_notMem ha, Finset.sup_insert,
        Function.update_self, hs]
      have he : W ⊔ (K ∙ (x : M) ⊔ s.sup (fun i => K ∙ v i)) =
          W' ⊔ s.sup (fun i => K ∙ v i) := by dsimp [W']; ac_rfl
      rw [he]
      rw [hr] at hdim
      omega

lemma sup_singleton_span (s : Finset ι) (v : ι → M) :
    s.sup (fun i => K ∙ v i) = Submodule.span K (v '' (s : Set ι)) := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro i hi
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr
      (Submodule.subset_span (Set.mem_image_of_mem v hi))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact (Finset.le_sup (f := fun i => K ∙ v i) hi)
      (Submodule.mem_span_singleton_self (v i))

/-- The subspace version of finite linear Rado. -/
theorem exists_independent_subspace_representatives [Infinite K] [Fintype ι]
    (U : ι → Submodule K M)
    (h : ∀ s : Finset ι, s.card ≤ finrank K ↥(s.sup U)) :
    ∃ v : ι → M, (∀ i, v i ∈ U i) ∧ LinearIndependent K v := by
  obtain ⟨v, hv, hr⟩ := exists_subspace_representatives Finset.univ U ⊥ (by
    intro s _
    rw [finrank_bot, zero_add, bot_sup_eq]
    exact h s)
  refine ⟨v, fun i => hv i (Finset.mem_univ i), ?_⟩
  apply linearIndependent_iff_card_le_finrank_span.mpr
  rw [finrank_bot, zero_add, bot_sup_eq, sup_singleton_span,
    Finset.coe_univ, Set.image_univ, Finset.card_univ] at hr
  exact hr

/-- Replacing one vector by a vector outside the span of the others preserves
linear independence. No infinitude hypothesis is needed for this step. -/
lemma independent_update {v : ι → M} (hv : LinearIndependent K v)
    (a : ι) {x : M} (hx : x ∉ Submodule.span K (v '' {a}ᶜ)) :
    LinearIndependent K (Function.update v a x) := by
  classical
  have he : Set.EqOn v (Function.update v a x) {a}ᶜ := by
    intro i hi
    exact (Function.update_of_ne (by simpa using hi) x v).symm
  have hs := (hv.linearIndepOn.mono (Set.subset_univ {a}ᶜ)).congr he
  have hx' : Function.update v a x a ∉
      Submodule.span K (Function.update v a x '' {a}ᶜ) := by
    rw [Function.update_self, ← Set.image_congr he]
    exact hx
  have hi := hs.insert hx'
  have huniv : insert a ({a}ᶜ : Set ι) = Set.univ := by ext i; simp; tauto
  rw [huniv, linearIndepOn_univ] at hi
  exact hi

/-- Independent representatives chosen in spans can be replaced by actual
members of the generating sets. -/
theorem replace_span_representatives [Fintype ι] (A : ι → Set M)
    {v : ι → M} (hv : LinearIndependent K v)
    (hmem : ∀ i, v i ∈ Submodule.span K (A i)) :
    ∃ w : ι → M, (∀ i, w i ∈ A i) ∧ LinearIndependent K w := by
  classical
  have hreplace : ∀ s : Finset ι, ∃ w : ι → M,
      LinearIndependent K w ∧ (∀ i, w i ∈ Submodule.span K (A i)) ∧
        (∀ i ∈ s, w i ∈ A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨v, hv, hmem, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨w, hw, hm, hs⟩ := ih
      obtain ⟨x, hxA, hx⟩ : ∃ x ∈ A a, x ∉ Submodule.span K (w '' {a}ᶜ) := by
        by_contra! hbad
        have hle : Submodule.span K (A a) ≤ Submodule.span K (w '' {a}ᶜ) :=
          Submodule.span_le.mpr hbad
        exact hw.notMem_span a (hle (hm a))
      refine ⟨Function.update w a x, independent_update hw a hx, ?_, ?_⟩
      · intro i
        by_cases hi : i = a
        · subst i; simpa using Submodule.subset_span hxA
        · simpa [Function.update_of_ne hi] using hm i
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa using hxA
        · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)] using hs i hi
  obtain ⟨w, hw, _, hm⟩ := hreplace Finset.univ
  exact ⟨w, fun i => hm i (Finset.mem_univ i), hw⟩

/-- Finite linear Rado: the Hall rank inequalities are sufficient for an
independent transversal of a family of sets over an infinite field. -/
theorem exists_independent_representatives [Infinite K] [Fintype ι]
    (A : ι → Set M)
    (h : ∀ s : Finset ι, s.card ≤ finrank K ↥(s.sup (fun i => Submodule.span K (A i)))) :
    ∃ v : ι → M, (∀ i, v i ∈ A i) ∧ LinearIndependent K v := by
  obtain ⟨v, hv, hi⟩ := exists_independent_subspace_representatives
    (fun i => Submodule.span K (A i)) h
  exact replace_span_representatives A hi hv

/-- The necessary half of the finite Hall rank criterion. -/
theorem rank_condition_of_representatives [Fintype ι] (A : ι → Set M)
    {v : ι → M} (hmem : ∀ i, v i ∈ A i) (hv : LinearIndependent K v)
    (s : Finset ι) :
    s.card ≤ finrank K ↥(s.sup (fun i => Submodule.span K (A i))) := by
  have hi : LinearIndependent K (fun i : s => v i.val) :=
    hv.comp Subtype.val Subtype.val_injective
  have hd := finrank_span_eq_card hi
  have hle : Submodule.span K (Set.range (fun i : s => v i.val)) ≤
      s.sup (fun i => Submodule.span K (A i)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (Finset.le_sup (f := fun i => Submodule.span K (A i)) i.property)
      (Submodule.subset_span (hmem i.val))
  have hm := Submodule.finrank_mono hle
  rw [hd, Fintype.card_coe] at hm
  exact hm

/-- Rado's independent-transversal criterion for finite families of vector
sets in a finite-dimensional space over an infinite field. -/
theorem independent_transversal_iff [Infinite K] [Fintype ι] (A : ι → Set M) :
    (∃ v : ι → M, (∀ i, v i ∈ A i) ∧ LinearIndependent K v) ↔
      ∀ s : Finset ι, s.card ≤ finrank K ↥(s.sup (fun i => Submodule.span K (A i))) := by
  constructor
  · rintro ⟨v, hm, hi⟩
    exact rank_condition_of_representatives A hm hi
  · exact exists_independent_representatives A

end Erdos184.SubspaceRado
