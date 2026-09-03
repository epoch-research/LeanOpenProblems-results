import Submission.ErdosSosHighDegree

set_option autoImplicit false

/-!
# Parity kernels of finite trees

A distance-free form of the parity-kernel lemma.  Vertices are partitioned into
`R` (a connected nonempty core), `U` (independent), and `W` (all of whose
neighbors belong to `U`).  The construction deletes at least `2*c` vertices
and uses at most `c` vertices of `U`.  The stronger rooted version applies
when both classes of a two-coloring have more than `c` vertices.

This file is independent of `Submission.Spec`.
-/

open Finset SimpleGraph Classical

namespace TreeParityKernel

universe u v

/-- The three parts of a parity kernel. -/
inductive Part
  | core | odd | even
  deriving DecidableEq, Fintype

open Part

/-- Cardinality of a predicate on a finite type. -/
noncomputable def number {V : Type u} [Fintype V] (p : V → Prop) : ℕ :=
  (univ.filter p).card

lemma number_eq_filter {V : Type u} [Fintype V] (p : V → Prop) [DecidablePred p] :
    number p = (univ.filter p).card := by
  unfold number
  congr 1
  ext x
  simp

lemma number_eq_sum {V : Type u} [Fintype V] (p : V → Prop) :
    number p = ∑ x, if p x then 1 else 0 := by
  simp only [number, Finset.card_filter]

lemma number_congr {V : Type u} [Fintype V] {p q : V → Prop}
    (h : ∀ x, p x ↔ q x) : number p = number q := by
  simp only [number, Finset.filter_congr (fun x _ => h x)]

lemma number_add_not {V : Type u} [Fintype V] (p : V → Prop) :
    number p + number (fun x => ¬ p x) = Fintype.card V := by
  simp only [number_eq_sum, ← sum_add_distrib]
  calc
    _ = ∑ _x : V, 1 := by
      apply sum_congr rfl
      intro x _
      by_cases h : p x <;> simp [h]
    _ = _ := by simp

lemma number_equiv {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (p : W → Prop) : number (fun x => p (e x)) = number p := by
  simp only [number_eq_sum]
  exact Equiv.sum_comp e (fun x => if p x then (1 : ℕ) else 0)

/-- Number of vertices carrying a given label. -/
noncomputable def count {V : Type u} [Fintype V] (f : V → Part) (s : Part) : ℕ :=
  number (fun x => f x = s)

/-- Number of vertices outside the core. -/
noncomputable def removed {V : Type u} [Fintype V] (f : V → Part) : ℕ :=
  count f odd + count f even

lemma count_total {V : Type u} [Fintype V] (f : V → Part) :
    count f core + removed f = Fintype.card V := by
  simp only [count, removed, number_eq_sum, ← sum_add_distrib]
  calc
    _ = ∑ _x : V, 1 := by
      apply sum_congr rfl
      intro x _
      cases f x <;> simp
    _ = _ := by simp

/-- The edge conditions for the independent separator and isolated remainder. -/
def GoodEdges {V : Type u} (G : SimpleGraph V) (f : V → Part) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → (f x = even → f y = odd) ∧ (f x = odd → f y ≠ odd)

/-- A branch certificate may have empty core.  Its root is never in `W`;
if any core survives, the root survives and reaches it inside the core. -/
structure Branch {V : Type u} (G : SimpleGraph V) (r : V) (f : V → Part) : Prop where
  edges : GoodEdges G f
  root_not_even : f r ≠ even
  reach : ∀ (x : V) (hx : f x = core), ∃ hr : f r = core,
    (G.induce {x | f x = core}).Reachable ⟨r, hr⟩ ⟨x, hx⟩

lemma Branch.connected {V : Type u} {G : SimpleGraph V} {r : V} {f : V → Part}
    (h : Branch G r f) (hr : f r = core) :
    (G.induce {x | f x = core}).Connected := by
  letI : Nonempty {x | f x = core} := ⟨⟨r, hr⟩⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨_, hx⟩ := h.reach x.val x.property
  obtain ⟨_, hy⟩ := h.reach y.val y.property
  exact hx.symm.trans hy

lemma branch_all {V : Type u} {G : SimpleGraph V} (hG : G.Connected) (r : V) :
    Branch G r (fun _ => core) := by
  refine ⟨?_, by simp, ?_⟩
  · intro x y _
    simp
  · intro x _
    refine ⟨rfl, ?_⟩
    let g : G →g G.induce {x | (fun _ : V => core) x = core} :=
      ⟨fun x => ⟨x, rfl⟩, fun h => h⟩
    exact (hG r x).map g

/-- A proper two-coloring, with no choice of orientation. -/
def TwoColor {V : Type u} (G : SimpleGraph V) (χ : V → Fin 2) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → χ x ≠ χ y

noncomputable def same {V : Type u} [Fintype V] (χ : V → Fin 2) (r : V) : ℕ :=
  number (fun x => χ x = χ r)

noncomputable def other {V : Type u} [Fintype V] (χ : V → Fin 2) (r : V) : ℕ :=
  number (fun x => χ x ≠ χ r)

lemma same_add_other {V : Type u} [Fintype V] (χ : V → Fin 2) (r : V) :
    same χ r + other χ r = Fintype.card V := number_add_not _

lemma same_pos {V : Type u} [Fintype V] (χ : V → Fin 2) (r : V) :
    0 < same χ r := by
  apply card_pos.mpr
  exact ⟨r, by simp⟩

/-- Remove an entire branch, putting its root-color in `U`. -/
noncomputable def discard {V : Type u} (χ : V → Fin 2) (r : V) (x : V) : Part :=
  if χ x = χ r then odd else even

/-- Keep just the branch root. -/
noncomputable def singleton {V : Type u} (χ : V → Fin 2) (r : V) (x : V) : Part :=
  if x = r then core else if χ x = χ r then even else odd

lemma branch_discard {V : Type u} {G : SimpleGraph V} {χ : V → Fin 2}
    (hχ : TwoColor G χ) (r : V) : Branch G r (discard χ r) := by
  refine ⟨?_, by simp [discard], ?_⟩
  · intro x y hxy
    have h := hχ hxy
    dsimp [discard]
    split_ifs <;> simp_all
    omega
  · intro x hx
    simp only [discard] at hx
    split_ifs at hx

lemma branch_singleton {V : Type u} {G : SimpleGraph V} {χ : V → Fin 2}
    (hχ : TwoColor G χ) (r : V) : Branch G r (singleton χ r) := by
  refine ⟨?_, by simp [singleton], ?_⟩
  · intro x y hxy
    have h := hχ hxy
    dsimp [singleton]
    split_ifs <;> simp_all
    omega
  · intro x hx
    have he : x = r := by
      by_contra hn
      simp only [singleton, if_neg hn] at hx
      split_ifs at hx
    subst x
    exact ⟨hx, .rfl⟩

lemma count_discard {V : Type u} [Fintype V] (χ : V → Fin 2) (r : V) :
    count (discard χ r) odd = same χ r ∧ removed (discard χ r) = same χ r + other χ r := by
  have ho : count (discard χ r) odd = same χ r := by
    apply number_congr
    intro x
    simp [discard]
  have he : count (discard χ r) even = other χ r := by
    apply number_congr
    intro x
    simp [discard]
  exact ⟨ho, by simp [removed, ho, he]⟩

lemma count_singleton {V : Type u} [Fintype V] (χ : V → Fin 2) (r : V) :
    count (singleton χ r) odd = other χ r ∧
      removed (singleton χ r) + 1 = same χ r + other χ r := by
  have ho : count (singleton χ r) odd = other χ r := by
    apply number_congr
    intro x
    by_cases h : x = r <;> simp [singleton, h]
  have hc : count (singleton χ r) core = 1 := by
    have he : ∀ x, singleton χ r x = core ↔ x = r := by
      intro x
      by_cases h : x = r
      · simp [singleton, h]
      · simp only [singleton, if_neg h]
        split_ifs <;> simp_all
    change number _ = 1
    rw [number_congr he]
    simp [number, Finset.filter_eq' (univ : Finset V) r]
  have ht := count_total (singleton χ r)
  have hs := same_add_other χ r
  exact ⟨ho, by omega⟩


section Join

open CommonMarkedForest

variable {I : Type u} (T : I → CommonMarkedForest.RootedTree.{u})

/-- Adjoin a new root to a family of disjoint rooted trees. -/
def joinGraph : SimpleGraph (Option (Σ i, (T i).V)) where
  Adj x y := match x, y with
    | none, none => False
    | none, some y => y.2 = (T y.1).root
    | some x, none => x.2 = (T x.1).root
    | some x, some y => (forestGraph T).Adj x y
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    intro x
    cases x
    · exact id
    · exact (forestGraph T).irrefl

/-- Glue branch labels, retaining the newly adjoined root. -/
def joinLabels (f : (i : I) → (T i).V → Part) : Option (Σ i, (T i).V) → Part
  | none => core
  | some ⟨i, x⟩ => f i x

@[simp] lemma joinLabels_none (f : (i : I) → (T i).V → Part) :
    joinLabels T f none = core := rfl

@[simp] lemma joinLabels_some (f : (i : I) → (T i).V → Part) (i : I) (x : (T i).V) :
    joinLabels T f (some ⟨i, x⟩) = f i x := rfl

lemma branch_join (f : (i : I) → (T i).V → Part)
    (hf : ∀ i, Branch (T i).graph (T i).root (f i)) :
    Branch (joinGraph T) none (joinLabels T f) := by
  refine ⟨?_, by simp, ?_⟩
  · intro x y hxy
    cases x with
    | none => simp [joinLabels]
    | some x =>
      cases y with
      | none =>
        change x.2 = (T x.1).root at hxy
        change (f x.1 x.2 = even → core = odd) ∧ (f x.1 x.2 = odd → core ≠ odd)
        rw [hxy]
        simp [(hf x.1).root_not_even]
      | some y =>
        change (forestGraph T).Adj x y at hxy
        obtain ⟨i, a, b, rfl, rfl, hab⟩ := hxy
        exact (hf i).edges hab
  · intro x hx
    refine ⟨rfl, ?_⟩
    cases x with
    | none => exact .rfl
    | some x =>
      rcases x with ⟨i, x⟩
      obtain ⟨hr, hrx⟩ := (hf i).reach x hx
      let g : ((T i).graph.induce {x | f i x = core}) →g
          ((joinGraph T).induce {x | joinLabels T f x = core}) :=
        { toFun := fun x => ⟨some ⟨i, x.val⟩, x.property⟩
          map_rel' := by
            intro a b hab
            exact (forestGraph_adj_same T i _ _).mpr hab }
      have hroot : ((joinGraph T).induce {x | joinLabels T f x = core}).Adj
          ⟨none, rfl⟩ (g ⟨(T i).root, hr⟩) := rfl
      exact hroot.reachable.trans (hrx.map g)

variable [Fintype I]

lemma number_join (p : Option (Σ i, (T i).V) → Prop) :
    number p = (if p none then 1 else 0) +
      ∑ i, number (fun x : (T i).V => p (some ⟨i, x⟩)) := by
  simp only [number_eq_sum, Fintype.sum_option, Fintype.sum_sigma]

lemma count_join (f : (i : I) → (T i).V → Part) (s : Part) :
    count (joinLabels T f) s = (if core = s then 1 else 0) + ∑ i, count (f i) s := by
  have h := number_join T (fun x => joinLabels T f x = s)
  cases s <;> simpa only [count, joinLabels_none, joinLabels_some, ite_true, ite_false,
    reduceCtorEq] using h

lemma removed_join (f : (i : I) → (T i).V → Part) :
    removed (joinLabels T f) = ∑ i, removed (f i) := by
  simp [removed, count_join, sum_add_distrib]

end Join

section Transport

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}

lemma Branch.map {r : V} {f : V → Part} (h : Branch G r f) (e : G ≃g H) :
    Branch H (e r) (fun x => f (e.symm x)) := by
  refine ⟨?_, by simpa using h.root_not_even, ?_⟩
  · intro x y hxy
    exact h.edges (e.symm.toHom.map_rel' hxy)
  · intro x hx
    obtain ⟨hr, hrx⟩ := h.reach (e.symm x) hx
    refine ⟨by simpa using hr, ?_⟩
    let g : (G.induce {x | f x = core}) →g (H.induce {x | f (e.symm x) = core}) :=
      { toFun := fun x => ⟨e x.val, by change f (e.symm (e x.val)) = core; rw [e.symm_apply_apply]; exact x.property⟩
        map_rel' := fun hxy => e.toHom.map_rel' hxy }
    convert hrx.map g using 1
    simp [g]

lemma count_map [Fintype V] [Fintype W] (e : V ≃ W) (f : V → Part) (s : Part) :
    count (fun x => f (e.symm x)) s = count f s := number_equiv e.symm (fun x => f x = s)

lemma removed_map [Fintype V] [Fintype W] (e : V ≃ W) (f : V → Part) :
    removed (fun x => f (e.symm x)) = removed f := by
  simp [removed, count_map]

end Transport


section RootDecomposition

open CommonMarkedForest ErdosSosHighDegree

variable {V : Type u} {G : SimpleGraph V} (hG : G.IsTree) (r : V)

/-- The unique vertex of a deleted-root component adjacent to the root. -/
noncomputable def componentRoot (C : (G.induce {r}ᶜ).ConnectedComponent) : C.supp :=
  ⟨(existsUnique_neighbor_in_component hG r C).choose,
    (existsUnique_neighbor_in_component hG r C).choose_spec.1.1⟩

lemma componentRoot_adj (C : (G.induce {r}ᶜ).ConnectedComponent) :
    G.Adj r (componentRoot hG r C).val.val :=
  (existsUnique_neighbor_in_component hG r C).choose_spec.1.2

lemma componentRoot_eq (C : (G.induce {r}ᶜ).ConnectedComponent) (x : C.supp)
    (hx : G.Adj r x.val.val) : x = componentRoot hG r C := by
  apply Subtype.ext
  exact (existsUnique_neighbor_in_component hG r C).choose_spec.2 x.val ⟨x.property, hx⟩

variable [Fintype V]

/-- The branches of a finite tree at a vertex. -/
noncomputable def rootFamily : (G.induce {r}ᶜ).ConnectedComponent →
    CommonMarkedForest.RootedTree.{u} :=
  componentFamily (G.induce {r}ᶜ) (hG.IsAcyclic.induce _) (componentRoot hG r)

/-- Exact reconstruction of a tree by joining the components at the deleted root. -/
noncomputable def rootIso : joinGraph (rootFamily hG r) ≃g G where
  toEquiv := (Equiv.optionCongr (Equiv.sigmaFiberEquiv (G.induce {r}ᶜ).connectedComponentMk)).trans
    (Equiv.optionSubtypeNe r)
  map_rel_iff' := by
    intro x y
    cases x with
    | none =>
      cases y with
      | none => exact ⟨fun h => h.ne rfl, False.elim⟩
      | some y =>
        change G.Adj r y.2.val.val ↔ y.2 = componentRoot hG r y.1
        exact ⟨componentRoot_eq hG r y.1 y.2,
          fun he => he ▸ componentRoot_adj hG r y.1⟩
    | some x =>
      cases y with
      | none =>
        change G.Adj x.2.val.val r ↔ x.2 = componentRoot hG r x.1
        exact ⟨fun h => componentRoot_eq hG r x.1 x.2 h.symm,
          fun he => (he ▸ componentRoot_adj hG r x.1).symm⟩
      | some y =>
        exact (componentUnionIso (G.induce {r}ᶜ) (hG.IsAcyclic.induce _)
          (componentRoot hG r)).map_rel_iff

@[simp] lemma rootIso_none : rootIso hG r none = r := rfl

@[simp] lemma rootIso_some (C : (G.induce {r}ᶜ).ConnectedComponent) (x : C.supp) :
    rootIso hG r (some ⟨C, x⟩) = x.val.val := rfl

lemma rootFamily_smaller (C : (G.induce {r}ᶜ).ConnectedComponent) :
    Fintype.card (rootFamily hG r C).V < Fintype.card V := by
  have hle : Fintype.card (rootFamily hG r C).V ≤ Fintype.card ({r}ᶜ : Set V) :=
    Fintype.card_le_of_injective (fun x => x.val) Subtype.val_injective
  have hlt : Fintype.card ({r}ᶜ : Set V) < Fintype.card V :=
    Fintype.card_subtype_lt (x := r) (by simp)
  exact hle.trans_lt hlt

end RootDecomposition


section Budgets

/-- Integral capacities can be split to realize every budget up to their sum. -/
lemma distribute_budget {I : Type u} (s : Finset I) (d : I → ℕ) (c : ℕ)
    (hc : c ≤ ∑ i ∈ s, d i) :
    ∃ h : I → ℕ, (∀ i, h i ≤ d i) ∧ ∑ i ∈ s, h i = c := by
  induction s using Finset.induction_on generalizing c with
  | empty =>
    have hc0 : c = 0 := by simpa using hc
    subst c
    exact ⟨fun _ => 0, fun _ => Nat.zero_le _, by simp⟩
  | @insert i s hi ih =>
    rw [sum_insert hi] at hc
    have hrem : c - min c (d i) ≤ ∑ j ∈ s, d j := by omega
    obtain ⟨h, hle, heq⟩ := ih _ hrem
    refine ⟨Function.update h i (min c (d i)), ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst j
        simp
      · simpa [Function.update_of_ne hj] using hle j
    · rw [sum_insert hi, Function.update_self]
      have hs : (∑ j ∈ s, Function.update h i (min c (d i)) j) = ∑ j ∈ s, h j := by
        apply sum_congr rfl
        intro j hj
        exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _
      rw [hs, heq]
      omega

/-- The numerical star exchange in the low-total-capacity case.  The set `S`
consists of branch roots deleted in addition to the endpoint deletions. -/
lemma star_budget {I : Type u} [Fintype I] (a b : I → ℕ) (c : ℕ)
    (ha : c < ∑ i, a i) (hb : c < 1 + ∑ i, b i)
    (hd : (∑ i, min (a i) (b i)) < c) :
    ∃ S : Finset I, S ⊆ univ.filter (fun i => b i < a i) ∧
      (∑ i, if b i < a i ∧ i ∉ S then b i else a i) ≤ c ∧
      2 * c ≤ ∑ i, if b i < a i ∧ i ∉ S then a i + b i - 1 else a i + b i := by
  let P := univ.filter (fun i => b i < a i)
  let d := ∑ i, min (a i) (b i)
  let e : I → ℕ := fun i => if b i < a i then a i - b i - 1 else 0
  let f : I → ℕ := fun i => if b i < a i then 0 else b i - a i
  let E := ∑ i, e i
  let F := ∑ i, f i
  let m := ∑ i, if b i < a i then a i + b i - 1 else a i + b i
  have heqA : (∑ i, a i) = d + P.card + E := by
    have hq : P.card = ∑ i, if b i < a i then 1 else 0 := by
      simp only [P, Finset.card_filter]
    rw [hq]
    simp only [d, E, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    dsimp [e]
    split_ifs <;> omega
  have heqB : (∑ i, b i) = d + F := by
    simp only [d, F, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    dsimp [f]
    split_ifs <;> omega
  have heqm : m = 2 * d + E + F := by
    simp only [m, d, E, F, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    dsimp [e, f]
    split_ifs <;> omega
  have hbase : (∑ i, if b i < a i then b i else a i) = d := by
    apply sum_congr rfl
    intro i _
    split_ifs <;> omega
  by_cases hm : 2 * c ≤ m
  · refine ⟨∅, empty_subset _, ?_, ?_⟩
    · simp only [notMem_empty, not_false_eq_true, and_true, hbase]
      exact hd.le
    · simp only [notMem_empty, not_false_eq_true, and_true]
      exact hm
  · let L := 2 * c - m
    have hL : L ≤ P.card := by omega
    have hLE : d + L + E ≤ c := by omega
    obtain ⟨S, hSP, hSc⟩ := exists_subset_card_eq hL
    refine ⟨S, hSP, ?_, ?_⟩
    · have hpoint (i : I) :
          (if b i < a i ∧ i ∉ S then b i else a i) ≤
            min (a i) (b i) + (if i ∈ S then 1 else 0) + e i := by
        have hmP : i ∈ S → b i < a i := fun h => (mem_filter.mp (hSP h)).2
        by_cases hS : i ∈ S
        · have hp := hmP hS
          simp only [e, hp, hS, not_true_eq_false, and_false, if_false, if_true]
          omega
        · by_cases hp : b i < a i <;>
            simp only [e, hp, hS, not_false_eq_true, and_true, if_false, if_true] <;> omega
      have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => hpoint i)
      have hcount : (∑ i : I, if i ∈ S then 1 else 0) = S.card := by
        simp
      simp only [sum_add_distrib, hcount, hSc] at hsum
      change _ ≤ d + L + E at hsum
      exact hsum.trans hLE
    · have hpoint (i : I) :
          (if b i < a i ∧ i ∉ S then a i + b i - 1 else a i + b i) =
            (if b i < a i then a i + b i - 1 else a i + b i) +
              (if i ∈ S then 1 else 0) := by
        have hmP : i ∈ S → b i < a i := fun h => (mem_filter.mp (hSP h)).2
        by_cases hS : i ∈ S
        · have hp := hmP hS
          simp only [hp, hS, not_true_eq_false, and_false, if_false, if_true]
          omega
        · simp [hS]
      simp_rw [hpoint]
      rw [sum_add_distrib]
      have hcount : (∑ i : I, if i ∈ S then 1 else 0) = S.card := by simp
      rw [hcount, hSc]
      change 2 * c ≤ m + L
      omega

/-- Every branch can spend any budget up to its smaller color class.  Strictly
interior budgets use the induction hypothesis; endpoints are explicit. -/
lemma budget_branch {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.Connected) (r : V) (χ : V → Fin 2) (hχ : TwoColor G χ)
    (c : ℕ) (hc : c ≤ min (same χ r) (other χ r))
    (ih : c < same χ r → c < other χ r →
      ∃ g : V → Part, Branch G r g ∧ g r = core ∧ count g odd ≤ c ∧ 2 * c ≤ removed g) :
    ∃ g : V → Part, Branch G r g ∧ count g odd ≤ c ∧ 2 * c ≤ removed g := by
  by_cases hc0 : c = 0
  · subst c
    exact ⟨fun _ => core, branch_all hG r, by simp [count, number], Nat.zero_le _⟩
  by_cases hlt : c < min (same χ r) (other χ r)
  · obtain ⟨g, hg, _, hcost, hdel⟩ := ih (lt_min_iff.mp hlt).1 (lt_min_iff.mp hlt).2
    exact ⟨g, hg, hcost, hdel⟩
  have heq : c = min (same χ r) (other χ r) := by omega
  by_cases hab : same χ r ≤ other χ r
  · obtain ⟨ho, hd⟩ := count_discard χ r
    refine ⟨discard χ r, branch_discard hχ r, ?_, ?_⟩ <;> omega
  · obtain ⟨ho, hd⟩ := count_singleton χ r
    refine ⟨singleton χ r, branch_singleton hχ r, ?_, ?_⟩ <;> omega

end Budgets


section RootStep

open CommonMarkedForest

variable {I : Type u} (T : I → CommonMarkedForest.RootedTree.{u})
    (χ : Option (Σ i, (T i).V) → Fin 2) (hχ : TwoColor (joinGraph T) χ)

/-- Restrict the coloring to a branch. -/
def branchColor (i : I) (x : (T i).V) : Fin 2 := χ (some ⟨i, x⟩)

include hχ

lemma branchColor_proper (i : I) : TwoColor (T i).graph (branchColor T χ i) := by
  intro x y hxy
  exact hχ ((forestGraph_adj_same T i x y).mpr hxy)

lemma branchColor_root_ne (i : I) : branchColor T χ i (T i).root ≠ χ none :=
  hχ (show (joinGraph T).Adj (some ⟨i, (T i).root⟩) none from rfl)

variable [Fintype I]

lemma same_join : same χ none = 1 + ∑ i, other (branchColor T χ i) (T i).root := by
  rw [same, number_join]
  simp only [ite_true]
  congr 1
  apply sum_congr rfl
  intro i _
  apply number_congr
  intro x
  have h := branchColor_root_ne T χ hχ i
  change χ (some ⟨i, x⟩) = χ none ↔
    χ (some ⟨i, x⟩) ≠ branchColor T χ i (T i).root
  omega

lemma other_join : other χ none = ∑ i, same (branchColor T χ i) (T i).root := by
  rw [other, number_join]
  simp only [ne_eq, not_true_eq_false, ite_false, zero_add]
  apply sum_congr rfl
  intro i _
  apply number_congr
  intro x
  have h := branchColor_root_ne T χ hχ i
  change χ (some ⟨i, x⟩) ≠ χ none ↔
    χ (some ⟨i, x⟩) = branchColor T χ i (T i).root
  omega

/-- The induction step: distribute branch budgets, or use the endpoint star
and delete a controlled number of its retained branch roots. -/
lemma join_kernel (c : ℕ) (ha : c < same χ none) (hb : c < other χ none)
    (ih : ∀ (i : I) (h : ℕ),
      h < same (branchColor T χ i) (T i).root →
      h < other (branchColor T χ i) (T i).root →
      ∃ g : (T i).V → Part, Branch (T i).graph (T i).root g ∧
        g (T i).root = core ∧ count g odd ≤ h ∧ 2 * h ≤ removed g) :
    ∃ g : Option (Σ i, (T i).V) → Part,
      Branch (joinGraph T) none g ∧ g none = core ∧
        count g odd ≤ c ∧ 2 * c ≤ removed g := by
  let a := fun i => same (branchColor T χ i) (T i).root
  let b := fun i => other (branchColor T χ i) (T i).root
  have hA : c < ∑ i, a i := by simpa only [other_join T χ hχ] using hb
  have hB : c < 1 + ∑ i, b i := by simpa only [same_join T χ hχ] using ha
  by_cases hc : c ≤ ∑ i, min (a i) (b i)
  · obtain ⟨h, hle, heq⟩ := distribute_budget univ (fun i => min (a i) (b i)) c hc
    have hex (i : I) : ∃ g : (T i).V → Part, Branch (T i).graph (T i).root g ∧
        count g odd ≤ h i ∧ 2 * h i ≤ removed g :=
      budget_branch (T i).isTree.isConnected (T i).root (branchColor T χ i)
        (branchColor_proper T χ hχ i) (h i) (hle i) (ih i (h i))
    choose f hf hcost hdel using hex
    refine ⟨joinLabels T f, branch_join T f hf, rfl, ?_, ?_⟩
    · rw [count_join]
      simp only [reduceCtorEq, ite_false, zero_add]
      exact (sum_le_sum (fun i _ => hcost i)).trans heq.le
    · rw [removed_join]
      calc
        2 * c = ∑ i, 2 * h i := by rw [← heq, mul_sum]
        _ ≤ ∑ i, removed (f i) := sum_le_sum (fun i _ => hdel i)
  · obtain ⟨S, _hSP, hcost, hdel⟩ := star_budget a b c hA hB (by omega)
    let f : (i : I) → (T i).V → Part := fun i =>
      if b i < a i ∧ i ∉ S then singleton (branchColor T χ i) (T i).root
      else discard (branchColor T χ i) (T i).root
    have hf (i : I) : Branch (T i).graph (T i).root (f i) := by
      dsimp only [f]
      split_ifs
      · exact branch_singleton (branchColor_proper T χ hχ i) (T i).root
      · exact branch_discard (branchColor_proper T χ hχ i) (T i).root
    refine ⟨joinLabels T f, branch_join T f hf, rfl, ?_, ?_⟩
    · rw [count_join]
      simp only [reduceCtorEq, ite_false, zero_add]
      have heq : (∑ i, count (f i) odd) =
          ∑ i, if b i < a i ∧ i ∉ S then b i else a i := by
        apply sum_congr rfl
        intro i _
        dsimp only [f]
        split_ifs
        · exact (count_singleton (branchColor T χ i) (T i).root).1
        · exact (count_discard (branchColor T χ i) (T i).root).1
      rw [heq]
      exact hcost
    · rw [removed_join]
      have heq : (∑ i, removed (f i)) =
          ∑ i, if b i < a i ∧ i ∉ S then a i + b i - 1 else a i + b i := by
        apply sum_congr rfl
        intro i _
        dsimp only [f]
        split_ifs
        · have h := (count_singleton (branchColor T χ i) (T i).root).2
          change removed _ = same (branchColor T χ i) (T i).root +
            other (branchColor T χ i) (T i).root - 1
          omega
        · exact (count_discard (branchColor T χ i) (T i).root).2
      rw [heq]
      exact hdel

end RootStep


/-- **Strong rooted parity-kernel lemma**, in label form.  Both color classes
larger than `c` allow the core to contain any prescribed root. -/
theorem rooted_labels {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (r : V) (χ : V → Fin 2) (hχ : TwoColor G χ)
    (c : ℕ) (ha : c < same χ r) (hb : c < other χ r) :
    ∃ g : V → Part, Branch G r g ∧ g r = core ∧ count g odd ≤ c ∧ 2 * c ≤ removed g := by
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V c with
  | h n ih =>
    let T := rootFamily hG r
    let e := rootIso hG r
    let ψ : Option (Σ i, (T i).V) → Fin 2 := fun x => χ (e x)
    have hψ : TwoColor (joinGraph T) ψ := by
      intro x y hxy
      exact hχ (e.toHom.map_rel' hxy)
    have hsame : same ψ none = same χ r :=
      number_equiv e.toEquiv (fun x => χ x = χ r)
    have hother : other ψ none = other χ r :=
      number_equiv e.toEquiv (fun x => χ x ≠ χ r)
    have hrec (i : (G.induce {r}ᶜ).ConnectedComponent) (h : ℕ)
        (hA : h < same (branchColor T ψ i) (T i).root)
        (hB : h < other (branchColor T ψ i) (T i).root) :
        ∃ g : (T i).V → Part, Branch (T i).graph (T i).root g ∧
          g (T i).root = core ∧ count g odd ≤ h ∧ 2 * h ≤ removed g := by
      have hlt : Fintype.card (T i).V < n := by
        simpa only [T, hn] using rootFamily_smaller hG r i
      exact ih _ hlt (T i).isTree (T i).root (branchColor T ψ i)
        (branchColor_proper T ψ hψ i) h hA hB rfl
    obtain ⟨f, hf, hfr, hcost, hdel⟩ := join_kernel T ψ hψ c
      (by rw [hsame]; exact ha) (by rw [hother]; exact hb) hrec
    let g : V → Part := fun x => f (e.symm x)
    refine ⟨g, hf.map e, ?_, ?_, ?_⟩
    · have he : e.symm r = none := e.symm_apply_apply none
      change f (e.symm r) = core
      rw [he]
      exact hfr
    · change count (fun x => f (e.toEquiv.symm x)) odd ≤ c
      rw [count_map]
      exact hcost
    · change 2 * c ≤ removed (fun x => f (e.toEquiv.symm x))
      rw [removed_map]
      exact hdel


/-- Unrooted label form, including the case of a small color class. -/
theorem labels {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (c : ℕ) (hc : 2 * c < Fintype.card V) :
    ∃ (r : V) (g : V → Part), Branch G r g ∧ g r = core ∧
      count g odd ≤ c ∧ 2 * c ≤ removed g := by
  obtain ⟨r⟩ := hG.isConnected.nonempty
  let χ := hG.coloringTwo
  have hχ : TwoColor G χ := by
    intro x y h
    exact χ.valid h
  have hsmall (x : V) (hx : other χ x ≤ c) :
      ∃ (r : V) (g : V → Part), Branch G r g ∧ g r = core ∧
        count g odd ≤ c ∧ 2 * c ≤ removed g := by
    obtain ⟨ho, hd⟩ := count_singleton χ x
    have ht := same_add_other χ x
    refine ⟨x, singleton χ x, branch_singleton hχ x, by simp [singleton], ?_, ?_⟩ <;> omega
  by_cases hb : other χ r ≤ c
  · exact hsmall r hb
  by_cases ha : same χ r ≤ c
  · have hp : 0 < other χ r := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hp
    have hxr : χ x ≠ χ r := by simpa using hx
    have he : other χ x = same χ r := by
      apply number_congr
      intro y
      omega
    apply hsmall x
    rw [he]
    exact ha
  · obtain ⟨g, hg⟩ := rooted_labels hG r χ hχ c (by omega) (by omega)
    exact ⟨r, g, hg⟩

/-- A finite, distance-free parity-kernel certificate.  The three sets partition
the vertex type.  `U` is independent, and no edge from `W` goes to `R` or `W`. -/
structure IsParityKernel {V : Type u} [Fintype V] (G : SimpleGraph V) (c : ℕ)
    (R U W : Finset V) : Prop where
  disjointRU : Disjoint R U
  disjointRW : Disjoint R W
  disjointUW : Disjoint U W
  partition : R ∪ U ∪ W = univ
  nonempty : R.Nonempty
  connected : (G.induce (R : Set V)).Connected
  independent : G.IsIndepSet (U : Set V)
  neighbors : ∀ w ∈ W, G.neighborSet w ⊆ (U : Set V)
  odd_le : U.card ≤ c
  outside_ge : 2 * c ≤ U.card + W.card

/-- Convert the internal labels to the public finite-set interface. -/
lemma partition_of_labels {V : Type u} [Fintype V] {G : SimpleGraph V}
    {r : V} {g : V → Part} {c : ℕ} (hg : Branch G r g) (hr : g r = core)
    (hcost : count g odd ≤ c) (hdel : 2 * c ≤ removed g) :
    ∃ R U W : Finset V, IsParityKernel G c R U W ∧ r ∈ R := by
  let R := univ.filter (fun x => g x = core)
  let U := univ.filter (fun x => g x = odd)
  let W := univ.filter (fun x => g x = even)
  have hR : (R : Set V) = {x | g x = core} := by ext x; simp [R]
  refine ⟨R, U, W, ?_, by simp [R, hr]⟩
  refine
    { disjointRU := ?_
      disjointRW := ?_
      disjointUW := ?_
      partition := ?_
      nonempty := ⟨r, by simp [R, hr]⟩
      connected := by rw [hR]; exact hg.connected hr
      independent := ?_
      neighbors := ?_
      odd_le := ?_
      outside_ge := ?_ }
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' : g x = core := (mem_filter.mp hx).2
    have hy' : g x = odd := (mem_filter.mp hy).2
    exact Part.noConfusion (hx'.symm.trans hy')
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' : g x = core := (mem_filter.mp hx).2
    have hy' : g x = even := (mem_filter.mp hy).2
    exact Part.noConfusion (hx'.symm.trans hy')
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' : g x = odd := (mem_filter.mp hx).2
    have hy' : g x = even := (mem_filter.mp hy).2
    exact Part.noConfusion (hx'.symm.trans hy')
  · ext x
    cases hx : g x <;> simp [R, U, W, hx]
  · intro x hx y hy _ hxy
    exact (hg.edges hxy).2 (mem_filter.mp hx).2 (mem_filter.mp hy).2
  · intro w hw z hwz
    exact mem_filter.mpr ⟨mem_univ _, (hg.edges hwz).1 (mem_filter.mp hw).2⟩
  · simpa only [count, number_eq_filter, U] using hcost
  · simpa only [removed, count, number_eq_filter, U, W] using hdel

namespace IsParityKernel

variable {V : Type u} [Fintype V] {G : SimpleGraph V} {c : ℕ} {R U W : Finset V}
    (h : IsParityKernel G c R U W)

include h

lemma card_partition : R.card + U.card + W.card = Fintype.card V := by
  have hd : Disjoint (R ∪ U) W := disjoint_union_left.mpr ⟨h.disjointRW, h.disjointUW⟩
  have hc := congrArg Finset.card h.partition
  rwa [card_union_of_disjoint hd, card_union_of_disjoint h.disjointRU, card_univ] at hc

lemma outside_eq : univ \ R = U ∪ W := by
  ext x
  simp only [mem_sdiff, mem_univ, true_and, mem_union]
  constructor
  · intro hx
    have hxall : x ∈ R ∪ U ∪ W := h.partition.symm ▸ mem_univ x
    rcases mem_union.mp hxall with hxRU | hxW
    · exact Or.inl ((mem_union.mp hxRU).resolve_left hx)
    · exact Or.inr hxW
  · rintro (hxU | hxW) hxR
    · exact disjoint_left.mp h.disjointRU hxR hxU
    · exact disjoint_left.mp h.disjointRW hxR hxW

lemma outside_card : (univ \ R).card = U.card + W.card := by
  rw [h.outside_eq, card_union_of_disjoint h.disjointUW]

lemma outside_card_ge : 2 * c ≤ (univ \ R).card := by
  rw [h.outside_card]
  exact h.outside_ge

lemma core_card_bound : R.card + 2 * c ≤ Fintype.card V := by
  have := h.card_partition
  have := h.outside_ge
  omega

lemma proper (hc : 1 ≤ c) : R ⊂ univ := by
  apply ssubset_iff_subset_ne.mpr
  refine ⟨subset_univ _, ?_⟩
  intro he
  have hb := h.core_card_bound
  rw [he, card_univ] at hb
  omega

lemma induced_isTree (hG : G.IsTree) : (G.induce (R : Set V)).IsTree :=
  ⟨h.connected, hG.IsAcyclic.induce _⟩

lemma core_edges_le (hG : G.IsTree) {k : ℕ} (hk : G.edgeFinset.card = k) :
    (G.induce (R : Set V)).edgeFinset.card ≤ k - 2 * c := by
  have ht := (h.induced_isTree hG).card_edgeFinset
  have hg := hG.card_edgeFinset
  have hb := h.core_card_bound
  simp only [Finset.coe_sort_coe, Fintype.card_coe] at ht
  omega

end IsParityKernel


/-- **Rooted parity kernel.** If both classes of a proper two-coloring have
more than `c` vertices, the core can contain any prescribed vertex `r`.
The parameter `c = 0` is allowed. -/
theorem rooted_parity_kernel {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (χ : G.Coloring (Fin 2)) (r : V) (c : ℕ)
    (hlarge : ∀ i : Fin 2, c < (univ.filter (fun x => χ x = i)).card) :
    ∃ R U W : Finset V, IsParityKernel G c R U W ∧ r ∈ R := by
  have hclasses (i : Fin 2) : c < number (fun x => χ x = i) := by
    rw [number_eq_filter]
    exact hlarge i
  have hA : c < same χ r := hclasses (χ r)
  have hB : c < other χ r := by
    by_cases hr : χ r = 0
    · have he : other χ r = number (fun x => χ x = (1 : Fin 2)) := by
        apply number_congr
        intro x
        omega
      rw [he]
      exact hclasses 1
    · have he : other χ r = number (fun x => χ x = (0 : Fin 2)) := by
        apply number_congr
        intro x
        omega
      rw [he]
      exact hclasses 0
  obtain ⟨g, hg, hr, hcost, hdel⟩ := rooted_labels hG r χ
    (by intro x y h; exact χ.valid h) c hA hB
  exact partition_of_labels hg hr hcost hdel

/-- **Parity-kernel lemma, by vertex order.** Every finite tree on more than
`2*c` vertices admits a kernel deleting at least `2*c` vertices at cost at
most `c`.  No restriction on the sizes of its color classes is needed. -/
theorem exists_parity_kernel_of_card {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (c : ℕ) (hc : 2 * c < Fintype.card V) :
    ∃ R U W : Finset V, IsParityKernel G c R U W := by
  obtain ⟨r, g, hg, hr, hcost, hdel⟩ := labels hG c hc
  obtain ⟨R, U, W, h, _⟩ := partition_of_labels hg hr hcost hdel
  exact ⟨R, U, W, h⟩

/-- **Parity-kernel lemma for a `k`-edge tree.** The core is nonempty and
connected (in `IsParityKernel`), is proper, has at least `2*c` vertices
outside it, and induces a tree with at most `k - 2*c` edges.  The independent
separator `U` has at most `c` vertices and contains every neighbor of `W`. -/
theorem parity_kernel {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) {k c : ℕ} (hk : G.edgeFinset.card = k)
    (hc : 1 ≤ c) (hck : c ≤ k / 2) :
    ∃ R U W : Finset V, IsParityKernel G c R U W ∧ R ⊂ univ ∧
      2 * c ≤ (univ \ R).card ∧ (G.induce (R : Set V)).IsTree ∧
      (G.induce (R : Set V)).edgeFinset.card ≤ k - 2 * c := by
  have hcard : 2 * c < Fintype.card V := by
    have ht := hG.card_edgeFinset
    omega
  obtain ⟨R, U, W, h⟩ := exists_parity_kernel_of_card hG c hcard
  exact ⟨R, U, W, h, h.proper hc, h.outside_card_ge, h.induced_isTree hG,
    h.core_edges_le hG hk⟩

/-- The usual `Fin (k+1)` interface, with no separate edge-count hypothesis. -/
theorem parity_kernel_fin (k c : ℕ) (G : SimpleGraph (Fin (k + 1)))
    (hG : G.IsTree) (hc : 1 ≤ c) (hck : c ≤ k / 2) :
    ∃ R U W : Finset (Fin (k + 1)), IsParityKernel G c R U W ∧ R ⊂ univ ∧
      2 * c ≤ (univ \ R).card ∧ (G.induce (R : Set (Fin (k + 1)))).IsTree ∧
      (G.induce (R : Set (Fin (k + 1)))).edgeFinset.card ≤ k - 2 * c := by
  have hk : G.edgeFinset.card = k := by
    have ht := hG.card_edgeFinset
    simp only [Fintype.card_fin] at ht
    omega
  simpa only [Finset.card_sdiff, Finset.inter_univ] using parity_kernel hG hk hc hck

end TreeParityKernel

-- Transitive dependency audit of the completed kernel theorems.
#print axioms TreeParityKernel.rooted_labels
#print axioms TreeParityKernel.rooted_parity_kernel
#print axioms TreeParityKernel.exists_parity_kernel_of_card
#print axioms TreeParityKernel.parity_kernel
#print axioms TreeParityKernel.parity_kernel_fin
