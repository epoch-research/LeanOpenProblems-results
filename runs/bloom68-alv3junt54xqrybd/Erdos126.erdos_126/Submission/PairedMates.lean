import Submission.PairedCore
import Submission.PairedHall

/-!
# Capacity mates and orientations for coherent paired blocks

Only finite-set combinatorics are used here.  A deepest selected block is
chosen by the sum of its two side cardinalities.  Coherence then puts both
of its sides inside those of every selected block containing the row.
This also handles repeated blocks and equal finite sides.

The capacity Hall argument is in `Submission.PairedHall`.  Inactive rows
are assigned the singleton source/target pair `{i}, {i}`.  Active rows use
the two sides of a deepest witness, in the appropriate order.  Oppositely
oriented rows have disjoint sources and disjoint targets, since coherence
and validity prohibit any left/right overlap anywhere in the family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos126Aux.Paired

variable {ι τ : Type*}

/-- Coherence passes to any selected subfamily; there is no closure condition. -/
lemma Coherent.mono {b : τ → Block ι} {u v : Finset τ}
    (h : Coherent b u) (hv : v ⊆ u) : Coherent b v := by
  intro t ht s hs
  exact h t (hv ht) s (hv hs)

/-- No left side can meet any right side of a valid coherent family. -/
lemma Coherent.left_right_disjoint {b : τ → Block ι} {u : Finset τ}
    (h : Coherent b u) (hb : ∀ t ∈ u, (b t).Valid)
    {t v : τ} (ht : t ∈ u) (hv : v ∈ u) :
    Disjoint (b t).left (b v).right := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  rcases h t ht v hv with htv | hvt | hd
  · exact (hb v hv).2.2.1 i (htv.1 hi) hj
  · exact (hb t ht).2.2.1 i hi (hvt.2 hj)
  · exact (hd i (Or.inl hi)).2 hj

/-- An active vertex has a deepest paired witness: both sides are contained
in both sides of every selected block containing that vertex.

Minimizing the sum of the side cardinalities resolves ties in finite sides.
For disjoint sides this sum is precisely the cardinality of the support. -/
lemma Coherent.exists_deepest {b : τ → Block ι} {u : Finset τ}
    (h : Coherent b u) (i : ι)
    (hi : ∃ t ∈ u, i ∈ (b t).left ∨ i ∈ (b t).right) :
    ∃ t ∈ u, (i ∈ (b t).left ∨ i ∈ (b t).right) ∧
      ∀ v ∈ u, (i ∈ (b v).left ∨ i ∈ (b v).right) →
        (b t).left ⊆ (b v).left ∧ (b t).right ⊆ (b v).right := by
  classical
  let A := u.filter (fun t => i ∈ (b t).left ∨ i ∈ (b t).right)
  have hA : A.Nonempty := by
    obtain ⟨t, ht, hit⟩ := hi
    exact ⟨t, Finset.mem_filter.mpr ⟨ht, hit⟩⟩
  obtain ⟨t, htA, hmin⟩ :=
    A.exists_min_image (fun t => (b t).left.card + (b t).right.card) hA
  obtain ⟨ht, hit⟩ := Finset.mem_filter.mp htA
  refine ⟨t, ht, hit, ?_⟩
  intro v hv hiv
  rcases h t ht v hv with htv | hvt | hd
  · exact htv
  · exact paired_subset_of_size_le hvt (hmin v (Finset.mem_filter.mpr ⟨hv, hiv⟩))
  · obtain ⟨hvl, hvr⟩ := hd i hit
    exact False.elim (hiv.elim hvl hvr)

private def Inactive (b : τ → Block ι) (u : Finset τ) (i : ι) : Prop :=
  ∀ t ∈ u, i ∉ (b t).left ∧ i ∉ (b t).right

private def PairCompatible (S T U V : Finset ι) : Prop :=
  (S ⊆ U ∧ T ⊆ V) ∨ (U ⊆ S ∧ V ⊆ T) ∨
    (Disjoint S U ∧ Disjoint T V)

private lemma pairCompatible_symm {S T U V : Finset ι}
    (h : PairCompatible S T U V) : PairCompatible U V S T := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨h.1.symm, h.2.symm⟩)

private lemma pairCompatible_swap {S T U V : Finset ι}
    (h : PairCompatible S T U V) : PairCompatible T S V U := by
  rcases h with h | h | h
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
  · exact Or.inr (Or.inr ⟨h.2, h.1⟩)

private lemma coherent_pairCompatible {b : τ → Block ι} {u : Finset τ}
    (h : Coherent b u) {t v : τ} (ht : t ∈ u) (hv : v ∈ u) :
    PairCompatible (b t).left (b t).right (b v).left (b v).right := by
  rcases h t ht v hv with htv | hvt | hd
  · exact Or.inl htv
  · exact Or.inr (Or.inl hvt)
  · right; right
    constructor
    · exact Finset.disjoint_left.mpr (fun i hi hj => (hd i (Or.inl hi)).1 hj)
    · exact Finset.disjoint_left.mpr (fun i hi hj => (hd i (Or.inr hi)).2 hj)

/-- Internal data for a row, including its simultaneous coverage property. -/
private structure MateRow (b : τ → Block ι) (u : Finset τ) (c : ℕ) (i : ι) where
  source : Finset ι
  target : Finset ι
  mem_source : i ∈ source
  balanced : source.card ≤ c * target.card
  cover_left : ∀ t ∈ u, i ∈ (b t).left → target ⊆ (b t).right
  cover_right : ∀ t ∈ u, i ∈ (b t).right → target ⊆ (b t).left
  kind : (source = {i} ∧ target = {i} ∧ Inactive b u i) ∨
    (∃ t ∈ u, source = (b t).left ∧ target = (b t).right) ∨
    (∃ t ∈ u, source = (b t).right ∧ target = (b t).left)

private lemma exists_mateRow (b : τ → Block ι) (u : Finset τ) (c : ℕ)
    (hc : 1 ≤ c) (hb : ∀ t ∈ u, (b t).Valid) (h : Coherent b u)
    (hbal : ∀ t ∈ u, (b t).Balanced c) (i : ι) :
    Nonempty (MateRow b u c i) := by
  classical
  by_cases hi : ∃ t ∈ u, i ∈ (b t).left ∨ i ∈ (b t).right
  · obtain ⟨t, ht, hit, hdeep⟩ := h.exists_deepest i hi
    by_cases hil : i ∈ (b t).left
    · refine ⟨{
        source := (b t).left
        target := (b t).right
        mem_source := hil
        balanced := (hbal t ht).1
        cover_left := ?_
        cover_right := ?_
        kind := Or.inr (Or.inl ⟨t, ht, rfl, rfl⟩)
      }⟩
      · intro v hv hiv
        exact (hdeep v hv (Or.inl hiv)).2
      · intro v hv hiv
        exact False.elim ((hb v hv).2.2.1 i ((hdeep v hv (Or.inr hiv)).1 hil) hiv)
    · have hir : i ∈ (b t).right := hit.resolve_left hil
      refine ⟨{
        source := (b t).right
        target := (b t).left
        mem_source := hir
        balanced := (hbal t ht).2
        cover_left := ?_
        cover_right := ?_
        kind := Or.inr (Or.inr ⟨t, ht, rfl, rfl⟩)
      }⟩
      · intro v hv hiv
        exact False.elim ((hb v hv).2.2.1 i hiv ((hdeep v hv (Or.inl hiv)).2 hir))
      · intro v hv hiv
        exact (hdeep v hv (Or.inr hiv)).1
  · have hin : Inactive b u i := by
      intro t ht
      exact ⟨fun hil => hi ⟨t, ht, Or.inl hil⟩, fun hir => hi ⟨t, ht, Or.inr hir⟩⟩
    refine ⟨{
      source := {i}
      target := {i}
      mem_source := by simp
      balanced := by simpa using hc
      cover_left := ?_
      cover_right := ?_
      kind := Or.inl ⟨rfl, rfl, hin⟩
    }⟩
    · intro t ht hit
      exact False.elim ((hin t ht).1 hit)
    · intro t ht hit
      exact False.elim ((hin t ht).2 hit)

private lemma inactive_row_compatible {b : τ → Block ι} {u : Finset τ}
    {c : ℕ} {i j : ι} (hi : Inactive b u i) (r : MateRow b u c j) :
    PairCompatible {i} {i} r.source r.target := by
  classical
  rcases r.kind with h0 | ⟨t, ht, hS, hT⟩ | ⟨t, ht, hS, hT⟩
  · rw [h0.1, h0.2.1]
    by_cases hij : i = j
    · subst j
      exact Or.inl ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
    · exact Or.inr (Or.inr ⟨by simp [hij], by simp [hij]⟩)
  · rw [hS, hT]
    exact Or.inr (Or.inr ⟨Finset.disjoint_singleton_left.mpr (hi t ht).1,
      Finset.disjoint_singleton_left.mpr (hi t ht).2⟩)
  · rw [hS, hT]
    exact Or.inr (Or.inr ⟨Finset.disjoint_singleton_left.mpr (hi t ht).2,
      Finset.disjoint_singleton_left.mpr (hi t ht).1⟩)

private lemma mateRow_compatible {b : τ → Block ι} {u : Finset τ} {c : ℕ}
    (hb : ∀ t ∈ u, (b t).Valid) (h : Coherent b u)
    {i j : ι} (r : MateRow b u c i) (s : MateRow b u c j) :
    PairCompatible r.source r.target s.source s.target := by
  rcases r.kind with h0 | ⟨t, ht, hS, hT⟩ | ⟨t, ht, hS, hT⟩
  · rw [h0.1, h0.2.1]
    exact inactive_row_compatible h0.2.2 s
  · rcases s.kind with h0 | ⟨v, hv, hsS, hsT⟩ | ⟨v, hv, hsS, hsT⟩
    · rw [h0.1, h0.2.1]
      exact pairCompatible_symm (inactive_row_compatible h0.2.2 r)
    · rw [hS, hT, hsS, hsT]
      exact coherent_pairCompatible h ht hv
    · rw [hS, hT, hsS, hsT]
      exact Or.inr (Or.inr ⟨h.left_right_disjoint hb ht hv,
        (h.left_right_disjoint hb hv ht).symm⟩)
  · rcases s.kind with h0 | ⟨v, hv, hsS, hsT⟩ | ⟨v, hv, hsS, hsT⟩
    · rw [h0.1, h0.2.1]
      exact pairCompatible_symm (inactive_row_compatible h0.2.2 r)
    · rw [hS, hT, hsS, hsT]
      exact Or.inr (Or.inr ⟨(h.left_right_disjoint hb hv ht).symm,
        h.left_right_disjoint hb ht hv⟩)
    · rw [hS, hT, hsS, hsT]
      exact pairCompatible_swap (coherent_pairCompatible h ht hv)

private lemma MateRow.target_of_inactive {b : τ → Block ι} {u : Finset τ}
    {c : ℕ} {i : ι} (r : MateRow b u c i) (hi : Inactive b u i) :
    r.target = {i} := by
  rcases r.kind with h0 | ⟨t, ht, hS, hT⟩ | ⟨t, ht, hS, hT⟩
  · exact h0.2.1
  · exact False.elim ((hi t ht).1 (hS ▸ r.mem_source))
  · exact False.elim ((hi t ht).2 (hS ▸ r.mem_source))

/-- Simultaneous mates for every block of a balanced coherent finite family.
Every fiber has cardinality at most `c`, and inactive vertices self-mate.
The weights play no role in the construction. -/
theorem exists_capacity_mate_self [Fintype ι] [DecidableEq ι]
    (b : τ → Block ι) (u : Finset τ) (c : ℕ)
    (hc : 1 ≤ c) (hb : ∀ t ∈ u, (b t).Valid) (h : Coherent b u)
    (hbal : ∀ t ∈ u, (b t).Balanced c) :
    ∃ F : ι → ι,
      (∀ j, (Finset.univ.filter (fun i => F i = j)).card ≤ c) ∧
      (∀ t ∈ u,
        (∀ i, i ∈ (b t).left → F i ∈ (b t).right) ∧
        (∀ i, i ∈ (b t).right → F i ∈ (b t).left)) ∧
      ∀ i, (∀ t ∈ u, i ∉ (b t).left ∧ i ∉ (b t).right) → F i = i := by
  classical
  let row (i : ι) : MateRow b u c i := Classical.choice (exists_mateRow b u c hc hb h hbal i)
  obtain ⟨F, hcap, hF⟩ := exists_capacity_selection id Function.injective_id
    (fun i => (row i).source) (fun i => (row i).target) c
    (fun i => (row i).mem_source) (fun i => (row i).balanced)
    (fun i j => mateRow_compatible hb h (row i) (row j))
  refine ⟨F, hcap, ?_, ?_⟩
  · intro t ht
    exact ⟨fun i hi => (row i).cover_left t ht hi (hF i),
      fun i hi => (row i).cover_right t ht hi (hF i)⟩
  · intro i hi
    have hFi := hF i
    rw [(row i).target_of_inactive hi] at hFi
    exact Finset.mem_singleton.mp hFi

/-- The capacity mate API without the additional inactive self-mate conclusion. -/
theorem exists_capacity_mate [Fintype ι] [DecidableEq ι]
    (b : τ → Block ι) (u : Finset τ) (c : ℕ)
    (hc : 1 ≤ c) (hb : ∀ t ∈ u, (b t).Valid) (h : Coherent b u)
    (hbal : ∀ t ∈ u, (b t).Balanced c) :
    ∃ F : ι → ι,
      (∀ j, (Finset.univ.filter (fun i => F i = j)).card ≤ c) ∧
      ∀ t ∈ u,
        (∀ i, i ∈ (b t).left → F i ∈ (b t).right) ∧
        (∀ i, i ∈ (b t).right → F i ∈ (b t).left) := by
  obtain ⟨F, hcap, hcover, _⟩ := exists_capacity_mate_self b u c hc hb h hbal
  exact ⟨F, hcap, hcover⟩

/-- Select exactly the balanced nodes, with no ancestor/descendant closure
requirement.  Vertices outside all selected sides self-mate. -/
theorem exists_balanced_capacity_mate_self [Fintype ι] [DecidableEq ι]
    (b : τ → Block ι) (u : Finset τ) (c : ℕ)
    (hc : 1 ≤ c) (hb : ∀ t ∈ u, (b t).Valid) (h : Coherent b u) :
    ∃ F : ι → ι,
      (∀ j, (Finset.univ.filter (fun i => F i = j)).card ≤ c) ∧
      (∀ t ∈ u, (b t).Balanced c →
        (∀ i, i ∈ (b t).left → F i ∈ (b t).right) ∧
        (∀ i, i ∈ (b t).right → F i ∈ (b t).left)) ∧
      ∀ i, (∀ t ∈ u, (b t).Balanced c →
        i ∉ (b t).left ∧ i ∉ (b t).right) → F i = i := by
  classical
  let v := u.filter (fun t => (b t).Balanced c)
  have hv : v ⊆ u := Finset.filter_subset _ _
  obtain ⟨F, hcap, hcover, hinactive⟩ := exists_capacity_mate_self b v c hc
    (fun t ht => hb t (hv ht)) (h.mono hv)
    (fun t ht => (Finset.mem_filter.mp ht).2)
  refine ⟨F, hcap, ?_, ?_⟩
  · intro t ht hbt
    exact hcover t (Finset.mem_filter.mpr ⟨ht, hbt⟩)
  · intro i hi
    apply hinactive i
    intro t ht
    obtain ⟨htu, hbt⟩ := Finset.mem_filter.mp ht
    exact hi t htu hbt

/-- The filtered mate API: only balanced nodes impose mate constraints.
In particular, arbitrarily many omitted unbalanced nodes cause no problem. -/
theorem exists_balanced_capacity_mate [Fintype ι] [DecidableEq ι]
    (b : τ → Block ι) (u : Finset τ) (c : ℕ)
    (hc : 1 ≤ c) (hb : ∀ t ∈ u, (b t).Valid) (h : Coherent b u) :
    ∃ F : ι → ι,
      (∀ j, (Finset.univ.filter (fun i => F i = j)).card ≤ c) ∧
      ∀ t ∈ u, (b t).Balanced c →
        (∀ i, i ∈ (b t).left → F i ∈ (b t).right) ∧
        (∀ i, i ∈ (b t).right → F i ∈ (b t).left) := by
  obtain ⟨F, hcap, hcover, _⟩ := exists_balanced_capacity_mate_self b u c hc hb h
  exact ⟨F, hcap, hcover⟩

/-- A coherent family has a simultaneous orientation.  There is no finiteness
assumption on the vertex type, and no balance or capacity assumption.
The chosen vector is zero at vertices outside all sides. -/
theorem exists_orientation (b : τ → Block ι) (u : Finset τ)
    (hb : ∀ t ∈ u, (b t).Valid) (h : Coherent b u) :
    ∃ sigma : ι → ℝ,
      (∀ i, |sigma i| ≤ 1) ∧
      (∀ t ∈ u, ∀ i, i ∈ (b t).left → sigma i = 1) ∧
      (∀ t ∈ u, ∀ i, i ∈ (b t).right → sigma i = -1) := by
  classical
  let sigma : ι → ℝ := fun i =>
    if ∃ t ∈ u, i ∈ (b t).left then 1
    else if ∃ t ∈ u, i ∈ (b t).right then -1 else 0
  refine ⟨sigma, ?_, ?_, ?_⟩
  · intro i
    dsimp only [sigma]
    split_ifs <;> norm_num
  · intro t ht i hi
    have hil : ∃ t ∈ u, i ∈ (b t).left := ⟨t, ht, hi⟩
    simp [sigma, hil]
  · intro t ht i hi
    have hil : ¬ ∃ v ∈ u, i ∈ (b v).left := by
      rintro ⟨v, hv, hiv⟩
      exact Finset.disjoint_left.mp (h.left_right_disjoint hb hv ht) hiv hi
    have hir : ∃ t ∈ u, i ∈ (b t).right := ⟨t, ht, hi⟩
    simp [sigma, hil, hir]

end Erdos126Aux.Paired
