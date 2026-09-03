import FormalConjecturesUtil

/-! A rank bound for the zero set of one binary linear functional. The proof
minimizes the common-zero rank of a pair and perturbs the pair. -/
namespace Erdos66BinaryZeroSpan
open Module
open scoped Classical
set_option maxHeartbeats 1600000

abbrev F := ZMod 2

lemma bit_cases (x : F) : x=0 ∨ x=1 := by fin_cases x <;> simp

lemma bit_eq_of_add_eq_zero (x y : F) (h : x+y=0) : x=y := by
  rcases bit_cases x with hx | hx <;> rcases bit_cases y with hy | hy <;> simp_all

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

noncomputable def fiber (S : Finset V) (f g : Module.Dual F V) (a b : F) : Finset V :=
  S.filter (fun x ↦ f x=a ∧ g x=b)

noncomputable def partSpan (S : Finset V) (f g : Module.Dual F V) (a b : F) : Submodule F V :=
  Submodule.span F (fiber S f g a b : Set V)

noncomputable def zeroSpan (S : Finset V) (f : Module.Dual F V) : Submodule F V :=
  Submodule.span F (S.filter (fun x ↦ f x=0) : Set V)

lemma mem_fiber (S : Finset V) (f g : Module.Dual F V) (a b : F) (x : V) :
    x∈fiber S f g a b ↔ x∈S ∧ f x=a ∧ g x=b := by
  simp only [fiber,Finset.mem_filter]

lemma minimum_pair (S : Finset V) :
    ∃ f g : Module.Dual F V, ∀ f' g' : Module.Dual F V,
      finrank F (partSpan S f g 0 0)≤finrank F (partSpan S f' g' 0 0) := by
  have h : ∃ n : ℕ, ∃ f g : Module.Dual F V, finrank F (partSpan S f g 0 0)=n :=
    ⟨_,0,0,rfl⟩
  obtain ⟨f,g,hfg⟩ := Nat.find_spec h
  refine ⟨f,g,fun f' g' ↦ ?_⟩
  rw [hfg]
  exact Nat.find_min' h ⟨f',g',rfl⟩

/-- At a minimum common-zero rank, the common-zero span is contained in the
span of every other cell of the two-functional partition. -/
lemma minimum_common_le_part (S : Finset V) (f g : Module.Dual F V)
    (hmin : ∀ f' g' : Module.Dual F V,
      finrank F (partSpan S f g 0 0)≤finrank F (partSpan S f' g' 0 0)) (a b : F) :
    partSpan S f g 0 0 ≤ partSpan S f g a b := by
  by_contra hn
  obtain ⟨x,hxW,hxP⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨h,hx,hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxP inferInstance
  have hzero (v : V) (hv : v∈partSpan S f g a b) : h v=0 := by
    have hm : h v∈(partSpan S f g a b).map h := Submodule.mem_map_of_mem hv
    rw [hmap] at hm
    exact hm
  let f' := f+a • h
  let g' := g+b • h
  have hle : partSpan S f' g' 0 0≤partSpan S f g 0 0 ⊓ h.ker := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨hvS,hvf,hvg⟩ := (mem_fiber S f' g' 0 0 v).mp hv
    have hf : f v+a*h v=0 := by simpa [f',LinearMap.smul_apply,smul_eq_mul] using hvf
    have hg : g v+b*h v=0 := by simpa [g',LinearMap.smul_apply,smul_eq_mul] using hvg
    have hhv : h v=0 := by
      rcases bit_cases (h v) with hz | hz
      · exact hz
      · have hfa : f v=a := by
          rw [hz,mul_one] at hf
          exact bit_eq_of_add_eq_zero _ _ hf
        have hgb : g v=b := by
          rw [hz,mul_one] at hg
          exact bit_eq_of_add_eq_zero _ _ hg
        have hp : v∈partSpan S f g a b :=
          Submodule.subset_span ((mem_fiber S f g a b v).mpr ⟨hvS,hfa,hgb⟩)
        have hh := hzero v hp
        exact False.elim (one_ne_zero (hz.symm.trans hh))
    have hvf0 : f v=0 := by simpa only [hhv,mul_zero,add_zero] using hf
    have hvg0 : g v=0 := by simpa only [hhv,mul_zero,add_zero] using hg
    exact ⟨Submodule.subset_span ((mem_fiber S f g 0 0 v).mpr ⟨hvS,hvf0,hvg0⟩),hhv⟩
  have hlt : partSpan S f g 0 0 ⊓ h.ker < partSpan S f g 0 0 := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hm : x∈partSpan S f g 0 0 ⊓ h.ker := he.symm ▸ hxW
    exact hx hm.2
  have hr := (Submodule.finrank_mono hle).trans_lt (Submodule.finrank_lt_finrank_of_lt hlt)
  exact (not_lt_of_ge (hmin f' g')) hr

lemma zeroSpan_le_part01 (S : Finset V) (f g : Module.Dual F V)
    (h : partSpan S f g 0 0≤partSpan S f g 0 1) :
    zeroSpan S f≤partSpan S f g 0 1 := by
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨hxS,hxf⟩ := Finset.mem_filter.mp hx
  rcases bit_cases (g x) with hxg | hxg
  · exact h (Submodule.subset_span ((mem_fiber S f g 0 0 x).mpr ⟨hxS,hxf,hxg⟩))
  · exact Submodule.subset_span ((mem_fiber S f g 0 1 x).mpr ⟨hxS,hxf,hxg⟩)

lemma zeroSpan_le_part10 (S : Finset V) (f g : Module.Dual F V)
    (h : partSpan S f g 0 0≤partSpan S f g 1 0) :
    zeroSpan S g≤partSpan S f g 1 0 := by
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨hxS,hxg⟩ := Finset.mem_filter.mp hx
  rcases bit_cases (f x) with hxf | hxf
  · exact h (Submodule.subset_span ((mem_fiber S f g 0 0 x).mpr ⟨hxS,hxf,hxg⟩))
  · exact Submodule.subset_span ((mem_fiber S f g 1 0 x).mpr ⟨hxS,hxf,hxg⟩)

lemma zeroSpan_le_part11 (S : Finset V) (f g : Module.Dual F V)
    (h : partSpan S f g 0 0≤partSpan S f g 1 1) :
    zeroSpan S (f+g)≤partSpan S f g 1 1 := by
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨hxS,hxs⟩ := Finset.mem_filter.mp hx
  change f x+g x=0 at hxs
  rcases bit_cases (f x) with hxf | hxf <;> rcases bit_cases (g x) with hxg | hxg
  · exact h (Submodule.subset_span ((mem_fiber S f g 0 0 x).mpr ⟨hxS,hxf,hxg⟩))
  · simp [hxf,hxg] at hxs
  · simp [hxf,hxg] at hxs
  · exact Submodule.subset_span ((mem_fiber S f g 1 1 x).mpr ⟨hxS,hxf,hxg⟩)

lemma fiber_disjoint (S : Finset V) (f g : Module.Dual F V) (a b c d : F)
    (h : a≠c ∨ b≠d) : Disjoint (fiber S f g a b) (fiber S f g c d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨_,hxa,hxb⟩ := (mem_fiber S f g a b x).mp hx
  obtain ⟨_,hxc,hxd⟩ := (mem_fiber S f g c d x).mp hy
  rcases h with h | h
  · exact h (hxa.symm.trans hxc)
  · exact h (hxb.symm.trans hxd)

lemma three_fiber_card_le (S : Finset V) (f g : Module.Dual F V) :
    (fiber S f g 0 1).card+(fiber S f g 1 0).card+(fiber S f g 1 1).card≤S.card := by
  have hd : Disjoint (fiber S f g 0 1) (fiber S f g 1 0) :=
    fiber_disjoint S f g 0 1 1 0 (Or.inl zero_ne_one)
  have hd' : Disjoint (fiber S f g 0 1 ∪ fiber S f g 1 0) (fiber S f g 1 1) := by
    rw [Finset.disjoint_union_left]
    exact ⟨fiber_disjoint S f g 0 1 1 1 (Or.inl zero_ne_one),
      fiber_disjoint S f g 1 0 1 1 (Or.inr zero_ne_one)⟩
  have hs : (fiber S f g 0 1 ∪ fiber S f g 1 0) ∪ fiber S f g 1 1⊆S := by
    exact Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (Finset.filter_subset _ _)
  have hh := Finset.card_le_card hs
  rwa [Finset.card_union_of_disjoint hd',Finset.card_union_of_disjoint hd] at hh

/-- Every finite binary vector family has a linear functional whose zero
vectors span dimension at most one third of the family's cardinality. -/
theorem exists_small_zero_span (S : Finset V) :
    ∃ f : Module.Dual F V, 3*finrank F (zeroSpan S f)≤S.card := by
  obtain ⟨f,g,hmin⟩ := minimum_pair S
  have h01 := zeroSpan_le_part01 S f g (minimum_common_le_part S f g hmin 0 1)
  have h10 := zeroSpan_le_part10 S f g (minimum_common_le_part S f g hmin 1 0)
  have h11 := zeroSpan_le_part11 S f g (minimum_common_le_part S f g hmin 1 1)
  have hr (a b : F) : finrank F (partSpan S f g a b)≤(fiber S f g a b).card :=
    finrank_span_finset_le_card _
  have h₁ := (Submodule.finrank_mono h01).trans (hr 0 1)
  have h₂ := (Submodule.finrank_mono h10).trans (hr 1 0)
  have h₃ := (Submodule.finrank_mono h11).trans (hr 1 1)
  have hc := three_fiber_card_le S f g
  have hcases : 3*finrank F (zeroSpan S f)≤S.card ∨
      3*finrank F (zeroSpan S g)≤S.card ∨
      3*finrank F (zeroSpan S (f+g))≤S.card := by omega
  rcases hcases with h | h | h
  · exact ⟨f,h⟩
  · exact ⟨g,h⟩
  · exact ⟨f+g,h⟩

end Erdos66BinaryZeroSpan
