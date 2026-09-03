import Submission.DoubleCosetOrbital

/-! Criteria for a stabilizer refinement to be a genuine matching cover.
These are conditional group-theoretic statements, not an extremal construction. -/
noncomputable section
open Classical SimpleGraph
namespace Erdos714DoubleCoset
variable {Γ : Type*} [Group Γ]

/-- On the old edge stabilizer, the two new stabilizers have the same kernel. -/
def FiberCompatible (H K H₀ K₀ : Subgroup Γ) (g : Γ) : Prop :=
  ∀ d ∈ H, g*d*g⁻¹ ∈ K → (d ∈ H₀ ↔ g*d*g⁻¹ ∈ K₀)

/-- The old edge stabilizer reaches every new sheet on the left. -/
def LeftSaturated (H K H₀ : Subgroup Γ) (g : Γ) : Prop :=
  ∀ h ∈ H, ∃ d ∈ H, g*d*g⁻¹ ∈ K ∧ d*h ∈ H₀

lemma compatible_cosets {H K H₀ K₀ : Subgroup Γ} {g s t : Γ}
    (hc : FiberCompatible H K H₀ K₀ g)
    (hH : coset H s = coset H t) (hK : coset K (g*s) = coset K (g*t)) :
    coset H₀ s = coset H₀ t ↔ coset K₀ (g*s) = coset K₀ (g*t) := by
  have hh := (coset_eq H s t).mp hH
  have hk : g*(t*s⁻¹)*g⁻¹ ∈ K := by
    convert (coset_eq K (g*s) (g*t)).mp hK using 1; group
  rw [coset_eq, coset_eq]
  convert hc (t*s⁻¹) hh hk using 1; group

lemma forget_rel {H K H₀ K₀ : Subgroup Γ} {g : Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) {x : Cosets H₀} {y : Cosets K₀}
    (h : Rel H₀ K₀ g x y) : Rel H K g (forget hH x) (forget hK y) := by
  obtain ⟨t, rfl, rfl⟩ := h
  exact ⟨t,rfl,rfl⟩

/-- Two neighbors of the same refined left vertex cannot lie above one old
right vertex when the edge-stabilizer kernels agree. -/
theorem matching_left_unique {H K H₀ K₀ : Subgroup Γ} {g : Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hc : FiberCompatible H K H₀ K₀ g)
    {x : Cosets H₀} {y z : Cosets K₀}
    (hy : Rel H₀ K₀ g x y) (hz : Rel H₀ K₀ g x z)
    (he : forget hK y = forget hK z) : y = z := by
  obtain ⟨s,hs,rfl⟩ := hy
  obtain ⟨t,ht,rfl⟩ := hz
  have h₀ : coset H₀ s = coset H₀ t := hs.trans ht.symm
  have h₁ : coset H s = coset H t := congrArg (forget hH) h₀
  exact (compatible_cosets hc h₁ he).mp h₀

/-- The analogous injectivity holds on the other side. -/
theorem matching_right_unique {H K H₀ K₀ : Subgroup Γ} {g : Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hc : FiberCompatible H K H₀ K₀ g)
    {x z : Cosets H₀} {y : Cosets K₀}
    (hx : Rel H₀ K₀ g x y) (hz : Rel H₀ K₀ g z y)
    (he : forget hH x = forget hH z) : x = z := by
  obtain ⟨s,rfl,hs⟩ := hx
  obtain ⟨t,rfl,ht⟩ := hz
  have h₀ : coset K₀ (g*s) = coset K₀ (g*t) := hs.trans ht.symm
  have h₁ : coset K (g*s) = coset K (g*t) := congrArg (forget hK) h₀
  exact (compatible_cosets hc he h₁).mpr h₀

/-- Saturation gives existence above every old neighbor, for any specified
refined left vertex. It does not require normality of the subgroups. -/
theorem matching_left_exists {H K H₀ K₀ : Subgroup Γ} {g : Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hsat : LeftSaturated H K H₀ g)
    (x : Cosets H₀) (y : Cosets K) (he : Rel H K g (forget hH x) y) :
    ∃ z : Cosets K₀, Rel H₀ K₀ g x z ∧ forget hK z = y := by
  induction x using Quotient.inductionOn with
  | h s =>
    obtain ⟨t,ht,rfl⟩ := he
    have hh : t*s⁻¹ ∈ H := by
      have h := H.inv_mem ((coset_eq H t s).mp ht)
      simpa only [mul_inv_rev,inv_inv] using h
    obtain ⟨d,hd,hkd,hdh⟩ := hsat (t*s⁻¹) hh
    refine ⟨coset K₀ (g*(d*t)), ⟨d*t, ?_, rfl⟩, ?_⟩
    · apply (coset_eq H₀ (d*t) s).mpr
      convert H₀.inv_mem hdh using 1; group
    · apply (coset_eq K (g*(d*t)) (g*t)).mpr
      convert K.inv_mem hkd using 1; group

/-- Together the two conditions give a unique lifted neighbor, not merely
a unique edge above an old edge without specified sheet. -/
theorem matching_left_exists_unique {H K H₀ K₀ : Subgroup Γ} {g : Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hc : FiberCompatible H K H₀ K₀ g)
    (hsat : LeftSaturated H K H₀ g)
    (x : Cosets H₀) (y : Cosets K) (he : Rel H K g (forget hH x) y) :
    ∃! z : Cosets K₀, Rel H₀ K₀ g x z ∧ forget hK z = y := by
  obtain ⟨z,hz,hzy⟩ := matching_left_exists hH hK hsat x y he
  refine ⟨z,⟨hz,hzy⟩,?_⟩
  rintro w ⟨hw,hwy⟩
  exact matching_left_unique hH hK hc hw hz (hwy.trans hzy.symm)

/-- Exact equivalence of row neighborhoods for such a matching cover. -/
def rowNeighborsEquiv {H K H₀ K₀ : Subgroup Γ} {g : Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hc : FiberCompatible H K H₀ K₀ g)
    (hsat : LeftSaturated H K H₀ g) (x : Cosets H₀) :
    {y : Cosets K₀ // Rel H₀ K₀ g x y} ≃
      {y : Cosets K // Rel H K g (forget hH x) y} := by
  let f : {y : Cosets K₀ // Rel H₀ K₀ g x y} →
      {y : Cosets K // Rel H K g (forget hH x) y} :=
    fun y => ⟨forget hK y.val, forget_rel hH hK y.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro y z he
    apply Subtype.ext
    exact matching_left_unique hH hK hc y.property z.property (congrArg Subtype.val he)
  · intro y
    obtain ⟨z,hz,hzy⟩ := matching_left_exists hH hK hsat x y.val y.property
    exact ⟨⟨z,hz⟩,Subtype.ext hzy⟩

/-- The row relation is precisely the actual graph neighborhood. -/
def rowNeighborTypeEquiv (H K : Subgroup Γ) (g : Γ) (x : Cosets H) :
    {y : Cosets K // Rel H K g x y} ≃ (graph H K g).neighborSet (.inl x) := by
  let f : {y : Cosets K // Rel H K g x y} →
      (graph H K g).neighborSet (.inl x) := fun y => ⟨.inr y.val,y.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro y z he
    apply Subtype.ext
    exact Sum.inr.inj (congrArg Subtype.val he)
  · rintro ⟨y,hy⟩
    cases y with
    | inl y => exact False.elim hy
    | inr y => exact ⟨⟨y,hy⟩,rfl⟩

/-- A genuine matching refinement preserves each left degree exactly. -/
def matchingNeighborEquiv {H K H₀ K₀ : Subgroup Γ} {g : Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hc : FiberCompatible H K H₀ K₀ g)
    (hsat : LeftSaturated H K H₀ g) (x : Cosets H₀) :
    (graph H₀ K₀ g).neighborSet (.inl x) ≃
      (graph H K g).neighborSet (.inl (forget hH x)) :=
  (rowNeighborTypeEquiv H₀ K₀ g x).symm.trans
    ((rowNeighborsEquiv hH hK hc hsat x).trans
      (rowNeighborTypeEquiv H K g (forget hH x)))

theorem matching_neighbor_card {H K H₀ K₀ : Subgroup Γ} {g : Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hc : FiberCompatible H K H₀ K₀ g)
    (hsat : LeftSaturated H K H₀ g) (x : Cosets H₀) :
    Nat.card ((graph H₀ K₀ g).neighborSet (.inl x)) =
      Nat.card ((graph H K g).neighborSet (.inl (forget hH x))) :=
  Nat.card_congr (matchingNeighborEquiv hH hK hc hsat x)

/-- At relative index two, one edge-stabilizer element outside the smaller
left stabilizer already supplies all left sheets. -/
theorem index_two_leftSaturated {H K H₀ : Subgroup Γ} {g d : Γ}
    (hi : H₀.relIndex H = 2) (hd : d ∈ H) (hk : g*d*g⁻¹ ∈ K)
    (hn : d ∉ H₀) : LeftSaturated H K H₀ g := by
  intro h hh
  by_cases hh₀ : h ∈ H₀
  · exact ⟨1,H.one_mem,by simp,by simpa using hh₀⟩
  · refine ⟨d,hd,hk,?_⟩
    have hm := (Subgroup.mul_mem_iff_of_index_two
      (H := H₀.subgroupOf H) hi (a := (⟨d,hd⟩ : H)) (b := (⟨h,hh⟩ : H)))
    simpa only [Subgroup.mem_subgroupOf,Subgroup.coe_mul] using
      hm.mpr (iff_of_false hn hh₀)

lemma fiberCompatible_swap {H K H₀ K₀ : Subgroup Γ} {g : Γ}
    (hc : FiberCompatible H K H₀ K₀ g) : FiberCompatible K H K₀ H₀ g⁻¹ := by
  intro d hd hkd
  have he : g*(g⁻¹*d*(g⁻¹)⁻¹)*g⁻¹ = d := by group
  have hh := hc (g⁻¹*d*(g⁻¹)⁻¹) hkd (he.symm ▸ hd)
  rw [he] at hh
  exact hh.symm

lemma rel_swap (H K : Subgroup Γ) (g : Γ) (x : Cosets H) (y : Cosets K) :
    Rel H K g x y ↔ Rel K H g⁻¹ y x := by
  constructor
  · rintro ⟨t,ht,hy⟩
    exact ⟨g*t,hy,by simpa only [inv_mul_cancel_left] using ht⟩
  · rintro ⟨t,ht,hy⟩
    exact ⟨g⁻¹*t,hy,by simpa only [mul_inv_cancel_left] using ht⟩

/-- With both relative indices two and the diagonal kernel condition, the
same odd stabilizer element gives unique lifts at either specified endpoint. -/
theorem index_two_right_exists_unique {H K H₀ K₀ : Subgroup Γ} {g d : Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hc : FiberCompatible H K H₀ K₀ g)
    (hiK : K₀.relIndex K = 2) (hd : d ∈ H) (hk : g*d*g⁻¹ ∈ K) (hn : d ∉ H₀)
    (x : Cosets H) (y : Cosets K₀) (he : Rel H K g x (forget hK y)) :
    ∃! z : Cosets H₀, Rel H₀ K₀ g z y ∧ forget hH z = x := by
  have hkn : g*d*g⁻¹ ∉ K₀ := fun h => hn ((hc d hd hk).mpr h)
  have hconj : g⁻¹*(g*d*g⁻¹)*(g⁻¹)⁻¹ = d := by group
  have hs : LeftSaturated K H K₀ g⁻¹ :=
    index_two_leftSaturated hiK hk (hconj.symm ▸ hd) hkn
  obtain ⟨z,⟨hz,hzx⟩,hu⟩ := matching_left_exists_unique hK hH
    (fiberCompatible_swap hc) hs y x ((rel_swap H K g x _).mp he)
  refine ⟨z,⟨(rel_swap H₀ K₀ g z y).mpr hz,hzx⟩,?_⟩
  intro w hw
  exact hu w ⟨(rel_swap H₀ K₀ g w y).mp hw.1,hw.2⟩

/-- A trivial old edge stabilizer cannot reach extra sheets: in that case
left saturation is equivalent to not refining the left stabilizer at all. -/
theorem freePair_leftSaturated_iff {H K H₀ : Subgroup Γ} {g : Γ}
    (hH : H₀ ≤ H) (hf : FreePair H K g) :
    LeftSaturated H K H₀ g ↔ H₀ = H := by
  constructor
  · intro hs
    apply le_antisymm hH
    intro h hh
    obtain ⟨d,hd,hk,hh₀⟩ := hs h hh
    have he := hf d hd hk
    simpa [he] using hh₀
  · rintro rfl h hh
    exact ⟨1,by simp,by simp,by simpa using hh⟩

end Erdos714DoubleCoset
#print axioms Erdos714DoubleCoset.matching_left_unique
#print axioms Erdos714DoubleCoset.matching_right_unique
#print axioms Erdos714DoubleCoset.matching_left_exists_unique
#print axioms Erdos714DoubleCoset.rowNeighborsEquiv
#print axioms Erdos714DoubleCoset.freePair_leftSaturated_iff

#print axioms Erdos714DoubleCoset.matching_neighbor_card

#print axioms Erdos714DoubleCoset.index_two_leftSaturated
#print axioms Erdos714DoubleCoset.index_two_right_exists_unique
