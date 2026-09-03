import FormalConjecturesUtil

/-!
# Algebra for a finite-field origin repair

This file concerns only a finite-field analogue of Erdős Problem 66.
It does not construct a subset of the natural numbers.
-/

namespace Erdos66OriginRepair

variable {K F : Type*} [Field K] [Field F]

/-- An odd-degree field extension has no new elements whose square lies in the base field. -/
lemma square_in_base_of_odd_finrank [Algebra K F] [FiniteDimensional K F]
    (hdeg : Odd (Module.finrank K F)) {x : F}
    (hx : x ^ 2 ∈ (algebraMap K F).range) : x ∈ (algebraMap K F).range := by
  obtain ⟨a, ha⟩ := hx
  have hi : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hp : Polynomial.aeval x (Polynomial.X ^ 2 - Polynomial.C a) = 0 := by
    simp [ha]
  have hd : (minpoly K x).natDegree ≤ 2 := by
    have hh := Polynomial.natDegree_le_of_dvd (minpoly.dvd K x hp)
      (Polynomial.monic_X_pow_sub_C a (by norm_num : (2 : ℕ) ≠ 0)).ne_zero
    simpa only [Polynomial.natDegree_X_pow_sub_C] using hh
  have hpos := minpoly.natDegree_pos hi
  have hne : (minpoly K x).natDegree ≠ 2 := by
    intro heq
    have hdiv := minpoly.degree_dvd hi
    rw [heq] at hdiv
    exact hdeg.not_two_dvd_nat hdiv
  exact minpoly.natDegree_eq_one_iff.mp (by omega)

lemma subfield_square_closed_of_odd_finrank (k : Subfield F) [FiniteDimensional k F]
    (hdeg : Odd (Module.finrank k F)) {x : F} (hx : x ^ 2 ∈ k) : x ∈ k := by
  have hh : x ^ 2 ∈ (algebraMap k F).range := ⟨⟨x ^ 2, hx⟩, rfl⟩
  obtain ⟨a, ha⟩ := square_in_base_of_odd_finrank hdeg hh
  change (a : F) = x at ha
  exact ha ▸ a.property

/-- No affine line over `k` contains three distinct elements of `D`. -/
def IsCap (k : Subfield F) (D : Finset F) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, a ≠ b → ∀ d ∈ D,
    (d - a) / (b - a) ∈ k → d = a ∨ d = b

lemma parabola_ratio_mem (k : Subfield F)
    (hclosed : ∀ x : F, x ^ 2 ∈ k → x ∈ k)
    (u v t s a d : F) (hu : u ∈ k) (hv : v ∈ k)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hs : s ≠ 0)
    (ha : s = (t - a) ^ 2 / u) (hd : s = (t - d) ^ 2 / v) :
    (t - d) / (t - a) ∈ k := by
  have ha' : (t - a) ^ 2 = s * u := (div_eq_iff hu0).mp ha.symm
  have hd' : (t - d) ^ 2 = s * v := (div_eq_iff hv0).mp hd.symm
  apply hclosed
  have he : ((t - d) / (t - a)) ^ 2 = v / u := by
    rw [div_pow, ha', hd']
    field_simp
  rw [he]
  exact k.div_mem hv hu

lemma difference_ratio_mem (k : Subfield F) (t a b d : F)
    (hta : t - a ≠ 0)
    (hb : (t - b) / (t - a) ∈ k) (hd : (t - d) / (t - a) ∈ k) :
    (d - a) / (b - a) ∈ k := by
  have hratio (x : F) : 1 - (t - x) / (t - a) = (x - a) / (t - a) := by
    field_simp
    ring
  have he : (d - a) / (b - a) =
      (1 - (t - d) / (t - a)) / (1 - (t - b) / (t - a)) := by
    rw [hratio, hratio, div_div_div_comm, div_self hta, div_one]
  rw [he]
  exact k.div_mem (k.sub_mem k.one_mem hd) (k.sub_mem k.one_mem hb)

/-- Horizontal translates indexed by a cap can cover any point at most twice. -/
lemma cap_parabola_intersection_le_two [DecidableEq F]
    (k : Subfield F) (hclosed : ∀ x : F, x ^ 2 ∈ k → x ∈ k)
    (U D : Finset F) (hU : ∀ u ∈ U, u ∈ k ∧ u ≠ 0)
    (hD : IsCap k D) (t s : F) :
    (D.filter (fun d ↦ ∃ u ∈ U, s = (t - d) ^ 2 / u)).card ≤ 2 := by
  classical
  by_contra hbad
  have hbad' : 2 < (D.filter (fun d ↦ ∃ u ∈ U, s = (t - d) ^ 2 / u)).card := by omega
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.mp hbad' 
  obtain ⟨haD, u, hu, ha⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbD, v, hv, hb⟩ := Finset.mem_filter.mp hb
  obtain ⟨hdD, w, hw, hd⟩ := Finset.mem_filter.mp hd
  have hs : s ≠ 0 := by
    intro hs
    have ha0 : t - a = 0 := eq_zero_of_pow_eq_zero (((div_eq_zero_iff).mp (ha.symm.trans hs)).resolve_right (hU u hu).2)
    have hb0 : t - b = 0 := eq_zero_of_pow_eq_zero (((div_eq_zero_iff).mp (hb.symm.trans hs)).resolve_right (hU v hv).2)
    exact hab (by linear_combination hb0 - ha0)
  have hta : t - a ≠ 0 := by
    intro hh
    apply hs
    simpa only [hh, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] using ha
  have hv' := parabola_ratio_mem k hclosed u v t s a b (hU u hu).1 (hU v hv).1
    (hU u hu).2 (hU v hv).2 hs ha hb
  have hw' := parabola_ratio_mem k hclosed u w t s a d (hU u hu).1 (hU w hw).1
    (hU u hu).2 (hU w hw).2 hs ha hd
  have hdab := difference_ratio_mem k t a b d hta hv' hw'
  rcases hD a haD b hbD hab d hdD hdab with h | h
  · exact had h.symm
  · exact hbd h.symm

section Circle
variable {L : Type*} [Field L]

/-- An algebraic unit circle; the usual quadratic-extension conjugation is an example. -/
def OnCircle (σ : L →+* L) (x : L) : Prop := x * σ x = 1

lemma circle_ne_zero (σ : L →+* L) {x : L} (hx : OnCircle σ x) : x ≠ 0 := by
  intro he
  simp [OnCircle, he] at hx

lemma circle_conjugate_eq_inv (σ : L →+* L) {x : L} (hx : OnCircle σ x) :
    σ x = x⁻¹ := by
  have h0 := circle_ne_zero σ hx
  apply mul_left_cancel₀ h0
  rw [mul_inv_cancel₀ h0]
  exact hx

/-- A nonzero sum of two points of a unit circle determines that unordered pair. -/
lemma circle_pair_unique (σ : L →+* L) {a b c d : L}
    (ha : OnCircle σ a) (hb : OnCircle σ b) (hc : OnCircle σ c) (hd : OnCircle σ d)
    (hp : a + b ≠ 0) (hs : a + b = c + d) : a = c ∨ a = d := by
  have ha0 := circle_ne_zero σ ha
  have hb0 := circle_ne_zero σ hb
  have hc0 := circle_ne_zero σ hc
  have hd0 := circle_ne_zero σ hd
  have hinv : a⁻¹ + b⁻¹ = c⁻¹ + d⁻¹ := by
    have hh := congrArg σ hs
    simpa only [map_add, circle_conjugate_eq_inv σ ha, circle_conjugate_eq_inv σ hb,
      circle_conjugate_eq_inv σ hc, circle_conjugate_eq_inv σ hd] using hh
  have hm : (a + b) * (c * d) = (c + d) * (a * b) := by
    field_simp at hinv
    linear_combination hinv
  have hprod : a * b = c * d := by
    apply mul_left_cancel₀ hp
    rw [← hs] at hm
    exact hm.symm
  have he : (a - c) * (a - d) = 0 := by
    linear_combination a * hs - hprod
  simpa only [sub_eq_zero] using mul_eq_zero.mp he

/-- A line over the fixed field meets a unit circle in at most two points. -/
lemma circle_affine_line [Algebra K L] (σ : L →ₐ[K] L) {a b d : L} (r : K)
    (ha : OnCircle σ.toRingHom a) (hb : OnCircle σ.toRingHom b)
    (hd : OnCircle σ.toRingHom d) (hab : a ≠ b)
    (he : d = a + r • (b - a)) : d = a ∨ d = b := by
  have hn : (b - a) * σ (b - a) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hab.symm) ((map_ne_zero σ).mpr (sub_ne_zero.mpr hab.symm))
  have hp : (algebraMap K L r) * (algebraMap K L r - 1) *
      ((b - a) * σ (b - a)) = 0 := by
    have hid : d * σ d = (1 - algebraMap K L r) * (a * σ a) +
        (algebraMap K L r) * (b * σ b) + (algebraMap K L r) * (algebraMap K L r - 1) *
          ((b - a) * σ (b - a)) := by
      rw [he]
      simp only [Algebra.smul_def, map_add, map_sub, map_mul, AlgHom.commutes]
      ring
    change a * σ a = 1 at ha
    change b * σ b = 1 at hb
    change d * σ d = 1 at hd
    rw [ha, hb, hd] at hid
    linear_combination -hid
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hn) with hr | hr
  · left
    simpa only [Algebra.smul_def, hr, zero_mul, add_zero] using he
  · right
    have hr' : algebraMap K L r = 1 := sub_eq_zero.mp hr
    simpa only [Algebra.smul_def, hr', one_mul, add_sub_cancel] using he

/-- Injective linear images of unit circles are caps. -/
lemma circle_image_isCap (k : Subfield F) [Algebra k L] (σ : L →ₐ[k] L)
    (T : L →ₗ[k] F) (hT : Function.Injective T) (D : Finset F)
    (hD : ∀ d ∈ D, ∃ x : L, OnCircle σ.toRingHom x ∧ T x = d) : IsCap k D := by
  intro a ha b hb hab d hd hr
  obtain ⟨x, hx, hxa⟩ := hD a ha
  obtain ⟨y, hy, hyb⟩ := hD b hb
  obtain ⟨z, hz, hzd⟩ := hD d hd
  let r : k := ⟨(d - a) / (b - a), hr⟩
  have he : z = x + r • (y - x) := by
    apply hT
    rw [map_add, map_smul, map_sub, hxa, hyb, hzd]
    change d = a + ((d - a) / (b - a)) * (b - a)
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.symm)]
    ring
  have hxy : x ≠ y := fun h ↦ hab (hxa.symm.trans ((congrArg T h).trans hyb))
  rcases circle_affine_line σ r hx hy hz hxy he with h | h
  · left
    exact hzd.symm.trans ((congrArg T h).trans hxa)
  · right
    exact hzd.symm.trans ((congrArg T h).trans hyb)

lemma circle_image_pair_unique (k : Subfield F) [Algebra k L] (σ : L →ₐ[k] L)
    (T : L →ₗ[k] F) (hT : Function.Injective T) (D : Finset F)
    (hD : ∀ d ∈ D, ∃ x : L, OnCircle σ.toRingHom x ∧ T x = d)
    {a b c d : F} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hd : d ∈ D)
    (hp : a + b ≠ 0) (hs : a + b = c + d) : a = c ∨ a = d := by
  obtain ⟨x, hx, hxa⟩ := hD a ha
  obtain ⟨y, hy, hyb⟩ := hD b hb
  obtain ⟨z, hz, hzc⟩ := hD c hc
  obtain ⟨w, hw, hwd⟩ := hD d hd
  have he : x + y = z + w := by
    apply hT
    simpa only [map_add, hxa, hyb, hzc, hwd] using hs
  have hp' : x + y ≠ 0 := by
    intro h
    apply hp
    have hh := congrArg T h
    simpa only [map_add, map_zero, hxa, hyb] using hh
  rcases circle_pair_unique σ.toRingHom hx hy hz hw hp' he with h | h
  · left
    exact hxa.symm.trans ((congrArg T h).trans hzc)
  · right
    exact hxa.symm.trans ((congrArg T h).trans hwd)

end Circle

section PairCounting
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The number of ordered representations from two finite sets. -/
def pairCount (A B : Finset G) (p : G) : ℕ :=
  (A.filter (fun a ↦ p - a ∈ B)).card

lemma pairCount_comm (A B : Finset G) (p : G) : pairCount A B p = pairCount B A p := by
  unfold pairCount
  apply Finset.card_bij (fun a _ ↦ p - a)
  · intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.2, by simpa only [sub_sub_cancel] using ha.1⟩
  · intro a ha b hb he
    exact sub_right_injective he
  · intro b hb
    simp only [Finset.mem_filter] at hb
    refine ⟨p - b, Finset.mem_filter.mpr ⟨hb.2, ?_⟩, ?_⟩
    · simpa only [sub_sub_cancel] using hb.1
    · exact sub_sub_cancel p b

lemma pairCount_union_left (A B C : Finset G) (p : G) (h : Disjoint A B) :
    pairCount (A ∪ B) C p = pairCount A C p + pairCount B C p := by
  unfold pairCount
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

lemma pairCount_union_right (A B C : Finset G) (p : G) (h : Disjoint B C) :
    pairCount A (B ∪ C) p = pairCount A B p + pairCount A C p := by
  rw [pairCount_comm, pairCount_union_left _ _ _ _ h,
    pairCount_comm B A, pairCount_comm C A]

lemma pairCount_union_self (A B : Finset G) (p : G) (h : Disjoint A B) :
    pairCount (A ∪ B) (A ∪ B) p =
      pairCount A A p + 2 * pairCount B A p + pairCount B B p := by
  rw [pairCount_union_left _ _ _ _ h, pairCount_union_right _ _ _ _ h,
    pairCount_union_right _ _ _ _ h, pairCount_comm A B]
  omega

lemma pairCount_self_le_two (D : Finset G)
    (hD : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ d ∈ D,
      a + b ≠ 0 → a + b = c + d → a = c ∨ a = d)
    (p : G) (hp : p ≠ 0) : pairCount D D p ≤ 2 := by
  let S := D.filter (fun a ↦ p - a ∈ D)
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := hS
    have ha' := Finset.mem_filter.mp ha
    have hsub : S ⊆ {a, p - a} := by
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      have hsum : a + (p - a) = d + (p - d) := by abel
      have heq : a + (p - a) = p := by abel
      have hne : a + (p - a) ≠ 0 := by rwa [heq]
      rcases hD a ha'.1 (p - a) ha'.2 d hd'.1 (p - d) hd'.2 hne hsum with hh | hh
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl hh.symm
      · have hd : d = p - a := by rw [hh, sub_sub_cancel]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr hd
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change S.card ≤ 2
    simp only [he, Finset.card_empty, zero_le]

end PairCounting

section FiniteGraphs
variable [Fintype F] [DecidableEq F]

noncomputable def parabolaSet (U : Finset F) : Finset (F × F) := by
  classical
  exact Finset.univ.filter (fun p ↦ ∃ u ∈ U, p.2 = p.1 ^ 2 / u)

def horizontal (D : Finset F) : Finset (F × F) := D.image (fun d ↦ (d, 0))

lemma horizontal_pair_count (U D : Finset F) (t s : F) :
    pairCount (horizontal D) (parabolaSet U) (t, s) =
      (D.filter (fun d ↦ ∃ u ∈ U, s = (t - d) ^ 2 / u)).card := by
  classical
  unfold pairCount horizontal
  have hi : Function.Injective (fun d : F ↦ (d, (0 : F))) := fun _ _ h ↦ congrArg Prod.fst h
  rw [Finset.filter_image, Finset.card_image_of_injective _ hi]
  congr 1
  apply Finset.filter_congr
  intro d hd
  simp [parabolaSet]

lemma horizontal_graph_pair_count_le_two (k : Subfield F)
    (hclosed : ∀ x : F, x ^ 2 ∈ k → x ∈ k)
    (U D : Finset F) (hU : ∀ u ∈ U, u ∈ k ∧ u ≠ 0)
    (hD : IsCap k D) (p : F × F) :
    pairCount (horizontal D) (parabolaSet U) p ≤ 2 := by
  obtain ⟨t, s⟩ := p
  rw [horizontal_pair_count]
  exact cap_parabola_intersection_le_two k hclosed U D hU hD t s

lemma graph_horizontal_disjoint (U D : Finset F) (hU : ∀ u ∈ U, u ≠ 0)
    (hD : (0 : F) ∉ D) : Disjoint (parabolaSet U) (horizontal D) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hd
  change p ∈ D.image (fun d ↦ (d, (0 : F))) at hd
  obtain ⟨d, hdD, heq⟩ := Finset.mem_image.mp hd
  subst p
  obtain ⟨u, hu, he⟩ := (Finset.mem_filter.mp hp).2
  have he' : d ^ 2 = 0 := ((div_eq_zero_iff).mp he.symm).resolve_right (hU u hu)
  exact hD (eq_zero_of_pow_eq_zero he' ▸ hdD)

omit [Fintype F] in
lemma horizontal_self_pair_count (D : Finset F) (t s : F) :
    pairCount (horizontal D) (horizontal D) (t, s) =
      if s = 0 then pairCount D D t else 0 := by
  classical
  unfold pairCount horizontal
  have hi : Function.Injective (fun d : F ↦ (d, (0 : F))) := fun _ _ h ↦ congrArg Prod.fst h
  rw [Finset.filter_image, Finset.card_image_of_injective _ hi]
  by_cases hs : s = 0
  · simp [hs]
  · simp [hs, Ne.symm hs]

omit [Fintype F] in
lemma horizontal_self_le_two (D : Finset F)
    (hD : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ d ∈ D,
      a + b ≠ 0 → a + b = c + d → a = c ∨ a = d)
    (p : F × F) (hp : p ≠ 0) : pairCount (horizontal D) (horizontal D) p ≤ 2 := by
  obtain ⟨t, s⟩ := p
  rw [horizontal_self_pair_count]
  split_ifs with hs
  · exact pairCount_self_le_two D hD t (fun ht ↦ hp (Prod.ext ht hs))
  · omega

omit [Fintype F] in
lemma horizontal_origin_count (D : Finset F) (hneg : ∀ d ∈ D, -d ∈ D) :
    pairCount (horizontal D) (horizontal D) (0, 0) = D.card := by
  rw [horizontal_self_pair_count, if_pos rfl, pairCount]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro d hd
  simpa only [zero_sub] using hneg d hd

lemma horizontal_graph_origin_count (U D : Finset F) (hU : ∀ u ∈ U, u ≠ 0)
    (hD : (0 : F) ∉ D) : pairCount (horizontal D) (parabolaSet U) (0, 0) = 0 := by
  classical
  rw [horizontal_pair_count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro d hd
  rintro ⟨u, hu, he⟩
  have hh : d ^ 2 / u = 0 := by simpa only [zero_sub, neg_sq] using he.symm
  have he' : d ^ 2 = 0 := ((div_eq_zero_iff).mp hh).resolve_right (hU u hu)
  exact hD (eq_zero_of_pow_eq_zero he' ▸ hd)

/-- The finite origin repair, with explicit cap and nonzero-sum uniqueness hypotheses.
No estimate here concerns an infinite subset of the natural numbers. -/
lemma origin_repair (k : Subfield F)
    (hclosed : ∀ x : F, x ^ 2 ∈ k → x ∈ k)
    (U D : Finset F) (hU : ∀ u ∈ U, u ∈ k ∧ u ≠ 0)
    (hcap : IsCap k D)
    (hpair : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ d ∈ D,
      a + b ≠ 0 → a + b = c + d → a = c ∨ a = d)
    (hneg : ∀ d ∈ D, -d ∈ D) (hD0 : (0 : F) ∉ D)
    (hzero : pairCount (parabolaSet U) (parabolaSet U) (0, 0) = 1) :
    pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) (0, 0) =
        1 + D.card ∧
      ∀ p : F × F, p ≠ 0 →
        pairCount (parabolaSet U) (parabolaSet U) p ≤
          pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) p ∧
        pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) p ≤
          pairCount (parabolaSet U) (parabolaSet U) p + 6 := by
  have hUn : ∀ u ∈ U, u ≠ 0 := fun u hu ↦ (hU u hu).2
  have hd := graph_horizontal_disjoint U D hUn hD0
  constructor
  · rw [pairCount_union_self _ _ _ hd, hzero, horizontal_graph_origin_count U D hUn hD0,
      horizontal_origin_count D hneg]
  · intro p hp
    rw [pairCount_union_self _ _ _ hd]
    have hmix := horizontal_graph_pair_count_le_two k hclosed U D hU hcap p
    have hself := horizontal_self_le_two D hpair p hp
    omega

lemma parabolaSet_origin_count (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0)
    (hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0) (hne : U.Nonempty) :
    pairCount (parabolaSet U) (parabolaSet U) (0, 0) = 1 := by
  classical
  have hzero : (0, 0) ∈ parabolaSet U := by
    obtain ⟨u, hu⟩ := hne
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, by simp⟩
  have he : ((parabolaSet U).filter (fun p ↦ (0, 0) - p ∈ parabolaSet U)) = {(0, 0)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hnp⟩
      obtain ⟨u, hu, hpu⟩ := (Finset.mem_filter.mp hp).2
      obtain ⟨v, hv, hpv⟩ := (Finset.mem_filter.mp hnp).2
      simp only [Prod.snd_sub, Prod.fst_sub, zero_sub, neg_sq] at hpv
      have hxu : p.2 * u = p.1 ^ 2 := (eq_div_iff (hU u hu)).mp hpu
      have hxv : -p.2 * v = p.1 ^ 2 := (eq_div_iff (hU v hv)).mp hpv
      have hm : p.1 ^ 2 * (u + v) = 0 := by
        linear_combination -v * hxu - u * hxv
      have hx : p.1 = 0 := eq_zero_of_pow_eq_zero
        ((mul_eq_zero.mp hm).resolve_right (hUU u hu v hv))
      have hy : p.2 = 0 := by simpa only [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] using hpu
      exact Prod.ext hx hy
    · intro hp
      subst p
      exact ⟨hzero, by simpa using hzero⟩
  unfold pairCount
  rw [he, Finset.card_singleton]

/-- Circle images supply both geometric hypotheses in the origin-repair lemma. -/
lemma circle_origin_repair (k : Subfield F) [FiniteDimensional k F]
    (hdeg : Odd (Module.finrank k F))
    {L : Type*} [Field L] [Algebra k L] (σ : L →ₐ[k] L)
    (T : L →ₗ[k] F) (hT : Function.Injective T)
    (U D : Finset F) (hU : ∀ u ∈ U, u ∈ k ∧ u ≠ 0)
    (hD : ∀ d ∈ D, ∃ x : L, OnCircle σ.toRingHom x ∧ T x = d)
    (hneg : ∀ d ∈ D, -d ∈ D)
    (hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0) (hne : U.Nonempty) :
    pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) (0, 0) =
        1 + D.card ∧
      ∀ p : F × F, p ≠ 0 →
        pairCount (parabolaSet U) (parabolaSet U) p ≤
          pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) p ∧
        pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) p ≤
          pairCount (parabolaSet U) (parabolaSet U) p + 6 := by
  have hzero := parabolaSet_origin_count U (fun u hu ↦ (hU u hu).2) hUU hne
  have hD0 : (0 : F) ∉ D := by
    intro h
    obtain ⟨x, hx, hTx⟩ := hD 0 h
    have hx0 : x = 0 := hT (hTx.trans (map_zero T).symm)
    exact circle_ne_zero σ.toRingHom hx hx0
  apply origin_repair k (fun x hx ↦ subfield_square_closed_of_odd_finrank k hdeg hx)
    U D hU (circle_image_isCap k σ T hT D hD) ?_ hneg hD0 hzero
  intro a ha b hb c hc d hd hp hs
  exact circle_image_pair_unique k σ T hT D hD ha hb hc hd hp hs

end FiniteGraphs

section ConstructCircle
variable {L : Type*} [Field L]

lemma exists_linear_injection [Algebra K L] [Algebra K F]
    [FiniteDimensional K L] [FiniteDimensional K F]
    (h : Module.finrank K L ≤ Module.finrank K F) :
    ∃ T : L →ₗ[K] F, Function.Injective T := by
  classical
  let b := Module.finBasis K L
  let c := Module.finBasis K F
  let e := Fin.castLEEmb h
  let T : L →ₗ[K] F := b.constr K (fun i ↦ c (e i))
  refine ⟨T, LinearMap.injective_of_linearIndependent b.span_eq ?_⟩
  have he : T ∘ b = c ∘ e := by
    funext i
    exact b.constr_basis K _ i
  rw [he]
  exact c.linearIndependent.comp e e.injective

lemma exists_primitive_root_of_card_dvd [Fintype L] [DecidableEq L]
    (n : ℕ) (hn : n ∣ Fintype.card L - 1) : ∃ ζ : L, IsPrimitiveRoot ζ n := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Lˣ)
  have hcard : Nat.card Lˣ = Fintype.card L - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hord : orderOf u ≠ 0 := by rw [hu]; exact Nat.card_pos.ne'
  have hd : n ∣ orderOf u := by rwa [hu, hcard]
  let v := u ^ (orderOf u / n)
  have hv : orderOf v = n := orderOf_pow_orderOf_div hord hd
  exact ⟨(v : L), IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hv)⟩

noncomputable def finiteCircle [Fintype K] [Fintype L] [Algebra K L] : Finset L := by
  classical
  exact Finset.univ.filter (OnCircle (FiniteField.frobeniusAlgHom K L).toRingHom)

lemma finiteCircle_card [Fintype K] [Fintype L] [Algebra K L]
    (hcard : Fintype.card L = Fintype.card K ^ 2) :
    (finiteCircle (K := K) (L := L)).card = Fintype.card K + 1 := by
  classical
  let q := Fintype.card K
  have hq : 1 ≤ q := Fintype.card_pos
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have hd : q + 1 ∣ Fintype.card L - 1 := by
    rw [hcard]
    refine ⟨q - 1, ?_⟩
    have h1 := Nat.sub_add_cancel hq
    have h2 := Nat.sub_add_cancel hq2
    change q ^ 2 - 1 = (q + 1) * (q - 1)
    nlinarith
  obtain ⟨ζ, hζ⟩ := exists_primitive_root_of_card_dvd (q + 1) hd
  have he : finiteCircle (K := K) (L := L) = Polynomial.nthRootsFinset (q + 1) (1 : L) := by
    ext x
    simp only [finiteCircle, Finset.mem_filter, Finset.mem_univ, true_and,
      Polynomial.mem_nthRootsFinset (by omega : 0 < q + 1), OnCircle,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, FiniteField.frobeniusAlgHom_apply]
    rw [pow_succ']
  rw [he, hζ.card_nthRootsFinset]

lemma finiteCircle_neg_closed [Fintype K] [Fintype L] [Algebra K L] :
    ∀ x ∈ finiteCircle (K := K) (L := L), -x ∈ finiteCircle (K := K) (L := L) := by
  classical
  intro x hx
  have hh := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simpa only [OnCircle, map_neg, neg_mul_neg] using hh

lemma finiteCircle_zero_not_mem [Fintype K] [Fintype L] [Algebra K L] :
    (0 : L) ∉ finiteCircle (K := K) (L := L) := by
  classical
  intro h
  exact circle_ne_zero _ (Finset.mem_filter.mp h).2 rfl

/-- In odd characteristic, a symmetric set avoiding zero has symmetric subsets
of every smaller even cardinality. -/
lemma exists_symmetric_subset [DecidableEq L] (h2 : (2 : L) ≠ 0)
    (C : Finset L) (hC : ∀ x ∈ C, -x ∈ C) (h0 : (0 : L) ∉ C)
    (m : ℕ) (hm : 2 * m ≤ C.card) :
    ∃ E : Finset L, E ⊆ C ∧ E.card = 2 * m ∧ ∀ x ∈ E, -x ∈ E := by
  induction m with
  | zero => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨E, hEC, hEcard, hEneg⟩ := ih (by omega)
    obtain ⟨x, hxC, hxE⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show E.card < C.card by omega)
    have hnx : -x ∉ E := fun h ↦ hxE (by simpa only [neg_neg] using hEneg (-x) h)
    have hx0 : x ≠ 0 := fun h ↦ h0 (h ▸ hxC)
    have hxnx : x ≠ -x := by
      intro he
      have hh : (2 : L) * x = 0 := by linear_combination he
      exact (mul_ne_zero h2 hx0) hh
    refine ⟨insert x (insert (-x) E), ?_, ?_, ?_⟩
    · intro y hy
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | rfl | hy
      · exact hxC
      · exact hC x hxC
      · exact hEC hy
    · have hxi : x ∉ insert (-x) E := by
        simpa only [Finset.mem_insert, not_or] using And.intro hxnx hxE
      rw [Finset.card_insert_of_notMem hxi, Finset.card_insert_of_notMem hnx, hEcard]
      omega
    · intro y hy
      simp only [Finset.mem_insert] at hy ⊢
      rcases hy with rfl | rfl | hy
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (neg_neg x)
      · exact Or.inr (Or.inr (hEneg y hy))

end ConstructCircle

section ConstructRepair
variable [Fintype F] [DecidableEq F]

/-- A finite odd-characteristic extension of dimension at least two contains symmetric
caps of all even sizes up to the base-field cardinality plus one, with unique nonzero sums. -/
lemma exists_circle_cap (k : Subfield F) [FiniteDimensional k F]
    (p : ℕ) [Fact p.Prime] [CharP k p] (h2 : (2 : k) ≠ 0)
    (hdim : 2 ≤ Module.finrank k F) (m : ℕ) (hm : 2 * m ≤ Nat.card k + 1) :
    ∃ D : Finset F, D.card = 2 * m ∧ (0 : F) ∉ D ∧
      (∀ x ∈ D, -x ∈ D) ∧ IsCap k D ∧
      (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ d ∈ D,
        a + b ≠ 0 → a + b = c + d → a = c ∨ a = d) := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  let L := FiniteField.Extension k p 2
  letI : Fintype L := Fintype.ofFinite L
  let σ : L →ₐ[k] L := FiniteField.frobeniusAlgHom k L
  have hfin : Module.finrank k L = 2 := FiniteField.finrank_extension k p 2
  have hcard : Fintype.card L = Fintype.card k ^ 2 := by
    simpa only [Nat.card_eq_fintype_card] using FiniteField.natCard_extension k p 2
  obtain ⟨T, hT⟩ := exists_linear_injection (K := k) (L := L) (F := F)
    (show Module.finrank k L ≤ Module.finrank k F by rw [hfin]; exact hdim)
  let C := finiteCircle (K := k) (L := L)
  have hCcard : C.card = Nat.card k + 1 := by
    rw [Nat.card_eq_fintype_card]
    exact finiteCircle_card hcard
  have h2L : (2 : L) ≠ 0 := by
    intro hh
    apply h2
    apply (algebraMap k L).injective
    simpa only [map_ofNat, map_zero] using hh
  obtain ⟨E, hEC, hEcard, hEneg⟩ := exists_symmetric_subset h2L C
    finiteCircle_neg_closed finiteCircle_zero_not_mem m (by rwa [hCcard])
  let D := E.image T
  have hD : ∀ d ∈ D, ∃ x : L, OnCircle σ.toRingHom x ∧ T x = d := by
    intro d hd
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hd
    exact ⟨x, (Finset.mem_filter.mp (hEC hx)).2, hxd⟩
  have hD0 : (0 : F) ∉ D := by
    intro h
    obtain ⟨x, hx, hTx⟩ := hD 0 h
    have hx0 : x = 0 := hT (hTx.trans (map_zero T).symm)
    exact circle_ne_zero σ.toRingHom hx hx0
  refine ⟨D, ?_, hD0, ?_, circle_image_isCap k σ T hT D hD, ?_⟩
  · exact (Finset.card_image_of_injective E hT).trans hEcard
  · intro d hd
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hd
    exact Finset.mem_image.mpr ⟨-x, hEneg x hx, by rw [map_neg, hxd]⟩
  · intro a ha b hb c hc d hd hp hs
    exact circle_image_pair_unique k σ T hT D hD ha hb hc hd hp hs

/-- The exceptional origin of the finite parabola construction can actually be repaired.
The added set has the prescribed even size; every nonzero count increases by at most six. -/
lemma exists_origin_repair (k : Subfield F) [FiniteDimensional k F]
    (p : ℕ) [Fact p.Prime] [CharP k p] (h2 : (2 : k) ≠ 0)
    (hdeg : Odd (Module.finrank k F)) (hdim : 2 ≤ Module.finrank k F)
    (U : Finset F) (hU : ∀ u ∈ U, u ∈ k ∧ u ≠ 0)
    (hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0) (hne : U.Nonempty)
    (m : ℕ) (hm : 2 * m ≤ Nat.card k + 1) :
    ∃ D : Finset F, D.card = 2 * m ∧
      pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) (0, 0) =
        1 + 2 * m ∧
      ∀ z : F × F, z ≠ 0 →
        pairCount (parabolaSet U) (parabolaSet U) z ≤
          pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) z ∧
        pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) z ≤
          pairCount (parabolaSet U) (parabolaSet U) z + 6 := by
  obtain ⟨D, hcard, hD0, hneg, hcap, hpair⟩ := exists_circle_cap k p h2 hdim m hm
  have hzero := parabolaSet_origin_count U (fun u hu ↦ (hU u hu).2) hUU hne
  obtain ⟨hz, hrest⟩ := origin_repair k
    (fun x hx ↦ subfield_square_closed_of_odd_finrank k hdeg hx)
    U D hU hcap hpair hneg hD0 hzero
  exact ⟨D, hcard, by simpa only [hcard] using hz, hrest⟩

end ConstructRepair
end Erdos66OriginRepair
