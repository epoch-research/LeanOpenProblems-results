import FormalConjecturesUtil

/-!
# A finite-field counting identity

This is an exploratory finite analogue, not a proof of Erdős Problem 66.
-/

namespace Erdos66FiniteField

variable {F : Type*} [Field F]

lemma parabola_equation_iff (u v t s x : F) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u + v ≠ 0) :
    x ^ 2 / u + (t - x) ^ 2 / v = s ↔
      ((u + v) * x - u * t) ^ 2 = u * v * ((u + v) * s - t ^ 2) := by
  have he : ((u + v) * x - u * t) ^ 2 - u * v * ((u + v) * s - t ^ 2) =
      (u * v * (u + v)) * (x ^ 2 / u + (t - x) ^ 2 / v - s) := by
    field_simp
    ring
  conv_rhs => rw [← sub_eq_zero, he, mul_eq_zero]
  simp only [mul_ne_zero (mul_ne_zero hu hv) huv, false_or, sub_eq_zero]

noncomputable def parabolaRootEquiv (u v t s : F) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u + v ≠ 0) :
    {x : F // x ^ 2 / u + (t - x) ^ 2 / v = s} ≃
      {y : F // y ^ 2 = u * v * ((u + v) * s - t ^ 2)} where
  toFun x := ⟨(u + v) * x.val - u * t,
    (parabola_equation_iff u v t s x.val hu hv huv).mp x.property⟩
  invFun y := ⟨(y.val + u * t) / (u + v), by
    apply (parabola_equation_iff u v t s _ hu hv huv).mpr
    have he : (u + v) * ((y.val + u * t) / (u + v)) - u * t = y.val := by
      field_simp
      ring
    rw [he]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    change (((u + v) * x.val - u * t) + u * t) / (u + v) = x.val
    field_simp
    ring
  right_inv y := by
    apply Subtype.ext
    change (u + v) * ((y.val + u * t) / (u + v)) - u * t = y.val
    field_simp
    ring

lemma parabola_sum_count [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (u v t s : F) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u + v ≠ 0) :
    (Fintype.card {x : F // x ^ 2 / u + (t - x) ^ 2 / v = s} : ℤ) =
      1 + quadraticChar F u * quadraticChar F v *
        quadraticChar F ((u + v) * s - t ^ 2) := by
  rw [Fintype.card_congr (parabolaRootEquiv u v t s hu hv huv)]
  have h := quadraticChar_card_sqrts hF (u * v * ((u + v) * s - t ^ 2))
  simpa only [Set.toFinset_card, Nat.card_eq_fintype_card, map_mul, add_comm] using h

section Counting
variable [Fintype F] [DecidableEq F]

noncomputable def graphCount (U : Finset F) (t s : F) : ℤ :=
  ∑ u ∈ U, ∑ v ∈ U,
    (Fintype.card {x : F // x ^ 2 / u + (t - x) ^ 2 / v = s} : ℤ)

noncomputable def charFiber (U : Finset F) (w : F) : ℤ :=
  ∑ u ∈ U, ∑ v ∈ U,
    if u + v = w then quadraticChar F u * quadraticChar F v else 0

lemma graphCount_identity (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0) (t s : F) :
    graphCount U t s = (U.card : ℤ) ^ 2 +
      ∑ w : F, charFiber U w * quadraticChar F (w * s - t ^ 2) := by
  have hcount : graphCount U t s = (U.card : ℤ) ^ 2 +
      ∑ u ∈ U, ∑ v ∈ U, quadraticChar F u * quadraticChar F v *
        quadraticChar F ((u + v) * s - t ^ 2) := by
    calc
      graphCount U t s = ∑ u ∈ U, ∑ v ∈ U,
          (1 + quadraticChar F u * quadraticChar F v *
            quadraticChar F ((u + v) * s - t ^ 2)) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact parabola_sum_count hF u v t s (hU u hu) (hU v hv) (hUU u hu v hv)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
  rw [hcount]
  congr 1
  symm
  simp only [charFiber, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma quadraticChar_abs_le_one (x : F) : |quadraticChar F x| ≤ 1 := by
  rcases quadraticChar_isQuadratic F x with h | h | h <;> simp [h]

lemma graphCount_error_bound (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0) (t s : F) :
    |graphCount U t s - (U.card : ℤ) ^ 2| ≤ ∑ w : F, |charFiber U w| := by
  rw [graphCount_identity hF U hU hUU, add_sub_cancel_left]
  calc
    _ ≤ ∑ w : F, |charFiber U w * quadraticChar F (w * s - t ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : F, |charFiber U w| := by
      apply Finset.sum_le_sum
      intro w hw
      rw [abs_mul]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (quadraticChar_abs_le_one (w * s - t ^ 2))
          (abs_nonneg (charFiber U w))

noncomputable def graphWeight (U : Finset F) (p : F × F) : ℤ :=
  ∑ u ∈ U, if p.2 = p.1 ^ 2 / u then 1 else 0

noncomputable def graphIndicator (U : Finset F) (p : F × F) : ℤ :=
  if ∃ u ∈ U, p.2 = p.1 ^ 2 / u then 1 else 0

noncomputable def finiteConv (f g : F × F → ℤ) (p : F × F) : ℤ :=
  ∑ a : F × F, f a * g (p - a)

omit [Fintype F] in
lemma graphWeight_nonzero (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0)
    (p : F × F) (hp : p ≠ 0) : graphWeight U p = graphIndicator U p := by
  classical
  unfold graphWeight graphIndicator
  by_cases he : ∃ u ∈ U, p.2 = p.1 ^ 2 / u
  · obtain ⟨u, hu, heq⟩ := he
    rw [if_pos ⟨u, hu, heq⟩]
    have hx : p.1 ≠ 0 := by
      intro h
      have hy : p.2 = 0 := by simpa [h] using heq
      exact hp (Prod.ext h hy)
    have hi : ∀ v ∈ U, p.2 = p.1 ^ 2 / v → v = u := by
      intro v hv hveq
      have hdiv : p.1 ^ 2 / v = p.1 ^ 2 / u := hveq.symm.trans heq
      have hm := (div_eq_div_iff (hU v hv) (hU u hu)).mp hdiv
      exact (mul_left_cancel₀ (pow_ne_zero 2 hx) hm).symm
    rw [Finset.sum_eq_single u]
    · simp [heq]
    · intro v hv hvu
      rw [if_neg (fun h ↦ hvu (hi v hv h))]
    · exact fun hn ↦ (hn hu).elim
  · simp only [if_neg he]
    apply Finset.sum_eq_zero
    intro u hu
    exact if_neg (fun h ↦ he ⟨u, hu, h⟩)

omit [Fintype F] in
lemma graphWeight_eq_indicator (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0)
    (hne : U.Nonempty) (p : F × F) :
    graphWeight U p = graphIndicator U p +
      ((U.card : ℤ) - 1) * (if p = 0 then 1 else 0) := by
  classical
  by_cases hp : p = 0
  · subst p
    obtain ⟨u, hu⟩ := hne
    simp [graphWeight, graphIndicator, show ∃ v, v ∈ U from ⟨u, hu⟩]
  · rw [graphWeight_nonzero U hU p hp, if_neg hp, mul_zero, add_zero]

lemma graph_pair_count (u v t s : F) :
    (∑ p : F × F, (if p.2 = p.1 ^ 2 / u then (1 : ℤ) else 0) *
      (if s - p.2 = (t - p.1) ^ 2 / v then 1 else 0)) =
      (Fintype.card {x : F // x ^ 2 / u + (t - x) ^ 2 / v = s} : ℤ) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply propext
  constructor <;> intro h <;> linear_combination -h

lemma graphCount_eq_conv (U : Finset F) (t s : F) :
    graphCount U t s = finiteConv (graphWeight U) (graphWeight U) (t, s) := by
  classical
  unfold graphCount finiteConv graphWeight
  symm
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, Prod.fst_sub, Prod.snd_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  exact graph_pair_count u v t s

lemma finiteConv_zero_left (f : F × F → ℤ) (p : F × F) :
    finiteConv (fun a ↦ if a = 0 then 1 else 0) f p = f p := by
  classical
  simp [finiteConv, ite_mul]

lemma finiteConv_zero_right (f : F × F → ℤ) (p : F × F) :
    finiteConv f (fun a ↦ if a = 0 then 1 else 0) p = f p := by
  classical
  simp [finiteConv, mul_ite, sub_eq_zero]

lemma finiteConv_add_zeroMass (f : F × F → ℤ) (c : ℤ) (p : F × F) :
    finiteConv (fun a ↦ f a + c * (if a = 0 then 1 else 0))
      (fun a ↦ f a + c * (if a = 0 then 1 else 0)) p =
      finiteConv f f p + 2 * c * f p + c ^ 2 * (if p = 0 then 1 else 0) := by
  classical
  let δ : F × F → ℤ := fun a ↦ if a = 0 then 1 else 0
  have he (a : F × F) :
      (f a + c * δ a) * (f (p - a) + c * δ (p - a)) =
      f a * f (p - a) + c * (δ a * f (p - a)) +
        c * (f a * δ (p - a)) + c ^ 2 * (δ a * δ (p - a)) := by ring
  change (∑ a : F × F, (f a + c * δ a) * (f (p - a) + c * δ (p - a))) = _
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  change finiteConv f f p + c * finiteConv δ f p +
    c * finiteConv f δ p + c ^ 2 * finiteConv δ δ p = _
  rw [finiteConv_zero_left, finiteConv_zero_right, finiteConv_zero_left]
  change finiteConv f f p + c * f p + c * f p + c ^ 2 * δ p =
    finiteConv f f p + 2 * c * f p + c ^ 2 * δ p
  ring

lemma graphCount_set_correction (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0)
    (hne : U.Nonempty) (t s : F) :
    graphCount U t s = finiteConv (graphIndicator U) (graphIndicator U) (t, s) +
      2 * ((U.card : ℤ) - 1) * graphIndicator U (t, s) +
      ((U.card : ℤ) - 1) ^ 2 * (if (t, s) = 0 then 1 else 0) := by
  rw [graphCount_eq_conv]
  have he : graphWeight U = fun p ↦ graphIndicator U p +
      ((U.card : ℤ) - 1) * (if p = 0 then 1 else 0) := by
    funext p
    exact graphWeight_eq_indicator U hU hne p
  rw [he]
  exact finiteConv_add_zeroMass _ _ _

omit [Fintype F] in
lemma graphIndicator_bounds (U : Finset F) (p : F × F) :
    0 ≤ graphIndicator U p ∧ graphIndicator U p ≤ 1 := by
  classical
  unfold graphIndicator
  split_ifs <;> norm_num

lemma graph_set_error_bound (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0)
    (hne : U.Nonempty) (t s : F) (hp : (t, s) ≠ 0) :
    |finiteConv (graphIndicator U) (graphIndicator U) (t, s) - (U.card : ℤ) ^ 2| ≤
      (∑ w : F, |charFiber U w|) + 2 * (U.card : ℤ) := by
  classical
  have hc : 0 ≤ (U.card : ℤ) - 1 := by
    have hh : 1 ≤ U.card := Finset.card_pos.mpr hne
    have hh' : (1 : ℤ) ≤ U.card := by exact_mod_cast hh
    omega
  obtain ⟨hI0, hI1⟩ := graphIndicator_bounds U (t, s)
  have hb : |2 * ((U.card : ℤ) - 1) * graphIndicator U (t, s)| ≤
      2 * (U.card : ℤ) := by
    rw [abs_of_nonneg (by positivity :
      0 ≤ 2 * ((U.card : ℤ) - 1) * graphIndicator U (t, s))]
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hI1)]
  have he := graphCount_set_correction U hU hne t s
  rw [if_neg hp, mul_zero, add_zero] at he
  have he' : finiteConv (graphIndicator U) (graphIndicator U) (t, s) - (U.card : ℤ) ^ 2 =
      (graphCount U t s - (U.card : ℤ) ^ 2) -
        2 * ((U.card : ℤ) - 1) * graphIndicator U (t, s) := by
    linear_combination -he
  rw [he']
  exact (abs_sub _ _).trans (add_le_add (graphCount_error_bound hF U hU hUU t s) hb)

lemma graph_set_origin (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0)
    (hne : U.Nonempty) :
    finiteConv (graphIndicator U) (graphIndicator U) (0, 0) = 1 := by
  have hm : graphCount U 0 0 = (U.card : ℤ) ^ 2 := by
    rw [graphCount_identity hF U hU hUU]
    simp
  have hi : graphIndicator U (0, 0) = 1 := by
    obtain ⟨u, hu⟩ := hne
    simp [graphIndicator, show ∃ v, v ∈ U from ⟨u, hu⟩]
  have he := graphCount_set_correction U hU hne 0 0
  rw [hm, hi] at he
  norm_num at he
  nlinarith

/-- Each nontrivial difference between two parabolas has at most two preimages. -/
lemma parabola_difference_count_le_two (hF : ringChar F ≠ 2)
    (u v t s : F) (hu : u ≠ 0) (hv : v ≠ 0) (hp : (t, s) ≠ 0) :
    (Fintype.card {x : F // x ^ 2 / u - (t - x) ^ 2 / v = s} : ℤ) ≤ 2 := by
  by_cases huv : u = v
  · subst v
    by_cases ht : t = 0
    · have hs : s ≠ 0 := fun hs ↦ hp (Prod.ext ht hs)
      have hi : IsEmpty {x : F // x ^ 2 / u - (t - x) ^ 2 / u = s} := by
        refine ⟨fun x ↦ hs ?_⟩
        have hx := x.property
        simpa [ht] using hx.symm
      haveI := hi
      simp
    · have hlin (x : F) (hx : x ^ 2 / u - (t - x) ^ 2 / u = s) :
          (2 * t) * x = s * u + t ^ 2 := by
        have hh : x ^ 2 - (t - x) ^ 2 = s * u := by
          apply (div_eq_iff hu).mp
          simpa only [sub_div] using hx
        linear_combination hh
      have hcard : Fintype.card {x : F // x ^ 2 / u - (t - x) ^ 2 / u = s} ≤ 1 := by
        apply Fintype.card_le_one_iff.mpr
        intro x y
        apply Subtype.ext
        exact mul_left_cancel₀ (mul_ne_zero (Ring.two_ne_zero hF) ht)
          ((hlin x.val x.property).trans (hlin y.val y.property).symm)
      have hcard' : (Fintype.card {x : F // x ^ 2 / u - (t - x) ^ 2 / u = s} : ℤ) ≤ 1 :=
        by exact_mod_cast hcard
      omega
  · have huv' : u + -v ≠ 0 := by simpa only [← sub_eq_add_neg, sub_ne_zero] using huv
    have he := parabola_sum_count hF u (-v) t s hu (neg_ne_zero.mpr hv) huv'
    simp only [div_neg, ← sub_eq_add_neg] at he
    rw [he]
    have hb : |quadraticChar F u * quadraticChar F (-v) *
        quadraticChar F ((u - v) * s - t ^ 2)| ≤ 1 := by
      rw [abs_mul, abs_mul]
      calc
        _ ≤ 1 * 1 * 1 := mul_le_mul
          (mul_le_mul (quadraticChar_abs_le_one u) (quadraticChar_abs_le_one (-v))
            (abs_nonneg _) (by norm_num))
          (quadraticChar_abs_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have := (abs_le.mp hb).2
    omega

noncomputable def graphDifferenceCount (U : Finset F) (t s : F) : ℤ :=
  ∑ u ∈ U, ∑ v ∈ U,
    (Fintype.card {x : F // x ^ 2 / u - (t - x) ^ 2 / v = s} : ℤ)

lemma graphDifferenceCount_le (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (t s : F) (hp : (t, s) ≠ 0) :
    graphDifferenceCount U t s ≤ 2 * (U.card : ℤ) ^ 2 := by
  calc
    graphDifferenceCount U t s ≤ ∑ u ∈ U, ∑ v ∈ U, (2 : ℤ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      exact parabola_difference_count_le_two hF u v t s (hU u hu) (hU v hv) hp
    _ = _ := by simp; ring

noncomputable def finiteDifference (f g : F × F → ℤ) (p : F × F) : ℤ :=
  ∑ a : F × F, f a * g (a - p)

lemma graph_pair_difference_count (u v t s : F) :
    (∑ p : F × F, (if p.2 = p.1 ^ 2 / u then (1 : ℤ) else 0) *
      (if p.2 - s = (p.1 - t) ^ 2 / v then 1 else 0)) =
      (Fintype.card {x : F // x ^ 2 / u - (t - x) ^ 2 / v = s} : ℤ) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply propext
  have hsq : (x - t) ^ 2 = (t - x) ^ 2 := by ring
  rw [hsq]
  constructor <;> intro h <;> linear_combination h

lemma graphDifferenceCount_eq_difference (U : Finset F) (t s : F) :
    graphDifferenceCount U t s = finiteDifference (graphWeight U) (graphWeight U) (t, s) := by
  classical
  unfold graphDifferenceCount finiteDifference graphWeight
  symm
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, Prod.fst_sub, Prod.snd_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  exact graph_pair_difference_count u v t s

omit [Fintype F] in
lemma graphWeight_nonneg (U : Finset F) (p : F × F) : 0 ≤ graphWeight U p := by
  apply Finset.sum_nonneg
  intro u hu
  split_ifs <;> norm_num

omit [Fintype F] in
lemma graphIndicator_le_weight (U : Finset F) (p : F × F) :
    graphIndicator U p ≤ graphWeight U p := by
  classical
  by_cases he : ∃ u ∈ U, p.2 = p.1 ^ 2 / u
  · obtain ⟨u, hu, heq⟩ := he
    rw [graphIndicator, if_pos ⟨u, hu, heq⟩]
    have hh := Finset.single_le_sum
      (f := fun v ↦ if p.2 = p.1 ^ 2 / v then (1 : ℤ) else 0)
      (fun v (_ : v ∈ U) ↦ by dsimp; split_ifs <;> norm_num) hu
    simpa only [if_pos heq] using hh
  · rw [graphIndicator, if_neg he]
    exact graphWeight_nonneg U p

/-- The ordinary set of graph points has uniformly bounded nonzero difference counts. -/
lemma graph_set_difference_le (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (p : F × F) (hp : p ≠ 0) :
    finiteDifference (graphIndicator U) (graphIndicator U) p ≤ 2 * (U.card : ℤ) ^ 2 := by
  calc
    _ ≤ finiteDifference (graphWeight U) (graphWeight U) p := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul (graphIndicator_le_weight U a)
        (graphIndicator_le_weight U (a - p)) (graphIndicator_bounds U (a - p)).1
        (graphWeight_nonneg U a)
    _ = graphDifferenceCount U p.1 p.2 := (graphDifferenceCount_eq_difference U p.1 p.2).symm
    _ ≤ _ := graphDifferenceCount_le hF U hU p.1 p.2 hp

end Counting
end Erdos66FiniteField
