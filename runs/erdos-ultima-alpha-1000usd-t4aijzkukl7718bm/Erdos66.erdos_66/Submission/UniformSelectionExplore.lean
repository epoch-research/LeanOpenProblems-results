import FormalConjecturesUtil

/-! Finite uniform selection with simultaneous small-hit and affine-avoidance
constraints. This is a tool for local representation repairs, not a proof of
Erdős 66. -/
namespace Erdos66UniformSelection
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def mean {γ : Type*} [Fintype γ] (F : γ → ℝ) : ℝ :=
  (∑ x, F x) / Fintype.card γ

lemma mean_mono {γ : Type*} [Fintype γ] (F G : γ → ℝ) (h : ∀ x, F x ≤ G x) :
    mean F ≤ mean G :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ ↦ h x)) (Nat.cast_nonneg _)

lemma mean_const {γ : Type*} [Fintype γ] [Nonempty γ] (c : ℝ) :
    mean (fun _ : γ ↦ c) = c := by
  have hc : (Fintype.card γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, hc]

lemma mean_add {γ : Type*} [Fintype γ] (F G : γ → ℝ) :
    mean (fun x ↦ F x + G x) = mean F + mean G := by
  simp only [mean, Finset.sum_add_distrib, add_div]

lemma mean_const_mul {γ : Type*} [Fintype γ] (c : ℝ) (F : γ → ℝ) :
    mean (fun x ↦ c * F x) = c * mean F := by
  simp only [mean, ← Finset.mul_sum, mul_div_assoc]

lemma mean_sum {γ κ : Type*} [Fintype γ] (S : Finset κ) (F : κ → γ → ℝ) :
    mean (fun x ↦ ∑ k ∈ S, F k x) = ∑ k ∈ S, mean (F k) := by
  simp only [mean, Finset.sum_div]
  exact Finset.sum_comm

lemma mean_indicator {γ : Type*} [Fintype γ] (P : γ → Prop) [DecidablePred P] :
    mean (fun x ↦ if P x then (1 : ℝ) else 0) =
      ((Finset.univ.filter P).card : ℝ) / Fintype.card γ := by
  simp only [mean, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma exists_lt_of_mean_lt {γ : Type*} [Fintype γ] [Nonempty γ]
    (F : γ → ℝ) (r : ℝ) (h : mean F < r) : ∃ x, F x < r := by
  by_contra hn
  push_neg at hn
  have hh := mean_mono (fun _ ↦ r) F hn
  rw [mean_const] at hh
  linarith

section Product
variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
  [DecidableEq ι] [DecidableEq α]

lemma mean_product (g : ι → α → ℝ) :
    mean (fun ω : ι → α ↦ ∏ i, g i (ω i)) = ∏ i, mean (g i) := by
  simp only [mean, Fintype.card_fun, Nat.cast_pow]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp

lemma mean_exp_sum (g : ι → α → ℝ) (t : ℝ) :
    mean (fun ω : ι → α ↦ Real.exp (t * ∑ i, g i (ω i))) =
      ∏ i, mean (fun x ↦ Real.exp (t * g i x)) := by
  simpa only [Finset.mul_sum, Real.exp_sum] using
    (mean_product (fun i x ↦ Real.exp (t * g i x)))

noncomputable def hits (S : Finset α) (ω : ι → α) : ℝ :=
  ∑ i, if ω i ∈ S then (1 : ℝ) else 0

lemma hits_nonneg (S : Finset α) (ω : ι → α) : 0 ≤ hits S ω := by
  exact Finset.sum_nonneg (fun i _ ↦ by split_ifs <;> norm_num)

lemma mean_exp_hit (S : Finset α) (t : ℝ) :
    mean (fun x : α ↦ Real.exp (t * (if x ∈ S then (1 : ℝ) else 0))) =
      1 + (Real.exp t - 1) * S.card / Fintype.card α := by
  have he (x : α) : Real.exp (t * (if x ∈ S then (1 : ℝ) else 0)) =
      1 + (Real.exp t - 1) * (if x ∈ S then (1 : ℝ) else 0) := by
    by_cases hx : x ∈ S <;> simp [hx]
  simp_rw [he]
  rw [mean_add, mean_const, mean_const_mul, mean_indicator]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, mul_div_assoc]

lemma hit_mgf_bound (S : Finset α) (t : ℝ) :
    mean (fun ω : ι → α ↦ Real.exp (t * hits S ω)) ≤
      Real.exp ((Fintype.card ι : ℝ) * Real.exp t * S.card / Fintype.card α) := by
  have hq : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hfactor : 0 ≤ 1 + (Real.exp t - 1) * S.card / Fintype.card α := by
    rw [← mean_exp_hit S t]
    exact div_nonneg (Finset.sum_nonneg (fun x _ ↦ (Real.exp_pos _).le)) hq.le
  have hbound : 1 + (Real.exp t - 1) * S.card / Fintype.card α ≤
      Real.exp (Real.exp t * S.card / Fintype.card α) := by
    have hs : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show Real.exp t - 1 ≤ Real.exp t by linarith) hs) hq.le
    have he := Real.add_one_le_exp (Real.exp t * S.card / Fintype.card α)
    linarith
  change mean (fun ω : ι → α ↦ Real.exp (t * ∑ i, if ω i ∈ S then (1 : ℝ) else 0)) ≤ _
  rw [mean_exp_sum (fun (_ : ι) (x : α) ↦ if x ∈ S then (1 : ℝ) else 0) t]
  simp_rw [mean_exp_hit]
  calc
    _ ≤ ∏ _i : ι, Real.exp (Real.exp t * S.card / Fintype.card α) :=
      Finset.prod_le_prod (fun _ _ ↦ hfactor) (fun _ _ ↦ hbound)
    _ = _ := by
      rw [← Real.exp_sum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      ring

/-- If all coordinates except one determine at most one bad choice, the
uniform probability of the bad event is at most 1/card(alpha). -/
lemma one_fiber_indicator_bound (P : (ι → α) → Prop) (i : ι)
    (hP : ∀ f : ι → α, ∀ x y : α,
      P (Function.update f i x) → P (Function.update f i y) → x = y) :
    mean (fun ω : ι → α ↦ if P ω then (1 : ℝ) else 0) ≤ 1 / Fintype.card α := by
  let a₀ : α := Classical.choice inferInstance
  let B : Finset (ι → α) := Finset.univ.filter P
  let U : Finset (ι → α) := Finset.univ.filter (fun f ↦ f i = a₀)
  have hsub : B.image (fun f ↦ Function.update f i a₀) ⊆ U := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    simp [U]
  have hinj : Set.InjOn (fun f : ι → α ↦ Function.update f i a₀) (B : Set (ι → α)) := by
    intro f hf g hg he
    have hfP : P f := (Finset.mem_filter.mp hf).2
    have hgP : P g := (Finset.mem_filter.mp hg).2
    have he' : Function.update f i (g i) = g := by
      apply Function.update_eq_iff.mpr
      refine ⟨rfl, fun j hj ↦ ?_⟩
      have hh := congrFun he j
      simpa [Function.update_of_ne hj] using hh
    have hi : f i = g i := hP f (f i) (g i) (by simpa using hfP) (by rwa [he'])
    funext j
    by_cases hj : j = i
    · simpa [hj] using hi
    · have hh := congrFun he j
      simpa [Function.update_of_ne hj] using hh
  have hUcard : U.card = Fintype.card α ^ (Fintype.card ι - 1) := by
    have hh := Fintype.card_filter_piFinset_const_eq_of_mem
      (Finset.univ : Finset α) i (Finset.mem_univ a₀)
    simpa only [Fintype.piFinset_univ, Finset.card_univ] using hh
  have hcard : B.card ≤ Fintype.card α ^ (Fintype.card ι - 1) := by
    rw [← hUcard, ← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hm : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hq : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [mean_indicator, Fintype.card_fun, Nat.cast_pow]
  have hh : (B.card : ℝ) ≤ (Fintype.card α : ℝ) ^ (Fintype.card ι - 1) := by exact_mod_cast hcard
  apply (div_le_div_of_nonneg_right hh (by positivity)).trans_eq
  have hm' : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
  rw [hm', pow_succ]
  field_simp
  simp

/-- An exponential-potential criterion for one selection satisfying all the
hit-count bounds while avoiding all the one-fiber bad events. -/
theorem exists_avoid_and_small_hits {κ ζ : Type*}
    (E : Finset κ) (P : κ → (ι → α) → Prop)
    (hP : ∀ j ∈ E, ∃ i : ι, ∀ f : ι → α, ∀ x y : α,
      P j (Function.update f i x) → P j (Function.update f i y) → x = y)
    (T : Finset ζ) (S : ζ → Finset α) (K R t : ℝ)
    (hS : ∀ z ∈ T, (S z).card ≤ K) (ht : 0 < t)
    (hsmall : (E.card : ℝ) / Fintype.card α +
      T.card * Real.exp ((Fintype.card ι : ℝ) * Real.exp t * K / Fintype.card α - t * R) < 1) :
    ∃ ω : ι → α, (∀ j ∈ E, ¬ P j ω) ∧ ∀ z ∈ T, hits (S z) ω < R := by
  let F : (ι → α) → ℝ := fun ω ↦
    (∑ j ∈ E, if P j ω then (1 : ℝ) else 0) +
      ∑ z ∈ T, Real.exp (t * (hits (S z) ω - R))
  have hterm (z : ζ) (hz : z ∈ T) :
      mean (fun ω : ι → α ↦ Real.exp (t * (hits (S z) ω - R))) ≤
        Real.exp ((Fintype.card ι : ℝ) * Real.exp t * K / Fintype.card α - t * R) := by
    have he (ω : ι → α) : Real.exp (t * (hits (S z) ω - R)) =
        Real.exp (-t * R) * Real.exp (t * hits (S z) ω) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [he]
    rw [mean_const_mul]
    have hb := mul_le_mul_of_nonneg_left (hit_mgf_bound (ι := ι) (S z) t) (Real.exp_pos (-t * R)).le
    apply hb.trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hS z hz) (by positivity : 0 ≤ (Fintype.card ι : ℝ) * Real.exp t))
      (Nat.cast_nonneg (α := ℝ) (Fintype.card α))
    linarith
  have hF : mean F < 1 := by
    dsimp only [F]
    rw [mean_add, mean_sum, mean_sum]
    have hb : (∑ j ∈ E, mean (fun ω : ι → α ↦ if P j ω then (1 : ℝ) else 0)) ≤
        E.card / (Fintype.card α : ℝ) := by
      calc
        _ ≤ ∑ _j ∈ E, 1 / (Fintype.card α : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨i, hi⟩ := hP j hj
          exact one_fiber_indicator_bound (P j) i hi
        _ = _ := by simp; ring
    have hs := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    linarith
  obtain ⟨ω, hω⟩ := exists_lt_of_mean_lt F 1 hF
  have hbad0 : 0 ≤ ∑ j ∈ E, if P j ω then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> norm_num)
  have hhit0 : 0 ≤ ∑ z ∈ T, Real.exp (t * (hits (S z) ω - R)) :=
    Finset.sum_nonneg (fun _ _ ↦ (Real.exp_pos _).le)
  refine ⟨ω, ?_, ?_⟩
  · intro j hj hjP
    have hh := Finset.single_le_sum
      (f := fun j ↦ if P j ω then (1 : ℝ) else 0)
      (fun _ _ ↦ by dsimp only; split_ifs <;> norm_num) hj
    dsimp only at hh
    rw [if_pos hjP] at hh
    dsimp only [F] at hω
    linarith
  · intro z hz
    have hh := Finset.single_le_sum
      (f := fun z ↦ Real.exp (t * (hits (S z) ω - R)))
      (fun _ _ ↦ (Real.exp_pos _).le) hz
    have he : Real.exp (t * (hits (S z) ω - R)) < 1 := by dsimp only [F] at hω; linarith
    have he' := Real.exp_lt_one_iff.mp he
    nlinarith

end Product
end Erdos66UniformSelection
