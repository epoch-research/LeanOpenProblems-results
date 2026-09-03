import Submission.FiniteSampling

/-! Higher even-moment estimates for finite empirical means. Work toward
L^p almost-periodicity; no original-conjecture conclusion is asserted. -/
namespace Erdos3FiniteSamplingMoments

open Finset Erdos3FiniteSampling
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

lemma prod_comp_eq_prod_fiber_pow {I J : Type*} [Fintype I] [Fintype J]
    (t : J → I) (g : I → ℝ) :
    (∏ j, g (t j)) = ∏ i, (g i)^(univ.filter (fun j ↦ t j = i)).card := by
  rw [← prod_fiberwise univ t (fun j ↦ g (t j))]
  apply prod_congr rfl
  intro i _
  calc
    _ = ∏ _j ∈ univ.filter (fun j ↦ t j = i), g i := by
      apply prod_congr rfl
      intro j hj
      rw [(mem_filter.mp hj).2]
    _ = _ := prod_const _

lemma expect_prod_comp_eq_zero {I J A : Type*} [Fintype I] [Fintype J] [Fintype A]
    (g : A → ℝ) (hg : (𝔼 a, g a) = 0) (t : J → I)
    (hs : ∃ i, (univ.filter (fun j ↦ t j = i)).card = 1) :
    (𝔼 v : I → A, ∏ j, g (v (t j))) = 0 := by
  calc
    _ = 𝔼 v : I → A, ∏ i, (g (v i))^(univ.filter (fun j ↦ t j = i)).card := by
      apply expect_congr rfl
      intro v _
      exact prod_comp_eq_prod_fiber_pow t (fun i ↦ g (v i))
    _ = ∏ i, 𝔼 a, (g a)^(univ.filter (fun j ↦ t j = i)).card :=
      expect_pi_prod (I := I) (A := A) (fun i a ↦ (g a)^(univ.filter (fun j ↦ t j = i)).card)
    _ = 0 := by
      obtain ⟨i, hi⟩ := hs
      apply prod_eq_zero (mem_univ i)
      simpa only [hi, pow_one] using hg

/-- A product of d real numbers is at most the sum of their d-th powers when d is even. -/
lemma prod_le_sum_even_powers {J : Type*} [Fintype J] [Nonempty J]
    {d : ℕ} (hd : Fintype.card J = d) (he : Even d) (f : J → ℝ) :
    (∏ j, f j) ≤ ∑ j, (f j)^d := by
  classical
  obtain ⟨j,hj,hmax⟩ := exists_max_image univ (fun j ↦ |f j|) univ_nonempty
  calc
    _ ≤ |∏ j, f j| := le_abs_self _
    _ = ∏ j, |f j| := abs_prod _ _
    _ ≤ ∏ _i : J, |f j| := prod_le_prod (fun i _ ↦ abs_nonneg _) hmax
    _ = (f j)^d := by rw [prod_const, card_univ, hd, he.pow_abs]
    _ ≤ _ := single_le_sum (fun i _ ↦ he.pow_nonneg _) hj

lemma expect_prod_comp_le {I J A : Type*} [Fintype I] [Fintype J] [Nonempty J]
    [Fintype A] [Nonempty A] {d : ℕ} (hd : Fintype.card J = d) (he : Even d)
    (g : A → ℝ) (t : J → I) :
    (𝔼 v : I → A, ∏ j, g (v (t j))) ≤ (d : ℝ)*(𝔼 a, (g a)^d) := by
  calc
    _ ≤ 𝔼 v : I → A, ∑ j, (g (v (t j)))^d :=
      expect_le_expect (fun v _ ↦ prod_le_sum_even_powers hd he _)
    _ = ∑ j : J, 𝔼 v : I → A, (g (v (t j)))^d := expect_sum_comm _ _ _
    _ = ∑ _j : J, 𝔼 a, (g a)^d := by
      apply sum_congr rfl
      intro j _
      exact expect_pi_apply (t j) (fun a ↦ (g a)^d)
    _ = _ := by simp [hd]

lemma range_card_le_half_of_no_singleton {I J : Type*} [Fintype I] [Fintype J]
    {m : ℕ} (hJ : Fintype.card J = 2*m) (t : J → I)
    (ht : ∀ i, (univ.filter (fun j ↦ t j = i)).card ≠ 1) :
    (univ.image t).card ≤ m := by
  have hcount : 2*(univ.image t).card ≤ Fintype.card J := by
    calc
      _ = ∑ _i ∈ univ.image t, 2 := by simp [mul_comm]
      _ ≤ ∑ i ∈ univ.image t, (univ.filter (fun j ↦ t j = i)).card := by
        apply sum_le_sum
        intro i hi
        obtain ⟨j,_,hj⟩ := mem_image.mp hi
        have hp : 0 < (univ.filter (fun j ↦ t j = i)).card :=
          card_pos.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
        have hn := ht i
        omega
      _ = Fintype.card J :=
        (card_eq_sum_card_fiberwise (fun j _ ↦ mem_image.mpr ⟨j,mem_univ _,rfl⟩)).symm
  omega

/-- Enumerate a small image with m slots and then specify the slot at every input. -/
lemma card_low_range_maps_le {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (m : ℕ) :
    (univ.filter (fun t : J → I ↦ (univ.image t).card ≤ m)).card ≤
      (Fintype.card I)^m * m^(Fintype.card J) := by
  classical
  let compose : ((Fin m → I) × (J → Fin m)) → (J → I) := fun uv ↦ uv.1 ∘ uv.2
  have hsurj : Set.SurjOn compose (univ : Finset ((Fin m → I) × (J → Fin m)))
      (univ.filter (fun t : J → I ↦ (univ.image t).card ≤ m)) := by
    intro t ht
    let S := univ.image t
    have hSc : Fintype.card S ≤ Fintype.card (Fin m) := by
      simpa only [Fintype.card_coe, Fintype.card_fin, S] using (mem_filter.mp ht).2
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hSc
    have hSn : S.Nonempty := by
      exact ⟨t (Classical.choice (inferInstance : Nonempty J)), mem_image.mpr
        ⟨Classical.choice (inferInstance : Nonempty J),mem_univ _,rfl⟩⟩
    letI : Nonempty S := hSn.to_subtype
    let u : Fin m → I := fun i ↦ (Function.invFun e i : S)
    let v : J → Fin m := fun j ↦ e ⟨t j,mem_image.mpr ⟨j,mem_univ _,rfl⟩⟩
    refine ⟨(u,v),mem_univ _,?_⟩
    funext j
    exact congrArg Subtype.val (Function.leftInverse_invFun e.injective ⟨t j,mem_image.mpr ⟨j,mem_univ _,rfl⟩⟩)
  simpa only [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using
    card_le_card_of_surjOn compose hsurj

lemma card_no_singleton_maps_le {I : Type*} [Fintype I] {m : ℕ} (hm : 0 < m) :
    (univ.filter (fun t : Fin (2*m) → I ↦
      ∀ i, (univ.filter (fun j ↦ t j = i)).card ≠ 1)).card ≤
      (Fintype.card I)^m * m^(2*m) := by
  letI : NeZero (2*m) := ⟨by omega⟩
  calc
    _ ≤ (univ.filter (fun t : Fin (2*m) → I ↦ (univ.image t).card ≤ m)).card := by
      apply card_le_card
      intro t ht
      exact mem_filter.mpr ⟨mem_univ _, range_card_le_half_of_no_singleton (by simp) t (mem_filter.mp ht).2⟩
    _ ≤ _ := by
      convert card_low_range_maps_le (I := I) (J := Fin (2*m)) m using 1
      · congr 1
        ext t
        simp
      · simp

#print axioms expect_prod_comp_eq_zero

/-- Singleton fibers vanish; all remaining moment terms have at most m distinct sample indices. -/
lemma centered_sum_even_moment {I A : Type*} [Fintype I] [Fintype A] [Nonempty A]
    (g : A → ℝ) (hg : (𝔼 a, g a) = 0) {m : ℕ} (hm : 0 < m) :
    (𝔼 v : I → A, (∑ i, g (v i))^(2*m)) ≤
      (2*m : ℝ)*(Fintype.card I : ℝ)^m*(m : ℝ)^(2*m)*(𝔼 a, (g a)^(2*m)) := by
  classical
  letI : NeZero (2*m) := ⟨by omega⟩
  let Q := univ.filter (fun t : Fin (2*m) → I ↦
    ∀ i, (univ.filter (fun j ↦ t j = i)).card ≠ 1)
  let H : (Fin (2*m) → I) → ℝ := fun t ↦ 𝔼 v : I → A, ∏ j, g (v (t j))
  have hpow (v : I → A) : (∑ i, g (v i))^(2*m) =
      ∑ t : Fin (2*m) → I, ∏ j, g (v (t j)) := by
    simpa using sum_pow' univ (fun i ↦ g (v i)) (2*m)
  have hzero : ∑ t : Fin (2*m) → I, H t = ∑ t ∈ Q, H t := by
    symm
    apply sum_subset (subset_univ _)
    intro t _ ht
    have hs : ∃ i, (univ.filter (fun j ↦ t j = i)).card = 1 := by
      simpa only [Q, mem_filter, mem_univ, true_and, not_forall, not_not] using ht
    exact expect_prod_comp_eq_zero g hg t hs
  have hc : (Q.card : ℝ) ≤ (Fintype.card I : ℝ)^m*(m : ℝ)^(2*m) := by
    have hh : Q.card ≤ (Fintype.card I)^m*m^(2*m) := by
      convert card_no_singleton_maps_le (I := I) hm using 1
    exact_mod_cast hh
  have hnonneg : 0 ≤ (2*m : ℝ)*(𝔼 a, (g a)^(2*m)) := by
    apply mul_nonneg (by positivity)
    exact expect_nonneg (fun a _ ↦ (even_two_mul m).pow_nonneg _)
  calc
    _ = ∑ t : Fin (2*m) → I, H t := by
      simp_rw [hpow]
      exact expect_sum_comm _ _ _
    _ = ∑ t ∈ Q, H t := hzero
    _ ≤ ∑ _t ∈ Q, (2*m : ℝ)*(𝔼 a, (g a)^(2*m)) := by
      apply sum_le_sum
      intro t _
      simpa only [H, Nat.cast_mul, Nat.cast_ofNat] using
        expect_prod_comp_le (by simp) (even_two_mul m) g t
    _ = (Q.card : ℝ)*((2*m : ℝ)*(𝔼 a, (g a)^(2*m))) := by simp
    _ ≤ ((Fintype.card I : ℝ)^m*(m : ℝ)^(2*m))*((2*m : ℝ)*(𝔼 a, (g a)^(2*m))) :=
      mul_le_mul_of_nonneg_right hc hnonneg
    _ = _ := by ring

lemma expect_even_pow_le {A : Type*} [Fintype A] [Nonempty A]
    {d : ℕ} (hd : Even d) (f : A → ℝ) : (𝔼 a, f a)^d ≤ 𝔼 a, (f a)^d := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hh := Real.pow_arith_mean_le_arith_mean_pow_of_even univ
    (fun _ : A ↦ 1/(Fintype.card A : ℝ)) f (fun _ _ ↦ by positivity)
    (by simp [hc]) hd
  simpa only [← mul_sum, one_div, ← div_eq_inv_mul, Fintype.expect_eq_sum_div_card, ← sum_div] using hh

lemma even_pow_sub_le {d : ℕ} (hd : Even d) (x y : ℝ) :
    (x-y)^d ≤ (2^d/2)*((x^d)+(y^d)) := by
  have hh := expect_even_pow_le hd ![x,-y]
  simp only [Fintype.expect_eq_sum_div_card, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Fintype.card_fin,
    hd.neg_pow, ← sub_eq_add_neg] at hh
  calc
    (x-y)^d = 2^d*((x-y)/2)^d := by rw [div_pow]; field_simp
    _ ≤ 2^d*((x^d+y^d)/2) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

lemma expect_center_even_pow_le {A : Type*} [Fintype A] [Nonempty A]
    {d : ℕ} (hd : Even d) (f : A → ℝ) :
    (𝔼 a, (f a - 𝔼 b, f b)^d) ≤ 2^d*(𝔼 a, (f a)^d) := by
  calc
    _ ≤ 𝔼 a, (2^d/2)*((f a)^d+(𝔼 b, f b)^d) :=
      expect_le_expect (fun a _ ↦ even_pow_sub_le hd _ _)
    _ = (2^d/2)*((𝔼 a, (f a)^d)+(𝔼 b, f b)^d) := by
      rw [← mul_expect, expect_add_distrib, Fintype.expect_const]
    _ ≤ (2^d/2)*((𝔼 a, (f a)^d)+(𝔼 b, (f b)^d)) := by
      gcongr
      exact expect_even_pow_le hd f
    _ = _ := by ring

/-- A polynomial-in-the-moment sampling estimate (with deliberately non-optimal constants). -/
theorem sample_mean_even_moment {I A : Type*} [Fintype I] [Nonempty I]
    [Fintype A] [Nonempty A] (f : A → ℝ) {m : ℕ} (hm : 0 < m) :
    (𝔼 v : I → A, ((𝔼 i, f (v i)) - (𝔼 a, f a))^(2*m)) ≤
      ((2*m : ℝ)*(2*m : ℝ)^(2*m) / (Fintype.card I : ℝ)^m) * (𝔼 a, (f a)^(2*m)) := by
  let g : A → ℝ := fun a ↦ f a - 𝔼 b, f b
  have hg : (𝔼 a, g a) = 0 := by simp [g, expect_sub_distrib]
  have hm' (v : I → A) : (𝔼 i, f (v i)) - (𝔼 a, f a) = 𝔼 i, g (v i) := by
    simp [g, expect_sub_distrib]
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hbase := centered_sum_even_moment (I := I) g hg hm
  have hcenter : (𝔼 a, (g a)^(2*m)) ≤ 2^(2*m)*(𝔼 a, (f a)^(2*m)) :=
    expect_center_even_pow_le (even_two_mul m) f
  calc
    _ = (𝔼 v : I → A, (∑ i, g (v i))^(2*m)) / (Fintype.card I : ℝ)^(2*m) := by
      calc
        _ = 𝔼 v : I → A, (∑ i, g (v i))^(2*m) / (Fintype.card I : ℝ)^(2*m) := by
          apply expect_congr rfl
          intro v _
          rw [hm', Fintype.expect_eq_sum_div_card, div_pow]
        _ = _ := (expect_div _ _ _).symm
    _ ≤ ((2*m : ℝ)*(Fintype.card I : ℝ)^m*(m : ℝ)^(2*m)*(𝔼 a, (g a)^(2*m))) /
        (Fintype.card I : ℝ)^(2*m) :=
      div_le_div_of_nonneg_right hbase (by positivity)
    _ = ((2*m : ℝ)*(m : ℝ)^(2*m) / (Fintype.card I : ℝ)^m)*(𝔼 a, (g a)^(2*m)) := by
      rw [show 2*m = m+m by omega, pow_add]
      field_simp
      ring
    _ ≤ ((2*m : ℝ)*(m : ℝ)^(2*m) / (Fintype.card I : ℝ)^m)*(2^(2*m)*(𝔼 a, (f a)^(2*m))) :=
      mul_le_mul_of_nonneg_left hcenter (by positivity)
    _ = _ := by rw [mul_pow]; ring

#print axioms card_no_singleton_maps_le

/-- Sum the scalar even-moment sampling bound over arbitrary finite coordinates. -/
lemma sample_mean_even_moment_sum {I A X : Type*} [Fintype I] [Nonempty I]
    [Fintype A] [Nonempty A] [Fintype X] (f : A → X → ℝ) {m : ℕ} (hm : 0 < m) :
    (𝔼 v : I → A, ∑ x, ((𝔼 i, f (v i) x) - (𝔼 a, f a x))^(2*m)) ≤
      ((2*m : ℝ)*(2*m : ℝ)^(2*m) / (Fintype.card I : ℝ)^m) *
        (∑ x, 𝔼 a, (f a x)^(2*m)) := by
  rw [expect_sum_comm, mul_sum]
  apply sum_le_sum
  intro x _
  exact sample_mean_even_moment (I := I) (fun a ↦ f a x) hm

/-- At least half of all samples have controlled even-moment error. -/
theorem many_good_moment_samples {I A X : Type*} [Fintype I] [Nonempty I]
    [Fintype A] [Nonempty A] [Fintype X] (f : A → X → ℝ) {m : ℕ} (hm : 0 < m) :
    ∃ L : Finset (I → A), Fintype.card (I → A) ≤ 2*L.card ∧
      ∀ v ∈ L, (∑ x, ((𝔼 i, f (v i) x) - (𝔼 a, f a x))^(2*m)) ≤
        2*((2*m : ℝ)*(2*m : ℝ)^(2*m) / (Fintype.card I : ℝ)^m) *
          (∑ x, 𝔼 a, (f a x)^(2*m)) := by
  classical
  let E : (I → A) → ℝ := fun v ↦ ∑ x, ((𝔼 i, f (v i) x) - (𝔼 a, f a x))^(2*m)
  let B : ℝ := ((2*m : ℝ)*(2*m : ℝ)^(2*m) / (Fintype.card I : ℝ)^m) *
    (∑ x, 𝔼 a, (f a x)^(2*m))
  have hB : 0 ≤ B := by
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun x _ ↦ expect_nonneg (fun a _ ↦ (even_two_mul m).pow_nonneg _))
  have hE (v : I → A) : 0 ≤ E v :=
    sum_nonneg (fun x _ ↦ (even_two_mul m).pow_nonneg _)
  have hmean : (𝔼 v, E v) ≤ B := sample_mean_even_moment_sum f hm
  have hsum : (∑ v, E v) ≤ Fintype.card (I → A)*B := by
    calc
      _ = Fintype.card (I → A)*(𝔼 v, E v) := (Fintype.card_mul_expect E).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)
  refine ⟨univ.filter (fun v ↦ E v ≤ 2*B), card_le_two_card_sublevel E hB hE hsum, ?_⟩
  intro v hv
  have hh := (mem_filter.mp hv).2
  dsimp only [E, B] at hh
  convert hh using 1
  ring

#print axioms sample_mean_even_moment
#print axioms many_good_moment_samples
end Erdos3FiniteSamplingMoments
