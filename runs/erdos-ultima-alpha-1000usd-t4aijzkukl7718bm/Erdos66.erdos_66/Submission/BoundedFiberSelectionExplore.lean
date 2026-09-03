import Submission.UniformSelectionExplore

/-! Uniform avoidance with nontrivial bounded fibers, for predecessor-cell
collisions. Different forbidden events can have different fiber bounds. -/
namespace Erdos66BoundedFiberSelection
open Erdos66UniformSelection
open scoped Classical
set_option maxHeartbeats 1800000
variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
  [DecidableEq ι] [DecidableEq α]

lemma bounded_fiber_indicator_bound (P : (ι → α) → Prop) (i : ι) (H : ℕ)
    (hP : ∀ f : ι → α, (Finset.univ.filter (fun a ↦ P (Function.update f i a))).card ≤ H) :
    mean (fun ω : ι → α ↦ if P ω then (1 : ℝ) else 0) ≤ H / (Fintype.card α : ℝ) := by
  let a₀ : α := Classical.choice inferInstance
  let B : Finset (ι → α) := Finset.univ.filter P
  let U : Finset (ι → α) := Finset.univ.filter (fun f ↦ f i = a₀)
  let reset : (ι → α) → (ι → α) := fun f ↦ Function.update f i a₀
  have hmap : ∀ f ∈ B, reset f ∈ U := by
    intro f hf
    simp [reset, U]
  have hfiber : ∀ g ∈ U, (B.filter (fun f ↦ reset f = g)).card ≤ H := by
    intro g hg
    apply le_trans (Finset.card_le_card_of_injOn (fun f : ι → α ↦ f i)
      (t := Finset.univ.filter (fun a ↦ P (Function.update g i a))) ?_ ?_) (hP g)
    · intro f hf
      obtain ⟨hfB, he⟩ := Finset.mem_filter.mp hf
      have hfP : P f := (Finset.mem_filter.mp hfB).2
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← he]
      simpa [reset] using hfP
    · intro f hf k hk he
      obtain ⟨_, hf⟩ := Finset.mem_filter.mp hf
      obtain ⟨_, hk⟩ := Finset.mem_filter.mp hk
      have hh : reset f = reset k := hf.trans hk.symm
      funext j
      by_cases hji : j = i
      · simpa only [hji] using he
      · have hj := congrFun hh j
        simpa only [reset, Function.update_of_ne hji] using hj
  have hcard : B.card ≤ H * U.card :=
    Finset.card_le_mul_card_image_of_maps_to hmap H hfiber
  have hUcard : U.card = Fintype.card α ^ (Fintype.card ι - 1) := by
    have hh := Fintype.card_filter_piFinset_const_eq_of_mem
      (Finset.univ : Finset α) i (Finset.mem_univ a₀)
    simpa only [Fintype.piFinset_univ, Finset.card_univ] using hh
  rw [hUcard] at hcard
  have hm : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hq : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [mean_indicator, Fintype.card_fun, Nat.cast_pow]
  have hh : (B.card : ℝ) ≤ H * (Fintype.card α : ℝ) ^ (Fintype.card ι - 1) :=
    by exact_mod_cast hcard
  apply (div_le_div_of_nonneg_right hh (by positivity)).trans_eq
  have hm' : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
  conv_lhs => arg 2; rw [hm', pow_succ]
  field_simp

lemma one_fiber_card_le_one (P : (ι → α) → Prop) (i : ι)
    (hP : ∀ f : ι → α, ∀ x y : α,
      P (Function.update f i x) → P (Function.update f i y) → x = y) (f : ι → α) :
    (Finset.univ.filter (fun a ↦ P (Function.update f i a))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  exact hP f a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

theorem exists_avoid_bounded_fibers_and_small_hits {κ ζ : Type*}
    (E : Finset κ) (P : κ → (ι → α) → Prop) (H : κ → ℕ)
    (hP : ∀ j ∈ E, ∃ i : ι, ∀ f : ι → α,
      (Finset.univ.filter (fun a ↦ P j (Function.update f i a))).card ≤ H j)
    (T : Finset ζ) (S : ζ → Finset α) (K R t : ℝ)
    (hS : ∀ z ∈ T, (S z).card ≤ K) (ht : 0 < t)
    (hsmall : (∑ j ∈ E, (H j : ℝ)) / Fintype.card α +
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
        (∑ j ∈ E, (H j : ℝ)) / (Fintype.card α : ℝ) := by
      calc
        _ ≤ ∑ j ∈ E, (H j : ℝ) / (Fintype.card α : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨i, hi⟩ := hP j hj
          exact bounded_fiber_indicator_bound (P j) i (H j) hi
        _ = _ := by rw [Finset.sum_div]
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


end Erdos66BoundedFiberSelection
