import Submission.SelbergLowerCriterion

/-! Absolute-error lower certificates transfer from larger hit probabilities to smaller ones. -/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem average_one (q : ι → ℝ) : average q (fun _ => 1) = 1 := by
  have hh := average_prod q (fun _ _ => (1 : ℝ))
  simpa using hh

theorem average_const (q : ι → ℝ) (c : ℝ) : average q (fun _ => c) = c := by
  have hh := average_mul_const q (fun _ => (1 : ℝ)) c
  simpa [average_one] using hh

theorem average_mono (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (f g : (ι → Bool) → ℝ) (hfg : ∀ ω, f ω ≤ g ω) : average q f ≤ average q g := by
  have hh := average_nonneg q hq (fun ω => g ω - f ω)
    (fun ω => sub_nonneg.mpr (hfg ω))
  rw [average_sub] at hh
  linarith

/-- Coordinates already hit by the added pattern disappear from each monomial. -/
theorem hitMonomial_or (T : Finset ι) (ω η : ι → Bool) :
    hitMonomial T (fun i => ω i || η i) =
      hitMonomial (T.filter (fun i => η i = false)) ω := by
  classical
  have heq : (∀ i ∈ T, (ω i || η i) = true) ↔
      ∀ i ∈ T.filter (fun i => η i = false), ω i = true := by
    constructor
    · intro h i hi
      have hi' := Finset.mem_filter.mp hi
      simpa [hi'.2] using h i hi'.1
    · intro h i hi
      cases he : η i
      · simpa [he] using h i (Finset.mem_filter.mpr ⟨hi, he⟩)
      · simp [he]
  simp only [hitMonomial_eq, heq]

/-- Adding independent hits replaces each marginal `q` by `a + (1-a)q`. -/
theorem average_restricted_prod (a q : ι → ℝ) (T : Finset ι) :
    average a (fun η => ∏ i ∈ T.filter (fun i => η i = false), q i) =
      ∏ i ∈ T, (a i + (1 - a i) * q i) := by
  classical
  have heq : (fun η : ι → Bool => ∏ i ∈ T.filter (fun i => η i = false), q i) =
      fun η => ∏ i : ι, if i ∈ T then (if η i then 1 else q i) else 1 := by
    funext η
    rw [Finset.prod_filter]
    calc
      _ = ∏ i ∈ T, if η i then 1 else q i := by
        apply Finset.prod_congr rfl
        intro i hi
        cases η i <;> simp
      _ = _ := by simp [Finset.prod_ite_mem]
  rw [heq, average_prod a (fun i b => if i ∈ T then (if b then 1 else q i) else 1)]
  calc
    _ = ∏ i : ι, if i ∈ T then (a i + (1 - a i) * q i) else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hiT : i ∈ T <;> simp only [hiT, if_true, if_false,
        Bool.false_eq_true, mul_one] <;> ring
    _ = _ := by simp [Finset.prod_ite_mem]

/-- A lower polynomial certified at coordinatewise larger hit probabilities works, with the
same absolute remainder allowance, at smaller hit probabilities. This does not assert existence
of a quadratic certificate. -/
theorem survivor_from_dominating_moments {α : Type*} (A : Finset α)
    (c : α → ℝ) (S : α → Finset ι) (q q' : ι → ℝ)
    (hq : ∀ i, q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hpoint : ∀ v : ι → Bool, v ≠ (fun _ => false) →
      (∑ a ∈ A, c a * hitMonomial (S a) v) ≤ 0)
    (hmain : (∑ a ∈ A, |c a|) < (m : ℝ) * ∑ a ∈ A, c a * ∏ i ∈ S a, q' i) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  let b (i : ι) := (q' i - q i) / (1 - q i)
  have hb (i : ι) : 0 ≤ b i ∧ b i ≤ 1 := by
    have hd : 0 < 1 - q i := sub_pos.mpr (hq i).1
    refine ⟨div_nonneg (sub_nonneg.mpr (hq i).2.1) hd.le, ?_⟩
    exact (div_le_one hd).mpr (by linarith [(hq i).2.2])
  have hprob (i : ι) : b i + (1 - b i) * q i = q' i := by
    have hd : 1 - q i ≠ 0 := (sub_pos.mpr (hq i).1).ne'
    dsimp [b]
    field_simp
    ring
  by_contra hbad
  push_neg at hbad
  have hpoint' (η : ι → Bool) :
      (∑ j ∈ Finset.range m, ∑ a ∈ A, c a *
        hitMonomial ((S a).filter (fun i => η i = false)) (ω j)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    simp_rw [← hitMonomial_or]
    apply hpoint
    intro heq
    obtain ⟨i, hi⟩ := hbad j (Finset.mem_range.mp hj)
    have hh := congrFun heq i
    cases hw : ω j i
    · exact hi hw
    · simp [hw] at hh
  have hbound (η : ι → Bool) :
      (m : ℝ) * ∑ a ∈ A, c a * ∏ i ∈ (S a).filter (fun i => η i = false), q i ≤
        ∑ a ∈ A, |c a| := by
    have hh := finite_polynomial_interval_error A c
      (fun a => (S a).filter (fun i => η i = false)) q m ω herr
    rw [average_sum] at hh
    simp_rw [average_mul_const, average_hitMonomial] at hh
    have hlow := (abs_le.mp hh).1
    linarith [hpoint' η]
  have hh := average_mono b hb
    (fun η => (m : ℝ) * ∑ a ∈ A, c a * ∏ i ∈ (S a).filter (fun i => η i = false), q i)
    (fun _ => ∑ a ∈ A, |c a|) hbound
  rw [average_const, average_mul_const, average_sum] at hh
  simp_rw [average_mul_const, average_restricted_prod, hprob] at hh
  exact hmain.not_ge hh

#print axioms survivor_from_dominating_moments

end Erdos970.FiniteSelberg
