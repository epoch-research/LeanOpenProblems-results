import Submission.ContinuousIntervalEnvelope

/-! Partitioning an interval cannot improve the regular real-valued envelopes.
This does not address extra information from integer survivor counts and does
not establish any asymptotic Jacobsthal bound. -/
namespace Erdos970.ContinuousInterval

lemma convex_nonnegative_add {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Set.Ici 0) f) (hzero : f 0 = 0)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f x + f y ≤ f (x + y) := by
  by_cases hxy : x + y = 0
  · have hxx : x = 0 := by linarith
    have hyy : y = 0 := by linarith
    simp [hxx, hyy, hzero]
  · have hpos : 0 < x + y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hxy)
    have ha : 0 ≤ x / (x + y) := div_nonneg hx hpos.le
    have hb : 0 ≤ y / (x + y) := div_nonneg hy hpos.le
    have hab : x / (x + y) + y / (x + y) = 1 := by
      rw [← add_div, div_self hxy]
    have hfx := hf.2 (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      (show x + y ∈ Set.Ici 0 from hpos.le) hb ha (by linarith)
    have hfy := hf.2 (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      (show x + y ∈ Set.Ici 0 from hpos.le) ha hb hab
    simp only [smul_eq_mul, mul_zero, zero_add, hzero,
      div_mul_cancel₀ _ hxy] at hfx hfy
    calc
      f x + f y ≤ x / (x + y) * f (x + y) + y / (x + y) * f (x + y) :=
        add_le_add hfx hfy
      _ = f (x + y) := by rw [← add_mul, hab, one_mul]

lemma concave_nonnegative_add {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hzero : f 0 = 0)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f (x + y) ≤ f x + f y := by
  have hh := convex_nonnegative_add hf.neg (by simpa using congrArg Neg.neg hzero)
    x y hx hy
  simp only [Pi.neg_apply] at hh
  linarith

lemma Regular.lower_add {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    L x + L y ≤ L (x + y) :=
  convex_nonnegative_add (h.lower_convex.subset (Set.subset_univ _) (convex_Ici 0))
    (h.lower_zero 0 le_rfl) x y hx hy

lemma Regular.upper_add {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    U (x + y) ≤ U x + U y :=
  concave_nonnegative_add h.upper_concave h.upper_zero x y hx hy

/-- No finite partition improves either envelope at the total length. -/
theorem Regular.partition {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    {ι : Type*} (s : Finset ι) (length : ι → ℝ)
    (hlen : ∀ i ∈ s, 0 ≤ length i) :
    (∑ i ∈ s, L (length i)) ≤ L (∑ i ∈ s, length i) ∧
      U (∑ i ∈ s, length i) ≤ ∑ i ∈ s, U (length i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.lower_zero 0 le_rfl, h.upper_zero]
  | @insert a s has ih =>
    have ha := hlen a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, 0 ≤ length i := fun i hi => hlen i (Finset.mem_insert_of_mem hi)
    have hi := ih hs
    have hsum : 0 ≤ ∑ i ∈ s, length i := Finset.sum_nonneg hs
    simp only [Finset.sum_insert has]
    exact ⟨(add_le_add le_rfl hi.1).trans (h.lower_add _ _ ha hsum),
      (h.upper_add _ _ ha hsum).trans (add_le_add le_rfl hi.2)⟩

#print axioms Regular.partition
end Erdos970.ContinuousInterval
