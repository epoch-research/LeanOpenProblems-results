import FormalConjecturesUtil

/-!
Pruning placements incompatible with a current divisor class does not change
any weighted count test under a measure already avoiding the current family.
This records a limitation of a proposed improvement, not an odd-cover proof.
-/
namespace Erdos7DivisorPlacementPruning

set_option autoImplicit false

/-- A finer congruence class meeting a divisor class is contained in it. -/
theorem nested_coset (d m a b x : ℤ) (hd : d ∣ m) (hab : d ∣ a-b)
    (hx : m ∣ x-a) : d ∣ x-b := by
  convert dvd_add (hd.trans hx) hab using 1 <;> ring

/-- Two congruence classes with comparable moduli are disjoint or nested. -/
theorem disjoint_or_nested (d m a b : ℤ) (hd : d ∣ m) :
    (∀ x : ℤ, m ∣ x-a → ¬ d ∣ x-b) ∨
      (∀ x : ℤ, m ∣ x-a → d ∣ x-b) := by
  by_cases hab : d ∣ a-b
  · exact Or.inr (fun x hx => nested_coset d m a b x hd hab hx)
  · left
    intro x hx hxb
    apply hab
    convert dvd_sub hxb (hd.trans hx) using 1 <;> ring

noncomputable def count {J : Type*} [Fintype J] (P : J → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter P).card

/-- If forbidden hits occur only at zero-weight points, deleting them leaves
an arbitrary test of the total hit count unchanged. No monotonicity, convexity,
or positivity assumption on the test or weights is needed. -/
theorem weighted_test_pruning {X J : Type*} [Fintype X] [Fintype J]
    (w : X → ℝ) (hit : J → X → Prop) (forbidden : J → Prop)
    (hzero : ∀ x j, forbidden j → hit j x → w x = 0) (F : ℕ → ℝ) :
    (∑ x, w x * F (count (fun j => hit j x))) =
      ∑ x, w x * F (count (fun j => ¬ forbidden j ∧ hit j x)) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hw : w x = 0
  · simp only [hw, zero_mul]
  · have he : (fun j => hit j x) = (fun j => ¬ forbidden j ∧ hit j x) := by
      funext j
      apply propext
      exact ⟨fun hj => ⟨fun hb => hw (hzero x j hb hj), hj⟩, And.right⟩
    rw [he]

/-- A proposed future placement is forbidden when it lies in a current class
whose modulus divides its modulus. The current index type need not be finite. -/
def Forbidden {I J : Type*} (d : I → ℤ) (b : I → ℤ)
    (m : J → ℤ) (a : J → ℤ) (j : J) : Prop :=
  ∃ i, d i ∣ m j ∧ d i ∣ a j-b i

/-- Exact arithmetic specialization. It applies to arbitrary finite sampling
spaces, including nonuniform measures on a common residue period. -/
theorem arithmetic_pruning {I X J : Type*} [Fintype X] [Fintype J]
    (z : X → ℤ) (w : X → ℝ) (d b : I → ℤ) (m a : J → ℤ)
    (havoid : ∀ x i, d i ∣ z x-b i → w x = 0) (F : ℕ → ℝ) :
    (∑ x, w x * F (count (fun j => m j ∣ z x-a j))) =
      ∑ x, w x * F (count (fun j => ¬ Forbidden d b m a j ∧ m j ∣ z x-a j)) := by
  apply weighted_test_pruning w (fun j x => m j ∣ z x-a j) (Forbidden d b m a)
  intro x j hj hx
  obtain ⟨i, hdm, hab⟩ := hj
  exact havoid x i (nested_coset (d i) (m j) (a j) (b i) (z x) hdm hab hx)

#print axioms disjoint_or_nested
#print axioms weighted_test_pruning
#print axioms arithmetic_pruning

/-- Monotonicity of the finite hit count. -/
theorem count_mono {J : Type*} [Fintype J] {P Q : J → Prop}
    (h : ∀ j, P j → Q j) : count P ≤ count Q := by
  classical
  unfold count
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h j (Finset.mem_filter.mp hj).2⟩

/-- Move every forbidden placement to one common surviving residue. -/
noncomputable def repaired {I J : Type*} (d b : I → ℤ) (m a : J → ℤ)
    (c : ℤ) (j : J) : ℤ := by
  classical
  exact if Forbidden d b m a j then c else a j

theorem repaired_valid {I J : Type*} (d b : I → ℤ) (m a : J → ℤ)
    (c : ℤ) (hc : ∀ i, ¬ d i ∣ c-b i) :
    ∀ j, ¬ Forbidden d b m (repaired d b m a c) j := by
  classical
  intro j hj
  obtain ⟨i, hdm, hab⟩ := hj
  by_cases hbad : Forbidden d b m a j
  · simp only [repaired, if_pos hbad] at hab
    exact hc i hab
  · simp only [repaired, if_neg hbad] at hab
    exact hbad ⟨i, hdm, hab⟩

/-- Repairing forbidden placements cannot lower any monotone count test under
nonnegative weights avoiding the current family. -/
theorem repaired_test_ge {I X J : Type*} [Fintype X] [Fintype J]
    (z : X → ℤ) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (d b : I → ℤ) (m a : J → ℤ)
    (havoid : ∀ x i, d i ∣ z x-b i → w x = 0)
    (c : ℤ) (F : ℕ → ℝ) (hF : Monotone F) :
    (∑ x, w x * F (count (fun j => m j ∣ z x-a j))) ≤
      ∑ x, w x * F (count (fun j => m j ∣ z x-repaired d b m a c j)) := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : w x = 0
  · simp only [hx, zero_mul, le_refl]
  · apply mul_le_mul_of_nonneg_left _ (hw x)
    apply hF
    apply count_mono
    intro j hj
    have hbad : ¬ Forbidden d b m a j := by
      rintro ⟨i, hdm, hab⟩
      exact hx (havoid x i (nested_coset (d i) (m j) (a j) (b i) (z x) hdm hab hj))
    simpa only [repaired, if_neg hbad] using hj

/-- In the independent-placement model, imposing compatibility with all
current divisor classes does not improve the worst-case monotone count test.
One common repaired family works simultaneously for every monotone test.
This does not impose compatibility constraints BETWEEN future classes. -/
theorem exists_valid_majorant {I X J : Type*} [Fintype X] [Fintype J]
    (z : X → ℤ) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (d b : I → ℤ) (m a : J → ℤ)
    (havoid : ∀ x i, d i ∣ z x-b i → w x = 0)
    (hpos : ∃ x, 0 < w x) :
    ∃ a' : J → ℤ, (∀ j, ¬ Forbidden d b m a' j) ∧
      ∀ F : ℕ → ℝ, Monotone F →
        (∑ x, w x * F (count (fun j => m j ∣ z x-a j))) ≤
          ∑ x, w x * F (count (fun j => m j ∣ z x-a' j)) := by
  obtain ⟨x₀, hx₀⟩ := hpos
  refine ⟨repaired d b m a (z x₀), repaired_valid d b m a (z x₀) ?_, ?_⟩
  · intro i hi
    exact (ne_of_gt hx₀) (havoid x₀ i hi)
  · intro F hF
    exact repaired_test_ge z w hw d b m a havoid (z x₀) F hF
#print axioms repaired_valid
#print axioms repaired_test_ge
#print axioms exists_valid_majorant
end Erdos7DivisorPlacementPruning
