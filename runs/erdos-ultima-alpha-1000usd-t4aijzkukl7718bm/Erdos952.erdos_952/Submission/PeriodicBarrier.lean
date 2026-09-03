import FormalConjecturesUtil

/-! A finite-height periodic barrier excludes every infinite king-neighbor path. -/

namespace Erdos952Investigation.PeriodicBarrier

set_option maxHeartbeats 0

def KingStep (z w : ℤ × ℤ) : Prop :=
  |w.1 - z.1| ≤ 1 ∧ |w.2 - z.2| ≤ 1

structure Barrier (A : ℤ × ℤ → Prop) where
  height : ℤ
  height_nonneg : 0 ≤ height
  region : Set (ℤ × ℤ)
  start : ∀ v, A (0, v) → (0, v) ∈ region
  upper : ∀ z ∈ region, z.1 ≤ height
  closed : ∀ z ∈ region, ∀ w, A z → A w → KingStep z w → 0 ≤ w.1 → w ∈ region

lemma barrier_bound {A : ℤ × ℤ → Prop} (b : Barrier A) (x : ℕ → ℤ × ℤ)
    (hA : ∀ n, A (x n)) (hstep : ∀ n, KingStep (x n) (x (n + 1)))
    (h0 : (x 0).1 ≤ 0) : ∀ n, (x n).1 ≤ b.height := by
  have hregion : ∀ n, (x n).1 ≤ 0 ∨ x n ∈ b.region := by
    intro n
    induction n with
    | zero => exact Or.inl h0
    | succ n ih =>
      by_cases hn : (x (n + 1)).1 ≤ 0
      · exact Or.inl hn
      apply Or.inr
      apply b.closed (x n) _ (x (n + 1)) (hA n) (hA (n + 1)) (hstep n) (by omega)
      rcases ih with hi | hi
      · have he : (x n).1 = 0 := by
          have := (abs_le.mp (hstep n).1).2
          omega
        have hpoint : x n = (0, (x n).2) := by ext <;> simp [he]
        rw [hpoint]
        exact b.start _ (hpoint ▸ hA n)
      · exact hi
  intro n
  rcases hregion n with hn | hn
  · exact hn.trans b.height_nonneg
  · exact b.upper _ hn

lemma upper_bound {A : ℤ × ℤ → Prop} (b : Barrier A) (P : ℤ) (hP : 0 < P)
    (hperiod : ∀ k : ℤ, ∀ z, A z → A (z.1 - k * P, z.2))
    (x : ℕ → ℤ × ℤ) (hA : ∀ n, A (x n))
    (hstep : ∀ n, KingStep (x n) (x (n + 1))) :
    ∃ B : ℤ, ∀ n, (x n).1 ≤ B := by
  let k : ℤ := |(x 0).1| + 1
  let y : ℕ → ℤ × ℤ := fun n => ((x n).1 - k * P, (x n).2)
  have hyA : ∀ n, A (y n) := fun n => hperiod k (x n) (hA n)
  have hys : ∀ n, KingStep (y n) (y (n + 1)) := by
    intro n
    simpa only [KingStep, y, sub_sub_sub_cancel_right] using hstep n
  have hy0 : (y 0).1 ≤ 0 := by
    have h1 : 1 ≤ P := hP
    have hk : 0 ≤ k := by dsimp [k]; positivity
    have hx := le_abs_self (x 0).1
    dsimp [y, k]
    nlinarith
  obtain hb := barrier_bound b y hyA hys hy0
  refine ⟨k * P + b.height, fun n => ?_⟩
  have := hb n
  dsimp [y] at this
  omega

lemma bounds {A : ℤ × ℤ → Prop} (b : Barrier A) (P : ℤ) (hP : 0 < P)
    (hperiod : ∀ k : ℤ, ∀ z, A z → A (z.1 - k * P, z.2))
    (hreflect : ∀ z, A z → A (-1 - z.1, z.2))
    (x : ℕ → ℤ × ℤ) (hA : ∀ n, A (x n))
    (hstep : ∀ n, KingStep (x n) (x (n + 1))) :
    ∃ L B : ℤ, ∀ n, L ≤ (x n).1 ∧ (x n).1 ≤ B := by
  obtain ⟨B, hB⟩ := upper_bound b P hP hperiod x hA hstep
  let y : ℕ → ℤ × ℤ := fun n => (-1 - (x n).1, (x n).2)
  have hyA : ∀ n, A (y n) := fun n => hreflect (x n) (hA n)
  have hys : ∀ n, KingStep (y n) (y (n + 1)) := by
    intro n
    refine ⟨?_, (hstep n).2⟩
    change |(-1 - (x (n + 1)).1) - (-1 - (x n).1)| ≤ 1
    convert (hstep n).1 using 1
    rw [show (-1 - (x (n + 1)).1) - (-1 - (x n).1) =
      -((x (n + 1)).1 - (x n).1) by ring, abs_neg]
  obtain ⟨B', hB'⟩ := upper_bound b P hP hperiod y hyA hys
  refine ⟨-1 - B', B, fun n => ⟨?_, hB n⟩⟩
  have := hB' n
  dsimp [y] at this
  omega

theorem no_injective_path {A : ℤ × ℤ → Prop} (b : Barrier A) (P : ℤ) (hP : 0 < P)
    (hperiod : ∀ k : ℤ, ∀ z, A z → A (z.1 - k * P, z.2))
    (hreflect : ∀ z, A z → A (-1 - z.1, z.2))
    (hswap : ∀ z, A z → A (z.2, z.1)) :
    ¬ ∃ x : ℕ → ℤ × ℤ, Function.Injective x ∧
      (∀ n, A (x n)) ∧ (∀ n, KingStep (x n) (x (n + 1))) := by
  rintro ⟨x, hx, hA, hstep⟩
  obtain ⟨L, B, h⟩ := bounds b P hP hperiod hreflect x hA hstep
  let y : ℕ → ℤ × ℤ := fun n => ((x n).2, (x n).1)
  have hyA : ∀ n, A (y n) := fun n => hswap (x n) (hA n)
  have hys : ∀ n, KingStep (y n) (y (n + 1)) := fun n => (hstep n).symm
  obtain ⟨L', B', h'⟩ := bounds b P hP hperiod hreflect y hyA hys
  have hf : (Set.Icc L B ×ˢ Set.Icc L' B' : Set (ℤ × ℤ)).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  apply Set.infinite_range_of_injective hx
  apply hf.subset
  rintro z ⟨n, rfl⟩
  exact ⟨h n, h' n⟩

#print axioms no_injective_path

end Erdos952Investigation.PeriodicBarrier
