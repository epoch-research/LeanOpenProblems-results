import FormalConjecturesUtil

/-! A divergent reciprocal sum need not survive any fixed positive shift intersection.
This is an obstruction to an induction strategy, not a counterexample to the conjecture. -/

namespace Erdos3IntersectionCheck

set_option maxHeartbeats 1000000

def spaced (n : ℕ) : ℕ := n * (Nat.log 2 n + 1)
def spacedRange : Set ℕ := Set.range spaced

theorem spaced_strictMono : StrictMono spaced := by
  intro m n hmn
  have hlog := Nat.log_mono_right (b := 2) hmn.le
  calc
    spaced m < n * (Nat.log 2 m + 1) :=
      Nat.mul_lt_mul_of_pos_right hmn (by omega)
    _ ≤ spaced n := Nat.mul_le_mul_left _ (by omega)

theorem spaced_pos {n : ℕ} (hn : 0 < n) : 0 < spaced n :=
  Nat.mul_pos hn (by omega)

theorem not_summable_spaced : ¬ Summable (fun n : ℕ ↦ 1 / (spaced n : ℝ)) := by
  intro hs
  have hmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n →
      1 / (spaced n : ℝ) ≤ 1 / (spaced m : ℝ) := by
    intro m n hm hmn
    exact one_div_le_one_div_of_le (by exact_mod_cast spaced_pos hm)
      (by exact_mod_cast spaced_strictMono.monotone hmn)
  have hc := (summable_condensed_iff_of_nonneg (fun n ↦ by positivity) hmono).mpr hs
  have heq (j : ℕ) : (2 : ℝ) ^ j * (1 / (spaced (2 ^ j) : ℝ)) = 1 / ((j + 1 : ℕ) : ℝ) := by
    unfold spaced
    rw [Nat.log_pow (by norm_num : 1 < 2)]
    push_cast
    field_simp
  have hc' : Summable (fun j : ℕ ↦ 1 / ((j + 1 : ℕ) : ℝ)) := hc.congr heq
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hc')

theorem spacedRange_divergent : ¬ Summable (fun a : spacedRange ↦ 1 / (a : ℝ)) := by
  intro hs
  let f : ℕ → spacedRange := fun n ↦ ⟨spaced n, ⟨n, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply spaced_strictMono.injective
    change spaced i = spaced j
    exact congrArg Subtype.val hij
  have hp : Summable (fun n : ℕ ↦ 1 / (spaced n : ℝ)) := hs.comp_injective (i := f) hf
  exact not_summable_spaced hp

theorem fixed_shift_intersection_finite (d : ℕ) (hd : 0 < d) :
    {n : ℕ | n ∈ spacedRange ∧ n + d ∈ spacedRange}.Finite := by
  apply ((Set.finite_Iio (2 ^ d)).image spaced).subset
  rintro n ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
  refine ⟨i, ?_, rfl⟩
  change i < 2 ^ d
  have hij : i < j := spaced_strictMono.lt_iff_lt.mp (by omega : spaced i < spaced j)
  have hgap : spaced i + (Nat.log 2 i + 1) ≤ spaced j := by
    calc
      spaced i + (Nat.log 2 i + 1) = (i + 1) * (Nat.log 2 i + 1) := by
        dsimp [spaced]
        ring
      _ ≤ j * (Nat.log 2 i + 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ spaced j := Nat.mul_le_mul_left _ (by
        have := Nat.log_mono_right (b := 2) hij.le
        omega)
  by_contra hlarge
  have hlog := Nat.log_mono_right (b := 2) (show 2 ^ d ≤ i by omega)
  rw [Nat.log_pow (by norm_num : 1 < 2)] at hlog
  omega

/-- No fixed positive shift preserves the reciprocal-divergence hypothesis for this set. -/
theorem fixed_shift_intersection_summable (d : ℕ) (hd : 0 < d) :
    Summable (fun a : {n : ℕ | n ∈ spacedRange ∧ n + d ∈ spacedRange} ↦ 1 / (a : ℝ)) := by
  letI := (fixed_shift_intersection_finite d hd).fintype
  exact (hasSum_fintype _).summable

theorem intersection_divergence_reduction_fails :
    ¬ (∀ A : Set ℕ, (¬ Summable (fun a : A ↦ 1 / (a : ℝ))) →
      ∃ d : ℕ, 0 < d ∧
        ¬ Summable (fun a : {n : ℕ | n ∈ A ∧ n + d ∈ A} ↦ 1 / (a : ℝ))) := by
  intro h
  obtain ⟨d, hd, hdiv⟩ := h spacedRange spacedRange_divergent
  exact hdiv (fixed_shift_intersection_summable d hd)

#print axioms intersection_divergence_reduction_fails

/-- The example does contain progressions of every finite length: its logarithmic blocks
are themselves arithmetic progressions. Thus it is not a disproof of the original conjecture. -/
theorem spacedRange_contains_ap (k : ℕ) :
    ∃ S ⊆ spacedRange, S.IsAPOfLength k := by
  let a := 2 ^ k * (k + 1)
  let d := k + 1
  let f : ℕ → ℕ := fun i ↦ a + i * d
  have hinj : Function.Injective f := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (Nat.add_left_cancel hij)
  refine ⟨f '' Set.Iio k, ?_, a, d, ?_, ?_⟩
  · rintro x ⟨i, hi, rfl⟩
    refine ⟨2 ^ k + i, ?_⟩
    have hi' : i < 2 ^ k := lt_trans hi Nat.lt_two_pow_self
    have hlog : Nat.log 2 (2 ^ k + i) = k :=
      Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [pow_succ]; omega)
    dsimp [f, a, d]
    rw [spaced, hlog]
    ring
  · change (f '' Set.Iio k).encard = (k : ℕ∞)
    rw [hinj.encard_image]
    exact Set.Nat.encard_range k
  · ext x
    simp [f]

#print axioms spacedRange_contains_ap

end Erdos3IntersectionCheck
