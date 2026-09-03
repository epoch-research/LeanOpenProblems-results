import Submission.CyclicThickeningExplore
import Submission.RectangleRepairExplore

/-! Mixed-count carry transfer. These statements concern finite cyclic groups. -/
namespace Erdos66MixedCyclicThickening
open Erdos66CyclicThickening Erdos66CarryAveraging

noncomputable def mixedConv {m : ℕ} [NeZero m]
    (w v : ZMod m → ℝ) (z : ZMod m) : ℝ := ∑ x, w x * v (z - x)

variable (p K : ℕ) [NeZero p] [NeZero K]

noncomputable def mixedFiber (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p) :
    Finset (ZMod p × ZMod p) := B.filter (fun a ↦ (t - a.1, s - a.2) ∈ C)

lemma lift_convolution_digits (w v : ZMod p × ZMod p → ℝ) (t s : ZMod (p * K)) :
    mixedConv (liftWeight p K w) (liftWeight p K v) (cyclicEncode (p * K) (t, s)) =
      ∑ x : ZMod (p * K), ∑ y : ZMod (p * K),
        w (reduceDigit p K x, reduceDigit p K y) *
          v (reduceDigit p K t - reduceDigit p K x,
            reduceDigit p K s - reduceDigit p K y - (borrow (p * K) t x : ZMod p)) := by
  unfold mixedConv
  rw [← Equiv.sum_comp (cyclicDigitEquiv (p * K)), Fintype.sum_prod_type]
  simp only [cyclicDigitEquiv, Equiv.ofBijective_apply, cyclicEncode_sub,
    liftWeight_encode, map_sub, map_natCast]


lemma lift_convolution_formula (w v : ZMod p × ZMod p → ℝ)
    (t : ZMod p) (q : Fin K) (s : ZMod (p * K)) :
    mixedConv (liftWeight p K w) (liftWeight p K v)
        (cyclicEncode (p * K) (blockDigit p K t q, s)) =
      (K : ℝ) * ∑ a : ZMod p, ∑ u : ZMod p,
        w (a, u) * ((lowCutoff p K q t a : ℝ) *
          v (t - a, reduceDigit p K s - u) +
          ((K : ℝ) - lowCutoff p K q t a) *
          v (t - a, reduceDigit p K s - u - 1)) := by
  rw [lift_convolution_digits, reduce_block]
  rw [← Equiv.sum_comp (blockEquiv p K), Fintype.sum_prod_type]
  simp only [blockEquiv, Equiv.ofBijective_apply, reduce_block, borrow_block]
  calc
    _ = ∑ a : ZMod p, ∑ i : Fin K, ∑ u : ZMod p,
        (K : ℝ) * (w (a, u) * v (t - a, reduceDigit p K s - u -
          ((if i.val < lowCutoff p K q t a then 0 else 1 : ℕ) : ZMod p))) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Equiv.sum_comp (blockEquiv p K), Fintype.sum_prod_type]
      simp only [blockEquiv, Equiv.ofBijective_apply, reduce_block,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ a : ZMod p, ∑ u : ZMod p, ∑ i : Fin K,
        (K : ℝ) * (w (a, u) * v (t - a, reduceDigit p K s - u -
          ((if i.val < lowCutoff p K q t a then 0 else 1 : ℕ) : ZMod p))) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      congr 2
      simp only [Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
      simp_rw [sub_ite, sub_zero, apply_ite (fun z ↦ v (t - a, z))]
      exact sum_fin_cutoff K (lowCutoff p K q t a) (lowCutoff_le p K q t a) _ _



lemma set_weight_fibers (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p)
    (g h : ZMod p × ZMod p → ℝ) :
    (∑ a : ZMod p, ∑ u : ZMod p, setWeight B (a, u) *
      (g (a, u) * setWeight C (t - a, s - u) +
        h (a, u) * setWeight C (t - a, s - u - 1))) =
      (∑ z ∈ mixedFiber p B C t s, g z) + ∑ z ∈ mixedFiber p B C t (s - 1), h z := by
  classical
  rw [← Fintype.sum_prod_type (fun z : ZMod p × ZMod p ↦ setWeight B z *
    (g z * setWeight C (t - z.1, s - z.2) +
      h z * setWeight C (t - z.1, s - z.2 - 1)))]
  simp only [mixedFiber, Finset.sum_filter, setWeight]
  have he : ∀ z : ZMod p × ZMod p,
      (if z ∈ B then (1 : ℝ) else 0) *
        (g z * (if (t - z.1, s - z.2) ∈ C then 1 else 0) +
          h z * (if (t - z.1, s - z.2 - 1) ∈ C then 1 else 0)) =
      (if z ∈ B then (if (t - z.1, s - z.2) ∈ C then g z else 0) else 0) +
        (if z ∈ B then (if (t - z.1, s - 1 - z.2) ∈ C then h z else 0) else 0) := by
    intro z
    rw [show s - 1 - z.2 = s - z.2 - 1 by ring]
    split_ifs <;> ring
  simp only [he, Finset.sum_add_distrib]
  simp


lemma lift_set_convolution_formula (B C : Finset (ZMod p × ZMod p))
    (t : ZMod p) (q : Fin K) (s : ZMod (p * K)) :
    mixedConv (liftWeight p K (setWeight B)) (liftWeight p K (setWeight C))
        (cyclicEncode (p * K) (blockDigit p K t q, s)) =
      (K : ℝ) * ((∑ z ∈ mixedFiber p B C t (reduceDigit p K s),
        (triangle K ((q.val : ℤ) - smallBorrow p t z.1) : ℝ)) +
        ∑ z ∈ mixedFiber p B C t (reduceDigit p K s - 1),
          (triangle K ((q.val : ℤ) + K - smallBorrow p t z.1) : ℝ)) := by
  rw [lift_convolution_formula]
  simp_rw [cutoff_complement_triangle, cutoff_triangle]
  congr 1
  exact set_weight_fibers p B C t (reduceDigit p K s)
    (fun z ↦ (triangle K ((q.val : ℤ) - smallBorrow p t z.1) : ℝ))
    (fun z ↦ (triangle K ((q.val : ℤ) + K - smallBorrow p t z.1) : ℝ))


lemma mixedConv_setWeight {m : ℕ} [NeZero m] (C D : Finset (ZMod m)) (z : ZMod m) :
    mixedConv (setWeight C) (setWeight D) z = ((C.filter (fun a ↦ z - a ∈ D)).card : ℝ) := by
  classical
  simp only [mixedConv, setWeight, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]

/-- Coordinate thickening converts flat two-coordinate counts into flat counts
in an actual cyclic group, with an explicit carry error. -/
theorem thickenedSet_error (B C : Finset (ZMod p × ZMod p)) (μ E : ℝ)
    (hB : ∀ t s : ZMod p, |((mixedFiber p B C t s).card : ℝ) - μ| ≤ E)
    (z : ZMod ((p * K) ^ 2)) :
    |(((thickenedSet p K B).filter (fun a ↦ z - a ∈ thickenedSet p K C)).card : ℝ) -
      (K : ℝ) ^ 2 * μ| ≤ (K : ℝ) ^ 2 * E + 2 * K * (μ + E) := by
  obtain ⟨⟨x, s⟩, rfl⟩ := (cyclicDigitEquiv (p * K)).surjective z
  obtain ⟨⟨t, q⟩, rfl⟩ := (blockEquiv p K).surjective x
  change |(((thickenedSet p K B).filter (fun a ↦
    cyclicEncode (p * K) (blockDigit p K t q, s) - a ∈ thickenedSet p K C)).card : ℝ) -
      (K : ℝ) ^ 2 * μ| ≤ _
  rw [← mixedConv_setWeight, thickenedSet_weight, thickenedSet_weight, lift_set_convolution_formula]
  exact two_fiber_error (mixedFiber p B C t (reduceDigit p K s))
    (mixedFiber p B C t (reduceDigit p K s - 1)) (fun a ↦ smallBorrow p t a.1)
    (fun a _ ↦ smallBorrow_cases p t a.1) (fun a _ ↦ smallBorrow_cases p t a.1)
    K q.val q.isLt μ E (hB _ _) (hB _ _)


lemma thickenedSet_mono {B C : Finset (ZMod p × ZMod p)} (h : B ⊆ C) :
    thickenedSet p K B ⊆ thickenedSet p K C := by
  intro z hz
  simp only [thickenedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  exact h hz

/-- An arbitrarily large prime gives a common cyclic group and a nested family
with simultaneous mixed-count bounds. -/
theorem exists_mixed_flat_cyclic_family (H K N : ℕ) [NeZero K] :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      N < p ∧ ∃ C : ℕ → Finset (ZMod ((p * K) ^ 2)), Monotone C ∧
        ∃ E : ℕ → ℕ → ℝ, ∀ i, 0 < i → i ≤ H → ∀ j, 0 < j → j ≤ H →
          0 ≤ E i j ∧ (E i j) ^ 2 ≤ 16 * (i : ℝ) * j * (i + j) ∧
          ∀ z : ZMod ((p * K) ^ 2),
            |(((C i).filter (fun a ↦ z - a ∈ C j)).card : ℝ) -
              (K : ℝ) ^ 2 * (4 * i * j)| ≤
            (K : ℝ) ^ 2 * (E i j + 10 * i + 10 * j + 8) +
              2 * K * (4 * i * j + E i j + 10 * i + 10 * j + 8) := by
  obtain ⟨p, hp, hpN, hp8, B, hmono, E, hB⟩ :=
    Erdos66RectangleRepair.exists_mixed_flat_prime_family H N
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hpN, fun i ↦ thickenedSet p K (B i), ?_, fun i j ↦ (E i j : ℝ), ?_⟩
  · intro i j hij
    exact thickenedSet_mono p K (hmono hij)
  · intro i hi hiH j hj hjH
    obtain ⟨hE0, hEsq, hcounts⟩ := hB i hi hiH j hj hjH
    dsimp only
    refine ⟨by exact_mod_cast hE0, by exact_mod_cast hEsq, ?_⟩
    intro z
    have hb : ∀ t s : ZMod p,
        |((mixedFiber p (B i) (B j) t s).card : ℝ) - 4 * i * j| ≤
          (E i j : ℝ) + 10 * i + 10 * j + 8 := by
      intro t s
      have hh := hcounts (t, s)
      change |((mixedFiber p (B i) (B j) t s).card : ℤ) - 4 * i * j| ≤ _ at hh
      exact_mod_cast hh
    have hh := thickenedSet_error p K (B i) (B j) (4 * i * j)
      ((E i j : ℝ) + 10 * i + 10 * j + 8) hb z
    convert hh using 1 <;> ring

end Erdos66MixedCyclicThickening
