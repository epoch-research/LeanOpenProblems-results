import Submission.Work

/-!
# Dirichlet moments of inverse-totient fibers

This auxiliary file studies a second-moment route to Erdős 821. It does not
assert the missing second-moment divergence, or settle the conjecture.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

lemma summable_totient_neg_rpow (u : ℝ) (hu : 1 < u) :
    Summable (fun m : ℕ => (Nat.totient m : ℝ) ^ (-u)) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (1 / (u - 1)))
  have hk1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  have hku : 1 < (k : ℝ) * (u - 1) :=
    (div_lt_iff₀ (by linarith : 0 < u - 1)).mp ((le_max_right _ _).trans_lt hk)
  let a : ℝ := u / ((k : ℝ) + 1)
  let v : ℝ := (k : ℝ) * a
  let C : ℝ := (((2 ^ (k + 1)).factorial) ^ k : ℕ)
  have ha : 0 < a := div_pos (by linarith) (by positivity)
  have hv : 1 < v := by
    dsimp [v, a]
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
    nlinarith
  have haid : ((k : ℝ) + 1) * a = u := by
    dsimp [a]
    field_simp
  have hC : 0 < C := by dsimp [C]; positivity
  have H : Summable (fun m : ℕ => (m : ℝ) ^ (-v)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine (H.mul_left (C ^ a)).of_nonneg_of_le
    (fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_
  intro m
  by_cases hm : m = 0
  · subst m
    simp only [Nat.totient_zero, Nat.cast_zero, Real.zero_rpow (by linarith : -u ≠ 0)]
    positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hφR : (0 : ℝ) < Nat.totient m := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)
  have hp : (m : ℝ) ^ k ≤ C * (Nat.totient m : ℝ) ^ (k + 1) := by
    dsimp only [C]
    exact_mod_cast input_pow_le_totient_pow m k hk0
  have hp' := Real.rpow_le_rpow (pow_nonneg hmR.le k) hp ha.le
  rw [← Real.rpow_natCast_mul hmR.le, Real.mul_rpow hC.le (by positivity),
    ← Real.rpow_natCast_mul hφR.le] at hp'
  have hid : ((k + 1 : ℕ) : ℝ) * a = u := by simpa using haid
  rw [hid] at hp'
  change (m : ℝ) ^ v ≤ C ^ a * (Nat.totient m : ℝ) ^ u at hp'
  rw [Real.rpow_neg hφR.le, Real.rpow_neg hmR.le,
    inv_eq_one_div, inv_eq_one_div, mul_one_div]
  exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hφR u)
    (Real.rpow_pos_of_pos hmR v)).mpr (by simpa only [one_mul] using hp')

lemma totient_fiber_tsum (w : ℕ → ℝ) (n : ℕ) :
    (∑' m : {m : ℕ | Nat.totient m = n}, w (Nat.totient m.val)) =
      (g n : ℝ) * w n := by
  have heq : (fun m : {m : ℕ | Nat.totient m = n} => w (Nat.totient m.val)) =
      (fun _ : {m : ℕ | Nat.totient m = n} => w n) :=
    funext (fun m => congrArg w m.property)
  rw [heq, tsum_const, nsmul_eq_mul, Nat.card_coe_set_eq]
  rfl

lemma summable_inverse_totient_first_moment (u : ℝ) (hu : 1 < u) :
    Summable (fun n : ℕ => (g n : ℝ) * (n : ℝ) ^ (-u)) := by
  have H := (summable_partition
    (f := fun m : ℕ => (Nat.totient m : ℝ) ^ (-u))
    (s := fun n : ℕ => {m : ℕ | Nat.totient m = n})
    (fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (by intro m; exact ⟨Nat.totient m, rfl, fun n hn => hn.symm⟩)).mp
      (summable_totient_neg_rpow u hu)
  exact H.2.congr (fun n => totient_fiber_tsum (fun j => (j : ℝ) ^ (-u)) n)

lemma summable_totient_weight_iff (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    Summable (fun m : ℕ => w (Nat.totient m)) ↔
      Summable (fun n : ℕ => (g n : ℝ) * w n) := by
  have H := summable_partition
    (f := fun m : ℕ => w (Nat.totient m))
    (s := fun n : ℕ => {m : ℕ | Nat.totient m = n})
    (fun m => hw _)
    (by intro m; exact ⟨Nat.totient m, rfl, fun n hn => hn.symm⟩)
  constructor
  · intro h
    exact (H.mp h).2.congr (totient_fiber_tsum w)
  · intro h
    apply H.mpr
    refine ⟨?_, h.congr (fun n => (totient_fiber_tsum w n).symm)⟩
    intro n
    letI := (finite_totient_fiber n).fintype
    exact summable_of_finite_support (Set.toFinite _)

lemma summable_totient_neg_rpow_iff (u : ℝ) :
    Summable (fun m : ℕ => (Nat.totient m : ℝ) ^ (-u)) ↔ 1 < u := by
  refine ⟨?_, summable_totient_neg_rpow u⟩
  intro H
  by_contra hu
  have hu1 : u ≤ 1 := le_of_not_gt hu
  have hsum : Summable (fun m : ℕ => (m : ℝ) ^ (-(1 : ℝ))) := by
    apply H.of_nonneg_of_le (fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    intro m
    by_cases hm : m = 0
    · subst m
      norm_num
      positivity
    have hφ1 : (1 : ℝ) ≤ Nat.totient m := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)
    calc
      (m : ℝ) ^ (-(1 : ℝ)) ≤ (Nat.totient m : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith)
          (by exact_mod_cast Nat.totient_le m) (by norm_num)
      _ ≤ (Nat.totient m : ℝ) ^ (-u) :=
        Real.rpow_le_rpow_of_exponent_le hφ1 (by linarith)
  have := Real.summable_nat_rpow.mp hsum
  linarith

/-- The first moment has its usual abscissa one, unconditionally. -/
lemma summable_inverse_totient_first_moment_iff (u : ℝ) :
    Summable (fun n : ℕ => (g n : ℝ) * (n : ℝ) ^ (-u)) ↔ 1 < u := by
  rw [← summable_totient_weight_iff (fun n => (n : ℝ) ^ (-u))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact summable_totient_neg_rpow_iff u

/-- A pointwise power saving, together with the unconditional first moment,
places the second moment strictly to the left of exponent one. -/
lemma summable_inverse_totient_second_moment_of_power_bound (β s : ℝ)
    (h : 1 + β < 2 * s)
    (H : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ) ^ β) :
    Summable (fun n : ℕ => (g n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * s))) := by
  have Hu : 1 < 2 * s - β := by linarith
  apply (summable_inverse_totient_first_moment (2 * s - β) Hu).of_norm_bounded_eventually_nat
  filter_upwards [H, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (g n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * s)) =
        (g n : ℝ) * ((g n : ℝ) * (n : ℝ) ^ (-(2 * s))) := by ring
    _ ≤ (g n : ℝ) * ((n : ℝ) ^ β * (n : ℝ) ^ (-(2 * s))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnpos.le _))
        (Nat.cast_nonneg _)
    _ = (g n : ℝ) * (n : ℝ) ^ (-(2 * s - β)) := by
      rw [← Real.rpow_add hnpos]
      congr 2
      ring

lemma not_summable_second_moment_of_infinite_power_exceedance (s : ℝ)
    (H : {n : ℕ | (g n : ℝ) > (n : ℝ) ^ s}.Infinite) :
    ¬Summable (fun n : ℕ => (g n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * s))) := by
  intro hsum
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hsum.tendsto_atTop_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hn, hnN⟩ := H.exists_gt (max N 0)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (le_max_right N 0) hnN)
  have hnpow : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos hn0 s
  have hg : (n : ℝ) ^ s < (g n : ℝ) := hn
  have hsq : ((n : ℝ) ^ s) ^ 2 < (g n : ℝ) ^ 2 := by nlinarith
  have hbase : ((n : ℝ) ^ s) ^ 2 * (n : ℝ) ^ (-(2 * s)) = 1 := by
    rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0]
    push_cast
    rw [show s * 2 + -(2 * s) = (0 : ℝ) by ring, Real.rpow_zero]
  have hlo : 1 < (g n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * s)) := by
    rw [← hbase]
    exact mul_lt_mul_of_pos_right hsq (Real.rpow_pos_of_pos hn0 _)
  exact (not_lt_of_ge hlo.le) (hN n ((le_max_left N 0).trans hnN.le))

/-- Exact second-moment reformulation. The nonsummability on the right is
not asserted unconditionally. -/
theorem erdos_821_iff_second_moment_divergence :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔
      ∀ s : ℝ, s < 1 →
        ¬Summable (fun n : ℕ => (g n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * s))) := by
  constructor
  · intro H s hs
    apply not_summable_second_moment_of_infinite_power_exceedance s
    simpa only [sub_sub_cancel] using H (1 - s) (by linarith)
  · intro H
    by_contra Hneg
    obtain ⟨ε, h⟩ := not_forall.mp Hneg
    obtain ⟨hε, hfin⟩ := _root_.not_imp.mp h
    obtain ⟨B, hB⟩ := (Set.not_infinite.mp hfin).bddAbove
    have hbound : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ) ^ (1 - ε) := by
      filter_upwards [eventually_gt_atTop B] with n hn
      exact le_of_not_gt (fun hg => (not_le_of_gt hn) (hB hg))
    apply H (1 - ε / 4) (by linarith)
    exact summable_inverse_totient_second_moment_of_power_bound
      (1 - ε) (1 - ε / 4) (by linarith) hbound

/-- The natural second moment counts ordered pairs in a full totient fiber. -/
lemma totient_collision_card (n : ℕ) :
    (((finite_totient_fiber n).toFinset ×ˢ
      (finite_totient_fiber n).toFinset).card : ℝ) = (g n : ℝ) ^ 2 := by
  have hcard : (finite_totient_fiber n).toFinset.card = g n :=
    (Set.ncard_eq_toFinset_card _ (finite_totient_fiber n)).symm
  rw [Finset.card_product, hcard, Nat.cast_mul]
  ring

/-- The off-diagonal factor is exactly the number of ordered distinct pairs,
not a signed auxiliary weight. -/
lemma totient_distinct_collision_card (n : ℕ) :
    (((finite_totient_fiber n).toFinset.offDiag).card : ℝ) =
      (g n : ℝ) * ((g n : ℝ) - 1) := by
  have hcard : (finite_totient_fiber n).toFinset.card = g n :=
    (Set.ncard_eq_toFinset_card _ (finite_totient_fiber n)).symm
  rw [Finset.offDiag_card, hcard]
  have hle : g n ≤ g n * g n := by
    simpa only [pow_two] using Nat.le_self_pow (by decide : 2 ≠ 0) (g n)
  rw [Nat.cast_sub hle, Nat.cast_mul]
  ring

/-- Diagonal pairs alone obstruct convergence only up to the half line. -/
lemma half_lt_of_summable_inverse_totient_second_moment (s : ℝ)
    (H : Summable (fun n : ℕ => (g n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * s)))) :
    1 / 2 < s := by
  have Hfirst : Summable (fun n : ℕ => (g n : ℝ) * (n : ℝ) ^ (-(2 * s))) := by
    apply H.of_nonneg_of_le (fun n => by positivity)
    intro n
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) (g n)
  have h := (summable_inverse_totient_first_moment_iff (2 * s)).mp Hfirst
  linarith

/-- Above the half line, all additional divergence must come from pairs of
distinct inputs with equal totient. -/
lemma summable_second_moment_iff_off_diagonal (s : ℝ) (hs : 1 / 2 < s) :
    Summable (fun n : ℕ => (g n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * s))) ↔
      Summable (fun n : ℕ =>
        (g n : ℝ) * ((g n : ℝ) - 1) * (n : ℝ) ^ (-(2 * s))) := by
  have Hfirst := summable_inverse_totient_first_moment (2 * s) (by linarith)
  constructor
  · intro H
    exact (H.sub Hfirst).congr (fun n => by ring)
  · intro H
    exact (H.add Hfirst).congr (fun n => by ring)

/-- An exact collision-only criterion for the original conjecture. No
unconditional off-diagonal divergence is claimed here. -/
theorem erdos_821_iff_off_diagonal_divergence :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔
      ∀ s : ℝ, 1 / 2 < s → s < 1 →
        ¬Summable (fun n : ℕ =>
          (g n : ℝ) * ((g n : ℝ) - 1) * (n : ℝ) ^ (-(2 * s))) := by
  rw [erdos_821_iff_second_moment_divergence]
  constructor
  · intro H s hs hs1 hsum
    exact H s hs1 ((summable_second_moment_iff_off_diagonal s hs).mpr hsum)
  · intro H s hs hsum
    have hh := half_lt_of_summable_inverse_totient_second_moment s hsum
    exact H s hh hs ((summable_second_moment_iff_off_diagonal s hh).mp hsum)

end Erdos821
