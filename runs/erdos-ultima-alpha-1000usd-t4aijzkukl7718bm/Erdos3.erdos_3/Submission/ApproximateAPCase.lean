import Submission.FiniteKernelCase

/-! Reciprocal divergence forces approximate arithmetic progressions via interval branching.
No conclusion about exact progressions is assumed or asserted here. -/

namespace Erdos3ApproximateAPCase

open Erdos3FiniteKernelCase

set_option maxHeartbeats 1000000

def translated (A : Set ℕ) (a : ℕ) : Set ℕ := {n | a + n ∈ A}

lemma count_blocks (A : Set ℕ) (a Q N : ℕ) :
    count (translated A a) (Q * N) =
      ∑ i : Fin Q, count (translated A (a + i.val * N)) N := by
  classical
  unfold count
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp [finProdFinEquiv, translated, Nat.add_comm, Nat.add_left_comm,
    Nat.mul_comm]

def FullGrid (A : Set ℕ) (Q : ℕ) : Prop :=
  ∃ a j : ℕ, ∀ i : Fin Q,
    0 < count (translated A (a + i.val * Q ^ j)) (Q ^ j)

lemma no_grid_count_bound {A : Set ℕ} {Q : ℕ} (h : ¬ FullGrid A Q) :
    ∀ j a : ℕ, count (translated A a) (Q ^ j) ≤ (Q - 1) ^ j := by
  classical
  intro j
  induction j with
  | zero => intro a; simpa using count_le (translated A a) 1
  | succ j ih =>
    intro a
    have hno : ¬ ∀ i : Fin Q,
        0 < count (translated A (a + i.val * Q ^ j)) (Q ^ j) := by
      intro hall
      exact h ⟨a, j, hall⟩
    obtain ⟨r, hr⟩ := not_forall.mp hno
    have hzero : count (translated A (a + r.val * Q ^ j)) (Q ^ j) = 0 := by omega
    rw [pow_succ', count_blocks]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r), hzero, add_zero]
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin Q)).erase r, (Q - 1) ^ j := by
        exact Finset.sum_le_sum (fun i _ ↦ ih _)
      _ = (Q - 1) ^ (j + 1) := by simp [pow_succ, mul_comm]

lemma summable_of_no_grid {A : Set ℕ} {Q : ℕ} (hQ : 1 < Q)
    (h : ¬ FullGrid A Q) : Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  apply summable_of_count_pow_bound hQ
  intro j
  simpa only [translated, zero_add, Set.setOf_mem_eq] using no_grid_count_bound h j 0

/-- At some scale, every one of Q consecutive, equally sized cells is occupied. -/
theorem divergence_full_grid {A : Set ℕ}
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) {Q : ℕ} (hQ : 1 < Q) :
    FullGrid A Q := by
  by_contra h
  exact hs (summable_of_no_grid hQ h)

lemma occupied_iff (A : Set ℕ) (a N : ℕ) :
    0 < count (translated A a) N ↔ ∃ x ∈ A, a ≤ x ∧ x < a + N := by
  classical
  rw [count_eq_card, Finset.card_pos]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨hnN, hnA⟩ := Finset.mem_filter.mp hn
    exact ⟨a + n, hnA, by omega, by have := Finset.mem_range.mp hnN; omega⟩
  · rintro ⟨x, hxA, hax, hxN⟩
    refine ⟨x - a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    change a + (x - a) ∈ A
    simpa only [Nat.add_sub_of_le hax] using hxA

/-- Arbitrarily accurate one-sided approximate progressions. The width L may grow
with the requested accuracy; this does not assert an exact progression. -/
theorem divergence_approximate_progressions {A : Set ℕ}
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (k M : ℕ) :
    ∃ a d L : ℕ, 0 < L ∧ d = (M + 2) * L ∧
      ∃ f : Fin k → ℕ, StrictMono f ∧
        ∀ i : Fin k, f i ∈ A ∧
          a + i.val * d ≤ f i ∧ f i < a + i.val * d + L := by
  classical
  let Q := (k + 1) * (M + 2)
  have hQ : 1 < Q := by dsimp [Q]; nlinarith
  obtain ⟨a, j, hgrid⟩ := divergence_full_grid hs hQ
  let L := Q ^ j
  let d := (M + 2) * L
  have hL : 0 < L := by dsimp [L]; positivity
  have hmem : ∀ i : Fin k, ∃ x ∈ A,
      a + i.val * d ≤ x ∧ x < a + i.val * d + L := by
    intro i
    have hi : i.val * (M + 2) < Q := by
      dsimp [Q]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    obtain ⟨x, hxA, hxlo, hxhi⟩ :=
      (occupied_iff A _ L).mp (hgrid ⟨i.val * (M + 2), hi⟩)
    refine ⟨x, hxA, ?_, ?_⟩
    · simpa only [d, Nat.mul_assoc] using hxlo
    · simpa only [d, Nat.mul_assoc] using hxhi
  choose f hfA hflo hfhi using hmem
  refine ⟨a, d, L, hL, rfl, f, ?_, fun i ↦ ⟨hfA i, hflo i, hfhi i⟩⟩
  intro i t hit
  have hival : i.val + 1 ≤ t.val := hit
  have hstep : i.val * d + L ≤ t.val * d := by
    have hmul := Nat.mul_le_mul_right d hival
    have hdL : L ≤ d := by dsimp [d]; nlinarith
    nlinarith
  have := hfhi i
  have := hflo t
  omega

/-- The same unconditional conclusion expressed using real relative error. -/
theorem divergence_real_approximate_progressions {A : Set ℕ}
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a d : ℕ, 0 < d ∧ ∃ f : Fin k → ℕ, StrictMono f ∧
      ∀ i : Fin k, f i ∈ A ∧
        |(f i : ℝ) - ((a : ℝ) + i.val * (d : ℝ))| < ε * d := by
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  obtain ⟨a, d, L, hL, hd, f, hmono, hf⟩ := divergence_approximate_progressions hs k M
  refine ⟨a, d, by rw [hd]; positivity, f, hmono, ?_⟩
  intro i
  obtain ⟨hiA, hilo, hihi⟩ := hf i
  refine ⟨hiA, ?_⟩
  have hilo' : (a : ℝ) + i.val * (d : ℝ) ≤ f i := by exact_mod_cast hilo
  have hihi' : (f i : ℝ) < (a : ℝ) + i.val * (d : ℝ) + L := by
    exact_mod_cast hihi
  rw [abs_of_nonneg (sub_nonneg.mpr hilo')]
  have hεM : 1 < ε * (M : ℝ) := by
    have := (div_lt_iff₀ hε).mp hM
    nlinarith
  have hd' : (d : ℝ) = ((M : ℝ) + 2) * L := by exact_mod_cast hd
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hscale : (L : ℝ) < ε * d := by
    rw [hd']
    nlinarith [mul_pos hε hL', mul_lt_mul_of_pos_right hεM hL']
  linarith

/-- A quadratic perturbation with a sufficiently large linear term is 3-AP-free. -/
lemma quadratic_perturbation_free (k D : ℕ) (hD : 2 * k ^ 2 < D) :
    ThreeAPFree (Set.range (fun i : Fin k ↦ D * i.val + i.val ^ 2)) := by
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ z ⟨t, rfl⟩ heq
  have hsq (i : Fin k) : i.val ^ 2 ≤ k ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_of_lt i.isLt) 2
  have hit : i.val ^ 2 + t.val ^ 2 < D := by nlinarith [hsq i, hsq t]
  have hjj : j.val ^ 2 + j.val ^ 2 < D := by nlinarith [hsq j]
  have heq' : D * (i.val + t.val) + (i.val ^ 2 + t.val ^ 2) =
      D * (j.val + j.val) + (j.val ^ 2 + j.val ^ 2) := by nlinarith
  have hmod := congrArg (fun n : ℕ ↦ n % D) heq'
  have hsquares : i.val ^ 2 + t.val ^ 2 = j.val ^ 2 + j.val ^ 2 := by
    simpa only [Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt hit, Nat.mod_eq_of_lt hjj] using hmod
  have hlinear : i.val + t.val = j.val + j.val := by
    have hmul : D * (i.val + t.val) = D * (j.val + j.val) := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < D) hmul
  have hlinear' : (i.val : ℝ) + t.val = j.val + j.val := by exact_mod_cast hlinear
  have hsquares' : (i.val : ℝ) ^ 2 + (t.val : ℝ) ^ 2 = (j.val : ℝ) ^ 2 + (j.val : ℝ) ^ 2 := by
    exact_mod_cast hsquares
  have ht : (t.val : ℝ) = 2 * (j.val : ℝ) - i.val := by linarith
  rw [ht] at hsquares'
  have hs : ((i.val : ℝ) - (j.val : ℝ)) ^ 2 = 0 := by nlinarith
  have hij : i.val = j.val := by
    exact_mod_cast sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  simp only [hij]

/-- No fixed relative accuracy, however small, forces an exact three-term AP:
there are 3-AP-free examples of arbitrarily long approximate progressions. -/
theorem threeAPFree_arbitrarily_accurate_finite_progressions (k M : ℕ) :
    ∃ D L : ℕ, 0 < L ∧ D = (M + 2) * L ∧
      ∃ f : Fin k → ℕ, StrictMono f ∧ ThreeAPFree (Set.range f) ∧
        ∀ i : Fin k, i.val * D ≤ f i ∧ f i < i.val * D + L := by
  let L := (k + 1) ^ 2
  let D := (M + 2) * L
  let f : Fin k → ℕ := fun i ↦ D * i.val + i.val ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hD : 2 * k ^ 2 < D := by
    calc
      2 * k ^ 2 < 2 * L := Nat.mul_lt_mul_of_pos_left
        (Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by decide : 2 ≠ 0)) (by decide)
      _ ≤ D := Nat.mul_le_mul_right L (by omega : 2 ≤ M + 2)
  refine ⟨D, L, hL, rfl, f, ?_, quadratic_perturbation_free k D hD, ?_⟩
  · intro i j hij
    have hsq := Nat.pow_le_pow_left (Nat.le_of_lt hij) 2
    have hmul := Nat.mul_lt_mul_of_pos_left hij (by omega : 0 < D)
    dsimp [f]
    omega
  · intro i
    have hi : i.val ^ 2 < L := by
      exact Nat.pow_lt_pow_left (by omega : i.val < k + 1) (by norm_num : 2 ≠ 0)
    dsimp [f]
    constructor <;> nlinarith


#print axioms divergence_full_grid
#print axioms divergence_approximate_progressions
#print axioms divergence_real_approximate_progressions
#print axioms threeAPFree_arbitrarily_accurate_finite_progressions

end Erdos3ApproximateAPCase
