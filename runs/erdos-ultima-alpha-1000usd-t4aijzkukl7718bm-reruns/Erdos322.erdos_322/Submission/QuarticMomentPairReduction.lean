import Submission.Spec
import Submission.GrowthReduction
import Submission.QuarticMomentFiber

/-!
An exact reduction of polynomial-sized quartic peaks to the number of different
first/second-moment pairs attained by the representations. The reduction alone
does not bound that number of pairs.
-/

namespace Erdos322Research.QuarticMomentPairs

open Erdos322

/-- Natural-coordinate versions of all the bounded quartic representations. -/
def tuples (n : ℕ) : Finset (Fin 4 → ℕ) := by
  classical
  exact ((Finset.univ : Finset (Fin 4 → Fin (n+1))).filter
    (fun a => ∑ i, (a i : ℕ)^4 = n)).image (fun a i => (a i : ℕ))

private theorem coe_injective (n : ℕ) :
    Function.Injective (fun a : Fin 4 → Fin (n+1) => fun i => (a i : ℕ)) := by
  intro a b hab
  funext i
  exact Fin.ext (congrFun hab i)

theorem card_tuples (n : ℕ) : (tuples n).card = representationCount 4 n := by
  classical
  unfold tuples
  rw [Finset.card_image_of_injective _ (coe_injective n)]
  rfl

private theorem tuple_sum {n : ℕ} {a : Fin 4 → ℕ} (ha : a ∈ tuples n) :
    ∑ i, a i^4 = n := by
  classical
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  exact (Finset.mem_filter.mp hb).2

/-- The two auxiliary moments. -/
def moments (a : Fin 4 → ℕ) : ℕ × ℕ := (∑ i, a i, ∑ i, a i^2)

/-- The number of different pairs, without multiplicities. -/
def pairCount (n : ℕ) : ℕ := by
  classical
  exact ((tuples n).image moments).card

theorem pairCount_le_representationCount (n : ℕ) :
    pairCount n ≤ representationCount 4 n := by
  classical
  exact (Finset.card_image_le).trans_eq (card_tuples n)

/-- The full count differs from the number of moment pairs by at most a
uniform subpolynomial factor. This theorem includes all quartic tuples. -/
theorem representationCount_le_pairs (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      (representationCount 4 n : ℝ) ≤ C*(n : ℝ)^ε*pairCount n := by
  classical
  obtain ⟨C, hC, hbound⟩ := QuarticMomentFiber.fiber_subpolynomial ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  let S := tuples n
  let I := S.image moments
  have hf (p : ℕ × ℕ) :
      (((S.filter (fun a => moments a = p)).card : ℕ) : ℝ) ≤ C*(n : ℝ)^ε := by
    apply hbound _ p.1 p.2 n hn
    · intro a ha
      exact congrArg Prod.fst (Finset.mem_filter.mp ha).2
    · intro a ha
      exact congrArg Prod.snd (Finset.mem_filter.mp ha).2
    · intro a ha
      exact tuple_sum (Finset.mem_filter.mp ha).1
  calc
    (representationCount 4 n : ℝ) = (S.card : ℝ) := by rw [card_tuples]
    _ = ∑ p ∈ I, (((S.filter (fun a => moments a = p)).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image moments S
    _ ≤ ∑ _p ∈ I, C*(n : ℝ)^ε := Finset.sum_le_sum (fun p _ => hf p)
    _ = C*(n : ℝ)^ε*pairCount n := by
      simp [pairCount, I, S, mul_comm]

/-- A uniform subpolynomial bound for the full count is equivalent to such a
bound for its number of moment pairs. Neither bound is asserted here. -/
theorem uniform_bound_iff_pair_bound :
    (∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      (representationCount 4 n : ℝ) ≤ C*(n : ℝ)^ε) ↔
    (∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      (pairCount n : ℝ) ≤ C*(n : ℝ)^ε) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hb⟩ := h ε hε
    refine ⟨C, hC, fun n hn => ?_⟩
    have hp : (pairCount n : ℝ) ≤ representationCount 4 n := by
      exact_mod_cast pairCount_le_representationCount n
    exact hp.trans (hb n hn)
  · intro h ε hε
    obtain ⟨C, hC, hc⟩ := representationCount_le_pairs (ε/2) (by positivity)
    obtain ⟨D, hD, hd⟩ := h (ε/2) (by positivity)
    refine ⟨C*D, mul_pos hC hD, ?_⟩
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      (representationCount 4 n : ℝ) ≤ C*(n : ℝ)^(ε/2)*pairCount n := hc n hn
      _ ≤ C*(n : ℝ)^(ε/2)*(D*(n : ℝ)^(ε/2)) :=
        mul_le_mul_of_nonneg_left (hd n hn) (by positivity)
      _ = (C*D)*(n : ℝ)^ε := by
        rw [show C*(n : ℝ)^(ε/2)*(D*(n : ℝ)^(ε/2)) =
          (C*D)*((n : ℝ)^(ε/2)*(n : ℝ)^(ε/2)) by ring,
          ← Real.rpow_add hnpos]
        congr 2
        ring

/-- Positive-power peaks are preserved exactly by passing to moment pairs.
This identifies an outstanding arithmetic counting problem, not its solution. -/
theorem peaks_iff_pair_peaks :
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < representationCount 4 n}.Infinite) ↔
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < pairCount n}.Infinite) := by
  have h := uniform_bound_iff_pair_bound
  rw [← no_polynomial_peaks_iff_uniform_bound (representationCount 4),
    ← no_polynomial_peaks_iff_uniform_bound pairCount] at h
  exact not_iff_not.mp h

end Erdos322Research.QuarticMomentPairs
