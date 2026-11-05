import Submission.EfficientCover.FiniteCover
import Submission.EfficientCover.Density
import Submission.EfficientCover.Survivors

/-! The complete efficient residue cover of every fixed multiple of the prime cutoff. -/

open Filter
open scoped BigOperators Topology

namespace Erdos5EfficientCover

/-- Assemble the medium zero classes, greedy small-prime classes, and reserve classes.
The assumptions here are finite cardinality facts, proved unconditionally below. -/
theorem cover_of_residual_bound (c y P T : ℕ) (hPd : P ≤ y / T)
    (aSmall : ℕ → ℕ) (hSmall : ∀ p ∈ primesUpTo P, aSmall p < p)
    (hcard : (uncovered (mediumSurvivors c y P T) (primesUpTo P) aSmall).card ≤
      (reservePrimes y T).card) :
    ∃ a : ℕ → ℕ, (∀ p, p.Prime → p ≤ y → a p < p) ∧
      ∀ s : ℕ, 0 < s → s ≤ c * y → ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ s % p = a p := by
  classical
  let R := uncovered (mediumSurvivors c y P T) (primesUpTo P) aSmall
  obtain ⟨aReserve, hReserve, hRCover⟩ := allocate_reserve R (reservePrimes y T)
    (fun p hp => (mem_reservePrimes.mp hp).1.pos) hcard
  let a : ℕ → ℕ := fun p => if p ≤ P then aSmall p else if p ≤ y / T then 0 else aReserve p
  refine ⟨a, ?_, ?_⟩
  · intro p hp hpy
    by_cases hpP : p ≤ P
    · simpa [a, hpP] using hSmall p (mem_primesUpTo.mpr ⟨hp, hpP⟩)
    · by_cases hpd : p ≤ y / T
      · simpa [a, hpP, hpd] using hp.pos
      · simpa [a, hpP, hpd] using hReserve p (mem_reservePrimes.mpr ⟨hp, hpy, lt_of_not_ge hpd⟩)
  · intro s hs hsbound
    by_cases hsM : s ∈ mediumSurvivors c y P T
    · by_cases hsR : s ∈ R
      · obtain ⟨p, hp, hpeq⟩ := hRCover s hsR
        have hp' := mem_reservePrimes.mp hp
        have hpP : ¬ p ≤ P := by omega
        have hpd : ¬ p ≤ y / T := not_le_of_gt hp'.2.2
        exact ⟨p, hp'.1, hp'.2.1, by simpa [a, hpP, hpd] using hpeq⟩
      · have hex : ∃ p ∈ primesUpTo P, s % p = aSmall p := by
          by_contra h
          push_neg at h
          exact hsR (mem_uncovered.mpr ⟨hsM, h⟩)
        obtain ⟨p, hp, hpeq⟩ := hex
        have hp' := mem_primesUpTo.mp hp
        exact ⟨p, hp'.1, hp'.2.trans (hPd.trans (Nat.div_le_self y T)),
          by simpa [a, hp'.2] using hpeq⟩
    · have hex : ∃ p ∈ mediumPrimes P y T, p ∣ s := by
        by_contra h
        push_neg at h
        exact hsM (mem_mediumSurvivors.mpr ⟨⟨hs, hsbound⟩, h⟩)
      obtain ⟨p, hp, hpdvd⟩ := hex
      have hp' := mem_mediumPrimes.mp hp
      have hpP : ¬ p ≤ P := not_le_of_gt hp'.2.1
      exact ⟨p, hp'.1, hp'.2.2.trans (Nat.div_le_self y T),
        by simp [a, hpP, hp'.2.2, Nat.mod_eq_zero_of_dvd hpdvd]⟩

/-- The complete elementary efficient cover: for each fixed positive `c`, all sufficiently
large `y` admit one class at each prime at most `y` covering every integer `1..c*y`. -/
theorem efficient_cover (c : ℕ) (hc : 1 ≤ c) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
      ∃ a : ℕ → ℕ, (∀ p : ℕ, p.Prime → p ≤ y → a p < p) ∧
        ∀ s : ℕ, 0 < s → s ≤ c * y →
          ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ s % p = a p := by
  classical
  obtain ⟨T, hT, hscale⟩ := exists_reserve_scale
  have hC := survivorConst_pos c T
  have hα : 0 < lowerConst / 2 := div_pos lowerConst_pos (by norm_num)
  obtain ⟨P, hP⟩ := exists_primeDensity_lt ((lowerConst / 2) / survivorConst c T) (div_pos hα hC)
  have hρC : primeDensity P * survivorConst c T ≤ lowerConst / 2 :=
    ((lt_div_iff₀ hC).mp hP).le
  have hevent : ∀ᶠ y : ℕ in atTop,
      ∃ a : ℕ → ℕ, (∀ p : ℕ, p.Prime → p ≤ y → a p < p) ∧
        ∀ s : ℕ, 0 < s → s ≤ c * y →
          ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ s % p = a p := by
    filter_upwards [eventually_mediumSurvivors_le c T P hc hT,
      eventually_reserve_lower T hT hscale, eventually_ge_atTop (P * T),
      eventually_ge_atTop (2 : ℕ)] with y hsurvivors hreserve hyP hy2
    have hPd : P ≤ y / T := (Nat.le_div_iff_mul_le hT).mpr hyP
    obtain ⟨aSmall, hSmall, hgreedy⟩ := greedy_residue_cover
      (mediumSurvivors c y P T) (primesUpTo P)
      (fun p hp => (mem_primesUpTo.mp hp).1.pos)
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hleft : ((uncovered (mediumSurvivors c y P T) (primesUpTo P) aSmall).card : ℝ) ≤
        ((reservePrimes y T).card : ℝ) := by
      change ((uncovered (mediumSurvivors c y P T) (primesUpTo P) aSmall).card : ℝ) ≤
        primeDensity P * (mediumSurvivors c y P T).card at hgreedy
      calc
        ((uncovered (mediumSurvivors c y P T) (primesUpTo P) aSmall).card : ℝ) ≤
            primeDensity P * (mediumSurvivors c y P T).card := hgreedy
        _ ≤ primeDensity P * (survivorConst c T * y / Real.log (y : ℝ)) :=
          mul_le_mul_of_nonneg_left hsurvivors (primeDensity_nonneg P)
        _ = (primeDensity P * survivorConst c T) * ((y : ℝ) / Real.log (y : ℝ)) := by ring
        _ ≤ (lowerConst / 2) * ((y : ℝ) / Real.log (y : ℝ)) :=
          mul_le_mul_of_nonneg_right hρC (div_nonneg (Nat.cast_nonneg y) hlogy.le)
        _ = (lowerConst / 2) * y / Real.log (y : ℝ) := by ring
        _ ≤ ((reservePrimes y T).card : ℝ) := hreserve
    exact cover_of_residual_bound c y P T hPd aSmall hSmall (by exact_mod_cast hleft)
  exact eventually_atTop.mp hevent

end Erdos5EfficientCover

#print axioms Erdos5EfficientCover.cover_of_residual_bound
#print axioms Erdos5EfficientCover.efficient_cover
