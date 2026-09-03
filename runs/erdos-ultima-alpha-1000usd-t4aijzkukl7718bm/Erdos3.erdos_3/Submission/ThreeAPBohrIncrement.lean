import Submission.CorrelationIncrement
import Submission.ThreeAPSifting

/-! A global Bohr-set density increment for finite three-term-progression-free sets.
This does not include the localized iteration, integer summability, or longer progressions. -/
namespace Erdos3ThreeAPBohrIncrement
open Finset Erdos3CorrelationSifting Erdos3PopularAlmostPeriods Erdos3PopularBohr
  Erdos3CorrelationIncrement Erdos3ThreeAPSifting Erdos3CorrelationMoments
  Erdos3CrootSisaskL2 Erdos3FiniteBohr
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 3000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma half_pow_le_density_iff (B : Finset G) (m : ℕ) :
    (1/2 : ℝ)^(2*m) ≤ density B ↔ Fintype.card G ≤ 2^(2*m)*B.card := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [density, div_pow, one_pow, div_le_div_iff₀ (by positivity) hN]
  norm_num only [one_mul]
  norm_cast
  simp only [mul_comm]

lemma smoothing_error_le (B : Finset G) (hB : B.Nonempty) (m : ℕ)
    (hBd : Fintype.card G ≤ 2^(2*m)*B.card) :
    4*((m+4 : ℕ) : ℝ)/((512*(m+4) : ℕ) : ℝ) +
      (1/density B)*(density B/128+2*(1/2 : ℝ)^(2*(m+4))) ≤ 3/128 := by
  have hβ := density_pos B hB
  have hh := (half_pow_le_density_iff B m).mpr hBd
  have ht : (1/2 : ℝ)^(2*(m+4)) ≤ density B/256 := by
    calc
      _ = (1/2 : ℝ)^(2*m)/256 := by
        rw [show 2*(m+4) = 2*m+8 by omega, pow_add]
        norm_num
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hh (by norm_num)
  have hn : (m : ℝ)+4 ≠ 0 := by positivity
  have hfirst : 4*((m+4 : ℕ) : ℝ)/((512*(m+4) : ℕ) : ℝ) = 1/128 := by
    push_cast
    field_simp
    ring
  rw [hfirst]
  have hterm : (1/density B)*(density B/128+2*(1/2 : ℝ)^(2*(m+4))) ≤ 1/64 := by
    calc
      _ ≤ (1/density B)*(density B/128+2*(density B/256)) := by gcongr
      _ = _ := by field_simp; norm_num
  linarith

lemma bad_fraction_le {p : ℕ} (hp : 16 ≤ p) :
    2*(17/18 : ℝ)^(8*p) ≤ 1/256 := by
  have hpow : (17/18 : ℝ)^(8*p) ≤ (17/18 : ℝ)^128 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc
    _ ≤ 2*(17/18 : ℝ)^128 := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ _ := by norm_num

def sampleMoment (p : ℕ) : ℕ := 8*p^2+1
def sampleLength (p : ℕ) : ℕ := 256*(sampleMoment p)^4*(512*(sampleMoment p+4))^2

lemma sifted_density_large_enough (A B : Finset G) {p : ℕ}
    (hα : (2/3 : ℝ)^p ≤ density A) (hB : (density A)^(8*p) ≤ 2*density B) :
    Fintype.card G ≤ 2^(2*sampleMoment p)*B.card := by
  have hhalf : (1/2 : ℝ)^p ≤ density A :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num : (1/2 : ℝ) ≤ 2/3) p).trans hα
  have hh : (1/2 : ℝ)^(sampleMoment p) ≤ density B := by
    calc
      _ = ((1/2 : ℝ)^p)^(8*p)/2 := by
        rw [sampleMoment, show 8*p^2+1 = p*(8*p)+1 by ring, pow_succ, pow_mul]
        ring
      _ ≤ (density A)^(8*p)/2 := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hhalf _) (by norm_num)
      _ ≤ _ := by linarith
  apply (half_pow_le_density_iff B (sampleMoment p)).mp
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))).trans hh

lemma smooth_normalized (A V : Finset G) (x : G) :
    smooth V (normalized A) x = smooth V (indicator A) x / density A := by
  unfold smooth normalized
  exact (expect_div _ _ _).symm

/-- A global density increment of factor 33/32 on a Bohr set, with a polynomial
sampling cost in p. This is not yet a localized density-increment theorem. -/
theorem exists_threeAPFree_bohr_increment (A : Finset G) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set G))
    (hsize : 4 ≤ (Fintype.card G : ℝ)*(density A)^2)
    {p : ℕ} (hpeven : Even p) (hp : 16 ≤ p) (hα : (2/3 : ℝ)^p ≤ density A) :
    ∃ B T : Finset G, B.Nonempty ∧ T.Nonempty ∧
      (density A)^(8*p) ≤ 2*density B ∧
      B.card^(sampleLength p)*Fintype.card G ≤
        2*(Fintype.card G)^(sampleLength p)*T.card ∧
      ∃ D : Finset (AddChar G ℂ), D.card ≤ ⌊16*Real.log (1/density T)⌋₊ ∧
        ∃ x : G, (33/32 : ℝ)*density A ≤
          smooth (bohr D (density B/(256*(D.card+1)))) (indicator A) x := by
  obtain ⟨v,hB,hBsize,hBbad⟩ := sift_threeAPFree A hA hfree hsize hpeven hα
  let B := common A v
  let f : G → ℝ := fun x ↦ if (17/16 : ℝ) < corr (normalized A) x then 1 else 0
  have hf (x : G) : 0 ≤ f x ∧ f x ≤ 1 := by dsimp [f]; split_ifs <;> norm_num
  have hbad : pairDensity B (fun x ↦ 1-f x) ≤
      (2*(17/18 : ℝ)^(8*p))*(density B)^2 := by
    have he : (fun x ↦ 1-f x) =
        (fun x ↦ if corr (normalized A) x ≤ 17/16 then (1 : ℝ) else 0) := by
      funext x
      dsimp [f]
      by_cases hx : (17/16 : ℝ) < corr (normalized A) x
      · simp [hx, not_le.mpr hx]
      · simp [hx, le_of_not_gt hx]
    rw [he]
    exact hBbad
  have hm : 0 < sampleMoment p := by simp [sampleMoment]
  have hr : 0 < 512*(sampleMoment p+4) := by positivity
  have hBd := sifted_density_large_enough A B hα hBsize
  obtain ⟨T,hT,_,hTcard,D,hD,_,hpop⟩ := exists_popular_bohr B univ hB univ_nonempty
    f hf (η := density B/128) (by positivity [density_nonneg B]) hbad hm hr
    (sampleMoment p+4) hBd
  have hcard : B.card^(sampleLength p)*Fintype.card G ≤
      2*(Fintype.card G)^(sampleLength p)*T.card := by
    simp only [card_univ] at hTcard
    apply hTcard.trans
    apply Nat.mul_le_mul_right T.card
    apply Nat.mul_le_mul_left 2
    exact Nat.pow_le_pow_left (card_le_univ (B+(univ : Finset G))) _
  have hg (x : G) : 0 ≤ normalized A x :=
    div_nonneg (indicator_nonneg A x) (density_nonneg A)
  obtain ⟨x,hx⟩ := bohr_translate_increment B hB D (by positivity [density_nonneg B])
    (normalized A) f hg (expect_normalized A hA) (by norm_num : (0 : ℝ) ≤ 17/16)
    (popular_indicator_bound (normalized A) hg (17/16)) hpop
  have he := smoothing_error_le B hB (sampleMoment p) hBd
  have hδ := bad_fraction_le hp
  have hinc : (33/32 : ℝ) ≤ smooth (bohr D ((density B/128/(D.card+1))/2)) (normalized A) x := by
    nlinarith
  have hrad : (density B/128/((D.card : ℝ)+1))/2 = density B/(256*((D.card : ℝ)+1)) := by
    rw [div_div, div_div]
    congr 1
    ring
  rw [hrad, smooth_normalized] at hinc
  have hx' := (le_div_iff₀ (density_pos A hA)).mp hinc
  exact ⟨B,T,hB,hT,hBsize,hcard,D,hD,x,hx'⟩

#print axioms exists_threeAPFree_bohr_increment
end Erdos3ThreeAPBohrIncrement
