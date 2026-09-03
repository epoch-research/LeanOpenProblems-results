import Submission.SummableDivisorCover

/-!
A cubic lower bound in two integer parameters yields reciprocal summability.
This is a familywise criterion, not a bound for all cubic collisions.
-/
namespace Erdos1206.BinaryHeightSummability
open scoped Classical

def height (p : ℤ × ℤ) : ℕ := max p.1.natAbs p.2.natAbs

private lemma abs_shift_summable :
    Summable (fun n : ℤ => (|(n:ℝ)|+1)^(-(3/2:ℝ))) := by
  have hs : Summable (fun n : ℕ => (((n+1:ℕ):ℝ))^(-(3/2:ℝ))) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  apply Summable.of_nat_of_neg
  · simpa using hs
  · simpa using hs

/-- The inverse cubic height is summable over two integer parameters. -/
theorem shifted_height_reciprocals_summable :
    Summable (fun p : ℤ × ℤ => (1:ℝ)/((height p:ℝ)+1)^3) := by
  have hs := abs_shift_summable.mul_of_nonneg abs_shift_summable
    (fun _ => by positivity) (fun _ => by positivity)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro p
  let H : ℝ := (height p:ℝ)+1
  have hH : 0 < H := by dsimp [H]; positivity
  have ha : |(p.1:ℝ)|+1 ≤ H := by
    dsimp [H,height]
    rw [← Int.cast_abs,← Nat.cast_natAbs]
    exact_mod_cast (show p.1.natAbs+1 ≤ max p.1.natAbs p.2.natAbs+1 by omega)
  have hb : |(p.2:ℝ)|+1 ≤ H := by
    dsimp [H,height]
    rw [← Int.cast_abs,← Nat.cast_natAbs]
    exact_mod_cast (show p.2.natAbs+1 ≤ max p.1.natAbs p.2.natAbs+1 by omega)
  have hab : (|(p.1:ℝ)|+1)*(|(p.2:ℝ)|+1) ≤ H^2 := by
    calc
      _ ≤ H*H := mul_le_mul ha hb (by positivity) hH.le
      _ = _ := by ring
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (|(p.1:ℝ)|+1)*(|(p.2:ℝ)|+1))
    hab (by norm_num : (0:ℝ) ≤ 3/2)
  have hHpow : (H^2)^(3/2:ℝ)=H^3 := by
    rw [← Real.rpow_natCast H 2,← Real.rpow_mul hH.le]
    norm_num
  rw [Real.mul_rpow (by positivity) (by positivity),hHpow] at hpow
  calc
    (1:ℝ)/H^3 ≤ 1/((|(p.1:ℝ)|+1)^(3/2:ℝ)*(|(p.2:ℝ)|+1)^(3/2:ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hpow
    _ = _ := by rw [Real.rpow_neg (by positivity),Real.rpow_neg (by positivity)]; ring

/-- The growth bound must hold for the normalized output, not merely for
an uncanceled numerator. -/
theorem family_reciprocals_summable {T : Set (ℤ × ℤ)} {M : T → ℕ} {C : ℝ}
    (hC : 0 < C) (hM : ∀ p : T, ((height p:ℝ)+1)^3 ≤ C*(M p:ℝ)) :
    Summable (fun p : T => (1:ℝ)/M p) := by
  have hs := (shifted_height_reciprocals_summable.subtype T).mul_left C
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro p
  have hH : 0 < ((height p:ℝ)+1)^3 := by positivity
  have hMp : 0 < (M p:ℝ) := by nlinarith [hM p]
  calc
    (1:ℝ)/M p ≤ C/((height p:ℝ)+1)^3 :=
      (div_le_div_iff₀ hMp hH).mpr (by simpa using hM p)
    _ = _ := by simp only [Function.comp_apply]; ring

/-- Repeated parameter values cause no problem: choose one preimage for
each distinct output divisor. -/
theorem range_reciprocals_summable {T : Set (ℤ × ℤ)} {M : T → ℕ} {C : ℝ}
    (hC : 0 < C) (hM : ∀ p : T, ((height p:ℝ)+1)^3 ≤ C*(M p:ℝ)) :
    Summable (fun n : ℕ => if n ∈ Set.range M then (1:ℝ)/n else 0) := by
  classical
  choose w hw using (fun n : Set.range M => n.2)
  have hi : Function.Injective w := by
    intro a b he
    apply Subtype.ext
    rw [← hw a,← hw b,he]
  have hs := (family_reciprocals_summable hC hM).comp_injective hi
  have hs' : Summable (fun n : Set.range M => (1:ℝ)/(n:ℕ)) := by
    apply hs.congr
    intro n
    simp only [Function.comp_apply,hw n]
  simpa only [Set.indicator_apply] using
    (summable_subtype_iff_indicator (f := fun n : ℕ => (1:ℝ)/n) (s := Set.range M)).mp hs'

/-- All multiples of all normalized outputs of one such family can be
excluded by a set of positive lower density. -/
theorem positive_density_avoids_family {T : Set (ℤ × ℤ)} {M : T → ℕ} {C : ℝ}
    (hC : 0 < C) (hM : ∀ p : T, ((height p:ℝ)+1)^3 ≤ C*(M p:ℝ))
    (h₁ : ∀ p, 1 < M p) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧ ∀ p t, t*M p ∉ A := by
  let A := divisorAvoider (Set.range M)
  have hnot : 1 ∉ Set.range M := by rintro ⟨p,hp⟩; have hh := h₁ p; omega
  have hd : 0 < A.lowerDensity := divisorAvoider_positive_density_of_summable hnot
    (range_reciprocals_summable hC hM)
  refine ⟨A,?_,hd,?_⟩
  · by_contra hf
    have hz : A.lowerDensity=0 := (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hf)).liminf_eq
    linarith
  · intro p t ht
    exact ht.2 (M p) (Set.mem_range_self p) (dvd_mul_left _ _)

#print axioms shifted_height_reciprocals_summable
#print axioms positive_density_avoids_family
end Erdos1206.BinaryHeightSummability
