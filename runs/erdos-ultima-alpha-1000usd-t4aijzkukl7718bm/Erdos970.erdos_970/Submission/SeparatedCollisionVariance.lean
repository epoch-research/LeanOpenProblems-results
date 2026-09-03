import Submission.ConditionalSurvivorBennett

/-! Deterministic summed conditional variances for a fixed interval population.
The product separation of the new primes limits collisions of each pair of
positions. No uniform concentration hypothesis on a sieved core is assumed. -/
namespace Erdos970.Resampling
open Finset Real Erdos970.GapAverages

lemma hit_pair_sum (p x y : ℕ) (hp : 0 < p) :
    (∑ a : Fin p, (if x % p = a.val then (1 : ℝ) else 0) *
      (if y % p = a.val then (1 : ℝ) else 0)) =
      if x % p = y % p then 1 else 0 := by
  by_cases hxy : x % p = y % p
  · rw [if_pos hxy]
    calc
      _ = ∑ a : Fin p, if x % p = a.val then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro a ha
        rw [← hxy]
        split_ifs <;> norm_num
      _ = 1 := coordinate_hit_sum p x hp
  · have hz (a : Fin p) :
        (if x % p = a.val then (1 : ℝ) else 0) *
          (if y % p = a.val then (1 : ℝ) else 0) = 0 := by
      by_cases hx : x % p = a.val
      · have hy : y % p ≠ a.val := fun hy => hxy (hx.trans hy.symm)
        simp [hx, hy]
      · simp [hx]
    simp [hz, hxy]

lemma classHits_square_sum (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    (∑ a : Fin p, classHits S p a ^ 2) =
      ∑ x ∈ S, ∑ y ∈ S, if x % p = y % p then (1 : ℝ) else 0 := by
  simp only [classHits, pow_two, sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  rw [sum_comm]
  apply sum_congr rfl
  intro y hy
  exact hit_pair_sum p x y hp

lemma classVariance_nonneg (S : Finset ℕ) (p : ℕ) : 0 ≤ classVariance S p :=
  residueMean_nonneg p (fun _ => sq_nonneg _)

lemma prime_mul_classVariance (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    (p : ℝ) * classVariance S p =
      (∑ a : Fin p, classHits S p a ^ 2) - (S.card : ℝ) ^ 2 / p := by
  have he := residueMean_centered_square p hp (classHits S p)
  rw [classHits_mean S p hp] at he
  change classVariance S p = _ at he
  rw [he, residueMean]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

/-- Concentrating the population into a single residue really gives a
quadratic-in-population variance. Thus the quadratic term in the aggregate
bound cannot simply be replaced by a uniform linear term for arbitrary S. -/
lemma classVariance_single_residue (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (b : Fin p) (hall : ∀ x ∈ S, x % p = b.val) :
    classVariance S p = (S.card : ℝ) ^ 2 / p * (1 - 1 / (p : ℝ)) := by
  have he (a : Fin p) : classHits S p a =
      if a = b then (S.card : ℝ) else 0 := by
    by_cases hab : a = b
    · subst a
      simp only [if_true, classHits]
      have hh : (∑ x ∈ S, if x % p = b.val then (1 : ℝ) else 0) = ∑ _x ∈ S, (1 : ℝ) := by
        apply sum_congr rfl
        intro x hx
        rw [if_pos (hall x hx)]
      simpa using hh
    · rw [if_neg hab]
      unfold classHits
      apply sum_eq_zero
      intro x hx
      apply if_neg
      intro hxa
      exact hab (Fin.ext (hxa.symm.trans (hall x hx)))
  have hs : (∑ a : Fin p, classHits S p a ^ 2) = (S.card : ℝ) ^ 2 := by
    simp_rw [he]
    simp
  have hh := prime_mul_classVariance S p hp
  rw [hs] at hh
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  apply (mul_left_cancel₀ hp0)
  calc
    (p : ℝ) * classVariance S p = (S.card : ℝ) ^ 2 - (S.card : ℝ) ^ 2 / p := hh
    _ = (p : ℝ) * ((S.card : ℝ) ^ 2 / p * (1 - 1 / (p : ℝ))) := by field_simp

/-- Two distinct positions have the same residue at at most one of the
separated primes. The assertion holds for every fixed population S. -/
lemma separated_equal_residues_card_le_one
    (P : Finset ℕ) (m x y : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → m ≤ p * q)
    (hx : x < m) (hy : y < m) (hxy : x ≠ y) :
    (P.filter (fun p => x % p = y % p)).card ≤ 1 := by
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpP, hxp⟩ := mem_filter.mp hp
  obtain ⟨hqP, hxq⟩ := mem_filter.mp hq
  by_contra hpq
  have hcop := (Nat.coprime_primes (hP p hpP) (hP q hqP)).mpr hpq
  have hmod := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hxp, hxq⟩
  have hb := hprod p hpP q hqP hpq
  exact hxy (hmod.eq_of_lt_of_lt (hx.trans_le hb) (hy.trans_le hb))

lemma separated_collision_sum_le
    (S P : Finset ℕ) (m : ℕ) (hSm : S ⊆ range m)
    (hP : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → m ≤ p * q) :
    (∑ p ∈ P, ∑ a : Fin p, classHits S p a ^ 2) ≤
      (S.card : ℝ) * ((P.card : ℝ) + S.card - 1) := by
  have hexp : (∑ p ∈ P, ∑ a : Fin p, classHits S p a ^ 2) =
      ∑ p ∈ P, ∑ x ∈ S, ∑ y ∈ S, if x % p = y % p then (1 : ℝ) else 0 := by
    apply sum_congr rfl
    intro p hp
    exact classHits_square_sum S p (hP p hp).pos
  rw [hexp, sum_comm]
  calc
    _ = ∑ x ∈ S, ∑ y ∈ S, ∑ p ∈ P,
        if x % p = y % p then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro x hx
      rw [sum_comm]
    _ ≤ ∑ x ∈ S, ∑ y ∈ S, if x = y then (P.card : ℝ) else 1 := by
      apply sum_le_sum
      intro x hx
      apply sum_le_sum
      intro y hy
      by_cases hxy : x = y
      · simp [hxy]
      · rw [if_neg hxy, sum_boole]
        exact_mod_cast separated_equal_residues_card_le_one P m x y hP hprod
          (mem_range.mp (hSm hx)) (mem_range.mp (hSm hy)) hxy
    _ = _ := by
      have he (x : ℕ) (hx : x ∈ S) :
          (∑ y ∈ S, if x = y then (P.card : ℝ) else 1) = P.card + (S.card : ℝ) - 1 := by
        have hi (y : ℕ) : (if x = y then (P.card : ℝ) else 1) =
            1 + (if y = x then (P.card : ℝ) - 1 else 0) := by
          by_cases h : x = y <;> simp [h, eq_comm]
        simp_rw [hi]
        simp [sum_add_distrib, hx]
        ring
      calc
        _ = ∑ _x ∈ S, ((P.card : ℝ) + S.card - 1) := sum_congr rfl he
        _ = _ := by simp; ring

/-- A deterministic aggregate bound; it is not the (false) claim that each
conditional row variance is uniformly bounded by its average over core phases. -/
theorem separated_weighted_variance_sum_le
    (S P : Finset ℕ) (m : ℕ) (hSm : S ⊆ range m)
    (hP : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → m ≤ p * q) :
    (∑ p ∈ P, (p : ℝ) * classVariance S p) ≤
      (S.card : ℝ) * ((P.card : ℝ) + S.card - 1) -
        (S.card : ℝ) ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) := by
  have he : (∑ p ∈ P, (p : ℝ) * classVariance S p) =
      (∑ p ∈ P, ∑ a : Fin p, classHits S p a ^ 2) -
        (S.card : ℝ) ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) := by
    simp_rw [mul_sum]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    simpa only [mul_one_div] using prime_mul_classVariance S p (hP p hp).pos
  rw [he]
  exact sub_le_sub_right (separated_collision_sum_le S P m hSm hP hprod) _

/-- Dividing the weighted estimate by a lower bound for all new primes. -/
theorem separated_variance_sum_le
    (S P : Finset ℕ) (m : ℕ) (hSm : S ⊆ range m)
    (hP : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → m ≤ p * q)
    (y : ℝ) (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ p) :
    (∑ p ∈ P, classVariance S p) ≤
      ((S.card : ℝ) * ((P.card : ℝ) + S.card - 1) -
        (S.card : ℝ) ^ 2 * ∑ p ∈ P, 1 / (p : ℝ)) / y := by
  apply (le_div_iff₀ hy).mpr
  calc
    _ = ∑ p ∈ P, y * classVariance S p := by rw [mul_comm, mul_sum]
    _ ≤ ∑ p ∈ P, (p : ℝ) * classVariance S p :=
      sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right (hmin p hp) (classVariance_nonneg S p))
    _ ≤ _ := separated_weighted_variance_sum_le S P m hSm hP hprod

/-- Insert the deterministic collision budget into the conditional Bennett
bound. The old population is still arbitrary inside the interval, and the
one-sided class cap B remains an explicit hypothesis. -/
theorem populationCoveredFraction_separated_bennett
    (S P : Finset ℕ) (m : ℕ) (hSm : S ⊆ range m)
    (hP : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → m ≤ p * q)
    (y : ℝ) (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ p)
    (B t : ℝ) (ht : 0 ≤ t)
    (hupper : ∀ (p : P) (a : Fin p.val), centeredHits S p.val a ≤ B) :
    populationCoveredFraction S P ≤ exp
      (-t * (S.card : ℝ) * (1 - ∑ p ∈ P, 1 / (p : ℝ)) +
        bennettFactor t B *
          (((S.card : ℝ) * ((P.card : ℝ) + S.card - 1) -
            (S.card : ℝ) ^ 2 * ∑ p ∈ P, 1 / (p : ℝ)) / y)) := by
  have hh := populationCoveredFraction_bennett S P hP t ht (fun _ => B) hupper
  rw [← mul_sum] at hh
  have hr : (∑ p : P, 1 / (p.val : ℝ)) = ∑ p ∈ P, 1 / (p : ℝ) :=
    sum_attach P (fun p : ℕ => 1 / (p : ℝ))
  have hv : (∑ p : P, classVariance S p.val) = ∑ p ∈ P, classVariance S p :=
    sum_attach P (fun p => classVariance S p)
  rw [hr, hv] at hh
  apply hh.trans
  apply exp_le_exp.mpr
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (separated_variance_sum_le S P m hSm hP hprod y hy hmin)
    (bennettFactor_nonneg t B))

/-- The resulting optimized bound uses a positive upper budget V, not an
unjustified replacement of a conditional variance by its phase average. -/
theorem populationCoveredFraction_separated_optimized
    (S P : Finset ℕ) (m : ℕ) (hSm : S ⊆ range m)
    (hP : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → m ≤ p * q)
    (y : ℝ) (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ p)
    (B : ℝ) (hB : 0 < B)
    (hupper : ∀ (p : P) (a : Fin p.val), centeredHits S p.val a ≤ B)
    (hρ : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 1)
    (V : ℝ) (hV : 0 < V)
    (hbudget : ((S.card : ℝ) * ((P.card : ℝ) + S.card - 1) -
      (S.card : ℝ) ^ 2 * ∑ p ∈ P, 1 / (p : ℝ)) / y ≤ V) :
    let u := (S.card : ℝ) * (1 - ∑ p ∈ P, 1 / (p : ℝ))
    populationCoveredFraction S P ≤ exp (-(V / B ^ 2 * bennettRate (B * u / V))) := by
  let u := (S.card : ℝ) * (1 - ∑ p ∈ P, 1 / (p : ℝ))
  have hu : 0 ≤ u := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hρ)
  let t := log (1 + B * u / V) / B
  have hx : 0 ≤ B * u / V := div_nonneg (mul_nonneg hB.le hu) hV.le
  have ht : 0 ≤ t := div_nonneg (log_nonneg (by linarith only [hx])) hB.le
  have hh := populationCoveredFraction_separated_bennett S P m hSm hP hprod
    y hy hmin B t ht hupper
  have hcap := mul_le_mul_of_nonneg_left hbudget (bennettFactor_nonneg t B)
  have hfinal : populationCoveredFraction S P ≤ exp (-t * u + bennettFactor t B * V) :=
    hh.trans (exp_le_exp.mpr (by dsimp only [u] at *; nlinarith only [hcap]))
  change populationCoveredFraction S P ≤ exp (-(V / B ^ 2 * bennettRate (B * u / V)))
  convert hfinal using 1
  congr 1
  exact (bennett_optimized_exponent B V u hB hV hu).symm

#print axioms classVariance_single_residue
#print axioms separated_collision_sum_le
#print axioms separated_weighted_variance_sum_le
#print axioms separated_variance_sum_le
#print axioms populationCoveredFraction_separated_bennett
#print axioms populationCoveredFraction_separated_optimized
end Erdos970.Resampling
