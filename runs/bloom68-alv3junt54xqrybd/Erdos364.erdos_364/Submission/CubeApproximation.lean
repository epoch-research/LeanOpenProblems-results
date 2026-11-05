import Submission.QuarticObstruction

/-!
Exact auxiliary results for the centered cubic equation, without changing
`Submission` and without importing `Submission.Spec`.

These do not prove Erdős 364. They exclude all prime-power square factors S,
exclude every cubic S, and certify a counterexample to a weaker integral-point
height assertion that assumes D^2 | y rather than the essential D^3 | y.
-/

namespace Erdos364.AuxiliaryCubeApproximation

open Erdos364.PowerfulStructure Erdos364.QuarticObstruction

/-- A factor coprime to both its complement and S is a cube. -/
theorem cube_factor_of_cubic_product {a b D S : ℕ} (hab : Nat.Coprime a b)
    (haS : Nat.Coprime a S) (heq : a * b = D ^ 3 * S ^ 2) :
    ∃ u : ℕ, a = u ^ 3 := by
  refine exists_eq_pow_of_mul_eq_pow (a := a) (b := b * S) (c := D * S) (k := 3) ?_ ?_
  · change IsUnit (Nat.gcd a (b * S))
    rw [hab.mul_right haS]
    exact isUnit_one
  · calc
      a * (b * S) = (a * b) * S := by ring
      _ = (D ^ 3 * S ^ 2) * S := by rw [heq]
      _ = (D * S) ^ 3 := by ring

/-- Coprimality with S, not with D, gives a pure cube entry. -/
theorem centered_cubic_cube_factors {t D S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) :
    (Nat.Coprime (t - 1) S → ∃ u : ℕ, t - 1 = u ^ 3) ∧
      (Nat.Coprime t S → ∃ u : ℕ, t = u ^ 3) ∧
      (Nat.Coprime (t + 1) S → ∃ u : ℕ, t + 1 = u ^ 3) := by
  have hc := centered_pairwise_coprime ht he
  have hp := heq
  rw [cube_sub_self_eq_centered_product] at hp
  refine ⟨?_, ?_, ?_⟩
  · intro hS
    apply cube_factor_of_cubic_product (hc.1.mul_right hc.2.1) hS
    simpa only [mul_assoc] using hp
  · intro hS
    apply cube_factor_of_cubic_product (hc.1.symm.mul_right hc.2.2) hS
    calc
      t * ((t - 1) * (t + 1)) = (t - 1) * t * (t + 1) := by ring
      _ = D ^ 3 * S ^ 2 := hp
  · intro hS
    apply cube_factor_of_cubic_product (hc.2.1.symm.mul_right hc.2.2.symm) hS
    calc
      (t + 1) * ((t - 1) * t) = (t - 1) * t * (t + 1) := by ring
      _ = D ^ 3 * S ^ 2 := hp

/-- Two positive cubes cannot be one or two apart. -/
theorem cube_add_small_ne_cube {a b e : ℕ} (ha : 0 < a) (he : 0 < e)
    (he' : e ≤ 2) : a ^ 3 + e ≠ b ^ 3 := by
  intro h
  have hab : a < b := (Nat.pow_lt_pow_iff_left (by decide : 3 ≠ 0)).mp (by omega)
  have hb : (a + 1) ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left (by omega : a + 1 ≤ b) 3
  nlinarith [Nat.zero_le (a ^ 2)]

private theorem prime_not_dvd_other {p a b : ℕ} (hp : Nat.Prime p)
    (hab : Nat.Coprime a b) (hpa : p ∣ a) : ¬p ∣ b := by
  intro hpb
  apply hp.not_dvd_one
  have hh := Nat.dvd_gcd hpa hpb
  rwa [hab] at hh

/-- Uniform exclusion of every prime-power S, for all D and all exponents.
No squarefreeness assumption on D is needed. -/
theorem even_cube_sub_self_ne_prime_power_square_mul_cube {t D p k : ℕ}
    (ht : 2 ≤ t) (he : Even t) (hp : Nat.Prime p) :
    t ^ 3 - t ≠ D ^ 3 * (p ^ k) ^ 2 := by
  intro heq
  have hs := centered_cubic_cube_factors ht he heq
  have hc := centered_pairwise_coprime ht he
  have hprev : t - 1 + 1 = t := by omega
  have hnext : t - 1 + 2 = t + 1 := by omega
  by_cases hpleft : p ∣ t - 1
  · have hnmid := prime_not_dvd_other hp hc.1 hpleft
    have hnright := prime_not_dvd_other hp hc.2.1 hpleft
    obtain ⟨a, ha⟩ := hs.2.1 ((hp.coprime_iff_not_dvd.mpr hnmid).symm.pow_right k)
    obtain ⟨b, hb⟩ := hs.2.2 ((hp.coprime_iff_not_dvd.mpr hnright).symm.pow_right k)
    have hapos : 0 < a := by
      apply Nat.pos_of_ne_zero
      intro hz
      simp only [hz, zero_pow (by decide : 3 ≠ 0)] at ha
      omega
    apply cube_add_small_ne_cube (b := b) (e := 1) hapos (by decide) (by decide)
    omega
  · by_cases hpright : p ∣ t + 1
    · have hnmid := prime_not_dvd_other hp hc.2.2.symm hpright
      obtain ⟨a, ha⟩ := hs.1 ((hp.coprime_iff_not_dvd.mpr hpleft).symm.pow_right k)
      obtain ⟨b, hb⟩ := hs.2.1 ((hp.coprime_iff_not_dvd.mpr hnmid).symm.pow_right k)
      have hapos : 0 < a := by
        apply Nat.pos_of_ne_zero
        intro hz
        simp only [hz, zero_pow (by decide : 3 ≠ 0)] at ha
        omega
      apply cube_add_small_ne_cube (b := b) (e := 1) hapos (by decide) (by decide)
      omega
    · obtain ⟨a, ha⟩ := hs.1 ((hp.coprime_iff_not_dvd.mpr hpleft).symm.pow_right k)
      obtain ⟨b, hb⟩ := hs.2.2 ((hp.coprime_iff_not_dvd.mpr hpright).symm.pow_right k)
      have hapos : 0 < a := by
        apply Nat.pos_of_ne_zero
        intro hz
        simp only [hz, zero_pow (by decide : 3 ≠ 0)] at ha
        omega
      apply cube_add_small_ne_cube (b := b) (e := 2) hapos (by decide) (by decide)
      omega

/-- The near-cube route immediately excludes every cubic S, not just S = 1. -/
theorem cubic_solution_S_not_cube {t D S r : ℕ} (ht : 2 ≤ t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) : S ≠ r ^ 3 := by
  intro hS
  apply cube_sub_self_ne_cube (D := D * r ^ 2) ht
  calc
    t ^ 3 - t = D ^ 3 * S ^ 2 := heq
    _ = (D * r ^ 2) ^ 3 := by rw [hS]; ring

/-- Every even-centered solution needs two distinct primes in S. -/
theorem cubic_solution_S_two_distinct_primes {t D S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ∣ S ∧ q ∣ S ∧ p ≠ q := by
  obtain ⟨p, hp, hpS⟩ := Nat.exists_prime_and_dvd (cubic_solution_S_ne_one ht heq)
  rcases cubic_solution_structure ht he heq with ⟨_, _, _, _, _, _, hS⟩
  by_contra hn
  have hunique : ∀ {q : ℕ}, Nat.Prime q → q ∣ S → q = p := by
    intro q hq hqS
    by_contra hqp
    exact hn ⟨p, q, hp, hq, hpS, hqS, Ne.symm hqp⟩
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hS.ne' hunique
  apply even_cube_sub_self_ne_prime_power_square_mul_cube (k := S.primeFactorsList.length) ht he hp
  exact heq.trans (congrArg (fun z : ℕ => D ^ 3 * z ^ 2) hpow)

/-- Quantitative consequence of the new support obstruction. -/
theorem cubic_solution_S_ge_six {t D S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) : 6 ≤ S := by
  obtain ⟨p, q, hp, hq, hpS, hqS, hpq⟩ := cubic_solution_S_two_distinct_primes ht he heq
  rcases cubic_solution_structure ht he heq with ⟨_, _, _, _, _, _, hS⟩
  have hprod : p * q ∣ S :=
    ((Nat.coprime_primes hp hq).mpr hpq).mul_dvd_of_dvd_of_dvd hpS hqS
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have h6 : 6 ≤ p * q := by
    by_cases hp_eq_two : p = 2
    · have hq3 : 3 ≤ q := by omega
      calc
        6 = 2 * 3 := by norm_num
        _ ≤ p * q := Nat.mul_le_mul hp2 hq3
    · have hp3 : 3 ≤ p := by omega
      calc
        6 = 3 * 2 := by norm_num
        _ ≤ p * q := Nat.mul_le_mul hp3 hq2
  exact h6.trans (Nat.le_of_dvd hS hprod)

/-- Any relevant solution is actually beyond t = 3D, not merely t = D. -/
theorem cubic_solution_three_mul_D_lt {t D S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) : 3 * D < t := by
  have hS6 := cubic_solution_S_ge_six ht he heq
  rcases cubic_solution_structure ht he heq with ⟨_, _, _, _, _, hD, _⟩
  have hD3 : 0 < D ^ 3 := pow_pos hD 3
  have hS2 : 36 ≤ S ^ 2 := by
    exact Nat.pow_le_pow_left hS6 2
  have hmul := Nat.mul_le_mul_left (D ^ 3) hS2
  have hN : t ^ 3 = D ^ 3 * S ^ 2 + t :=
    (Nat.sub_eq_iff_eq_add (Nat.le_self_pow (by decide : 3 ≠ 0) t)).mp heq
  have hcube : (3 * D) ^ 3 < t ^ 3 := by nlinarith
  exact (Nat.pow_lt_pow_iff_left (by decide : 3 ≠ 0)).mp hcube


/-- Exact algebraic gap bounds: the near-cube error is of order 1/t.
Putting u = D * S^(2/3) gives an error of order 1/(D*t), hence order D^(-2)
for the rational approximation t/D. -/
theorem near_cube_gap {t u : ℝ} (ht : 2 ≤ t) (hu : 0 ≤ u)
    (h : u ^ 3 = t ^ 3 - t) :
    1 / (3 * t) < t - u ∧ t - u < 1 / (2 * t) := by
  have htpos : 0 < t := by linarith
  have hult : u < t := lt_of_pow_lt_pow_left₀ 3 htpos.le (by linarith)
  have hdpos : 0 < t - u := sub_pos.mpr hult
  have hu2 : u ^ 2 < t ^ 2 := (pow_lt_pow_iff_left₀ hu htpos.le (by decide : 2 ≠ 0)).mpr hult
  have htu : t * u < t * t := mul_lt_mul_of_pos_left hult htpos
  have hk : t ^ 2 + t * u + u ^ 2 < 3 * t ^ 2 := by nlinarith
  have hnorm : (t - u) * (t ^ 2 + t * u + u ^ 2) = t := by nlinarith [h]
  have hprod : t < (t - u) * (3 * t ^ 2) := by
    calc
      t = (t - u) * (t ^ 2 + t * u + u ^ 2) := hnorm.symm
      _ < (t - u) * (3 * t ^ 2) := mul_lt_mul_of_pos_left hk hdpos
  have hcancel : t * 1 < t * (3 * t * (t - u)) := by nlinarith only [hprod]
  have hone : 1 < 3 * t * (t - u) := (mul_lt_mul_iff_right₀ htpos).mp hcancel
  have hlow : 1 / (3 * t) < t - u :=
    (div_lt_iff₀ (by positivity : 0 < 3 * t)).mpr (by nlinarith only [hone])
  have ht2 : 4 ≤ t ^ 2 := by nlinarith
  have hpoly : 0 < 4 * t ^ 4 - 6 * t ^ 2 + 1 := by
    nlinarith [sq_nonneg (t ^ 2 - 1)]
  have hscaled :
      8 * t ^ 3 * ((t ^ 3 - t) - (t - 1 / (2 * t)) ^ 3) =
        4 * t ^ 4 - 6 * t ^ 2 + 1 := by
    field_simp
    ring
  have hdifference : 0 < (t ^ 3 - t) - (t - 1 / (2 * t)) ^ 3 := by
    apply (mul_pos_iff_of_pos_left (by positivity : 0 < 8 * t ^ 3)).mp
    rw [hscaled]
    exact hpoly
  have hcompare : t - 1 / (2 * t) < u :=
    lt_of_pow_lt_pow_left₀ 3 hu (by linarith [hdifference])
  exact ⟨hlow, by linarith⟩


/-- An exact even integral point with powerful center that is far beyond x = D².
It has D² | y, but deliberately does NOT have D³ | y. Thus this does not
refute the centered cubic equation or the original conjecture. -/
theorem weaker_cm_height_counterexample :
    Squarefree (2301 : ℕ) ∧ Even (31212 : ℕ) ∧ Nat.Powerful 31212 ∧
      71818812 = 2301 * 31212 ∧ 2301 ^ 2 ∣ 608635563354 ∧
      (608635563354 : ℕ) ^ 2 = 71818812 ^ 3 - 2301 ^ 2 * 71818812 ∧
      2301 < 31212 ∧ ¬2301 ^ 3 ∣ 608635563354 := by
  have hsf : Squarefree (2301 : ℕ) := by
    have h3 : Squarefree (3 : ℕ) := (by norm_num : Nat.Prime 3).squarefree
    have h13 : Squarefree (13 : ℕ) := (by norm_num : Nat.Prime 13).squarefree
    have h59 : Squarefree (59 : ℕ) := (by norm_num : Nat.Prime 59).squarefree
    have hleft : Squarefree (3 * 13 : ℕ) :=
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 3 13)).mpr ⟨h3, h13⟩
    have hfull : Squarefree ((3 * 13) * 59 : ℕ) :=
      (Nat.squarefree_mul (by norm_num : Nat.Coprime (3 * 13) 59)).mpr ⟨hleft, h59⟩
    norm_num at hfull ⊢
    exact hfull
  have hp : Nat.Powerful 31212 := by
    have heq : (31212 : ℕ) = 34 ^ 2 * 3 ^ 3 := by norm_num
    rw [heq]
    exact powerful_mul (powerful_square 34) (powerful_cube 3)
  refine ⟨hsf, ?_, hp, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [even_iff_two_dvd]


/-- The global reduction remains exact after imposing the new unbounded S restrictions.
This is a reduction, NOT a proof of nonexistence. -/
theorem exists_powerful_triple_iff_restricted_squarefree_cubic :
    (∃ n : ℕ, Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) ↔
      ∃ t D S : ℕ, Even t ∧ 2 ≤ t ∧ 0 < D ∧ Squarefree D ∧
        t ^ 3 - t = D ^ 3 * S ^ 2 ∧ 6 ≤ S ∧ 3 * D < t ∧
        (∀ r : ℕ, S ≠ r ^ 3) ∧
        (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ∣ S ∧ q ∣ S ∧ p ≠ q) := by
  constructor
  · intro h
    rcases exists_powerful_triple_iff_squarefree_cubic.mp h with
      ⟨t, D, S, he, ht, hD, hsf, heq⟩
    refine ⟨t, D, S, he, ht, hD, hsf, heq, cubic_solution_S_ge_six ht he heq,
      cubic_solution_three_mul_D_lt ht he heq, ?_, cubic_solution_S_two_distinct_primes ht he heq⟩
    intro r
    exact cubic_solution_S_not_cube ht heq
  · rintro ⟨t, D, S, he, ht, hD, hsf, heq, _, _, _, _⟩
    exact exists_powerful_triple_iff_squarefree_cubic.mpr ⟨t, D, S, he, ht, hD, hsf, heq⟩

end Erdos364.AuxiliaryCubeApproximation

#print axioms Erdos364.AuxiliaryCubeApproximation.cube_factor_of_cubic_product
#print axioms Erdos364.AuxiliaryCubeApproximation.centered_cubic_cube_factors
#print axioms Erdos364.AuxiliaryCubeApproximation.cube_add_small_ne_cube
#print axioms Erdos364.AuxiliaryCubeApproximation.even_cube_sub_self_ne_prime_power_square_mul_cube
#print axioms Erdos364.AuxiliaryCubeApproximation.cubic_solution_S_not_cube
#print axioms Erdos364.AuxiliaryCubeApproximation.weaker_cm_height_counterexample
#print axioms Erdos364.AuxiliaryCubeApproximation.cubic_solution_S_two_distinct_primes
#print axioms Erdos364.AuxiliaryCubeApproximation.near_cube_gap
#print axioms Erdos364.AuxiliaryCubeApproximation.cubic_solution_S_ge_six
#print axioms Erdos364.AuxiliaryCubeApproximation.cubic_solution_three_mul_D_lt
#print axioms Erdos364.AuxiliaryCubeApproximation.exists_powerful_triple_iff_restricted_squarefree_cubic
