import FormalConjecturesUtil

/-!
A modular restriction on the reduced gaps in a cubic collision.
This only excludes specified gap-ratio families, not all collisions.
-/

namespace Erdos1206

/-- Cancel the common gap factor before making any modular reduction. -/
lemma cube_collision_cancel_common_gap {a b g u v : ℕ} (hg : 0 < g)
    (he : (a + g * u) ^ 3 + b ^ 3 = a ^ 3 + (b + g * v) ^ 3) :
    u * ((a + g * u) ^ 2 + (a + g * u) * a + a ^ 2) =
      v * ((b + g * v) ^ 2 + (b + g * v) * b + b ^ 2) := by
  apply Nat.eq_of_mul_eq_mul_left hg
  have ha : (a + g * u) ^ 3 =
      a ^ 3 + g * (u * ((a + g * u) ^ 2 + (a + g * u) * a + a ^ 2)) := by ring
  have hb : (b + g * v) ^ 3 =
      b ^ 3 + g * (v * ((b + g * v) ^ 2 + (b + g * v) * b + b ^ 2)) := by ring
  omega

/-- If all roots are `1 mod m`, the reduced gaps must agree modulo `m`,
provided that `3` is coprime to `m`. The common gap factor may be divisible by `m`. -/
lemma cube_collision_gap_ratio_modEq {a b g u v m : ℕ}
    (hg : 0 < g) (hm : Nat.Coprime m 3)
    (ha : Nat.ModEq m a 1) (hau : Nat.ModEq m (a + g * u) 1)
    (hb : Nat.ModEq m b 1) (hbv : Nat.ModEq m (b + g * v) 1)
    (he : (a + g * u) ^ 3 + b ^ 3 = a ^ 3 + (b + g * v) ^ 3) :
    Nat.ModEq m u v := by
  have hQ₁ : Nat.ModEq m ((a + g * u) ^ 2 + (a + g * u) * a + a ^ 2) 3 := by
    simpa using ((hau.pow 2).add (hau.mul ha)).add (ha.pow 2)
  have hQ₂ : Nat.ModEq m ((b + g * v) ^ 2 + (b + g * v) * b + b ^ 2) 3 := by
    simpa using ((hbv.pow 2).add (hbv.mul hb)).add (hb.pow 2)
  have hcancel := cube_collision_cancel_common_gap hg he
  have heq : Nat.ModEq m
      (u * ((a + g * u) ^ 2 + (a + g * u) * a + a ^ 2))
      (v * ((b + g * v) ^ 2 + (b + g * v) * b + b ^ 2)) := by rw [hcancel]
  exact Nat.ModEq.cancel_right_of_coprime hm
    ((hQ₁.mul_left u).symm.trans (heq.trans (hQ₂.mul_left v)))

/-- In particular, unequal gap numerators smaller than the modulus are excluded. -/
lemma no_cube_collision_small_gap_ratio {a b g u v m : ℕ}
    (hg : 0 < g) (hm : Nat.Coprime m 3) (hu : u < m) (hv : v < m) (huv : u ≠ v)
    (ha : Nat.ModEq m a 1) (hau : Nat.ModEq m (a + g * u) 1)
    (hb : Nat.ModEq m b 1) (hbv : Nat.ModEq m (b + g * v) 1) :
    (a + g * u) ^ 3 + b ^ 3 ≠ a ^ 3 + (b + g * v) ^ 3 := by
  intro he
  have h := cube_collision_gap_ratio_modEq hg hm ha hau hb hbv he
  apply huv
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using h

open Filter
open scoped Topology

lemma one_residue_positive_lowerDensity {m : ℕ} (hm : 1 < m) :
    0 < ({n : ℕ | Nat.ModEq m n 1} : Set ℕ).lowerDensity := by
  let A : Set ℕ := {n | Nat.ModEq m n 1}
  have hc (N : ℕ) : N / m ≤ (A ∩ Set.Iio N).ncard := by
    have hi : (Set.Iio (N / m) : Set ℕ).ncard ≤ (A ∩ Set.Iio N).ncard := by
      apply Set.ncard_le_ncard_of_injOn (fun k : ℕ => 1 + m * k)
      · intro k hk
        refine ⟨?_, ?_⟩
        · change Nat.ModEq m (1 + m * k) 1
          simp [Nat.ModEq, Nat.add_mod]
        · have hmul : m * (k + 1) ≤ N :=
            (Nat.mul_le_mul_left m (show k + 1 ≤ N / m from hk)).trans (Nat.mul_div_le N m)
          change 1 + m * k < N
          nlinarith
      · intro k _ l _ hkl
        dsimp only at hkl
        nlinarith
    simpa using hi
  have hmr : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hev : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / (2 * m) ≤ A.partialDensity Set.univ N := by
    filter_upwards [eventually_ge_atTop (2 * m)] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hdiv : N < m * (N / m) + m := by
      have h := Nat.mod_lt N (show 0 < m by omega)
      have h' := Nat.mod_add_div N m
      omega
    have hdiv' : (N : ℝ) < m * (N / m : ℕ) + m := by exact_mod_cast hdiv
    have hN' : (2 : ℝ) * m ≤ N := by exact_mod_cast hN
    have hc' : (N / m : ℕ) ≤ ((A ∩ Set.Iio N).ncard : ℝ) := by exact_mod_cast hc N
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    apply (le_div_iff₀ hN0).mpr
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).mpr
    nlinarith
  have hl : (1 : ℝ) / (2 * m) ≤ A.lowerDensity :=
    le_liminf_of_le (isCoboundedUnder_ge_of_le atTop
      (fun N => Set.partialDensity_le_one A Set.univ N)) hev
  exact (by positivity : (0 : ℝ) < 1 / (2 * m)).trans_le hl

/-- A positive-density progression avoids every collision having one of the
finitely many unequal gap ratios with both numerator and denominator at most `K`.
The common multiplier of the two gaps is unrestricted. -/
lemma positive_density_avoids_bounded_gap_ratios (K : ℕ) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ a b g u v : ℕ, 0 < g → u ≤ K → v ≤ K → u ≠ v →
        a ∈ A → a + g * u ∈ A → b ∈ A → b + g * v ∈ A →
        (a + g * u) ^ 3 + b ^ 3 ≠ a ^ 3 + (b + g * v) ^ 3 := by
  let m := 3 * (K + 1) + 1
  let A : Set ℕ := {n | Nat.ModEq m n 1}
  have hm : 1 < m := by dsimp [m]; omega
  have hm3 : Nat.Coprime m 3 := by
    change Nat.gcd m 3 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec]
    simp [m, Nat.add_mod]
  have hd : 0 < A.lowerDensity := one_residue_positive_lowerDensity hm
  refine ⟨A, ?_, hd, ?_⟩
  · by_contra hfin
    have hzero := (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
    change A.lowerDensity = 0 at hzero
    linarith
  · intro a b g u v hg hu hv huv ha hau hb hbv
    exact no_cube_collision_small_gap_ratio hg hm3
      (by dsimp [m]; omega) (by dsimp [m]; omega) huv ha hau hb hbv

end Erdos1206

#print axioms Erdos1206.cube_collision_gap_ratio_modEq
#print axioms Erdos1206.no_cube_collision_small_gap_ratio

#print axioms Erdos1206.one_residue_positive_lowerDensity
#print axioms Erdos1206.positive_density_avoids_bounded_gap_ratios
