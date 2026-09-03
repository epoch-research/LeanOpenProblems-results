import Submission.CubicRootObstruction

/-! Fixed square-class obstructions to a suggested sixth-power construction.
These exclude two specific one-step cubic amplifier families. They neither
prove sixth-power descent nor settle Erdős 406. -/
namespace Erdos406CubeAmplificationSquare

private def squareResidue (m n : ℕ) : Prop :=
  ∃ x : Fin m, (x : ℕ)^2 % m = n % m

private instance (m n : ℕ) : Decidable (squareResidue m n) :=
  inferInstanceAs (Decidable (∃ x : Fin m, (x : ℕ)^2 % m = n % m))

private lemma squareResidue_of_isSquare {m n : ℕ} (hm : 0 < m)
    (h : IsSquare n) : squareResidue m n := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨⟨x % m, Nat.mod_lt _ hm⟩, ?_⟩
  simp [pow_two, Nat.mul_mod]

private lemma pow_mod_period (a m t n : ℕ) (h : a^t % m = 1) :
    a^n % m = a^(n%t) % m := by
  conv_lhs => rw [← Nat.mod_add_div n t, pow_add, pow_mul]
  simp only [Nat.mul_mod, Nat.pow_mod, h, one_pow, Nat.mod_mod]
  simp

private lemma amplifier_square_residue (a L m t : ℕ) (hm : 0 < m)
    (hperiod : 3^t % m = 1) (h : IsSquare (a*(3^L+1))) :
    squareResidue m (a*(3^(L%t)+1)) := by
  have hh := squareResidue_of_isSquare hm h
  have hp := pow_mod_period 3 m t L hperiod
  simpa only [squareResidue, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, hp] using hh

private lemma seed562_certificate : ∀ e : Fin 24,
    ¬ (squareResidue 32 (562*(3^(e:ℕ)+1)) ∧
      squareResidue 7 (562*(3^(e:ℕ)+1)) ∧
      squareResidue 13 (562*(3^(e:ℕ)+1))) := by
  decide +kernel

private lemma seed7489_certificate : ∀ e : Fin 18,
    ¬ (squareResidue 7 (7489*(3^(e:ℕ)+1)) ∧
      squareResidue 13 (7489*(3^(e:ℕ)+1)) ∧
      squareResidue 19 (7489*(3^(e:ℕ)+1)) ∧
      squareResidue 37 (7489*(3^(e:ℕ)+1))) := by
  decide +kernel

/-- No spacing, small or large, makes this amplified bad cube root a square. -/
theorem seed562_amplifier_not_square (L : ℕ) :
    ¬ IsSquare (562*(3^L+1)) := by
  intro h
  apply seed562_certificate ⟨L%24, Nat.mod_lt _ (by decide)⟩
  exact ⟨amplifier_square_residue 562 L 32 24 (by decide) (by norm_num) h,
    amplifier_square_residue 562 L 7 24 (by decide) (by norm_num) h,
    amplifier_square_residue 562 L 13 24 (by decide) (by norm_num) h⟩

/-- The other known primitive bad cube root has a different modular obstruction. -/
theorem seed7489_amplifier_not_square (L : ℕ) :
    ¬ IsSquare (7489*(3^L+1)) := by
  intro h
  apply seed7489_certificate ⟨L%18, Nat.mod_lt _ (by decide)⟩
  exact ⟨amplifier_square_residue 7489 L 7 18 (by decide) (by norm_num) h,
    amplifier_square_residue 7489 L 13 18 (by decide) (by norm_num) h,
    amplifier_square_residue 7489 L 19 18 (by decide) (by norm_num) h,
    amplifier_square_residue 7489 L 37 18 (by decide) (by norm_num) h⟩

private lemma scaled_seed_certificate : ∀ e : Fin 8,
    ¬ (squareResidue 32 (871070230939*(3^(e:ℕ)+1)) ∧
      squareResidue 5 (871070230939*(3^(e:ℕ)+1))) := by
  decide +kernel

/-- This seed witnesses failure of unrestricted descent for a scaled cube,
but its one-step amplifications never have square roots at the cube level. -/
theorem scaled_seed_amplifier_not_square (L : ℕ) :
    ¬ IsSquare (871070230939*(3^L+1)) := by
  intro h
  apply scaled_seed_certificate ⟨L%8, Nat.mod_lt _ (by decide)⟩
  exact ⟨amplifier_square_residue 871070230939 L 32 8 (by decide) (by norm_num) h,
    amplifier_square_residue 871070230939 L 5 8 (by decide) (by norm_num) h⟩

private lemma scaled_two_step_certificate : ∀ e f : Fin 16,
    ¬ (squareResidue 64 (871070230939*(3^(e:ℕ)+1)*(3^(f:ℕ)+1)) ∧
      squareResidue 5 (871070230939*(3^(e:ℕ)+1)*(3^(f:ℕ)+1))) := by
  decide +kernel

/-- Even two successive cubic amplifications of the scaled seed cannot give
a square, with no assumptions on either spacing. -/
theorem scaled_seed_two_amplifiers_not_square (L K : ℕ) :
    ¬ IsSquare (871070230939*(3^L+1)*(3^K+1)) := by
  intro h
  have residue (m : ℕ) (hm : 0 < m) (hperiod : 3^16 % m = 1) :
      squareResidue m (871070230939*(3^(L%16)+1)*(3^(K%16)+1)) := by
    have hh := squareResidue_of_isSquare hm h
    have hL := pow_mod_period 3 m 16 L hperiod
    have hK := pow_mod_period 3 m 16 K hperiod
    simpa only [squareResidue, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, hL, hK] using hh
  exact scaled_two_step_certificate ⟨L%16, Nat.mod_lt _ (by decide)⟩
    ⟨K%16, Nat.mod_lt _ (by decide)⟩
    ⟨residue 64 (by decide) (by norm_num), residue 5 (by decide) (by norm_num)⟩

lemma cube_not_sixth_of_not_square {n : ℕ} (hn : ¬ IsSquare n) (x : ℕ) :
    n^3 ≠ x^6 := by
  intro h
  have hh : n^3 = (x^2)^3 := by simpa only [← pow_mul] using h
  have he : n = x^2 := (Nat.pow_left_inj (by decide : 3 ≠ 0)).mp hh
  exact hn ⟨x, by simpa only [pow_two] using he⟩

/-- These entire good-cube amplifier families cannot supply the required
integer sixth powers. This is not an assertion about all good cubes. -/
theorem seed562_amplified_cube_not_sixth (L x : ℕ) :
    (562*(3^L+1))^3 ≠ x^6 :=
  cube_not_sixth_of_not_square (seed562_amplifier_not_square L) x

theorem seed7489_amplified_cube_not_sixth (L x : ℕ) :
    (7489*(3^L+1))^3 ≠ x^6 :=
  cube_not_sixth_of_not_square (seed7489_amplifier_not_square L) x

theorem scaled_seed_amplified_cube_not_scaled_sixth (L x : ℕ) :
    4*(871070230939*(3^L+1))^3 ≠ 4*x^6 := by
  intro h
  exact cube_not_sixth_of_not_square (scaled_seed_amplifier_not_square L) x
    (by omega)

open Erdos406Work in
/-- A scale-uniform whole-number statement, with the separation bound explicit. -/
lemma good_scaled_cube_mul_separated (c n r : ℕ)
    (hg : Nat.digits 3 (c*n^3) ⊆ [0,1])
    (hr : (Nat.digits 3 (c*n^3)).length ≤ r) :
    Nat.digits 3 (c*(n*(3^(r+1)+1))^3) ⊆ [0,1] := by
  have hnlt : c*n^3 < 3^r :=
    (Nat.lt_base_pow_length_digits (b := 3) (m := c*n^3) (by decide)).trans_le
      (Nat.pow_le_pow_right (by decide) hr)
  have hnlt1 : c*n^3 < 3^(r+1) :=
    hnlt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hnlt2 : c*n^3 < 3^(r+2) :=
    hnlt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hg1 := good_add_shifted hnlt hg hg
  have hg2 := good_add_shifted hnlt1 hg hg1
  have hg3 := good_add_shifted hnlt2 hg hg2
  have he : c*(n*(3^(r+1)+1))^3 =
      c*n^3 + 3^(r+2)*(c*n^3 + 3^(r+1)*(c*n^3 + 3^r*(c*n^3))) := by
    simp only [pow_succ]
    ring
  rw [he]
  exact hg3

lemma seed7489_good_cube_bad_root :
    Nat.digits 3 ((7489 : ℕ)^3) ⊆ [0,1] ∧
      ¬ Nat.digits 3 (7489 : ℕ) ⊆ [0,1] := by
  decide +kernel

/-- This is an infinite-spacing family of good scaled cubes with bad,
nonsquare roots, not a family of counterexamples to sixth-power descent. -/
theorem scaled_seed_family (r : ℕ)
    (hr : (Nat.digits 3 (4*(871070230939 : ℕ)^3)).length ≤ r)
    (hroot : (Nat.digits 3 (871070230939 : ℕ)).length ≤ r+1) :
    Nat.digits 3 (4*(871070230939*(3^(r+1)+1))^3) ⊆ [0,1] ∧
      ¬ Nat.digits 3 (871070230939*(3^(r+1)+1)) ⊆ [0,1] ∧
      ¬ IsSquare (871070230939*(3^(r+1)+1)) := by
  have hs := Erdos406Work.cubic_descent_counterexample
  exact ⟨good_scaled_cube_mul_separated 4 871070230939 r hs.1 hr,
    Erdos406Work.bad_mul_separated (by decide) hs.2 hroot,
    scaled_seed_amplifier_not_square (r+1)⟩

#print axioms scaled_seed_two_amplifiers_not_square
#print axioms scaled_seed_family
#print axioms scaled_seed_amplifier_not_square
#print axioms good_scaled_cube_mul_separated
#print axioms seed562_amplifier_not_square
#print axioms seed7489_amplifier_not_square
#print axioms seed562_amplified_cube_not_sixth
end Erdos406CubeAmplificationSquare
