import Submission.ExponentLinearization
import Submission.PurePowerCubeBoundary

/-! Fixed-valuation, arbitrary finite-window obstructions.
These results do not settle Erdős 406. -/
namespace Erdos406Work

lemma scaledQuotient_one_coprime (s : ℕ) :
    Nat.Coprime (scaledQuotient 1 s) (3 ^ (s + 1)) := by
  have hm : scaledQuotient 1 s % 3 = 1 := by
    simpa [scaledQuotient] using scaledQuotient_stable 1 0 s
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  simp [Nat.dvd_iff_mod_eq_zero, hm]

lemma linear_window_unit (s : ℕ) :
    ∃ u : ℕ, 0 < u ∧ u < 3 ^ (s + 1) ∧ ¬ 3 ∣ u ∧
      u * scaledQuotient 1 s % 3 ^ (s + 1) = 1 := by
  obtain ⟨u, hu, he⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (scaledQuotient_one_coprime s) (one_lt_pow₀ (by decide) (by omega))
  have he' : u * scaledQuotient 1 s % 3 ^ (s + 1) = 1 := by
    simpa [mul_comm] using he
  have hp : 0 < u := by
    by_contra h
    have hz : u = 0 := by omega
    simp [hz] at he'
  have hn : ¬ 3 ∣ u := by
    intro hd
    have hmul : 3 ∣ u * scaledQuotient 1 s := dvd_mul_of_dvd_left hd _
    have hm := congrArg (fun n : ℕ => n % 3) he'
    dsimp only at hm
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega : s + 1 ≠ 0)),
      Nat.mod_eq_zero_of_dvd hmul] at hm
    norm_num at hm
  exact ⟨u, hp, hu, hn, he'⟩

lemma linear_window_power_residue {s u : ℕ}
    (hu : u * scaledQuotient 1 s % 3 ^ (s + 1) = 1) :
    4 ^ (u * 3 ^ s) % 3 ^ (2 * s + 2) = 1 + 3 ^ (s + 1) := by
  have hm := scaledQuotient_linear_mod u s
  change scaledQuotient u s % 3 ^ (s + 1) = _ at hm
  rw [hu] at hm
  rw [scaledQuotient_identity,
    show 2 * s + 2 = (s + 1) + (s + 1) by omega,
    high_block_mod 1 (s + 1) _ (s + 1) (one_lt_pow₀ (by decide) (by omega)), hm]
  simp

lemma good_one_add_three_power (s : ℕ) :
    Nat.digits 3 (1 + 3 ^ (s + 1)) ⊆ [0, 1] := by
  have hh := good_mul_one_add_three_pow (n := 1) (q := s + 1)
    (by decide) (by decide +kernel) (by norm_num)
  simpa [add_comm] using hh

/-- No fixed digit-window size, even one chosen as a function of the exact
3-adic valuation of the exponent, can exclude all bad powers in that class.
The constructed full powers are bad; no infinite family of good powers is asserted. -/
lemma arbitrarily_large_bad_powers_with_fixed_valuation_good_window (s R M : ℕ) :
    ∃ u : ℕ, M ≤ u ∧ ¬ 3 ∣ u ∧
      Nat.digits 3 (4 ^ (u * 3 ^ s) % 3 ^ R) ⊆ [0, 1] ∧
      ¬ Nat.digits 3 (4 ^ (u * 3 ^ s)) ⊆ [0, 1] := by
  let A := 1 + 3 ^ (s + 1)
  have hA : A % 3 = 1 := by
    dsimp [A]
    rw [pow_succ]
    omega
  obtain ⟨m, L, hm, hres, hlead⟩ := residue_prefix_in_four_powers
    (s + R + 1) A 2 (3 ^ s * M) hA (by decide)
  have hp : 1 < 3 ^ (s + 1) := one_lt_pow₀ (by decide) (by omega)
  have hAmod : A % 3 ^ (s + 1) = 1 := by
    dsimp [A]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hp]
  have hsmall : Nat.ModEq (3 ^ (s + 1)) (4 ^ m) 1 := by
    have hh := hres.of_dvd (pow_dvd_pow 3 (by omega : s + 1 ≤ s + R + 1 + 1))
    change 4 ^ m % 3 ^ (s + 1) = 1 % 3 ^ (s + 1)
    rw [hh, hAmod, Nat.mod_eq_of_lt hp]
  have hdiv : 3 ^ s ∣ m := (four_pow_mod_eq_one_iff s m).mp hsmall
  have hnot : ¬ 3 ^ (s + 1) ∣ m := by
    intro hd
    have hh := (four_pow_mod_eq_one_iff (s + 1) m).mpr hd
    have hl := hres.of_dvd (pow_dvd_pow 3
      (by omega : s + 2 ≤ s + R + 1 + 1))
    have hAlt : A < 3 ^ (s + 2) := by
      dsimp [A]
      rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
      omega
    have he : A % 3 ^ (s + 2) = 1 % 3 ^ (s + 2) := hl.symm.trans hh
    rw [Nat.mod_eq_of_lt hAlt,
      Nat.mod_eq_of_lt (one_lt_pow₀ (by decide) (by omega : s + 2 ≠ 0))] at he
    dsimp [A] at he
    omega
  obtain ⟨u, hu⟩ := hdiv
  have he : m = u * 3 ^ s := by simpa [mul_comm] using hu
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · have hpos : 0 < 3 ^ s := by positivity
    rw [hu] at hm
    exact (mul_le_mul_iff_right₀ hpos).mp hm
  · rintro ⟨v, hv⟩
    apply hnot
    refine ⟨v, ?_⟩
    rw [hu, hv, pow_succ]
    ring
  · have hl := hres.of_dvd (pow_dvd_pow 3
      (by omega : R ≤ s + R + 1 + 1))
    rw [← he, hl]
    exact good_mod_three_pow (good_one_add_three_power s) R
  · intro hg
    rw [← he] at hg
    have hb := good_div_three_pow hg L
    rw [hlead] at hb
    exact (by decide +kernel : ¬ Nat.digits 3 2 ⊆ [0, 1]) hb

#print axioms arbitrarily_large_bad_powers_with_fixed_valuation_good_window
#print axioms linear_window_unit
#print axioms linear_window_power_residue
end Erdos406Work
