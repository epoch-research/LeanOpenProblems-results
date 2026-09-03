import Submission.DoubleCoverThirtieth

/-! Double prime-class covers have a uniform linear length bound. Arbitrary
Jacobsthal covers need not satisfy the indispensable no-triple-hit hypothesis. -/
namespace Erdos970.DoubleCover
open Finset Real WeightedMertens Filter

lemma thirtieth_power_floor (m : ℕ) : ∃ t : ℕ,
    t ^ 30 ≤ m ∧ m < (t + 1) ^ 30 ∧ ∀ T : ℕ, T ^ 30 ≤ m → T ≤ t := by
  let t := Nat.findGreatest (fun s => s ^ 30 ≤ m) m
  have hroot : t ^ 30 ≤ m := Nat.findGreatest_spec (P := fun s => s ^ 30 ≤ m)
    (m := 0) (n := m) (by omega) (by norm_num)
  have hmax : ∀ T : ℕ, T ^ 30 ≤ m → T ≤ t := by
    intro T hT
    exact Nat.le_findGreatest ((Nat.le_pow (by omega : 0 < 30)).trans hT) hT
  refine ⟨t, hroot, ?_, hmax⟩
  by_contra hn
  have h := hmax (t + 1) (by omega)
  omega

/-- There is one absolute linear bound for every prime-class cover of
multiplicity at most two. -/
theorem prime_double_cover_linear :
    ∃ C > (0 : ℝ), ∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ),
      (∀ p ∈ P, p.Prime) →
      (∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) →
      (∀ x < m, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ 2) →
      (m : ℝ) ≤ C * P.card := by
  obtain ⟨N, hN⟩ := exists_prime_count_threshold
  have hev : ∀ᶠ t : ℕ in atTop,
      2000 * (boundConstant + 1) ≤ log (t : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  let T := max 2 (max N M)
  have hT2 : 2 ≤ T := le_max_left _ _
  have hTN : N ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTM : M ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  let C : ℕ := T ^ 30 + 2 ^ 30 * 6000
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P r m hP hcover hdouble
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  by_cases hm : m = 0
  · simp only [hm, Nat.cast_zero]
    positivity
  have hk : 1 ≤ P.card := by
    obtain ⟨p, hp, _⟩ := hcover 0 (by omega)
    exact card_pos.mpr ⟨p,hp⟩
  suffices hh : m ≤ C * P.card by exact_mod_cast hh
  by_cases hlarge : T ^ 30 ≤ m
  · obtain ⟨t, htroot, htnext, htmax⟩ := thirtieth_power_floor m
    have hTt := htmax T hlarge
    have ht2 : 2 ≤ t := hT2.trans hTt
    have hbound := prime_double_cover_thirtieth P hP r t ht2
      (hM t (hTM.trans hTt))
      (fun n hn => hN n (hTN.trans (hTt.trans hn)))
      (fun x hx => hcover x (hx.trans_le htroot))
      (fun x hx => hdouble x (hx.trans_le htroot))
    have htwice : (t + 1) ^ 30 ≤ 2 ^ 30 * t ^ 30 := by
      simpa only [mul_pow] using Nat.pow_le_pow_left (by omega : t + 1 ≤ 2 * t) 30
    have hb := Nat.mul_le_mul_left (2 ^ 30) hbound
    dsimp [C]
    nlinarith only [htnext, htwice, hb, Nat.zero_le (T ^ 30 * P.card)]
  · have hsmall : m ≤ T ^ 30 := by omega
    have hTle : T ^ 30 ≤ C := by dsimp [C]; omega
    exact (hsmall.trans hTle).trans (Nat.le_mul_of_pos_right C hk)

#print axioms thirtieth_power_floor
#print axioms prime_double_cover_linear
end Erdos970.DoubleCover
