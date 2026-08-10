import FormalConjectures.Util.ProblemImports
import Submission.CoeffLemma
open PowerSeries BigOperators
set_option linter.unusedVariables false

noncomputable def rootCoeff (d : ℕ → ℤ) : ℕ → ℤ
| 0 => 1
| n+1 =>
    ((16 * d (n+1) - PowerSeries.coeff (n+1)
      ((PowerSeries.mk fun k => if h : k < n+1 then rootCoeff d k else 0 : PowerSeries ℤ) ^ 8)) / 8)
termination_by n => n

lemma partial_const (d : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff 0 (PowerSeries.mk fun k => if h : k < n+1 then rootCoeff d k else 0 : PowerSeries ℤ) = 1 := by
  simp [rootCoeff.eq_1]

lemma partial_as_one_add_two (d : ℕ → ℤ) : ∀ n : ℕ,
    (∀ k, 0 < k → k < n+1 → (2 : ℤ) ∣ rootCoeff d k) →
    ∃ E : PowerSeries ℤ, (PowerSeries.mk fun k => if h : k < n+1 then rootCoeff d k else 0 : PowerSeries ℤ) = 1 + 2 • E
| n, hev => by
    let E : PowerSeries ℤ := PowerSeries.mk fun k => if k = 0 then 0 else ((if h : k < n+1 then rootCoeff d k else 0 : ℤ) / 2)
    refine ⟨E, ?_⟩
    ext k
    by_cases hk0 : k = 0
    · subst hk0
      simp [rootCoeff.eq_1]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      by_cases hkn : k < n+1
      · obtain ⟨z, hz⟩ := hev k hkpos hkn
        simp [E, hk0, hkn, hz]
      · simp [E, hk0, hkn]

lemma partial_pow8_coeff_dvd16 (d : ℕ → ℤ) (n : ℕ)
    (hev : ∀ k, 0 < k → k < n+1 → (2 : ℤ) ∣ rootCoeff d k) :
    (16 : ℤ) ∣ PowerSeries.coeff (n+1)
      ((PowerSeries.mk fun k => if h : k < n+1 then rootCoeff d k else 0 : PowerSeries ℤ) ^ 8) := by
  obtain ⟨E, hE⟩ := partial_as_one_add_two d n hev
  rw [hE]
  exact coeff_pos_pow8_one_add_two_dvd16 E (Nat.succ_pos n)

lemma rootCoeff_even_pos (d : ℕ → ℤ) : ∀ n, 0 < n → (2 : ℤ) ∣ rootCoeff d n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ m =>
      rw [rootCoeff.eq_2]
      have hev : ∀ k, 0 < k → k < m+1 → (2 : ℤ) ∣ rootCoeff d k := by
        intro k hkpos hkm
        exact ih k (by omega) hkpos
      have h16 := partial_pow8_coeff_dvd16 d m hev
      obtain ⟨z, hz⟩ := h16
      rw [hz]
      -- ((16*d - 16*z)/8) = 2*(d-z)
      use (2 * (d (m+1) - z))
      ring_nf
      -- need division simplification
      norm_num
