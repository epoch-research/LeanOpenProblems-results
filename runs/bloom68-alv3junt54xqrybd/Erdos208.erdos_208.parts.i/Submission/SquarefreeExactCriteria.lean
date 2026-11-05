import Submission.GapCriteria

/-!
# Exact criteria for the negation of the squarefree-gap conjecture

Only equivalences and implications are proved here. No unbounded bad-interval
family is constructed and no all-exponent interval exclusion is proved.
This module does not import or reference either original stub theorem.
-/


open Filter

namespace SquarefreeExactCriteria

/-- The all-positive-exponent squarefree-gap assertion, independently stated. -/
def GapConjecture : Prop :=
  ∀ ε > (0 : ℝ),
    (fun n : ℕ => (SquarefreeSqrt.s (n + 1) - SquarefreeSqrt.s n : ℝ))
      =O[atTop] (fun n => (SquarefreeSqrt.s n : ℝ) ^ ε)

theorem exact_disproof_criterion :
    (¬ GapConjecture) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 0 < C → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧
          C * (SquarefreeSqrt.s n : ℝ) ^ ε <
            (SquarefreeSqrt.s (n + 1) -
              SquarefreeSqrt.s n : ℝ) := by
  change
    (¬ (∀ ε : ℝ, 0 < ε →
      ((fun n : ℕ => (SquarefreeSqrt.s (n + 1) - SquarefreeSqrt.s n : ℝ))
        =O[atTop] (fun n => (SquarefreeSqrt.s n : ℝ) ^ ε)))) ↔ _
  simp only [SquarefreeCriteria.gap_isBigO_iff_eventual_bound]
  push_neg
  rfl

/-- An unbounded fixed-power bad-interval family would give a genuine disproof.
This implication does not construct such a family. -/
theorem disproof_of_polynomial_bad_intervals
    (A : ℝ) (hA : 0 < A)
    (hbad : ∀ M : ℕ, ∃ N H : ℕ, M ≤ N ∧ M ≤ H ∧
      (N : ℝ) ≤ (H : ℝ) ^ A ∧
      ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m) :
    ¬ GapConjecture := by
  intro htarget
  let ε : ℝ := 1 / (2 * A)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have ht : ∀ ε > (0 : ℝ),
      ((fun n : ℕ => (SquarefreeSqrt.s (n + 1) - SquarefreeSqrt.s n : ℝ))
        =O[atTop] (fun n => (SquarefreeSqrt.s n : ℝ) ^ ε)) := htarget
  obtain ⟨C, hC, N₀, hinterval⟩ :=
    (SquarefreeCriteria.gap_isBigO_iff_intervalBound hε.le).mp (ht ε hε)
  let M : ℕ := max N₀ (max 1 (⌈C ^ 2⌉₊ + 1))
  obtain ⟨N, H, hNM, hHM, hsize, hnosf⟩ := hbad M
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hNM
  have hH1 : 1 ≤ H :=
    (le_max_left 1 (⌈C ^ 2⌉₊ + 1)).trans ((le_max_right _ _).trans hHM)
  have hceilH : ⌈C ^ 2⌉₊ + 1 ≤ H :=
    (le_max_right 1 (⌈C ^ 2⌉₊ + 1)).trans ((le_max_right _ _).trans hHM)
  have hHpos : 0 < (H : ℝ) := by exact_mod_cast hH1
  have hC2H : C ^ 2 < (H : ℝ) := by
    have hceil : C ^ 2 ≤ (⌈C ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have hh : (⌈C ^ 2⌉₊ : ℝ) + 1 ≤ (H : ℝ) := by exact_mod_cast hceilH
    linarith
  have hmul : A * ε = (1 / 2 : ℝ) := by
    dsimp [ε]
    field_simp
  have hrootbound : (N : ℝ) ^ ε ≤ Real.sqrt (H : ℝ) := by
    calc
      (N : ℝ) ^ ε ≤ ((H : ℝ) ^ A) ^ ε :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hsize hε.le
      _ = (H : ℝ) ^ (A * ε) := (Real.rpow_mul hHpos.le A ε).symm
      _ = Real.sqrt (H : ℝ) := by rw [hmul, Real.sqrt_eq_rpow]
  have hCroot : C * Real.sqrt (H : ℝ) < (H : ℝ) := by
    have hsqrt := Real.sq_sqrt hHpos.le
    have hsqrtpos := Real.sqrt_pos.mpr hHpos
    nlinarith
  obtain ⟨m, hsf, hNm, hdist⟩ := hinterval N hN₀
  have hmdist : (m : ℝ) - (N : ℝ) < (H : ℝ) :=
    lt_of_le_of_lt (hdist.trans (mul_le_mul_of_nonneg_left hrootbound hC.le)) hCroot
  have hmHreal : (m : ℝ) ≤ (N : ℝ) + (H : ℝ) := by linarith
  have hmH : m ≤ N + H := by exact_mod_cast hmHreal
  exact hnosf m hNm hmH hsf

theorem polynomial_bad_intervals_of_disproof
    (hnot : ¬ GapConjecture) :
    ∃ A : ℝ, 0 < A ∧ ∀ M : ℕ, ∃ N H : ℕ, M ≤ N ∧ M ≤ H ∧
      (N : ℝ) ≤ (H : ℝ) ^ A ∧
      ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m := by
  obtain ⟨ε, hε, hlarge⟩ := exact_disproof_criterion.mp hnot
  have hi : 0 < ε⁻¹ := inv_pos.mpr hε
  refine ⟨ε⁻¹, hi, ?_⟩
  intro M
  let J : ℕ := max M ⌈(M : ℝ) ^ ε⁻¹⌉₊
  obtain ⟨n, hn, hgap⟩ := hlarge 2 (by norm_num) J
  let N : ℕ := SquarefreeSqrt.s n
  let H : ℕ := ⌈(N : ℝ) ^ ε⌉₊
  have hnN : n ≤ N := SquarefreeSqrt.s_strictMono.id_le n
  have hNM : M ≤ N := (le_max_left _ _).trans (hn.trans hnN)
  have hceilN : ⌈(M : ℝ) ^ ε⁻¹⌉₊ ≤ N :=
    (le_max_right _ _).trans (hn.trans hnN)
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast SquarefreeSqrt.s_pos n
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (SquarefreeSqrt.s_pos n).ne')
  have hMpow : (M : ℝ) ≤ (N : ℝ) ^ ε := by
    have hbase : (M : ℝ) ^ ε⁻¹ ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hceilN)
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg M) _) hbase hε.le
    simpa only [Real.rpow_inv_rpow (Nat.cast_nonneg M) hε.ne'] using hh
  have hMH : M ≤ H := by
    have hh : (M : ℝ) ≤ (H : ℝ) := hMpow.trans (Nat.le_ceil _)
    exact_mod_cast hh
  have hsize : (N : ℝ) ≤ (H : ℝ) ^ ε⁻¹ := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le ε)
      (Nat.le_ceil ((N : ℝ) ^ ε)) hi.le
    simpa only [Real.rpow_rpow_inv hNpos.le hε.ne'] using hh
  have hpow1 : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hHlt : (H : ℝ) < 2 * (N : ℝ) ^ ε := by
    have hc : (H : ℝ) < (N : ℝ) ^ ε + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg hNpos.le _)
    linarith
  refine ⟨N, H, hNM, hMH, hsize, ?_⟩
  intro m hNm hmH hsf
  have hnext : (SquarefreeSqrt.s (n + 1) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast SquarefreeSqrt.next_le_of_squarefree hsf hNm
  have hmreal : (m : ℝ) ≤ (N : ℝ) + (H : ℝ) := by exact_mod_cast hmH
  dsimp [N] at hHlt hmreal
  linarith

theorem exact_polynomial_bad_interval_criterion :
    (¬ GapConjecture) ↔
      ∃ A : ℝ, 0 < A ∧ ∀ M : ℕ, ∃ N H : ℕ, M ≤ N ∧ M ≤ H ∧
        (N : ℝ) ≤ (H : ℝ) ^ A ∧
        ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m := by
  constructor
  · exact polynomial_bad_intervals_of_disproof
  · rintro ⟨A, hA, hbad⟩
    exact disproof_of_polynomial_bad_intervals A hA hbad

theorem exact_polynomial_interval_proof_criterion :
    GapConjecture ↔
      ∀ A : ℝ, 0 < A → ∃ M : ℕ, ∀ N : ℕ, M ≤ N → ∀ H : ℕ,
        M ≤ H → (N : ℝ) ≤ (H : ℝ) ^ A →
          ∃ m : ℕ, N < m ∧ m ≤ N + H ∧ Squarefree m := by
  classical
  have h := not_congr exact_polynomial_bad_interval_criterion
  push_neg at h
  constructor
  · intro hp A hA
    obtain ⟨M, hM⟩ := h.mp hp A hA
    exact ⟨M, fun N hN H hH hsize => hM N H hN hH hsize⟩
  · intro hp
    apply h.mpr
    intro A hA
    obtain ⟨M, hM⟩ := hp A hA
    exact ⟨M, fun N H hN hH hsize => hM N hN H hH hsize⟩

#print axioms polynomial_bad_intervals_of_disproof
#print axioms exact_polynomial_bad_interval_criterion
#print axioms exact_polynomial_interval_proof_criterion

#print axioms exact_disproof_criterion
#print axioms disproof_of_polynomial_bad_intervals

end SquarefreeExactCriteria
