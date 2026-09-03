import Submission.QuadraticRecurrenceAverages

/-! Two finite extraction steps for a polynomial single-phase recurrence bound. -/
namespace Erdos3QuadraticRecurrenceExtraction
open Finset Erdos3QuadraticRecurrenceAverages Erdos3FiniteFourier
  Erdos3LinearFormsUniformity Erdos3FiniteUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000

lemma unit_power_pair (z : ℂ) (hz : ‖z‖ = 1) {i j : ℕ} (hij : j ≤ i) :
    z^i*conj (z^j) = z^(i-j) := by
  calc
    _ = z^(i-j)*(z^j*conj (z^j)) := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hij]
    _ = _ := by rw [mul_conj_eq_one (by rw [norm_pow, hz, one_pow]), mul_one]

lemma norm_pair_swap {X : Type*} [Fintype X] (f g : X → ℂ) :
    ‖𝔼 x, f x*conj (g x)‖ = ‖𝔼 x, g x*conj (f x)‖ := by
  calc
    _ = ‖conj (𝔼 x, f x*conj (g x))‖ := (Complex.norm_conj _).symm
    _ = _ := by
      rw [expect_conj]
      congr 1
      apply expect_congr rfl
      intro x _
      rw [map_mul, starRingEnd_self_apply, mul_comm]

/-- If unit phases avoid 1, a small positive power has a large mean. -/
theorem avoidance_frequency {X : Type*} [Fintype X] [Nonempty X]
    (q : X → ℂ) (hq : ∀ x, ‖q x‖ = 1) {ε : ℝ} (hε : 0 < ε)
    (havoid : ∀ x, ε ≤ ‖q x-1‖) {K : ℕ} (hK : 0 < K)
    (hscale : 8 ≤ (K : ℝ)*ε^2) :
    ∃ k : ℕ, 0 < k ∧ k < K ∧ 1/(4*(K : ℝ)) < ‖𝔼 x, (q x)^k‖ := by
  letI : NeZero K := ⟨by omega⟩
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hden : 0 < (K : ℝ)*ε := mul_pos hKr hε
  have hgeo (x : X) : ‖𝔼 j : Fin K, (q x)^j.val‖ ≤ 2/((K : ℝ)*ε) := by
    have hmul : ‖𝔼 j : Fin K, (q x)^j.val‖*ε ≤ 2/(K : ℝ) :=
      (mul_le_mul_of_nonneg_left (havoid x) (norm_nonneg _)).trans
        (geometric_mean_norm (q x) (hq x) K)
    calc
      _ ≤ (2/(K : ℝ))/ε := (le_div_iff₀ hε).mpr hmul
      _ = _ := by ring
  have hnum : (2/((K : ℝ)*ε))^2 ≤ 1/(2*(K : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(K : ℝ))).mpr
    have hh : (2/((K : ℝ)*ε))^2*(2*(K : ℝ)) =
        8/((K : ℝ)*ε^2) := by field_simp; ring
    rw [hh]
    exact (div_le_one (by positivity)).mpr hscale
  have heupper : (𝔼 x, ‖𝔼 j : Fin K, (q x)^j.val‖^2) ≤ 1/(2*(K : ℝ)) := by
    apply expect_le univ_nonempty
    intro x _
    exact (pow_le_pow_left₀ (norm_nonneg _) (hgeo x) 2).trans hnum
  by_contra hn
  push_neg at hn
  have hpair (i j : Fin K) (hij : i ≠ j) :
      ‖𝔼 x, (q x)^i.val*conj ((q x)^j.val)‖ ≤ 1/(4*(K : ℝ)) := by
    have hordered (i j : Fin K) (hji : j.val < i.val) :
        ‖𝔼 x, (q x)^i.val*conj ((q x)^j.val)‖ ≤ 1/(4*(K : ℝ)) := by
      simp_rw [unit_power_pair _ (hq _) hji.le]
      exact hn (i.val-j.val) (by omega) (by omega)
    rcases lt_trichotomy j.val i.val with h|h|h
    · exact hordered i j h
    · exact (hij (Fin.ext h.symm)).elim
    · rw [norm_pair_swap]
      exact hordered j i h
  have hlower := (pair_energy_bounds (fun x (j : Fin K) ↦ (q x)^j.val)
    (fun x j ↦ by rw [norm_pow, hq, one_pow])
    (by positivity : 0 ≤ 1/(4*(K : ℝ))) hpair).1
  rw [Fintype.card_fin] at hlower
  have hstrict : 1/(2*(K : ℝ)) < 1/(K : ℝ)-1/(4*(K : ℝ)) := by
    field_simp
    nlinarith
  linarith

/-- A large interval mean forces a large off-diagonal short-shift correlation. -/
theorem short_shift_correlation (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ = 1)
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) {δ : ℝ} (hδ : 0 < δ)
    (hmean : δ ≤ ‖intervalMean N f‖)
    (hshift : 2*(H : ℝ)/(N : ℝ) ≤ δ/2)
    (hdiag : 1/(H : ℝ) ≤ δ^2/8) :
    ∃ i j : Fin H, i ≠ j ∧ δ^2/16 <
      ‖𝔼 n : Fin N, f (n.val+i.val)*conj (f (n.val+j.val))‖ := by
  letI : NeZero N := ⟨by omega⟩
  letI : NeZero H := ⟨by omega⟩
  let a : ℂ := 𝔼 h : Fin H, intervalMean N (fun n ↦ f (n+h.val))
  have ha : δ/2 ≤ ‖a‖ := by
    have hd := averaged_shift_bound f (fun n ↦ (hf n).le) N H hH
    have ht : ‖intervalMean N f‖ ≤ ‖a‖+‖a-intervalMean N f‖ := by
      calc
        _ = ‖a-(a-intervalMean N f)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    change ‖a-intervalMean N f‖ ≤ _ at hd
    linarith
  have henergy : δ^2/4 ≤ 𝔼 n : Fin N, ‖𝔼 h : Fin H, f (n.val+h.val)‖^2 := by
    have he : a = 𝔼 n : Fin N, 𝔼 h : Fin H, f (n.val+h.val) := by
      exact expect_comm _ _ _
    calc
      _ = (δ/2)^2 := by ring
      _ ≤ ‖a‖^2 := pow_le_pow_left₀ (by positivity) ha 2
      _ ≤ _ := by rw [he]; exact norm_mean_sq_le _
  by_contra hn
  push_neg at hn
  have hu := (pair_energy_bounds (fun (n : Fin N) (h : Fin H) ↦ f (n.val+h.val))
    (fun n h ↦ hf _) (by positivity : 0 ≤ δ^2/16) hn).2
  rw [Fintype.card_fin] at hu
  have hpos : 0 < δ^2 := sq_pos_of_pos hδ
  linarith

#print axioms avoidance_frequency
#print axioms short_shift_correlation
end Erdos3QuadraticRecurrenceExtraction
