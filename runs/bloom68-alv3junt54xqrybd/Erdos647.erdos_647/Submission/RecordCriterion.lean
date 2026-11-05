import Submission.Structural

/-!
Exact whole-prefix record reformulation. These results do not assert the
existence or nonexistence of a large record satisfying the required prime heads.
-/

namespace Erdos647Record

open scoped ArithmeticFunction.sigma

/-- A weak record of the actual function `m ↦ m + τ(m)`. -/
def WeakRecord (r : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ r → m + σ 0 m ≤ r + σ 0 r

theorem sigma_double_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    σ 0 (2 * p) = 4 := by
  have hodd := hp.eq_two_or_odd.resolve_left hp2
  have hcop : Nat.Coprime 2 p :=
    Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd)
  have htwo : σ 0 2 = 2 := by
    simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) Nat.prime_two
  have hprime : σ 0 p = 2 := by
    simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hp
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, htwo, hprime]
  norm_num

theorem P_iff_prime_weak_record {n : ℕ} (hn : 24 < n) :
    Structural.P n ↔ ∃ p : ℕ, 11 < p ∧ p.Prime ∧ (2 * p + 1).Prime ∧
      n = 2 * p + 2 ∧ WeakRecord (2 * p) := by
  constructor
  · intro hP
    obtain ⟨p, hp, hp2, heq⟩ := Structural.sub_two_prime_form hP hn
    have hlast := Structural.prime_sub_one_of_P hP hn
    have hlast' : (2 * p + 1).Prime := by
      have he : n - 1 = 2 * p + 1 := by omega
      simpa only [he] using hlast
    refine ⟨p, by omega, hp, hlast', heq, ?_⟩
    intro m hm
    have hbound := hP m (by omega)
    rw [sigma_double_prime hp hp2]
    omega
  · rintro ⟨p, hp11, hp, hlast, rfl, hrecord⟩
    have hp2 : p ≠ 2 := by omega
    have hlast_count : σ 0 (2 * p + 1) = 2 := by
      simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hlast
    intro m hm
    by_cases hle : m ≤ 2 * p
    · have hbound := hrecord m hle
      rw [sigma_double_prime hp hp2] at hbound
      omega
    · have heq : m = 2 * p + 1 := by omega
      rw [heq, hlast_count]
      omega

theorem existence_iff_prime_weak_record :
    (∃ n > 24, (⨆ m : Fin n, (m : ℕ) + σ 0 (m : ℕ)) ≤ n + 2) ↔
    ∃ p : ℕ, 11 < p ∧ p.Prime ∧ (2 * p + 1).Prime ∧ WeakRecord (2 * p) := by
  constructor
  · rintro ⟨n, hn, hsup⟩
    have hP := (Structural.P_iff_iSup_le n).mpr hsup
    obtain ⟨p, hp11, hp, hlast, heq, hrecord⟩ :=
      (P_iff_prime_weak_record hn).mp hP
    exact ⟨p, hp11, hp, hlast, hrecord⟩
  · rintro ⟨p, hp11, hp, hlast, hrecord⟩
    have hn : 24 < 2 * p + 2 := by omega
    refine ⟨2 * p + 2, hn, ?_⟩
    apply (Structural.P_iff_iSup_le _).mp
    exact (P_iff_prime_weak_record hn).mpr ⟨p, hp11, hp, hlast, rfl, hrecord⟩

theorem grid_of_prime_weak_record {p : ℕ} (hp11 : 11 < p)
    (hp : p.Prime) (hlast : (2 * p + 1).Prime) (hrecord : WeakRecord (2 * p)) :
    180180 ∣ p + 1 := by
  have hn : 24 < 2 * p + 2 := by omega
  have hP := (P_iff_prime_weak_record hn).mpr ⟨p, hp11, hp, hlast, rfl, hrecord⟩
  obtain ⟨d, hd⟩ := Structural.base_dvd_of_P hP hn
  exact ⟨d, by omega⟩

/-- The exact strict improvement needed to defeat a candidate record. -/
theorem not_weak_record_iff_offset_witness {p : ℕ} (hp11 : 11 < p) (hp : p.Prime) :
    ¬ WeakRecord (2 * p) ↔
      ∃ h : ℕ, 0 < h ∧ h < 2 * p ∧ h + 5 ≤ σ 0 (2 * p - h) := by
  unfold WeakRecord
  rw [sigma_double_prime hp (by omega)]
  push_neg
  constructor
  · rintro ⟨m, hm, hbad⟩
    have hm0 : 0 < m := by
      by_contra hz
      have he : m = 0 := by omega
      subst m
      simp at hbad
    have hmlt : m < 2 * p := by
      by_contra hz
      have he : m = 2 * p := by omega
      rw [he, sigma_double_prime hp (by omega)] at hbad
      omega
    refine ⟨2 * p - m, by omega, by omega, ?_⟩
    have he : 2 * p - (2 * p - m) = m := by omega
    rw [he]
    omega
  · rintro ⟨h, hh0, hhp, hcount⟩
    refine ⟨2 * p - h, by omega, ?_⟩
    omega

/-- A logical reduction, not an assertion that the pointwise selector holds. -/
theorem disproof_iff_grid_offset_selector :
    (¬ (∃ n > 24, (⨆ m : Fin n, (m : ℕ) + σ 0 (m : ℕ)) ≤ n + 2)) ↔
    (∀ p : ℕ, 11 < p → p.Prime → (2 * p + 1).Prime →
      180180 ∣ p + 1 →
      ∃ h : ℕ, 0 < h ∧ h < 2 * p ∧ h + 5 ≤ σ 0 (2 * p - h)) := by
  rw [existence_iff_prime_weak_record]
  constructor
  · intro hnone p hp11 hp hlast _hgrid
    apply (not_weak_record_iff_offset_witness hp11 hp).mp
    intro hrecord
    exact hnone ⟨p, hp11, hp, hlast, hrecord⟩
  · intro selector hex
    obtain ⟨p, hp11, hp, hlast, hrecord⟩ := hex
    have hgrid := grid_of_prime_weak_record hp11 hp hlast hrecord
    exact (not_weak_record_iff_offset_witness hp11 hp).mpr
      (selector p hp11 hp hlast hgrid) hrecord

/-- A uniform divisor bound closes all but a finite suffix of the record test. -/
theorem weak_record_of_uniform_window {p B : ℕ} (hp11 : 11 < p) (hp : p.Prime)
    (hcount : ∀ m : ℕ, m < 2 * p → σ 0 m ≤ B)
    (hwindow : ∀ h : ℕ, 0 < h → h ≤ B - 5 → h < 2 * p →
      σ 0 (2 * p - h) ≤ h + 4) : WeakRecord (2 * p) := by
  by_contra hnot
  obtain ⟨h, hh0, hhp, hbad⟩ := (not_weak_record_iff_offset_witness hp11 hp).mp hnot
  have hupper := hcount (2 * p - h) (by omega)
  have hsize : h ≤ B - 5 := by omega
  have hcap := hwindow h hh0 hsize hhp
  omega

/-- Exact original supremum interface for a completely checked finite window. -/
theorem iSup_le_of_uniform_record_window {p B : ℕ} (hp11 : 11 < p) (hp : p.Prime)
    (hlast : (2 * p + 1).Prime)
    (hcount : ∀ m : ℕ, m < 2 * p → σ 0 m ≤ B)
    (hwindow : ∀ h : ℕ, 0 < h → h ≤ B - 5 → h < 2 * p →
      σ 0 (2 * p - h) ≤ h + 4) :
    (⨆ m : Fin (2 * p + 2), (m : ℕ) + σ 0 (m : ℕ)) ≤ 2 * p + 4 := by
  have hn : 24 < 2 * p + 2 := by omega
  have hrecord := weak_record_of_uniform_window hp11 hp hcount hwindow
  have hP := (P_iff_prime_weak_record hn).mpr ⟨p, hp11, hp, hlast, rfl, hrecord⟩
  simpa [Nat.add_assoc] using (Structural.P_iff_iSup_le _).mp hP

end Erdos647Record
