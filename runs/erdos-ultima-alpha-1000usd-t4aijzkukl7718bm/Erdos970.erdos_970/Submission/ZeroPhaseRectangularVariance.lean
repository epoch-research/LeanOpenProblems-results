import Submission.RectangularVarianceTransfer

/-! Exact zero-phase identities. Rough-number counts at the two rectangle
scales supply a lower, not an upper, bound on the row variance. -/
namespace Erdos970.GapAverages
open Finset Real

noncomputable def zeroPhase (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) : Phase P :=
  fun q => ⟨0, (hP q.val q.property).pos⟩

lemma affine_zeroPhase (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (p : ℕ) (hc : ∀ q ∈ P, p.Coprime q) :
    affinePhaseEquiv P hP 0 p hc (zeroPhase P hP) = zeroPhase P hP := by
  funext q
  apply Fin.ext
  simp [affinePhaseEquiv_val, zeroPhase]

lemma point_zeroPhase (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (x : ℕ) :
    point P x (zeroPhase P hP) = if ∀ q ∈ P, ¬q ∣ x then 1 else 0 := by
  classical
  rw [CoverFibers.point_eq_avoidance_indicator]
  have he : (∀ q : P, x % q.val ≠ ((zeroPhase P hP) q).val) ↔
      ∀ q ∈ P, ¬q ∣ x := by
    simp only [zeroPhase, ne_eq, Nat.dvd_iff_mod_eq_zero, Subtype.forall]
  simp only [he]

noncomputable def roughCount (P : Finset ℕ) (m : ℕ) : ℝ :=
  (((range m).filter (fun x => ∀ q ∈ P, ¬q ∣ x)).card : ℝ)

lemma intervalCount_zeroPhase (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (m : ℕ) :
    intervalCount P m (zeroPhase P hP) = roughCount P m := by
  simp only [intervalCount, point_zeroPhase, sum_boole, roughCount]

lemma row_zeroPhase_rectangle (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (n p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) :
    rowCount P (p * n) p ⟨0, hp⟩ (zeroPhase P hP) = roughCount P n := by
  have hh := row_zero_affine_rectangle P hP n p hp hc (zeroPhase P hP)
  rw [affine_zeroPhase, intervalCount_zeroPhase] at hh
  exact hh

/-- Any discrepancy between the two rough-number densities contributes to
conditional row variance, even if both counts are large and positive. -/
theorem roughCount_gap_square_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (n p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) :
    (roughCount P n - roughCount P (p * n) / p) ^ 2 ≤
      (p : ℝ) * rowConditionalVariance P (p * n) p (zeroPhase P hP) := by
  have hh := row_deviation_square_le P (p * n) p hp (zeroPhase P hP) ⟨0, hp⟩
  rwa [row_zeroPhase_rectangle P hP n p hp hc, intervalCount_zeroPhase] at hh

lemma rough_below_square_iff (p x : ℕ) (hp : 2 < p) (hx : x < p ^ 2) :
    (∀ q ∈ p.primesBelow, ¬q ∣ x) ↔ x = 1 ∨ (x.Prime ∧ p ≤ x) := by
  constructor
  · intro hs
    have hxpos : 0 < x := by
      by_contra h
      have hx0 : x = 0 := by omega
      exact hs 2 (Nat.mem_primesBelow.mpr ⟨hp, Nat.prime_two⟩) (hx0 ▸ dvd_zero 2)
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      have hprime : x.Prime := by
        by_contra hn
        have hq := Nat.minFac_prime hx1
        have hsq := Nat.minFac_sq_le_self hxpos hn
        have hlt : x.minFac < p := by nlinarith
        exact hs x.minFac (Nat.mem_primesBelow.mpr ⟨hlt, hq⟩) (Nat.minFac_dvd x)
      refine ⟨hprime, ?_⟩
      by_contra hlt
      exact hs x (Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩) (dvd_refl x)
  · rintro (rfl | ⟨hxprime, hpx⟩) q hq hd
    · exact (Nat.prime_of_mem_primesBelow hq).not_dvd_one hd
    · rcases (Nat.dvd_prime hxprime).mp hd with h1 | he
      · exact (Nat.prime_of_mem_primesBelow hq).ne_one h1
      · have hh := Nat.lt_of_mem_primesBelow hq
        omega

/-- Below the square of a prime cutoff, zero-phase survivors are exactly one
and the primes above the cutoff. The interval here is [0,m), not [1,m]. -/
theorem roughCount_primesBelow_eq (p m : ℕ) (hp : 2 < p)
    (hpm : p ≤ m) (hmp : m ≤ p ^ 2) :
    roughCount p.primesBelow m = (m.primeCounting' : ℝ) - p.primeCounting' + 1 := by
  classical
  have hs : (range m).filter (fun x => ∀ q ∈ p.primesBelow, ¬q ∣ x) =
      insert 1 (m.primesBelow \ p.primesBelow) := by
    ext x
    simp only [mem_filter, mem_range, mem_insert, mem_sdiff]
    constructor
    · rintro ⟨hxm, hx⟩
      rcases (rough_below_square_iff p x hp (hxm.trans_le hmp)).mp hx with h1 | ⟨hpr, hpx⟩
      · exact Or.inl h1
      · exact Or.inr ⟨Nat.mem_primesBelow.mpr ⟨hxm, hpr⟩,
          fun hh => (Nat.lt_of_mem_primesBelow hh).not_ge hpx⟩
    · rintro (rfl | ⟨hxm', hn⟩)
      · refine ⟨by omega, ?_⟩
        exact (rough_below_square_iff p 1 hp (by nlinarith)).mpr (Or.inl rfl)
      · obtain ⟨hxm, hpr⟩ := Nat.mem_primesBelow.mp hxm'
        refine ⟨hxm, ?_⟩
        apply (rough_below_square_iff p x hp (hxm.trans_le hmp)).mpr
        exact Or.inr ⟨hpr, le_of_not_gt (fun hh => hn (Nat.mem_primesBelow.mpr ⟨hh, hpr⟩))⟩
  have h1 : 1 ∉ m.primesBelow \ p.primesBelow := by
    intro hh
    exact (by decide : ¬Nat.Prime 1) (Nat.prime_of_mem_primesBelow (mem_sdiff.mp hh).1)
  have hsub : p.primesBelow ⊆ m.primesBelow := by
    intro q hq
    obtain ⟨hqp, hpr⟩ := Nat.mem_primesBelow.mp hq
    exact Nat.mem_primesBelow.mpr ⟨hqp.trans_le hpm, hpr⟩
  rw [roughCount, hs, card_insert_of_notMem h1, card_sdiff_of_subset hsub,
    Nat.primesBelow_card_eq_primeCounting', Nat.primesBelow_card_eq_primeCounting',
    Nat.cast_add, Nat.cast_sub (Nat.monotone_primeCounting' hpm), Nat.cast_one]

#print axioms roughCount_gap_square_le
#print axioms roughCount_primesBelow_eq
end Erdos970.GapAverages
