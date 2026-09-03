import FormalConjecturesUtil

/-! Exact reciprocal identities for a prime-pair floor interval. These do not
assert existence of prime pairs. In particular, reciprocal exchange gives a
ceiling index, not another floor prime pair. -/
namespace Erdos972ReciprocalPrimePairs

lemma reciprocal_window {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {n : ℕ} (hn : 0 < n) :
    (n - 1 : ℕ) < (⌊α * n⌋₊ : ℝ) / α ∧
      (⌊α * n⌋₊ : ℝ) / α < n := by
  have hα0 : 0 < α := by linarith
  have hN : 1 ≤ n := hn
  have hlo := Nat.lt_floor_add_one (α * n)
  have hhi : (⌊α * n⌋₊ : ℝ) < α * n :=
    lt_of_le_of_ne (Nat.floor_le (by positivity))
      ((hI.mul_natCast hn.ne').ne_nat _).symm
  constructor
  · apply (lt_div_iff₀ hα0).mpr
    rw [Nat.cast_sub hN, Nat.cast_one]
    nlinarith
  · exact (div_lt_iff₀ hα0).mpr (by simpa only [mul_comm] using hhi)

theorem reciprocal_floor_eq_pred {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {n : ℕ} (hn : 0 < n) :
    ⌊(⌊α * n⌋₊ : ℝ) / α⌋₊ = n - 1 := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hlo, hhi⟩ := reciprocal_window hα hI hn
  apply (Nat.floor_eq_iff (by positivity)).mpr
  refine ⟨hlo.le, ?_⟩
  simpa only [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel] using hhi

theorem reciprocal_ceil_eq {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {n : ℕ} (hn : 0 < n) :
    ⌈(⌊α * n⌋₊ : ℝ) / α⌉₊ = n := by
  obtain ⟨hlo, hhi⟩ := reciprocal_window hα hI hn
  exact (Nat.ceil_eq_iff hn.ne').mpr ⟨hlo, hhi.le⟩

/-- A prime input beyond three gives a composite reciprocal floor index,
even when the forward output happens to be prime. This is not a disproof:
the reciprocal slope is below one, and the assertion concerns only the
specific forward outputs, not all prime inputs at that slope. -/
theorem reciprocal_floor_not_prime {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ Nat.Prime ⌊(⌊α * p⌋₊ : ℝ) / α⌋₊ := by
  rw [reciprocal_floor_eq_pred hα hI hp.pos]
  intro hpred
  have he : Even (p - 1) := hp.even_sub_one (by omega)
  have htwo : p - 1 = 2 := hpred.even_iff.mp he
  omega

#print axioms reciprocal_floor_not_prime
#print axioms reciprocal_floor_eq_pred
#print axioms reciprocal_ceil_eq

end Erdos972ReciprocalPrimePairs
