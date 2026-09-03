import FormalConjecturesUtil

/-! Exact recurrences for some quadratic slopes. These do not settle Erdős 972. -/
namespace Erdos972QuadraticRecurrence

lemma floor_quadratic_recurrence {α : ℝ} {k : ℕ}
    (hα : 1 < α) (hk : 2 ≤ k) (hpoly : α ^ 2 + 1 = (k : ℝ) * α)
    (n : ℕ) :
    ⌊α * (⌊α * n⌋₊ : ℕ)⌋₊ + n = k * ⌊α * n⌋₊ := by
  let q := ⌊α * n⌋₊
  have hα0 : 0 < α := by linarith
  have hqn : n ≤ q := Nat.le_floor (by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith)
  have hnkq : n ≤ k * q := hqn.trans (by
    calc q = 1 * q := (one_mul q).symm
         _ ≤ k * q := Nat.mul_le_mul_right q (by omega))
  let m := k * q - n
  have hmn : m + n = k * q := Nat.sub_add_cancel hnkq
  have hm : (m : ℝ) = (k : ℝ) * q - n := by
    have h := congrArg (fun j : ℕ => (j : ℝ)) hmn
    push_cast at h
    linarith
  have hqlo : (q : ℝ) ≤ α * n := Nat.floor_le (by positivity)
  have hqhi : α * n < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have he : α * (α * (q : ℝ) - m) = α * n - q := by
    rw [hm]
    have h := congrArg (fun x : ℝ => x * (q : ℝ)) hpoly
    nlinarith
  have hlo : (m : ℝ) ≤ α * q := by
    have h : 0 ≤ α * (α * (q : ℝ) - m) := by rw [he]; linarith
    have h' := (mul_nonneg_iff_of_pos_left hα0).mp h
    linarith
  have hhi : α * (q : ℝ) < m + 1 := by
    have h : α * (α * (q : ℝ) - m) < α * 1 := by rw [he]; linarith
    have h' := (mul_lt_mul_iff_right₀ hα0).mp h
    linarith
  have hf : ⌊α * (q : ℝ)⌋₊ = m :=
    (Nat.floor_eq_iff (by positivity)).mpr ⟨hlo, hhi⟩
  change ⌊α * (q : ℝ)⌋₊ + n = k * q
  rw [hf]
  exact hmn

/-- For odd k, two successive prime values above two force the third value
not to be prime. This is not a finiteness assertion about the prime pairs. -/
theorem no_three_successive_primes {α : ℝ} {k p : ℕ}
    (hα : 1 < α) (hk : 2 ≤ k) (hpoly : α ^ 2 + 1 = (k : ℝ) * α)
    (hkodd : Odd k) (hp : p.Prime) (hp2 : 2 < p)
    (hq : (⌊α * p⌋₊).Prime) :
    ¬ (⌊α * (⌊α * p⌋₊ : ℕ)⌋₊).Prime := by
  intro hr
  have hpq : p ≤ ⌊α * p⌋₊ := Nat.le_floor (by
    have hn : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith)
  have hqr : ⌊α * p⌋₊ ≤ ⌊α * (⌊α * p⌋₊ : ℕ)⌋₊ := Nat.le_floor (by
    have hn : (0 : ℝ) ≤ (⌊α * p⌋₊ : ℕ) := Nat.cast_nonneg _
    nlinarith)
  have hpo := hp.odd_of_ne_two (by omega)
  have hqo := hq.odd_of_ne_two (by omega)
  have hro := hr.odd_of_ne_two (by omega)
  have he := hro.add_odd hpo
  rw [floor_quadratic_recurrence hα hk hpoly] at he
  have ho := Nat.odd_iff.mp (hkodd.mul hqo)
  have hev := Nat.even_iff.mp he
  omega

#print axioms floor_quadratic_recurrence
#print axioms no_three_successive_primes

end Erdos972QuadraticRecurrence
