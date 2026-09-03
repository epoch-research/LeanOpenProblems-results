import Submission.BeattyRows

/-! Common good scales for all the finitely many Beatty rows occurring in
fixed-cutoff Type-I sums. The row centers retain the actual Chebyshev function. -/
namespace Erdos972BeattyRowScales

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972WeightedPrimeRotation Erdos972RootScaleArc Erdos972BeattyRows

lemma mangoldtArcSum_nat_add (k : ℕ) (θ t a b : ℝ) (N : ℕ) :
    mangoldtArcSum ((k : ℝ)+θ) t a b N = mangoldtArcSum θ t a b N := by
  unfold mangoldtArcSum
  congr 1
  ext n
  have he : ((k : ℝ)+θ)*n+t = (θ*n+t)+(k*n : ℕ) := by push_cast; ring
  simp only [mem_filter, he, Int.fract_add_natCast]

lemma rowArcLeft_mono {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) : rowArcLeft α ≤ rowArcLeft β := by
  have hh := one_div_le_one_div_of_le hα hαβ
  unfold rowArcLeft
  linarith

lemma factorial_frequency {α : ℝ} (hα : 0 < α) (M m : ℕ) (hm : 0 < m) (hmM : m ≤ M) :
    ((M.factorial/m : ℕ) : ℝ)*(2+1/(α*M.factorial)) =
      ((2*(M.factorial/m) : ℕ) : ℝ)+1/(α*m) := by
  have hd : m ∣ M.factorial := Nat.dvd_factorial hm hmM
  have he : ((M.factorial/m : ℕ) : ℝ)*(m : ℝ) = M.factorial := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hD0 : (M.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)
  push_cast
  field_simp
  nlinarith

/-- Every fixed finite collection of Beatty rows has arbitrarily large common
scales with a uniform, logarithmically weighted error. The center is
`ψ(β L)/β`, rather than `L`, so this result requires no quantitative PNT. -/
theorem exists_common_beatty_row_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (M k : ℕ) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ ∀ m : ℕ, 0 < m → m ≤ M → ∀ L : ℕ,
      floorMul (α*m) L ≤ u^6 →
      |mangoldtRow (α*m) L - Chebyshev.psi ((α*m)*L)/(α*m)| * (1+Real.log u)^k ≤ ε*(u : ℝ)^6 := by
  let D := M.factorial
  let θ := 2+1/(α*D)
  have hα0 : 0 < α := by linarith
  have hD : 0 < D := Nat.factorial_pos M
  have hθ : 1 < θ := by
    have : 0 < 1/(α*D) := by positivity
    dsimp [θ]
    linarith
  have hθI : Irrational θ := by
    have hh := (hI.mul_natCast (Nat.ne_of_gt hD)).inv
    simpa only [θ, one_div] using hh.natCast_add 2
  have hη := (rowArcLeft_bounds hα).1
  obtain ⟨u, hu, hbound⟩ := exists_log_weighted_uniform_arc_scale hθ hθI D k hD (rowArcLeft α) hη hε B
  refine ⟨u, hu, ?_⟩
  intro m hm hmM L hL
  let j := D/m
  have hd : m ∣ D := Nat.dvd_factorial hm hmM
  have hj : 0 < j := Nat.div_pos (Nat.le_of_dvd hD hd) hm
  have hjD : j ≤ D := Nat.div_le_self _ _
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hβ : 1 < α*m := by nlinarith
  have hβI := hI.mul_natCast (Nat.ne_of_gt hm)
  have hαβ : α ≤ α*m := by nlinarith
  have hleft := rowArcLeft_mono hα0 hαβ
  have harc := rowArcLeft_bounds hβ
  have hh := hbound j hj hjD (rowArcLeft (α*m)) (1-rowArcLeft (α*m)) (by linarith)
    hleft (by linarith) (-rowArcLeft (α*m)) (floorMul (α*m) L) hL
  have hfreq : (j : ℝ)*θ = ((2*j : ℕ) : ℝ)+1/(α*m) := factorial_frequency hα0 M m hm hmM
  rw [hfreq, mangoldtArcSum_nat_add, ← mangoldtRow_eq_arc hβ hβI L] at hh
  have hwidth : (1-rowArcLeft (α*m))-rowArcLeft (α*m) = 1/(α*m) := by unfold rowArcLeft; ring
  have hpsi : Chebyshev.psi (floorMul (α*m) L) = Chebyshev.psi ((α*m)*L) := by
    simp only [Chebyshev.psi, Nat.floor_natCast, floorMul]
  simpa only [hwidth, hpsi, one_div_mul_eq_div] using hh

#print axioms factorial_frequency
#print axioms exists_common_beatty_row_scale

end Erdos972BeattyRowScales
