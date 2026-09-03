import Submission.PeriodicBoxCount

/-! One-dimensional uniform discrepancy for a union of residue classes. -/
namespace Erdos1206.PeriodicResidueCounts
open Finset PeriodicBoxCount
open scoped Classical

noncomputable def count (N D : ℕ) (B : Finset ℕ) : ℕ :=
  ((range N).filter (fun n => n%D ∈ B)).card

lemma count_eq (N D : ℕ) (B : Finset ℕ) : count N D B=∑r∈B,rowCount N D r := by
  rw [count,←sum_card_fiberwise_eq_card_filter]
  rfl

lemma row_error (N D r : ℕ) (hD : 0 < D) (hr : r < D) :
    |(rowCount N D r:ℝ)-(N:ℝ)/D| ≤ 1 := by
  obtain ⟨hl,hu⟩ := rowCount_bounds N D r hD hr
  have hq : ((N/D:ℕ):ℝ) ≤ (N:ℝ)/D := Nat.cast_div_le
  have hQ : (N:ℝ)/D < (N/D:ℕ)+1 := by
    apply (div_lt_iff₀ (show (0:ℝ) < D by exact_mod_cast hD)).mpr
    exact_mod_cast (by simpa only [mul_comm] using Nat.lt_mul_div_succ N hD)
  have hlR : ((N/D:ℕ):ℝ) ≤ rowCount N D r := by exact_mod_cast hl
  have huR : (rowCount N D r:ℝ) ≤ (N/D:ℕ)+1 := by exact_mod_cast hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma discrepancy (N D : ℕ) (B : Finset ℕ) (hD : 0 < D) (hB : B ⊆ range D) :
    |(count N D B:ℝ)-(B.card:ℝ)*(N:ℝ)/D| ≤ D := by
  have he : (count N D B:ℝ)-(B.card:ℝ)*(N:ℝ)/D=
      ∑r∈B,((rowCount N D r:ℝ)-(N:ℝ)/D) := by
    rw [count_eq,Nat.cast_sum,sum_sub_distrib,sum_const,nsmul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ ∑r∈B,|(rowCount N D r:ℝ)-(N:ℝ)/D| := abs_sum_le_sum_abs _ _
    _ ≤ ∑_r∈B,(1:ℝ) := sum_le_sum (fun r hr => row_error N D r hD (mem_range.mp (hB hr)))
    _ = (B.card:ℝ) := by simp
    _ ≤ D := by exact_mod_cast (card_le_card hB).trans_eq (card_range D)

lemma prefix_lower (N D : ℕ) (B : Finset ℕ) (hD : 0 < D) (hB : B ⊆ range D)
    {δ : ℝ} (hδ : δ*D ≤ B.card) : δ*N ≤ (count N D B:ℝ)+D := by
  have hdR : (0:ℝ) < D := by exact_mod_cast hD
  have hh := (abs_le.mp (discrepancy N D B hD hB)).1
  have hc : δ ≤ (B.card:ℝ)/D := (le_div_iff₀ hdR).mpr hδ
  have hm := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)
  rw [div_mul_eq_mul_div] at hm
  linarith

#print axioms discrepancy
#print axioms prefix_lower
end Erdos1206.PeriodicResidueCounts
