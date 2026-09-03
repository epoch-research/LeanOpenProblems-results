import FormalConjecturesUtil

/-!
Uniform discrepancy for arbitrary periodic conditions on a two-dimensional
integer box. This is a counting lemma, with no Sidon conclusion.
-/
namespace Erdos1206.PeriodicBoxCount
open Finset
open scoped Classical

noncomputable def rowCount (N d r : ℕ) : ℕ := ((range N).filter (fun n => n%d=r)).card
noncomputable def boxCount (N d : ℕ) (B : Finset (ℕ × ℕ)) : ℕ :=
  (((range N) ×ˢ (range N)).filter (fun x => (x.1%d,x.2%d) ∈ B)).card

lemma rowCount_bounds (N d r : ℕ) (hd : 0 < d) (hr : r < d) :
    N/d ≤ rowCount N d r ∧ rowCount N d r ≤ N/d+1 := by
  have he : ((range N).filter (fun n => n%d=r)) =
      ((range N).filter (fun n => Nat.ModEq d n r)) := by
    ext n
    simp only [mem_filter,Nat.ModEq,Nat.mod_eq_of_lt hr]
  rw [rowCount,he,← Nat.count_eq_card_filter_range,Nat.count_modEq_card N hd r]
  split_ifs <;> omega

lemma boxCount_eq (N d : ℕ) (B : Finset (ℕ × ℕ)) :
    boxCount N d B = ∑ r ∈ B, rowCount N d r.1*rowCount N d r.2 := by
  rw [boxCount,← sum_card_fiberwise_eq_card_filter]
  apply sum_congr rfl
  intro r hr
  have he : (((range N) ×ˢ (range N)).filter (fun x => (x.1%d,x.2%d)=r)) =
      ((range N).filter (fun n => n%d=r.1)) ×ˢ
        ((range N).filter (fun n => n%d=r.2)) := by
    ext x
    simp only [mem_filter,mem_product]
    aesop
  rw [he,card_product]
  rfl

lemma row_product_discrepancy (N d a b : ℕ) (hd : 0 < d) (ha : a < d) (hb : b < d) :
    |((rowCount N d a*rowCount N d b : ℕ):ℝ)-((N:ℝ)/d)^2| ≤ 2*((N:ℝ)/d)+1 := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  obtain ⟨haL,haU⟩ := rowCount_bounds N d a hd ha
  obtain ⟨hbL,hbU⟩ := rowCount_bounds N d b hd hb
  have hlo : ((N/d:ℕ):ℝ)^2 ≤ ((rowCount N d a*rowCount N d b : ℕ):ℝ) := by
    exact_mod_cast (show (N/d)^2 ≤ rowCount N d a*rowCount N d b from by
      simpa only [pow_two] using Nat.mul_le_mul haL hbL)
  have hhi : ((rowCount N d a*rowCount N d b : ℕ):ℝ) ≤ (((N/d:ℕ):ℝ)+1)^2 := by
    exact_mod_cast (show rowCount N d a*rowCount N d b ≤ (N/d+1)^2 from by
      simpa only [pow_two] using Nat.mul_le_mul haU hbU)
  have hq : ((N/d:ℕ):ℝ) ≤ (N:ℝ)/d := Nat.cast_div_le
  have hQ : (N:ℝ)/d ≤ ((N/d:ℕ):ℝ)+1 := by
    apply (div_le_iff₀ hdR).mpr
    have hh : (N:ℝ) < (d:ℝ)*(((N/d:ℕ):ℝ)+1) := by exact_mod_cast Nat.lt_mul_div_succ N hd
    nlinarith only [hh]
  have hq0 : (0:ℝ) ≤ (N/d:ℕ) := Nat.cast_nonneg _
  have hq2 := pow_le_pow_left₀ hq0 hq 2
  have hQ2 := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg N) hdR.le) hQ 2
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The error depends on the modulus itself, not on the number or shape of
allowed residue classes. It is valid at every box size N. -/
theorem boxCount_discrepancy (N d : ℕ) (B : Finset (ℕ × ℕ))
    (hd : 0 < d) (hB : B ⊆ (range d) ×ˢ (range d)) :
    |(boxCount N d B:ℝ)-(N:ℝ)^2*(B.card:ℝ)/(d:ℝ)^2| ≤
      2*(N:ℝ)*d+(d:ℝ)^2 := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hbc : (B.card:ℝ) ≤ (d:ℝ)^2 := by
    have hh := card_le_card hB
    simpa only [card_product,card_range,pow_two,Nat.cast_mul] using (show (B.card:ℝ) ≤ (((range d) ×ˢ (range d)).card:ℝ) from by exact_mod_cast hh)
  have hnonneg : 0 ≤ 2*((N:ℝ)/d)+1 := by positivity
  have he : (boxCount N d B:ℝ)-(N:ℝ)^2*(B.card:ℝ)/(d:ℝ)^2 =
      ∑ r ∈ B, (((rowCount N d r.1*rowCount N d r.2:ℕ):ℝ)-((N:ℝ)/d)^2) := by
    rw [boxCount_eq,Nat.cast_sum,sum_sub_distrib,sum_const,nsmul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ ∑ r ∈ B, |((rowCount N d r.1*rowCount N d r.2:ℕ):ℝ)-((N:ℝ)/d)^2| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ B, (2*((N:ℝ)/d)+1) := by
      apply sum_le_sum
      intro r hr
      obtain ⟨ha,hb⟩ := mem_product.mp (hB hr)
      exact row_product_discrepancy N d r.1 r.2 hd (mem_range.mp ha) (mem_range.mp hb)
    _ = (B.card:ℝ)*(2*((N:ℝ)/d)+1) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (d:ℝ)^2*(2*((N:ℝ)/d)+1) := mul_le_mul_of_nonneg_right hbc hnonneg
    _ = _ := by field_simp

#print axioms rowCount_bounds
#print axioms boxCount_discrepancy
end Erdos1206.PeriodicBoxCount
