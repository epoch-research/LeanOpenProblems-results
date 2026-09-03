import Submission.ThreePrimePatternSieve

/-! Elementary cofactor sums for the dimension-three incidence sieve. -/
namespace Erdos371.FiniteSieve
open Finset

lemma lcm_eq_gcd_times_quotients (a b : ℕ) (ha : 0<a) :
    a.lcm b=a.gcd b*(a/a.gcd b)*(b/a.gcd b) := by
  have hg := Nat.gcd_pos_of_pos_left b ha
  have he₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have he₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc
    _ = a*b := Nat.gcd_mul_lcm a b
    _ = a.gcd b*(a.gcd b*(a/a.gcd b)*(b/a.gcd b)) := by
      calc
        a*b = (a.gcd b*(a/a.gcd b))*(a.gcd b*(b/a.gcd b)) := congrArg₂ Nat.mul he₁.symm he₂.symm
        _ = _ := by ring

/-- The gcd/quotient coordinates inject into a three-dimensional box,
and the reciprocal lcm becomes the product of the three reciprocals. -/
theorem sum_reciprocal_lcm_le_harmonic_cube (X : ℕ) :
    (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, (1 : ℝ)/(a.lcm b)) ≤ (harmonic X : ℝ)^3 := by
  let f : ℕ × ℕ → ℕ × ℕ × ℕ := fun ab =>
    (ab.1.gcd ab.2,ab.1/(ab.1.gcd ab.2),ab.2/(ab.1.gcd ab.2))
  let w : ℕ × ℕ × ℕ → ℝ := fun t => (1 : ℝ)/t.1*(1/t.2.1)*(1/t.2.2)
  let S := Icc 1 X ×ˢ Icc 1 X
  let T := Icc 1 X ×ˢ (Icc 1 X ×ˢ Icc 1 X)
  have hrecon (ab : ℕ × ℕ) : ((f ab).1*(f ab).2.1,(f ab).1*(f ab).2.2)=ab := by
    dsimp only [f]
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left ab.1 ab.2),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right ab.1 ab.2)]
  have hinj : Function.Injective f := by
    intro ab cd he
    have hh := congrArg (fun t : ℕ × ℕ × ℕ => (t.1*t.2.1,t.1*t.2.2)) he
    simpa only [hrecon] using hh
  have hmap : S.image f ⊆ T := by
    intro t ht
    obtain ⟨ab,hab,rfl⟩ := mem_image.mp ht
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    obtain ⟨ha0,haX⟩ := mem_Icc.mp ha
    obtain ⟨hb0,hbX⟩ := mem_Icc.mp hb
    have hg := Nat.gcd_pos_of_pos_left ab.2 ha0
    have hga := Nat.gcd_le_left ab.2 ha0
    have hgb := Nat.gcd_le_right ab.1 hb0
    refine mem_product.mpr ⟨mem_Icc.mpr ⟨hg,hga.trans haX⟩,
      mem_product.mpr ⟨mem_Icc.mpr ⟨Nat.div_pos hga hg,(Nat.div_le_self _ _).trans haX⟩,
        mem_Icc.mpr ⟨Nat.div_pos hgb hg,(Nat.div_le_self _ _).trans hbX⟩⟩⟩
  have hrow (ab : ℕ × ℕ) (hab : ab ∈ S) : (1 : ℝ)/(ab.1.lcm ab.2)=w (f ab) := by
    have ha := (mem_Icc.mp (mem_product.mp hab).1).1
    rw [lcm_eq_gcd_times_quotients ab.1 ab.2 ha]
    dsimp only [w,f]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
    ring
  calc
    _ = ∑ ab ∈ S, (1 : ℝ)/(ab.1.lcm ab.2) := (sum_product _ _ _).symm
    _ = ∑ ab ∈ S, w (f ab) := sum_congr rfl hrow
    _ = ∑ t ∈ S.image f, w t := (sum_image (fun _ _ _ _ he => hinj he)).symm
    _ ≤ ∑ t ∈ T, w t := sum_le_sum_of_subset_of_nonneg hmap (by intros; dsimp [w]; positivity)
    _ = (∑ a ∈ Icc 1 X, (1 : ℝ)/a)^3 := by
      simp only [T,w,sum_product,← mul_sum,← sum_mul]
      ring
    _ = _ := by
      congr 1
      simp [harmonic_eq_sum_Icc,one_div]

lemma sum_reciprocal_max_le (X : ℕ) :
    (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, (1 : ℝ)/(max a b : ℕ)) ≤ 2*X := by
  have hrow (a : ℕ) (ha : a ∈ Icc 1 X) :
      (∑ b ∈ Icc 1 X, if b≤a then (1 : ℝ)/a else 0)=1 := by
    rw [← sum_filter]
    have he : (Icc 1 X).filter (· ≤ a)=Icc 1 a := by
      ext b
      simp only [mem_filter,mem_Icc]
      have := (mem_Icc.mp ha).2
      omega
    rw [he,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by have := (mem_Icc.mp ha).1; omega : a ≠ 0)
    field_simp
  have hpoint (a b : ℕ) : (1 : ℝ)/(max a b : ℕ) ≤
      (if b≤a then (1 : ℝ)/a else 0)+(if a≤b then (1 : ℝ)/b else 0) := by
    rcases le_total b a with h | h
    · rw [max_eq_left h,if_pos h]
      split_ifs <;> linarith [show (0 : ℝ) ≤ 1/(a : ℝ) by positivity, show (0 : ℝ) ≤ 1/(b : ℝ) by positivity]
    · rw [max_eq_right h,if_pos h]
      split_ifs <;> linarith [show (0 : ℝ) ≤ 1/(a : ℝ) by positivity, show (0 : ℝ) ≤ 1/(b : ℝ) by positivity]
  have hh := sum_le_sum (s := Icc 1 X) (fun a _ =>
    sum_le_sum (s := Icc 1 X) (fun b _ => hpoint a b))
  simp_rw [sum_add_distrib] at hh
  have h₁ : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, if b≤a then (1 : ℝ)/a else 0) = X := by
    rw [sum_congr rfl hrow]
    simp
  have h₂ : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, if a≤b then (1 : ℝ)/b else 0) = X := by
    rw [sum_comm]
    exact h₁
  rw [h₁,h₂] at hh
  linarith

#print axioms sum_reciprocal_lcm_le_harmonic_cube
#print axioms sum_reciprocal_max_le
end Erdos371.FiniteSieve
