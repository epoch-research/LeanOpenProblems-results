import Submission.MixedComplementRectangle

/-! The separated factor-pair sum counts each complementary divisor exactly
once; its support is an explicit subset of the original radical divisors. -/
namespace Erdos371
open Finset FiniteSieve

lemma small_high_factor_unique (W m f f' g g' : ℕ)
    (hf : 0 < f) (hf' : 0 < f') (hfW : f ≤ W) (hfW' : f' ≤ W)
    (hg : g ∣ roughRadical W m) (hg' : g' ∣ roughRadical W m)
    (he : f*g=f'*g') : f=f' ∧ g=g' := by
  have hff : f=f' := by
    apply Nat.dvd_antisymm
    · apply (small_high_coprime W m f g' hf hfW hg').dvd_of_dvd_mul_right
      rw [← he]
      exact Nat.dvd_mul_right _ _
    · apply (small_high_coprime W m f' g hf' hfW' hg).dvd_of_dvd_mul_right
      rw [he]
      exact Nat.dvd_mul_right _ _
  refine ⟨hff,?_⟩
  exact Nat.eq_of_mul_eq_mul_left hf (by simpa only [← hff] using he)

noncomputable def mixedComplementPairs (B W F X n : ℕ) : Finset (ℕ × ℕ) :=
  ((roughRadical B (n*(n+1))).divisors.filter (fun f => f ≤ F)) ×ˢ
    ((roughRadical W (n*(n+1))).divisors.filter (fun g => 1 < g ∧ g ≤ X))

noncomputable def mixedComplementSupport (B W F X n : ℕ) : Finset ℕ :=
  (mixedComplementPairs B W F X n).image (fun fg => fg.1*fg.2)

lemma mixedComplementPairs_inj (B W F X n : ℕ) (hF : F ≤ W) :
    Set.InjOn (fun fg : ℕ × ℕ => fg.1*fg.2) (mixedComplementPairs B W F X n) := by
  intro fg hfg fg' hfg' he
  obtain ⟨hf,hg⟩ := mem_product.mp hfg
  obtain ⟨hf',hg'⟩ := mem_product.mp hfg'
  obtain ⟨hfd,hfF⟩ := mem_filter.mp hf
  obtain ⟨hfd',hfF'⟩ := mem_filter.mp hf'
  have hgd := (Nat.mem_divisors.mp (mem_filter.mp hg).1).1
  have hgd' := (Nat.mem_divisors.mp (mem_filter.mp hg').1).1
  have hpos := roughRadical_pos B (n*(n+1))
  obtain ⟨h1,h2⟩ := small_high_factor_unique W _ fg.1 fg'.1 fg.2 fg'.2
    (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hfd).1 hpos)
    (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hfd').1 hpos)
    (hfF.trans hF) (hfF'.trans hF) hgd hgd' he
  exact Prod.ext h1 h2

lemma mixedComplementSupport_subset (B W F X n : ℕ) (hBW : B ≤ W) (hF : F ≤ W) :
    mixedComplementSupport B W F X n ⊆ (roughRadical B (n*(n+1))).divisors := by
  intro e he
  obtain ⟨fg,hfg,rfl⟩ := mem_image.mp he
  obtain ⟨hf,hg⟩ := mem_product.mp hfg
  obtain ⟨hfd,hfF⟩ := mem_filter.mp hf
  have hgd := (Nat.mem_divisors.mp (mem_filter.mp hg).1).1
  have hfd := (Nat.mem_divisors.mp hfd).1
  have hpos := roughRadical_pos B (n*(n+1))
  have hcop := small_high_coprime W _ fg.1 fg.2 (Nat.pos_of_dvd_of_pos hfd hpos) (hfF.trans hF) hgd
  exact Nat.mem_divisors.mpr ⟨hcop.mul_dvd_of_dvd_of_dvd hfd
    (hgd.trans (roughRadical_dvd_of_le B W _ hBW)),hpos.ne'⟩

/-- No multiplicities are introduced by the mixed factorization. -/
lemma mixedComplementRectangleAt_original_support (B D W F X n : ℕ)
    (hBW : B ≤ W) (hF : F ≤ W) :
    mixedComplementRectangleAt B D W F X n=
      (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
        ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
          if e ∈ mixedComplementSupport B W F X n ∧ D*e < roughRadical B (n*(n+1)) then
            (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e)
          else 0 := by
  let V : ℕ → ℝ := fun e => if D*e < roughRadical B (n*(n+1)) then
    (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e) else 0
  have hsum : (∑ f ∈ (roughRadical B (n*(n+1))).divisors,
      ∑ g ∈ (roughRadical W (n*(n+1))).divisors,
        if f ≤ F ∧ 1 < g ∧ g ≤ X ∧ D*(f*g) < roughRadical B (n*(n+1)) then
          (ArithmeticFunction.moebius (f*g) : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/(f*g)) else 0)=
      ∑ fg ∈ mixedComplementPairs B W F X n, V (fg.1*fg.2) := by
    simp only [mixedComplementPairs,sum_product,sum_filter,V]
    apply sum_congr rfl
    intro f _
    by_cases hf : f ≤ F
    · simp only [hf,true_and,if_true]
      apply sum_congr rfl
      intro g _
      by_cases hg : 1 < g ∧ g ≤ X
      · simp [hg.1,hg.2]
      · have hnot : ¬(1 < g ∧ g ≤ X ∧ D*(f*g) < roughRadical B (n*(n+1))) :=
          fun h => hg ⟨h.1,h.2.1⟩
        simp only [hg,hnot,if_false]
    · simp [hf]
  have himg : (∑ fg ∈ mixedComplementPairs B W F X n, V (fg.1*fg.2))=
      ∑ e ∈ mixedComplementSupport B W F X n, V e := by
    symm
    apply sum_image
    exact mixedComplementPairs_inj B W F X n hF
  have hfilter : (roughRadical B (n*(n+1))).divisors.filter
      (fun e => e ∈ mixedComplementSupport B W F X n)=mixedComplementSupport B W F X n := by
    ext e
    simp only [mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨mixedComplementSupport_subset B W F X n hBW hF h,h⟩⟩
  unfold mixedComplementRectangleAt
  rw [hsum,himg]
  congr 1
  rw [← hfilter,sum_filter]
  apply sum_congr rfl
  intro e hd
  dsimp only [V]
  by_cases he : e ∈ mixedComplementSupport B W F X n <;> simp [he,Nat.mem_divisors.mp hd]

lemma mixedComplementRectangleAt_one (B D W X n : ℕ) :
    mixedComplementRectangleAt B D W 1 X n=highComplementAt B D W X n := by
  unfold mixedComplementRectangleAt highComplementAt
  congr 1
  rw [sum_eq_single 1]
  · simp only [le_refl,true_and,one_mul]
  · intro f hf hf1
    have hp := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hf).1 (roughRadical_pos B (n*(n+1)))
    have hnot : ¬f ≤ 1 := by omega
    simp only [hnot,false_and,if_false,sum_const_zero]
  · intro h
    exact False.elim (h (Nat.one_mem_divisors.mpr (roughRadical_pos B (n*(n+1))).ne'))

#print axioms mixedComplementRectangleAt_original_support
end Erdos371
