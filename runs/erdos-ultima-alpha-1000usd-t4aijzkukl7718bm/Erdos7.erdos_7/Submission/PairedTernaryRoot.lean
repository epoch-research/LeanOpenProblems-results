import Submission.IndependentLiftSampling
import Submission.RetainedRealCompression

/-! Initial average-count bounds on two independent pure-avoiding ternary
branches. This is an initial comparison, not a paired backward-budget tower. -/
namespace Erdos7PairedTernaryRoot
open scoped BigOperators
open Erdos7PresentCylinderArithmetic Erdos7IndependentPureLifts
open Erdos7IndependentLiftSampling Erdos7RealChain Erdos7RetainedRealCompression
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

lemma pair_fraction_le_max {X : Type*} [DecidableEq X]
    (S T C : Finset X) (hS : S.Nonempty) (hT : T.Nonempty)
    (hthin : ∀ x ∈ S, ∀ y ∈ T, ¬ (x ∈ C ∧ y ∈ C)) :
    (((S ×ˢ T).filter (fun z => z.1 ∈ C ∨ z.2 ∈ C)).card : ℚ) /
        (S ×ˢ T).card ≤
      max (((S ∩ C).card : ℚ)/S.card) (((T ∩ C).card : ℚ)/T.card) := by
  have hs0 : (S.card : ℚ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hS)
  have ht0 : (T.card : ℚ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hT)
  by_cases hSC : (S ∩ C).Nonempty
  · obtain ⟨x, hx⟩ := hSC
    have hz : ∀ y ∈ T, y ∉ C := by
      intro y hy hyC
      exact hthin x (Finset.mem_inter.mp hx).1 y hy ⟨(Finset.mem_inter.mp hx).2, hyC⟩
    have he : (S ×ˢ T).filter (fun z => z.1 ∈ C ∨ z.2 ∈ C) = (S ∩ C) ×ˢ T := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_inter]
      constructor
      · rintro ⟨⟨hs, ht⟩, hc | hc⟩
        · exact ⟨⟨hs,hc⟩,ht⟩
        · exact False.elim (hz z.2 ht hc)
      · rintro ⟨⟨hs,hc⟩,ht⟩
        exact ⟨⟨hs,ht⟩,Or.inl hc⟩
    rw [he, Finset.card_product, Finset.card_product, Nat.cast_mul, Nat.cast_mul]
    have heq : ((S ∩ C).card : ℚ)*T.card/(S.card*T.card) = (S ∩ C).card/S.card := by
      field_simp
    rw [heq]
    exact le_max_left _ _
  · have hz : ∀ x ∈ S, x ∉ C := by
      intro x hx hxC
      exact hSC ⟨x,Finset.mem_inter.mpr ⟨hx,hxC⟩⟩
    have he : (S ×ˢ T).filter (fun z => z.1 ∈ C ∨ z.2 ∈ C) = S ×ˢ (T ∩ C) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_inter]
      constructor
      · rintro ⟨⟨hs,ht⟩,hc | hc⟩
        · exact False.elim (hz z.1 hs hc)
        · exact ⟨hs,ht,hc⟩
      · rintro ⟨hs,ht,hc⟩
        exact ⟨⟨hs,ht⟩,Or.inr hc⟩
    rw [he, Finset.card_product, Finset.card_product, Nat.cast_mul, Nat.cast_mul]
    have heq : (S.card : ℚ)*(T ∩ C).card/(S.card*T.card) = (T ∩ C).card/T.card := by
      field_simp
    rw [heq]
    exact le_max_right _ _

/-- One positive-depth cylinder can be active in only one of two different
first-digit branches, so its pair activation bound pays for ONE branch. -/
theorem branch_pair_one_cylinder (p E e : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (he : 1 ≤ e) (heE : e ≤ E)
    (a : ℕ → ℤ) (b c r : ℤ) (hbc : ¬ (p : ℤ) ∣ b-c) :
    let S := branchGood p E a b
    let T := branchGood p E a c
    (((S ×ˢ T).filter (fun z => z.1 ∈ cylinder p E e r ∨
      z.2 ∈ cylinder p E e r)).card : ℚ)/(S ×ˢ T).card ≤
      (p*(p-1)/(p-2) : ℚ)*((p : ℚ)⁻¹)^e := by
  dsimp only
  apply (pair_fraction_le_max (branchGood p E a b) (branchGood p E a c)
    (cylinder p E e r) (branchGood_nonempty p E hp hE a b)
    (branchGood_nonempty p E hp hE a c) ?_).trans
  · exact max_le (branch_hit_fraction_le p E e hp hE heE a b r)
      (branch_hit_fraction_le p E e hp hE heE a c r)
  · intro x hx y hy hxy
    exact lifts_thin p e (by omega) x.val y.val b c r
      ((mem_branchGood p E a b x).mp hx).1
      ((mem_branchGood p E a c y).mp hy).1 hbc
      ⟨(mem_cylinder p E e r x).mp hxy.1, (mem_cylinder p E e r y).mp hxy.2⟩

noncomputable def q (R j : ℕ) : ℝ :=
  if j < R then 6*(1/3 : ℝ)^(j+2) else 0

lemma q_nonneg (R j : ℕ) : 0 ≤ q R j := by
  unfold q
  split_ifs <;> positivity

lemma q_terminal (R : ℕ) : q R R = 0 := by simp [q]

lemma q_zero_le (R : ℕ) : q R 0 ≤ 1 := by
  unfold q
  split_ifs <;> norm_num

lemma q_step (R j : ℕ) : q R (j+1) ≤ q R j := by
  unfold q
  split_ifs with h₁ h₂
  · rw [show j+1+2 = (j+2)+1 by omega, pow_succ]
    have hp : 0 ≤ (1/3 : ℝ)^(j+2) := by positivity
    nlinarith
  · omega
  · positivity
  · exact le_rfl

noncomputable def law (R : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (1-q R 0)*φ (3/2) + ∑ j ∈ Finset.range R,
    (q R j-q R (j+1))*φ (3/2+((j:ℝ)+1)/2)

/-- A normalized pair activation count contributes one half. Its finite
positive comparison law starts at3/2, not at1. -/
theorem average_count_comparison {A : Type*} [Fintype A]
    (μ : A → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (s : ℕ → A → ℝ) (K : A → ℝ) (R : ℕ)
    (hs : ∀ j < R, ∀ x, s j x ∈ Set.Icc (0:ℝ) 1)
    (hmarg : ∀ j < R, (∑ x, μ x*s j x) ≤ 6*(1/3 : ℝ)^(j+2))
    (hK : ∀ x, K x ≤ 3/2+(∑ j ∈ Finset.range R, s j x)/2)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x, μ x*φ (K x)) ≤ law R φ := by
  have he (x : A) : (3/2 : ℝ)+(∑ j ∈ Finset.range R, s j x)/2 =
      3/2+prefixWeight (fun j => s j x/2) R := by
    rw [prefixWeight, Finset.sum_div]
  have hb := retained_group_mixture μ hμ 1 1 (by simpa using hm) φ hφ hmφ
    (3/2) (fun _ => (1/2 : ℝ)) (fun j x => s j x/2) (q R) R
    (fun j hj => by norm_num) (fun j hj x => by have := (hs j hj x).1; positivity)
    (fun j hj x => by have := (hs j hj x).2; linarith)
    (fun j hj => by
      simp only [one_mul]
      rw [show q R j = 6*(1/3 : ℝ)^(j+2) by simp [q,hj]]
      have hn := mul_le_mul_of_nonneg_right (hmarg j hj) (by norm_num : (0:ℝ) ≤ 1/2)
      rw [Finset.sum_mul] at hn
      convert hn using 1 <;> ring_nf)
    (q_terminal R)
  have hb' : (∑ x, μ x*φ (3/2+(∑ j ∈ Finset.range R, s j x)/2)) ≤ law R φ := by
    simpa only [one_mul, law, prefixWeight, ← Finset.sum_div, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one, mul_one_div] using hb
  apply LE.le.trans _ hb'
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hmφ (hK x)) (hμ x))

lemma law_nonnegative_coefficients (R : ℕ) :
    0 ≤ 1-q R 0 ∧ ∀ j, 0 ≤ q R j-q R (j+1) :=
  ⟨sub_nonneg.mpr (q_zero_le R),fun j => sub_nonneg.mpr (q_step R j)⟩

lemma law_mass (R : ℕ) : law R (fun _ => (1 : ℝ)) = 1 := by
  simp only [law, mul_one]
  rw [Finset.sum_range_sub', q_terminal]
  ring

#print axioms branch_pair_one_cylinder
#print axioms average_count_comparison
#print axioms law_mass

lemma q_sum (R : ℕ) : (∑ j ∈ Finset.range R, q R j) = 1-(1/3 : ℝ)^R := by
  have he : ∀ n : ℕ, (∑ j ∈ Finset.range n, 6*(1/3 : ℝ)^(j+2)) = 1-(1/3 : ℝ)^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, show n+2 = (n+1)+1 by omega, pow_succ, pow_succ]
      ring
  calc
    _ = ∑ j ∈ Finset.range R, 6*(1/3 : ℝ)^(j+2) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [q,Finset.mem_range.mp hj]
    _ = _ := he R

lemma law_mean (R : ℕ) : law R (fun t => t) = 2-(1/3 : ℝ)^R/2 := by
  have ht := chain_summation_by_parts (fun j : ℕ => (3/2 : ℝ)+(j:ℝ)/2) (q R) R
  simp only [q_terminal,zero_mul,Nat.cast_zero,zero_div,add_zero,Nat.cast_add,Nat.cast_one] at ht
  have he (j : ℕ) : (3/2 : ℝ)+((j:ℝ)+1)/2-(3/2+(j:ℝ)/2) = 1/2 := by ring
  simp_rw [he] at ht
  rw [← Finset.sum_mul, q_sum] at ht
  unfold law
  dsimp only at ht ⊢
  linarith

lemma law_mean_lt_two (R : ℕ) : law R (fun t => t) < 2 := by
  rw [law_mean]
  have hp : 0 < (1/3 : ℝ)^R := by positivity
  linarith

#print axioms law_mean
#print axioms law_mean_lt_two


noncomputable def uniformOn {X : Type*} [DecidableEq X] (S : Finset X) (x : X) : ℝ :=
  if x ∈ S then 1/(S.card : ℝ) else 0

lemma uniformOn_nonneg {X : Type*} [DecidableEq X] (S : Finset X) (x : X) :
    0 ≤ uniformOn S x := by
  unfold uniformOn
  split_ifs <;> positivity

lemma uniformOn_event {X : Type*} [Fintype X] [DecidableEq X]
    (S : Finset X) (P : X → Prop) [DecidablePred P] :
    (∑ x, uniformOn S x*(if P x then 1 else 0)) =
      ((S.filter P).card : ℝ)/S.card := by
  calc
    _ = ∑ x, if x ∈ S.filter P then (1 : ℝ)/S.card else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S <;> by_cases hp : P x <;> simp [uniformOn,hx,hp]
    _ = _ := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      simp [div_eq_mul_inv]

lemma uniformOn_mass {X : Type*} [Fintype X] [DecidableEq X]
    (S : Finset X) (hS : S.Nonempty) : (∑ x, uniformOn S x) = 1 := by
  have hh := uniformOn_event S (fun _ => True)
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  simpa [hcard] using hh

noncomputable def pairAverage {X : Type*} [DecidableEq X]
    (C : ℕ → Finset X) (R : ℕ) (z : X × X) : ℝ :=
  ((1+∑ j ∈ Finset.range (R+1), if z.1 ∈ C (j+1) then (1:ℝ) else 0) +
    (1+∑ j ∈ Finset.range (R+1), if z.2 ∈ C (j+1) then (1:ℝ) else 0))/2

lemma pairAverage_bound {X : Type*} [DecidableEq X]
    (C : ℕ → Finset X) (R : ℕ) (z : X × X)
    (hthin : ∀ e, 1 ≤ e → e ≤ R+1 → ¬ (z.1 ∈ C e ∧ z.2 ∈ C e)) :
    pairAverage C R z ≤ 3/2 +
      (∑ j ∈ Finset.range R, if z.1 ∈ C (j+2) ∨ z.2 ∈ C (j+2) then (1:ℝ) else 0)/2 := by
  have hfirst : (if z.1 ∈ C 1 then (1:ℝ) else 0) +
      (if z.2 ∈ C 1 then (1:ℝ) else 0) ≤ 1 := by
    have hn := hthin 1 (by omega) (by omega)
    by_cases h₁ : z.1 ∈ C 1 <;> by_cases h₂ : z.2 ∈ C 1 <;> simp_all
  have hsum : (∑ j ∈ Finset.range R, if z.1 ∈ C (j+2) then (1:ℝ) else 0) +
      (∑ j ∈ Finset.range R, if z.2 ∈ C (j+2) then (1:ℝ) else 0) =
      ∑ j ∈ Finset.range R, if z.1 ∈ C (j+2) ∨ z.2 ∈ C (j+2) then (1:ℝ) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hn := hthin (j+2) (by omega) (by have := Finset.mem_range.mp hj; omega)
    by_cases h₁ : z.1 ∈ C (j+2) <;> by_cases h₂ : z.2 ∈ C (j+2) <;> simp_all
  unfold pairAverage
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.zero_add, show ∀ j : ℕ, j+1+1 = j+2 by omega]
  linarith

/-- The actual uniform product of two pure-avoiding ternary branches obeys
the finite average-count law. Both coordinates use the same cylinder family;
no independence between different cylinders is assumed. -/
theorem arithmetic_pair_average_comparison (R : ℕ) (a c : ℕ → ℤ)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    let S := branchGood 3 (R+1) a 1
    let T := branchGood 3 (R+1) a 2
    let C := fun e => cylinder 3 (R+1) e (c e)
    (∑ z, uniformOn (S ×ˢ T) z * φ (pairAverage C R z)) ≤ law R φ := by
  let S := branchGood 3 (R+1) a 1
  let T := branchGood 3 (R+1) a 2
  let C := fun e => cylinder 3 (R+1) e (c e)
  let s := fun j (z : ZMod (3^(R+1)) × ZMod (3^(R+1))) =>
    if z.1 ∈ C (j+2) ∨ z.2 ∈ C (j+2) then (1:ℝ) else 0
  have hS : S.Nonempty := branchGood_nonempty 3 (R+1) (by omega) (by omega) a 1
  have hT : T.Nonempty := branchGood_nonempty 3 (R+1) (by omega) (by omega) a 2
  have hs : ∀ j < R, ∀ z, s j z ∈ Set.Icc (0:ℝ) 1 := by
    intro j hj z
    dsimp [s]
    split_ifs <;> norm_num
  have hthin (z : ZMod (3^(R+1)) × ZMod (3^(R+1))) (hz : z ∈ S ×ˢ T)
      (e : ℕ) (he : 1 ≤ e) (heE : e ≤ R+1) : ¬ (z.1 ∈ C e ∧ z.2 ∈ C e) := by
    intro hh
    obtain ⟨hzS,hzT⟩ := Finset.mem_product.mp hz
    exact lifts_thin 3 e (by omega) z.1.val z.2.val 1 2 (c e)
      ((mem_branchGood 3 (R+1) a 1 z.1).mp hzS).1
      ((mem_branchGood 3 (R+1) a 2 z.2).mp hzT).1 (by norm_num)
      ⟨(mem_cylinder 3 (R+1) e (c e) z.1).mp hh.1,
       (mem_cylinder 3 (R+1) e (c e) z.2).mp hh.2⟩
  have hmarg : ∀ j < R, (∑ z, uniformOn (S ×ˢ T) z*s j z) ≤ 6*(1/3 : ℝ)^(j+2) := by
    intro j hj
    dsimp only [s]
    rw [uniformOn_event]
    have hb := branch_pair_one_cylinder 3 (R+1) (j+2) (by omega) (by omega)
      (by omega) (by omega) a 1 2 (c (j+2)) (by norm_num)
    dsimp only at hb
    norm_num at hb
    dsimp only [S, T, C]
    rw [Finset.card_product]
    have hbR := (Rat.cast_le (K := ℝ)).mpr hb
    push_cast at hbR
    simpa only [one_div, Nat.cast_mul] using hbR
  have hb := average_count_comparison (uniformOn (S ×ˢ T)) (uniformOn_nonneg _)
    (uniformOn_mass _ (hS.product hT)) s
    (fun z => 3/2+(∑ j ∈ Finset.range R, s j z)/2) R hs hmarg
    (fun _ => le_rfl) φ hφ hmφ
  change (∑ z, uniformOn (S ×ˢ T) z * φ (pairAverage C R z)) ≤ _
  apply LE.le.trans _ hb
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : z ∈ S ×ˢ T
  · apply mul_le_mul_of_nonneg_left _ (uniformOn_nonneg _ _)
    exact hmφ (pairAverage_bound C R z (hthin z hz))
  · simp [uniformOn,hz]

#print axioms arithmetic_pair_average_comparison

lemma q_first_moment (R : ℕ) : (∑ j ∈ Finset.range R, q R j*(j:ℝ)) =
    1/2-((R:ℝ)+1/2)*(1/3 : ℝ)^R := by
  have he : ∀ n : ℕ, (∑ j ∈ Finset.range n, 6*(1/3 : ℝ)^(j+2)*(j:ℝ)) =
      1/2-((n:ℝ)+1/2)*(1/3 : ℝ)^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one,
        show n+2 = (n+1)+1 by omega, pow_succ, pow_succ]
      ring
  calc
    _ = ∑ j ∈ Finset.range R, 6*(1/3 : ℝ)^(j+2)*(j:ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [q,Finset.mem_range.mp hj]
    _ = _ := he R

lemma law_second_moment (R : ℕ) : law R (fun t => t^2) =
    17/4-((R:ℝ)/2+2)*(1/3 : ℝ)^R := by
  have ht := chain_summation_by_parts (fun j : ℕ => ((3/2 : ℝ)+(j:ℝ)/2)^2) (q R) R
  simp only [q_terminal,zero_mul,Nat.cast_zero,zero_div,add_zero,Nat.cast_add,Nat.cast_one] at ht
  have he (j : ℕ) : ((3/2 : ℝ)+((j:ℝ)+1)/2)^2-(3/2+(j:ℝ)/2)^2 = 7/4+(j:ℝ)/2 := by ring
  have hx (j : ℕ) : q R j*(7/4+(j:ℝ)/2) = q R j*(7/4)+(q R j*(j:ℝ))/2 := by ring
  simp_rw [he, hx] at ht
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div, q_sum, q_first_moment] at ht
  unfold law
  dsimp only at ht ⊢
  nlinarith

lemma law_second_moment_lt (R : ℕ) : law R (fun t => t^2) < 17/4 := by
  rw [law_second_moment]
  have hp : 0 < (1/3 : ℝ)^R := by positivity
  have hR : 0 ≤ (R:ℝ) := Nat.cast_nonneg R
  nlinarith

#print axioms law_second_moment
#print axioms law_second_moment_lt
end Erdos7PairedTernaryRoot
