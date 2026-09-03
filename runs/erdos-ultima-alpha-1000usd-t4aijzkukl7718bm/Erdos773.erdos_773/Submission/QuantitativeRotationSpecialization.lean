import Submission.QuadraticRotationPairs

/-!
Quantitative integer specialization of the finite rotation model. This is
an auxiliary construction, not a settlement of Erdős 773.
-/
namespace Erdos773.QuantitativeRotationSpecialization
open Finset MvPolynomial
noncomputable section
set_option maxHeartbeats 2500000

lemma degree_sub {n : ℕ} (P Q : MvPolynomial (Fin n) ℚ) :
    (P-Q).totalDegree ≤ max P.totalDegree Q.totalDegree := by
  simpa only [sub_eq_add_neg, totalDegree_neg] using totalDegree_add P (-Q)

lemma bounded_pair_specialization {n : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial (Fin n) ℚ) (D : ℕ)
    (hP : ∀ i, (P i).totalDegree ≤ D) :
    ∃ x : Fin n → ℕ,
      (∀ i, 3*(D*Fintype.card ι^4+1) < x i ∧
        x i ≤ 4*(D*Fintype.card ι^4+1)) ∧
      ∀ a b c d,
        eval (fun i => (x i : ℚ)) (P a+P b) =
          eval (fun i => (x i : ℚ)) (P c+P d) ↔ P a+P b=P c+P d := by
  classical
  let T := ι × ι × ι × ι
  let diff (t : T) := P t.1+P t.2.1-(P t.2.2.1+P t.2.2.2)
  let factor (t : T) := if diff t=0 then 1 else diff t
  let F := ∏ t : T, factor t
  have hF : F ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro t _
    dsimp only [factor]
    split_ifs with h
    · exact one_ne_zero
    · exact h
  have hd (t : T) : (factor t).totalDegree ≤ D := by
    dsimp only [factor]
    split_ifs
    · simp
    · exact (degree_sub _ _).trans (max_le
        ((totalDegree_add _ _).trans (max_le (hP _) (hP _)))
        ((totalDegree_add _ _).trans (max_le (hP _) (hP _))))
  have hdeg : F.totalDegree ≤ D*Fintype.card ι^4 := by
    calc
      _ ≤ ∑ t : T, (factor t).totalDegree := totalDegree_finset_prod _ _
      _ ≤ ∑ _t : T, D := sum_le_sum (fun t _ => hd t)
      _ = _ := by simp [T, pow_succ]; ring
  let Q := D*Fintype.card ι^4+1
  let S : Finset ℚ := (Icc (3*Q+1) (4*Q)).image (fun a : ℕ => (a : ℚ))
  have hSc : S.card=Q := by
    rw [card_image_of_injective _ (Nat.cast_injective (R := ℚ))]
    simp only [Nat.card_Icc]
    dsimp [Q]
    omega
  have hex : ∃ y : Fin n → ℚ, (∀ i, y i ∈ S) ∧ eval y F ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hF
    apply eq_zero_of_eval_zero_at_prod_finset F (fun _ => S)
    · intro i
      rw [hSc]
      exact lt_of_le_of_lt (degreeOf_le_totalDegree F i) (by dsimp [Q]; omega)
    · exact hn
  obtain ⟨y,hy,hyF⟩ := hex
  have hy' : ∀ i, ∃ a : ℕ, a ∈ Icc (3*Q+1) (4*Q) ∧ (a:ℚ)=y i := by
    intro i
    exact mem_image.mp (hy i)
  choose x hx hxy using hy'
  have hxe : (fun i => (x i : ℚ))=y := funext hxy
  refine ⟨x,fun i => ?_,fun a b c d => ⟨?_,fun h => congrArg (eval _) h⟩⟩
  · have hh := mem_Icc.mp (hx i)
    change 3*Q < x i ∧ x i ≤ 4*Q
    omega
  · intro he
    by_contra hn
    have ht : diff (a,b,c,d) ≠ 0 := sub_ne_zero.mpr hn
    have hz : eval y (factor (a,b,c,d))=0 := by
      dsimp only [factor]
      rw [if_neg ht]
      dsimp only [diff]
      rw [map_sub,← hxe,he,sub_self]
    apply hyF
    change eval y (∏ t : T, factor t)=0
    rw [map_prod]
    exact prod_eq_zero (mem_univ (a,b,c,d)) hz

open Erdos773.QuadraticRotationTrade

lemma poly_degree {n : ℕ} (u : Root n) : (poly u).totalDegree ≤ 1 := by
  cases u with
  | core a =>
      change (C (5:ℚ)*X a).totalDegree ≤ 1
      apply (totalDegree_mul _ _).trans
      norm_num
  | plus e =>
      change (C (3:ℚ)*X e.val.1+C (4:ℚ)*X e.val.2).totalDegree ≤ 1
      apply (totalDegree_add _ _).trans
      apply max_le
      all_goals apply (totalDegree_mul _ _).trans; norm_num
  | minus e =>
      change (C (4:ℚ)*X e.val.1-C (3:ℚ)*X e.val.2).totalDegree ≤ 1
      apply (degree_sub _ _).trans
      apply max_le
      all_goals apply (totalDegree_mul _ _).trans; norm_num

lemma value_degree {n : ℕ} (u : Root n) : (value u).totalDegree ≤ 2 := by
  exact (totalDegree_pow _ _).trans (by have := poly_degree u; omega)

def rootAt {n : ℕ} (x : Fin n → ℕ) : Root n → ℕ
  | .core a => 5*x a
  | .plus e => 3*x e.val.1+4*x e.val.2
  | .minus e => 4*x e.val.1-3*x e.val.2

lemma rootAt_bounds {n Q : ℕ} (x : Fin n → ℕ)
    (hx : ∀ i, 3*Q < x i ∧ x i ≤ 4*Q) (u : Root n) :
    0 < rootAt x u ∧ rootAt x u ≤ 28*Q := by
  cases u with
  | core a => have ha := hx a; dsimp [rootAt]; omega
  | plus e => have ha := hx e.val.1; have hb := hx e.val.2; dsimp [rootAt]; omega
  | minus e => have ha := hx e.val.1; have hb := hx e.val.2; dsimp [rootAt]; omega

lemma eval_rootAt {n Q : ℕ} (x : Fin n → ℕ)
    (hx : ∀ i, 3*Q < x i ∧ x i ≤ 4*Q) (u : Root n) :
    eval (fun i => (x i : ℚ)) (poly u) = (rootAt x u : ℚ) := by
  cases u with
  | core a => simp [poly,rootAt]
  | plus e => simp [poly,rootAt]
  | minus e =>
      have ha := hx e.val.1
      have hb := hx e.val.2
      have hh : 3*x e.val.2 ≤ 4*x e.val.1 := by omega
      simp [poly,rootAt,Nat.cast_sub hh]

/-- A finite restriction of the rotation model admits an integer specialization
with height at most `28*(2*m^4+1)`, where `m` is its number of roots. -/
theorem bounded_model {n : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Root n) (he : Function.Injective e) :
    ∃ f : ι → ℕ,
      (∀ u, 0 < f u ∧ f u ≤ 28*(2*Fintype.card ι^4+1)) ∧
      Function.Injective f ∧
      ∀ u v w z, f u^2+f v^2=f w^2+f z^2 ↔
        value (e u)+value (e v)=value (e w)+value (e z) := by
  obtain ⟨x,hx,hpair⟩ := bounded_pair_specialization
    (fun u => value (e u)) 2 (fun u => value_degree (e u))
  let f : ι → ℕ := fun u => rootAt x (e u)
  have hev (u : ι) : eval (fun i => (x i : ℚ)) (value (e u)) = (f u : ℚ)^2 := by
    rw [value,map_pow,eval_rootAt x hx]
  have hrel (u v w z : ι) :
      f u^2+f v^2=f w^2+f z^2 ↔
        value (e u)+value (e v)=value (e w)+value (e z) := by
    rw [← hpair]
    simp only [map_add,hev]
    exact_mod_cast (Iff.rfl : f u^2+f v^2=f w^2+f z^2 ↔ _)
  refine ⟨f,fun u => rootAt_bounds x hx (e u),?_,hrel⟩
  intro u v huv
  apply he
  apply value_injective
  have hh := (hrel u u v v).mp (by rw [huv])
  have hh' : (2: MvPolynomial (Fin n) ℚ)*value (e u)=2*value (e v) := by
    simpa only [two_mul] using hh
  exact mul_left_cancel₀ (by norm_num : (2:MvPolynomial (Fin n) ℚ) ≠ 0) hh'

#print axioms bounded_pair_specialization
#print axioms bounded_model
end
end Erdos773.QuantitativeRotationSpecialization
