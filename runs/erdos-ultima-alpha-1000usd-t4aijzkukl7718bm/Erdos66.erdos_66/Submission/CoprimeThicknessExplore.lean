import Submission.RectangularRadixExplore
import Submission.RectangularCarryAverageExplore
import Submission.MixedCyclicThickeningExplore
import Submission.CarrySplitFibersExplore

/-! A common-prime, coprime-thickness mixed-count construction. The high digit
is decomposed by CRT; subtraction retains its lower-digit borrow. -/
namespace Erdos66CoprimeThickness
open Erdos66RectangularRadix Erdos66RectangularCarryAverage
  Erdos66CyclicThickening Erdos66OuterCarryProfile Erdos66MixedCyclicThickening
  Erdos66CarrySplitFibers
open scoped Classical
set_option maxHeartbeats 2400000

variable (p K L : ℕ) [NeZero p] [NeZero K] [NeZero L]
variable (hp : p.Coprime (K*L)) (hKL : K.Coprime L)

noncomputable def highCRT : ZMod (p*(K*L)) ≃+* ZMod p × (ZMod K × ZMod L) :=
  (ZMod.chineseRemainder hp).trans
    (RingEquiv.prodCongr (RingEquiv.refl (ZMod p)) (ZMod.chineseRemainder hKL))

noncomputable def leftRows (B : Finset (ZMod p × ZMod p)) :
    Finset (ZMod p × ZMod (p*(K*L))) :=
  Finset.univ.filter (fun z ↦
    (z.1, (highCRT p K L hp hKL z.2).1-((highCRT p K L hp hKL z.2).2.1.val:ZMod p))∈B)

noncomputable def rightRows (C : Finset (ZMod p × ZMod p)) :
    Finset (ZMod p × ZMod (p*(K*L))) :=
  Finset.univ.filter (fun z ↦
    (z.1, (highCRT p K L hp hKL z.2).1-((highCRT p K L hp hKL z.2).2.2.val:ZMod p))∈C)

noncomputable def leftSet (B : Finset (ZMod p × ZMod p)) : Finset (ZMod (p*(p*(K*L)))) :=
  radixSet p (p*(K*L)) (leftRows p K L hp hKL B)

noncomputable def rightSet (C : Finset (ZMod p × ZMod p)) : Finset (ZMod (p*(p*(K*L)))) :=
  radixSet p (p*(K*L)) (rightRows p K L hp hKL C)

lemma count_crt_formula (B C : Finset (ZMod p × ZMod p)) (t : ZMod p)
    (s : ZMod (p*(K*L))) :
    cyclicCount (p*(p*(K*L))) (leftSet p K L hp hKL B) (rightSet p K L hp hKL C)
      (encode p (p*(K*L)) (t,s)) =
      ∑ x : ZMod p, ∑ w : ZMod p, ∑ i : ZMod K, ∑ j : ZMod L,
        if (x,w-(i.val:ZMod p))∈B ∧
          (t-x, (highCRT p K L hp hKL s).1-w-(borrow p t x:ZMod p)-
            (((highCRT p K L hp hKL s).2.2-j-(borrow p t x:ZMod L)).val:ZMod p))∈C
        then 1 else 0 := by
  rw [leftSet, rightSet, mixed_count_formula]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Equiv.sum_comp (highCRT p K L hp hKL).symm.toEquiv,
    Fintype.sum_prod_type]
  simp only [leftRows, rightRows, Finset.mem_filter, Finset.mem_univ, true_and,
    map_sub, map_natCast, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, RingEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_natCast, Prod.snd_natCast]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Fintype.sum_prod_type]

lemma count_independent_residues (B C : Finset (ZMod p × ZMod p)) (t : ZMod p)
    (s : ZMod (p*(K*L))) :
    cyclicCount (p*(p*(K*L))) (leftSet p K L hp hKL B) (rightSet p K L hp hKL C)
      (encode p (p*(K*L)) (t,s)) =
      ∑ x : ZMod p, ∑ w : ZMod p, ∑ i : ZMod K, ∑ j : ZMod L,
        if (x,w-(i.val:ZMod p))∈B ∧
          (t-x, (highCRT p K L hp hKL s).1-w-(borrow p t x:ZMod p)-(j.val:ZMod p))∈C
        then 1 else 0 := by
  rw [count_crt_formula]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Equiv.sum_comp (Equiv.subLeft ((highCRT p K L hp hKL s).2.2-(borrow p t x:ZMod L)))]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Equiv.subLeft_apply]
  have he : (highCRT p K L hp hKL s).2.2-
      ((highCRT p K L hp hKL s).2.2-(borrow p t x:ZMod L)-j)-(borrow p t x:ZMod L)=j := by ring
  simp only [he]

lemma count_parameter_formula (B C : Finset (ZMod p × ZMod p)) (t : ZMod p)
    (s : ZMod (p*(K*L))) :
    cyclicCount (p*(p*(K*L))) (leftSet p K L hp hKL B) (rightSet p K L hp hKL C)
      (encode p (p*(K*L)) (t,s)) =
      ∑ i : ZMod K, ∑ j : ZMod L, ∑ x : ZMod p, ∑ u : ZMod p,
        if (x,u)∈B ∧ (t-x, (highCRT p K L hp hKL s).1-(i.val:ZMod p)-
          (j.val:ZMod p)-(borrow p t x:ZMod p)-u)∈C then 1 else 0 := by
  rw [count_independent_residues]
  calc
    _ = ∑ x : ZMod p, ∑ i : ZMod K, ∑ j : ZMod L, ∑ u : ZMod p,
        if (x,u)∈B ∧ (t-x, (highCRT p K L hp hKL s).1-(i.val:ZMod p)-
          (j.val:ZMod p)-(borrow p t x:ZMod p)-u)∈C then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [←Equiv.sum_comp (Equiv.addLeft (i.val:ZMod p))]
      apply Finset.sum_congr rfl
      intro u hu
      change (if (x, (i.val:ZMod p)+u-i.val)∈B ∧
        (t-x, (highCRT p K L hp hKL s).1-((i.val:ZMod p)+u)-(borrow p t x:ZMod p)-j.val)∈C
        then 1 else 0) = _
      have he₁ : (i.val:ZMod p)+u-i.val=u := by ring
      have he₂ : (highCRT p K L hp hKL s).1-((i.val:ZMod p)+u)-(borrow p t x:ZMod p)-j.val =
          (highCRT p K L hp hKL s).1-i.val-j.val-(borrow p t x:ZMod p)-u := by ring
      rw [he₁, he₂]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]

lemma count_split_formula (B C : Finset (ZMod p × ZMod p)) (t : ZMod p)
    (s : ZMod (p*(K*L))) :
    cyclicCount (p*(p*(K*L))) (leftSet p K L hp hKL B) (rightSet p K L hp hKL C)
      (encode p (p*(K*L)) (t,s)) =
      ∑ i : ZMod K, ∑ j : ZMod L,
        (beforeCount p B C t ((highCRT p K L hp hKL s).1-i.val-j.val)+
         afterCount p B C t ((highCRT p K L hp hKL s).1-i.val-j.val-1)) := by
  rw [count_parameter_formula]
  simp_rw [carry_split]

/-- Mixed counts for these two CRT-compatible thickenings have an area main
term and only a boundary-sized carry loss. Both sets are actual cyclic sets. -/
theorem mixed_thickness_error (B C : Finset (ZMod p × ZMod p)) (μ E : ℝ)
    (hflat : ∀ t s, |((mixedFiber p B C t s).card:ℝ)-μ| ≤ E)
    (z : ZMod (p*(p*(K*L)))) :
    |(cyclicCount (p*(p*(K*L))) (leftSet p K L hp hKL B) (rightSet p K L hp hKL C) z:ℝ)-
      (K:ℝ)*L*μ| ≤ (K:ℝ)*L*E+(min K L:ℕ)*(μ+E) := by
  obtain ⟨⟨t,s⟩, rfl⟩ := (radixEquiv p (p*(K*L))).surjective z
  change |(cyclicCount _ _ _ (encode p (p*(K*L)) (t,s)):ℝ)-_| ≤ _
  have he : (cyclicCount (p*(p*(K*L))) (leftSet p K L hp hKL B) (rightSet p K L hp hKL C)
      (encode p (p*(K*L)) (t,s)):ℝ) =
      ∑ i : ZMod K, ∑ j : ZMod L,
        ((beforeCount p B C t ((highCRT p K L hp hKL s).1-i.val-j.val):ℝ)+
         afterCount p B C t ((highCRT p K L hp hKL s).1-i.val-j.val-1)) := by
    exact_mod_cast count_split_formula p K L hp hKL B C t s
  rw [he]
  exact averaged_fiber_error p K L B C t (highCRT p K L hp hKL s).1 μ E (hflat t)

lemma leftSet_univ : leftSet p K L hp hKL Finset.univ=Finset.univ := by
  simp only [leftSet, leftRows, Finset.mem_univ, Finset.filter_true, radixSet_univ]

lemma rightSet_univ : rightSet p K L hp hKL Finset.univ=Finset.univ := by
  simp only [rightSet, rightRows, Finset.mem_univ, Finset.filter_true, radixSet_univ]

lemma plane_indicator_sum (B : Finset (ZMod p × ZMod p)) :
    (∑ x : ZMod p, ∑ u : ZMod p, if (x,u)∈B then 1 else 0) = B.card := by
  rw [←Fintype.sum_prod_type (fun z : ZMod p × ZMod p ↦ if z∈B then (1:ℕ) else 0)]
  simp

lemma leftSet_card (B : Finset (ZMod p × ZMod p)) :
    (leftSet p K L hp hKL B).card=K*L*B.card := by
  have hh := count_parameter_formula p K L hp hKL B Finset.univ 0 0
  rw [rightSet_univ] at hh
  simp only [cyclicCount, Finset.mem_univ, Finset.filter_true, and_true,
    plane_indicator_sum, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hh
  simpa only [mul_assoc] using hh

lemma reflected_indicator_sum (C : Finset (ZMod p × ZMod p)) (t q : ZMod p) :
    (∑ x : ZMod p, ∑ u : ZMod p,
      if (t-x,q-(borrow p t x:ZMod p)-u)∈C then 1 else 0) = C.card := by
  calc
    _ = ∑ x : ZMod p, ∑ u : ZMod p, if (t-x,u)∈C then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [←Equiv.sum_comp (Equiv.subLeft (q-(borrow p t x:ZMod p)))]
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
    _ = ∑ x : ZMod p, ∑ u : ZMod p, if (x,u)∈C then 1 else 0 := by
      rw [←Equiv.sum_comp (Equiv.subLeft t)]
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
    _ = _ := plane_indicator_sum p C

lemma rightSet_card (C : Finset (ZMod p × ZMod p)) :
    (rightSet p K L hp hKL C).card=K*L*C.card := by
  have hh := count_parameter_formula p K L hp hKL Finset.univ C 0 0
  rw [leftSet_univ] at hh
  have hcount : cyclicCount (p*(p*(K*L))) Finset.univ (rightSet p K L hp hKL C)
      (encode p (p*(K*L)) (0,0)) = (rightSet p K L hp hKL C).card := by
    rw [cyclicCount_sum]
    simp only [Finset.mem_univ, true_and]
    rw [←Equiv.sum_comp (Equiv.subLeft (encode p (p*(K*L)) (0,0)))]
    simp only [Equiv.subLeft_apply, sub_sub_cancel]
    simp
  rw [hcount] at hh
  simp only [Finset.mem_univ, true_and, reflected_indicator_sum,
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hh
  simpa only [mul_assoc] using hh

lemma actual_mean_scaling (B C : Finset (ZMod p × ZMod p)) :
    ((leftSet p K L hp hKL B).card:ℝ)*(rightSet p K L hp hKL C).card /
      (p*(p*(K*L)):ℕ) =
      (K:ℝ)*L*((B.card:ℝ)*C.card/(p:ℝ)^2) := by
  rw [leftSet_card, rightSet_card]
  push_cast
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast NeZero.ne p
  have hK0 : (K:ℝ)≠0 := by exact_mod_cast NeZero.ne K
  have hL0 : (L:ℝ)≠0 := by exact_mod_cast NeZero.ne L
  field_simp

end Erdos66CoprimeThickness
