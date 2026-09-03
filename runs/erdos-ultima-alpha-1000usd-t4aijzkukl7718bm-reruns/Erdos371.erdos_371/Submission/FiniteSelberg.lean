import FormalConjecturesUtil
import Submission.FiniteBrun

/-! A finite quadratic sieve certificate based on the orthogonal product basis
for independent Bernoulli variables. Arithmetic distribution errors are kept
explicit. This file makes no signed prime-factor assertion. -/

namespace Erdos371FiniteSelberg

open Finset

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def nuProd (ν : ι → ℝ) (t : Finset ι) : ℝ := ∏ p ∈ t, ν p
noncomputable def oddsProd (ν : ι → ℝ) (t : Finset ι) : ℝ :=
  ∏ p ∈ t, ν p/(1-ν p)
noncomputable def invOddsProd (ν : ι → ℝ) (t : Finset ι) : ℝ :=
  ∏ p ∈ t, (1-ν p)/ν p
noncomputable def monomial (t : Finset ι) (x : ι → ℝ) : ℝ := ∏ p ∈ t, x p
noncomputable def basis (ν : ι → ℝ) (t : Finset ι) (x : ι → ℝ) : ℝ :=
  ∏ p ∈ t, (1-x p/ν p)
noncomputable def coefficient (ν : ι → ℝ) (d : Finset ι) : ℝ :=
  (-1)^d.card/nuProd ν d
noncomputable def bit (v : Finset ι) (p : ι) : ℝ := if p ∈ v then 1 else 0
noncomputable def cubeWeight (ν : ι → ℝ) (s v : Finset ι) : ℝ :=
  ∏ p ∈ s, if p ∈ v then ν p else 1-ν p
noncomputable def ideal (ν : ι → ℝ) (s : Finset ι) (F : Finset ι → ℝ) : ℝ :=
  ∑ v ∈ s.powerset, cubeWeight ν s v * F v

lemma sum_cube_prod (s : Finset ι) (a b : ι → ℝ) :
    (∑ v ∈ s.powerset, ∏ p ∈ s, if p ∈ v then a p else b p) =
      ∏ p ∈ s, (a p+b p) := by
  rw [prod_add]
  apply sum_congr rfl
  intro v hv
  have hv : v ⊆ s := mem_powerset.mp hv
  rw [prod_ite]
  have h1 : s.filter (fun p => p ∈ v) = v := by
    ext p
    simp only [mem_filter]
    exact ⟨And.right, fun hp => ⟨hv hp, hp⟩⟩
  have h2 : s.filter (fun p => p ∉ v) = s \ v := by ext p; simp
  rw [h1,h2]

lemma prod_extend {t s : Finset ι} (ht : t ⊆ s) (f : ι → ℝ) :
    (∏ p ∈ t, f p) = ∏ p ∈ s, if p ∈ t then f p else 1 := by
  rw [prod_ite]
  have he : s.filter (fun p => p ∈ t) = t := by
    ext p
    simp only [mem_filter]
    exact ⟨And.right, fun hp => ⟨ht hp, hp⟩⟩
  simp [he]

lemma basis_expansion (ν : ι → ℝ) (t : Finset ι) (x : ι → ℝ) :
    basis ν t x = ∑ d ∈ t.powerset, coefficient ν d * monomial d x := by
  rw [basis,prod_sub]
  apply sum_congr rfl
  intro d hd
  simp only [prod_const_one,mul_one,prod_div_distrib,coefficient,nuProd,monomial]
  ring

lemma monomial_bits (d v : Finset ι) : monomial d (bit v) = if d ⊆ v then 1 else 0 := by
  simp [monomial,bit,prod_boole,subset_iff]

lemma monomial_mul {x : ι → ℝ} (hx : ∀ p, x p*x p=x p) (d e : Finset ι) :
    monomial d x*monomial e x = monomial (d ∪ e) x := by
  simp only [monomial]
  rw [← prod_union_inter]
  rw [prod_extend (show d ∩ e ⊆ d ∪ e from fun p hp => mem_union_left _ (mem_inter.mp hp).1)]
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  split_ifs
  · exact hx p
  · exact mul_one _

lemma ideal_monomial {s d : Finset ι} (hd : d ⊆ s) (ν : ι → ℝ) :
    ideal ν s (fun v => monomial d (bit v)) = nuProd ν d := by
  have he (v : Finset ι) : cubeWeight ν s v * monomial d (bit v) =
      ∏ p ∈ s, if p ∈ v then ν p else if p ∈ d then 0 else 1-ν p := by
    rw [monomial,prod_extend hd, cubeWeight,← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    by_cases hv : p ∈ v <;> by_cases hd : p ∈ d <;> simp [bit,hv,hd]
  rw [ideal,sum_congr rfl (fun v _ => he v),sum_cube_prod]
  rw [nuProd,prod_extend hd]
  apply prod_congr rfl
  intro p hp
  split_ifs <;> ring

lemma ideal_basis_product {s t u : Finset ι} (ht : t ⊆ s) (hu : u ⊆ s)
    (ν : ι → ℝ) (hν : ∀ p ∈ s, ν p ≠ 0) :
    ideal ν s (fun v => basis ν t (bit v)*basis ν u (bit v)) =
      if t=u then invOddsProd ν t else 0 := by
  have he (v : Finset ι) :
      cubeWeight ν s v * (basis ν t (bit v)*basis ν u (bit v)) =
      ∏ p ∈ s, if p ∈ v then
        ν p*(if p ∈ t then 1-1/ν p else 1)*(if p ∈ u then 1-1/ν p else 1)
        else 1-ν p := by
    rw [basis,basis,prod_extend ht,prod_extend hu,cubeWeight,← prod_mul_distrib,← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    by_cases hv : p ∈ v <;> by_cases hpt : p ∈ t <;> by_cases hpu : p ∈ u <;>
      simp [bit,hv,hpt,hpu] <;> ring
  rw [ideal,sum_congr rfl (fun v _ => he v),sum_cube_prod]
  have hp (p : ι) (hps : p ∈ s) :
      ν p*(if p ∈ t then 1-1/ν p else 1)*(if p ∈ u then 1-1/ν p else 1)+(1-ν p) =
      if p ∈ t then (if p ∈ u then (1-ν p)/ν p else 0)
      else if p ∈ u then 0 else 1 := by
    have hn := hν p hps
    split_ifs <;> field_simp <;> ring
  rw [prod_congr rfl hp]
  by_cases htu : t=u
  · subst u
    rw [if_pos rfl,invOddsProd,prod_extend ht]
    apply prod_congr rfl
    intro p hp
    split_ifs <;> simp_all
  · rw [if_neg htu]
    have hne : ¬ ∀ p, p ∈ t ↔ p ∈ u := fun h => htu (Finset.ext h)
    push_neg at hne
    obtain ⟨p,hp⟩ := hne
    by_cases hpt : p ∈ t
    · have hpu : p ∉ u := by tauto
      exact prod_eq_zero (ht hpt) (by simp [hpt,hpu])
    · have hpu : p ∈ u := by tauto
      exact prod_eq_zero (hu hpu) (by simp [hpt,hpu])


open Erdos371FiniteBrun

noncomputable def pairFunctional (ν : ι → ℝ) (C : Finset ι → ℝ)
    (t u : Finset ι) : ℝ :=
  ∑ d ∈ t.powerset, ∑ e ∈ u.powerset,
    coefficient ν d * coefficient ν e * C (d ∪ e)

lemma basis_product_expansion (ν : ι → ℝ) {x : ι → ℝ}
    (hx : ∀ p, x p*x p=x p) (t u : Finset ι) :
    basis ν t x * basis ν u x = pairFunctional ν (fun d => monomial d x) t u := by
  rw [basis_expansion, basis_expansion]
  rw [sum_mul]
  simp only [pairFunctional, mul_sum]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  rw [show coefficient ν d * monomial d x * (coefficient ν e * monomial e x) =
    coefficient ν d * coefficient ν e * (monomial d x * monomial e x) by ring]
  rw [monomial_mul hx]

lemma pairFunctional_sum {β : Type*} (ν : ι → ℝ) (B : Finset β)
    (C : β → Finset ι → ℝ) (t u : Finset ι) :
    pairFunctional ν (fun d => ∑ b ∈ B, C b d) t u =
      ∑ b ∈ B, pairFunctional ν (C b) t u := by
  simp only [pairFunctional, mul_sum]
  conv_lhs => arg 2; ext d; rw [sum_comm]
  rw [sum_comm]

lemma pairFunctional_smul (ν : ι → ℝ) (c : ℝ) (C : Finset ι → ℝ) (t u : Finset ι) :
    pairFunctional ν (fun d => c * C d) t u = c * pairFunctional ν C t u := by
  simp only [pairFunctional, mul_sum]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  ring

lemma sum_basis_product (A : Finset α) (b : ι → α → Prop)
    (ν : ι → ℝ) (t u : Finset ι) :
    (∑ n ∈ A, basis ν t (hit b n)*basis ν u (hit b n)) =
      pairFunctional ν (jointCount A b) t u := by
  have hx (n : α) (p : ι) : hit b n p * hit b n p = hit b n p := by
    unfold hit; split_ifs <;> norm_num
  simp_rw [basis_product_expansion ν (hx _)]
  rw [← pairFunctional_sum]
  congr 1
  funext d
  exact sum_hit_prod A b d

lemma pairFunctional_main {s t u : Finset ι} (ht : t ⊆ s) (hu : u ⊆ s)
    (ν : ι → ℝ) (hν : ∀ p ∈ s, ν p ≠ 0) :
    pairFunctional ν (nuProd ν) t u = if t=u then invOddsProd ν t else 0 := by
  have h := ideal_basis_product ht hu ν hν
  have hx (v : Finset ι) (p : ι) : bit v p * bit v p = bit v p := by
    unfold bit; split_ifs <;> norm_num
  simp_rw [basis_product_expansion ν (hx _)] at h
  unfold ideal at h
  simp_rw [← pairFunctional_smul] at h
  rw [← pairFunctional_sum] at h
  rw [← h]
  unfold pairFunctional
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  have hds : d ∪ e ⊆ s := union_subset (Subset.trans (mem_powerset.mp hd) ht)
    (Subset.trans (mem_powerset.mp he) hu)
  rw [← ideal_monomial hds ν]
  rfl

lemma pairFunctional_error (ν : ι → ℝ) (C E : Finset ι → ℝ) (X : ℝ)
    {s t u : Finset ι} (ht : t ⊆ s) (hu : u ⊆ s)
    (hE : ∀ d ⊆ s, |C d - X*nuProd ν d| ≤ E d) :
    |pairFunctional ν C t u - X*pairFunctional ν (nuProd ν) t u| ≤
      ∑ d ∈ t.powerset, ∑ e ∈ u.powerset,
        |coefficient ν d| * |coefficient ν e| * E (d ∪ e) := by
  rw [← pairFunctional_smul]
  simp only [pairFunctional, ← sum_sub_distrib, ← mul_sub]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro e he
  rw [abs_mul, abs_mul]
  apply mul_le_mul_of_nonneg_left
  · exact hE _ (union_subset (Subset.trans (mem_powerset.mp hd) ht)
      (Subset.trans (mem_powerset.mp he) hu))
  · positivity

noncomputable def combination (ν : ι → ℝ) (T : Finset (Finset ι))
    (w : Finset ι → ℝ) (x : ι → ℝ) : ℝ := ∑ t ∈ T, w t * basis ν t x

lemma combination_sq (ν : ι → ℝ) (T : Finset (Finset ι))
    (w : Finset ι → ℝ) (x : ι → ℝ) :
    combination ν T w x ^ 2 =
      ∑ t ∈ T, ∑ u ∈ T, w t*w u*(basis ν t x*basis ν u x) := by
  simp only [combination, pow_two, sum_mul, mul_sum]
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro u hu
  ring

lemma combination_main {s : Finset ι} {T : Finset (Finset ι)}
    (hT : ∀ t ∈ T, t ⊆ s) (ν : ι → ℝ) (hν : ∀ p ∈ s, ν p ≠ 0)
    (w : Finset ι → ℝ) :
    (∑ t ∈ T, ∑ u ∈ T, w t*w u*pairFunctional ν (nuProd ν) t u) =
      ∑ t ∈ T, (w t)^2 * invOddsProd ν t := by
  apply sum_congr rfl
  intro t ht
  calc
    _ = ∑ u ∈ T, if t=u then w t*w u*invOddsProd ν t else 0 := by
      apply sum_congr rfl
      intro u hu
      rw [pairFunctional_main (hT t ht) (hT u hu) ν hν, mul_ite, mul_zero]
    _ = _ := by simp [ht, pow_two]

/-- A general quadratic certificate. The pairwise distribution errors remain
hypotheses; this lemma does not presume independence of arithmetic events. -/
theorem quadratic_certificate (A : Finset α) (s : Finset ι) (b : ι → α → Prop)
    (ν : ι → ℝ) (hν : ∀ p ∈ s, ν p ≠ 0)
    (T : Finset (Finset ι)) (hT : ∀ t ∈ T, t ⊆ s)
    (w : Finset ι → ℝ) (hw : ∀ t ∈ T, 0 ≤ w t) (hw1 : ∑ t ∈ T, w t = 1)
    (X E : ℝ)
    (hE : ∀ t ∈ T, ∀ u ∈ T,
      |pairFunctional ν (jointCount A b) t u -
        X*pairFunctional ν (nuProd ν) t u| ≤ E) :
    (survivors A s b).card ≤ X*(∑ t ∈ T, (w t)^2*invOddsProd ν t)+E := by
  have hbound : (survivors A s b).card ≤ ∑ n ∈ A, combination ν T w (hit b n)^2 := by
    rw [survivors, card_filter]
    push_cast
    apply sum_le_sum
    intro n hn
    split_ifs with h
    · have he : combination ν T w (hit b n) = 1 := by
        rw [combination]
        convert hw1 using 1
        apply sum_congr rfl
        intro t ht
        have hb : basis ν t (hit b n) = 1 := by
          apply prod_eq_one
          intro p hp
          simp [hit, h p (hT t ht hp)]
        rw [hb, mul_one]
      simp [he]
    · exact sq_nonneg _
  have hsum : (∑ n ∈ A, combination ν T w (hit b n)^2) =
      ∑ t ∈ T, ∑ u ∈ T, w t*w u*pairFunctional ν (jointCount A b) t u := by
    simp_rw [combination_sq]
    rw [sum_comm]
    apply sum_congr rfl
    intro t ht
    rw [sum_comm]
    apply sum_congr rfl
    intro u hu
    rw [← mul_sum, sum_basis_product]
  apply hbound.trans
  rw [hsum]
  calc
    _ ≤ ∑ t ∈ T, ∑ u ∈ T,
        w t*w u*(X*pairFunctional ν (nuProd ν) t u+E) := by
      apply sum_le_sum
      intro t ht
      apply sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw t ht) (hw u hu))
      have hh := (abs_le.mp (hE t ht u hu)).2
      linarith
    _ = X*(∑ t ∈ T, ∑ u ∈ T, w t*w u*pairFunctional ν (nuProd ν) t u)+
        (∑ t ∈ T, w t)*(∑ u ∈ T, w u)*E := by
      simp only [sum_add_distrib, mul_sum, sum_mul, mul_add]
      congr 1 <;> apply sum_congr rfl <;> intro t ht <;>
        apply sum_congr rfl <;> intro u hu <;> ring
    _ = _ := by rw [hw1, combination_main hT ν hν]; ring


lemma oddsProd_pos {s : Finset ι} {ν : ι → ℝ}
    (hν : ∀ p ∈ s, 0 < ν p ∧ ν p < 1) : 0 < oddsProd ν s := by
  apply prod_pos
  intro p hp
  exact div_pos (hν p hp).1 (sub_pos.mpr (hν p hp).2)

lemma oddsProd_mul_invOddsProd {s : Finset ι} {ν : ι → ℝ}
    (hν : ∀ p ∈ s, 0 < ν p ∧ ν p < 1) :
    oddsProd ν s * invOddsProd ν s = 1 := by
  rw [oddsProd, invOddsProd, ← prod_mul_distrib]
  apply prod_eq_one
  intro p hp
  have h0 := (hν p hp).1.ne'
  have h1 := (sub_pos.mpr (hν p hp).2).ne'
  field_simp

/-- Optimal weights in the finite orthogonal basis. -/
theorem selberg_upper (A : Finset α) (s : Finset ι) (b : ι → α → Prop)
    (ν : ι → ℝ) (hν : ∀ p ∈ s, 0 < ν p ∧ ν p < 1)
    (T : Finset (Finset ι)) (hT : ∀ t ∈ T, t ⊆ s)
    (hG : 0 < ∑ t ∈ T, oddsProd ν t) (X E : ℝ)
    (hE : ∀ t ∈ T, ∀ u ∈ T,
      |pairFunctional ν (jointCount A b) t u -
        X*pairFunctional ν (nuProd ν) t u| ≤ E) :
    (survivors A s b).card ≤ X/(∑ t ∈ T, oddsProd ν t)+E := by
  let G := ∑ t ∈ T, oddsProd ν t
  let w : Finset ι → ℝ := fun t => oddsProd ν t/G
  have hw (t : Finset ι) (ht : t ∈ T) : 0 < oddsProd ν t :=
    oddsProd_pos (fun p hp => hν p (hT t ht hp))
  have hw0 (t : Finset ι) (ht : t ∈ T) : 0 ≤ w t := div_nonneg (hw t ht).le hG.le
  have hw1 : ∑ t ∈ T, w t = 1 := by
    change (∑ t ∈ T, oddsProd ν t / G) = 1
    rw [← sum_div, show (∑ t ∈ T, oddsProd ν t) = G from rfl, div_self hG.ne']
  have hmain : (∑ t ∈ T, w t^2 * invOddsProd ν t) = 1/G := by
    calc
      _ = ∑ t ∈ T, oddsProd ν t/G^2 := by
        apply sum_congr rfl
        intro t ht
        have hc := oddsProd_mul_invOddsProd (fun p hp => hν p (hT t ht hp))
        dsimp [w]
        calc
          _ = oddsProd ν t * (oddsProd ν t * invOddsProd ν t) / G^2 := by ring
          _ = _ := by rw [hc, mul_one]
      _ = G/G^2 := by rw [← sum_div]
      _ = _ := by field_simp
  have hh := quadratic_certificate A s b ν (fun p hp => (hν p hp).1.ne')
    T hT w hw0 hw1 X E hE
  rw [hmain] at hh
  simpa only [mul_one_div] using hh

lemma prod_union_le (ρ : ι → ℝ) {d e : Finset ι}
    (hρ : ∀ p ∈ d ∪ e, 1 ≤ ρ p) :
    (∏ p ∈ d ∪ e, ρ p) ≤ (∏ p ∈ d, ρ p)*(∏ p ∈ e, ρ p) := by
  have h0 : 0 ≤ ∏ p ∈ d ∪ e, ρ p := prod_nonneg (fun p hp => (hρ p hp).trans' zero_le_one)
  have h1 : 1 ≤ ∏ p ∈ d ∩ e, ρ p := by
    calc
      _ = ∏ _p ∈ d ∩ e, (1:ℝ) := (prod_const_one).symm
      _ ≤ _ := prod_le_prod (fun _ _ => zero_le_one)
        (fun p hp => hρ p (mem_union_left _ (mem_inter.mp hp).1))
  calc
    _ ≤ (∏ p ∈ d ∪ e, ρ p)*(∏ p ∈ d ∩ e, ρ p) := by nlinarith
    _ = _ := prod_union_inter

lemma multiplicative_pair_error {s t u : Finset ι} (ht : t ⊆ s) (hu : u ⊆ s)
    (ν ρ : ι → ℝ) (hρ : ∀ p ∈ s, 1 ≤ ρ p)
    (C : Finset ι → ℝ) (X : ℝ)
    (hE : ∀ d ⊆ s, |C d-X*nuProd ν d| ≤ ∏ p ∈ d, ρ p) :
    |pairFunctional ν C t u - X*pairFunctional ν (nuProd ν) t u| ≤
      (∑ d ∈ t.powerset, |coefficient ν d| * ∏ p ∈ d, ρ p) *
      (∑ e ∈ u.powerset, |coefficient ν e| * ∏ p ∈ e, ρ p) := by
  apply (pairFunctional_error ν C (fun d => ∏ p ∈ d, ρ p) X ht hu hE).trans
  rw [sum_mul_sum]
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro e he
  have hunion : d ∪ e ⊆ s := union_subset ((mem_powerset.mp hd).trans ht)
    ((mem_powerset.mp he).trans hu)
  have hh := mul_le_mul_of_nonneg_left (prod_union_le ρ (fun p hp => hρ p (hunion hp)))
    (show 0 ≤ |coefficient ν d| * |coefficient ν e| by positivity)
  convert hh using 1 <;> ring

lemma coefficient_abs {ν : ι → ℝ} {d : Finset ι} (hν : ∀ p ∈ d, 0 < ν p) :
    |coefficient ν d| = 1/nuProd ν d := by
  simp only [coefficient, abs_div, abs_pow, abs_neg, abs_one, one_pow]
  rw [nuProd, abs_of_pos (prod_pos hν)]

lemma coefficient_error_sum {ν ρ : ι → ℝ} {t : Finset ι}
    (hν : ∀ p ∈ t, 0 < ν p) :
    (∑ d ∈ t.powerset, |coefficient ν d| * ∏ p ∈ d, ρ p) =
      ∏ p ∈ t, (1+ρ p/ν p) := by
  rw [prod_one_add]
  apply sum_congr rfl
  intro d hd
  rw [coefficient_abs (fun p hp => hν p (mem_powerset.mp hd hp)), nuProd, prod_div_distrib]
  ring

lemma pair_error_modulus_bound {s t u : Finset ι} (ht : t ⊆ s) (hu : u ⊆ s)
    (ν ρ q : ι → ℝ) (hν : ∀ p ∈ s, 0 < ν p) (hρ : ∀ p ∈ s, 1 ≤ ρ p)
    (hq : ∀ p ∈ s, 2 ≤ q p) (heq : ∀ p ∈ s, ρ p/ν p=q p)
    (C : Finset ι → ℝ) (X : ℝ)
    (hE : ∀ d ⊆ s, |C d-X*nuProd ν d| ≤ ∏ p ∈ d, ρ p)
    {z : ℝ} (htz : (∏ p ∈ t, q p) ≤ z) (huz : (∏ p ∈ u, q p) ≤ z) :
    |pairFunctional ν C t u - X*pairFunctional ν (nuProd ν) t u| ≤ z^4 := by
  have hbound (v : Finset ι) (hv : v ⊆ s) (hvz : (∏ p ∈ v, q p) ≤ z) :
      (∏ p ∈ v, (1+ρ p/ν p)) ≤ z^2 := by
    calc
      _ = ∏ p ∈ v, (1+q p) := prod_congr rfl (fun p hp => by rw [heq p (hv hp)])
      _ ≤ ∏ p ∈ v, (q p)^2 := prod_le_prod
        (fun p hp => by have := hq p (hv hp); linarith)
        (fun p hp => by have := hq p (hv hp); nlinarith)
      _ = (∏ p ∈ v, q p)^2 := (prod_pow _ _ _)
      _ ≤ _ := pow_le_pow_left₀ (prod_nonneg (fun p hp => by have := hq p (hv hp); linarith)) hvz 2
  have hu0 : 0 ≤ ∏ p ∈ u, (1+ρ p/ν p) := prod_nonneg (fun p hp => by
    rw [heq p (hu hp)]; have := hq p (hu hp); linarith)
  have he := multiplicative_pair_error ht hu ν ρ hρ C X hE
  rw [coefficient_error_sum (fun p hp => hν p (ht hp)),
    coefficient_error_sum (fun p hp => hν p (hu hp))] at he
  exact he.trans ((mul_le_mul (hbound t ht htz) (hbound u hu huz)
    hu0 (sq_nonneg z)).trans_eq (by ring))

end Erdos371FiniteSelberg

#print axioms Erdos371FiniteSelberg.selberg_upper
#print axioms Erdos371FiniteSelberg.pair_error_modulus_bound
