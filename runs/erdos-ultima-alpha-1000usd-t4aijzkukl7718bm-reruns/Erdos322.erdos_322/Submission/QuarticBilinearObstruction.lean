import Submission.LinearObstruction

/-! A sharp dimension obstruction to bilinear multiplication of quartic norms. -/

namespace Erdos322Research.QuarticBilinear

open Erdos322Research

/-- A bilinear product preserving quartic norms needs at least the product of
its input dimensions. The coordinatewise tensor product attains this bound. -/
theorem output_dimension_ge_product
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    [DecidableEq κ] [DecidableEq ν]
    (M : ι → κ → ν → ℝ) (C : ℝ) (hC : 0 < C)
    (h : ∀ (x : κ → ℝ) (y : ν → ℝ),
      ∑ i, (∑ j, ∑ l, M i j l*x j*y l)^4 =
        C*(∑ j, x j^4)*(∑ l, y l^4)) :
    Fintype.card κ * Fintype.card ν ≤ Fintype.card ι := by
  classical
  let eK (j : κ) : κ → ℝ := fun k ↦ if k=j then 1 else 0
  let eL (l : ν) : ν → ℝ := fun k ↦ if k=l then 1 else 0
  have he (j : κ) (l : ν) : ∑ i, M i j l^4=C := by
    simpa [eK,eL] using h (eK j) (eL l)
  have hrow (y : ν → ℝ) {j j' : κ} (hj : j ≠ j') (i : ι) :
      (∑ l, M i j l*y l)*(∑ l, M i j' l*y l)=0 := by
    apply quartic_similarity_disjoint (fun i j ↦ ∑ l, M i j l*y l)
      (C*∑ l, y l^4) _ hj i
    intro x
    have hh := h x y
    have heq (i : ι) : (∑ j, (∑ l, M i j l*y l)*x j)=
        ∑ j, ∑ l, M i j l*x j*y l := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    simp_rw [heq]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  have hcol (x : κ → ℝ) {l l' : ν} (hl : l ≠ l') (i : ι) :
      (∑ j, M i j l*x j)*(∑ j, M i j l'*x j)=0 := by
    apply quartic_similarity_disjoint (fun i l ↦ ∑ j, M i j l*x j)
      (C*∑ j, x j^4) _ hl i
    intro y
    have hh := h x y
    have heq (i : ι) : (∑ l, (∑ j, M i j l*x j)*y l)=
        ∑ j, ∑ l, M i j l*x j*y l := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
    simp_rw [heq]
    exact hh
  have hdj {j j' : κ} (hj : j ≠ j') (l l' : ν) (i : ι) :
      M i j l * M i j' l'=0 := by
    have ha : M i j l*M i j' l=0 := by
      simpa [eL] using hrow (eL l) hj i
    have hb : M i j l'*M i j' l'=0 := by
      simpa [eL] using hrow (eL l') hj i
    have hc : (M i j l+M i j l')*(M i j' l+M i j' l')=0 := by
      simpa [eL, mul_add, Finset.sum_add_distrib] using
        hrow (fun k ↦ eL l k+eL l' k) hj i
    by_cases ha0 : M i j l=0
    · simp [ha0]
    have haz : M i j' l=0 := (mul_eq_zero.mp ha).resolve_left ha0
    rw [haz,zero_add] at hc
    nlinarith only [hb,hc]
  have hdl (j : κ) {l l' : ν} (hl : l ≠ l') (i : ι) :
      M i j l * M i j l'=0 := by
    simpa [eK] using hcol (eK j) hl i
  have hn (p : κ × ν) : ∃ i, M i p.1 p.2 ≠ 0 := by
    by_contra hh
    push_neg at hh
    have hz := he p.1 p.2
    simp [hh] at hz
    linarith
  choose f hf using hn
  have hinj : Function.Injective f := by
    intro p q hpq
    by_contra hpne
    have hz : M (f p) p.1 p.2 * M (f p) q.1 q.2=0 := by
      by_cases heq : p.1=q.1
      · have hne : p.2 ≠ q.2 := by
          intro h
          exact hpne (Prod.ext heq h)
        rw [←heq]
        exact hdl p.1 hne (f p)
      · exact hdj heq p.2 q.2 (f p)
    exact (mul_ne_zero (hf p) (by simpa only [hpq] using hf q)) hz
  simpa only [Fintype.card_prod] using Fintype.card_le_of_injective f hinj

/-- In particular, there is no four-coordinate bilinear quartic norm product. -/
theorem no_four_coordinate_product
    (M : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ¬ (∀ (x y : Fin 4 → ℝ),
      ∑ i, (∑ j, ∑ l, M i j l*x j*y l)^4 =
        (∑ j, x j^4)*(∑ l, y l^4)) := by
  intro h
  have hc := output_dimension_ge_product M 1 (by norm_num) (by simpa using h)
  norm_num at hc

end Erdos322Research.QuarticBilinear
