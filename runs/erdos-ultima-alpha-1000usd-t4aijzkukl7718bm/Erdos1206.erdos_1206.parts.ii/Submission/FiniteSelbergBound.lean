import Submission.FiniteSelbergWeights

/-!
An optimized finite upper sieve for a sample with few local obstructions.
Local distribution estimates and growth of the sieve mass remain hypotheses.
-/
namespace Erdos1206.FiniteSelbergBound
open Finset FiniteThinnedSieve FiniteSelbergWeights
open scoped Classical
variable {ι α : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
lemma restrict_error (P : Finset ι) (D : Finset (Finset ι))
    (lam : Finset ι → ℝ) (e : Finset ι → Finset ι → ℝ)
    (hP : ∀ S ∈ D, S ⊆ P) (hlam : ∀ S, S ∉ D → lam S=0) :
    (∑ S ∈ P.powerset, ∑ T ∈ P.powerset, |lam S*lam T| *e S T) =
      ∑ S ∈ D, ∑ T ∈ D, |lam S*lam T| *e S T := by
  have hsub : D ⊆ P.powerset := fun S hS => mem_powerset.mpr (hP S hS)
  calc
    _ = ∑ S ∈ D, ∑ T ∈ P.powerset, |lam S*lam T| *e S T := by
      symm
      apply sum_subset hsub
      intro S hS hSD
      simp [hlam S hSD]
    _ = _ := by
      apply sum_congr rfl
      intro S hS
      symm
      apply sum_subset hsub
      intro T hT hTD
      simp [hlam T hTD]

/-- The exact optimized bound retains the individual remainder terms. -/
theorem few_hits_selberg (P : Finset ι) (X : Finset α) (G : α → Finset ι)
    (r : ι → ℝ) (M : ℝ) (D : Finset (Finset ι)) (k : ℕ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hr : ∀ p ∈ P, 0 < r p ∧ r p < 1)
    (hG : ∀ x ∈ X, G x ⊆ P) (hP : ∀ S ∈ D, S ⊆ P)
    (hD : ∀ S ∈ D, ∀ U, U ⊆ S → U ∈ D) (h0 : ∅ ∈ D) :
    (((X.filter (fun x => (G x).card ≤ k)).card : ℝ)*(1-q)^k) ≤
      M/sieveMass (fun p => q*r p) D +
      ∑ S ∈ D, ∑ T ∈ D,
        |selbergWeight (fun p => q*r p) D S*selbergWeight (fun p => q*r p) D T| *
          q^((S ∪ T).card)* |remainder X G r M (S ∪ T)| := by
  have hr' (p : ι) (hp : p ∈ P) : 0 < q*r p ∧ q*r p < 1 := by
    refine ⟨mul_pos hq0 (hr p hp).1,?_⟩
    exact (mul_le_of_le_one_left (hr p hp).1.le hq1).trans_lt (hr p hp).2
  have hm := sieveMass_pos P (fun p => q*r p) D hP h0 hr'
  have hh := few_hits_le_main_error P X G r M (selbergWeight (fun p => q*r p) D)
    k hq0.le hq1 hG (selbergWeight_empty _ D hm.ne')
  rw [selbergWeight_main P _ D hP (fun p hp => (hr' p hp).2.ne) hm.ne'] at hh
  have he := restrict_error P D (selbergWeight (fun p => q*r p) D)
    (fun S T => q^((S ∪ T).card)* |remainder X G r M (S ∪ T)|)
    hP (fun S hS => selbergWeight_support _ D hD hS)
  simp only [mul_assoc] at hh he
  rw [he] at hh
  simpa only [div_eq_mul_inv,one_mul,mul_assoc] using hh

/-- A convenient uniform-error form. The coefficient bound L and remainder
bound R are required only on the chosen downward-closed truncation D. -/
theorem few_hits_selberg_uniform (P : Finset ι) (X : Finset α) (G : α → Finset ι)
    (r : ι → ℝ) (M : ℝ) (D : Finset (Finset ι)) (k : ℕ) {q L R : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hr : ∀ p ∈ P, 0 < r p ∧ r p < 1)
    (hG : ∀ x ∈ X, G x ⊆ P) (hP : ∀ S ∈ D, S ⊆ P)
    (hD : ∀ S ∈ D, ∀ U, U ⊆ S → U ∈ D) (h0 : ∅ ∈ D)
    (hL : 0 ≤ L) (_hR : 0 ≤ R)
    (hcoeff : ∀ S ∈ D, (∏ p ∈ S, (1+odds (fun p => q*r p) p)) ≤ L)
    (hrem : ∀ S ∈ D, ∀ T ∈ D, |remainder X G r M (S ∪ T)| ≤ R) :
    (((X.filter (fun x => (G x).card ≤ k)).card : ℝ)*(1-q)^k) ≤
      M/sieveMass (fun p => q*r p) D + (D.card:ℝ)^2*L^2*R := by
  apply (few_hits_selberg P X G r M D k hq0 hq1 hr hG hP hD h0).trans
  refine add_le_add le_rfl ?_
  have hr' (p : ι) (hp : p ∈ P) : 0 < q*r p ∧ q*r p < 1 :=
    ⟨mul_pos hq0 (hr p hp).1,(mul_le_of_le_one_left (hr p hp).1.le hq1).trans_lt (hr p hp).2⟩
  have hm := sieveMass_pos P (fun p => q*r p) D hP h0 hr'
  have hw (S : Finset ι) (hS : S ∈ D) : |selbergWeight (fun p => q*r p) D S| ≤ L :=
    (selbergWeight_abs_le P S _ D hP (hP S hS) hD
      (fun p hp => ⟨(hr' p hp).1.le,(hr' p hp).2⟩) hm).trans (hcoeff S hS)
  calc
    _ ≤ ∑ S ∈ D, ∑ T ∈ D, L^2*R := by
      apply sum_le_sum
      intro S hS
      apply sum_le_sum
      intro T hT
      have hab : |selbergWeight (fun p => q*r p) D S*selbergWeight (fun p => q*r p) D T| ≤ L^2 := by
        rw [abs_mul,pow_two]
        exact mul_le_mul (hw S hS) (hw T hT) (abs_nonneg _) hL
      have hq : q^((S ∪ T).card) ≤ 1 := pow_le_one₀ hq0.le hq1
      have habq : |selbergWeight (fun p => q*r p) D S*selbergWeight (fun p => q*r p) D T| *
          q^((S ∪ T).card) ≤ L^2 := by
        calc
          _ ≤ |selbergWeight (fun p => q*r p) D S*selbergWeight (fun p => q*r p) D T| *1 :=
            mul_le_mul_of_nonneg_left hq (abs_nonneg _)
          _ ≤ _ := by simpa using hab
      exact mul_le_mul habq (hrem S hS T hT) (abs_nonneg _) (sq_nonneg L)
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

#print axioms few_hits_selberg
#print axioms few_hits_selberg_uniform
end Erdos1206.FiniteSelbergBound
