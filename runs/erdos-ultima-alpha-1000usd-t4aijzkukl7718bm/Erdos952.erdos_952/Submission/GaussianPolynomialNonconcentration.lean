import Submission.GaussianFinitePolynomialCover

/-! Coefficient-uniform nonconcentration of bounded-step injective paths in
bounded-degree polynomial images. This does not classify the shapes of prime
paths and does not prove the Gaussian moat conjecture. -/
namespace Erdos952Investigation.GaussianPolynomialNonconcentration
open GaussianPolynomialImageObstruction GaussianPolynomialShortEdges GaussianFinitePolynomialCover
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

/-- Indices of a finite path segment covered by the given polynomial family. -/
def coveredIndices {J : Type*} (P : J → Polynomial GaussianInt)
    (x : ℕ → GaussianInt) (L : ℕ) : Finset ℕ :=
  (Finset.range (L+1)).filter (fun n => ∃ j, x n ∈ Set.range (P j).eval)

lemma coveredIndices_mem {J : Type*} (P : J → Polynomial GaussianInt)
    (x : ℕ → GaussianInt) (L n : ℕ) :
    n ∈ coveredIndices P x L ↔ n ≤ L ∧ ∃ j, x n ∈ Set.range (P j).eval := by
  simp only [coveredIndices,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]

lemma same_bucket_difference_sq_le (H i j : ℕ) (he : i/(H+1) = j/(H+1)) :
    ((j : ℤ)-(i : ℤ))^2 ≤ (H : ℤ)^2 := by
  have hi := Nat.mod_add_div i (H+1)
  have hj := Nat.mod_add_div j (H+1)
  rw [he] at hi
  have hri := Nat.mod_lt i (show 0 < H+1 by omega)
  have hrj := Nat.mod_lt j (show 0 < H+1 by omega)
  have hh : -(H : ℤ) ≤ (j : ℤ)-(i : ℤ) ∧ (j : ℤ)-(i : ℤ) ≤ H := by omega
  nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (sub_nonneg.mpr hh.1)]

/-- All but finitely many covered indices can be injected into
(bucket index, polynomial index). Two indices with the same pair would
produce a short polynomial-image edge and hence enter the exception set. -/
theorem covered_count_le {J : Type*} [Fintype J]
    (P : J → Polynomial GaussianInt) (d : ℕ)
    (hP : ∀ j, 2 ≤ (P j).natDegree ∧ (P j).natDegree ≤ d)
    (x : ℕ → GaussianInt) (C : ℤ) (L H : ℕ)
    (hx : Set.InjOn x (Set.Iic L))
    (hs : ∀ n < L, (x (n+1)-x n).norm ≤ C) :
    (coveredIndices P x L).card ≤
      Fintype.card J*((ball (max C 0*(H : ℤ)^2)).card^2*d)+
        (L/(H+1)+1)*Fintype.card J := by
  let S := coveredIndices P x L
  let B := max C 0*(H : ℤ)^2
  let E := familyCertificate P B
  let A := S.filter (fun n => x n ∈ E)
  let G := S.filter (fun n => x n ∉ E)
  have hS (n : ℕ) (hn : n ∈ S) : n ≤ L ∧ ∃ j, x n ∈ Set.range (P j).eval :=
    (coveredIndices_mem P x L n).mp hn
  have hAcard : A.card ≤ E.card := by
    let f : A → E := fun n => ⟨x n.val,(Finset.mem_filter.mp n.property).2⟩
    have hf : Function.Injective f := by
      intro m n he
      apply Subtype.ext
      exact hx (hS m.val (Finset.mem_filter.mp m.property).1).1
        (hS n.val (Finset.mem_filter.mp n.property).1).1 (congrArg Subtype.val he)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  have hg (n : G) : n.val ≤ L ∧ (∃ j, x n.val ∈ Set.range (P j).eval) ∧ x n.val ∉ E := by
    obtain ⟨hn,hne⟩ := Finset.mem_filter.mp n.property
    exact ⟨(hS n.val hn).1,(hS n.val hn).2,hne⟩
  choose c hc using (fun n : G => (hg n).2.1)
  let f : G → Fin (L/(H+1)+1) × J := fun n =>
    (⟨n.val/(H+1),by have := Nat.div_le_div_right (c := H+1) (hg n).1; omega⟩,c n)
  have hf : Function.Injective f := by
    intro m n he
    have hdiv : m.val/(H+1) = n.val/(H+1) := congrArg (fun v => v.1.val) he
    have hclass : c m = c n := congrArg Prod.snd he
    apply Subtype.ext
    apply hx (hg m).1 (hg n).1
    by_contra hne
    apply (hg m).2.2
    apply mem_familyCertificate P (fun j => (hP j).1) B (c m) _ _ (hc m)
    · simpa only [hclass] using hc n
    · exact hne
    · have hb := norm_displacement_le_on_segment x (max C 0) L
        (fun k hk => (hs k hk).trans (le_max_left _ _)) n.val m.val (hg n).1 (hg m).1
      exact hb.trans (mul_le_mul_of_nonneg_left
        (same_bucket_difference_sq_le H m.val n.val hdiv) (le_max_right _ _))
  have hGcard : G.card ≤ (L/(H+1)+1)*Fintype.card J := by
    simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using
      Fintype.card_le_of_injective f hf
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun n => x n ∈ E)
  change A.card+G.card = S.card at hsplit
  have hEcard := familyCertificate_card_le P d (fun j => (hP j).2) B
  change E.card ≤ _ at hEcard
  dsimp only [B] at hEcard
  change S.card ≤ _
  omega

/-- Polynomial images have uniformly vanishing density along bounded-step
injective segments. The threshold N is independent of the path, its starting
point, and every polynomial coefficient. -/
theorem uniform_polynomial_nonconcentration {J : Type*} [Fintype J]
    (d : ℕ) (C : ℤ) (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ,
    ∀ P : J → Polynomial GaussianInt,
      (∀ j, 2 ≤ (P j).natDegree ∧ (P j).natDegree ≤ d) →
    ∀ x : ℕ → GaussianInt, ∀ L : ℕ, N ≤ L →
      Set.InjOn x (Set.Iic L) →
      (∀ n < L, (x (n+1)-x n).norm ≤ C) →
      ((coveredIndices P x L).card : ℝ) ≤ ε*((L : ℝ)+1) := by
  let K := Fintype.card J
  obtain ⟨H,hH⟩ := exists_nat_gt (2*(K : ℝ)/ε)
  have hHK : 2*(K : ℝ) ≤ ε*((H : ℝ)+1) := by
    have hh := (div_lt_iff₀ hε).mp hH
    nlinarith
  let Q := K*((ball (max C 0*(H : ℤ)^2)).card^2*d)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*((Q : ℝ)+(K : ℝ))/ε)
  refine ⟨N,?_⟩
  intro P hP x L hNL hx hs
  have hc := covered_count_le P d hP x C L H hx hs
  change (coveredIndices P x L).card ≤ Q+(L/(H+1)+1)*K at hc
  have hcR : ((coveredIndices P x L).card : ℝ) ≤
      (Q : ℝ)+(((L/(H+1) : ℕ) : ℝ)+1)*(K : ℝ) := by exact_mod_cast hc
  have hq : (((L/(H+1) : ℕ) : ℝ))*((H : ℝ)+1) ≤ (L : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self L (H+1)
  have hq0 : (0 : ℝ) ≤ ((L/(H+1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsmall : 2*(K : ℝ)*((L/(H+1) : ℕ) : ℝ) ≤ ε*(L : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hHK hq0
    have h2 := mul_le_mul_of_nonneg_left hq hε.le
    nlinarith
  have hconst : 2*((Q : ℝ)+(K : ℝ)) ≤ ε*(L : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp hN
    have hNL' : (N : ℝ) ≤ (L : ℝ) := by exact_mod_cast hNL
    have hm := mul_le_mul_of_nonneg_left hNL' hε.le
    nlinarith
  nlinarith

/-- Indices within a fixed norm-neighborhood of some polynomial image. -/
def nearIndices {J : Type*} (P : J → Polynomial GaussianInt)
    (B : ℤ) (x : ℕ → GaussianInt) (L : ℕ) : Finset ℕ :=
  (Finset.range (L+1)).filter (fun n => ∃ j u, (x n-(P j).eval u).norm ≤ B)

/-- Neighborhoods are handled by finitely many constant-term shifts. This
uniformity also allows the polynomial family to change with segment length. -/
theorem uniform_polynomial_neighborhood_nonconcentration {J : Type*} [Fintype J]
    (d : ℕ) (B C : ℤ) (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ,
    ∀ P : J → Polynomial GaussianInt,
      (∀ j, 2 ≤ (P j).natDegree ∧ (P j).natDegree ≤ d) →
    ∀ x : ℕ → GaussianInt, ∀ L : ℕ, N ≤ L →
      Set.InjOn x (Set.Iic L) →
      (∀ n < L, (x (n+1)-x n).norm ≤ C) →
      ((nearIndices P B x L).card : ℝ) ≤ ε*((L : ℝ)+1) := by
  let T := {t : GaussianInt // t.norm ≤ B}
  letI : Fintype T := (norm_sublevel_finite B).fintype
  obtain ⟨N,hN⟩ := uniform_polynomial_nonconcentration (J := J × T) d C ε hε
  refine ⟨N,?_⟩
  intro P hP x L hNL hx hs
  let Q : J × T → Polynomial GaussianInt := fun j => P j.1+Polynomial.C j.2.val
  have hQ (j : J × T) : 2 ≤ (Q j).natDegree ∧ (Q j).natDegree ≤ d := by
    simpa only [Q,Polynomial.natDegree_add_C] using hP j.1
  have hsame : nearIndices P B x L = coveredIndices Q x L := by
    ext n
    simp only [nearIndices,coveredIndices,Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨j,u,hu⟩
      refine ⟨(j,⟨x n-(P j).eval u,hu⟩),u,?_⟩
      simp only [Q,Polynomial.eval_add,Polynomial.eval_C]
      abel
    · rintro ⟨⟨j,t⟩,u,hu⟩
      refine ⟨j,u,?_⟩
      have he : x n-(P j).eval u = t.val := by
        simp only [Q,Polynomial.eval_add,Polynomial.eval_C] at hu
        rw [← hu]
        abel
      rw [he]
      exact t.property
  rw [hsame]
  exact hN Q hQ x L hNL hx hs

#print axioms uniform_polynomial_nonconcentration
#print axioms uniform_polynomial_neighborhood_nonconcentration
#print axioms same_bucket_difference_sq_le
#print axioms covered_count_le
end
end Erdos952Investigation.GaussianPolynomialNonconcentration
