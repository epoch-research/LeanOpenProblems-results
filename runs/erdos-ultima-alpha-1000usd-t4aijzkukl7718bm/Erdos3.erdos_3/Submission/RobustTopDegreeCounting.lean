import Submission.TopDegreeFiberCounting

/-! Robust top-degree model counting on a positive-mass coefficient set. The
lower factor need only be approximately constant, replacing the single zero
coefficient by an entire set of approximate returns. -/
namespace Erdos3RobustTopDegreeCounting
open Finset Erdos3TopDegreeFiberCounting Erdos3FiniteSamplingMoments Erdos3EvenPolynomialModel
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

lemma abs_prod_sub_prod_le {I : Type*} (s : Finset I) (f g : I → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i)-(∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i-g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfS : ∀ j ∈ s, |f j| ≤ 1 := fun j hj ↦ hf j (mem_insert_of_mem hj)
    have hgS : ∀ j ∈ s, |g j| ≤ 1 := fun j hj ↦ hg j (mem_insert_of_mem hj)
    have hgp : |∏ j ∈ s, g j| ≤ 1 := by
      rw [abs_prod]
      exact prod_le_one (fun j _ ↦ abs_nonneg _) hgS
    rw [prod_insert hi,prod_insert hi,sum_insert hi]
    calc
      _ = |f i*((∏ j ∈ s, f j)-(∏ j ∈ s, g j))+(f i-g i)*(∏ j ∈ s, g j)| := by congr 1; ring
      _ ≤ |f i| *|(∏ j ∈ s, f j)-(∏ j ∈ s, g j)| +|f i-g i| *|∏ j ∈ s, g j| := by
        simpa only [abs_mul] using abs_add_le
          (f i*((∏ j ∈ s, f j)-(∏ j ∈ s, g j))) ((f i-g i)*(∏ j ∈ s, g j))
      _ ≤ (∑ j ∈ s, |f j-g j|)+|f i-g i| := by
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_right (hf i (mem_insert_self _ _)) (abs_nonneg _)).trans
            (by simpa only [one_mul] using ih hfS hgS)
        · exact (mul_le_mul_of_nonneg_left hgp (abs_nonneg _)).trans_eq (mul_one _)
      _ = _ := add_comm _ _

lemma set_slice_le_expect {C : Type*} [Fintype C] (S : Finset C)
    (g : C → ℝ) (hg : ∀ c, 0 ≤ g c) (B : ℝ) (hB : ∀ c ∈ S, B ≤ g c) :
    (S.card : ℝ)/(Fintype.card C : ℝ)*B ≤ 𝔼 c : C, g c := by
  rw [Fintype.expect_eq_sum_div_card]
  calc
    _ = (∑ _c ∈ S, B)/(Fintype.card C : ℝ) := by simp; ring
    _ ≤ (∑ c ∈ S, g c)/(Fintype.card C : ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum hB) (Nat.cast_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_right
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun c _ _ ↦ hg c)) (Nat.cast_nonneg _)

variable {H Q C : Type*} [Fintype H] [Nonempty H]
variable [AddCommGroup Q] [Fintype Q] [Fintype C]

/-- The lower-factor error is paid once per configuration position; the mass
of all good coefficients multiplies the resulting top-degree count. -/
theorem robust_fibered_count (m : ℕ) (M : H → C → Fin (2*m+2) → H)
    (f : H → Q → ℝ) (hf : ∀ a z, 0 ≤ f a z ∧ f a z ≤ 1)
    (S : Finset C) {τ : ℝ}
    (hflat : ∀ c ∈ S, ∀ a j z, |f (M a c j) z-f a z| ≤ τ) :
    (S.card : ℝ)/(Fintype.card C : ℝ)*
      ((𝔼 a : H, 𝔼 z : Q, f a z)^(2*m+2)-(2*m+2 : ℕ)*τ) ≤ fiberedEvenCount m M f := by
  let β : ℝ := (S.card : ℝ)/(Fintype.card C : ℝ)
  have hβ : 0 ≤ β := by positivity
  have hlocal (a : H) (c : C) (hc : c ∈ S) :
      (𝔼 z : Q, f a z)^(2*m+2)-(2*m+2 : ℕ)*τ ≤
      𝔼 p : Q × (Fin m → Q) × (Fin m → Q),
        ∏ j : Fin (2*m+2), f (M a c j) (evenPolynomial m p j.val) := by
    have hp (p : Q × (Fin m → Q) × (Fin m → Q)) :
        (∏ j : Fin (2*m+2), f a (evenPolynomial m p j.val))-(2*m+2 : ℕ)*τ ≤
        ∏ j : Fin (2*m+2), f (M a c j) (evenPolynomial m p j.val) := by
      have hd := abs_prod_sub_prod_le univ
        (fun j : Fin (2*m+2) ↦ f (M a c j) (evenPolynomial m p j.val))
        (fun j : Fin (2*m+2) ↦ f a (evenPolynomial m p j.val))
        (fun j _ ↦ by simpa only [abs_of_nonneg (hf _ _).1] using (hf (M a c j) (evenPolynomial m p j.val)).2)
        (fun j _ ↦ by simpa only [abs_of_nonneg (hf _ _).1] using (hf a (evenPolynomial m p j.val)).2)
      have hs : (∑ j : Fin (2*m+2), |f (M a c j) (evenPolynomial m p j.val)-f a (evenPolynomial m p j.val)|) ≤
          (2*m+2 : ℕ)*τ := by
        calc
          _ ≤ ∑ _j : Fin (2*m+2), τ := sum_le_sum (fun j _ ↦ hflat c hc a j _)
          _ = _ := by simp
      have hh := (abs_le.mp (hd.trans hs)).1
      linarith
    have hmean := expect_le_expect (s := univ) (fun p _ ↦ hp p)
    rw [expect_sub_distrib,Fintype.expect_const] at hmean
    exact (sub_le_sub_right (even_polynomial_model_lower m (f a)) _).trans hmean
  have hs (a : H) : β*((𝔼 z : Q, f a z)^(2*m+2)-(2*m+2 : ℕ)*τ) ≤
      𝔼 c : C, 𝔼 p : Q × (Fin m → Q) × (Fin m → Q),
        ∏ j : Fin (2*m+2), f (M a c j) (evenPolynomial m p j.val) :=
    set_slice_le_expect S _
      (fun c ↦ expect_nonneg (fun p _ ↦ prod_nonneg (fun j _ ↦ (hf _ _).1))) _ (hlocal a)
  have hpow := expect_even_pow_le (show Even (2*m+2) from ⟨m+1,by omega⟩) (fun a : H ↦ 𝔼 z : Q, f a z)
  calc
    _ ≤ β*((𝔼 a : H, (𝔼 z : Q, f a z)^(2*m+2))-(2*m+2 : ℕ)*τ) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hpow _) hβ
    _ = 𝔼 a : H, β*((𝔼 z : Q, f a z)^(2*m+2)-(2*m+2 : ℕ)*τ) := by
      rw [← mul_expect,expect_sub_distrib,Fintype.expect_const]
    _ ≤ _ := expect_le_expect (fun a _ ↦ hs a)

#print axioms abs_prod_sub_prod_le
#print axioms robust_fibered_count
end Erdos3RobustTopDegreeCounting
