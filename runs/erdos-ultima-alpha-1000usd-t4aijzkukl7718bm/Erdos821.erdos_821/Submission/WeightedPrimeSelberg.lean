import Submission.WeightedSieveKernel
import Submission.SieveUnionError

/-!
# A one-root weighted Selberg bound using an averaged progression error

Grouping by the union of supports retains only a fixed subpower loss.
No uniform maximum of the individual progression discrepancies is needed.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

noncomputable def oneRootDenominator (P : Finset ℕ) (z : ℕ) : ℝ :=
  ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z, ∏ p ∈ S, ((p : ℝ)-1)⁻¹

lemma one_root_local_weight_le_two (p : ℕ) (hp : p.Prime) :
    0 ≤ (1-(p : ℝ)⁻¹)⁻¹ ∧ (1-(p : ℝ)⁻¹)⁻¹ ≤ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hi : (p : ℝ)⁻¹ ≤ 1/2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2) hp2
  have hd : (1/2 : ℝ) ≤ 1-(p : ℝ)⁻¹ := by linarith only [hi]
  refine ⟨inv_nonneg.mpr (by linarith),?_⟩
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/2) hd
  norm_num only [one_div,inv_div,inv_one,div_one] at hh
  exact hh

lemma weighted_selberg_union_error {α : Type*}
    (A : Finset α) (h : α → ℝ) (hh : ∀ x ∈ A, 0 ≤ h x)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℕ) (hz : 1 ≤ z)
    (bad : ℕ → α → Prop) (X : ℝ) (R : ℕ → ℝ)
    (hR : ∀ d ∈ Icc 1 (z^2), 0 ≤ R d)
    (hdist : ∀ U ∈ P.powerset, (∏ p ∈ U, p) ≤ z^2 →
      |(∑ x ∈ A, if ∀ p ∈ U, bad p x then h x else 0)-X/((∏ p ∈ U, p : ℕ) : ℝ)| ≤
        R (∏ p ∈ U, p)) :
    (∑ x ∈ A with ∀ p ∈ P, ¬bad p x, h x) ≤ X*(oneRootDenominator P z)⁻¹+
      ∑ U ∈ P.powerset with (∏ p ∈ U, p) ≤ z^2, (16 : ℝ)^U.card*R (∏ p ∈ U, p) := by
  classical
  let W := P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)
  let V := P.powerset.filter (fun U => (∏ p ∈ U, p) ≤ z^2)
  let v : ℕ → ℝ := fun p => (p : ℝ)⁻¹
  have hWP : W ⊆ P.powerset := filter_subset _ _
  have hW0 : ∅ ∈ W := by simp [W,hz]
  have hdown : ∀ U ∈ W, ∀ S, S ⊆ U → S ∈ W := by
    intro U hU S hSU
    obtain ⟨hUP,hUz⟩ := mem_filter.mp hU
    have hUP' := mem_powerset.mp hUP
    refine mem_filter.mpr ⟨mem_powerset.mpr (hSU.trans hUP'),?_⟩
    exact (prod_le_prod_of_subset_of_one_le' hSU (fun p hp _ => (hP p (hUP' hp)).one_le)).trans hUz
  have hv : ∀ p ∈ P, 0 < v p ∧ v p < 1 := by
    intro p hp
    have hpp : (1 : ℝ)<p := by exact_mod_cast (hP p hp).one_lt
    exact ⟨inv_pos.mpr (by linarith),(inv_lt_one₀ (by linarith)).mpr hpp⟩
  obtain ⟨w,hw0,hwzero,hwlocal,hwmain⟩ := exists_selberg_weights_local P W hWP hW0 hdown v hv
  have hw : ∀ S ∈ W, |w S| ≤ (2 : ℝ)^S.card := by
    intro S hS
    apply (hwlocal S (hWP hS)).trans
    rw [← prod_const]
    exact Finset.prod_le_prod
      (fun p hp => (one_root_local_weight_le_two p (hP p (mem_powerset.mp (hWP hS) hp))).1)
      (fun p hp => (one_root_local_weight_le_two p (hP p (mem_powerset.mp (hWP hS) hp))).2)
  have hmap : ∀ S ∈ W, ∀ T ∈ W, S∪T ∈ V := by
    intro S hS T hT
    have hSP := mem_powerset.mp (hWP hS)
    have hTP := mem_powerset.mp (hWP hT)
    refine mem_filter.mpr ⟨mem_powerset.mpr (union_subset hSP hTP),?_⟩
    exact (prime_union_product_le P S T hP hSP hTP).trans
      ((Nat.mul_le_mul (mem_filter.mp hS).2 (mem_filter.mp hT).2).trans_eq (pow_two z).symm)
  let E : Finset ℕ → α → Prop := fun S x => ∀ p ∈ S, bad p x
  let good : α → Prop := fun x => ∀ p ∈ P, ¬bad p x
  let K : Finset ℕ → Finset ℕ → ℝ := fun S T => ∏ p ∈ S∪T, v p
  let err : Finset ℕ → Finset ℕ → ℝ := fun S T =>
    (∑ x ∈ A, if ∀ p ∈ S∪T, bad p x then h x else 0)-X*K S T
  have hgood : ∀ x ∈ A, good x → (∑ S ∈ W, if E S x then w S else 0)=1 := by
    intro x hx hg
    exact selberg_good_sum_on_support P W hWP hW0 bad w hw0 x hg
  have hcount : ∀ S ∈ W, ∀ T ∈ W,
      (∑ x ∈ A, if E S x ∧ E T x then h x else 0)=X*K S T+err S T := by
    intro S hS T hT
    simp only [err,Finset.forall_mem_union,E]
    ring
  have hmain : (∑ S ∈ W, ∑ T ∈ W, w S*w T*K S T)=(oneRootDenominator P z)⁻¹ := by
    rw [show (∑ S ∈ W, ∑ T ∈ W, w S*w T*K S T)=
        ∑ S ∈ P.powerset, ∑ T ∈ P.powerset, w S*w T*(∏ p ∈ S∪T, v p) from
      selberg_quadratic_restrict_support P W hWP w hwzero v,hwmain]
    simp only [oneRootDenominator,W,v,inv_inv,prod_inv_distrib]
  have herr : ∀ S ∈ W, ∀ T ∈ W, |err S T| ≤ R (∏ p ∈ S∪T, p) := by
    intro S hS T hT
    have hhU := mem_filter.mp (hmap S hS T hT)
    have hh' := hdist (S∪T) hhU.1 hhU.2
    simpa only [err,K,v,prod_inv_distrib,Nat.cast_prod,div_eq_mul_inv] using hh'
  have hR' : ∀ U ∈ V, 0 ≤ R (∏ p ∈ U, p) := by
    intro U hU
    exact hR _ (mem_Icc.mpr ⟨prod_pos
      (fun p hp => (hP p (mem_powerset.mp (mem_filter.mp hU).1 hp)).pos),(mem_filter.mp hU).2⟩)
  have hb := weighted_sifted_le_main_error A W E good w h hh X K err hgood hcount
  rw [hmain] at hb
  apply hb.trans
  apply _root_.add_le_add le_rfl
  apply le_trans _ (weighted_union_error_sum_le W V w (fun U => R (∏ p ∈ U, p)) hmap hw hR')
  apply sum_le_sum
  intro S hS
  apply sum_le_sum
  intro T hT
  exact mul_le_mul_of_nonneg_left (herr S hS T hT) (abs_nonneg _)

/-- The constant depends only on epsilon, not on the prime pool, sifting
length, sequence, residue conditions, or error function. -/
theorem exists_weighted_selberg_mean_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : Type*) (A : Finset α) (h : α → ℝ),
      (∀ x ∈ A, 0 ≤ h x) → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ z : ℕ, 1 ≤ z → ∀ bad : ℕ → α → Prop, ∀ X : ℝ, ∀ R : ℕ → ℝ,
      (∀ d ∈ Icc 1 (z^2), 0 ≤ R d) →
      (∀ U ∈ P.powerset, (∏ p ∈ U, p) ≤ z^2 →
        |(∑ x ∈ A, if ∀ p ∈ U, bad p x then h x else 0)-X/((∏ p ∈ U, p : ℕ) : ℝ)| ≤
          R (∏ p ∈ U, p)) →
      (∑ x ∈ A with ∀ p ∈ P, ¬bad p x, h x) ≤
        X*(oneRootDenominator P z)⁻¹+C*((z^2 : ℕ) : ℝ)^ε*∑ d ∈ Icc 1 (z^2), R d := by
  obtain ⟨C,hC,HC⟩ := exists_union_error_mean_bound ε hε
  refine ⟨C,hC,?_⟩
  intro α A h hh P hP z hz bad X R hR hdist
  exact (weighted_selberg_union_error A h hh P hP z hz bad X R hR hdist).trans
    (_root_.add_le_add le_rfl (HC P hP (z^2) R hR))

end Erdos821.Sieve
