import Submission.WeightedSelbergSharpSource
import Submission.BuchstabLocalCost

/-! Normalizer-sensitive source costs for the existing Buchstab main terms.
The cost is the squared exact ordinary coefficient norm. All propagation
still uses the maximum of incurred errors, never the selected main's cost. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
set_option maxHeartbeats 0

noncomputable def sharpSelbergCost (p : ℕ → ℕ) (k : ℕ) (D : ℝ) : ℝ :=
  kernelCost (fun i : Fin k => 1/(p i.val : ℝ))
    (canonicalOrthogonal (fun i : Fin k => 1/(p i.val : ℝ))
      (divisorSupport (fun i : Fin k => p i.val) (selbergCutoff D)))^2

lemma sharpSelbergCost_nonneg (p : ℕ → ℕ) (k : ℕ) (D : ℝ) :
    0 ≤ sharpSelbergCost p k D := sq_nonneg _

lemma sharpSelbergCost_le_old (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (k : ℕ) (D : ℝ) :
    sharpSelbergCost p k D ≤ selbergCost k D := by
  have hR : 0 < selbergCutoff D := (by norm_num : 0 < (1 : ℕ)).trans_le (le_max_left _ _)
  have hpp : Function.Injective (fun i : Fin k => p i.val) := hinj.comp Fin.val_injective
  have hq := prime_marginals (fun i : Fin k => p i.val) (fun i => hp i.val)
  have hc := canonical_cost_le_card _ hq _ (divisorSupport_nonempty _ _ hR)
    (divisorSupport_downward _ (fun i : Fin k => (hp i.val).pos) _)
  have hcard : (((divisorSupport (fun i : Fin k => p i.val) (selbergCutoff D)).card) : ℝ) ≤
      selbergCutoff D := by
    exact_mod_cast divisorSupport_card_le (fun i : Fin k => p i.val) (fun i => hp i.val) hpp _
  exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => abs_nonneg _)) (hc.trans hcard) 2

lemma sharpSelbergCost_le_normalized (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (k : ℕ) (D : ℝ) :
    sharpSelbergCost p k D ≤
      (exp 2 * (selbergCutoff D : ℝ) * selbergBase p k D)^2 := by
  have hR : 0 < selbergCutoff D := (by norm_num : 0 < (1 : ℕ)).trans_le (le_max_left _ _)
  have hh := prime_canonical_cost_le (fun i : Fin k => p i.val) (fun i => hp i.val)
    (hinj.comp Fin.val_injective) (selbergCutoff D) hR
  apply pow_le_pow_left₀ (sum_nonneg (fun _ _ => abs_nonneg _))
  simpa only [selbergBase,mul_one_div] using hh

theorem conditional_selberg_upper_cost {α : Type*} (A : Finset α) (w : α → ℝ)
    (ω : α → ℕ → Bool) (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (x D : ℝ) (K : ℕ)
    (hw : ∀ j ∈ A, 0 ≤ w j)
    (hmoment : ∀ T : Finset ℕ, T ⊆ range K →
      |moment A w ω T-x*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1)
    (k : ℕ) (hk : k ≤ K) (T : Finset ℕ) (hTK : T ⊆ range K)
    (hT : ∀ i ∈ T, k ≤ i) :
    sifted A w ω T k ≤
      (x*∏ i ∈ T, 1/(p i : ℝ))*selbergBase p k (D*∏ i ∈ T, 1/(p i : ℝ))+
        sharpSelbergCost p k (D*∏ i ∈ T, 1/(p i : ℝ)) := by
  classical
  let q : ℕ → ℝ := fun i => 1/(p i : ℝ)
  let R := selbergCutoff (D*∏ i ∈ T, q i)
  let pp : Fin k → ℕ := fun i => p i.val
  let W : α → ℝ := fun j => w j*hit T (ω j)
  let Ω : α → Fin k → Bool := fun j i => ω j i.val
  have hR : 0 < R := (by norm_num : 0 < (1 : ℕ)).trans_le (le_max_left _ _)
  have hpp : Function.Injective pp := hpinj.comp Fin.val_injective
  have hq (i : Fin k) : 0 < q i.val ∧ q i.val < 1 := by
    have hi : (1 : ℝ) < p i.val := by exact_mod_cast (hp i.val).one_lt
    exact ⟨by dsimp [q]; positivity, (div_lt_one (by linarith)).mpr hi⟩
  have hW : ∀ j ∈ A, 0 ≤ W j := fun j hj => mul_nonneg (hw j hj) (hit_nonneg _ _)
  have herr (U : Finset (Fin k)) :
      |(∑ j ∈ A, W j*hitMonomial U (Ω j))-(x*∏ i ∈ T, q i)*∏ i ∈ U, q i.val| ≤ 1 := by
    have hUK : U.image Fin.val ⊆ range K := by
      intro i hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      exact mem_range.mpr (j.isLt.trans_le hk)
    have hdisj : Disjoint T (U.image Fin.val) := by
      rw [disjoint_left]
      intro i hiT hiU
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hiU
      exact (not_lt_of_ge (hT j.val hiT)) j.isLt
    have he := hmoment (T ∪ U.image Fin.val) (union_subset hTK hUK)
    change |moment A w ω (T ∪ U.image Fin.val)-x*∏ i ∈ T ∪ U.image Fin.val, q i| ≤ 1 at he
    rw [prod_union hdisj, prod_image Fin.val_injective.injOn] at he
    simpa only [moment, hit_union_prefix, W, Ω, mul_assoc] using he
  have hs := weighted_survivors_le_cost (fun i : Fin k => q i.val) hq
    (divisorSupport pp R) (divisorSupport_nonempty pp R hR)
    (divisorSupport_downward pp (fun i => (hp i.val).one_lt.le) R)
    A W Ω (x*∏ i ∈ T, q i) hW herr
  convert hs using 1
  · unfold sifted
    apply sum_congr rfl
    intro j hj
    dsimp only [W, Ω]
    rw [avoid_prefix]
    by_cases hh : ∀ i : Fin k, ω j i.val = false <;> simp [hh]
  · simp only [selbergBase,sharpSelbergCost,pp,R,q,mul_one_div]

noncomputable def scaledSharpSelbergCost (p : ℕ → ℕ) (k : ℕ) (D : ℝ) : ℝ :=
  sharpSelbergCost p k (4*D)

lemma scaledSharpSelbergCost_nonneg (p : ℕ → ℕ) (k : ℕ) (D : ℝ) :
    0 ≤ scaledSharpSelbergCost p k D := sharpSelbergCost_nonneg _ _ _

lemma scaledSharpSelbergCost_le_old (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (k : ℕ) (D : ℝ) :
    scaledSharpSelbergCost p k D ≤ scaledSelbergCost k D :=
  sharpSelbergCost_le_old p hp hinj k (4*D)

lemma lowerErrorStep_mono_cost (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (E F : ℕ → ℝ → ℝ) (hEF : ∀ k D, E k D ≤ F k D) (k : ℕ) (D : ℝ) :
    lowerErrorStep q keep E k D ≤ lowerErrorStep q keep F k D := by
  classical
  unfold lowerErrorStep
  split_ifs
  · exact add_le_add le_rfl (sum_le_sum (fun (i : Fin k) _ => hEF i.val (D*q i.val)))
  · rfl

lemma upperError_mono_cost (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (E F : ℕ → ℝ → ℝ) (hEF : ∀ k D, E k D ≤ F k D) (n k : ℕ) (D : ℝ) :
    upperError q keep E n k D ≤ upperError q keep F n k D := by
  induction n generalizing k D with
  | zero => exact hEF k D
  | succ n ih =>
    apply max_le_max (ih k D)
    exact add_le_add le_rfl (sum_le_sum (fun (i : Fin k) _ =>
      lowerErrorStep_mono_cost q keep _ _ ih i.val (D*q i.val)))

/-- The complete improved error is never larger than the old complete error. -/
theorem scaled_sharp_refined_error_le_old (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (n k : ℕ) (D : ℝ) :
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) (scaledSharpSelbergCost p) n) k D ≤
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) scaledSelbergCost n) k D :=
  lowerErrorStep_mono_cost _ _ _ _
    (upperError_mono_cost _ _ _ _ (scaledSharpSelbergCost_le_old p hp hinj) n) k D

/-- A fully charged survivor criterion with unchanged main terms and the
normalizer-sensitive exact source costs. No uniform cost saving is assumed. -/
theorem survivor_of_scaled_sharp_refinement {α : Type*} (A : Finset α) (w : α → ℝ)
    (ω : α → ℕ → Bool) (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hmono : StrictMono p) (x D : ℝ) (K : ℕ) (hx : 0 ≤ x)
    (hw : ∀ j ∈ A, 0 ≤ w j)
    (hmoment : ∀ T : Finset ℕ, T ⊆ range K →
      |moment A w ω T-x*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1)
    (n : ℕ)
    (hpos : lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) (scaledSharpSelbergCost p) n) K D <
      x*lowerStep (fun i => 1/(p i : ℝ)) (primeKeep p)
        (upperMain (fun i => 1/(p i : ℝ)) (primeKeep p) (scaledSelbergBase p) n) K D) :
    ∃ j ∈ A, ∀ i < K, ω j i = false := by
  apply survivor_of_refinement A w ω (fun i => 1/(p i : ℝ)) x D K (primeKeep p)
    (scaledSelbergBase p) (scaledSharpSelbergCost p) hw (fun i => by positivity) hx
    (scaledSharpSelbergCost_nonneg p) hmoment _ n hpos
  intro k hk T hTK hT
  simpa only [scaledSelbergBase,scaledSharpSelbergCost,mul_assoc] using
    conditional_selberg_upper_cost A w ω p hp hmono.injective x (4*D) K hw hmoment k hk T hTK hT

#print axioms conditional_selberg_upper_cost
#print axioms sharpSelbergCost_le_normalized
#print axioms scaled_sharp_refined_error_le_old
#print axioms survivor_of_scaled_sharp_refinement
end Erdos970.RecursiveSieve.Buchstab
