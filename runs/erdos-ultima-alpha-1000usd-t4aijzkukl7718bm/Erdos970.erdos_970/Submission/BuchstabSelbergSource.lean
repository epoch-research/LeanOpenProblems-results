import Submission.WeightedSelbergSource
import Submission.BuchstabRefinementSound
import Submission.BuchstabPrimeCost

/-! A canonical Selberg base source at every rescaled node of Buchstab
refinement. The final criterion charges the entire fixed-depth power budget. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg

noncomputable def selbergCutoff (D : ℝ) : ℕ := max 1 ⌊sqrt D⌋₊

noncomputable def selbergBase (p : ℕ → ℕ) (k : ℕ) (D : ℝ) : ℝ :=
  1 / normalizer (fun i : Fin k => 1/(p i.val : ℝ))
    (divisorSupport (fun i : Fin k => p i.val) (selbergCutoff D))

noncomputable def selbergCost (_k : ℕ) (D : ℝ) : ℝ := (selbergCutoff D : ℝ)^2

lemma selbergCost_nonneg (k : ℕ) (D : ℝ) : 0 ≤ selbergCost k D := sq_nonneg _

lemma selbergCost_le_level (k : ℕ) (D : ℝ) (hD : 1 ≤ D) : selbergCost k D ≤ D := by
  have hr : 1 ≤ sqrt D := by simpa using sqrt_le_sqrt hD
  have hfloor : 1 ≤ ⌊sqrt D⌋₊ := Nat.floor_pos.mpr hr
  have hh := sq_le_sq₀ (Nat.cast_nonneg ⌊sqrt D⌋₊) (sqrt_nonneg D) |>.mpr
    (Nat.floor_le (sqrt_nonneg D))
  simpa only [selbergCost, selbergCutoff, max_eq_right hfloor, sq_sqrt (by linarith : 0 ≤ D)] using hh

lemma hit_union_prefix (k : ℕ) (T : Finset ℕ) (U : Finset (Fin k)) (ω : ℕ → Bool) :
    hit (T ∪ U.image Fin.val) ω = hit T ω * hitMonomial U (fun i => ω i.val) := by
  classical
  simp only [hit, hitMonomial_eq, forall_mem_union, forall_mem_image]
  split_ifs <;> simp_all

lemma avoid_prefix (k : ℕ) (ω : ℕ → Bool) :
    avoid k ω = if ∀ i : Fin k, ω i.val = false then 1 else 0 := by
  have he : (∀ i < k, ω i = false) ↔ ∀ i : Fin k, ω i.val = false := by
    constructor
    · exact fun h i => h i.val i.isLt
    · exact fun h i hi => h ⟨i,hi⟩
  simp only [avoid, he]

/-- The required hits and the forbidden prefix are disjoint. Consequently all
moments of the conditional population are among the original moment hypotheses. -/
theorem conditional_selberg_upper {α : Type*} (A : Finset α) (w : α → ℝ)
    (ω : α → ℕ → Bool) (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (x D : ℝ) (K : ℕ)
    (hw : ∀ j ∈ A, 0 ≤ w j)
    (hmoment : ∀ T : Finset ℕ, T ⊆ range K →
      |moment A w ω T-x*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1)
    (k : ℕ) (hk : k ≤ K) (T : Finset ℕ) (hTK : T ⊆ range K)
    (hT : ∀ i ∈ T, k ≤ i) :
    sifted A w ω T k ≤
      (x*∏ i ∈ T, 1/(p i : ℝ))*selbergBase p k (D*∏ i ∈ T, 1/(p i : ℝ))+
        selbergCost k (D*∏ i ∈ T, 1/(p i : ℝ)) := by
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
  have hs := weighted_survivors_le (fun i : Fin k => q i.val) hq
    (divisorSupport pp R) (divisorSupport_nonempty pp R hR)
    (divisorSupport_downward pp (fun i => (hp i.val).one_lt.le) R)
    A W Ω (x*∏ i ∈ T, q i) hW herr
  have hs : sifted A w ω T k ≤
      (x*∏ i ∈ T, q i)/normalizer (fun i : Fin k => q i.val) (divisorSupport pp R)+
        ((divisorSupport pp R).card : ℝ)^2 := by
    convert hs using 1
    unfold sifted
    apply sum_congr rfl
    intro j hj
    dsimp only [W, Ω]
    rw [avoid_prefix]
    by_cases hh : ∀ i : Fin k, ω j i.val = false <;> simp [hh]
  have hcR : ((divisorSupport pp R).card : ℝ) ≤ R := by
    exact_mod_cast divisorSupport_card_le pp (fun i => hp i.val) hpp R
  have hsq := sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg R) |>.mpr hcR
  apply hs.trans
  change (x*∏ i ∈ T, q i)/normalizer (fun i : Fin k => q i.val) (divisorSupport pp R)+
    ((divisorSupport pp R).card : ℝ)^2 ≤
      (x*∏ i ∈ T, q i)*(1/normalizer (fun i : Fin k => q i.val) (divisorSupport pp R))+(R : ℝ)^2
  simpa only [mul_one_div] using add_le_add (le_refl _) hsq

/-- Canonical fixed-depth refinement, now with an unconditional valid base
source. A positive main term by itself is NOT sufficient: the displayed power
budget must be smaller than the expected surviving mass. -/
theorem survivor_of_selberg_refinement {α : Type*} (A : Finset α) (w : α → ℝ)
    (ω : α → ℕ → Bool) (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hmono : StrictMono p) (x D : ℝ) (K : ℕ) (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hw : ∀ j ∈ A, 0 ≤ w j)
    (hmoment : ∀ T : Finset ℕ, T ⊆ range K →
      |moment A w ω T-x*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1)
    (a : ℝ) (ha : 1 < a) (n : ℕ)
    (hpos : (1+reciprocalPowerConstant a)^(2*n+1)*D^a <
      x*lowerStep (fun i => 1/(p i : ℝ)) (primeKeep p)
        (upperMain (fun i => 1/(p i : ℝ)) (primeKeep p) (selbergBase p) n) K D) :
    ∃ j ∈ A, ∀ i < K, ω j i = false := by
  apply survivor_of_refinement A w ω (fun i => 1/(p i : ℝ)) x D K (primeKeep p)
    (selbergBase p) selbergCost hw (fun i => by positivity) hx selbergCost_nonneg hmoment
      (fun k hk T hTK hT => conditional_selberg_upper A w ω p hp hmono.injective x D K
        hw hmoment k hk T hTK hT) n
  exact (prime_refined_lowerError_le p hp hmono selbergCost selbergCost_le_level a ha n K D hD).trans_lt hpos

#print axioms conditional_selberg_upper
#print axioms survivor_of_selberg_refinement
end Erdos970.RecursiveSieve.Buchstab
