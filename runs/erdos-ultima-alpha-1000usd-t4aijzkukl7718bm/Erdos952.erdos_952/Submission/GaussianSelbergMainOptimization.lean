import Submission.GaussianRootCRT
import Submission.FiniteSelbergOptimization
import Submission.FiniteSelbergWeights

/-! The exact finite Selberg optimization instantiated with actual Gaussian
polynomial root densities. All local collisions remain in the root counts.
These theorems optimize the main term, not the accompanying lattice error. -/
namespace Erdos952Investigation.GaussianSelbergMainOptimization
open GaussianIdealRepresentatives GaussianPolynomialBoxCounts GaussianWeightedSieve GaussianRootCRT
open FiniteSelbergOptimization FiniteSelbergWeights
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0
local instance : GCDMonoid GaussianInt := EuclideanDomain.gcdMonoid GaussianInt

variable {ι : Type*}

def modulus (g : ι → GaussianInt) (s : Finset ι) : GaussianInt := ∏ i ∈ s, g i

def localDensity (P : Polynomial GaussianInt) (g : GaussianInt) : ℝ :=
  (rho P g : ℝ)/(g.norm.natAbs : ℝ)

lemma modulus_ne_zero (g : ι → GaussianInt) (h0 : ∀ i, g i ≠ 0) (s : Finset ι) :
    modulus g s ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => h0 i)

lemma rho_associated (P : Polynomial GaussianInt) (a b : GaussianInt)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Associated a b) : rho P a = rho P b := by
  have he : multiples a = multiples b := by
    ext z
    simp only [mem_multiples_iff]
    exact h.dvd_iff_dvd_left
  let e := Submodule.quotEquivOfEq (multiples a) (multiples b) he
  have hr (q : GaussianInt ⧸ multiples a) :
      q ∈ rootClasses a ha P ↔ e q ∈ rootClasses b hb P := by
    obtain ⟨t,rfl⟩ := (Submodule.Quotient.mk_surjective (multiples a)) q
    rw [Submodule.quotEquivOfEq_mk,mem_rootClasses,mem_rootClasses]
    exact h.dvd_iff_dvd_left
  rw [rho_of_ne_zero P a ha,rho_of_ne_zero P b hb,rootCount_card,rootCount_card]
  exact Nat.card_congr (e.toEquiv.subtypeEquiv hr)

lemma localDensity_associated (P : Polynomial GaussianInt) (a b : GaussianInt)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Associated a b) : localDensity P a = localDensity P b := by
  rw [localDensity,localDensity,rho_associated P a b ha hb h,
    Zsqrtd.norm_eq_of_associated (by norm_num : (-1 : ℤ) ≤ 0) h]

lemma density_modulus (g : ι → GaussianInt) (h0 : ∀ i, g i ≠ 0)
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (P : Polynomial GaussianInt) (s : Finset ι) :
    localDensity P (modulus g s) = mass (fun i => localDensity P (g i)) s := by
  have hn : (modulus g s).norm.natAbs = ∏ i ∈ s, (g i).norm.natAbs := by
    change (Zsqrtd.normMonoidHom (∏ i ∈ s, g i)).natAbs = _
    rw [map_prod]
    exact map_prod Int.natAbsHom _ _
  unfold localDensity mass
  rw [hn,Nat.cast_prod,modulus,rho_prod g h0 hc,Nat.cast_prod,Finset.prod_div_distrib]

lemma lcm_modulus_associated_union (g : ι → GaussianInt)
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j))) (s t : Finset ι) :
    Associated (lcm (modulus g s) (modulus g t)) (modulus g (s∪t)) := by
  apply associated_of_dvd_dvd
  · exact lcm_dvd
      (Finset.prod_dvd_prod_of_subset s (s∪t) g Finset.subset_union_left)
      (Finset.prod_dvd_prod_of_subset t (s∪t) g Finset.subset_union_right)
  · apply Finset.prod_dvd_of_coprime (fun _ _ _ _ hne => hc hne)
    intro i hi
    rcases Finset.mem_union.mp hi with hs | ht
    · exact (Finset.dvd_prod_of_mem g hs).trans (dvd_lcm_left _ _)
    · exact (Finset.dvd_prod_of_mem g ht).trans (dvd_lcm_right _ _)

lemma density_lcm_modulus (g : ι → GaussianInt) (h0 : ∀ i, g i ≠ 0)
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (P : Polynomial GaussianInt) (s t : Finset ι) :
    localDensity P (lcm (modulus g s) (modulus g t)) =
      mass (fun i => localDensity P (g i)) (s∪t) := by
  have hl : lcm (modulus g s) (modulus g t) ≠ 0 := by
    simp only [ne_eq,lcm_eq_zero_iff,not_or]
    exact ⟨modulus_ne_zero g h0 s,modulus_ne_zero g h0 t⟩
  rw [localDensity_associated P _ _ hl (modulus_ne_zero g h0 (s∪t))
    (lcm_modulus_associated_union g hc s t),density_modulus g h0 hc]

def indexedMain (D : Finset (Finset ι)) (g : ι → GaussianInt)
    (P : Polynomial GaussianInt) (w : D → ℝ) : ℝ :=
  ∑ s : D, ∑ t : D, w s*w t*localDensity P (lcm (modulus g s.val) (modulus g t.val))

lemma indexedMain_eq (D : Finset (Finset ι)) (g : ι → GaussianInt) (h0 : ∀ i, g i ≠ 0)
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (P : Polynomial GaussianInt) (w : D → ℝ) :
    indexedMain D g P w = main D (fun i => localDensity P (g i)) w := by
  simp only [indexedMain,main,density_lcm_modulus g h0 hc]

/-- Optimal Gaussian main term, with the hypotheses 0<rho(g)<norm(g)
retained explicitly. The support family must be downward-closed. -/
theorem gaussian_main_lower_bound (D : Finset (Finset ι)) (hD : DownClosed D)
    (hD0 : ∅ ∈ D) (g : ι → GaussianInt) (h0 : ∀ i, g i ≠ 0)
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (P : Polynomial GaussianInt) (hρ : ∀ i, 0 < rho P (g i) ∧ rho P (g i) < (g i).norm.natAbs)
    (w : D → ℝ) (hw : w ⟨∅,hD0⟩ = 1) :
    1/denominator D (fun i => localDensity P (g i)) ≤ indexedMain D g P w := by
  rw [indexedMain_eq D g h0 hc]
  apply reciprocal_denominator_le_main D hD hD0 _ _ w hw
  intro i
  have hm : (0 : ℝ) < (g i).norm.natAbs := by
    exact_mod_cast (lt_trans (hρ i).1 (hρ i).2)
  constructor
  · exact div_pos (by exact_mod_cast (hρ i).1) hm
  · exact (div_lt_one hm).mpr (by exact_mod_cast (hρ i).2)

theorem gaussian_main_optimal_weights (D : Finset (Finset ι)) (hD : DownClosed D)
    (hD0 : ∅ ∈ D) (g : ι → GaussianInt) (h0 : ∀ i, g i ≠ 0)
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (P : Polynomial GaussianInt) (hρ : ∀ i, 0 < rho P (g i) ∧ rho P (g i) < (g i).norm.natAbs) :
    ∃ w : D → ℝ, w ⟨∅,hD0⟩ = 1 ∧
      indexedMain D g P w = 1/denominator D (fun i => localDensity P (g i)) := by
  have hν (i) : 0 < localDensity P (g i) ∧ localDensity P (g i) < 1 := by
    have hm : (0 : ℝ) < (g i).norm.natAbs := by
      exact_mod_cast (lt_trans (hρ i).1 (hρ i).2)
    exact ⟨div_pos (by exact_mod_cast (hρ i).1) hm,
      (div_lt_one hm).mpr (by exact_mod_cast (hρ i).2)⟩
  obtain ⟨w,hw,he⟩ := exists_optimal_weights D hD hD0 _ hν
  exact ⟨w,hw,(indexedMain_eq D g h0 hc P w).trans he⟩


lemma reciprocal_mass_le_norm (g : ι → GaussianInt) (h0 : ∀ i, g i ≠ 0)
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (P : Polynomial GaussianInt) (hρ : ∀ i, 0 < rho P (g i)) (s : Finset ι) :
    1/mass (fun i => localDensity P (g i)) s ≤ ((modulus g s).norm.natAbs : ℝ) := by
  have hp : 0 < rho P (modulus g s) := by
    rw [modulus,rho_prod g h0 hc]
    exact Finset.prod_pos (fun i _ => hρ i)
  have hp' : (0 : ℝ) < rho P (modulus g s) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ rho P (modulus g s) := by exact_mod_cast hp
  have hn : (0 : ℝ) ≤ (modulus g s).norm.natAbs := Nat.cast_nonneg _
  rw [← density_modulus g h0 hc P s,localDensity,one_div_div]
  apply (div_le_iff₀ hp').mpr
  nlinarith

lemma gaussian_optimalWeights_bound (D : Finset (Finset ι)) (hD0 : ∅ ∈ D)
    (g : ι → GaussianInt) (h0 : ∀ i, g i ≠ 0)
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (P : Polynomial GaussianInt) (hρ : ∀ i, 0 < rho P (g i) ∧ rho P (g i) < (g i).norm.natAbs)
    (s : D) :
    |optimalWeights D (fun i => localDensity P (g i)) s| ≤ ((modulus g s.val).norm.natAbs : ℝ) := by
  apply (abs_optimalWeights_le D hD0 _ _ s).trans
    (reciprocal_mass_le_norm g h0 hc P (fun i => (hρ i).1) s.val)
  intro i
  have hm : (0 : ℝ) < (g i).norm.natAbs := by exact_mod_cast lt_trans (hρ i).1 (hρ i).2
  exact ⟨div_pos (by exact_mod_cast (hρ i).1) hm,
    (div_lt_one hm).mpr (by exact_mod_cast (hρ i).2)⟩

lemma modulus_injective (g : ι → GaussianInt) (hg : ∀ i, Prime (g i))
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j))) : Function.Injective (modulus g) := by
  classical
  have hd (i : ι) (s : Finset ι) : g i ∣ modulus g s ↔ i ∈ s := by
    constructor
    · intro h
      obtain ⟨j,hj,hd⟩ := ((hg i).dvd_finset_prod_iff g).mp h
      have he : i = j := by
        by_contra hn
        exact (hg i).not_unit ((hc hn).isUnit_of_dvd hd)
      simpa only [he] using hj
    · intro hi
      exact Finset.dvd_prod_of_mem g hi
  intro s t he
  ext i
  rw [← hd i s,← hd i t,he]

def modulusSupport (D : Finset (Finset ι)) (g : ι → GaussianInt) : Finset GaussianInt :=
  D.image (modulus g)

/-- Reindex the previously verified Gaussian Lambda-squared main sum by
squarefree prime supports. This is an equality with the original sieve
expression, not just a new analogous quadratic form. -/
lemma mainSum_eq_indexed (D : Finset (Finset ι)) (g : ι → GaussianInt)
    (hg : ∀ i, Prime (g i)) (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (P : Polynomial GaussianInt) (W : GaussianInt → ℝ) :
    mainSum (modulusSupport D g) W P = indexedMain D g P (fun s => W (modulus g s.val)) := by
  have hi := modulus_injective g hg hc
  unfold mainSum modulusSupport
  rw [Finset.sum_image hi.injOn]
  simp_rw [Finset.sum_image hi.injOn]
  have hsum (F : Finset ι → Finset ι → ℝ) :
      (∑ s : D, ∑ t : D, F s.val t.val) = ∑ s ∈ D, ∑ t ∈ D, F s t := by
    rw [Finset.sum_coe_sort D (fun s => ∑ t : D, F s t.val)]
    exact Finset.sum_congr rfl (fun s _ => Finset.sum_coe_sort D (F s))
  simpa only [indexedMain,localDensity,mul_div_assoc] using
    (hsum (fun s t => W (modulus g s)*W (modulus g t)*
      localDensity P (lcm (modulus g s) (modulus g t)))).symm

/-- There are weights for the ORIGINAL Gaussian sieve with exact optimal
main term and a norm bound at every supported modulus. No error estimate is
suppressed in transferring these weights to a counting theorem. -/
theorem exists_gaussian_sieve_weights (D : Finset (Finset ι)) (hD : DownClosed D)
    (hD0 : ∅ ∈ D) (g : ι → GaussianInt) (hg : ∀ i, Prime (g i))
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (P : Polynomial GaussianInt) (hρ : ∀ i, 0 < rho P (g i) ∧ rho P (g i) < (g i).norm.natAbs) :
    ∃ W : GaussianInt → ℝ, W 1 = 1 ∧
      mainSum (modulusSupport D g) W P = 1/denominator D (fun i => localDensity P (g i)) ∧
      ∀ d ∈ modulusSupport D g, |W d| ≤ (d.norm.natAbs : ℝ) := by
  let ν : ι → ℝ := fun i => localDensity P (g i)
  have hν (i : ι) : 0 < ν i ∧ ν i < 1 := by
    have hm : (0 : ℝ) < (g i).norm.natAbs := by exact_mod_cast lt_trans (hρ i).1 (hρ i).2
    exact ⟨div_pos (by exact_mod_cast (hρ i).1) hm,
      (div_lt_one hm).mpr (by exact_mod_cast (hρ i).2)⟩
  let w := optimalWeights D ν
  let f : D → GaussianInt := fun s => modulus g s.val
  have hf : Function.Injective f := (modulus_injective g hg hc).comp Subtype.val_injective
  let W : GaussianInt → ℝ := Function.extend f w (fun _ => 0)
  have he (s : D) : W (modulus g s.val) = w s := hf.extend_apply _ _ _
  refine ⟨W,?_,?_,?_⟩
  · simpa only [modulus,Finset.prod_empty] using (he ⟨∅,hD0⟩).trans (optimalWeights_empty D hD0 ν hν)
  · rw [mainSum_eq_indexed D g hg hc P W]
    have hfun : (fun s : D => W (modulus g s.val)) = w := funext he
    rw [hfun,indexedMain_eq D g (fun i => (hg i).ne_zero) hc]
    exact optimalWeights_main D hD hD0 ν hν
  · intro d hd
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hd
    rw [he ⟨s,hs⟩]
    exact gaussian_optimalWeights_bound D hD0 g (fun i => (hg i).ne_zero) hc P hρ ⟨s,hs⟩

#print axioms gaussian_optimalWeights_bound
#print axioms exists_gaussian_sieve_weights

#print axioms gaussian_main_lower_bound
#print axioms gaussian_main_optimal_weights
end
end Erdos952Investigation.GaussianSelbergMainOptimization
