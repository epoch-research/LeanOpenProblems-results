import Submission.ExceptionalScalar

/-!
# Separate bounds for each distortion layer

These bounds do not assume that the base boxes cover. They allow a hybrid
prefix/tail estimate and a separate exceptional box.
-/
namespace Erdos7ExceptionalLayers
open scoped BigOperators
open Erdos7CompressionSieve Erdos7Distortion
set_option maxHeartbeats 5000000

theorem layer_exponent_loss_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (c s : Fin n → ℚ) (r q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1≤c i) (hs : ∀ i, 0 < s i)
    (hr : ∀ i g, g < E i → 0≤r i (g+1))
    (hrs : ∀ i, (∑ g∈Finset.range (E i), r i (g+1))≤s i)
    (hq1 : ∀ i, q i 0≤1) (hqdec : ∀ i g, g < E i → q i (g+1)≤q i g)
    (hqE : ∀ i, q i (E i)=0)
    (hqr : ∀ i g, g < E i → c i*r i (g+1)≤q i g)
    (e : κ → Fin n → ℕ) (heinj : Function.Injective e)
    (he : ∀ k i, e k i≤E i) (hne : ∀ k, (expSupport (e k)).Nonempty)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, e k i≠0 → fraction (X k i)≤r i (e k i))
    (σ : κ → Fin n)
    (hσ : ∀ k, σ k ∈ expSupport (e k))
    (hS : ∀ k j, j ∈ expSupport (e k) → j ≤ σ k) (i : Fin n) :
    (∑ x, towerWeights A (layeredBad A (fun k => expSupport (e k)) X σ) c i.val x *
      Erdos7Distortion.residual (c i)
        (coordinateFraction A i (layeredBad A (fun k => expSupport (e k)) X σ i) x)) ≤
      exponentEnvelope E q (fun x => Erdos7Distortion.residual (c i) (s i*x)) i.val 1 := by
  classical
  let S (k : κ) := expSupport (e k)
  let B := layeredBad A S X σ
  have hc0 : ∀ i, 0≤c i := fun i => (by norm_num : (0:ℚ)≤1).trans (hc i)
  let K := layerFamily σ i
  let Kg (g : ℕ) := K.filter (fun k => e k i=g+1)
  let e' (k : κ) := Function.update (e k) i 0
  let W (k : κ) (x : ∀ j, A j) := boxIndicator A (expSupport (e' k)) (X k) x
  let N (g : ℕ) (x : ∀ j, A j) := ∑ k∈Kg g, W k x
  let φ (x : ℚ) := Erdos7Distortion.residual (c i) (s i*x)
  let G := exponentEnvelope E q φ i.val 1
  have hki (k : κ) (hk : k∈K) : i∈S k := by
    simpa only [(Finset.mem_filter.mp hk).2] using hσ k
  have he' (k : κ) (j : Fin n) : e' k j≤E j := by
    by_cases hj : j=i
    · subst j; simp [e']
    · simpa only [e',Function.update_of_ne hj] using he k j
  have hprev (k : κ) (hk : k∈K) (j : Fin n) (hj : j∈expSupport (e' k)) : j.val < i.val := by
    rw [expSupport_update_zero] at hj
    have hle := hS k j (Finset.mem_erase.mp hj).2
    rw [(Finset.mem_filter.mp hk).2] at hle
    exact (show j < i from lt_of_le_of_ne hle (Finset.mem_erase.mp hj).1)
  have hX' (k : κ) (j : Fin n) (hj : j∈expSupport (e' k)) :
      c j*fraction (X k j)≤q j (e' k j-1) := by
    rw [expSupport_update_zero] at hj
    have hjne := (Finset.mem_erase.mp hj).1
    have hpos := (mem_expSupport _ _).mp (Finset.mem_erase.mp hj).2
    have hEj : e k j-1 < E j := by have := he k j; omega
    have hq := hqr j (e k j-1) hEj
    have heq : e k j-1+1=e k j := by omega
    rw [heq] at hq
    simpa only [e',Function.update_of_ne hjne] using
      (mul_le_mul_of_nonneg_left (hX k j hpos) (hc0 j)).trans hq
  have hmult (g : ℕ) (f : Fin n → ℕ) : ((Kg g).filter (fun k => e' k=f)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro k hk l hl
    obtain ⟨hk,hkf⟩ := Finset.mem_filter.mp hk
    obtain ⟨hl,hlf⟩ := Finset.mem_filter.mp hl
    have hkg := (Finset.mem_filter.mp hk).2
    have hlg := (Finset.mem_filter.mp hl).2
    apply heinj
    funext j
    by_cases hj : j=i
    · subst j; exact hkg.trans hlg.symm
    · have hh := congrFun (hkf.trans hlf.symm) j
      simpa only [e',Function.update_of_ne hj] using hh
  have hcomp (g : ℕ) : (∑ x, towerWeights A B c i.val x*φ (N g x))≤G :=
    tower_exponent_convex_bound A B c E q hc hq1 hqdec hqE φ
      (residual_scaled_convex _ _) (residual_scaled_monotone _ _ (hc0 i) (hs i).le)
      i.val i.isLt.le 1 (Kg g) e' X (fun k _ => he' k)
      (fun k hk => hprev k (Finset.mem_filter.mp hk).1) (fun k _ => hX' k) (hmult g)
  have hG : 0≤G := exponentEnvelope_nonneg E q hq1 hqdec φ (fun _ => le_max_left _ _) _ _
  have hpoint (x : ∀ j, A j) : coordinateFraction A i (B i) x ≤
      ∑ g∈Finset.range (E i), r i (g+1)*N g x := by
    have hzero : K.filter (fun k => e k i=0)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      obtain ⟨hk,hz⟩ := Finset.mem_filter.mp hk
      exact (mem_expSupport _ _).mp (hki k hk) hz
    have hfull : K.filter (fun k => e k i≤E i)=K := Finset.filter_true_of_mem (fun k _ => he k i)
    have hsum := sum_filter_nat_le K (fun k => e k i) (E i) (fun k => r i (e k i)*W k x)
    rw [hzero,hfull,Finset.sum_empty,zero_add] at hsum
    calc
      _ ≤ ∑ k∈K, fraction (X k i)*boxIndicator A ((S k).erase i) (X k) x :=
        layered_fraction_bound A S X σ hσ i x
      _ ≤ ∑ k∈K, r i (e k i)*W k x := by
        apply Finset.sum_le_sum
        intro k hk
        have hi := (mem_expSupport _ _).mp (hki k hk)
        simpa only [W,e',expSupport_update_zero,S] using
          mul_le_mul_of_nonneg_right (hX k i hi) (boxIndicator_nonneg A ((S k).erase i) (X k) x)
      _ = ∑ g∈Finset.range (E i), r i (g+1)*N g x := by
        rw [hsum]
        apply Finset.sum_congr rfl
        intro g hg
        rw [show r i (g+1)*N g x = ∑ k∈Kg g, r i (g+1)*W k x from Finset.mul_sum _ _ _]
        apply Finset.sum_congr rfl
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
  have hres (x : ∀ j, A j) : Erdos7Distortion.residual (c i) (coordinateFraction A i (B i) x) ≤
      ∑ g∈Finset.range (E i), (r i (g+1)/s i)*φ (N g x) := by
    apply (max_le_max le_rfl (sub_le_sub_right (mul_le_mul_of_nonneg_left (hpoint x) (hc0 i)) _)).trans
    exact weighted_residual_bound (Finset.range (E i)) (c i) (s i) (hc i) (hs i)
      (fun g => r i (g+1)) (fun g => N g x)
      (fun g hg => hr i g (Finset.mem_range.mp hg)) (hrs i)
  calc
    _ ≤ ∑ x, towerWeights A B c i.val x *
        (∑ g∈Finset.range (E i), (r i (g+1)/s i)*φ (N g x)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hres x) (towerWeights_nonneg A B c hc i.val x))
    _ = ∑ g∈Finset.range (E i), (r i (g+1)/s i)*
        (∑ x, towerWeights A B c i.val x*φ (N g x)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ ∑ g∈Finset.range (E i), (r i (g+1)/s i)*G :=
      Finset.sum_le_sum (fun g hg => mul_le_mul_of_nonneg_left (hcomp g)
        (div_nonneg (hr i g (Finset.mem_range.mp hg)) (hs i).le))
    _ ≤ G := by
      rw [← Finset.sum_mul,← Finset.sum_div]
      have hh := mul_le_mul_of_nonneg_right ((div_le_one (hs i)).mpr (hrs i)) hG
      simpa only [one_mul] using hh


theorem layer_raw_loss_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p : Fin n → ℕ) (hp : ∀ i, 1 < p i)
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (X : κ → ∀ i, Finset (A i)) (hX0 : ∀ k i, e k i = 0 → X k i = Finset.univ)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i))
    (c : Fin n → ℚ) (hc : ∀ i, 1 < c i)
    (σ : κ → Fin n)
    (hσ : ∀ k, σ k ∈ expSupport (e k))
    (hS : ∀ k j, j ∈ expSupport (e k) → j ≤ σ k) (i : Fin n) :
    (∑ x, towerWeights A (layeredBad A (fun k => expSupport (e k)) X σ) c i.val x *
      Erdos7Distortion.residual (c i)
        (coordinateFraction A i (layeredBad A (fun k => expSupport (e k)) X σ i) x)) ≤
    c i ^ 2 / (4*(c i-1)) * (1/(p i-1 : ℚ)^2 *
      ∏ j ∈ Finset.univ.filter (fun j => j < i),
        (1+c j*(3*(p j : ℚ)-1)/(p j-1)^2)) := by
  classical
  let S (k : κ) := expSupport (e k)
  have hmem (k : κ) (i : Fin n) : i ∈ S k ↔ e k i ≠ 0 := mem_expSupport _ _
  have hX0' (k : κ) (j : Fin n) (hj : j ∉ S k) : X k j = Finset.univ := by
    apply hX0 k j
    by_contra hh
    exact hj ((hmem k j).mpr hh)
  have hc0 (j : Fin n) : 0 ≤ c j := by have := hc j; linarith
  have hfrac (k : κ) (j : Fin n) : fraction (X k j) ≤ ((p j : ℚ)⁻¹)^(e k j) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hX k j
  have hinter (k l : κ) (j : Fin n) :
      fraction (X k j ∩ X l j) ≤ ((p j : ℚ)⁻¹)^(max (e k j) (e l j)) := by
    by_cases hkl : e k j ≤ e l j
    · rw [max_eq_right hkl]
      apply (le_trans _ (hfrac l j))
      apply div_le_div_of_nonneg_right _ card_pos_rat.le
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : X k j ∩ X l j ⊆ X l j)
    · rw [max_eq_left (le_of_not_ge hkl)]
      apply (le_trans _ (hfrac k j))
      apply div_le_div_of_nonneg_right _ card_pos_rat.le
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : X k j ∩ X l j ⊆ X k j)
  let E (j : Fin n) := Finset.univ.sup (fun k => e k j)
  have heE (k : κ) (j : Fin n) : e k j ≤ E j :=
    Finset.le_sup (f := fun k => e k j) (Finset.mem_univ k)
  have hpair (i : Fin n) (k : κ) (hk : k ∈ layerFamily σ i) (l : κ) (hl : l ∈ layerFamily σ i) :
      fraction (X k i) * fraction (X l i) *
        (∏ j ∈ (S k ∪ S l).erase i, c j * fraction (X k j ∩ X l j)) ≤
      ((p i : ℚ)⁻¹)^(e k i) * ((p i : ℚ)⁻¹)^(e l i) *
        ∏ j ∈ Finset.univ.filter (fun j => j < i), exponentPairFactor (p j) (c j) (e k j) (e l j) := by
    have hki : σ k = i := (Finset.mem_filter.mp hk).2
    have hli : σ l = i := (Finset.mem_filter.mp hl).2
    let U := (S k ∪ S l).erase i
    let V := Finset.univ.filter (fun j : Fin n => j < i)
    have hUV : U ⊆ V := by
      intro j hj
      obtain ⟨hji,hju⟩ := Finset.mem_erase.mp hj
      have hle : j ≤ i := by
        rcases Finset.mem_union.mp hju with hjk | hjl
        · simpa only [hki] using hS k j hjk
        · simpa only [hli] using hS l j hjl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_ne hle hji⟩
    have hmax (j : Fin n) (hj : j ∈ U) : max (e k j) (e l j) ≠ 0 := by
      intro hzero
      rcases Finset.mem_union.mp (Finset.mem_erase.mp hj).2 with hjk | hjl
      · have hh := (hmem k j).mp hjk; omega
      · have hh := (hmem l j).mp hjl; omega
    have hprod : (∏ j ∈ U, c j * fraction (X k j ∩ X l j)) ≤
        ∏ j ∈ U, exponentPairFactor (p j) (c j) (e k j) (e l j) := by
      apply Finset.prod_le_prod
      · intro j _; exact mul_nonneg (hc0 j) (fraction_nonneg _)
      · intro j hj
        rw [exponentPairFactor, if_neg (hmax j hj)]
        exact mul_le_mul_of_nonneg_left (hinter k l j) (hc0 j)
    have hext : (∏ j ∈ U, exponentPairFactor (p j) (c j) (e k j) (e l j)) =
        ∏ j ∈ V, exponentPairFactor (p j) (c j) (e k j) (e l j) := by
      apply Finset.prod_subset hUV
      intro j hjV hjU
      have hji : j ≠ i := ne_of_lt (Finset.mem_filter.mp hjV).2
      have hk0 : e k j = 0 := by
        by_contra h
        exact hjU (Finset.mem_erase.mpr ⟨hji, Finset.mem_union_left _ ((hmem k j).mpr h)⟩)
      have hl0 : e l j = 0 := by
        by_contra h
        exact hjU (Finset.mem_erase.mpr ⟨hji, Finset.mem_union_right _ ((hmem l j).mpr h)⟩)
      simp [exponentPairFactor, hk0, hl0]
    have hnew := mul_le_mul (hfrac k i) (hfrac l i) (fraction_nonneg _) (by positivity)
    exact mul_le_mul hnew (hprod.trans_eq hext)
      (Finset.prod_nonneg (fun j _ => mul_nonneg (hc0 j) (fraction_nonneg _))) (by positivity)
  have hcoeff : 0 ≤ c i ^ 2 / (4*(c i-1)) := by
    apply div_nonneg (sq_nonneg _)
    have hh : 0 < c i-1 := by have := hc i; linarith
    positivity
  have hres : (∑ x, towerWeights A (layeredBad A S X σ) c i.val x *
      Erdos7Distortion.residual (c i) (coordinateFraction A i (layeredBad A S X σ i) x)) ≤
      c i ^ 2 / (4*(c i-1)) * (∑ x, towerWeights A (layeredBad A S X σ) c i.val x *
        coordinateFraction A i (layeredBad A S X σ i) x ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (residual_le_second_moment (α := coordinateFraction A i (layeredBad A S X σ i) x) (hc i))
      (towerWeights_nonneg A (layeredBad A S X σ) c (fun j => (hc j).le) i.val x)
    convert hh using 1 <;> ring
  apply hres.trans
  apply (mul_le_mul_of_nonneg_left
    (layered_second_moment_bound A S X σ hσ hS hX0' c (fun j => (hc j).le) i) hcoeff).trans
  have hsum : (∑ k ∈ layerFamily σ i, ∑ l ∈ layerFamily σ i,
      fraction (X k i) * fraction (X l i) *
        ∏ j ∈ (S k ∪ S l).erase i, c j * fraction (X k j ∩ X l j)) ≤
      ∑ k ∈ layerFamily σ i, ∑ l ∈ layerFamily σ i,
        ((p i : ℚ)⁻¹)^(e k i) * ((p i : ℚ)⁻¹)^(e l i) *
          ∏ j ∈ Finset.univ.filter (fun j => j < i), exponentPairFactor (p j) (c j) (e k j) (e l j) :=
    Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun l hl => hpair i k hk l hl))
  have hepos : ∀ k ∈ layerFamily σ i, 0 < e k i := by
    intro k hk
    have hki : σ k = i := (Finset.mem_filter.mp hk).2
    have hh := (hmem k (σ k)).mp (hσ k)
    rw [hki] at hh
    omega
  have hefuture : ∀ k ∈ layerFamily σ i, ∀ j, i < j → e k j = 0 := by
    intro k hk j hij
    by_contra h
    have hj := hS k j ((hmem k j).mpr h)
    have hki : σ k = i := (Finset.mem_filter.mp hk).2
    rw [hki] at hj
    exact (not_le_of_gt hij) hj
  have hbudget := exponent_layer_pair_bound p E hp c hc0 (layerFamily σ i) e he
    (fun k _ j => heE k j) i hepos hefuture
  have hcoeff : 0 ≤ c i ^ 2 / (4 * (c i - 1)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (by have := hc i; linarith))
  exact mul_le_mul_of_nonneg_left (hsum.trans hbudget) hcoeff


#print axioms layer_exponent_loss_bound
#print axioms layer_raw_loss_bound
end Erdos7ExceptionalLayers
