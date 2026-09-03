import Submission.SupportCompression

/-! A finite covering criterion retaining a bound on individual prime support.
This does not settle the unrestricted conjecture. -/
namespace Erdos7SupportCompression
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

def supportMultiplicity (d r : ℕ) : ℕ := if r ≤ d then 1 else 0

lemma supportEnvelope_nonneg {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (hq1 : ∀ i, q i 0≤1) (hqdec : ∀ i g, g < E i → q i (g+1)≤q i g)
    (φ : ℚ → ℚ) (hφ : ∀ M : ℕ, 0≤φ M) (t : ℕ) (w : ℕ → ℕ) :
    0≤supportEnvelope E q φ t w := by
  induction t generalizing w with
  | zero => exact hφ (w 0)
  | succ t ih =>
    simp only [supportEnvelope]
    split_ifs with h
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hq1 _)) (ih _))
        (Finset.sum_nonneg (fun g hg => mul_nonneg
          (sub_nonneg.mpr (hqdec _ g (Finset.mem_range.mp hg))) (ih _)))
    · exact ih w

/-- The full-exponent scalar budget with the hinge loss left exact. -/
def supportCost {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) (c s : Fin n → ℚ) (d : ℕ) : ℚ :=
  ∑ i, supportEnvelope E q (fun x => residual (c i) (s i*x)) i.val (supportMultiplicity d)

/-- Distinct nonzero exponent patterns in a covering force the finite
exponent-compression budget to be at least one. The profile `r` bounds the
coordinate densities, and `s` bounds its positive-exponent sum. -/
theorem distinct_support_convex_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (c s : Fin n → ℚ) (r q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1≤c i) (hs : ∀ i, 0 < s i)
    (hr : ∀ i g, g < E i → 0≤r i (g+1))
    (hrs : ∀ i, (∑ g∈Finset.range (E i), r i (g+1))≤s i)
    (hq1 : ∀ i, q i 0≤1) (hqdec : ∀ i g, g < E i → q i (g+1)≤q i g)
    (hqE : ∀ i, q i (E i)=0)
    (hqr : ∀ i g, g < E i → c i*r i (g+1)≤q i g)
    (d : ℕ) (e : κ → Fin n → ℕ) (heinj : Function.Injective e)
    (he : ∀ k i, e k i≤E i) (hne : ∀ k, (expSupport (e k)).Nonempty)
    (hsize : ∀ k, (expSupport (e k)).card ≤ d + 1)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, e k i≠0 → fraction (X k i)≤r i (e k i))
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i∈expSupport (e k), x i∈X k i) :
    1≤supportCost E q c s d := by
  classical
  let S (k : κ) := expSupport (e k)
  let σ (k : κ) := (S k).max' (hne k)
  have hσ (k : κ) : σ k∈S k := Finset.max'_mem _ _
  have hS (k : κ) (j : Fin n) (hj : j∈S k) : j≤σ k := Finset.le_max' _ _ hj
  let B := layeredBad A S X σ
  have hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v∈B j ↔ x∈B j := by
    intro i j hji x v
    exact layeredBad_invariant A S X σ hS i j hji x v
  have hbcover : ∀ x : ∀ i, A i, ∃ i, x∈B i := by
    intro x
    obtain ⟨k,hk⟩ := hcover x
    exact ⟨σ k,Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, by simp [layerFamily], hk⟩⟩
  have hb := coordinate_residual_cover_bound A B c hc hB hbcover
  have hc0 : ∀ i, 0≤c i := fun i => (by norm_num : (0:ℚ)≤1).trans (hc i)
  apply hb.trans
  apply Finset.sum_le_sum
  intro i _
  let K := layerFamily σ i
  let Kg (g : ℕ) := K.filter (fun k => e k i=g+1)
  let e' (k : κ) := Function.update (e k) i 0
  let W (k : κ) (x : ∀ j, A j) := boxIndicator A (expSupport (e' k)) (X k) x
  let N (g : ℕ) (x : ∀ j, A j) := ∑ k∈Kg g, W k x
  let φ (x : ℚ) := residual (c i) (s i*x)
  let G := supportEnvelope E q φ i.val (supportMultiplicity d)
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
  have hsmall (k : κ) (hk : k ∈ K) : (expSupport (e' k)).card ≤ d := by
    have hi := hki k hk
    rw [expSupport_update_zero, Finset.card_erase_of_mem hi]
    have h := hsize k
    dsimp only [S] at *
    omega
  have hmult' (g : ℕ) (f : Fin n → ℕ) :
      ((Kg g).filter (fun k => e' k = f)).card ≤ supportMultiplicity d (expSupport f).card := by
    by_cases hf : (expSupport f).card ≤ d
    · simpa only [supportMultiplicity, if_pos hf] using hmult g f
    · have hempty : (Kg g).filter (fun k => e' k = f) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        obtain ⟨hk, heq⟩ := Finset.mem_filter.mp hk
        have hs := hsmall k (Finset.mem_filter.mp hk).1
        rw [heq] at hs
        exact hf hs
      simp only [hempty, Finset.card_empty, Nat.zero_le]
  have hcomp (g : ℕ) : (∑ x, towerWeights A B c i.val x*φ (N g x))≤G :=
    tower_support_convex_bound A B c E q hc hq1 hqdec hqE φ
      (residual_scaled_convex _ _) (residual_scaled_monotone _ _ (hc0 i) (hs i).le)
      i.val i.isLt.le (supportMultiplicity d) (Kg g) e' X (fun k _ => he' k)
      (fun k hk => hprev k (Finset.mem_filter.mp hk).1) (fun k _ => hX' k) (hmult' g)
  have hG : 0≤G := supportEnvelope_nonneg E q hq1 hqdec φ (fun _ => le_max_left _ _) _ _
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
  have hres (x : ∀ j, A j) : residual (c i) (coordinateFraction A i (B i) x) ≤
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


#print axioms distinct_support_convex_bound
end Erdos7SupportCompression
