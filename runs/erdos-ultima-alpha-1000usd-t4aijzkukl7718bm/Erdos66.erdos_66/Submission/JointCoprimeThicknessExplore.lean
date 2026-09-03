import Submission.CoprimeThicknessGeometryExplore
import Submission.PeriodicPatternComparisonExplore

/-! All four mixed pair types for two coprime thicknesses over one plane.
The self-type counts are transferred through an exact common-period identity. -/
namespace Erdos66JointCoprimeThickness
open Erdos66CoprimeThickness Erdos66CoprimeThicknessGeometry
  Erdos66PeriodicPatternComparison Erdos66OuterCarryProfile
  Erdos66MixedCyclicThickening Erdos66CyclicThickening
open scoped Classical
set_option maxHeartbeats 1800000

lemma verticalPreimage_fiber_card (p : ℕ) [NeZero p] (k : ZMod p)
    (hk : IsUnit k) (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p) :
    (mixedFiber p (verticalPreimage p k B) (verticalPreimage p k C) t s).card =
      (mixedFiber p B C t (k*s)).card := by
  obtain ⟨u, rfl⟩ := hk
  apply Finset.card_nbij (fun a : ZMod p × ZMod p ↦ (a.1,(u:ZMod p)*a.2))
  · intro a ha
    simp only [Finset.mem_coe, mixedFiber, verticalPreimage, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha ⊢
    simpa only [mul_sub] using ha
  · intro a ha b hb hab
    apply Prod.ext
    · have hh := congrArg Prod.fst hab; exact hh
    · exact u.isUnit.mul_left_cancel (congrArg Prod.snd hab)
  · intro b hb
    refine ⟨(b.1,(↑u⁻¹:ZMod p)*b.2), ?_, ?_⟩
    · simp only [Finset.mem_coe, mixedFiber, verticalPreimage, Finset.mem_filter, Finset.mem_univ,
        true_and] at hb ⊢
      simpa only [mul_sub, ←mul_assoc, Units.mul_inv, one_mul] using hb
    · simp only [←mul_assoc, Units.mul_inv, one_mul]

lemma cyclicCount_comm (M : ℕ) [NeZero M] (B C : Finset (ZMod M)) (z : ZMod M) :
    cyclicCount M B C z = cyclicCount M C B z := by
  rw [cyclicCount_sum, cyclicCount_sum, ← Equiv.sum_comp (Equiv.subLeft z)]
  simp only [Equiv.subLeft_apply, sub_sub_cancel, and_comm]

lemma mixedFiber_card_comm (p : ℕ) [NeZero p]
    (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p) :
    (mixedFiber p B C t s).card = (mixedFiber p C B t s).card := by
  apply Finset.card_nbij (fun a : ZMod p × ZMod p ↦ (t-a.1,s-a.2))
  · intro a ha
    simpa only [Finset.mem_coe, mixedFiber, Finset.mem_filter, sub_sub_cancel,
      Prod.eta, and_comm] using ha
  · intro a ha b hb hab
    have hh := congrArg (fun a : ZMod p × ZMod p ↦ (t-a.1,s-a.2)) hab
    simpa only [sub_sub_cancel, Prod.eta] using hh
  · intro b hb
    refine ⟨(t-b.1,s-b.2), ?_, ?_⟩
    · simpa only [Finset.mem_coe, mixedFiber, Finset.mem_filter, sub_sub_cancel,
        Prod.eta, and_comm] using hb
    · simp only [sub_sub_cancel, Prod.eta]

variable (p K L : ℕ) [NeZero p] [NeZero K] [NeZero L]
variable (hp : p.Coprime (K*L)) (hKL : K.Coprime L)

lemma left_count_comparison (B C : Finset (ZMod p × ZMod p)) (n : ℕ) :
    K * cyclicCount _ (leftSet p K L hp hKL B) (leftSet p K L hp hKL C)
      (n : ZMod (p*(p*(K*L)))) =
    L * cyclicCount _ (thickenedSet p K (verticalPreimage p (K:ZMod p) B))
      (thickenedSet p K (verticalPreimage p (K:ZMod p) C))
      (n : ZMod ((p*K)^2)) := by
  exact periodic_mixed_count_comparison (p*(p*(K*L))) ((p*K)^2) K L
    (by ring) _ _ _ _ (leftSet_is_thickening p K L hp hKL B)
    (leftSet_is_thickening p K L hp hKL C) n

lemma right_count_comparison (B C : Finset (ZMod p × ZMod p)) (n : ℕ) :
    L * cyclicCount _ (rightSet p K L hp hKL B) (rightSet p K L hp hKL C)
      (n : ZMod (p*(p*(K*L)))) =
    K * cyclicCount _ (thickenedSet p L (verticalPreimage p (L:ZMod p) B))
      (thickenedSet p L (verticalPreimage p (L:ZMod p) C))
      (n : ZMod ((p*L)^2)) := by
  exact periodic_mixed_count_comparison (p*(p*(K*L))) ((p*L)^2) L K
    (by ring) _ _ _ _ (rightSet_is_thickening p K L hp hKL B)
    (rightSet_is_thickening p K L hp hKL C) n

lemma rescale_thickness_error (K L : ℝ) (hK : 0<K) (hL : 0≤L)
    (r R μ E : ℝ) (hcount : K*r=L*R)
    (herr : |R-K^2*μ|≤K^2*E+2*K*(μ+E)) :
    |r-K*L*μ|≤K*L*E+2*L*(μ+E) := by
  apply le_of_mul_le_mul_left (a := K) _ hK
  have he : K*(r-K*L*μ)=L*(R-K^2*μ) := by nlinarith only [hcount]
  calc
    K*|r-K*L*μ| = |K*(r-K*L*μ)| := by rw [abs_mul, abs_of_pos hK]
    _ = L*|R-K^2*μ| := by rw [he, abs_mul, abs_of_nonneg hL]
    _ ≤ L*(K^2*E+2*K*(μ+E)) := mul_le_mul_of_nonneg_left herr hL
    _ = K*(K*L*E+2*L*(μ+E)) := by ring

/-- Left/left mixed counts, not only diagonal self-counts. -/
theorem left_left_error (B C : Finset (ZMod p × ZMod p)) (μ E : ℝ)
    (hB : ∀ t s : ZMod p, |((mixedFiber p B C t s).card:ℝ)-μ|≤E)
    (z : ZMod (p*(p*(K*L)))) :
    |(cyclicCount _ (leftSet p K L hp hKL B) (leftSet p K L hp hKL C) z:ℝ)-
      (K:ℝ)*L*μ| ≤ (K:ℝ)*L*E+2*L*(μ+E) := by
  have hk : IsUnit (K:ZMod p) :=
    (ZMod.isUnit_iff_coprime K p).mpr (Nat.coprime_mul_iff_right.mp hp).1.symm
  have hf : ∀ t s : ZMod p,
      |((mixedFiber p (verticalPreimage p (K:ZMod p) B)
        (verticalPreimage p (K:ZMod p) C) t s).card:ℝ)-μ|≤E := by
    intro t s
    rw [verticalPreimage_fiber_card p _ hk]
    exact hB _ _
  have herr := thickenedSet_error p K _ _ μ E hf (z.val : ZMod ((p*K)^2))
  have hc := left_count_comparison p K L hp hKL B C z.val
  rw [ZMod.natCast_zmod_val] at hc
  have hcr : (K:ℝ)*(cyclicCount _ (leftSet p K L hp hKL B)
      (leftSet p K L hp hKL C) z:ℝ) = (L:ℝ)*
      (cyclicCount _ (thickenedSet p K (verticalPreimage p (K:ZMod p) B))
        (thickenedSet p K (verticalPreimage p (K:ZMod p) C))
        (z.val : ZMod ((p*K)^2)):ℝ) := by exact_mod_cast hc
  exact rescale_thickness_error K L (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K))
    (Nat.cast_nonneg L) _ _ μ E hcr herr

/-- Right/right mixed counts in the same common modulus. -/
theorem right_right_error (B C : Finset (ZMod p × ZMod p)) (μ E : ℝ)
    (hB : ∀ t s : ZMod p, |((mixedFiber p B C t s).card:ℝ)-μ|≤E)
    (z : ZMod (p*(p*(K*L)))) :
    |(cyclicCount _ (rightSet p K L hp hKL B) (rightSet p K L hp hKL C) z:ℝ)-
      (K:ℝ)*L*μ| ≤ (K:ℝ)*L*E+2*K*(μ+E) := by
  have hk : IsUnit (L:ZMod p) :=
    (ZMod.isUnit_iff_coprime L p).mpr (Nat.coprime_mul_iff_right.mp hp).2.symm
  have hf : ∀ t s : ZMod p,
      |((mixedFiber p (verticalPreimage p (L:ZMod p) B)
        (verticalPreimage p (L:ZMod p) C) t s).card:ℝ)-μ|≤E := by
    intro t s
    rw [verticalPreimage_fiber_card p _ hk]
    exact hB _ _
  have herr := thickenedSet_error p L _ _ μ E hf (z.val : ZMod ((p*L)^2))
  have hc := right_count_comparison p K L hp hKL B C z.val
  rw [ZMod.natCast_zmod_val] at hc
  have hcr : (L:ℝ)*(cyclicCount _ (rightSet p K L hp hKL B)
      (rightSet p K L hp hKL C) z:ℝ) = (K:ℝ)*
      (cyclicCount _ (thickenedSet p L (verticalPreimage p (L:ZMod p) B))
        (thickenedSet p L (verticalPreimage p (L:ZMod p) C))
        (z.val : ZMod ((p*L)^2)):ℝ) := by exact_mod_cast hc
  have hh := rescale_thickness_error L K
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L))
    (Nat.cast_nonneg K) _ _ μ E hcr herr
  simpa only [mul_comm (L:ℝ) (K:ℝ)] using hh

noncomputable def twoSet (side : Bool) (B : Finset (ZMod p × ZMod p)) :
    Finset (ZMod (p*(p*(K*L)))) :=
  if side then rightSet p K L hp hKL B else leftSet p K L hp hKL B

lemma twoSet_card (side : Bool) (B : Finset (ZMod p × ZMod p)) :
    (twoSet p K L hp hKL side B).card = K*L*B.card := by
  cases side <;> simp only [twoSet, Bool.false_eq_true, if_false, if_true]
  · exact leftSet_card p K L hp hKL B
  · exact rightSet_card p K L hp hKL B

/-- All four pair types in one common cyclic modulus. -/
theorem twoSet_error (B C : Finset (ZMod p × ZMod p)) (μ E : ℝ)
    (hμ : 0≤μ) (hE : 0≤E)
    (hB : ∀ t s : ZMod p, |((mixedFiber p B C t s).card:ℝ)-μ|≤E)
    (a b : Bool) (z : ZMod (p*(p*(K*L)))) :
    |(cyclicCount _ (twoSet p K L hp hKL a B) (twoSet p K L hp hKL b C) z:ℝ)-
      (K:ℝ)*L*μ| ≤ (K:ℝ)*L*E+2*(max K L:ℕ)*(μ+E) := by
  have hKmax : (K:ℝ)≤(max K L:ℕ) := by exact_mod_cast le_max_left K L
  have hLmax : (L:ℝ)≤(max K L:ℕ) := by exact_mod_cast le_max_right K L
  have hminmax : (min K L:ℕ)≤(max K L:ℕ) := (min_le_left K L).trans (le_max_left K L)
  have hminR : ((min K L:ℕ):ℝ)≤(max K L:ℕ) := by exact_mod_cast hminmax
  have hμE : 0≤μ+E := add_nonneg hμ hE
  have hmax : (0:ℝ)≤(max K L:ℕ) := Nat.cast_nonneg _
  cases a <;> cases b <;> simp only [twoSet, Bool.false_eq_true, if_false, if_true]
  · exact (left_left_error p K L hp hKL B C μ E hB z).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hLmax hμE])
  · exact (mixed_thickness_error p K L hp hKL B C μ E hB z).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hminR hμE])
  · rw [cyclicCount_comm]
    have hC : ∀ t s : ZMod p, |((mixedFiber p C B t s).card:ℝ)-μ|≤E := by
      intro t s
      rw [mixedFiber_card_comm]
      exact hB t s
    exact (mixed_thickness_error p K L hp hKL C B μ E hC z).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hminR hμE])
  · exact (right_right_error p K L hp hKL B C μ E hB z).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hKmax hμE])

end Erdos66JointCoprimeThickness
