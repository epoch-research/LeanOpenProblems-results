import Submission.DecreasingPrefixMixture

/-! Cyclic approximation to residue-conditioned correlations on translated
intervals. Translation rotates the cycle; it does not change the residue law. -/
namespace Erdos371.FiniteInformation
open Finset
set_option autoImplicit false

noncomputable def translatedGapTest {X : Type*} (q : ℕ) (L : ℕ → X)
    (C : X → X → ℝ) (n : ℕ) : ℝ :=
  q*(if q ∣ n then C (L n) (L (n+q)) else 0)-C (L n) (L (n+q))

lemma gap_value_bound (q : ℕ) (P : Prop) [Decidable P] (v : ℝ) (hv : |v| ≤ 1) :
    |(q : ℝ)*(if P then v else 0)-v| ≤ q+1 := by
  have ht := abs_sub ((q : ℝ)*(if P then v else 0)) v
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)] at ht
  have hi : |if P then v else 0| ≤ 1 := by
    split_ifs
    · exact hv
    · simp
  have hm := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (α := ℝ) q)
  nlinarith

lemma translatedGapTest_abs_le {X : Type*} (q : ℕ) (L : ℕ → X)
    (C : X → X → ℝ) (hC : ∀ a b, |C a b| ≤ 1) (n : ℕ) :
    |translatedGapTest q L C n| ≤ q+1 := gap_value_bound q _ _ (hC _ _)

noncomputable def translatedNaturalGapDiscrepancy {X : Type*} (S N q : ℕ)
    (L : ℕ → X) (C : X → X → ℝ) : ℝ := prefixMean N (fun n => translatedGapTest q L C (S+n))

noncomputable def translatedCycleLabel {X : Type*} (S N : ℕ) (L : ℕ → X) (x : ZMod N) : X :=
  L (S+(x-(S : ZMod N)).val)

lemma mean_uniform_zmod_translate (N : ℕ) [NeZero N] (F : ZMod N → ℝ) (t : ZMod N) :
    mean (uniformLaw (ZMod N)) F = mean (uniformLaw (ZMod N)) (fun x => F (x+t)) := by
  have h := mean_mapLaw (uniformLaw (ZMod N)) (Equiv.addRight t) F
  rw [mapLaw_uniform_equiv] at h
  exact h

lemma translated_cycle_pair {X : Type*} (S N q : ℕ) (L : ℕ → X) (x : ZMod N) :
    translatedCycleLabel S N L (x+S) = L (S+x.val) ∧
      translatedCycleLabel S N L (x+S+q) = L (S+(x+q).val) := by
  unfold translatedCycleLabel
  constructor
  · rw [add_sub_cancel_right]
  · rw [show x+(S : ZMod N)+q-S=x+q by ring]

lemma cyclicGapDiscrepancy_translated_prefix {X : Type*} (S N q : ℕ) [NeZero N]
    (hd : q ∣ N) (L : ℕ → X) (C : X → X → ℝ) :
    cyclicGapDiscrepancy N q (translatedCycleLabel S N L) C =
      prefixMean N (fun n => (q : ℝ)*(if q ∣ S+n then C (L (S+n)) (L (S+(n+q)%N)) else 0)-
        C (L (S+n)) (L (S+(n+q)%N))) := by
  classical
  unfold cyclicGapDiscrepancy
  rw [← mean_const_mul,← mean_sub]
  rw [mean_uniform_zmod_translate N _ (S : ZMod N)]
  rw [mean_uniform_zmod_prefix]
  apply prefixMean_congr
  intro n hn
  have hp := translated_cycle_pair S N q L (n : ZMod N)
  simp only [hp.1,hp.2]
  have hr : cyclicResidue N q ((n : ZMod N)+S)=0 ↔ q ∣ S+n := by
    rw [cyclicResidue_eq_castHom hd,map_add,map_natCast,map_natCast,← Nat.cast_add,ZMod.natCast_eq_zero_iff]
    rw [Nat.add_comm]
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hn,← Nat.cast_add]
  rw [← Nat.cast_add] at hr
  simp only [hr]

lemma translated_cyclic_natural_error {X : Type*} (S N q : ℕ) [NeZero N]
    (hq : q ≤ N) (hd : q ∣ N) (L : ℕ → X) (C : X → X → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |cyclicGapDiscrepancy N q (translatedCycleLabel S N L) C-
      translatedNaturalGapDiscrepancy S N q L C| ≤ 2*q*(q+1 : ℝ)/N := by
  classical
  rw [cyclicGapDiscrepancy_translated_prefix S N q hd]
  unfold translatedNaturalGapDiscrepancy
  have h := prefixMean_tail_bound N q hq
    (fun n => (q : ℝ)*(if q ∣ S+n then C (L (S+n)) (L (S+(n+q)%N)) else 0)-
      C (L (S+n)) (L (S+(n+q)%N)))
    (fun n => translatedGapTest q L C (S+n)) (q+1)
    (fun n _ => gap_value_bound q _ _ (hC _ _))
    (fun n _ => translatedGapTest_abs_le q L C hC (S+n))
    (fun n hn => by
      dsimp only [translatedGapTest]
      rw [Nat.mod_eq_of_lt (by omega : n+q < N)]
      simp only [Nat.add_assoc])
  exact h.trans_eq (by ring)

lemma translated_natural_endpoint_error {X : Type*} (S k M q : ℕ)
    (hk : 0 < k) (hkM : k ≤ M) (L : ℕ → X) (C : X → X → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |translatedNaturalGapDiscrepancy S M q L C-translatedNaturalGapDiscrepancy S k q L C| ≤
      2*(q+1 : ℝ)*(M-k : ℕ)/M := by
  exact prefixMean_endpoint_bound k M hk hkM _ (q+1) (fun n _ => translatedGapTest_abs_le q L C hC (S+n))

lemma translated_natural_cyclic_round_up_error {X : Type*} (S k M q B T : ℕ) [NeZero M]
    (hk : 0 < k) (hkM : k ≤ M) (htail : M-k ≤ T) (hqB : q ≤ B) (hBM : B ≤ M)
    (hd : q ∣ M) (L : ℕ → X) (C : X → X → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |translatedNaturalGapDiscrepancy S k q L C-
      cyclicGapDiscrepancy M q (translatedCycleLabel S M L) C| ≤
        (2*(B+1 : ℝ)*T+2*B*(B+1 : ℝ))/k := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have he := translated_natural_endpoint_error S k M q hk hkM L C hC
  rw [abs_sub_comm] at he
  have hc := translated_cyclic_natural_error S M q (hqB.trans hBM) hd L C hC
  rw [abs_sub_comm] at hc
  have he' : 2*(q+1 : ℝ)*(M-k : ℕ)/M ≤ 2*(B+1 : ℝ)*T/k := by
    calc
      _ ≤ 2*(B+1 : ℝ)*T/M := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hkr (by exact_mod_cast hkM)
  have hc' : 2*(q : ℝ)*(q+1)/M ≤ 2*(B : ℝ)*(B+1)/k := by
    calc
      _ ≤ 2*(B : ℝ)*(B+1)/M := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hkr (by exact_mod_cast hkM)
  exact (abs_sub_le _ (translatedNaturalGapDiscrepancy S M q L C) _).trans
    ((add_le_add (he.trans he') (hc.trans hc')).trans_eq (by ring))

#print axioms translated_natural_cyclic_round_up_error
end Erdos371.FiniteInformation
