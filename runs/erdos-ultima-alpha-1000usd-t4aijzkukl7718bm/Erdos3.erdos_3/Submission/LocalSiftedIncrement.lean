import Submission.StableSupportedIncrement

/-! A local weighted correlation moment yields a stable relative density increment,
under explicit nesting and growth hypotheses. -/
namespace Erdos3LocalSiftedIncrement
open Finset Erdos3StableSupportedIncrement Erdos3BohrIncrementParameters
  Erdos3AsymmetricLocalization Erdos3AsymmetricSifting Erdos3LocalCorrelationCentering
  Erdos3CorrelationMoments Erdos3CorrelationSifting Erdos3BohrLocalAverages
  Erdos3FiniteBohr Erdos3BohrCovering Erdos3BohrStableScale Erdos3CrootSisaskL2
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 3000000

lemma bad_fraction_small {p : ℕ} (hp : 536 ≤ p) :
    2*((33/32 : ℝ)/(67/64))^p ≤ 1/128 := by
  have hbase : (66/67 : ℝ)^67 ≤ 1/2 := by norm_num
  have hpow : (66/67 : ℝ)^536 ≤ 1/256 := by
    rw [show 536 = 67*8 by decide, pow_mul]
    calc
      _ ≤ (1/2 : ℝ)^8 := pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by norm_num
  have hdec : (66/67 : ℝ)^p ≤ (66/67 : ℝ)^536 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  norm_num only [show (33/32 : ℝ)/(67/64) = 66/67 by norm_num]
  linarith only [hdec.trans hpow]

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma size_of_relative_lower (S C W : Finset G) (hS : S.Nonempty) (hSC : S ⊆ C)
    {σ : ℝ} {m : ℕ} (hrel : σ ≤ 2*relativeDensity S C)
    (hW : (W.card : ℝ) ≤ 2*C.card) (hbudget : 4 ≤ (2 : ℝ)^(2*m)*σ) :
    W.card ≤ 2^(2*m)*S.card := by
  have hC : (0 : ℝ) < C.card := by exact_mod_cast (hS.mono hSC).card_pos
  have hrel' : σ*(C.card : ℝ) ≤ 2*S.card := by
    unfold relativeDensity at hrel
    rw [inter_eq_left.mpr hSC, ← mul_div_assoc] at hrel
    exact (le_div_iff₀ hC).mp hrel
  have h₁ := mul_le_mul_of_nonneg_left hrel' (by positivity : (0 : ℝ) ≤ 2^(2*m))
  have h₂ := mul_le_mul_of_nonneg_right hbudget hC.le
  have hh : (W.card : ℝ) ≤ (2 : ℝ)^(2*m)*S.card := by nlinarith
  exact_mod_cast hh

lemma shift_sumset_subset (E : Finset (AddChar G ℂ)) {u q : ℝ}
    (T : Finset G) (x : G) (hT : T ⊆ shiftSet (bohr E u) x) :
    T+bohr E q ⊆ shiftSet (bohr E (u+q)) x := by
  intro y hy
  obtain ⟨t,ht,v,hv,rfl⟩ := mem_add.mp hy
  obtain ⟨w,hw,rfl⟩ := mem_image.mp (hT ht)
  exact mem_image.mpr ⟨w+v,bohr_add hw hv,by abel⟩

lemma enlargement_le_twice (E : Finset (AddChar G ℂ)) {r h δ : ℝ}
    (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgrowth : ((bohr E (r+h)).card : ℝ) ≤ (1+δ)*((bohr E (r-h)).card : ℝ)) :
    ((bohr E (r+h)).card : ℝ) ≤ 2*((bohr E r).card : ℝ) := by
  have hsub : ((bohr E (r-h)).card : ℝ) ≤ (bohr E r).card := by
    exact_mod_cast card_le_card (bohr_mono E (by linarith : r-h ≤ r))
  calc
    _ ≤ (1+δ)*((bohr E (r-h)).card : ℝ) := hgrowth
    _ ≤ (1+δ)*((bohr E r).card : ℝ) := mul_le_mul_of_nonneg_left hsub (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- The full moment-to-increment step with explicit local geometry. Its rank cost
is polynomial in m, independently of the ambient density or the old rank. -/
theorem moment_to_stable_increment (E : Finset (AddChar G ℂ))
    {c hC δC u q hQ : ℝ} (hc : 0 ≤ c) (hhC : 0 ≤ hC)
    (hδC : 0 ≤ δC) (hδC1 : δC ≤ 1) (hu : 0 ≤ u) (huC : u ≤ hC)
    (hq : 0 ≤ q) (hhQ : 0 < hQ)
    (hCgrowth : ((bohr E (c+hC)).card : ℝ) ≤ (1+δC)*((bohr E (c-hC)).card : ℝ))
    (hUgrowth : ((bohr E (u+q)).card : ℝ) ≤ 2*((bohr E u).card : ℝ))
    (A B V : Finset G) (hA : A.Nonempty) (hAB : A ⊆ B) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ t ∈ bohr E c, a-t ∈ V)
    (hVsize : density V ≤ (67/64 : ℝ)*density B)
    {p m : ℕ} (hp : 536 ≤ p) (hm : 0 < m)
    (hmoment : (17/16 : ℝ)^p ≤ 𝔼 t : G, corr (normalized (bohr E c)) t*
      (corr (localNormalized A B) t/density B)^p)
    (herror : δC*(1/relativeDensity A B)^p ≤ (17/16 : ℝ)^p-(67/64 : ℝ)^p)
    (hbudget : 4 ≤ (2 : ℝ)^(2*m)*(relativeDensity A B)^(2*p))
    (hQgrowth : ((bohr E (q+hQ)).card : ℝ) ≤
      (1+translationTolerance m (rankBudget m))*((bohr E (q-hQ)).card : ℝ))
    {z : ℕ} (hz : 0 < z) :
    ∃ D : Finset (AddChar G ℂ), D.card ≤ rankBudget m ∧
      let s := min hQ (generatorRadius m (rankBudget m))
      ∃ r : ℝ, s/2 ≤ r-stabilityWidth (E ∪ D) z (s/2) ∧
        r+stabilityWidth (E ∪ D) z (s/2) ≤ s ∧
        ((bohr (E ∪ D) (r+stabilityWidth (E ∪ D) z (s/2))).card : ℝ) ≤
          (1+1/(z : ℝ))*((bohr (E ∪ D) (r-stabilityWidth (E ∪ D) z (s/2))).card : ℝ) ∧
        ∃ x : G, (129/128 : ℝ)*relativeDensity A B ≤ smooth (bohr (E ∪ D) r) (indicator A) x := by
  obtain ⟨x,hx,S,hSC,T,hTU,hS,hT,hSrel,hTrel,hbad⟩ := localize_and_sift E hc hhC hδC
    (by norm_num : (0 : ℝ) < 33/32) (by norm_num : (0 : ℝ) < 67/64)
    hCgrowth A B (bohr E u) V hA hAB ⟨0,bohr_zero E hu⟩ (bohr_mono E huC)
    hV hsupport hVsize p hmoment herror
  let W := shiftSet (bohr E (c+hC)) x
  have hWsize : (W.card : ℝ) ≤ 2*((bohr E c).card : ℝ) := by
    dsimp only [W]
    rw [shiftSet_card]
    exact enlargement_le_twice E hhC hδC hδC1 hCgrowth
  have hWS : W.card ≤ 2^(2*m)*S.card := size_of_relative_lower S (bohr E c) W hS hSC hSrel hWsize hbudget
  have hsumsize : ((T+bohr E q).card : ℝ) ≤ 2*((shiftSet (bohr E u) x).card : ℝ) := by
    rw [shiftSet_card]
    calc
      _ ≤ ((shiftSet (bohr E (u+q)) x).card : ℝ) := by
        exact_mod_cast card_le_card (shift_sumset_subset E T x hTU)
      _ = ((bohr E (u+q)).card : ℝ) := by rw [shiftSet_card]
      _ ≤ _ := hUgrowth
  have hTQ : (T+bohr E q).card ≤ 2^(2*m)*T.card :=
    size_of_relative_lower T (shiftSet (bohr E u) x) (T+bohr E q) hT hTU hTrel hsumsize hbudget
  let f : G → ℝ := fun t ↦ if (33/32 : ℝ) < corr (localNormalized A B) t/density B then 1 else 0
  have hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1 := by intro t; unfold f; split_ifs <;> norm_num
  have hfc : ∀ t, (33/32 : ℝ)*f t ≤ corr (localNormalized A B) t/density B := by
    intro t
    by_cases ht : (33/32 : ℝ) < corr (localNormalized A B) t/density B
    · simpa only [f, if_pos ht, mul_one] using ht.le
    · simpa only [f, if_neg ht, mul_zero] using (local_correlation_bound A B hA hAB t).1
  have hbad' : crossPairDensity S T (fun t ↦ 1-f t) ≤ (1/128 : ℝ)*density S*density T := by
    have he (t : G) : 1-f t =
        if corr (localNormalized A B) t/density B ≤ (33/32 : ℝ) then 1 else 0 := by
      unfold f
      split_ifs <;> simp_all <;> linarith
    simp_rw [he]
    exact hbad.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (bad_fraction_small hp) (density_nonneg S)) (density_nonneg T))
  exact stable_increment A B S T W E hq hhQ hA hAB hS hT f hf hfc hbad'
    (cross_differences_in_enlargement E (bohr E u) S T x (bohr_mono E huC) hSC hTU)
    hm hWS hTQ hQgrowth hz

#print axioms bad_fraction_small
#print axioms moment_to_stable_increment
end Erdos3LocalSiftedIncrement
