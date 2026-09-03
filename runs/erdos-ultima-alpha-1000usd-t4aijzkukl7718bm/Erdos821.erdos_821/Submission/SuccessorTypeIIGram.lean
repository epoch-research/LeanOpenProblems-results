import Submission.SuccessorVaughanReduction
import Submission.DyadicTypeII

/-!
# Removing the signed coefficients from a successor Type II sum

Two Cauchy--Schwarz steps give a fourth-power bound in terms of the Gram
energy of the actual output-weight kernel. No estimate for the necessary
off-diagonal correlations is assumed to follow from input character means.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
namespace Erdos821.AnalyticSieve.SuccessorVaughan
set_option maxHeartbeats 3000000

noncomputable def kernelBilinear {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (a : ι → ℝ) (b : κ → ℝ) (K : ι → κ → ℝ) : ℝ :=
  ∑ r ∈ A, ∑ s ∈ B, a r*b s*K r s

noncomputable def rowGram {ι κ : Type*} (B : Finset κ)
    (K : ι → κ → ℝ) (r t : ι) : ℝ :=
  ∑ s ∈ B, K r s*K t s

noncomputable def kernelGramEnergy {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (K : ι → κ → ℝ) : ℝ :=
  ∑ r ∈ A, ∑ t ∈ A, (rowGram B K r t)^2

lemma kernelGramEnergy_nonneg {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (K : ι → κ → ℝ) : 0 ≤ kernelGramEnergy A B K :=
  sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))

lemma column_projection_square {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (a : ι → ℝ) (K : ι → κ → ℝ) :
    (∑ s ∈ B, (∑ r ∈ A, a r*K r s)^2) =
      ∑ r ∈ A, ∑ t ∈ A, (a r*a t)*rowGram B K r t := by
  simp only [rowGram, pow_two, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro s hs
  ring

/-- All signed coefficients have been removed from the remaining Gram
energy, but the full two-variable kernel is retained. -/
theorem kernelBilinear_fourth_le {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (a : ι → ℝ) (b : κ → ℝ) (K : ι → κ → ℝ) :
    (kernelBilinear A B a b K)^4 ≤
      (∑ r ∈ A, (a r)^2)^2 * (∑ s ∈ B, (b s)^2)^2 *
        kernelGramEnergy A B K := by
  classical
  let E₁ := ∑ r ∈ A, (a r)^2
  let E₂ := ∑ s ∈ B, (b s)^2
  let Q := ∑ s ∈ B, (∑ r ∈ A, a r*K r s)^2
  have hQ : 0 ≤ Q := sum_nonneg (fun _ _ => sq_nonneg _)
  have hE₂ : 0 ≤ E₂ := sum_nonneg (fun _ _ => sq_nonneg _)
  have he : kernelBilinear A B a b K =
      ∑ s ∈ B, b s*(∑ r ∈ A, a r*K r s) := by
    unfold kernelBilinear
    rw [sum_comm]
    apply sum_congr rfl
    intro s hs
    rw [mul_sum]
    exact sum_congr rfl (fun r _ => by ring)
  have hCS₁ : (kernelBilinear A B a b K)^2 ≤ E₂*Q := by
    rw [he]
    exact sum_mul_sq_le_sq_mul_sq B b (fun s => ∑ r ∈ A, a r*K r s)
  have hCS₂ : Q^2 ≤ E₁^2*kernelGramEnergy A B K := by
    have h := sum_mul_sq_le_sq_mul_sq (A ×ˢ A)
      (fun z => a z.1*a z.2) (fun z => rowGram B K z.1 z.2)
    have hprod : (∑ z ∈ A ×ˢ A, (a z.1*a z.2)^2) = E₁^2 := by
      rw [sum_product]
      simp only [mul_pow]
      rw [← sum_mul_sum]
      dsimp [E₁]
      ring
    rw [hprod, sum_product, sum_product] at h
    change _ ≤ E₁^2*kernelGramEnergy A B K at h
    simpa only [Q, column_projection_square] using h
  calc
    _ = ((kernelBilinear A B a b K)^2)^2 := by ring
    _ ≤ (E₂*Q)^2 := pow_le_pow_left₀ (sq_nonneg _) hCS₁ 2
    _ = E₂^2*Q^2 := mul_pow _ _ _
    _ ≤ E₂^2*(E₁^2*kernelGramEnergy A B K) :=
      mul_le_mul_of_nonneg_left hCS₂ (sq_nonneg _)
    _ = _ := by dsimp [E₁,E₂]; ring

lemma rowGram_self_nonneg {ι κ : Type*} (B : Finset κ)
    (K : ι → κ → ℝ) (r : ι) : 0 ≤ rowGram B K r r :=
  sum_nonneg (fun _ _ => mul_self_nonneg _)

lemma rowGram_self_le {ι κ : Type*} (B : Finset κ)
    (K : ι → κ → ℝ) (r : ι) (D : ℝ)
    (hK : ∀ s ∈ B, |K r s| ≤ D) :
    rowGram B K r r ≤ (B.card : ℝ)*D^2 := by
  calc
    _ ≤ ∑ _s ∈ B, D^2 := by
      apply sum_le_sum
      intro s hs
      have h := pow_le_pow_left₀ (abs_nonneg (K r s)) (hK s hs) 2
      rw [sq_abs] at h
      simpa only [pow_two] using h
    _ = _ := by simp

/-- The diagonal needs only a pointwise bound. The off-diagonal row
correlations, however, remain an explicit hypothesis. -/
theorem kernelGramEnergy_le_of_correlations {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (K : ι → κ → ℝ) (D T : ℝ)
    (hK : ∀ r ∈ A, ∀ s ∈ B, |K r s| ≤ D)
    (hT : ∀ r ∈ A, ∀ t ∈ A, r ≠ t → |rowGram B K r t| ≤ T) :
    kernelGramEnergy A B K ≤
      (A.card : ℝ)*(B.card : ℝ)^2*D^4 + (A.card : ℝ)^2*T^2 := by
  classical
  have hrow (r : ι) (hr : r ∈ A) :
      (∑ t ∈ A, (rowGram B K r t)^2) ≤
        ((B.card : ℝ)*D^2)^2+(A.card : ℝ)*T^2 := by
    have hd := pow_le_pow_left₀ (rowGram_self_nonneg B K r)
      (rowGram_self_le B K r D (hK r hr)) 2
    have hoff : (∑ t ∈ A.erase r, (rowGram B K r t)^2) ≤
        (A.card : ℝ)*T^2 := by
      calc
        _ ≤ ∑ _t ∈ A.erase r, T^2 := by
          apply sum_le_sum
          intro t ht
          obtain ⟨htr,ht⟩ := mem_erase.mp ht
          have h := pow_le_pow_left₀ (abs_nonneg (rowGram B K r t))
            (hT r hr t ht htr.symm) 2
          simpa only [sq_abs] using h
        _ = ((A.erase r).card : ℝ)*T^2 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card (erase_subset r A)) (sq_nonneg _)
    rw [← sum_erase_add _ _ hr]
    linarith only [hd,hoff]
  calc
    _ ≤ ∑ _r ∈ A, (((B.card : ℝ)*D^2)^2+(A.card : ℝ)*T^2) := sum_le_sum hrow
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

/-- The output cutoff and the centered output weight are both retained. -/
noncomputable def successorKernel (w v : ℕ → ℝ) (X r s : ℕ) : ℝ :=
  if r*s ≤ X then w (r*s)-v (r*s) else 0

lemma hyperbolic_discrepancy_eq_kernelBilinear
    (f g : ArithmeticFunction ℝ) (w v : ℕ → ℝ) (X : ℕ) :
    hyperbolicSum f g (fun n => w n-v n) X =
      kernelBilinear (Icc 1 X) (Icc 1 X) f g (successorKernel w v X) := by
  unfold hyperbolicSum kernelBilinear successorKernel
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro s hs
  split_ifs <;> simp

/-- A finite output-weighted Vaughan Type II block is bounded by the
Gram energy of its actual centered successor kernel. -/
theorem successor_typeII_block_fourth_le (w v : ℕ → ℝ)
    (A B : Finset ℕ) (R S U V X : ℕ)
    (hA : A ⊆ Icc 1 R) (hB : B ⊆ Icc 1 S) :
    (kernelBilinear A B (vaughanTypeII V) (longPart vonMangoldt U)
      (successorKernel w v X))^4 ≤
      ((R : ℝ)*(1+Real.log R)^3)^2*((S : ℝ)*(Real.log S)^2)^2*
        kernelGramEnergy A B (successorKernel w v X) := by
  have h₁ : (∑ r ∈ A, (vaughanTypeII V r)^2) ≤ (R : ℝ)*(1+Real.log R)^3 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      sum_subset_typeII_energy_le V R A hA
  have h₂ : (∑ s ∈ B, (longPart vonMangoldt U s)^2) ≤ (S : ℝ)*(Real.log S)^2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      sum_subset_vonMangoldt_energy_le U S B hB
  apply (kernelBilinear_fourth_le A B (vaughanTypeII V) (longPart vonMangoldt U)
    (successorKernel w v X)).trans
  have h₁' := pow_le_pow_left₀ (sum_nonneg (fun _ _ => sq_nonneg _)) h₁ 2
  have h₂' := pow_le_pow_left₀ (sum_nonneg (fun _ _ => sq_nonneg _)) h₂ 2
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul h₁' h₂' (sq_nonneg _) (sq_nonneg _))
    (kernelGramEnergy_nonneg A B _)

/-- The Gram energy is an exact four-corner correlation of the same
kernel, not a count with the output weights removed. -/
lemma kernelGramEnergy_four_corners {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (K : ι → κ → ℝ) :
    kernelGramEnergy A B K =
      ∑ r ∈ A, ∑ t ∈ A, ∑ s ∈ B, ∑ z ∈ B,
        K r s*K t s*K r z*K t z := by
  unfold kernelGramEnergy rowGram
  simp only [pow_two, sum_mul, mul_sum]
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro s hs
  exact sum_congr rfl (fun z _ => by ring)

lemma sum_fourth_le_card_cube {ι : Type*} (A : Finset ι) (f : ι → ℝ) :
    (∑ r ∈ A, f r)^4 ≤ (A.card : ℝ)^3*∑ r ∈ A, (f r)^4 := by
  have h₁ := sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) f
  have h₂ := sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) (fun r => (f r)^2)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at h₁ h₂
  have hh : (∑ r ∈ A, (f r)^2)^2 ≤ (A.card : ℝ)*∑ r ∈ A, (f r)^4 := by
    simpa only [← pow_mul] using h₂
  calc
    _ = ((∑ r ∈ A, f r)^2)^2 := by ring
    _ ≤ ((A.card : ℝ)*(∑ r ∈ A, (f r)^2))^2 :=
      pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ = (A.card : ℝ)^2*(∑ r ∈ A, (f r)^2)^2 := mul_pow _ _ _
    _ ≤ (A.card : ℝ)^2*((A.card : ℝ)*∑ r ∈ A, (f r)^4) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by ring

/-- Dyadic assembly retains the actual output discrepancy inside every
block, including the hyperbolic cutoff. -/
lemma successor_typeII_dyadic (w v : ℕ → ℝ) (N U V : ℕ) (hV : 1 ≤ V) :
    hyperbolicSum (vaughanTypeII V) (longPart vonMangoldt U)
      (fun n => w n-v n) N =
    ∑ j ∈ typeIILevels N U V,
      kernelBilinear (typeIILeftBlock N V j) (typeIIRightBlock N U j)
        (vaughanTypeII V) (longPart vonMangoldt U) (successorKernel w v N) := by
  classical
  let F (m n : ℕ) : ℝ := if m*n ≤ N then
    (vaughanTypeII V m*longPart vonMangoldt U n)*(w (m*n)-v (m*n)) else 0
  have hf (m : ℕ) (hm : m ≤ V) (n : ℕ) : F m n = 0 := by
    simp only [F, vaughanTypeII_eq_zero hm, zero_mul, ite_self]
  have hfilter : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, F m n) =
      ∑ m ∈ (Icc 1 N).filter (fun m => V < m), ∑ n ∈ Icc 1 N, F m n := by
    symm
    apply sum_filter_of_ne
    intro m hm h
    by_contra hn
    exact h (by simp only [hf m (Nat.le_of_not_gt hn), sum_const_zero])
  have hright (j m : ℕ) (hm : m ∈ typeIILeftBlock N V j) :
      (∑ n ∈ Icc 1 N, F m n) = ∑ n ∈ typeIIRightBlock N U j, F m n := by
    have hmj := typeIILeftBlock_bounds hV hm
    symm
    apply sum_subset
    · intro n hn
      obtain ⟨hnU,hnN⟩ := mem_Icc.mp hn
      exact mem_Icc.mpr ⟨by omega,hnN.trans (Nat.div_le_self N _)⟩
    · intro n hn hnB
      obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
      by_cases hUn : U < n
      · have hnDiv : ¬n ≤ N/2^j := by
          intro hnd
          exact hnB (mem_Icc.mpr ⟨hUn,hnd⟩)
        have hmn : ¬m*n ≤ N := by
          intro hmn
          have hh : n*2^j ≤ N := by
            have hmul := Nat.mul_le_mul_right n hmj.2.2.2.1.le
            nlinarith only [hmul,hmn]
          exact hnDiv ((Nat.le_div_iff_mul_le (by positivity)).mpr hh)
        simp only [F, if_neg hmn]
      · simp only [F, longPart_apply, if_neg hUn, mul_zero, zero_mul, ite_self]
  have hsum : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, F m n) =
      ∑ j ∈ typeIILevels N U V,
        ∑ m ∈ typeIILeftBlock N V j, ∑ n ∈ typeIIRightBlock N U j, F m n := by
    calc
      _ = ∑ j ∈ range (Nat.log 2 N+1), ∑ m ∈ typeIILeftBlock N V j,
          ∑ n ∈ Icc 1 N, F m n := by rw [hfilter,sum_typeII_left_blocks]
      _ = ∑ j ∈ range (Nat.log 2 N+1), ∑ m ∈ typeIILeftBlock N V j,
          ∑ n ∈ typeIIRightBlock N U j, F m n := by
        apply sum_congr rfl
        intro j hj
        exact sum_congr rfl (fun m hm => hright j m hm)
      _ = _ := by
        symm
        apply sum_filter_of_ne
        intro j hj h
        by_contra hn
        rcases typeII_inactive_blocks hV hn with he | he
        · exact h (by simp only [he,sum_empty])
        · exact h (by simp only [he,sum_empty,sum_const_zero])
  change _ = _ at hsum
  apply hsum.trans
  apply sum_congr rfl
  intro j hj
  unfold kernelBilinear
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro n hn
  dsimp [F,successorKernel]
  split_ifs <;> simp

noncomputable def successorTypeIIBlockFourthMajorant (w v : ℕ → ℝ)
    (N U V j : ℕ) : ℝ :=
  (((2^(j+1) : ℕ) : ℝ)*(1+Real.log (2^(j+1) : ℕ))^3)^2*
    (((N/2^j : ℕ) : ℝ)*(Real.log (N/2^j : ℕ))^2)^2*
      kernelGramEnergy (typeIILeftBlock N V j) (typeIIRightBlock N U j)
        (successorKernel w v N)

/-- An unconditional finite reduction of the entire Type II discrepancy
to centered four-corner correlations on its active dyadic blocks. -/
theorem successor_typeII_fourth_le_gram_sum (w v : ℕ → ℝ)
    (N U V : ℕ) (hV : 1 ≤ V) :
    (hyperbolicSum (vaughanTypeII V) (longPart vonMangoldt U)
      (fun n => w n-v n) N)^4 ≤
    ((typeIILevels N U V).card : ℝ)^3*
      ∑ j ∈ typeIILevels N U V, successorTypeIIBlockFourthMajorant w v N U V j := by
  rw [successor_typeII_dyadic w v N U V hV]
  apply (sum_fourth_le_card_cube _ _).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro j hj
  apply successor_typeII_block_fourth_le
  · intro m hm
    have hh := typeIILeftBlock_bounds hV hm
    exact mem_Icc.mpr ⟨hh.1,hh.2.2.2.2⟩
  · intro n hn
    have hh := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by omega,hh.2⟩

/-- The first three discrepancies in Vaughan's identity. -/
noncomputable def successorTypeIError (w v : ℕ → ℝ) (N U V : ℕ) : ℝ :=
  |weightedSum (shortPart vonMangoldt U) (fun n => w n-v n) N| +
  |hyperbolicSum (shortPart (μ : ArithmeticFunction ℝ) V) log
    (fun n => w n-v n) N| +
  |hyperbolicSum (vaughanTypeI U V) (ζ : ArithmeticFunction ℝ)
    (fun n => w n-v n) N|

lemma successor_typeII_abs_le_of_gram (w v : ℕ → ℝ)
    (N U V : ℕ) (hV : 1 ≤ V) (E : ℝ) (hE : 0 ≤ E)
    (H : ((typeIILevels N U V).card : ℝ)^3*
      (∑ j ∈ typeIILevels N U V, successorTypeIIBlockFourthMajorant w v N U V j) ≤ E^4) :
    |hyperbolicSum (vaughanTypeII V) (longPart vonMangoldt U)
      (fun n => w n-v n) N| ≤ E := by
  apply (pow_le_pow_iff_left₀ (abs_nonneg _) hE (by decide : 4 ≠ 0)).mp
  have h := (successor_typeII_fourth_le_gram_sum w v N U V hV).trans H
  simpa only [show (4 : ℕ)=2*2 by decide, pow_mul, sq_abs] using h

/-- A finite conditional prime-output criterion with the signed Type II
term replaced by an explicit centered Gram bound. Neither that Gram bound
nor the required Type I/main-term comparison is asserted unconditionally. -/
theorem prime_output_card_gt_of_gram (w v : ℕ → ℝ)
    (N U V : ℕ) (hN : 1 ≤ N) (hV : 1 ≤ V) (B K E : ℝ)
    (hB0 : 0 ≤ B) (hE : 0 ≤ E)
    (hw : ∀ n ∈ Icc 1 N, 0 ≤ w n) (hB : ∀ n ∈ Icc 1 N, w n ≤ B)
    (Hgram : ((typeIILevels N U V).card : ℝ)^3*
      (∑ j ∈ typeIILevels N U V, successorTypeIIBlockFourthMajorant w v N U V j) ≤ E^4)
    (Hmain : B*Real.log N*K+2*B*Real.sqrt N*Real.log N+
      successorTypeIError w v N U V+E < weightedSum vonMangoldt v N) :
    K < ((positivePrimeOutputs w N).card : ℝ) := by
  have hII := successor_typeII_abs_le_of_gram w v N U V hV E hE Hgram
  have hd := weighted_mangoldt_discrepancy_le w v U V N
  change |weightedSum vonMangoldt w N-weightedSum vonMangoldt v N| ≤
    successorTypeIError w v N U V+_ at hd
  have hdiff := hd.trans (add_le_add le_rfl hII)
  have hlo := neg_le_abs (weightedSum vonMangoldt w N-weightedSum vonMangoldt v N)
  have hup := weighted_mangoldt_le_prime_outputs w N hN B hB0 hw hB
  by_contra hc
  have hc' : ((positivePrimeOutputs w N).card : ℝ) ≤ K := le_of_not_gt hc
  have hcount := mul_le_mul_of_nonneg_left hc'
    (mul_nonneg hB0 (Real.log_natCast_nonneg N))
  linarith only [Hmain,hdiff,hlo,hup,hcount]

/-- The rectangle weight supplies genuine smooth predecessors when all
three input factors are smooth. This does not supply any prime outputs. -/
lemma rectangle_positive_output_smooth (P A B : Finset ℕ) (Y n : ℕ)
    (hP : ∀ p ∈ P, p ∈ Nat.smoothNumbers Y)
    (hA : ∀ a ∈ A, a ∈ Nat.smoothNumbers Y)
    (hB : ∀ b ∈ B, b ∈ Nat.smoothNumbers Y)
    (hn : 0 < rectangleOutputWeight P A B n) :
    n-1 ∈ Nat.smoothNumbers Y := by
  have hc : 0 < ((P ×ˢ (A ×ˢ B)).filter
      (fun z => z.1*z.2.1*z.2.2+1=n)).card := by
    unfold rectangleOutputWeight at hn
    exact_mod_cast hn
  obtain ⟨z,hz⟩ := card_pos.mp hc
  obtain ⟨hz,hzn⟩ := mem_filter.mp hz
  obtain ⟨hp,hab⟩ := mem_product.mp hz
  obtain ⟨ha,hb⟩ := mem_product.mp hab
  have hs := Nat.mul_mem_smoothNumbers
    (Nat.mul_mem_smoothNumbers (hP z.1 hp) (hA z.2.1 ha)) (hB z.2.2 hb)
  have he : n-1=z.1*z.2.1*z.2.2 := by omega
  rwa [he]

end Erdos821.AnalyticSieve.SuccessorVaughan
