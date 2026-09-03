import Submission.FiniteMixtureLaw

/-! Entropy selection on a finite mixture of cycles. The same selected scale
controls the mixture, rather than separately selected component scales. -/
namespace Erdos371.FiniteInformation
open Finset BlockPrimes EntropyScales
set_option autoImplicit false
universe u v

variable {ι : Type v} [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]

noncomputable def cyclicMixtureLaw (ρ : Law ι) : Law (Σ i, ZMod (N i)) :=
  sigmaLaw ρ (fun i => uniformLaw (ZMod (N i)))

def cyclicMixtureShift (x : Σ i, ZMod (N i)) : Σ i, ZMod (N i) := ⟨x.1,x.2+1⟩

def cyclicMixtureResidue (M : ℕ) (x : Σ i, ZMod (N i)) : ZMod M :=
  cyclicResidue (N x.1) M x.2

lemma cyclicMixture_stationary (ρ : Law ι) :
    mapLaw (cyclicMixtureLaw N ρ) (cyclicMixtureShift N) = cyclicMixtureLaw N ρ :=
  sigmaLaw_map_components ρ _ (fun i => Equiv.addRight (1 : ZMod (N i)))
    (fun _ => mapLaw_uniform_equiv _)

lemma cyclicMixture_semiconj (M : ℕ) (hd : ∀ i, M ∣ N i) :
    Function.Semiconj (cyclicMixtureResidue N M) (cyclicMixtureShift N)
      (Equiv.addRight (1 : ZMod M)) := by
  intro ⟨i,x⟩
  exact cyclicResidue_semiconj (hd i) x

lemma cyclicMixture_residue_uniform (ρ : Law ι) (M : ℕ) [NeZero M]
    (hd : ∀ i, M ∣ N i) :
    mapLaw (cyclicMixtureLaw N ρ) (cyclicMixtureResidue N M) = uniformLaw (ZMod M) := by
  unfold cyclicMixtureLaw cyclicMixtureResidue
  apply sigmaLaw_map_common ρ (fun i => uniformLaw (ZMod (N i)))
    (fun i => cyclicResidue (N i) M) (uniformLaw (ZMod M))
  intro i
  exact mapLaw_uniform_cyclicResidue (N i) M (hd i)

variable {A : Type u} [Fintype A]

lemma cyclicMixture_labelBlock (L : ∀ i, ZMod (N i) → A) (H : ℕ)
    (i : ι) (x : ZMod (N i)) :
    labelBlock (cyclicMixtureShift N) (fun y => L y.1 y.2) H ⟨i,x⟩ =
      labelBlock (Equiv.addRight (1 : ZMod (N i))) (L i) H x := by
  funext j
  unfold labelBlock
  have he := sigma_iterate (fun i => Equiv.addRight (1 : ZMod (N i))) j.val i x
  exact congrArg (fun y => L y.1 y.2) he

/-- The entropy horizon is chosen before the component count, component
lengths, mixture law, and labels. -/
theorem mixture_cyclic_prime_entropy_decrement
    (H₀ : ℕ) (hH₀ : 1 < H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ (ι : Type v) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)],
      (∀ i, (∏ n ∈ range K, primorial (factorialScale H₀ n)) ∣ N i) →
      ∀ (ρ : Law ι) (L : ∀ i, ZMod (N i) → A),
        ∃ n < K, mutualInformation
          (blockJointLaw (cyclicMixtureLaw N ρ) (cyclicMixtureShift N)
            (fun x => L x.1 x.2) (cyclicMixtureResidue N (primorial (factorialScale H₀ n)))
            (factorialScale H₀ n)) <
              ε * factorialScale H₀ n / Real.log (factorialScale H₀ n : ℝ) := by
  obtain ⟨K,hK,hdec⟩ := stationary_entropy_decrement (A := A) H₀ hH₀ (Real.log 4) ε
    (Real.log_nonneg (by norm_num)) hε
  refine ⟨K,hK,?_⟩
  intro ι _ N _ hd ρ L
  apply hdec (Σ i, ZMod (N i)) (cyclicMixtureLaw N ρ) (cyclicMixtureShift N)
    (cyclicMixture_stationary N ρ) (fun x => L x.1 x.2)
    (fun H => ZMod (primorial H)) (fun H => cyclicMixtureResidue N (primorial H))
    (fun _ => Equiv.addRight 1)
  · intro n hn
    exact cyclicMixture_semiconj N _ (fun i =>
      (dvd_prod_of_mem (fun n => primorial (factorialScale H₀ n)) (mem_range.mpr hn)).trans (hd i))
  · intro n hn
    simpa only [ZMod.card] using log_primorial_le (factorialScale H₀ n)

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable (q : κ → ℕ) [∀ k, NeZero (q k)]

/-- The information estimate is applied to the joint mixture law. In
particular, no componentwise small-information hypothesis is required. -/
theorem mixture_cyclic_gap_average_sq_le_information
    (hcop : Pairwise (fun k l => Nat.Coprime (q k) (q l)))
    (ρ : Law ι) (M H : ℕ) [NeZero M] (hM : ∀ i, M ∣ N i) (hd : (∏ k, q k) ∣ M)
    (hq : ∀ k, 2*q k ≤ H) (L : ∀ i, ZMod (N i) → A) (C : A → A → ℝ)
    (hC : ∀ a b, |C a b| ≤ 1) :
    (mean ρ (fun i => (∑ k, cyclicGapDiscrepancy (N i) (q k) (L i) C) / Fintype.card κ))^2 ≤
      8 * mutualInformation
        (blockJointLaw (cyclicMixtureLaw N ρ) (cyclicMixtureShift N) (fun x => L x.1 x.2)
          (cyclicMixtureResidue N M) H) / Fintype.card κ := by
  let P := blockJointLaw (cyclicMixtureLaw N ρ) (cyclicMixtureShift N)
    (fun x => L x.1 x.2) (cyclicMixtureResidue N M) H
  let F : (Fin H → A) → ∀ k, ZMod (q k) → ℝ := fun a k j => blockPairArray H (q k) (hq k) C a j
  have hP : secondMarginal P = uniformLaw (ZMod M) := by
    rw [secondMarginal_blockJointLaw]
    exact cyclicMixture_residue_uniform N ρ M hM
  have hh := residue_choice_sq_le_information q hcop M hd P hP F
    (fun a k j => blockPairArray_abs_le H (q k) (hq k) C hC a j)
  have hdiv (k : κ) : q k ∣ M := (dvd_prod_of_mem q (mem_univ k)).trans hd
  have he : mean P (fun ay => (∑ k, (F ay.1 k (-cyclicResidue M (q k) ay.2) -
      mean (uniformLaw (ZMod (q k))) (F ay.1 k))) / Fintype.card κ) =
        mean ρ (fun i => (∑ k, cyclicGapDiscrepancy (N i) (q k) (L i) C) / Fintype.card κ) := by
    simp only [P, blockJointLaw, mean_mapLaw, cyclicMixtureLaw, mean_sigmaLaw]
    apply congrArg (mean ρ)
    funext i
    rw [mean_div, mean_finset_sum]
    congr 1
    apply sum_congr rfl
    intro k _
    have hres (x : ZMod (N i)) :
        cyclicResidue M (q k) (cyclicMixtureResidue N M ⟨i,x⟩) = cyclicResidue (N i) (q k) x :=
      congrFun (cyclicResidue_comp (N i) M (q k) (hM i) (hdiv k)) x
    simp only [F, cyclicMixture_labelBlock, blockPairArray_cyclicBlock, hres]
    exact mean_cyclic_selection_discrepancy (N i) (q k) ((hdiv k).trans (hM i))
      (fun x => C (L i x) (L i (x+(q k : ZMod (N i)))))
  rw [he] at hh
  exact hh

/-- One scale works simultaneously for every bounded observable on the
weighted mixture. The weights and labels are fixed before that scale is chosen. -/
theorem mixture_cyclic_prime_gap_transfer
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ (ι : Type v) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)],
      (∀ i, (∏ n ∈ range K, primorial (factorialScale H₀ n)) ∣ N i) →
      ∀ (ρ : Law ι) (L : ∀ i, ZMod (N i) → A), ∃ n < K,
        ∀ C : A → A → ℝ, (∀ a b, |C a b| ≤ 1) →
          |mean ρ (fun i => (∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
            cyclicGapDiscrepancy (N i) p (L i) C) /
              (halfBlockPrimes (factorialScale H₀ n)).card)| < ε := by
  classical
  let δ : ℝ := ε^2 * Real.log 2 / 64
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK,hdec⟩ := mixture_cyclic_prime_entropy_decrement (A := A) H₀ (by omega) δ hδ
  refine ⟨K,hK,?_⟩
  intro ι _ N _ hd ρ L
  obtain ⟨n,hn,hinfo⟩ := hdec ι N hd ρ L
  refine ⟨n,hn,?_⟩
  intro C hC
  let H := factorialScale H₀ n
  have hH : 8 ≤ H := hH₀.trans (factorialScale_ge H₀ n)
  have hnon := halfBlockPrimes_nonempty H (by omega)
  letI : Nonempty (halfBlockPrimes H) := ⟨⟨hnon.choose,hnon.choose_spec⟩⟩
  have hM (i : ι) : primorial H ∣ N i :=
    (dvd_prod_of_mem (fun n => primorial (factorialScale H₀ n)) (mem_range.mpr hn)).trans (hd i)
  have hb := mixture_cyclic_gap_average_sq_le_information N
    (fun p : halfBlockPrimes H => (p : ℕ)) (halfBlockPrimes_pairwise_coprime H) ρ
    (primorial H) H hM (halfBlockPrimes_prod_dvd_primorial H)
    (fun p => (mem_halfBlockPrimes.mp p.property).2) L C hC
  have hsum (i : ι) : (∑ p : halfBlockPrimes H, cyclicGapDiscrepancy (N i) p (L i) C) =
      ∑ p ∈ halfBlockPrimes H, cyclicGapDiscrepancy (N i) p (L i) C :=
    sum_coe_sort (halfBlockPrimes H) (fun p => cyclicGapDiscrepancy (N i) p (L i) C)
  simp only [hsum, Fintype.card_coe] at hb
  have hcard : 0 < ((halfBlockPrimes H).card : ℝ) := by exact_mod_cast card_pos.mpr hnon
  have hlower := halfBlockPrimes_card_lower H hH
  have hscaled := mul_le_mul_of_nonneg_left hlower (by positivity : (0 : ℝ) ≤ ε^2/8)
  have hbound : δ*H/Real.log (H : ℝ) ≤ (ε^2/8)*((halfBlockPrimes H).card : ℝ) := by
    convert hscaled using 1
    dsimp [δ]
    ring
  have hi : mutualInformation
      (blockJointLaw (cyclicMixtureLaw N ρ) (cyclicMixtureShift N) (fun x => L x.1 x.2)
        (cyclicMixtureResidue N (primorial H)) H) <
          (ε^2/8)*((halfBlockPrimes H).card : ℝ) := hinfo.trans_le hbound
  have hr : 8*mutualInformation
      (blockJointLaw (cyclicMixtureLaw N ρ) (cyclicMixtureShift N) (fun x => L x.1 x.2)
        (cyclicMixtureResidue N (primorial H)) H) / ((halfBlockPrimes H).card : ℝ) < ε^2 := by
    apply (div_lt_iff₀ hcard).mpr
    nlinarith
  have hs := hb.trans_lt hr
  change |mean ρ (fun i => (∑ p ∈ halfBlockPrimes H, cyclicGapDiscrepancy (N i) p (L i) C) /
    ((halfBlockPrimes H).card : ℝ))| < ε
  nlinarith [sq_abs (mean ρ (fun i => (∑ p ∈ halfBlockPrimes H,
    cyclicGapDiscrepancy (N i) p (L i) C) / ((halfBlockPrimes H).card : ℝ)))]

#print axioms mixture_cyclic_prime_entropy_decrement
#print axioms mixture_cyclic_gap_average_sq_le_information
#print axioms mixture_cyclic_prime_gap_transfer
end Erdos371.FiniteInformation
