import Submission.HarmonicPrimeGapTransfer

/-! Componentwise entropy budgets for a mixture of cycles. The selected scale
controls the mean square discrepancy, with a separate observable in each
component. The horizon does not depend on the number of components. -/
namespace Erdos371.FiniteInformation
open Finset BlockPrimes EntropyScales EntropyDecrement
set_option autoImplicit false
universe u v

lemma mean_nonneg_of_nonneg {ι : Type*} [Fintype ι] (ρ : Law ι) (F : ι → ℝ)
    (hF : ∀ i, 0 ≤ F i) : 0 ≤ mean ρ F :=
  sum_nonneg fun i _ => mul_nonneg (ρ.nonneg i) (hF i)

lemma mean_sq_le_mean_square {ι : Type*} [Fintype ι] (ρ : Law ι) (F : ι → ℝ) :
    (mean ρ F)^2 ≤ mean ρ (fun i => (F i)^2) := by
  have hn := mean_nonneg_of_nonneg ρ (fun i => (F i-mean ρ F)^2) (fun _ => sq_nonneg _)
  have he : mean ρ (fun i => (F i-mean ρ F)^2) =
      mean ρ (fun i => (F i)^2)-(mean ρ F)^2 := by
    have hp : (fun i => (F i-mean ρ F)^2) =
        (fun i => (F i)^2 - (2*mean ρ F)*F i+(mean ρ F)^2) := by funext i; ring
    rw [hp,mean_add,mean_sub,mean_const_mul,mean_const]
    ring
  rw [he] at hn
  linarith

/-- Average the information in each component, not the information in the
unconditioned mixture. In particular, no entropy of the component index is
charged. -/
theorem componentwise_cyclic_prime_entropy_decrement {A : Type u} [Fintype A]
    (H₀ : ℕ) (hH₀ : 1 < H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ (ι : Type v) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)],
      (∀ i, (∏ n ∈ range K, primorial (factorialScale H₀ n)) ∣ N i) →
      ∀ (ρ : Law ι) (L : ∀ i, ZMod (N i) → A),
        ∃ n < K, mean ρ (fun i => mutualInformation
          (blockJointLaw (uniformLaw (ZMod (N i))) (Equiv.addRight 1) (L i)
            (cyclicResidue (N i) (primorial (factorialScale H₀ n)))
            (factorialScale H₀ n))) <
              ε * factorialScale H₀ n / Real.log (factorialScale H₀ n : ℝ) := by
  obtain ⟨K,hK,hdec⟩ := exists_factorial_decrement_horizon H₀ hH₀
    (Real.log (Fintype.card A)) (Real.log 4) ε (Real.log_nonneg (by norm_num)) hε
  refine ⟨K,hK,?_⟩
  intro ι _ N _ hd ρ L
  let E (H : ℕ) := mean ρ (fun i => entropy
    (blockLaw (uniformLaw (ZMod (N i))) (Equiv.addRight 1) (L i) H))
  let I (H : ℕ) := mean ρ (fun i => mutualInformation
    (blockJointLaw (uniformLaw (ZMod (N i))) (Equiv.addRight 1) (L i)
      (cyclicResidue (N i) (primorial H)) H))
  apply hdec E I
  · intro H
    exact mean_nonneg_of_nonneg ρ _ (fun _ => entropy_nonneg _)
  · apply (mean_mono ρ _ (fun _ => Real.log (Fintype.card A)*H₀) ?_).trans_eq
      (mean_const _ _)
    intro i
    exact (entropy_blockLaw_le _ _ _ _).trans_eq (mul_comm _ _)
  · intro n hn
    have hM (i : ι) : primorial (factorialScale H₀ n) ∣ N i :=
      (dvd_prod_of_mem (fun j => primorial (factorialScale H₀ j))
        (mem_range.mpr hn)).trans (hd i)
    have hrec (i : ι) := stationary_block_entropy_recurrence
      (uniformLaw (ZMod (N i))) (Equiv.addRight 1) (mapLaw_uniform_equiv _) (L i)
      (cyclicResidue (N i) (primorial (factorialScale H₀ n)))
      (Equiv.addRight 1) (cyclicResidue_semiconj (hM i))
      (factorialScale H₀ n) ((n+2)^2)
    have hr (i : ι) : entropy
        (mapLaw (uniformLaw (ZMod (N i)))
          (cyclicResidue (N i) (primorial (factorialScale H₀ n)))) ≤
          Real.log 4 * factorialScale H₀ n := by
      exact (entropy_le_log_card _).trans (by
        simpa only [ZMod.card] using log_primorial_le (factorialScale H₀ n))
    have hh := mean_mono ρ _ _ (fun i => (hrec i).trans (add_le_add (hr i) le_rfl))
    simp only [Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,
      mean_add,mean_const,mean_const_mul,mean_sub] at hh
    simpa only [E,I,factorialScale_succ] using hh

/-- This version permits any sufficiently numerous family of primes in the
block. It bounds the AVERAGE SQUARE, before taking component signs or weights. -/
theorem componentwise_cyclic_prime_subset_transfer {A : Type u} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (S : ℕ → Finset ℕ)
    (hS : ∀ H, H₀ ≤ H → S H ⊆ halfBlockPrimes H)
    (hcard : ∀ H, H₀ ≤ H → c*H/Real.log (H : ℝ) ≤ (S H).card) :
    ∃ K > 0, ∀ (ι : Type v) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)],
      (∀ i, (∏ n ∈ range K, primorial (factorialScale H₀ n)) ∣ N i) →
      ∀ (ρ : Law ι) (L : ∀ i, ZMod (N i) → A), ∃ n < K,
        ∀ C : ι → A → A → ℝ, (∀ i a b, |C i a b| ≤ 1) →
          mean ρ (fun i => ((∑ p ∈ S (factorialScale H₀ n),
            cyclicGapDiscrepancy (N i) p (L i) (C i)) /
              (S (factorialScale H₀ n)).card)^2) < ε^2 := by
  classical
  let δ : ℝ := ε^2*c/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK,hdec⟩ := componentwise_cyclic_prime_entropy_decrement
    (A := A) H₀ (by omega) δ hδ
  refine ⟨K,hK,?_⟩
  intro ι _ N _ hd ρ L
  obtain ⟨n,hn,hi⟩ := hdec ι N hd ρ L
  refine ⟨n,hn,?_⟩
  intro C hC
  let H := factorialScale H₀ n
  have hH : H₀ ≤ H := factorialScale_ge H₀ n
  have hH0 : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hcardpos : 0 < ((S H).card : ℝ) := (div_pos (mul_pos hc hH0) hlog).trans_le (hcard H hH)
  have hnon : (S H).Nonempty := card_pos.mp (by exact_mod_cast hcardpos)
  letI : Nonempty (S H) := ⟨⟨hnon.choose,hnon.choose_spec⟩⟩
  have hmem (p : S H) := mem_halfBlockPrimes.mp (hS H hH p.property)
  letI (p : S H) : NeZero (p : ℕ) := ⟨(hmem p).1.ne_zero⟩
  have hcop : Pairwise (fun p q : S H => Nat.Coprime (p : ℕ) (q : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (hmem p).1 (hmem q).1).mpr
      (fun he => hpq (Subtype.ext he))
  have hprod : (∏ p : S H, (p : ℕ)) ∣ primorial H := by
    have he : (∏ p : S H, (p : ℕ)) = ∏ p ∈ S H, p := prod_coe_sort (S H) id
    have he' : (∏ p : halfBlockPrimes H, (p : ℕ)) = ∏ p ∈ halfBlockPrimes H, p :=
      prod_coe_sort (halfBlockPrimes H) id
    rw [he]
    apply (prod_dvd_prod_of_subset (S H) (halfBlockPrimes H) id (hS H hH)).trans
    simp only [id_eq]
    rw [← he']
    exact halfBlockPrimes_prod_dvd_primorial H
  have hM (i : ι) : primorial H ∣ N i :=
    (dvd_prod_of_mem (fun j => primorial (factorialScale H₀ j)) (mem_range.mpr hn)).trans (hd i)
  have hb (i : ι) := cyclic_gap_average_sq_le_information
    (fun p : S H => (p : ℕ)) hcop (N i) (primorial H) H (hM i) hprod
      (fun p => (hmem p).2) (L i) (C i) (hC i)
  have hsum (i : ι) : (∑ p : S H, cyclicGapDiscrepancy (N i) (p : ℕ) (L i) (C i)) =
      ∑ p ∈ S H, cyclicGapDiscrepancy (N i) p (L i) (C i) :=
    sum_coe_sort (S H) (fun p => cyclicGapDiscrepancy (N i) p (L i) (C i))
  simp only [hsum,Fintype.card_coe] at hb
  have havg := mean_mono ρ _ _ hb
  rw [mean_div,mean_const_mul] at havg
  have hbound : δ*H/Real.log (H : ℝ) ≤ (ε^2/8)*(S H).card := by
    convert mul_le_mul_of_nonneg_left (hcard H hH) (by positivity : 0 ≤ ε^2/8) using 1
    dsimp [δ]
    ring
  have hi' := hi.trans_le hbound
  apply havg.trans_lt
  apply (div_lt_iff₀ hcardpos).mpr
  nlinarith

lemma mean_abs_lt_of_mean_square_lt {ι : Type*} [Fintype ι] (ρ : Law ι)
    (F : ι → ℝ) (ε : ℝ) (hε : 0 < ε)
    (h : mean ρ (fun i => (F i)^2) < ε^2) :
    mean ρ (fun i => |F i|) < ε := by
  have hh := mean_sq_le_mean_square ρ (fun i => |F i|)
  simp only [sq_abs] at hh
  have hn := mean_nonneg_of_nonneg ρ (fun i => |F i|) (fun _ => abs_nonneg _)
  nlinarith

/-- Component observables may be selected after the common entropy scale.
There is still a single scale for the whole mixture. -/
theorem componentwise_cyclic_prime_subset_L1_transfer {A : Type u} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (S : ℕ → Finset ℕ)
    (hS : ∀ H, H₀ ≤ H → S H ⊆ halfBlockPrimes H)
    (hcard : ∀ H, H₀ ≤ H → c*H/Real.log (H : ℝ) ≤ (S H).card) :
    ∃ K > 0, ∀ (ι : Type v) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)],
      (∀ i, (∏ n ∈ range K, primorial (factorialScale H₀ n)) ∣ N i) →
      ∀ (ρ : Law ι) (L : ∀ i, ZMod (N i) → A), ∃ n < K,
        ∀ C : ι → A → A → ℝ, (∀ i a b, |C i a b| ≤ 1) →
          mean ρ (fun i => |(∑ p ∈ S (factorialScale H₀ n),
            cyclicGapDiscrepancy (N i) p (L i) (C i)) /
              (S (factorialScale H₀ n)).card|) < ε := by
  obtain ⟨K,hK,htrans⟩ := componentwise_cyclic_prime_subset_transfer
    (A := A) H₀ hH₀ ε c hε hc S hS hcard
  refine ⟨K,hK,?_⟩
  intro ι _ N _ hd ρ L
  obtain ⟨n,hn,h⟩ := htrans ι N hd ρ L
  exact ⟨n,hn,fun C hC => mean_abs_lt_of_mean_square_lt ρ _ ε hε (h C hC)⟩

#print axioms componentwise_cyclic_prime_entropy_decrement
#print axioms componentwise_cyclic_prime_subset_transfer
#print axioms componentwise_cyclic_prime_subset_L1_transfer
end Erdos371.FiniteInformation
