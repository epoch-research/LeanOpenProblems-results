import Submission.HarmonicPrimeGapTransfer

/-! Positive prefix mixtures for arbitrary decreasing nonnegative weights.
The reciprocal-length moment gives an explicit common-scale entropy error. -/
namespace Erdos371.FiniteInformation
open Finset Filter BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

lemma weighted_prefix_abel (w F : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range (N+1), w n*F n) =
      (N+1 : ℝ)*w N*prefixMean (N+1) F +
        ∑ k ∈ range N, (k+1 : ℝ)*(w k-w (k+1))*prefixMean (k+1) F := by
  induction N with
  | zero => simp [prefixMean]
  | succ N ih =>
    rw [sum_range_succ,ih,sum_range_succ]
    have hN : (N+1 : ℝ) ≠ 0 := by positivity
    have hN' : (N+2 : ℝ) ≠ 0 := by positivity
    have he : prefixMean (N+1+1) F =
        ((N+1 : ℝ)*prefixMean (N+1) F+F (N+1))/(N+2 : ℝ) := by
      unfold prefixMean
      rw [sum_range_succ]
      simp only [Nat.cast_add,Nat.cast_one]
      field_simp
      ring
    rw [he]
    simp only [Nat.cast_add,Nat.cast_one]
    field_simp
    ring

noncomputable def decreasingPrefixWeight (w : ℕ → ℝ) (N : ℕ) (i : Fin (N+1)) : ℝ :=
  if i.val=0 then (N+1 : ℝ)*w N else (i.val : ℝ)*(w (i.val-1)-w i.val)

lemma decreasingPrefixWeight_nonneg (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n≤N, 0 ≤ w n) (hanti : AntitoneOn w (Set.Iic N)) (i : Fin (N+1)) :
    0 ≤ decreasingPrefixWeight w N i := by
  unfold decreasingPrefixWeight
  split_ifs
  · exact mul_nonneg (by positivity) (hw N le_rfl)
  · apply mul_nonneg (Nat.cast_nonneg _)
    exact sub_nonneg.mpr (hanti (by simp only [Set.mem_Iic]; omega)
      (by simp only [Set.mem_Iic]; omega) (Nat.sub_le _ _))

lemma decreasingPrefixWeight_sum_test (w : ℕ → ℝ) (N : ℕ) (G : ℕ → ℝ) :
    (∑ i, decreasingPrefixWeight w N i * G (harmonicPrefixLength N i)) =
      (N+1 : ℝ)*w N*G (N+1) +
        ∑ k ∈ range N, (k+1 : ℝ)*(w k-w (k+1))*G (k+1) := by
  rw [Fin.sum_univ_succ]
  simp only [decreasingPrefixWeight,harmonicPrefixLength,Fin.val_zero,if_true,Fin.val_succ,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.add_sub_cancel,
    Nat.cast_add,Nat.cast_one]
  rw [← sum_range (n := N) (fun k => (k+1 : ℝ)*(w k-w (k+1))*G (k+1))]

lemma decreasingPrefixWeight_sum (w : ℕ → ℝ) (N : ℕ) :
    (∑ i, decreasingPrefixWeight w N i) = ∑ n ∈ range (N+1), w n := by
  have hid (k : ℕ) (hk : 0 < k) : prefixMean k (fun _ => (1 : ℝ)) = 1 := by
    simp [prefixMean,show (k : ℝ) ≠ 0 by exact_mod_cast hk.ne']
  have ha := weighted_prefix_abel w (fun _ => 1) N
  simp only [mul_one,hid _ (Nat.succ_pos _)] at ha
  have he := decreasingPrefixWeight_sum_test w N (fun _ => (1 : ℝ))
  simp only [mul_one] at he
  exact he.trans ha.symm

noncomputable def decreasingPrefixLaw (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n≤N, 0 ≤ w n) (hanti : AntitoneOn w (Set.Iic N))
    (hW : 0 < ∑ n ∈ range (N+1), w n) : Law (Fin (N+1)) where
  mass i := decreasingPrefixWeight w N i / ∑ n ∈ range (N+1), w n
  nonneg i := div_nonneg (decreasingPrefixWeight_nonneg w N hw hanti i) hW.le
  total := by rw [← sum_div,decreasingPrefixWeight_sum,div_self hW.ne']

lemma decreasingPrefixLaw_representation (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n≤N, 0 ≤ w n) (hanti : AntitoneOn w (Set.Iic N))
    (hW : 0 < ∑ n ∈ range (N+1), w n) (F : ℕ → ℝ) :
    mean (decreasingPrefixLaw w N hw hanti hW) (fun i => prefixMean (harmonicPrefixLength N i) F) =
      (∑ n ∈ range (N+1), w n*F n)/(∑ n ∈ range (N+1), w n) := by
  unfold mean decreasingPrefixLaw
  simp only [div_mul_eq_mul_div,← sum_div]
  congr 1
  rw [decreasingPrefixWeight_sum_test w N (fun k => prefixMean k F),← weighted_prefix_abel]

lemma decreasingPrefixLaw_reciprocal_length (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n≤N, 0 ≤ w n) (hanti : AntitoneOn w (Set.Iic N))
    (hW : 0 < ∑ n ∈ range (N+1), w n) :
    mean (decreasingPrefixLaw w N hw hanti hW) (fun i => (1 : ℝ)/harmonicPrefixLength N i) =
      w 0/(∑ n ∈ range (N+1), w n) := by
  let F : ℕ → ℝ := fun n => if n=0 then 1 else 0
  have hF (k : ℕ) (hk : 0 < k) : prefixMean k F = (1 : ℝ)/k := by
    simp [prefixMean,F,hk]
  have he : (fun i : Fin (N+1) => (1 : ℝ)/harmonicPrefixLength N i) =
      (fun i => prefixMean (harmonicPrefixLength N i) F) := by
    funext i
    exact (hF _ (harmonicPrefixLength_pos N i)).symm
  rw [he,decreasingPrefixLaw_representation]
  congr 1
  simp [F,mul_ite]

/-- Generic weighted prefix transfer, with a fully explicit dependence on
the ratio of the first weight to total mass. No dilation assumption is used. -/
theorem decreasing_weight_prime_gap_transfer {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) (w : ℕ → ℝ),
      (∀ n≤N, 0 ≤ w n) → AntitoneOn w (Set.Iic N) →
      0 < (∑ n ∈ range (N+1), w n) →
      D*w 0/(∑ n ∈ range (N+1), w n) < ε/2 →
      ∀ L : ℕ → A, ∃ n < K, ∀ C : A → A → ℝ, (∀ a b, |C a b| ≤ 1) →
        |(∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
          (∑ m ∈ range (N+1), w m*((p : ℝ)*(if p ∣ m then C (L m) (L (m+p)) else 0)-
            C (L m) (L (m+p)))) / (∑ m ∈ range (N+1), w m)) /
              (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  classical
  obtain ⟨K,hK,htransfer⟩ := mixture_cyclic_prime_gap_transfer (A := A) H₀ hH₀ (ε/2) (by positivity)
  let Q : ℕ := ∏ n ∈ range K, primorial (factorialScale H₀ n)
  let B : ℕ := (range K).sup (factorialScale H₀)
  let T : ℕ := Q*(B+1)
  let D : ℝ := 2*(B+1 : ℝ)*T+2*B*(B+1 : ℝ)+1
  have hQ : 0 < Q := prod_pos (fun _ _ => primorial_pos _)
  refine ⟨K,hK,D,by dsimp [D]; positivity,?_⟩
  intro N w hw hanti hW hsmall L
  let ρ := decreasingPrefixLaw w N hw hanti hW
  let M (i : Fin (N+1)) := Q*(harmonicPrefixLength N i/Q+B+1)
  have hprops (i : Fin (N+1)) :
      harmonicPrefixLength N i ≤ M i ∧ B ≤ M i ∧ M i-harmonicPrefixLength N i ≤ T := by
    have hd := Nat.div_add_mod (harmonicPrefixLength N i) Q
    have hm := Nat.mod_lt (harmonicPrefixLength N i) hQ
    have hB : B ≤ Q*(B+1) := by nlinarith
    have hme : M i = Q*(harmonicPrefixLength N i/Q)+Q*(B+1) := by dsimp [M]; ring
    dsimp [T]
    rw [hme]
    constructor
    · nlinarith
    constructor <;> omega
  have hM (i : Fin (N+1)) : 0 < M i := (harmonicPrefixLength_pos N i).trans_le (hprops i).1
  letI (i : Fin (N+1)) : NeZero (M i) := ⟨(hM i).ne'⟩
  have hQM (i : Fin (N+1)) : Q ∣ M i := dvd_mul_right Q _
  obtain ⟨n,hn,hscale⟩ := htransfer (Fin (N+1)) M hQM ρ (fun _ x => L x.val)
  refine ⟨n,hn,?_⟩
  intro C hC
  let S := halfBlockPrimes (factorialScale H₀ n)
  have hH : factorialScale H₀ n ≤ B := le_sup (mem_range.mpr hn)
  have hS : S.Nonempty := halfBlockPrimes_nonempty _
    (le_trans (by omega : 4 ≤ H₀) (factorialScale_ge H₀ n))
  let U (i : Fin (N+1)) := (∑ p ∈ S, naturalGapDiscrepancy (harmonicPrefixLength N i) p L C)/(S.card : ℝ)
  let V (i : Fin (N+1)) := (∑ p ∈ S, cyclicGapDiscrepancy (M i) p (fun x => L x.val) C)/(S.card : ℝ)
  have he (i : Fin (N+1)) : |U i-V i| ≤ D/harmonicPrefixLength N i := by
    dsimp [U,V]
    rw [← sub_div,← sum_sub_distrib]
    apply abs_finset_average_le S hS
    intro p hp
    have hpH := (mem_halfBlockPrimes.mp hp).2
    have h := natural_cyclic_round_up_error (harmonicPrefixLength N i) (M i) p B T
      (harmonicPrefixLength_pos N i) (hprops i).1 (hprops i).2.2
      (by omega) (hprops i).2.1 L C hC
    exact h.trans (div_le_div_of_nonneg_right (by dsimp [D]; linarith) (Nat.cast_nonneg _))
  have herr : |mean ρ U-mean ρ V| ≤ D*w 0/(∑ m ∈ range (N+1), w m) := by
    rw [← mean_sub]
    apply (abs_mean_le_mean_abs _ _).trans
    apply (mean_mono _ _ _ he).trans_eq
    have hid : (fun i => D/(harmonicPrefixLength N i : ℝ)) =
        (fun i => D*((1 : ℝ)/harmonicPrefixLength N i)) := by funext i; ring
    rw [hid,mean_const_mul]
    dsimp only [ρ]
    rw [decreasingPrefixLaw_reciprocal_length]
    ring
  have hu : mean ρ U =
      (∑ p ∈ S, (∑ m ∈ range (N+1), w m*((p : ℝ)*(if p ∣ m then C (L m) (L (m+p)) else 0)-
        C (L m) (L (m+p)))) / (∑ m ∈ range (N+1), w m)) / (S.card : ℝ) := by
    dsimp [U]
    rw [mean_div,mean_finset_sum]
    congr 1
    apply sum_congr rfl
    intro p hp
    have hid (k : ℕ) : naturalGapDiscrepancy k p L C =
        prefixMean k (fun m => (p : ℝ)*(if p ∣ m then C (L m) (L (m+p)) else 0)-C (L m) (L (m+p))) := by
      simp only [naturalGapDiscrepancy,prefixMean,sum_sub_distrib,sub_div,← mul_sum]
      ring
    simp_rw [hid]
    exact decreasingPrefixLaw_representation w N hw hanti hW _
  have hv := hscale C hC
  change |mean ρ V| < ε/2 at hv
  have htri := abs_sub_le (mean ρ U) (mean ρ V) 0
  simp only [sub_zero] at htri
  rw [← hu]
  linarith

#print axioms decreasingPrefixLaw_representation
#print axioms decreasingPrefixLaw_reciprocal_length
#print axioms decreasing_weight_prime_gap_transfer
end Erdos371.FiniteInformation
