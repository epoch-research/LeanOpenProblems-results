import Submission.HarmonicPrefixOddEnergy

/-! Fixed integer quotient reindexing of harmonic-prefix mixtures. The
estimate holds for any bounded function, without multiplier invariance. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def harmonicRawRange (N : ℕ) (G : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range N, G n/(n+1 : ℝ)

lemma harmonicRawRange_Icc_error (N : ℕ) (G : ℕ → ℝ) (hG : ∀ n, |G n| ≤ 1) :
    |harmonicRawRange N G-∑ n ∈ Icc 1 N, G n/(n : ℝ)| ≤ 2 := by
  cases N with
  | zero => simp [harmonicRawRange]
  | succ N => exact harmonic_range_Icc_sum_error N G hG

lemma harmonicRawRange_endpoint_error (M N : ℕ) (hMN : M ≤ N)
    (G : ℕ → ℝ) (hG : ∀ n, |G n| ≤ 1) :
    |harmonicRawRange N G-harmonicRawRange M G| ≤ (N-M : ℕ) := by
  have he : harmonicRawRange N G-harmonicRawRange M G =
      ∑ k ∈ range (N-M), G (M+k)/(M+k+1 : ℝ) := by
    unfold harmonicRawRange
    have h := sum_range_add (fun n => G n/(n+1 : ℝ)) M (N-M)
    rw [Nat.add_sub_of_le hMN] at h
    rw [h]
    simp only [Nat.cast_add]
    ring
  rw [he]
  have hbound (k : ℕ) : |G (M+k)/(M+k+1 : ℝ)| ≤ 1 := by
    rw [abs_div,abs_of_pos (by positivity : (0 : ℝ)<M+k+1)]
    apply (div_le_one (by positivity)).mpr
    exact (hG (M+k)).trans (by have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _; have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith)
  simpa only [one_mul] using abs_sum_range_le (N-M) _ 1 (fun k _ => hbound k)

lemma harmonicRawRange_div_endpoint_error (p N : ℕ) (hp : 0 < p)
    (G : ℕ → ℝ) (hG : ∀ n, |G n| ≤ 1) :
    |harmonicRawRange N G-harmonicRawRange (N/p) G| ≤ (p : ℝ)+4 := by
  have h₁ := harmonicRawRange_Icc_error N G hG
  have h₂ := harmonicRawRange_Icc_error (N/p) G hG
  have h₃ := harmonic_div_endpoint_bound p N hp G hG
  have ht₁ := abs_sub_le (harmonicRawRange N G) (∑ n ∈ Icc 1 N, G n/(n : ℝ))
    (harmonicRawRange (N/p) G)
  have ht₂ := abs_sub_le (∑ n ∈ Icc 1 N, G n/(n : ℝ)) (∑ n ∈ Icc 1 (N/p), G n/(n : ℝ))
    (harmonicRawRange (N/p) G)
  rw [abs_sub_comm (∑ n ∈ Icc 1 (N/p), G n/(n : ℝ))] at ht₂
  linarith

noncomputable def quotientHarmonicBlock (p m : ℕ) : ℝ :=
  ∑ r ∈ range p, (1 : ℝ)/(p*m+r+1 : ℝ)

lemma quotientHarmonicBlock_lower (p m : ℕ) (hp : 0 < p) :
    1/(m+1 : ℝ) ≤ quotientHarmonicBlock p m := by
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  have hs : (∑ _r ∈ range p, (1 : ℝ)/(p*(m+1) : ℝ)) ≤ quotientHarmonicBlock p m := by
    apply sum_le_sum
    intro r hr
    have hr' : (r : ℝ)+1 ≤ p := by exact_mod_cast (mem_range.mp hr)
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have he : (∑ _r ∈ range p, (1 : ℝ)/(p*(m+1) : ℝ)) = 1/(m+1 : ℝ) := by
    simp only [sum_const,card_range,nsmul_eq_mul]
    field_simp
  rwa [he] at hs

lemma harmonicRawRange_quotient_blocks (p T : ℕ) (hp : 0 < p) (G : ℕ → ℝ) :
    harmonicRawRange (p*T) (fun n => G (n/p)) =
      ∑ m ∈ range T, G m*quotientHarmonicBlock p m := by
  induction T with
  | zero => simp [harmonicRawRange]
  | succ T ih =>
    have he : p*(T+1)=p*T+p := by ring
    unfold harmonicRawRange at *
    rw [he,sum_range_add,ih,sum_range_succ]
    congr 1
    unfold quotientHarmonicBlock
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    dsimp only
    rw [Nat.mul_add_div hp,Nat.div_eq_of_lt (mem_range.mp hr),Nat.add_zero]
    push_cast
    ring

lemma harmonicRawRange_quotient_block_error (p T : ℕ) (hp : 0 < p)
    (G : ℕ → ℝ) (hG : ∀ n, |G n| ≤ 1) :
    |harmonicRawRange (p*T) (fun n => G (n/p))-harmonicRawRange T G| ≤ (p : ℝ)+4 := by
  have he : harmonicRawRange (p*T) (fun n => G (n/p))-harmonicRawRange T G =
      ∑ m ∈ range T, G m*(quotientHarmonicBlock p m-1/(m+1 : ℝ)) := by
    rw [harmonicRawRange_quotient_blocks p T hp]
    unfold harmonicRawRange
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    ring
  have hs : |∑ m ∈ range T, G m*(quotientHarmonicBlock p m-1/(m+1 : ℝ))| ≤
      ∑ m ∈ range T, (quotientHarmonicBlock p m-1/(m+1 : ℝ)) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro m _
    have hm := sub_nonneg.mpr (quotientHarmonicBlock_lower p m hp)
    rw [abs_mul,abs_of_nonneg hm]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hG m) hm
  have he₁ := harmonicRawRange_quotient_blocks p T hp (fun _ => (1 : ℝ))
  simp only [one_mul] at he₁
  have he₂ : (∑ m ∈ range T, (quotientHarmonicBlock p m-1/(m+1 : ℝ))) =
      harmonicRawRange (p*T) (fun _ => 1)-harmonicRawRange T (fun _ => 1) := by
    rw [sum_sub_distrib,← he₁]
    rfl
  rw [he]
  rw [he₂] at hs
  have hb := harmonicRawRange_div_endpoint_error p (p*T) hp (fun _ => 1) (by intro; norm_num)
  rw [Nat.mul_div_right _ hp] at hb
  exact hs.trans ((le_abs_self _).trans hb)

lemma harmonicRawRange_floor_reindex_error (p N : ℕ) (hp : 0 < p)
    (G : ℕ → ℝ) (hG : ∀ n, |G n| ≤ 1) :
    |harmonicRawRange N (fun n => G (n/p))-harmonicRawRange N G| ≤ 3*p+8 := by
  let T := N/p
  have hM : p*T ≤ N := Nat.mul_div_le N p
  have hrem : N-p*T ≤ p := by
    have hh := Nat.div_add_mod N p
    have hr := Nat.mod_lt N hp
    dsimp [T]
    omega
  have h₁ := harmonicRawRange_endpoint_error (p*T) N hM (fun n => G (n/p)) (fun n => hG _)
  have h₁' : |harmonicRawRange N (fun n => G (n/p))-harmonicRawRange (p*T) (fun n => G (n/p))| ≤ p :=
    h₁.trans (by exact_mod_cast hrem)
  have h₂ := harmonicRawRange_quotient_block_error p T hp G hG
  have h₃ := harmonicRawRange_div_endpoint_error p N hp G hG
  have ht₁ := abs_sub_le (harmonicRawRange N (fun n => G (n/p)))
    (harmonicRawRange (p*T) (fun n => G (n/p))) (harmonicRawRange N G)
  have ht₂ := abs_sub_le (harmonicRawRange (p*T) (fun n => G (n/p)))
    (harmonicRawRange T G) (harmonicRawRange N G)
  rw [abs_sub_comm (harmonicRawRange T G)] at ht₂
  change |harmonicRawRange N G-harmonicRawRange T G| ≤ _ at h₃
  linarith

lemma mean_harmonicPrefixLaw_range_identity (N : ℕ) (G : ℕ → ℝ) :
    mean (harmonicPrefixLaw N) (fun i => G (harmonicPrefixLength N i)) =
      harmonicRangeMean (N+1) G+(G (N+1)-G 0)/(harmonic (N+1) : ℝ) := by
  rw [mean_harmonicPrefixLaw,harmonicRangeMean,sum_range_succ']
  simp only [Nat.cast_zero,zero_add,div_one,Nat.cast_add,Nat.cast_one]
  ring

lemma mean_harmonicPrefixLaw_range_error (N : ℕ) (G : ℕ → ℝ) (hG : ∀ n, |G n| ≤ 1) :
    |mean (harmonicPrefixLaw N) (fun i => G (harmonicPrefixLength N i))-
      harmonicRangeMean (N+1) G| ≤ 2/(harmonic (N+1) : ℝ) := by
  rw [mean_harmonicPrefixLaw_range_identity,add_sub_cancel_left,abs_div,
    abs_of_pos (harmonic_real_pos N)]
  exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (by linarith [hG (N+1),hG 0]))
    (harmonic_real_pos N).le

/-- Fixed quotient reindexing of the whole component law has a uniform
vanishing error, even when G is NOT multiplier-stable. -/
theorem harmonicPrefixLaw_floor_reindex_error (p N : ℕ) (hp : 0 < p)
    (G : ℕ → ℝ) (hG : ∀ n, |G n| ≤ 1) :
    |mean (harmonicPrefixLaw N) (fun i => G (harmonicPrefixLength N i/p))-
      mean (harmonicPrefixLaw N) (fun i => G (harmonicPrefixLength N i))| ≤
        (3*p+12 : ℝ)/(harmonic (N+1) : ℝ) := by
  have h₁ := mean_harmonicPrefixLaw_range_error N (fun n => G (n/p)) (fun n => hG _)
  have h₂ := mean_harmonicPrefixLaw_range_error N G hG
  have h₃ : |harmonicRangeMean (N+1) (fun n => G (n/p))-harmonicRangeMean (N+1) G| ≤
      (3*p+8 : ℝ)/(harmonic (N+1) : ℝ) := by
    rw [harmonicRangeMean,harmonicRangeMean,← sub_div,abs_div,abs_of_pos (harmonic_real_pos N)]
    exact div_le_div_of_nonneg_right (harmonicRawRange_floor_reindex_error p (N+1) hp G hG)
      (harmonic_real_pos N).le
  have ht₁ := abs_sub_le (mean (harmonicPrefixLaw N) (fun i => G (harmonicPrefixLength N i/p)))
    (harmonicRangeMean (N+1) (fun n => G (n/p)))
    (mean (harmonicPrefixLaw N) (fun i => G (harmonicPrefixLength N i)))
  have ht₂ := abs_sub_le (harmonicRangeMean (N+1) (fun n => G (n/p)))
    (harmonicRangeMean (N+1) G) (mean (harmonicPrefixLaw N) (fun i => G (harmonicPrefixLength N i)))
  rw [abs_sub_comm (harmonicRangeMean (N+1) G)] at ht₂
  have he : (3*(p : ℝ)+12)/(harmonic (N+1) : ℝ) =
      2/(harmonic (N+1) : ℝ)+(3*p+8 : ℝ)/(harmonic (N+1) : ℝ)+2/(harmonic (N+1) : ℝ) := by ring
  rw [he]
  linarith

#print axioms harmonicRawRange_floor_reindex_error
#print axioms harmonicPrefixLaw_floor_reindex_error
end Erdos371.FiniteInformation
