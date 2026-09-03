import Submission.LinearPrefixExtensionExplore

/-! An explicit fixed-tolerance logarithmic transition criterion. The old
prefix is prescribed, but the predictive-mean and concentration-budget
hypotheses are retained. No shrinking-tolerance iteration is asserted. -/
namespace Erdos66LogarithmicPrefixExtension
open AdditiveCombinatorics Erdos66LinearPrefixExtension
open scoped Classical
set_option maxHeartbeats 1500000

lemma logarithmic_transition_budget (N : ℕ) (hN : 3 ≤ N) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico N (2*N)) (b ε : ℝ) (hb : 0 ≤ b)
    (hscale : 16 ≤ ε^2*b) :
    (∑ n∈S, 2*Real.exp (-ε^2*(b*Real.log n)/8))<1 := by
  have hnR : (2:ℝ)<N := by exact_mod_cast (show 2<N by omega)
  have hn0 : (0:ℝ)<N := by linarith
  have hlog0 : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by linarith)
  have hcard : S.card ≤ N := by
    have hh := Finset.card_le_card hS
    simpa only [Nat.card_Ico,show 2*N-N=N by omega] using hh
  have hexp : Real.exp (-(2*Real.log (N:ℝ)))=1/(N:ℝ)^2 := by
    rw [Real.exp_neg]
    rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log hn0]
    simp only [one_div]
  have hterm (n : ℕ) (hn : n∈S) :
      2*Real.exp (-ε^2*(b*Real.log n)/8) ≤ 2/(N:ℝ)^2 := by
    have hnN := (Finset.mem_Ico.mp (hS hn)).1
    have hnN' : (N:ℝ) ≤ n := by exact_mod_cast hnN
    have hlog := Real.log_le_log hn0 hnN'
    have h₁ := mul_le_mul_of_nonneg_left hlog (mul_nonneg (sq_nonneg ε) hb)
    have h₂ := mul_le_mul_of_nonneg_right hscale hlog0
    have he : -ε^2*(b*Real.log n)/8 ≤ -(2*Real.log (N:ℝ)) := by nlinarith only [h₁,h₂]
    have hh := Real.exp_le_exp.mpr he
    rw [hexp] at hh
    convert mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring
  have hs := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  apply hs.trans_lt
  have hc : (S.card:ℝ) ≤ N := by exact_mod_cast hcard
  have hs' : (S.card:ℝ)*(2/(N:ℝ)^2) ≤ (N:ℝ)*(2/(N:ℝ)^2) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  apply hs'.trans_lt
  have he : (N:ℝ)*(2/(N:ℝ)^2)=2/(N:ℝ) := by field_simp
  rw [he]
  exact (div_lt_one hn0).mpr hnR

/-- Every admissible predictive profile has a Boolean first-window extension
under the displayed mean-scale threshold. Both old bits and old counts are
preserved, and only the new mixed mass enters the variance scale. -/
theorem exists_logarithmic_prefix_extension (N L : ℕ) (hN : 3 ≤ N)
    (B : Finset ℕ) (hB : ∀ a∈B, a<N)
    (p : Fin L → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ico N (2*N))
    (c a b ε : ℝ) (hb : 0 ≤ b) (hε : 0<ε) (hε1 : ε ≤ 1)
    (hscale : 16 ≤ ε^2*b)
    (hmean : ∀ n∈S, mixedMean N B n p ≤ b*Real.log n)
    (hbias : ∀ n∈S, |((sumRep (B:Set ℕ) n:ℝ)+mixedMean N B n p)-c*Real.log n| ≤
      a*Real.log n) :
    ∃ F : Finset ℕ, F ⊆ Finset.Ico N (N+L) ∧ Disjoint B F ∧
      (∀ x<N, x∈B∪F ↔ x∈B) ∧
      (∀ n<N, sumRep ((B∪F:Finset ℕ):Set ℕ) n=sumRep (B:Set ℕ) n) ∧
      ∀ n∈S, |(sumRep ((B∪F:Finset ℕ):Set ℕ) n:ℝ)/Real.log n-c|<a+ε*b := by
  obtain ⟨F,hF,hd,hbits,hpast,hgood⟩ := exists_profile_prefix_extension N L B hB p hp S
    (fun n hn ↦ (Finset.mem_Ico.mp (hS hn)).2)
    (fun n ↦ b*Real.log n) (fun n ↦ c*Real.log n) (fun n ↦ a*Real.log n)
    ε hε hε1 hmean hbias (logarithmic_transition_budget N hN S hS b ε hb hscale)
  refine ⟨F,hF,hd,hbits,hpast,?_⟩
  intro n hn
  have hnN := (Finset.mem_Ico.mp (hS hn)).1
  have hlog : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hh := (div_lt_div_iff_of_pos_right hlog).mpr (hgood n hn)
  have he : ((sumRep ((B∪F:Finset ℕ):Set ℕ) n:ℝ)-c*Real.log n)/Real.log n=
      (sumRep ((B∪F:Finset ℕ):Set ℕ) n:ℝ)/Real.log n-c := by field_simp
  have hr : (a*Real.log n+ε*(b*Real.log n))/Real.log n=a+ε*b := by field_simp
  have hh' : |((sumRep ((B∪F:Finset ℕ):Set ℕ) n:ℝ)-c*Real.log n)/Real.log n| <
      (a*Real.log n+ε*(b*Real.log n))/Real.log n := by
    simpa only [abs_div,abs_of_pos hlog] using hh
  rwa [he,hr] at hh'

end Erdos66LogarithmicPrefixExtension
