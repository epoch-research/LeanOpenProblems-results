import Submission.ClippedTwoPeriodExplore
import Submission.DyadicCyclicPaletteExplore
import Submission.LogarithmicPrefixSystemExplore

/-! Unconditional common-source dyadic period comparison. Logarithmic means
are measured in the COMMON period; the shorter-period mean has the required
factor one half. No infinite extension is asserted. -/
namespace Erdos66DyadicTwoPeriodSystem
open Erdos66ClippedTwoPeriod Erdos66ClippedModulus Erdos66DyadicCyclicPalette
  Erdos66OuterCarryProfile Erdos66OuterMixedPrefix Erdos66SaturatingCyclicFamily
  Erdos66LogarithmicPrefixSystem Erdos66CyclicLiftMixed
open scoped Classical
set_option maxHeartbeats 2400000

lemma rebase_self (M : ℕ) [NeZero M] (C : Finset (ZMod M)) : rebase M M C=C := by
  ext a
  simp only [mem_rebase,ZMod.natCast_zmod_val]

lemma prefix_full (M : ℕ) [NeZero M] (C D : Finset (ZMod M)) (z : ZMod M) :
    prefixCount M C D z M=cyclicCount M C D z := by
  simp only [prefixCount,cyclicCount,ZMod.val_lt,true_and]

lemma mean_tuning_of_prefix_tuning (M : ℕ) [NeZero M] (hM : 1<M)
    (C : Finset (ZMod M)) (c τ : ℝ)
    (h : ∀ z, |(prefixCount M C C z M:ℝ)/Real.log M-c| ≤ τ) :
    |actualMean M C C/Real.log M-c| ≤ τ := by
  have hlog := Real.log_pos (show (1:ℝ)<M by exact_mod_cast hM)
  have hflat : ∀ z, |(cyclicCount M C C z:ℝ)-c*Real.log M| ≤ τ*Real.log M := by
    intro z
    have hh := mul_le_mul_of_nonneg_right (h z) hlog.le
    rw [prefix_full] at hh
    have he : ((cyclicCount M C C z:ℝ)/Real.log M-c)*Real.log M=
        (cyclicCount M C C z:ℝ)-c*Real.log M := by field_simp
    rwa [←abs_of_pos hlog,←abs_mul,abs_of_pos hlog,he] at hh
  have hh := div_le_div_of_nonneg_right (actualMean_error M C C _ _ hflat) hlog.le
  have he : (actualMean M C C-c*Real.log M)/Real.log M=actualMean M C C/Real.log M-c := by
    field_simp
  have hh' : |(actualMean M C C-c*Real.log M)/Real.log M| ≤ τ := by
    simpa only [abs_div,abs_of_pos hlog,mul_div_cancel_right₀ _ hlog.ne'] using hh
  rwa [he] at hh'

/-- Both periodic patterns come from one finite source, agree through the
entire short period, and have jointly controlled common-period mixed counts. -/
theorem exists_dyadic_two_period_system (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) (N₀ : ℕ) :
    ∃ k : ℕ, N₀<k ∧ ∃ B : Finset (ZMod (2^k)),
      ∃ C : Finset (ZMod ((2^k)*2)),
        (∀ a : ℕ, a<2^k → ((a : ZMod (2^k))∈B ↔ (a : ZMod ((2^k)*2))∈C)) ∧
        (∀ b d : Bool, ∀ z : ZMod ((2^k)*2),
          |(cyclicCount ((2^k)*2)
            (if b then C else outerLift (2^k) 2 B)
            (if d then C else outerLift (2^k) 2 B) z:ℝ)/Real.log ((2^k)*2:ℕ)-c| ≤ δ) ∧
        (∀ z : ZMod (2^k),
          |(cyclicCount (2^k) B B z:ℝ)/Real.log ((2^k)*2:ℕ)-c/2| ≤ δ/2) := by
  let η := min (1/32) (δ/(100*(c+1)))
  have hη : 0<η := by dsimp [η]; positivity
  have hη32 : η ≤ 1/32 := min_le_left _ _
  have hη1 : η ≤ 1 := by linarith
  have hbudget : 100*η*(c+1) ≤ δ := by
    have hh := (le_div_iff₀ (by positivity : 0<100*(c+1))).mp
      (min_le_right (1/32) (δ/(100*(c+1))))
    change η*(100*(c+1)) ≤ δ at hh
    nlinarith only [hh]
  obtain ⟨j,hj,hrest⟩ :=
    exists_dyadic_logarithmic_palette c η hc hη (N₀+1)
  obtain ⟨k,rfl⟩ : ∃ k, j=k+1 := ⟨j-1,by omega⟩
  have hk : N₀<k := by omega
  let M := 2^k
  have hM : 0<M := by dsimp [M]; positivity
  letI : NeZero M := ⟨hM.ne'⟩
  have hN : 1<M*2 := by omega
  have hlog : 0<Real.log (M*2:ℕ) := Real.log_pos (by exact_mod_cast hN)
  have hrewrite : 2^(k+1)=M*2 := by dsimp [M]; rw [pow_succ]
  simp only [hrewrite] at hrest
  obtain ⟨C,P,hCP,hfull,hnest,htune,hprefix⟩ := hrest
  have hnear := mean_tuning_of_prefix_tuning (M*2) hN C c η (fun z ↦ by
    have hh := htune z (M*2) le_rfl
    have hn0 : (M*2:ℝ)≠0 := by positivity
    simpa only [Nat.cast_mul, Nat.cast_ofNat, div_self hn0,one_mul] using hh)
  have hf : ∀ b d : Bool, ∀ z : ZMod (M*2),
      |(cyclicCount (M*2) (if b then C else outerLift M 2 (rebase M (M*2) C))
        (if d then C else outerLift M 2 (rebase M (M*2) C)) z:ℝ)/Real.log (M*2:ℕ)-c| ≤ δ := by
    intro b d z
    have hh := twoPeriod_error M 2 (M*2) le_rfl C C η hη.le
      (hprefix C hCP C hCP) (hprefix C hCP C hCP) b d z
    simp only [twoPeriod,rebase_self,div_self (by exact_mod_cast (NeZero.ne (M*2)) :
      ((M*2:ℕ):ℝ)≠0),one_mul,Nat.cast_ofNat] at hh
    have hh' : |(cyclicCount (M*2)
        (if b then C else outerLift M 2 (rebase M (M*2) C))
        (if d then C else outerLift M 2 (rebase M (M*2) C)) z:ℝ)-
        actualMean (M*2) C C*1| ≤ (8*η)*actualMean (M*2) C C*1 := by
      simpa only [mul_one, show (4:ℝ)*2=8 by norm_num] using hh
    have hnorm := normalized_weighted_error _ (actualMean (M*2) C C) 1 c η (8*η) 1
      (Real.log (M*2:ℕ)) hlog (by norm_num) le_rfl hη.le (by positivity) hnear hh'
    simp only [mul_one] at hnorm
    have hs : 8*η*(c+η)+η ≤ δ := by
      have h₁ := mul_le_mul_of_nonneg_left hη1 (show 0 ≤ 8*η by positivity)
      have h₂ : 0 ≤ η*c := mul_nonneg hη.le hc.le
      nlinarith only [hbudget,h₁,h₂,hη]
    exact hnorm.trans hs
  refine ⟨k,hk,rebase M (M*2) C,C,?_,hf,?_⟩
  · intro a ha
    have haN : a<M*2 := by change a<M at ha; omega
    simp only [mem_rebase,ZMod.val_natCast_of_lt ha]
  · intro z
    have hh := hf false false (z.val : ZMod (M*2))
    simp only [Bool.false_eq_true,if_false,outer_cyclicCount,map_natCast,
      ZMod.natCast_zmod_val,Nat.cast_mul,Nat.cast_ofNat] at hh
    have hd := div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 2)
    have he : ((2:ℝ)*(cyclicCount M (rebase M (M*2) C) (rebase M (M*2) C) z:ℝ)/
        Real.log (M*2:ℕ)-c)/2=
      (cyclicCount M (rebase M (M*2) C) (rebase M (M*2) C) z:ℝ)/Real.log (M*2:ℕ)-c/2 := by ring
    have hd' : |((2:ℝ)*(cyclicCount M (rebase M (M*2) C) (rebase M (M*2) C) z:ℝ)/
        Real.log (M*2:ℕ)-c)/2| ≤ δ/2 := by
      simpa only [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),Nat.cast_mul,Nat.cast_ofNat] using hd
    rw [he] at hd'
    exact hd'

end Erdos66DyadicTwoPeriodSystem
