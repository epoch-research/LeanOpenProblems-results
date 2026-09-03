import Submission.CrootSisaskL2
import Submission.FiniteSamplingMoments

/-! Even-moment Croot--Sisask almost-periodicity with polynomial sampling cost.
This is an auxiliary quantitative result, not a proof of Erdős 3. -/
namespace Erdos3CrootSisaskLp

open Finset Erdos3CrootSisaskL2 Erdos3FiniteSamplingMoments
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

def evenMoment (f : G → ℝ) (m : ℕ) : ℝ := ∑ x, (f x)^(2*m)

omit [AddCommGroup G] in
lemma evenMoment_nonneg (f : G → ℝ) (m : ℕ) : 0 ≤ evenMoment f m :=
  sum_nonneg (fun _ _ ↦ (even_two_mul m).pow_nonneg _)

lemma sample_energy (A : Finset G) (hA : A.Nonempty) (f : G → ℝ) (m : ℕ) :
    (∑ x : G, 𝔼 a : A, (f (x+(a : G)))^(2*m)) = evenMoment f m := by
  letI : Nonempty A := hA.to_subtype
  rw [← expect_sum_comm]
  have hs (a : A) : (∑ x : G, (f (x+(a : G)))^(2*m)) = evenMoment f m :=
    sum_translate (fun x ↦ (f x)^(2*m)) a
  simp_rw [hs]
  exact Fintype.expect_const _

/-- The raw even-moment form, retaining the constants from the sampling estimate. -/
theorem exists_many_even_moment_periods (A S : Finset G) (hA : A.Nonempty) (hS : S.Nonempty)
    (f : G → ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ∃ T : Finset G, T ⊆ S ∧
      A.card^n*S.card ≤ 2*(A+S).card^n*T.card ∧
      ∀ s ∈ T, ∀ t ∈ T,
        evenMoment (fun x ↦ smooth A f (x+s) - smooth A f (x+t)) m ≤
          (2^(2*m+1)*((2*m : ℝ)*(2*m : ℝ)^(2*m)/(n : ℝ)^m))*evenMoment f m := by
  classical
  letI : Nonempty A := hA.to_subtype
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨L, hLc, hgood⟩ := many_good_moment_samples (I := Fin n)
    (fun (a : A) (x : G) ↦ f (x+(a : G))) hm
  have hLc' : A.card^n ≤ 2*L.card := by simpa using hLc
  have hLn : L.Nonempty := by
    have hh : 0 < A.card^n := pow_pos (card_pos.mpr hA) _
    exact card_pos.mp (by omega)
  let C : ℝ := (2*m : ℝ)*(2*m : ℝ)^(2*m)/(n : ℝ)^m
  have hgood' (v : Fin n → A) (hv : v ∈ L) :
      evenMoment (fun x ↦ empirical (fun i ↦ (v i : G)) f x - smooth A f x) m ≤
        2*C*evenMoment f m := by
    simpa only [C, evenMoment, empirical, smooth, Fintype.card_fin, sample_energy A hA f m] using hgood v hv
  obtain ⟨u,T,hTS,hTc,hrep⟩ := common_translate_fiber A S L hS hLn
  refine ⟨T, hTS, ?_, ?_⟩
  · calc
      A.card^n*S.card ≤ (2*L.card)*S.card := Nat.mul_le_mul_right _ hLc'
      _ = 2*(L.card*S.card) := by ring
      _ ≤ 2*((A+S).card^n*T.card) := Nat.mul_le_mul_left 2 (by simpa using hTc)
      _ = _ := by ring
  · intro s hs t ht
    obtain ⟨v,hv,hvs⟩ := hrep s hs
    obtain ⟨w,hw,hwt⟩ := hrep t ht
    have he (z : Fin n → A) (r : G) (hz : ∀ i, (z i : G)+r = u i) (x : G) :
        empirical (fun i ↦ (z i : G)) f (x+r) = empirical u f x := by
      apply expect_congr rfl
      intro i _
      congr 1
      rw [← hz i]
      abel
    have herr (z : Fin n → A) (r : G) (hz : ∀ i, (z i : G)+r = u i) :
        evenMoment (fun x ↦ empirical u f x - smooth A f (x+r)) m =
          evenMoment (fun x ↦ empirical (fun i ↦ (z i : G)) f x - smooth A f x) m := by
      calc
        _ = ∑ x : G, (empirical (fun i ↦ (z i : G)) f (x+r) - smooth A f (x+r))^(2*m) := by
          simp_rw [he z r hz]
          rfl
        _ = _ := sum_translate (fun x ↦
          (empirical (fun i ↦ (z i : G)) f x - smooth A f x)^(2*m)) r
    have hes : evenMoment (fun x ↦ empirical u f x - smooth A f (x+s)) m ≤
        2*C*evenMoment f m := by rw [herr v s hvs]; exact hgood' v hv
    have het : evenMoment (fun x ↦ empirical u f x - smooth A f (x+t)) m ≤
        2*C*evenMoment f m := by rw [herr w t hwt]; exact hgood' w hw
    calc
      _ ≤ ∑ x : G, (2^(2*m)/2)*((empirical u f x - smooth A f (x+s))^(2*m) +
          (empirical u f x - smooth A f (x+t))^(2*m)) := by
        apply sum_le_sum
        intro x _
        have hh := even_pow_sub_le (even_two_mul m)
          (empirical u f x - smooth A f (x+t)) (empirical u f x - smooth A f (x+s))
        convert hh using 1 <;> ring
      _ = (2^(2*m)/2)*(evenMoment (fun x ↦ empirical u f x - smooth A f (x+s)) m +
          evenMoment (fun x ↦ empirical u f x - smooth A f (x+t)) m) := by
        unfold evenMoment
        rw [← mul_sum, sum_add_distrib]
      _ ≤ (2^(2*m)/2)*(2*C*evenMoment f m + 2*C*evenMoment f m) := by gcongr
      _ = _ := by dsimp [C]; rw [pow_succ]; ring

lemma moment_coefficient_bound {m : ℕ} (hm : 0 < m) :
    2^(2*m+1)*(2*m)*(2*m)^(2*m) ≤ (256*m^4)^m := by
  calc
    _ = (4*m)^(2*m+1) := by
      rw [show 4*m = 2*(2*m) by ring, mul_pow 2 (2*m) (2*m+1), pow_succ (2*m) (2*m)]
      ring
    _ ≤ (4*m)^(4*m) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = ((4*m)^4)^m := by rw [← pow_mul]
    _ = _ := by congr 1; ring

/-- Polynomial dependence on the moment: n samples give error factor (256*m⁴/n)^m. -/
theorem exists_many_Lp_almost_periods (A S : Finset G) (hA : A.Nonempty) (hS : S.Nonempty)
    (f : G → ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ∃ T : Finset G, T ⊆ S ∧
      A.card^n*S.card ≤ 2*(A+S).card^n*T.card ∧
      ∀ s ∈ T, ∀ t ∈ T,
        evenMoment (fun x ↦ smooth A f (x+s) - smooth A f (x+t)) m ≤
          (256*(m : ℝ)^4/(n : ℝ))^m*evenMoment f m := by
  obtain ⟨T,hT,hcard,hperiod⟩ := exists_many_even_moment_periods A S hA hS f hn hm
  refine ⟨T,hT,hcard,fun s hs t ht ↦ (hperiod s hs t ht).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (evenMoment_nonneg f m)
  rw [div_pow]
  have hh : (2 : ℝ)^(2*m+1)*(2*m)*(2*m)^(2*m) ≤ (256*(m : ℝ)^4)^m := by
    exact_mod_cast moment_coefficient_bound hm
  calc
    _ = ((2 : ℝ)^(2*m+1)*(2*m)*(2*m)^(2*m))/(n : ℝ)^m := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hh (by positivity)

#print axioms exists_many_Lp_almost_periods
end Erdos3CrootSisaskLp
