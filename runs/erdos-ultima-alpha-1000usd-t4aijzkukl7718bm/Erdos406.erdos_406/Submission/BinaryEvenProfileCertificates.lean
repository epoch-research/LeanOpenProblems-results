import Submission.BinaryProfileMinplusCertificates

/-! Profile certificates whose lower bound is required only at even exponents.
No supercritical instance is asserted here. -/
namespace Erdos406BinaryEvenProfile
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
open Erdos406BinaryWeighted

lemma even_exponent {k : ℕ} (h : Nat.digits 3 (2^k) ⊆ [0,1]) : Even k := by
  have hpos : 0 < 2^k := by positivity
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hpos] at h
  have hmod : 2^k%3 = 0 ∨ 2^k%3 = 1 := by
    simpa using h (by simp : 2^k%3 ∈ (2^k%3 :: Nat.digits 3 (2^k/3)))
  rcases Nat.even_or_odd k with hk | ⟨j,rfl⟩
  · exact hk
  · simp [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod] at hmod

/-- Odd exponents are already excluded by the last ternary digit. -/
theorem construction_even_potential_criterion (V : ℕ → ℝ) (a B : ℝ)
    (hstep : ∀ n d : ℕ, d < 2 → V (3*n+d) ≤ V n+1)
    (hpower : ∀ k : ℕ, Even k → a*k-B ≤ V (2^k))
    (hcrit : Real.log 2 < a*Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hgap : 0 < a*Real.log 3-Real.log 2 := by linarith
  obtain ⟨M,hM⟩ := exists_nat_gt
    ((V 0+B+1)*Real.log 3/(a*Real.log 3-Real.log 2))
  have hlarge := (div_lt_iff₀ hgap).mp hM
  have hcut (k : ℕ) (hk : M ≤ k) : ¬ Nat.digits 3 (2^k) ⊆ [0,1] := by
    intro hg
    have hp := hpower k (even_exponent hg)
    have hb := hp.trans (construction_good_bound V hstep _ hg)
    have hbl := mul_le_mul_of_nonneg_right hb hlog.le
    have hlen := ternary_power_length_log k
    have hMk : (M : ℝ) ≤ k := by exact_mod_cast hk
    have hkm := mul_le_mul_of_nonneg_right hMk hgap.le
    nlinarith
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨2^M,?_⟩
  rintro n ⟨⟨k,rfl⟩,hg⟩
  by_cases hk : k < M
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact (hcut k (by omega) hg).elim

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

structure PowerBound (D : Automaton σ) (F : σ → Prop) where
  a : ℝ
  B : ℝ
  G : σ → Bool → Prop
  Z : σ → Bool → Prop
  J : σ → Bool → ℝ
  start : ∀ s, s ∈ D.next D.start 1 → G s false
  forward : ∀ s t p, G s p → t ∈ D.next s 0 → G t (!p)
  accepting : ∀ t, F t → Z t false
  backward : ∀ s t p, Z t (!p) → t ∈ D.next s 0 → Z s p
  lower_step : ∀ s t p, G s p → Z t (!p) → t ∈ D.next s 0 →
    a+J t (!p)-J s p ≤ D.weight s 0 t
  lower_end : ∀ s t, s ∈ D.next D.start 1 → G t false → F t → Z s false →
    -B ≤ D.weight D.start 1 s+J t false-J s false

namespace PowerBound
variable {D : Automaton σ} {F : σ → Prop} (P : PowerBound D F)

lemma zero_run_lower (k : ℕ) {s t v}
    (h : Run D s (List.replicate (2*k) 0) t v)
    (hs : P.G s false) (ht : P.Z t false) :
    P.G t false ∧ P.Z s false ∧ P.a*(2*k)+P.J t false-P.J s false ≤ v := by
  induction k generalizing s v with
  | zero =>
    simp only [mul_zero,List.replicate_zero] at h
    cases h
    exact ⟨hs,ht,by simp⟩
  | succ k ih =>
    have he : 2*(k+1) = 2*k+1+1 := by omega
    rw [he,List.replicate_succ,List.replicate_succ] at h
    cases h with
    | @cons _ u _ _ _ w hu hw =>
      cases hw with
      | @cons _ q _ _ _ z hq hz =>
        have hgu := P.forward s u false hs hu
        have hgq := P.forward u q true hgu hq
        obtain ⟨hgt,hzq,hb⟩ := ih hz hgq
        have hzu := P.backward u q true hzq hq
        have hzs := P.backward s u false hzu hu
        have he1 := P.lower_step s u false hs hzu hu
        have he2 := P.lower_step u q true hgu hzq hq
        refine ⟨hgt,hzs,?_⟩
        simp only [Bool.not_false,Bool.not_true] at he1 he2
        push_cast
        linarith

lemma power_run_lower (k : ℕ) {t v}
    (h : Run D D.start (1::List.replicate (2*k) 0) t v) (hF : F t) :
    P.a*(2*k)-P.B ≤ v := by
  cases h with
  | @cons _ s _ _ _ w hs hw =>
    obtain ⟨hgt,hzs,hb⟩ := P.zero_run_lower k hw (P.start s hs) (P.accepting t hF)
    have he := P.lower_end s t hs hgt hF hzs
    linarith

lemma power_lower (h : Total D F) (k : ℕ) :
    P.a*(2*k)-P.B ≤ value D F h (2^(2*k)) := by
  have hword : (Nat.digits 2 (2^(2*k))).reverse = 1::List.replicate (2*k) 0 := by
    have hh := Nat.digits_base_pow_mul (b:=2) (k:=2*k) (m:=1) (by decide) (by decide)
    simpa using congrArg List.reverse hh
  obtain ⟨t,ht,hF⟩ := exists_min_run h (2^(2*k))
  exact P.power_run_lower k (hword ▸ ht) hF

lemma power_lower_of_even (h : Total D F) (k : ℕ) (hk : Even k) :
    P.a*k-P.B ≤ value D F h (2^k) := by
  obtain ⟨m,rfl⟩ := hk
  simpa only [two_mul,Nat.cast_add] using P.power_lower h m
end PowerBound

/-- The conclusion is the exact conjecture, conditional on a strict-rate instance. -/
theorem even_profile_minplus_criterion {τ : Type*}
    (D : Automaton σ) (F : σ → Prop) (h : Total D F)
    (C : Erdos406BinaryProfileMinplus.Construction D F τ)
    (P : PowerBound D F) (hcrit : Real.log 2 < P.a*Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite :=
  construction_even_potential_criterion (value D F h) P.a P.B
    (C.construction_bound h) (P.power_lower_of_even h) hcrit

end Erdos406BinaryEvenProfile
