import Submission.LocalPolynomialPhaseExtension

/-! Simultaneous flattening of finite-interval polynomial phases of arbitrary
fixed degree. This is a pointwise oscillation theorem, not a density-preserving
partition or a higher Gowers inverse theorem. -/
namespace Erdos3HigherPolynomialFlattening
open Finset Erdos3HigherPhaseDifferences Erdos3HigherPhaseRepresentation
  Erdos3LocalPolynomialPhaseExtension Erdos3SimultaneousPolynomialRecurrence
  Erdos3LocalQuadraticProgressions
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

def monomialFlattenBound (K m t : ℕ) : ℕ :=
  2^(simultaneousPowerConstant K (m*K)*(t+1))

lemma monomial_centered_sum {G : Type*} [AddCommGroup G] (K : ℕ)
    (c : Fin (K+1) → G) (n : ℕ) :
    (∑ j, (n^j.val) • c j)-(∑ j, (0^j.val) • c j) =
      ∑ j : Fin K, (n^(j.val+1)) • c j.succ := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_nsmul,Fin.val_succ,
    zero_pow (Nat.succ_ne_zero _),zero_smul,sum_const_zero,add_zero]
  abel

/-- A uniformly bounded positive stride flattens all the supplied polynomial
phases through the initial point. The finite interval contains every point
used in the proof. -/
theorem simultaneous_polynomial_flattening {I : Type*} [Fintype I]
    (f : I → ℕ → Additive Circle) (K N L t : ℕ) (hL : 0 < L)
    (hf : ∀ i n, n+(K+1) ≤ N → diffIter (K+1) (f i) n = 0)
    (hN : L*monomialFlattenBound K (Fintype.card I) t ≤ N) :
    ∃ d : ℕ, 0 < d ∧ d ≤ monomialFlattenBound K (Fintype.card I) t ∧
      ∀ i, ∀ n ≤ L, ‖phase (f i (n*d))-phase (f i 0)‖ ≤
        (K : ℝ)*(L : ℝ)^K*(1/2 : ℝ)^t := by
  have hrep (i : I) : ∃ c : Fin (K+1) → Additive Circle,
      ∀ n ≤ N, f i n = ∑ j, (n^j.val) • c j :=
    local_polynomial_phase_representation (f i) K N (hf i)
  choose c hc using hrep
  let e : I × Fin K → ℕ := fun ij ↦ ij.2.val+1
  let v : I × Fin K → ℂ := fun ij ↦ phase (c ij.1 ij.2.succ)
  have he (ij : I × Fin K) : 0 < e ij ∧ e ij ≤ K := by dsimp [e]; constructor <;> omega
  have hv (ij : I × Fin K) : ‖v ij‖ = 1 := phase_norm _
  obtain ⟨d,hd,hbound,hrec⟩ := simultaneous_polynomial_recurrence K e he v hv t
  have hbound' : d ≤ monomialFlattenBound K (Fintype.card I) t := by
    simpa only [monomialFlattenBound,Fintype.card_prod,Fintype.card_fin] using hbound
  refine ⟨d,hd,hbound',?_⟩
  intro i n hn
  have hnN : n*d ≤ N := (Nat.mul_le_mul hn hbound').trans hN
  have hsum : f i (n*d)-f i 0 = ∑ j : Fin K, ((n*d)^(j.val+1)) • c i j.succ := by
    rw [hc i (n*d) hnN,hc i 0 (Nat.zero_le _)]
    exact monomial_centered_sum K (c i) (n*d)
  have hterm (j : Fin K) :
      ‖phase (((n*d)^(j.val+1)) • c i j.succ)-1‖ ≤ (L : ℝ)^K*(1/2 : ℝ)^t := by
    have hunit : ‖(v (i,j))^(d^(e (i,j)))‖ = 1 := by rw [norm_pow,hv,one_pow]
    have hosc := unit_power_oscillation ((v (i,j))^(d^(e (i,j)))) hunit (n^(e (i,j)))
    have hrewrite : phase (((n*d)^(j.val+1)) • c i j.succ) =
        ((v (i,j))^(d^(e (i,j))))^(n^(e (i,j))) := by
      rw [phase_nsmul,← pow_mul,mul_pow]
      dsimp [e,v]
      rw [Nat.mul_comm]
    have hnpow : ((n^(e (i,j)) : ℕ) : ℝ) ≤ (L : ℝ)^K := by
      have hh : n^(e (i,j)) ≤ L^K := (Nat.pow_le_pow_left hn _).trans
        (Nat.pow_le_pow_right hL (he (i,j)).2)
      exact_mod_cast hh
    rw [hrewrite]
    exact hosc.trans (mul_le_mul hnpow (hrec (i,j)) (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg L) K))
  rw [phase_sub_norm,hsum]
  calc
    _ ≤ ∑ j : Fin K, ‖phase (((n*d)^(j.val+1)) • c i j.succ)-1‖ := phase_sum_oscillation _ _
    _ ≤ ∑ _j : Fin K, (L : ℝ)^K*(1/2 : ℝ)^t := sum_le_sum (fun j _ ↦ hterm j)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

def higherFlattenAccuracy (K L s : ℕ) : ℕ := s+Nat.clog 2 (K+1)+K*Nat.clog 2 L

def higherFlattenBound (K m L s : ℕ) : ℕ :=
  monomialFlattenBound K m (higherFlattenAccuracy K L s)

lemma higherFlattenAccuracy_error (K L s : ℕ) :
    (K : ℝ)*(L : ℝ)^K*(1/2 : ℝ)^(higherFlattenAccuracy K L s) ≤ (1/2 : ℝ)^s := by
  have hK : (K : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 (K+1)) := by
    exact_mod_cast (Nat.le_succ K).trans (Nat.le_pow_clog (by decide) (K+1))
  have hL : (L : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 L) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) L
  calc
    _ ≤ (2 : ℝ)^(Nat.clog 2 (K+1))*((2 : ℝ)^(Nat.clog 2 L))^K*
        (1/2 : ℝ)^(higherFlattenAccuracy K L s) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hK (pow_le_pow_left₀ (Nat.cast_nonneg L) hL K)
        (pow_nonneg (Nat.cast_nonneg L) K) (pow_nonneg (by norm_num) _)
    _ = _ := by
      unfold higherFlattenAccuracy
      rw [Nat.mul_comm K (Nat.clog 2 L),pow_add,pow_add,pow_mul]
      simp only [div_pow,one_pow]
      field_simp

/-- Dyadic-accuracy form of the finite-interval higher-degree flattening theorem. -/
theorem simultaneous_polynomial_flattening_dyadic {I : Type*} [Fintype I]
    (f : I → ℕ → Additive Circle) (K N L s : ℕ) (hL : 0 < L)
    (hf : ∀ i n, n+(K+1) ≤ N → diffIter (K+1) (f i) n = 0)
    (hN : L*higherFlattenBound K (Fintype.card I) L s ≤ N) :
    ∃ d : ℕ, 0 < d ∧ d ≤ higherFlattenBound K (Fintype.card I) L s ∧
      ∀ i, ∀ n ≤ L, ‖phase (f i (n*d))-phase (f i 0)‖ ≤ (1/2 : ℝ)^s := by
  obtain ⟨d,hd,hbound,hflat⟩ := simultaneous_polynomial_flattening f K N L
    (higherFlattenAccuracy K L s) hL hf hN
  exact ⟨d,hd,hbound,fun i n hn ↦ (hflat i n hn).trans (higherFlattenAccuracy_error K L s)⟩

#print axioms simultaneous_polynomial_flattening
#print axioms simultaneous_polynomial_flattening_dyadic
end Erdos3HigherPolynomialFlattening
