import FormalConjecturesUtil
import Submission.ThetaBalancedSplit

/-! Elementary parameter bounds for the transversal-completion diagnostic. -/
namespace Erdos713ThetaTransversalParameters
open Erdos713ThetaBalancedSplit
set_option maxHeartbeats 2000000

lemma parameter_bounds {m k r q : ℕ} (hk : 0 < k) (hr : 1 ≤ r)
    (hm : 100*k^2 < m) (hcube : m*r ≤ k^3) (hqlo : 2*k < q) (hqhi : q ≤ 4*k) :
    let d := m*r/k+1
    let T := d/q+1
    0 < T ∧ T ≤ q ∧ q^2 ≤ m ∧ d+q ≤ 2*(T*q) ∧ T*q^2 ≤ 8*m*r := by
  dsimp only
  let d := m*r/k+1
  let T := d/q+1
  change 0 < T ∧ T ≤ q ∧ q^2 ≤ m ∧ d+q ≤ 2*(T*q) ∧ T*q^2 ≤ 8*m*r
  have hq : 0 < q := by omega
  have hd := balanced_cap (e := m*r) hk
  have hT := balanced_cap (e := d) hq
  change 0 < d ∧ m*r ≤ d*k ∧ d*k ≤ m*r+k at hd
  change 0 < T ∧ d ≤ T*q ∧ T*q ≤ d+q at hT
  have hmr : m ≤ m*r := by nlinarith
  have hksq : k^2 ≤ k^3 := by nlinarith
  have hqlo2 := Nat.pow_le_pow_left hqlo.le 2
  have hqhi2 := Nat.pow_le_pow_left hqhi 2
  have hqm : q^2 ≤ m := by nlinarith
  have hdsmall : d ≤ k^2+1 := by
    suffices hh : d*k ≤ (k^2+1)*k from Nat.le_of_mul_le_mul_right hh hk
    nlinarith [hd.2.2]
  have hTsmall : T ≤ q := by
    apply Nat.le_of_mul_le_mul_right (b := q) ?_ hq
    have hq2 : 2 ≤ q := by omega
    have h1 : 1 ≤ k^2 := Nat.one_le_pow _ _ hk
    have hqq : 2*q ≤ q^2 := by nlinarith
    nlinarith [hT.2.2]
  have hD : d+q ≤ 2*(T*q) := by
    have hqT : q ≤ T*q := by nlinarith [hT.1]
    omega
  have hmul : T*q*k ≤ m*r+k+q*k := by
    have hh := Nat.mul_le_mul_right k hT.2.2
    nlinarith [hd.2.2]
  have hpower : T*q^2 ≤ 8*m*r := by
    suffices hh : (T*q^2)*k ≤ (8*m*r)*k from Nat.le_of_mul_le_mul_right hh hk
    have h1 := Nat.mul_le_mul_right q hmul
    have h2 := Nat.mul_le_mul_left (m*r+k+q*k) hqhi
    have h3 := Nat.mul_le_mul_left (4*k^2) hqhi
    have h4 := Nat.mul_le_mul_right k (hm.le.trans hmr)
    nlinarith
  exact ⟨hT.1,hTsmall,hqm,hD,hpower⟩

lemma real_gap {m q T s N : ℕ} (hm : 0 < m) (hT : 0 < T)
    (hqm : q^2 ≤ m) (hp : T*q^2 ≤ 8*m*s^2) (hs : s = 100*(N+1)) :
    (N : ℝ)*((T*m+q^2 : ℕ)+(T*q : ℕ)*Real.sqrt (T*m+q^2)) < (T*m*s^2 : ℕ) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hqmR : (q : ℝ)^2 ≤ m := by exact_mod_cast hqm
  have hpR : (T : ℝ)*q^2 ≤ 8*m*s^2 := by exact_mod_cast hp
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hM : (T : ℝ)*m+q^2 ≤ 2*(T*m) := by nlinarith
  have hk2 : ((T : ℝ)*q)^2 ≤ 8*(T*m)*s^2 := by nlinarith [mul_le_mul_of_nonneg_left hpR hTr.le]
  have hroot : ((T : ℝ)*q)*Real.sqrt ((T : ℝ)*m+q^2) ≤ 4*(T*m)*s := by
    have hprod := mul_le_mul hk2 hM (by positivity : 0 ≤ (T : ℝ)*m+q^2) (by positivity)
    have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ (T : ℝ)*m+q^2)
    have hsq : ((T : ℝ)*q*Real.sqrt ((T : ℝ)*m+q^2))^2 ≤ (4*(T*m)*s)^2 := by
      calc
        _ = ((T : ℝ)*q)^2*((T : ℝ)*m+q^2) := by rw [mul_pow,hsqrt]
        _ ≤ 8*(T*m)*s^2*(2*(T*m)) := hprod
        _ = _ := by ring
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have hsR : (s : ℝ) = 100*((N : ℝ)+1) := by exact_mod_cast hs
  have hsGap : (N : ℝ)*(2+4*s) < s^2 := by nlinarith [sq_nonneg (N : ℝ)]
  have hmul := mul_lt_mul_of_pos_right hsGap (mul_pos hTr hmr)
  have hup := mul_le_mul_of_nonneg_left (add_le_add hM hroot) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  push_cast
  nlinarith

#print axioms parameter_bounds
#print axioms real_gap
end Erdos713ThetaTransversalParameters
