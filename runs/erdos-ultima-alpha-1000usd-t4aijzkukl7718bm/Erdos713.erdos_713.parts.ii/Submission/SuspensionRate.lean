import FormalConjecturesUtil
import Submission.SuspensionPower

/-! Extremal upper bounds transferred through bipartite suspension. -/
open Filter SimpleGraph Asymptotics Finset
namespace Erdos713Suspension
set_option maxHeartbeats 2000000

lemma upper_of_regular_power {W : Type*} (H : SimpleGraph W) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hBound : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        H.Free G → G.IsBipartite → 0 < Fintype.card V →
        ∀ d : ℝ, 0 < d → (∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
          (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) →
        d^a ≤ C*(Fintype.card V : ℝ)^b) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^(1 + (b : ℝ)/a)) := by
  classical
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hr : (1 : ℝ) < 1+(b : ℝ)/a := by linarith [div_pos hbR haR]
  by_contra hO
  have hLarge : ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      C * (n : ℝ)^(1+(b : ℝ)/a) < (extremalNumber n H : ℝ) := by
    intro C N
    by_contra hh
    push_neg at hh
    apply hO
    apply IsBigO.of_bound C
    refine eventually_atTop.mpr ⟨N,fun n hn => ?_⟩
    rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact hh n hn
  obtain ⟨R,hR,hRegular⟩ := Erdos713RateRegularization.exists_almost_regular_below H hr hLarge
  obtain ⟨C,hC,hB⟩ := hBound R hR
  let A : ℝ := C+1
  have hA : 0 < A := by dsimp [A]; linarith
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hAC : C < A := by dsimp [A]; linarith
  have hAa : A ≤ A^a := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    rw [hk, pow_succ]
    exact le_mul_of_one_le_left hA.le (one_le_pow₀ hA1)
  obtain ⟨V,_,G,d,_,hn,hfree,hBip,_,hd,hdLow,hdeg⟩ := hRegular A hA 1
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hexp : (1 + (b : ℝ)/a - 1)*(a : ℝ) = b := by field_simp; ring
  have hpow : ((Fintype.card V : ℝ)^(1+(b : ℝ)/a-1))^a = (Fintype.card V : ℝ)^b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le, hexp, Real.rpow_natCast]
  have hlow := pow_le_pow_left₀ (by positivity : 0 ≤ A*(Fintype.card V : ℝ)^(1+(b : ℝ)/a-1)) hdLow a
  rw [mul_pow,hpow] at hlow
  have hhigh := hB V G hfree hBip hn d hd hdeg
  have hh : A^a ≤ C := (mul_le_mul_iff_left₀ (pow_pos hnR b)).mp (hlow.trans hhigh)
  linarith

lemma tree_upper {W : Type*} [Fintype W] (H : SimpleGraph W) (c : H.Coloring Bool)
    (hH : H.IsTree) :
    (fun n : ℕ => (extremalNumber n (graph H c) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((3 : ℝ)/2)) := by
  have hh := upper_of_regular_power (graph H c) 2 1 (by decide) (by decide) (by
    intro R hR
    refine ⟨(4*(Fintype.card W : ℝ)+2)*R^2,by positivity,?_⟩
    intro V _ G hfree hBip hn d hd hdeg
    simpa only [pow_one] using almost_regular_tree H c hH G hBip hfree hn hR hd hdeg)
  norm_num at hh ⊢
  exact hh

lemma cubic_upper {W : Type*} (H : SimpleGraph W) (c : H.Coloring Bool)
    (hH : H.Connected) (C : ℕ) (hUpper : ∀ n, extremalNumber n H ^ 3 ≤ C*n^4) :
    (fun n : ℕ => (extremalNumber n (graph H c) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((8 : ℝ)/5)) := by
  have hh := upper_of_regular_power (graph H c) 5 3 (by decide) (by decide) (by
    intro R hR
    refine ⟨(512*(C : ℝ)+32)*R^7,by positivity,?_⟩
    intro V _ G hfree hBip hn d hd hdeg
    exact almost_regular_cube H c hH C hUpper G hBip hfree hn hR hd hdeg)
  norm_num at hh ⊢
  exact hh


lemma contains_C4 {W : Type*} (H : SimpleGraph W) (c : H.Coloring Bool)
    {a b : W} (hab : H.Adj a b) : Erdos713C4.K22 ⊑ graph H c := by
  classical
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨{Sum.inl (c a),Sum.inr a},{Sum.inl (c b),Sum.inr b},by simp,by simp,?_⟩
  intro x hx y hy
  simp only [mem_coe,mem_insert,mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact c.valid hab
  · exact c.valid hab
  · exact c.valid hab
  · exact hab

lemma tree_rate {W : Type*} [Fintype W] (H : SimpleGraph W) (c : H.Coloring Bool)
    (hH : H.IsTree) {a b : W} (hab : H.Adj a b) :
    Erdos713Rate.HasRate (graph H c) ((3 : ℝ)/2) :=
  Erdos713Rate.rate_of_C4_upper (contains_C4 H c hab) (tree_upper H c hH)

lemma tree_sandwich_rate {W V : Type*} [Fintype W] (H : SimpleGraph W) (c : H.Coloring Bool)
    (hH : H.IsTree) (G : SimpleGraph V) (hlo : Erdos713C4.K22 ⊑ G) (hhi : G ⊑ graph H c) :
    Erdos713Rate.HasRate G ((3 : ℝ)/2) :=
  Erdos713Rate.rate_of_C4_upper hlo ((Erdos713Rate.extremal_mono_bigO hhi).trans (tree_upper H c hH))

end Erdos713Suspension
