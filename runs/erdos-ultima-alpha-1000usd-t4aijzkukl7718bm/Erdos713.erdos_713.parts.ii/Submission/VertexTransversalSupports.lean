import FormalConjecturesUtil
import Submission.VertexRobustSplit
import Submission.QuadraticSupportTangents

/-! Quadratic supports supply a multi-order weighted vertex-transversal
bound. This does not bound a transversal's cardinality without further
control of its vertex degrees. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical
namespace Erdos713VertexTransversalSupports
open Erdos713VertexRobustSplit Erdos713ExactCloneSaturation
open Erdos713QuadraticSupportTangents
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma support_decrement (f : ℕ → ℕ) {ε : ℝ} {n s : ℕ}
    (hs : s+1 ≤ n) (hrec : QuadSupport f ε n) :
    ε*((s : ℝ)+1)*(2*n-s-1) ≤ (f n : ℝ)-(f (n-s-1) : ℝ) := by
  have hh := hrec (n-s-1)
  have hsub : ((n-s-1 : ℕ) : ℝ) = (n : ℝ)-((s : ℝ)+1) := by
    rw [Nat.sub_sub,Nat.cast_sub hs,Nat.cast_add,Nat.cast_one]
  rw [hsub] at hh
  nlinarith only [hh]

lemma support_transversal [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    {ε : ℝ} (hrec : QuadSupport (fun n => extremalNumber n H) ε (Fintype.card V))
    (S : Finset V) {u v : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (hn : ¬ G.Adj u v) (hblock : ¬ Avoids H G u v S) :
    ε*((S.card : ℝ)+1)*(2*(Fintype.card V : ℝ)-S.card-1) ≤
      ((∑ z ∈ S, Nat.card (G.neighborSet z)) : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ) := by
  have hs := card_le_univ (insert u S)
  rw [card_insert_of_notMem hu] at hs
  exact (support_decrement _ hs hrec).trans
    (transversal_degree_bound H G hf he S hu hv huv hn hblock)

/-- For bounded-size transversals, each deleted vertex earns a full sharp
support increment. The coefficient may approach c*alpha from below. -/
theorem eventually_support_transversals (H : SimpleGraph W) {α c a : ℝ}
    (ha : 0 < a) (hac : a < c*α)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → H.Free G → Nat.card G.edgeSet = extremalNumber n H →
      ∀ ε : ℝ, QuadSupport (fun n => extremalNumber n H) ε n →
      ∀ S : Finset V, S.card ≤ M → ∀ u v, u ∉ S → v ∉ S → u ≠ v → ¬ G.Adj u v →
        ¬ Avoids H G u v S →
        a*((S.card : ℝ)+1)*(n : ℝ)^(α-1) ≤
          ((∑ z ∈ S, Nat.card (G.neighborSet z)) : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ) := by
  let b : ℝ := (a+c*α)/2
  have hab : a < b := by dsimp [b]; linarith
  have hbc : b < c*α := by dsimp [b]; linarith
  have hb : 0 < b := ha.trans hab
  have hlarge : ∀ᶠ n : ℕ in atTop, b*M+(b-a) ≤ (2*(b-a))*(n : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith : 0 < 2*(b-a))).eventually_ge_atTop _
  filter_upwards [eventually_support_lower h hbc,hlarge,eventually_gt_atTop (0 : ℕ)] with n hlo hlarge hn
  intro V hV G hcard hf he ε hrec S hSM u v hu hv huv hnot hblock
  have hSlope := hlo ε hrec
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hε : 0 ≤ ε := by
    have hpow : 0 < (n : ℝ)^(α-1) := Real.rpow_pos_of_pos hnR _
    have hpos : 0 < ε*(2*(n : ℝ)-1) := (mul_pos hb hpow).trans hSlope
    have hfactor : 0 < 2*(n : ℝ)-1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact ((mul_pos_iff_of_pos_right hfactor).mp hpos).le
  have hSMR : (S.card : ℝ) ≤ M := by exact_mod_cast hSM
  have hcomp : a*(2*(n : ℝ)-1) ≤ b*(2*(n : ℝ)-S.card-1) := by
    nlinarith only [hlarge,mul_le_mul_of_nonneg_left hSMR hb.le]
  have hbound : a*(n : ℝ)^(α-1) ≤ ε*(2*(n : ℝ)-S.card-1) := by
    have h1 := mul_le_mul_of_nonneg_left hcomp hε
    have h2 := mul_le_mul_of_nonneg_left hSlope.le ha.le
    apply (mul_le_mul_iff_right₀ hb).mp
    show b*(a*(n : ℝ)^(α-1)) ≤ b*(ε*(2*(n : ℝ)-S.card-1))
    nlinarith only [h1,h2]
  have hs := support_transversal H G hf (hcard ▸ he) (hcard ▸ hrec) S hu hv huv hnot hblock
  rw [hcard] at hs
  have hmul := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (S.card : ℝ)+1 by positivity)
  nlinarith only [hmul,hs]

#print axioms support_transversal
#print axioms eventually_support_transversals
end Erdos713VertexTransversalSupports
