import FormalConjecturesUtil
import Submission.BatchCloneRepairGap

/-! Polynomially growing root covers and vertex batches still fail to track
C4 extremal increments below an explicit scale. No termwise differentiation
of an extremal asymptotic is used, and no rationality theorem is asserted. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical
namespace Erdos713GrowingCloneRepairGap
open Erdos713C4 Erdos713BatchCloneRepairGap
set_option maxHeartbeats 2000000

lemma power_increment_bound (f : ℕ → ℕ) (N : ℕ) (A β : ℝ) (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (h : ∀ n, N ≤ n → (f (n+1) : ℝ) ≤ f n + A*(n : ℝ)^β) :
    ∀ n, N ≤ n → (f n : ℝ) ≤ f N + A*(n : ℝ)*(n : ℝ)^β := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact le_add_of_nonneg_right (by positivity)
  | succ n hn ih =>
    have hi := h n hn
    have hm : (n : ℝ)^β ≤ (n+1 : ℕ)^β :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ n) hβ
    have hp := mul_le_mul_of_nonneg_left hm (show 0 ≤ A*((n+1 : ℕ) : ℝ) by positivity)
    simp only [Nat.cast_add,Nat.cast_one] at hp
    calc
      (f (n+1) : ℝ) ≤ f N + A*(n : ℝ)*(n : ℝ)^β + A*(n : ℝ)^β := by linarith
      _ = f N + A*(n+1)*(n : ℝ)^β := by ring
      _ ≤ f N + A*((n+1 : ℕ) : ℝ)*((n+1 : ℕ) : ℝ)^β := by
        simp only [Nat.cast_add,Nat.cast_one]
        linarith only [hp]

lemma power_increments_bigO (f : ℕ → ℕ) (N : ℕ) (A β : ℝ) (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (h : ∀ n, N ≤ n → (f (n+1) : ℝ) ≤ f n + A*(n : ℝ)^β) :
    (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^(β+1)) := by
  apply IsBigO.of_bound (f N + A : ℝ)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right N 1).trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hp : 1 ≤ (n : ℝ)^(β+1) := Real.one_le_rpow hn1 (by linarith)
  have hb := power_increment_bound f N A β hA hβ h n hnN
  have he : A*(n : ℝ)*(n : ℝ)^β = A*(n : ℝ)^(β+1) := by
    rw [Real.rpow_add hn0,Real.rpow_one]
    ring
  rw [he] at hb
  rw [Real.norm_natCast,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hh := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (f N) : (0 : ℝ) ≤ f N)
  nlinarith

/-- Unboundedness at every sub-square-root power scale, from the prime-field
lower bound alone. This is not an asymptotic formula for each increment. -/
theorem c4_cofinal_power_increment (β A : ℝ) (hβ : 0 ≤ β) (hhalf : β < 1/2)
    (hA : 0 ≤ A) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (extremalNumber n K22 : ℝ) + A*(n : ℝ)^β <
      extremalNumber (n+1) K22 := by
  by_contra h
  push_neg at h
  have hb := power_increments_bigO (fun n => extremalNumber n K22) N A β hA hβ h
  have he := lower_exponent_of_prime_bound hb extremal_lower_prime
  linarith

/-- A uniform real-power upper bound for the finite patch cost. -/
lemma patch_cost_bound (n k t : ℕ) (hn : 1 ≤ n) (A B κ τ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hk : (k : ℝ) ≤ A*(n : ℝ)^κ) (ht : (t : ℝ) ≤ B*(n : ℝ)^τ) :
    (((t+1)*k+2*t.choose 2 : ℕ) : ℝ) ≤
      (A*B+A+2*B^2)*(n : ℝ)^(max (κ+τ) (2*τ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  let β := max (κ+τ) (2*τ)
  have hkβ : (n : ℝ)^κ ≤ (n : ℝ)^β :=
    Real.rpow_le_rpow_of_exponent_le hn1 (le_trans (by linarith : κ ≤ κ+τ) (le_max_left _ _))
  have hktβ : (n : ℝ)^(κ+τ) ≤ (n : ℝ)^β :=
    Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _)
  have httβ : (n : ℝ)^(2*τ) ≤ (n : ℝ)^β :=
    Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)
  have hkt : (t : ℝ)*k ≤ A*B*(n : ℝ)^β := by
    calc
      (t : ℝ)*k ≤ (B*(n : ℝ)^τ)*(A*(n : ℝ)^κ) :=
        mul_le_mul ht hk (Nat.cast_nonneg _) (by positivity)
      _ = A*B*(n : ℝ)^(κ+τ) := by rw [Real.rpow_add hn0]; ring
      _ ≤ A*B*(n : ℝ)^β := mul_le_mul_of_nonneg_left hktβ (mul_nonneg hA hB)
  have hkk : (k : ℝ) ≤ A*(n : ℝ)^β :=
    hk.trans (mul_le_mul_of_nonneg_left hkβ hA)
  have htt : (t : ℝ)^2 ≤ B^2*(n : ℝ)^β := by
    calc
      (t : ℝ)^2 ≤ (B*(n : ℝ)^τ)^2 := by nlinarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
      _ = B^2*(n : ℝ)^(2*τ) := by
        rw [show 2*τ=τ+τ by ring,Real.rpow_add hn0]
        ring
      _ ≤ B^2*(n : ℝ)^β := mul_le_mul_of_nonneg_left httβ (sq_nonneg _)
  have hc : (t.choose 2 : ℝ) ≤ (t : ℝ)^2 := by exact_mod_cast Nat.choose_le_pow t 2
  push_cast
  dsimp [β] at hkt hkk htt
  nlinarith

/-- For root exponent κ and batch exponent τ with κ+τ<1/2 and 2τ<1/2,
one exact extremizer defeats ALL allowed growing patches at its order.
The deficit can be any prescribed multiple of n^max(κ+τ,2τ). -/
theorem exact_hosts_growing_gap (κ τ A B R : ℝ)
    (hκ : 0 ≤ κ) (hτ : 0 ≤ τ) (hκτ : κ+τ < 1/2) (hττ : 2*τ < 1/2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (N : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n ∧ 1 ≤ n ∧ K22.Free G ∧
      Nat.card G.edgeSet = extremalNumber n K22 ∧
      ∀ (t : ℕ) (K : SimpleGraph (Fin n)) (L : SimpleGraph (Fin t))
        (S : Finset (Fin n)) (Q : Fin t → Finset (Fin n)),
        K ≤ G → (S.card : ℝ) ≤ A*(n : ℝ)^κ → (t : ℝ) ≤ B*(n : ℝ)^τ →
        (∀ w v, v ∈ Q w → ∃ s ∈ S, G.Adj s v) → K22.Free (patch K L Q) →
        (Nat.card (patch K L Q).edgeSet : ℝ) + R*(n : ℝ)^(max (κ+τ) (2*τ)) <
          extremalNumber (n+1) K22 := by
  let β := max (κ+τ) (2*τ)
  have hβ : 0 ≤ β := (add_nonneg hκ hτ).trans (le_max_left _ _)
  have hhalf : β < 1/2 := max_lt hκτ hττ
  have hcoeff : 0 ≤ A*B+A+2*B^2+R := by positivity
  obtain ⟨n,hn,hinc⟩ := c4_cofinal_power_increment β (A*B+A+2*B^2+R) hβ hhalf hcoeff (max N 1)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hedge : ∃ a b, K22.Adj a b :=
    ⟨.inl 0,.inr 0,by simp [K22,completeBipartiteGraph]⟩
  obtain ⟨G,hG,he⟩ := Erdos713CloneSymm.exists_ordinary_optimal K22 hedge n
  refine ⟨n,G,hnN,hn1,hG.free,he,?_⟩
  intro t K L S Q hle hk ht hcover hf
  have hb := Erdos713BatchCloneRepairGap.net_gain_le G K L S Q hle hcover hf
  simp only [Fintype.card_fin,he] at hb
  have hb' : (Nat.card (patch K L Q).edgeSet : ℝ) ≤ extremalNumber n K22 +
      (((t+1)*S.card+2*t.choose 2 : ℕ) : ℝ) := by exact_mod_cast (by simpa only [Nat.add_assoc] using hb)
  have hc := patch_cost_bound n S.card t hn1 A B κ τ hA hB hτ hk ht
  change (extremalNumber n K22 : ℝ) + (A*B+A+2*B^2+R)*(n : ℝ)^(max (κ+τ) (2*τ)) < _ at hinc
  nlinarith

end Erdos713GrowingCloneRepairGap
