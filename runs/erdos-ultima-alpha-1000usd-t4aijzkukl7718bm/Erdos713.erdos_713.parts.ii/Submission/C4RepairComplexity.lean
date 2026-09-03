import FormalConjecturesUtil
import Submission.GrowingCloneRepairGap

/-! Quantitative cofinal lower bounds on the complexity of local C4 repairs.
These do not supply the rationality implication in the original conjecture. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713C4RepairComplexity
open Erdos713C4 Erdos713GrowingCloneRepairGap Erdos713BatchCloneRepairGap
set_option maxHeartbeats 2000000

/-- A fixed positive square-root increment occurs arbitrarily late, using
only the prime-field construction, not an exact extremal asymptotic. -/
theorem cofinal_sqrt_increment (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (extremalNumber n K22 : ℝ) + (1/4)*Real.sqrt n <
      extremalNumber (n+1) K22 := by
  by_contra h
  push_neg at h
  have hh : ∀ n, N ≤ n → (extremalNumber (n+1) K22 : ℝ) ≤
      extremalNumber n K22 + (1/4)*(n : ℝ)^(1/2 : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using h
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (N+4*extremalNumber N K22+1)
  have hp1 : 1 ≤ p := hprime.one_lt.le
  have hpN : N ≤ 2*p^2 := by nlinarith
  have hlarge : 4*extremalNumber N K22 < p^3 := by
    have hc := Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) p
    omega
  have hu := power_increment_bound (fun n => extremalNumber n K22) N
    (1/4) (1/2) (by norm_num) (by norm_num) hh (2*p^2) hpN
  rw [← Real.sqrt_eq_rpow] at hu
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hu
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),Real.sqrt_sq (Nat.cast_nonneg p)] at hu
  have hs : Real.sqrt (2 : ℝ) ≤ 3/2 := by rw [Real.sqrt_le_iff]; norm_num
  have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p) 3)
  have hl : (p : ℝ)^3 ≤ extremalNumber (2*p^2) K22 := by
    exact_mod_cast extremal_lower_prime p hprime
  have hb : 4*(extremalNumber N K22 : ℝ) < (p : ℝ)^3 := by exact_mod_cast hlarge
  nlinarith

lemma square_of_sqrt_quarter_lt (n b : ℕ) (h : (1/4)*Real.sqrt n < (b : ℝ)) :
    n < 16*b^2 := by
  have hs := Real.sqrt_nonneg (n : ℝ)
  have he := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hh : (n : ℝ) < 16*(b : ℝ)^2 := by nlinarith
  exact_mod_cast hh

lemma budget_le_complexity_square (k t : ℕ) :
    (t+1)*k+2*t.choose 2 ≤ (k+t+1)^2 := by
  have hc : 2*t.choose 2 ≤ t^2 := by
    rw [Nat.choose_two_right]
    have hh := Nat.div_mul_le_self (t*(t-1)) 2
    have hm := Nat.mul_le_mul_left t (Nat.sub_le t 1)
    nlinarith
  nlinarith

/-- The selected exact host works uniformly for every finite patch. To reach
even the next single-vertex extremal number, its root and batch parameters
must satisfy the explicit fourth-power lower bound. -/
theorem exact_hosts_complexity_lower (N : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n ∧ 1 ≤ n ∧ K22.Free G ∧
      Nat.card G.edgeSet = extremalNumber n K22 ∧
      ∀ (t : ℕ) (K : SimpleGraph (Fin n)) (L : SimpleGraph (Fin t))
        (S : Finset (Fin n)) (Q : Fin t → Finset (Fin n)),
        K ≤ G → (∀ w v, v ∈ Q w → ∃ s ∈ S, G.Adj s v) →
        K22.Free (patch K L Q) → extremalNumber (n+1) K22 ≤ Nat.card (patch K L Q).edgeSet →
        n < 16*(S.card+t+1)^4 := by
  obtain ⟨n,hn,hinc⟩ := cofinal_sqrt_increment (max N 1)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hedge : ∃ a b, K22.Adj a b :=
    ⟨.inl 0,.inr 0,by simp [K22,completeBipartiteGraph]⟩
  obtain ⟨G,hG,he⟩ := Erdos713CloneSymm.exists_ordinary_optimal K22 hedge n
  refine ⟨n,G,hnN,hn1,hG.free,he,?_⟩
  intro t K L S Q hle hcover hf hattain
  have hu := Erdos713BatchCloneRepairGap.net_gain_le G K L S Q hle hcover hf
  simp only [Fintype.card_fin,he] at hu
  have hb : extremalNumber (n+1) K22 ≤ extremalNumber n K22 +
      ((t+1)*S.card+2*t.choose 2) := by omega
  have hbr : (extremalNumber (n+1) K22 : ℝ) ≤ extremalNumber n K22 +
      (((t+1)*S.card+2*t.choose 2 : ℕ) : ℝ) := by exact_mod_cast hb
  have hlt : (1/4)*Real.sqrt n < (((t+1)*S.card+2*t.choose 2 : ℕ) : ℝ) := by linarith
  have hs := square_of_sqrt_quarter_lt n _ hlt
  have hc := budget_le_complexity_square S.card t
  have hm := Nat.pow_le_pow_left hc 2
  have heq : ((S.card+t+1)^2)^2 = (S.card+t+1)^4 := by ring
  rw [heq] at hm
  exact lt_of_lt_of_le hs (Nat.mul_le_mul_left 16 hm)

end Erdos713C4RepairComplexity
