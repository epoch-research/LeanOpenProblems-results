import Submission.ChangingFieldIterationExplore
import Submission.ChangingFieldGrowthExplore

/-! A logarithmic-cap obstruction for full line recoloring with changing
finite fields. It concerns finite product groups, not all natural sets. -/
namespace Erdos66ChangingFieldLogCap
open Erdos66ChangingFieldIteration Erdos66ChangingFieldLineStep Erdos66ChangingFieldGrowth
  Erdos66OriginRepair Erdos66ParabolaRepair
open scoped Classical
set_option maxHeartbeats 3000000
universe u
variable {G : Type u} {F : ℕ → Type u}
  [AddCommGroup G] [DecidableEq G] [Fintype G]
  [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, DecidableEq (F n)]

lemma space_log_nonneg (n : ℕ) : 0≤Real.log (Fintype.card (Space G F n):ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast Fintype.card_pos (α := Space G F n)

lemma space_log_succ (n : ℕ) :
    Real.log (Fintype.card (Space G F (n+1)):ℝ)=
      Real.log (Fintype.card (Space G F n):ℝ)+2*Real.log (Fintype.card (F (n+1)):ℝ) := by
  rw [space_card_succ]
  push_cast
  rw [Real.log_mul (by exact_mod_cast Fintype.card_ne_zero (α := Space G F n))
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero (α := F (n+1)))),Real.log_pow]
  norm_num

/-- Arbitrary finite initial stages may be discarded. No eventual cap is
possible even with growing fields, injective color changes, and additions. -/
theorem no_eventual_log_cap
    (B : (n : ℕ) → F n → Finset (Space G F n))
    (e : (n : ℕ) → F n ↪ F (n+1)) (τ α : (n : ℕ) → F (n+1))
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, step (e n) (B n) (τ n) (α n) v⊆B (n+1) v)
    (v : F 0) (hB : (B 0 v).Nonempty) (K C : ℝ) (N : ℕ)
    (hcap : ∀ n, N≤n → ∀ z : Space G F n,
      (pairCount (Finset.univ.biUnion (B n)) (Finset.univ.biUnion (B n)) z:ℝ)≤
        K+C*Real.log (Fintype.card (Space G F n):ℝ)) : False := by
  let K' := |K|+1
  let C' := |C|+1
  let T (k : ℕ) := Real.log (Fintype.card (Space G F (N+k)):ℝ)
  let q (k : ℕ) : ℝ := Fintype.card (F (N+k+1))
  have hK' : 0≤K' := by dsimp [K']; positivity
  have hC' : 0≤C' := by dsimp [C']; positivity
  have hT (k : ℕ) : 0≤T k := space_log_nonneg (N+k)
  have hq (k : ℕ) : 0<q k := by dsimp [q]; exact_mod_cast Fintype.card_pos
  have hrec (k : ℕ) : T (k+1)=T k+2*Real.log (q k) := by
    dsimp [T,q]
    rw [show N+(k+1)=(N+k)+1 by omega,space_log_succ]
  have hcap' (n : ℕ) (hn : N≤n) (z : Space G F n) :
      (pairCount (Finset.univ.biUnion (B n)) (Finset.univ.biUnion (B n)) z:ℝ)≤
        K'+C'*Real.log (Fintype.card (Space G F n):ℝ) := by
    apply (hcap n hn z).trans
    apply add_le_add
    · dsimp [K']; linarith only [le_abs_self K]
    · apply mul_le_mul_of_nonneg_right _ (space_log_nonneg n)
      dsimp [C']; linarith only [le_abs_self C]
  have hfield (k : ℕ) : q k≤K'+C'*T (k+1) := by
    obtain ⟨z,hz⟩ := field_peak_each_stage B e τ α hα hstep v hB (N+k)
    have hz' : (Fintype.card (F (N+k+1)):ℝ)≤
        (pairCount (Finset.univ.biUnion (B (N+k+1))) (Finset.univ.biUnion (B (N+k+1))) z:ℝ) := by
      exact_mod_cast hz
    have hh := hz'.trans (hcap' (N+k+1) (by omega) z)
    simpa only [T,q,Nat.add_assoc] using hh
  obtain ⟨w,hw⟩ := nonempty_stages B e τ α hα hstep v hB N
  have hpeak (k : ℕ) : (2:ℝ)^k≤K'+C'*T (2*k) := by
    obtain ⟨w',z,hz⟩ := exponential_peak_from B e τ α hα hstep N w hw k
    have hsub : B (N+2*k) w'⊆Finset.univ.biUnion (B (N+2*k)) := by
      intro a ha
      exact Finset.mem_biUnion.mpr ⟨w',Finset.mem_univ _,ha⟩
    have hz' : (2:ℝ)^k≤
        (pairCount (Finset.univ.biUnion (B (N+2*k))) (Finset.univ.biUnion (B (N+2*k))) z:ℝ) := by
      exact_mod_cast hz.trans (pairCount_mono hsub hsub z)
    exact hz'.trans (hcap' (N+2*k) (by omega) z)
  exact no_logarithmic_budget T q K' C' hK' hC' hT hq hrec hfield hpeak

/-- Violations occur arbitrarily late, without a bound or regularity
assumption on how the finite fields change. -/
theorem arbitrarily_late_log_cap_violation
    (B : (n : ℕ) → F n → Finset (Space G F n))
    (e : (n : ℕ) → F n ↪ F (n+1)) (τ α : (n : ℕ) → F (n+1))
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, step (e n) (B n) (τ n) (α n) v⊆B (n+1) v)
    (v : F 0) (hB : (B 0 v).Nonempty) (K C : ℝ) :
    ∀ N : ℕ, ∃ n, N≤n ∧ ∃ z : Space G F n,
      K+C*Real.log (Fintype.card (Space G F n):ℝ)<
        (pairCount (Finset.univ.biUnion (B n)) (Finset.univ.biUnion (B n)) z:ℝ) := by
  intro N
  by_contra h
  push_neg at h
  exact no_eventual_log_cap B e τ α hα hstep v hB K C N h

end Erdos66ChangingFieldLogCap
