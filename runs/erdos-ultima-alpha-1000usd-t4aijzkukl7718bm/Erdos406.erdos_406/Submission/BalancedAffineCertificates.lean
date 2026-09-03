import Submission.BalancedAffineTransducer
import Submission.AffineBarrierCertificates

/-! Soundness of balanced-LSD weighted certificates. Every separating or
subcritical witness remains a hypothesis; Erdős 406 is not settled here. -/
namespace Erdos406BalancedCertificate
open Erdos406Balanced Erdos406AffinePotential

lemma weightFrom_append {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ)
    (s : σ) (u v : List ℕ) :
    weightFrom D w s (u++v) = weightFrom D w s u +
      weightFrom D w (D.evalFrom s u) v := by
  induction u generalizing s with
  | nil => simp [weightFrom]
  | cons d u ih =>
    simp only [List.cons_append,weightFrom,DFA.evalFrom_cons,ih]
    ring

def potential {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (n : ℕ) : ℝ :=
  weightFrom D w D.start (digits n)

@[simp] lemma potential_zero {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) :
    potential D w 0 = 0 := by simp [potential,weightFrom]

structure Lower (σ : Type*) where
  D : DFA ℕ σ
  w : σ → ℕ → ℝ
  lam : ℝ
  delta : ℝ
  R : σ → σ → ℤ → Prop
  H : σ → σ → ℤ → ℝ
  relation_start : R D.start D.start 1
  lower_start : H D.start D.start 1 ≤ 0
  relation_step : ∀ s t c d, -2 ≤ c ∧ c ≤ 2 → d < 3 → R s t c →
    R (D.step s d) (D.step t (outDigit d c)) (nextCarry d c)
  lower_step : ∀ s t c d, -2 ≤ c ∧ c ≤ 2 → d < 3 → R s t c →
    H (D.step s d) (D.step t (outDigit d c)) (nextCarry d c) ≤
      H s t c + w t (outDigit d c) - lam*w s d
  finish_empty : delta ≤ H D.start D.start 1 + weightFrom D w D.start (digits 1)
  finish_one : ∀ s t c, -2 ≤ c ∧ c ≤ 2 → R s t c →
    delta ≤ H (D.step s 2) (D.step t (outDigit 2 c)) (nextCarry 2 c) +
      weightFrom D w (D.step t (outDigit 2 c)) (digits (nextCarry 2 c).toNat)

namespace Lower
variable {σ : Type*} (C : Lower σ)

lemma run_lower (s t : σ) (c : ℤ) (u : List ℕ)
    (hc : -2 ≤ c ∧ c ≤ 2) (hu : Valid u) (hr : C.R s t c) :
    C.R (C.D.evalFrom s u) (C.D.evalFrom t (transfer c u).1) (transfer c u).2 ∧
      C.H (C.D.evalFrom s u) (C.D.evalFrom t (transfer c u).1) (transfer c u).2 ≤
        C.H s t c + weightFrom C.D C.w t (transfer c u).1 -
          C.lam*weightFrom C.D C.w s u := by
  induction u generalizing s t c with
  | nil => simpa [transfer,weightFrom] using And.intro hr (le_refl (C.H s t c))
  | cons d u ih =>
    have hd := hu d (by simp)
    have he := C.lower_step s t c d hc hd hr
    have hi := ih (C.D.step s d) (C.D.step t (outDigit d c)) (nextCarry d c)
      (nextCarry_bounds hd hc) (valid_tail hu) (C.relation_step s t c d hc hd hr)
    simp only [transfer,DFA.evalFrom_cons,weightFrom]
    exact ⟨hi.1, by nlinarith [hi.2]⟩

lemma run_finish (s t : σ) (c : ℤ) (u : List ℕ)
    (hc : -2 ≤ c ∧ c ≤ 2) (hu : Valid u) (hr : C.R s t c)
    (hlast : u.getLast? = some 2) :
    C.delta ≤ C.H (C.D.evalFrom s u) (C.D.evalFrom t (transfer c u).1) (transfer c u).2 +
      weightFrom C.D C.w (C.D.evalFrom t (transfer c u).1) (digits (transfer c u).2.toNat) := by
  induction u generalizing s t c with
  | nil => simp at hlast
  | cons d u ih =>
    cases u with
    | nil =>
      have hd : d = 2 := by simpa using hlast
      simpa [hd,transfer,DFA.evalFrom_cons] using C.finish_one s t c hc hr
    | cons e u =>
      have hd := hu d (by simp)
      exact ih (C.D.step s d) (C.D.step t (outDigit d c)) (nextCarry d c)
        (nextCarry_bounds hd hc) (valid_tail hu) (C.relation_step s t c d hc hd hr)
        (by simpa only [List.getLast?_cons_cons] using hlast)

/-- This is the exact numerical inequality encoded by the balanced carry LP. -/
theorem affine_lower (n : ℕ) :
    C.lam * potential C.D C.w n + C.delta ≤ potential C.D C.w (4*n+1) := by
  have hi := C.run_lower C.D.start C.D.start 1 (digits n) (by norm_num)
    (digits_lt_three n) C.relation_start
  have hf : C.delta ≤ C.H (C.D.eval (digits n))
      (C.D.eval (transfer 1 (digits n)).1) (transfer 1 (digits n)).2 +
        weightFrom C.D C.w (C.D.eval (transfer 1 (digits n)).1)
          (digits (transfer 1 (digits n)).2.toNat) := by
    by_cases hn : n = 0
    · simpa [hn,transfer] using C.finish_empty
    · exact C.run_finish C.D.start C.D.start 1 (digits n) (by norm_num)
        (digits_lt_three n) C.relation_start (digits_last n (by omega))
  simp only [potential]
  rw [affine_digits,weightFrom_append]
  have hstart := C.lower_start
  change C.delta ≤ C.H (C.D.evalFrom C.D.start (digits n))
      (C.D.evalFrom C.D.start (transfer 1 (digits n)).1) (transfer 1 (digits n)).2 + _ at hf
  simp only [DFA.eval] at hf
  linarith [hi.2]

end Lower

structure GoodUpper {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) where
  c : ℝ
  B : ℝ
  G : σ → Prop
  J : σ → ℝ
  start : G D.start
  initial : J D.start = 0
  zero_bound : 0 ≤ B
  step : ∀ s d, G s → (d = 1 ∨ d = 2) → G (D.step s d)
  upper_step : ∀ s d, G s → (d = 1 ∨ d = 2) →
    w s d ≤ c + J (D.step s d) - J s
  terminal : ∀ s, G s → J (D.step s 2) ≤ B

namespace GoodUpper
variable {σ : Type*} {D : DFA ℕ σ} {w : σ → ℕ → ℝ} (C : GoodUpper D w)

lemma run_bound (s : σ) (u : List ℕ) (hs : C.G s)
    (hu : ∀ d ∈ u, d = 1 ∨ d = 2) :
    C.G (D.evalFrom s u) ∧ weightFrom D w s u ≤
      C.c * (u.length : ℝ) + C.J (D.evalFrom s u) - C.J s := by
  induction u generalizing s with
  | nil => simpa [weightFrom] using And.intro hs (le_refl (0 : ℝ))
  | cons d u ih =>
    have hd := hu d (by simp)
    have ht : ∀ e ∈ u, e = 1 ∨ e = 2 := fun e he => hu e (by simp [he])
    have hh := ih (D.step s d) (C.step s d hs hd) ht
    have he := C.upper_step s d hs hd
    simp only [DFA.evalFrom_cons,weightFrom,List.length_cons,Nat.cast_add,Nat.cast_one]
    exact ⟨hh.1, by nlinarith [hh.2]⟩

lemma terminal_bound (s : σ) (u : List ℕ) (hs : C.G s)
    (hu : ∀ d ∈ u, d = 1 ∨ d = 2) (hlast : u.getLast? = some 2) :
    C.J (D.evalFrom s u) ≤ C.B := by
  obtain ⟨v,rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hv : ∀ d ∈ v, d = 1 ∨ d = 2 := fun d hd => hu d (by simp [hd])
  have hr := (C.run_bound s v hs hv).1
  simpa only [DFA.evalFrom_append_singleton] using C.terminal _ hr

theorem good_bound (n : ℕ) (hg : Nat.digits 3 n ⊆ [0,1]) :
    potential D w n ≤ C.c * (Nat.digits 3 n).length + C.B := by
  by_cases hn : n = 0
  · simpa [hn] using C.zero_bound
  have hu : ∀ d ∈ digits n, d = 1 ∨ d = 2 := by
    intro d hd
    rw [digits_eq_map_of_good hg,List.mem_map] at hd
    obtain ⟨e,he,rfl⟩ := hd
    have hb := hg he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    omega
  have hr := (C.run_bound D.start (digits n) C.start hu).2
  have ht := C.terminal_bound D.start (digits n) C.start hu (digits_last n (by omega))
  have hlen : (digits n).length = (Nat.digits 3 n).length := by
    rw [digits_eq_map_of_good hg,List.length_map]
  rw [C.initial,hlen] at hr
  change weightFrom D w D.start (digits n) ≤ _
  linarith

end GoodUpper

/-- The searched finite inequalities suffice, IF a strictly separating
rational witness is supplied. This theorem supplies no such witness. -/
theorem barrier_criterion {σ : Type*} (C : Lower σ) (U : GoodUpper C.D C.w)
    (hu : U.c = 0) (hlam : 0 < C.lam)
    (hdelta : C.delta = (1-C.lam)*U.B) (E : ℕ)
    (hseed : U.B < potential C.D C.w (Erdos406AffineCertificate.orbit 4 1 E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply Erdos406AffineBarrier.affine_contracting_barrier_criterion
    (potential C.D C.w) U.B C.lam E hlam ?_ ?_ hseed
  · intro n
    have hh := C.affine_lower n
    rw [hdelta] at hh
    nlinarith
  · intro n hn
    simpa only [hu,zero_mul,zero_add] using U.good_bound n hn

/-- Likewise, a subcritical positive-growth certificate would suffice. -/
theorem growth_criterion {σ : Type*} (C : Lower σ) (U : GoodUpper C.D C.w)
    (hlam : C.lam = 1) (hdelta : C.delta = 1)
    (hc : 0 ≤ U.c) (hcrit : U.c * Real.log 4 < Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply affine_potential_criterion (potential C.D C.w) U.c U.B hc hcrit ?_
    (fun n hn => U.good_bound n hn)
  intro n
  simpa only [hlam,hdelta,one_mul] using C.affine_lower n

#print axioms Lower.affine_lower
#print axioms GoodUpper.good_bound
#print axioms barrier_criterion
#print axioms growth_criterion
end Erdos406BalancedCertificate
