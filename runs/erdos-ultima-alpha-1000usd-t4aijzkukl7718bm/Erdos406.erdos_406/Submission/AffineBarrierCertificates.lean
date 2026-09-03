import Submission.AffinePotentialCertificates

/-! Soundness of nondecreasing weighted barriers. These criteria do not
assert that any separating barrier exists, and do not settle Erdős 406. -/

namespace Erdos406AffineBarrier
open Erdos406AffineCertificate Erdos406GroupedCertificate Erdos406AffinePotential

/-- Unlike a positive-growth rate criterion, this requires only monotonicity
and one strict seed separation from a uniform bound on good words. -/
theorem affine_barrier_criterion (V : ℕ → ℝ) (B : ℝ) (E : ℕ)
    (hmono : ∀ n, V n ≤ V (4*n+1))
    (hgood : ∀ n, Good n → V n ≤ B)
    (hseed : B < V (orbit 4 1 E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have horbit : ∀ j : ℕ, V (orbit 4 1 E) ≤ V (orbit 4 1 (E+j)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      simpa only [Nat.add_succ, orbit_succ] using
        ih.trans (hmono (orbit 4 1 (E+j)))
  have hcut : ∀ t : ℕ, E ≤ t → ¬ Good (orbit 4 1 t) := by
    intro t ht hg
    have hh := horbit (t-E)
    rw [Nat.add_sub_of_le ht] at hh
    exact (not_lt_of_ge (hh.trans (hgood _ hg))) hseed
  apply Erdos406SingleAffine.single_affine_criterion
  refine ((Finset.range E).finite_toSet.image (orbit 4 1)).subset ?_
  rintro n ⟨⟨t,rfl⟩,hg⟩
  refine ⟨t, ?_, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra ht
  exact hcut t (by omega) hg

structure MonotoneCore (σ : Type*) where
  D : DFA ℕ σ
  w : σ → ℕ → ℝ
  R : σ → σ → ℕ → Prop
  P : σ → σ → ℕ → ℝ
  relation_start : ∀ c, c < 4 → R D.start (evalNat 3 D c) c
  relation_step : ∀ s t c d e c', c < 4 → d < 3 → e < 3 → c' < 4 →
    4*d+c' = 3*c+e → R s t c → R (D.step s d) (D.step t e) c'
  lower_start : ∀ c, c < 4 → P D.start (evalNat 3 D c) c ≤ weightNat D w c
  lower_step : ∀ s t c d e c', c < 4 → d < 3 → e < 3 → c' < 4 →
    4*d+c' = 3*c+e → R s t c →
    P (D.step s d) (D.step t e) c' ≤ P s t c + w t e - w s d
  lower_finish : ∀ s t, R s t 1 → 0 ≤ P s t 1

namespace MonotoneCore
variable {σ : Type*} (C : MonotoneCore σ)

lemma relation_potential (n c : ℕ) (hc : c < 4) :
    C.R (evalNat 3 C.D n) (evalNat 3 C.D (4*n+c)) c ∧
    C.P (evalNat 3 C.D n) (evalNat 3 C.D (4*n+c)) c ≤
      weightNat C.D C.w (4*n+c) - weightNat C.D C.w n := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [mul_zero, zero_add, evalNat_zero, weightNat_zero, sub_zero] using
        And.intro (C.relation_start c hc) (C.lower_start c hc)
    · have hnpos := Nat.pos_of_ne_zero hn
      let d := n % 3
      let cp := (4*d+c)/3
      let e := (4*d+c)%3
      have hd : d < 3 := Nat.mod_lt _ (by decide)
      have he : e < 3 := Nat.mod_lt _ (by decide)
      have hcp : cp < 4 := by dsimp [cp]; omega
      have hi := ih (n/3) (Nat.div_lt_self hnpos (by decide)) cp hcp
      have hid : 4*d+c = 3*cp+e := by dsimp [cp,e]; omega
      have hr := C.relation_step _ _ cp d e c hcp hd he hc hid hi.1
      have hp := C.lower_step _ _ cp d e c hcp hd he hc hid hi.1
      have hout : 0 < 4*n+c := by omega
      obtain ⟨hq,hm⟩ := affine_div_mod 3 4 n c (by decide)
      rw [evalNat_pos 3 C.D (by decide) hnpos, evalNat_pos 3 C.D (by decide) hout, hq, hm,
        weightNat_pos C.D C.w hnpos, weightNat_pos C.D C.w hout, hq, hm]
      exact ⟨hr, by dsimp only [d,cp,e] at hi hp ⊢; linarith⟩

lemma nondecreasing (n : ℕ) : weightNat C.D C.w n ≤ weightNat C.D C.w (4*n+1) := by
  have hh := C.relation_potential n 1 (by decide)
  have hf := C.lower_finish _ _ hh.1
  linarith

end MonotoneCore

/-- Soundness of a finite signed-weight certificate. All certificate data and
strict seed separation are hypotheses; no witness has been supplied. -/
theorem weighted_barrier_criterion {σ : Type*} (C : MonotoneCore σ)
    (S : GoodBound C.D C.w) (hc : S.c = 0) (E : ℕ)
    (hseed : S.B < weightNat C.D C.w (orbit 4 1 E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply affine_barrier_criterion (weightNat C.D C.w) S.B E C.nondecreasing
    (fun n hn => ?_) hseed
  have hh := S.good_bound n hn
  simpa only [hc, zero_mul, zero_add] using hh

/-- Strict threshold invariance suffices; the potential need not be globally
nondecreasing. This is still a conditional criterion. -/
theorem affine_threshold_criterion (V : ℕ → ℝ) (B : ℝ) (E : ℕ)
    (hpres : ∀ n, B < V n → B < V (4*n+1))
    (hgood : ∀ n, Good n → V n ≤ B)
    (hseed : B < V (orbit 4 1 E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have horbit : ∀ j : ℕ, B < V (orbit 4 1 (E+j)) := by
    intro j
    induction j with
    | zero => simpa using hseed
    | succ j ih =>
      simpa only [Nat.add_succ, orbit_succ] using hpres (orbit 4 1 (E+j)) ih
  have hcut : ∀ t : ℕ, E ≤ t → ¬ Good (orbit 4 1 t) := by
    intro t ht hg
    have hh := horbit (t-E)
    rw [Nat.add_sub_of_le ht] at hh
    exact (not_lt_of_ge (hgood _ hg)) hh
  apply Erdos406SingleAffine.single_affine_criterion
  refine ((Finset.range E).finite_toSet.image (orbit 4 1)).subset ?_
  rintro n ⟨⟨t,rfl⟩,hg⟩
  refine ⟨t, ?_, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra ht
  exact hcut t (by omega) hg

/-- A positive multiplier preserves a strict margin, even when it is less
than one. No function satisfying the hypotheses is constructed here. -/
theorem affine_contracting_barrier_criterion (V : ℕ → ℝ) (B a : ℝ) (E : ℕ)
    (ha : 0 < a)
    (hstep : ∀ n, a * (V n-B) ≤ V (4*n+1)-B)
    (hgood : ∀ n, Good n → V n ≤ B)
    (hseed : B < V (orbit 4 1 E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply affine_threshold_criterion V B E ?_ hgood hseed
  intro n hn
  have hh := (mul_pos ha (sub_pos.mpr hn)).trans_le (hstep n)
  exact sub_pos.mp hh

#print axioms affine_threshold_criterion
#print axioms affine_contracting_barrier_criterion

#print axioms affine_barrier_criterion
#print axioms MonotoneCore.nondecreasing
#print axioms weighted_barrier_criterion

end Erdos406AffineBarrier
