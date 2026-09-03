import Submission.GroupedAffineCertificates

/-! A shared orbit y'=64y+1 for the two affine classes. Long division
converts an invariant for y into invariants for 7y and 28y. No invariant
witness or unconditional finiteness theorem is supplied. -/

namespace Erdos406SharedCertificate
open Erdos406AffineCertificate Erdos406GroupedCertificate

lemma orbit_scale (q a t : ℕ) : orbit q a t = a * orbit q 1 t := by
  induction t with
  | zero => simp
  | succ t ih => rw [orbit_succ, orbit_succ, ih]; ring

lemma quotient_carry (b m n : ℕ) :
    (b * (n / b % m) + n % b) / m = n / m % b ∧
    (b * (n / b % m) + n % b) % m = n % m := by
  have he : b * (n / b % m) + n % b = n % (b * m) := by
    rw [Nat.mod_mul]
    omega
  rw [he, Nat.mod_mul_left_div_self,
    Nat.mod_mod_of_dvd n (dvd_mul_left m b)]
  exact ⟨rfl, rfl⟩

def quotientDFA {σ : Type*} (b m : ℕ) (hm : 0 < m) (D : DFA ℕ σ) :
    DFA ℕ (σ × Fin m) where
  start := (D.start, ⟨0, hm⟩)
  step s d := (D.step s.1 ((b * s.2.val + d) / m),
    ⟨(b * s.2.val + d) % m, Nat.mod_lt _ hm⟩)
  accept := {s | s.1 ∈ D.accept ∧ s.2.val = 0}

lemma evalNat_step {σ : Type*} (b : ℕ) (D : DFA ℕ σ) (hb : 2 ≤ b)
    (hz : D.step D.start 0 = D.start) (n : ℕ) :
    evalNat b D n = D.step (evalNat b D (n / b)) (n % b) := by
  by_cases hn : n = 0
  · simp [hn, evalNat_zero, hz]
  · exact evalNat_pos b D hb (Nat.pos_of_ne_zero hn)

lemma quotientDFA_eval {σ : Type*} (b m : ℕ) (hm : 0 < m)
    (D : DFA ℕ σ) (hb : 2 ≤ b) (hz : D.step D.start 0 = D.start) (n : ℕ) :
    evalNat b (quotientDFA b m hm D) n =
      (evalNat b D (n / m), ⟨n % m, Nat.mod_lt _ hm⟩) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [evalNat_zero, quotientDFA]
    have hnpos := Nat.pos_of_ne_zero hn
    rw [evalNat_pos b _ hb hnpos, ih (n / b) (Nat.div_lt_self hnpos hb)]
    apply Prod.ext
    · change D.step (evalNat b D (n / b / m)) ((b * (n / b % m) + n % b) / m) =
        evalNat b D (n / m)
      have hdiv : n / b / m = n / m / b := by
        rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm b m]
      rw [(quotient_carry b m n).1, hdiv, ← evalNat_step b D hb hz (n / m)]
    · apply Fin.ext
      exact (quotient_carry b m n).2

lemma quotientDFA_accept_iff {σ : Type*} (b m : ℕ) (hm : 0 < m)
    (D : DFA ℕ σ) (hb : 2 ≤ b) (hz : D.step D.start 0 = D.start) (n : ℕ) :
    evalNat b (quotientDFA b m hm D) n ∈ (quotientDFA b m hm D).accept ↔
      evalNat b D (n / m) ∈ D.accept ∧ m ∣ n := by
  rw [quotientDFA_eval b m hm D hb hz n]
  change (_ ∈ D.accept ∧ n % m = 0) ↔ _
  rw [Nat.dvd_iff_mod_eq_zero]

lemma quotient_accepts_scaled_orbit {σ : Type*} (C : Erdos406GroupedCertificate.Core σ)
    (hz : C.D.step C.D.start 0 = C.D.start) (hc : C.c = 1)
    (a : ℕ) (ha : 0 < a) (t : ℕ) :
    evalNat C.base (quotientDFA C.base a ha C.D) (orbit C.q a t) ∈
      (quotientDFA C.base a ha C.D).accept := by
  rw [quotientDFA_accept_iff C.base a ha C.D C.base_ge_two hz, orbit_scale]
  constructor
  · have hh := C.accepts_orbit t
    simpa only [hc, Nat.mul_div_cancel_left _ ha] using hh
  · exact dvd_mul_right _ _

/-- The finite-language rank check is independent of how the automaton is
proved to contain an orbit; this allows the long-division construction. -/
theorem finite_good_accepted {σ : Type*} (h : ℕ) (hh : 0 < h) (D : DFA ℕ σ)
    (G K : σ → Prop) (rank : σ → ℕ) (bound : ℕ)
    (hgstart : ∀ d, GoodBlock h d → d ≠ 0 → G (D.step D.start d))
    (hgstep : ∀ s d, GoodBlock h d → G s → G (D.step s d))
    (hkacc : ∀ s, s ∈ D.accept → K s)
    (hkstep : ∀ s d, GoodBlock h d → K (D.step s d) → K s)
    (hrstep : ∀ s d, GoodBlock h d → G s → K (D.step s d) → rank (D.step s d) < rank s)
    (hrbound : ∀ s, rank s ≤ bound) :
    {n : ℕ | Good n ∧ evalNat (3 ^ h) D n ∈ D.accept}.Finite := by
  have hb : 2 ≤ 3 ^ h := by
    have hp := one_lt_pow₀ (by decide : 1 < (3 : ℕ)) (Nat.ne_of_gt hh)
    omega
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨(3 ^ h) ^ (bound + 1), ?_⟩
  rintro n ⟨hd, ha⟩
  by_cases hn : n = 0
  · simp [hn]
  · have hdigits := good_grouped_digits h hh hd
    have hl := digit_length_bound (3 ^ h) D (GoodBlock h) G K rank bound
      hgstart hgstep hkacc hkstep hrstep hrbound (Nat.pos_of_ne_zero hn) hdigits ha
    have hlt := Nat.lt_base_pow_length_digits (b := 3 ^ h) (m := n) hb
    exact (Nat.le_of_lt hlt).trans (Nat.pow_le_pow_right (by omega) hl)

/-- A shared certificate, with finite good languages for its two quotient
DFAs, suffices for the exact original conjecture. The hypotheses are not
asserted to hold for any automaton in this file. -/
theorem shared_certificate_criterion {σ : Type*} (C : Erdos406GroupedCertificate.Core σ)
    (hz : C.D.step C.D.start 0 = C.D.start) (hq : C.q = 64) (hc : C.c = 1)
    (h7 : {n : ℕ | Good n ∧
      evalNat C.base (quotientDFA C.base 7 (by decide) C.D) n ∈
        (quotientDFA C.base 7 (by decide) C.D).accept}.Finite)
    (h28 : {n : ℕ | Good n ∧
      evalNat C.base (quotientDFA C.base 28 (by decide) C.D) n ∈
        (quotientDFA C.base 28 (by decide) C.D).accept}.Finite) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply affine_orbits_criterion
  · refine h7.subset ?_
    rintro n ⟨⟨t, rfl⟩, hd⟩
    exact ⟨hd, by simpa only [hq] using quotient_accepts_scaled_orbit C hz hc 7 (by decide) t⟩
  · refine h28.subset ?_
    rintro n ⟨⟨t, rfl⟩, hd⟩
    exact ⟨hd, by simpa only [hq] using quotient_accepts_scaled_orbit C hz hc 28 (by decide) t⟩

#print axioms quotientDFA_eval
#print axioms finite_good_accepted
#print axioms shared_certificate_criterion
end Erdos406SharedCertificate
