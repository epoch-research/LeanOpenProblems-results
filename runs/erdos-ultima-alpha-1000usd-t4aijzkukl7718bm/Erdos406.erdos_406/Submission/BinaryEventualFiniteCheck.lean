import Submission.BinaryResidueSplitFiniteCheck
import Submission.BinaryEventualCertificates

/-! Finite checks for eventual binary residue certificates. Every check remains
an explicit premise; no certificate satisfying the power-tail seed is asserted. -/
namespace Erdos406BinaryEventualFinite
open Erdos406BinaryCertificate Erdos406BinaryResidueSplit

def layer (H h : ℕ) : Fin (H + 1) := ⟨min H h, by omega⟩
def nextLayer {H : ℕ} (h : Fin (H + 1)) : Fin (H + 1) := layer H (h.val + 1)

lemma layer_of_le {H h : ℕ} (hh : h ≤ H) :
    (layer H h).val = h := min_eq_right hh

lemma nextLayer_layer {H h : ℕ} (hh : h ≤ H) :
    nextLayer (layer H h) = layer H (h + 1) := by
  simp only [nextLayer, layer_of_le hh]

/-- A concrete instance of these finite premises would settle the conjecture.
In particular, boundary acceptance and the power-tail seed are not omitted. -/
theorem finite_of_checks {q k : ℕ} (F : Data q k) (hq : 0 < q) (hk : 0 < k)
    (H E : ℕ) (R : Fin (H + 1) → Fin q → Fin k → Fin k → Fin 3 → Bool)
    (hstart : ∀ c : Fin 3,
      R (layer H 0) (evalNat (F.dfa hq hk) 1).1 (evalNat (F.dfa hq hk) 1).2
        (evalNat (F.dfa hq hk) (3 + c.val)).2 c = true)
    (hstep : ∀ (h : Fin (H + 1)) (r : Fin q) (a b : Fin k)
      (c cp : Fin 3) (d e : Fin 2),
      3 * d.val + cp.val = 2 * c.val + e.val → R h r a b c = true →
      R (nextLayer h) (nextParent hq r d.val) (F.step r a d)
        (F.step (outputParent hq r c.val) b e) cp = true)
    (hfinish : ∀ (r : Fin q) (a b : Fin k) (c : Fin 2),
      R (layer H H) r a b ⟨c.val, by omega⟩ = true → F.test r a = true →
      F.test (outputParent hq r c.val) b = true)
    (hboundary : ∀ n : Fin (3 * 2 ^ H + 2), 2 ^ H ≤ n.val →
      Nat.digits 3 n.val ⊆ [0, 1] →
      F.test (evalNat (F.dfa hq hk) n.val).1 (evalNat (F.dfa hq hk) n.val).2 = true)
    (htailStart : F.tail (evalNat (F.dfa hq hk) (2 ^ E)).1
      (evalNat (F.dfa hq hk) (2 ^ E)).2 = true)
    (htailStep : ∀ (r : Fin q) (a : Fin k), F.tail r a = true →
      F.tail (nextParent hq r 0) (F.step r a 0) = true)
    (htailReject : ∀ (r : Fin q) (a : Fin k), F.tail r a = true → F.test r a = false) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  let D := F.dfa hq hk
  let Q : ℕ → (Fin q × Fin k) → (Fin q × Fin k) → ℕ → Prop := fun h s t c =>
    t.1 = outputParent hq s.1 c ∧ R (layer H h) s.1 s.2 t.2 (rem 3 (by decide) c) = true
  let C : Erdos406BinaryEventual.Certificate (Fin q × Fin k) := {
    D := D
    height := H
    R := Q
    relation_start := by
      intro c hc
      constructor
      · apply Fin.ext
        change (evalNat (F.dfa hq hk) (3 + c)).1.val =
          (3 * (evalNat (F.dfa hq hk) 1).1.val + c) % q
        rw [parent_eval, parent_eval]
        conv_lhs => rw [show 3 = 3 * 1 by omega]
        exact (Nat.ModEq.refl 3 |>.mul (Nat.mod_modEq 1 q)).add_right c |>.symm
      · simpa only [D, rem, Nat.mod_eq_of_lt hc] using hstart ⟨c, hc⟩
    relation_step := by
      rintro h ⟨r, a⟩ ⟨s, b⟩ c d e cp hh hc hd he hcp heq ⟨hs, hr⟩
      change s = outputParent hq r c at hs
      subst s
      have hnext := hstep (layer H h) r a b ⟨c, hc⟩ ⟨cp, hcp⟩ ⟨d, hd⟩ ⟨e, he⟩ heq
        (by simpa only [rem, Nat.mod_eq_of_lt hc] using hr)
      rw [nextLayer_layer hh] at hnext
      constructor
      · simpa only [D, Data.dfa, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] using
          parent_carry hq r c d e cp heq
      · have hl : layer H (min H (h + 1)) = layer H (h + 1) := by
          apply Fin.ext
          simp [layer]
        simpa only [Q, D, Data.dfa, rem, bit, Nat.mod_eq_of_lt hd,
          Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hcp, hl] using hnext
    relation_finish := by
      rintro ⟨r, a⟩ ⟨s, b⟩ c hc ⟨hs, hr⟩ ha
      change s = outputParent hq r c at hs
      subst s
      exact hfinish r a b ⟨c, hc⟩
        (by simpa only [rem, Nat.mod_eq_of_lt (show c < 3 by omega)] using hr) ha
    boundary := by
      intro n hn hb hg
      exact hboundary ⟨n, by omega⟩ hn hg
    cutoff := E
    Z := fun s => F.tail s.1 s.2 = true
    tail_start := htailStart
    tail_step := by
      rintro ⟨r, a⟩ hz
      exact htailStep r a hz
    tail_reject := by
      rintro ⟨r, a⟩ hz ha
      have hh := htailReject r a hz
      change F.test r a = true at ha
      rw [hh] at ha
      contradiction
  }
  exact C.finiteness

#print axioms finite_of_checks
end Erdos406BinaryEventualFinite
