import Submission.BinaryCertificates

/-! A finite-check interface for the binary residue-splitting search.
This is a conditional criterion, not a witness settling Erdős 406. -/
namespace Erdos406BinaryResidueSplit
open Erdos406BinaryCertificate

structure Data (q k : ℕ) where
  step : Fin q → Fin k → Fin 2 → Fin k
  test : Fin q → Fin k → Bool
  relation : Fin q → Fin k → Fin k → Fin 3 → Bool
  tail : Fin q → Fin k → Bool

def rem (q : ℕ) (hq : 0 < q) (n : ℕ) : Fin q := ⟨n % q, Nat.mod_lt n hq⟩
def bit (d : ℕ) : Fin 2 := rem 2 (by decide) d

def nextParent {q : ℕ} (hq : 0 < q) (r : Fin q) (d : ℕ) : Fin q :=
  rem q hq (2 * r.val + d)

def outputParent {q : ℕ} (hq : 0 < q) (r : Fin q) (c : ℕ) : Fin q :=
  rem q hq (3 * r.val + c)

def Data.dfa {q k : ℕ} (F : Data q k) (hq : 0 < q) (hk : 0 < k) :
    DFA ℕ (Fin q × Fin k) where
  start := (⟨0, hq⟩, ⟨0, hk⟩)
  step s d := (nextParent hq s.1 (d % 2), F.step s.1 s.2 (bit d))
  accept := {s | F.test s.1 s.2 = true}

lemma bit_val (d : Fin 2) : bit d.val = d := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt d.isLt

lemma dfa_step {q k : ℕ} (F : Data q k) (hq : 0 < q) (hk : 0 < k)
    (s : Fin q × Fin k) (d : Fin 2) :
    (F.dfa hq hk).step s d.val = (nextParent hq s.1 d.val, F.step s.1 s.2 d) := by
  simp only [Data.dfa, Nat.mod_eq_of_lt d.isLt, bit_val]

lemma parent_eval {q k : ℕ} (F : Data q k) (hq : 0 < q) (hk : 0 < k) (n : ℕ) :
    (evalNat (F.dfa hq hk) n).1.val = n % q := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [evalNat_zero, Data.dfa]
    · rw [evalNat_pos _ (by omega : 0 < n)]
      change (2 * (evalNat (F.dfa hq hk) (n / 2)).1.val + n % 2 % 2) % q = n % q
      rw [ih (n / 2) (Nat.div_lt_self (by omega) (by decide)), Nat.mod_mod]
      calc
        _ = (2 * (n / 2) + n % 2) % q := by simp [Nat.add_mod, Nat.mul_mod]
        _ = _ := by congr 1; omega

lemma parent_carry {q : ℕ} (hq : 0 < q) (r : Fin q) (c d e cp : ℕ)
    (he : 3 * d + cp = 2 * c + e) :
    nextParent hq (outputParent hq r c) e =
      outputParent hq (nextParent hq r d) cp := by
  apply Fin.ext
  change (2 * ((3 * r.val + c) % q) + e) % q =
    (3 * ((2 * r.val + d) % q) + cp) % q
  calc
    _ = (2 * (3 * r.val + c) + e) % q := by simp [Nat.add_mod, Nat.mul_mod]
    _ = (3 * (2 * r.val + d) + cp) % q := by congr 1; omega
    _ = _ := by simp [Nat.add_mod, Nat.mul_mod]

/-- Every quantified check below ranges over a finite type. A concrete witness
still has to satisfy all these checks; none is asserted in this file. -/
theorem finite_of_checks {q k : ℕ} (F : Data q k) (hq : 0 < q) (hk : 0 < k) (E : ℕ)
    (hstart : ∀ c : Fin 3,
      F.relation ⟨0, hq⟩ ⟨0, hk⟩ (evalNat (F.dfa hq hk) c.val).2 c = true)
    (hstep : ∀ (r : Fin q) (a b : Fin k) (c cp : Fin 3) (d e : Fin 2),
      3 * d.val + cp.val = 2 * c.val + e.val → F.relation r a b c = true →
      F.relation (nextParent hq r d.val) (F.step r a d)
        (F.step (outputParent hq r c.val) b e) cp = true)
    (hfinish : ∀ (r : Fin q) (a b : Fin k) (c : Fin 2),
      F.relation r a b ⟨c.val, by omega⟩ = true → F.test r a = true →
      F.test (outputParent hq r c.val) b = true)
    (hzero : F.test ⟨0, hq⟩ ⟨0, hk⟩ = true)
    (htailStart : F.tail (evalNat (F.dfa hq hk) (2 ^ E)).1
      (evalNat (F.dfa hq hk) (2 ^ E)).2 = true)
    (htailStep : ∀ (r : Fin q) (a : Fin k), F.tail r a = true →
      F.tail (nextParent hq r 0) (F.step r a 0) = true)
    (htailReject : ∀ (r : Fin q) (a : Fin k), F.tail r a = true → F.test r a = false) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  let D := F.dfa hq hk
  let R : (Fin q × Fin k) → (Fin q × Fin k) → ℕ → ℕ → Prop := fun s t c v =>
    v = 0 ∧ t.1 = outputParent hq s.1 c ∧
      F.relation s.1 s.2 t.2 (rem 3 (by decide) c) = true
  let C : Certificate (Fin q × Fin k) := {
    D := D
    depth := 0
    R := R
    relation_start := by
      intro c hc
      refine ⟨rfl, ?_, ?_⟩
      · apply Fin.ext
        simpa [D, Data.dfa, outputParent, rem] using parent_eval F hq hk c
      · simpa [D, Data.dfa, rem, Nat.mod_eq_of_lt hc] using hstart ⟨c, hc⟩
    relation_step := by
      rintro ⟨r, a⟩ ⟨s, b⟩ c v d e cp hc hv hd he hcp heq ⟨hv0, hs, hr⟩
      change s = outputParent hq r c at hs
      subst s
      have hh := hstep r a b ⟨c, hc⟩ ⟨cp, hcp⟩ ⟨d, hd⟩ ⟨e, he⟩ heq
        (by simpa only [rem, Nat.mod_eq_of_lt hc] using hr)
      change (2 * v + d) % 3 ^ 0 = 0 ∧ _
      refine ⟨by exact Nat.mod_one _, ?_, ?_⟩
      · simpa only [D, Data.dfa, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] using
          parent_carry hq r c d e cp heq
      · simpa only [D, Data.dfa, rem, bit, Nat.mod_eq_of_lt hd,
          Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hcp] using hh
    relation_finish := by
      rintro ⟨r, a⟩ ⟨s, b⟩ c v hc hv hg ⟨hv0, hs, hr⟩ ha
      change s = outputParent hq r c at hs
      subst s
      exact hfinish r a b ⟨c, hc⟩
        (by simpa only [rem, Nat.mod_eq_of_lt (show c < 3 by omega)] using hr) ha
    accept_zero := hzero
    cutoff := E
    Z := fun s _ => F.tail s.1 s.2 = true
    tail_start := htailStart
    tail_step := by
      rintro ⟨r, a⟩ v hv hz
      exact htailStep r a hz
    tail_reject := by
      rintro ⟨r, a⟩ v hv hz hg ha
      have hh := htailReject r a hz
      change F.test r a = true at ha
      rw [hh] at ha
      contradiction
  }
  exact C.finiteness

#print axioms finite_of_checks
end Erdos406BinaryResidueSplit
