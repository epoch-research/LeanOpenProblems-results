import FormalConjecturesUtil

/-! Soundness of a dual certificate search: a binary automaton invariant under
`n ↦ 3*n` and `n ↦ 3*n+1`, with a fixed ternary residue guard. No certificate
witness is asserted here. -/

namespace Erdos406BinaryCertificate

def evalNat {σ : Type*} (D : DFA ℕ σ) (n : ℕ) : σ :=
  D.eval (Nat.digits 2 n).reverse

lemma evalNat_zero {σ : Type*} (D : DFA ℕ σ) : evalNat D 0 = D.start := by
  simp [evalNat]

lemma evalNat_pos {σ : Type*} (D : DFA ℕ σ) {n : ℕ} (hn : 0 < n) :
    evalNat D n = D.step (evalNat D (n / 2)) (n % 2) := by
  rw [evalNat, Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hn,
    List.reverse_cons, DFA.eval_append_singleton]
  rfl

lemma evalNat_twice {σ : Type*} (D : DFA ℕ σ) {n : ℕ} (hn : 0 < n) :
    evalNat D (2 * n) = D.step (evalNat D n) 0 := by
  rw [evalNat_pos D (by omega : 0 < 2 * n)]
  simp

lemma good_ofDigits {w : List ℕ} (hw : w ⊆ [0, 1]) :
    Nat.digits 3 (Nat.ofDigits 3 w) ⊆ [0, 1] := by
  induction w with
  | nil => simp [Nat.ofDigits]
  | cons d w ih =>
    have hd := hw (by simp : d ∈ d :: w)
    have ht : w ⊆ [0, 1] := fun a ha => hw (by simp [ha])
    have h := ih ht
    have hdlt : d < 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    rw [Nat.ofDigits_cons]
    by_cases hz : d = 0 ∧ Nat.ofDigits 3 w = 0
    · simp [hz.1, hz.2]
    · rw [Nat.digits_add 3 (by decide) d (Nat.ofDigits 3 w) hdlt (by tauto)]
      simpa using List.cons_subset.mpr ⟨hd, h⟩

lemma good_mod {n : ℕ} (hn : Nat.digits 3 n ⊆ [0, 1]) (r : ℕ) :
    Nat.digits 3 (n % 3 ^ r) ⊆ [0, 1] := by
  rw [Nat.self_mod_pow_eq_ofDigits_take r n (by decide : 2 ≤ 3)]
  exact good_ofDigits fun d hd => hn (List.mem_of_mem_take hd)

/-- A finite-state instance of this structure would settle the conjecture.
The relation reads binary digits most significant first. Its carry satisfies
`3*d + nextCarry = 2*carry + outputDigit`. -/
structure Certificate (σ : Type*) where
  D : DFA ℕ σ
  depth : ℕ
  R : σ → σ → ℕ → ℕ → Prop
  relation_start : ∀ c, c < 3 → R D.start (evalNat D c) c 0
  relation_step : ∀ s t c v d e c', c < 3 → v < 3 ^ depth →
    d < 2 → e < 2 → c' < 3 → 3 * d + c' = 2 * c + e → R s t c v →
    R (D.step s d) (D.step t e) c' ((2 * v + d) % 3 ^ depth)
  relation_finish : ∀ s t c v, c < 2 → v < 3 ^ depth →
    Nat.digits 3 v ⊆ [0, 1] → R s t c v → s ∈ D.accept → t ∈ D.accept
  accept_zero : D.start ∈ D.accept
  cutoff : ℕ
  Z : σ → ℕ → Prop
  tail_start : Z (evalNat D (2 ^ cutoff)) (2 ^ cutoff % 3 ^ depth)
  tail_step : ∀ s v, v < 3 ^ depth → Z s v → Z (D.step s 0) (2 * v % 3 ^ depth)
  tail_reject : ∀ s v, v < 3 ^ depth → Z s v → Nat.digits 3 v ⊆ [0, 1] →
    s ∉ D.accept

namespace Certificate

variable {σ : Type*} (C : Certificate σ)

lemma relation (n c : ℕ) (hc : c < 3) :
    C.R (evalNat C.D n) (evalNat C.D (3 * n + c)) c (n % 3 ^ C.depth) := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [mul_zero, zero_add, Nat.zero_mod, evalNat_zero] using
        C.relation_start c hc
    · have hnpos : 0 < n := by omega
      let d := n % 2
      let cp := (3 * d + c) / 2
      let e := (3 * d + c) % 2
      have hd : d < 2 := Nat.mod_lt n (by decide)
      have he : e < 2 := Nat.mod_lt _ (by decide)
      have hcp : cp < 3 := by dsimp [cp]; omega
      have hrel := ih (n / 2) (Nat.div_lt_self hnpos (by decide)) cp hcp
      have hv : n / 2 % 3 ^ C.depth < 3 ^ C.depth := Nat.mod_lt _ (by positivity)
      have hstep := C.relation_step _ _ cp _ d e c hcp hv hd he hc
        (by dsimp [cp, e]; omega) hrel
      have hq : (3 * n + c) / 2 = 3 * (n / 2) + cp := by dsimp [cp, d]; omega
      have hm : (3 * n + c) % 2 = e := by dsimp [e, d]; omega
      have hv' : (2 * (n / 2 % 3 ^ C.depth) + d) % 3 ^ C.depth = n % 3 ^ C.depth := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
        congr 1
        dsimp [d]
        omega
      rw [evalNat_pos C.D hnpos, evalNat_pos C.D (by omega : 0 < 3 * n + c), hq, hm]
      rwa [hv'] at hstep

lemma affine_closed (n c : ℕ) (hc : c < 2)
    (hg : Nat.digits 3 (n % 3 ^ C.depth) ⊆ [0, 1])
    (ha : evalNat C.D n ∈ C.D.accept) :
    evalNat C.D (3 * n + c) ∈ C.D.accept := by
  exact C.relation_finish _ _ c _ hc (Nat.mod_lt _ (by positivity)) hg
    (C.relation n c (by omega)) ha

lemma accepts_good (n : ℕ) (hn : Nat.digits 3 n ⊆ [0, 1]) :
    evalNat C.D n ∈ C.D.accept := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · simpa [hn0, evalNat_zero] using C.accept_zero
    · have hnpos : 0 < n := by omega
      rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hnpos] at hn
      have hd : n % 3 < 2 := by
        have hh := hn (List.mem_cons_self ..)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        omega
      have hg : Nat.digits 3 (n / 3) ⊆ [0, 1] :=
        fun d hd => hn (List.mem_cons_of_mem _ hd)
      have hh := C.affine_closed (n / 3) (n % 3) hd (good_mod hg C.depth)
        (ih (n / 3) (Nat.div_lt_self hnpos (by decide)) hg)
      have he : 3 * (n / 3) + n % 3 = n := by omega
      simpa only [he] using hh

lemma tail (t : ℕ) :
    C.Z (evalNat C.D (2 ^ (C.cutoff + t))) (2 ^ (C.cutoff + t) % 3 ^ C.depth) := by
  induction t with
  | zero => simpa using C.tail_start
  | succ t ih =>
    have hh := C.tail_step _ _ (Nat.mod_lt _ (by positivity)) ih
    rw [← Nat.add_assoc, pow_succ', evalNat_twice C.D (by positivity)]
    simpa only [Nat.mul_mod, Nat.mod_mod] using hh

/-- This conclusion is the original conjecture, conditional on a certificate.
No certificate witness has been constructed. -/
theorem finiteness (C : Certificate σ) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨2 ^ C.cutoff, ?_⟩
  rintro n ⟨⟨k, rfl⟩, hg⟩
  by_cases hk : k < C.cutoff
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · have he : C.cutoff + (k - C.cutoff) = k := by omega
    have hz := C.tail (k - C.cutoff)
    rw [he] at hz
    exact False.elim (C.tail_reject _ _ (Nat.mod_lt _ (by positivity)) hz
      (good_mod hg C.depth) (C.accepts_good _ hg))

end Certificate

#print axioms Certificate.finiteness
end Erdos406BinaryCertificate


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


/-! Conditional soundness for binary invariants whose affine-construction
failures occur only below a fixed threshold. No witness is supplied. -/
namespace Erdos406BinaryEventual
open Erdos406BinaryCertificate

structure Certificate (σ : Type*) where
  D : DFA ℕ σ
  height : ℕ
  R : ℕ → σ → σ → ℕ → Prop
  relation_start : ∀ c, c < 3 → R 0 (evalNat D 1) (evalNat D (3 + c)) c
  relation_step : ∀ h s t c d e cp, h ≤ height → c < 3 → d < 2 → e < 2 → cp < 3 →
    3 * d + cp = 2 * c + e → R h s t c →
    R (min height (h + 1)) (D.step s d) (D.step t e) cp
  relation_finish : ∀ s t c, c < 2 → R height s t c → s ∈ D.accept → t ∈ D.accept
  boundary : ∀ n, 2 ^ height ≤ n → n ≤ 3 * 2 ^ height + 1 →
    Nat.digits 3 n ⊆ [0, 1] → evalNat D n ∈ D.accept
  cutoff : ℕ
  Z : σ → Prop
  tail_start : Z (evalNat D (2 ^ cutoff))
  tail_step : ∀ s, Z s → Z (D.step s 0)
  tail_reject : ∀ s, Z s → s ∉ D.accept

namespace Certificate
variable {σ : Type*} (C : Certificate σ)

lemma relation (n c : ℕ) (hn : 0 < n) (hc : c < 3) :
    C.R (min C.height n.log2) (evalNat C.D n) (evalNat C.D (3 * n + c)) c := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst n
      simpa only [show Nat.log2 1 = 0 by decide, Nat.min_zero, Nat.mul_one] using C.relation_start c hc
    · have hn2 : 2 ≤ n := by omega
      let d := n % 2
      let cp := (3 * d + c) / 2
      let e := (3 * d + c) % 2
      have hd : d < 2 := Nat.mod_lt _ (by decide)
      have he : e < 2 := Nat.mod_lt _ (by decide)
      have hcp : cp < 3 := by dsimp [cp]; omega
      have hprev := ih (n / 2) (Nat.div_lt_self hn (by decide)) cp (by omega) hcp
      have hs := C.relation_step (min C.height (n / 2).log2) _ _ cp d e c
        (Nat.min_le_left _ _) hcp hd he hc (by dsimp [cp, e]; omega) hprev
      have hq : (3 * n + c) / 2 = 3 * (n / 2) + cp := by dsimp [cp, d]; omega
      have hm : (3 * n + c) % 2 = e := by dsimp [e, d]; omega
      have hl : n.log2 = (n / 2).log2 + 1 := by
        rw [Nat.log2_def n, if_pos hn2]
      have hh : min C.height (min C.height (n / 2).log2 + 1) = min C.height n.log2 := by
        rw [hl]
        omega
      rw [hh] at hs
      rw [evalNat_pos C.D hn, evalNat_pos C.D (by omega : 0 < 3 * n + c), hq, hm]
      exact hs

lemma affine_closed (n c : ℕ) (hn : 2 ^ C.height ≤ n) (hc : c < 2)
    (ha : evalNat C.D n ∈ C.D.accept) : evalNat C.D (3 * n + c) ∈ C.D.accept := by
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hh : C.height ≤ n.log2 := (Nat.le_log2 (Nat.ne_of_gt hn0)).mpr hn
  have hr := C.relation n c hn0 (by omega)
  rw [min_eq_left hh] at hr
  exact C.relation_finish _ _ c hc hr ha

lemma accepts_good (n : ℕ) (hn : 2 ^ C.height ≤ n)
    (hg : Nat.digits 3 n ⊆ [0, 1]) : evalNat C.D n ∈ C.D.accept := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hb : n ≤ 3 * 2 ^ C.height + 1
    · exact C.boundary n hn hb hg
    · have hn0 : 0 < n := by omega
      rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn0] at hg
      have hd : n % 3 < 2 := by
        have hh := hg (List.mem_cons_self ..)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        omega
      have hgood : Nat.digits 3 (n / 3) ⊆ [0, 1] :=
        fun d hd => hg (List.mem_cons_of_mem _ hd)
      have hlarge : 2 ^ C.height ≤ n / 3 := by omega
      have ha := ih (n / 3) (Nat.div_lt_self hn0 (by decide)) hlarge hgood
      have hh := C.affine_closed (n / 3) (n % 3) hlarge hd ha
      have he : 3 * (n / 3) + n % 3 = n := by omega
      rwa [he] at hh

lemma tail (t : ℕ) : C.Z (evalNat C.D (2 ^ (C.cutoff + t))) := by
  induction t with
  | zero => simpa using C.tail_start
  | succ t ih =>
    have hh := C.tail_step _ ih
    rw [← Nat.add_assoc, pow_succ', evalNat_twice C.D (by positivity)]
    exact hh

theorem finiteness (C : Certificate σ) : {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨max (2 ^ C.height) (2 ^ C.cutoff), ?_⟩
  rintro n ⟨⟨e, he⟩, hg⟩
  by_cases hn : n < 2 ^ C.height
  · exact hn.le.trans (le_max_left _ _)
  · have ha := C.accepts_good n (by omega) hg
    by_cases hec : e ≤ C.cutoff
    · rw [he]
      exact (Nat.pow_le_pow_right (by decide) hec).trans (le_max_right _ _)
    · have ht := C.tail (e - C.cutoff)
      have hh : C.cutoff + (e - C.cutoff) = e := by omega
      rw [hh, ← he] at ht
      exact False.elim (C.tail_reject _ ht ha)

end Certificate
#print axioms Certificate.finiteness
end Erdos406BinaryEventual


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

/-! Generated eventual binary-residue checks, using kernel reduction. -/
namespace Erdos406BinaryEventualExport
open Erdos406BinaryResidueSplit Erdos406BinaryCertificate Erdos406BinaryEventualFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 100000
def stepTable : List (List ℕ) := [[0, 0], [0, 0], [0, 0]]
def relationTable : List (List (List ℕ)) := [[[0, 0, 0], [1, 1, 1], [0, 0, 0]], [[1, 1, 1], [0, 0, 0], [1, 1, 1]], [[1, 1, 1], [1, 1, 1], [1, 1, 1]], [[1, 1, 1], [1, 1, 1], [1, 1, 1]]]
def acceptTable : List ℕ := [1, 1, 0]
def tailTable : List ℕ := [0, 0, 0]

def data : Data 3 1 where
  step r a d := rem 1 (by decide) ((stepTable.getD r.val []).getD (2 * a.val + d.val) 0)
  test r a := (acceptTable.getD r.val 0).testBit a.val
  relation _ _ _ _ := false
  tail r a := (tailTable.getD r.val 0).testBit a.val

def rel (h : Fin 4) (r : Fin 3) (a b : Fin 1) (c : Fin 3) : Bool :=
  (((relationTable.getD h.val []).getD r.val []).getD (1 * c.val + a.val) 0).testBit b.val

lemma checked_start : ∀ c : Fin 3,
    rel (layer 3 0) (evalNat (data.dfa (by decide) (by decide)) 1).1
      (evalNat (data.dfa (by decide) (by decide)) 1).2
      (evalNat (data.dfa (by decide) (by decide)) (3 + c.val)).2 c = true := by
  decide +kernel
lemma checked_step : ∀ (h : Fin 4) (r : Fin 3) (a b : Fin 1)
    (c cp : Fin 3) (d e : Fin 2),
    3*d.val+cp.val=2*c.val+e.val → rel h r a b c = true →
    rel (nextLayer h) (nextParent (by decide) r d.val) (data.step r a d)
      (data.step (outputParent (by decide) r c.val) b e) cp = true := by
  decide +kernel
lemma checked_finish : ∀ (r : Fin 3) (a b : Fin 1) (c : Fin 2),
    rel (layer 3 3) r a b ⟨c.val, by omega⟩ = true → data.test r a = true →
    data.test (outputParent (by decide) r c.val) b = true := by
  decide +kernel
lemma checked_boundary : ∀ n : Fin (3 * 2 ^ 3 + 2), 2 ^ 3 ≤ n.val →
    Nat.digits 3 n.val ⊆ [0,1] →
    data.test (evalNat (data.dfa (by decide) (by decide)) n.val).1
      (evalNat (data.dfa (by decide) (by decide)) n.val).2 = true := by
  decide +kernel
lemma checked_tail_step : ∀ (r : Fin 3) (a : Fin 1), data.tail r a = true →
    data.tail (nextParent (by decide) r 0) (data.step r a 0) = true := by
  decide +kernel
lemma checked_tail_reject : ∀ (r : Fin 3) (a : Fin 1), data.tail r a = true →
    data.test r a = false := by
  decide +kernel

/-- Control only: the necessary power-tail seed is FALSE. -/
lemma no_seed : ¬ (data.tail (evalNat (data.dfa (by decide) (by decide)) (2 ^ 40)).1 (evalNat (data.dfa (by decide) (by decide)) (2 ^ 40)).2 = true) := by decide +kernel
#print axioms checked_start
#print axioms checked_step
#print axioms checked_finish
#print axioms checked_boundary
#print axioms checked_tail_step
#print axioms checked_tail_reject
end Erdos406BinaryEventualExport
