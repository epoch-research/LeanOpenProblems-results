import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command Nat List

set_option maxHeartbeats 0
set_option maxRecDepth 10000

elab "#reset_caches" : command => do
  liftCoreM do modify fun s => { s with cache := {}, messages := {} }
  liftTermElabM do
    modifyThe Meta.State fun s => { s with cache := {}, mctx := {}, postponed := {}, diag := {} }
  modify fun s => { s with infoState := {}, traceState := {}, messages := {} }

abbrev n0 : ℕ := 550172
abbrev cover0 : ℕ := 17135927
abbrev missR : ℕ := 63945
abbrev bound0 : ℕ := 16331504
abbrev lastPrime0 : ℕ := 8165753
abbrev period0 : ℕ := 80200

def binPowMod : ℕ → ℕ → ℕ
  | 0, _ => 1
  | d + 1, k =>
      let r := binPowMod d (k / 2)
      let r2 := (r * r) % n0
      if k % 2 = 0 then r2 else (r2 * 2) % n0

def checkOne (k r : ℕ) : Bool :=
  decide (1 ≤ k) && decide (k ≤ cover0) && (binPowMod 25 k == (r + k) % n0)

lemma checkOne_iff (k r : ℕ) :
    checkOne k r = true ↔
      1 ≤ k ∧ k ≤ cover0 ∧ binPowMod 25 k = (r + k) % n0 := by
  constructor
  · intro h
    have h' : (decide (1 ≤ k) = true ∧ decide (k ≤ cover0) = true) ∧
        (binPowMod 25 k == (r + k) % n0) = true := by
      simpa [checkOne, Bool.and_eq_true] using h
    exact ⟨decide_eq_true_eq.mp h'.1.1, decide_eq_true_eq.mp h'.1.2,
      beq_iff_eq.mp h'.2⟩
  · intro h
    refine Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨?_, ?_⟩, ?_⟩
    · exact decide_eq_true_eq.mpr h.1
    · exact decide_eq_true_eq.mpr h.2.1
    · exact beq_iff_eq.mpr h.2.2

def checkList : List ℕ → ℕ → Bool
  | [], _ => true
  | k :: ks, r => checkOne k r && checkList ks (r + 1)

lemma checkList_cons (k : ℕ) (ks : List ℕ) (r : ℕ) :
    checkList (k :: ks) r = (checkOne k r && checkList ks (r + 1)) := rfl

lemma checkList_spec :
    ∀ (ks : List ℕ) (start : ℕ),
      checkList ks start = true →
      ∀ (i : ℕ) (hi : i < ks.length),
        1 ≤ ks[i] ∧ ks[i] ≤ cover0 ∧
          binPowMod 25 ks[i] = (start + i + ks[i]) % n0
  | [], start, h, i, hi => nomatch hi
  | k :: ks, start, h, 0, hi => by
    have h' : checkOne k start = true ∧ checkList ks (start + 1) = true :=
      Bool.and_eq_true_iff.1 (by simpa [checkList_cons] using h)
    simpa using (checkOne_iff k start).1 h'.1
  | k :: ks, start, h, i + 1, hi => by
    have h' : checkOne k start = true ∧ checkList ks (start + 1) = true :=
      Bool.and_eq_true_iff.1 (by simpa [checkList_cons] using h)
    have hi' : i < ks.length := Nat.succ_lt_succ_iff.mp hi
    have ih := checkList_spec ks (start + 1) h'.2 i hi'
    refine ⟨ih.1, ih.2.1, ?_⟩
    have : start + (i + 1) = start + 1 + i := by omega
    rw [this]
    exact ih.2.2

lemma exists_of_checkList (ks : List ℕ) (start : ℕ)
    (h : checkList ks start = true) (r : ℕ)
    (h1 : start ≤ r) (h2 : r < start + ks.length) :
    ∃ k, 1 ≤ k ∧ k ≤ cover0 ∧ binPowMod 25 k = (r + k) % n0 := by
  let i := r - start
  have hi : i < ks.length := by omega
  have hs := checkList_spec ks start h i hi
  have hsum : start + i = r := by omega
  refine ⟨ks[i], hs.1, hs.2.1, ?_⟩
  rw [hsum] at hs
  exact hs.2.2

def baseOf (i : ℕ) : ℕ :=
  200 * ((((2 ^ i % 401 + 616 - i) % 401) * 399) % 401) + i

def checkMiss (i t : ℕ) : Bool :=
  let k := baseOf i + period0 * t
  decide (bound0 ≤ k) || !(binPowMod 25 k == (missR + k) % n0)

lemma checkMiss_spec (i t : ℕ) (h : checkMiss i t = true) :
    bound0 ≤ baseOf i + period0 * t ∨
      binPowMod 25 (baseOf i + period0 * t) ≠
        (missR + (baseOf i + period0 * t)) % n0 := by
  dsimp [checkMiss] at h
  cases hb : decide (bound0 ≤ baseOf i + period0 * t) with
  | true =>
    left
    exact decide_eq_true_eq.mp hb
  | false =>
    right
    have hne : (binPowMod 25 (baseOf i + period0 * t) ==
        (missR + (baseOf i + period0 * t)) % n0) = false := by
      simpa [hb] using h
    exact beq_eq_false_iff_ne.mp hne

def checkMissRow (i : ℕ) : Bool :=
  (List.range 204).all (fun t => checkMiss i t)

lemma checkMissRow_spec (i : ℕ) (h : checkMissRow i = true) :
    ∀ t, t ≤ 203 → checkMiss i t = true := by
  intro t ht
  have : t ∈ List.range 204 := by
    simp [List.mem_range]
    omega
  exact List.all_eq_true.mp h t this

def strictSorted : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && strictSorted (b :: rest)

lemma strictSorted_head_le :
    ∀ (a : ℕ) (l : List ℕ), strictSorted (a :: l) = true →
      ∀ p ∈ (a :: l), a ≤ p
  | a, [], _, p, hp => by
    cases hp with
    | head => omega
    | tail _ h => cases h
  | a, b :: ls, h, p, hp => by
    have h' : a < b ∧ strictSorted (b :: ls) = true := by
      simpa [strictSorted, Bool.and_eq_true, decide_eq_true_eq] using h
    cases hp with
    | head => omega
    | tail _ hp' =>
      have := strictSorted_head_le b ls h'.2 p hp'
      omega

lemma strictSorted_nodup : ∀ l : List ℕ, strictSorted l = true → l.Nodup
  | [], _ => nodup_nil
  | [a], _ => nodup_singleton a
  | a :: b :: ls, h => by
    have h' : a < b ∧ strictSorted (b :: ls) = true := by
      simpa [strictSorted, Bool.and_eq_true, decide_eq_true_eq] using h
    have hnd : (b :: ls).Nodup := strictSorted_nodup (b :: ls) h'.2
    have hnotin : a ∉ b :: ls := by
      intro hin
      have := strictSorted_head_le b ls h'.2 a hin
      omega
    exact nodup_cons.2 ⟨hnotin, hnd⟩

lemma toFinset_card_ss (l : List ℕ) (h : strictSorted l = true) :
    l.toFinset.card = l.length :=
  toFinset_card_of_nodup (strictSorted_nodup l h)

def tiny : List ℕ := [1, 2]
lemma tiny_ok : checkList tiny 1 = true := rfl
lemma tiny_ex : ∃ k, 1 ≤ k ∧ k ≤ cover0 ∧ binPowMod 25 k = (1 + k) % n0 :=
  exists_of_checkList tiny 1 tiny_ok 1 (by decide) (by decide)
