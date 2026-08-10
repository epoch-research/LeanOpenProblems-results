import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The auxiliary sequence $A262439$: $a(n) = \pi(\frac{n(n+1)}{2} + 1)$, where $\pi(x)$ is the prime-counting function.
-/
def A262439 (n : ℕ) : ℕ :=
  primeCounting (n * (n + 1) / 2 + 1)

/--
A262446: Number of ways to write $A262439(n) = A262439(k) + A262439(m)$ with $0 < k < m < n$.
-/
def A262446 (n : ℕ) : ℕ :=
  -- We iterate over $k$ such that $1 \le k < n$.
  (Ico 1 n).sum fun k =>
    -- We iterate over $m$ such that $k + 1 \le m < n$.
    (Ico (k + 1) n).sum fun m =>
      if A262439 n = A262439 k + A262439 m then 1 else 0

/-- The set of $n$ for which the conjecture claims A262446(n) = 1. -/
def A262446_unique_n_set : Finset ℕ :=
  {4, 6, 11, 21, 54, 253, 325}

/-!
Supporting machinery: a kernel-reducible prime-counting function `KS.cntP`,
proven equal to `Nat.primeCounting`, used to evaluate `A262439` without building
the huge `List.range` underlying `Nat.count`.
-/

set_option maxRecDepth 100000

namespace KS
def dsF : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, a, b, n => (a < b) && (a * a ≤ n) && (n % a == 0)
  | (f+1), a, b, n =>
    if b ≤ a + 1 then (a < b) && (a * a ≤ n) && (n % a == 0)
    else if n < a * a then false
    else let mid := (a + b) / 2; dsF f a mid n || dsF f mid b n
theorem dsF_iff (f : ℕ) : ∀ a b n, b - a ≤ f →
    (dsF f a b n = true ↔ ∃ m, a ≤ m ∧ m < b ∧ m * m ≤ n ∧ m ∣ n) := by
  induction f with
  | zero =>
    intro a b n hf
    have hb : b ≤ a + 1 := by omega
    rw [dsF, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        decide_eq_true_eq, ← Nat.dvd_iff_mod_eq_zero]
    constructor
    · rintro ⟨⟨hab, hsq⟩, hd⟩; exact ⟨a, le_refl a, hab, hsq, hd⟩
    · rintro ⟨m, h1, h2, h3, h4⟩; have : m = a := by omega
      subst this; exact ⟨⟨h2, h3⟩, h4⟩
  | succ f ih =>
    intro a b n hf
    rw [dsF]
    by_cases hb : b ≤ a + 1
    · simp only [hb, if_true]
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          decide_eq_true_eq, ← Nat.dvd_iff_mod_eq_zero]
      constructor
      · rintro ⟨⟨hab, hsq⟩, hd⟩; exact ⟨a, le_refl a, hab, hsq, hd⟩
      · rintro ⟨m, h1, h2, h3, h4⟩; have : m = a := by omega
        subst this; exact ⟨⟨h2, h3⟩, h4⟩
    · simp only [hb, if_false]
      by_cases hp : n < a * a
      · simp only [hp, if_true]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨m, h1, h2, h3, h4⟩
          have : a * a ≤ m * m := Nat.mul_le_mul h1 h1
          omega
      · simp only [hp, if_false]
        rw [Bool.or_eq_true, ih a ((a+b)/2) n (by omega), ih ((a+b)/2) b n (by omega)]
        constructor
        · rintro (⟨m, h1, h2, h3, h4⟩ | ⟨m, h1, h2, h3, h4⟩)
          · exact ⟨m, h1, by omega, h3, h4⟩
          · exact ⟨m, by omega, h2, h3, h4⟩
        · rintro ⟨m, h1, h2, h3, h4⟩
          by_cases hm : m < (a + b) / 2
          · exact Or.inl ⟨m, h1, hm, h3, h4⟩
          · exact Or.inr ⟨m, by omega, h2, h3, h4⟩
def isPrimeB (n : ℕ) : Bool := (2 ≤ n) && !(dsF n 2 n n)
theorem isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ Nat.Prime n := by
  rw [Nat.prime_def_le_sqrt]
  unfold isPrimeB
  rw [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', ← Bool.not_eq_true]
  by_cases h2 : 2 ≤ n
  · rw [dsF_iff n 2 n n (by omega)]
    simp only [h2, true_and]
    constructor
    · intro hno m hm hms hdvd
      apply hno
      have hmn : m < n := by nlinarith [Nat.le_sqrt.mp hms]
      exact ⟨m, hm, hmn, Nat.le_sqrt.mp hms, hdvd⟩
    · rintro hall ⟨m, h1, h2', h3, h4⟩
      exact hall m h1 (Nat.le_sqrt.mpr h3) h4
  · constructor
    · rintro ⟨hc, _⟩; exact absurd hc h2
    · rintro ⟨hc, _⟩; exact absurd hc h2
def cntPF : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => if a < b ∧ isPrimeB a then 1 else 0
  | (f+1), a, b =>
    if b ≤ a + 1 then (if a < b ∧ isPrimeB a then 1 else 0)
    else let mid := (a + b) / 2; cntPF f a mid + cntPF f mid b
theorem cntPF_eq_card (f : ℕ) : ∀ a b, b - a ≤ f →
    cntPF f a b = ((Finset.Ico a b).filter (fun k => isPrimeB k)).card := by
  induction f with
  | zero =>
    intro a b hf
    rw [cntPF]
    rcases Nat.lt_or_ge a b with hab | hab
    · have hb : b = a + 1 := by omega
      subst hb; rw [Nat.Ico_succ_singleton]
      by_cases hp : isPrimeB a
      · rw [if_pos ⟨hab, hp⟩, Finset.filter_singleton, if_pos hp]; simp
      · rw [if_neg (by simp [hp]), Finset.filter_singleton, if_neg (by simp [hp])]; simp
    · rw [if_neg (by simp; omega)]
      have : Finset.Ico a b = ∅ := by rw [Finset.Ico_eq_empty]; omega
      rw [this]; simp
  | succ f ih =>
    intro a b hf
    rw [cntPF]
    by_cases hb : b ≤ a + 1
    · simp only [hb, if_true]
      rcases Nat.lt_or_ge a b with hab | hab
      · have hbe : b = a + 1 := by omega
        subst hbe; rw [Nat.Ico_succ_singleton]
        by_cases hp : isPrimeB a
        · rw [if_pos ⟨hab, hp⟩, Finset.filter_singleton, if_pos hp]; simp
        · rw [if_neg (by simp [hp]), Finset.filter_singleton, if_neg (by simp [hp])]; simp
      · rw [if_neg (by simp; omega)]
        have : Finset.Ico a b = ∅ := by rw [Finset.Ico_eq_empty]; omega
        rw [this]; simp
    · simp only [hb, if_false]
      rw [ih a ((a+b)/2) (by omega), ih ((a+b)/2) b (by omega),
          ← Finset.card_union_of_disjoint
            (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive a ((a+b)/2) b))]
      congr 1
      rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico] <;> omega
def cntP (a b : ℕ) : ℕ := cntPF (b - a) a b
theorem cntP_eq_card (a b : ℕ) :
    cntP a b = ((Finset.Ico a b).filter (fun k => isPrimeB k)).card :=
  cntPF_eq_card (b - a) a b (le_refl _)
theorem cntP_eq_primeCounting (m : ℕ) : cntP 0 (m + 1) = Nat.primeCounting m := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range,
      cntP_eq_card, Finset.range_eq_Ico]
  apply Finset.card_nbij' id id <;> intro x hx <;>
    simp_all [Finset.mem_filter, isPrimeB_iff]
end KS

/-- Bridge: `A262439 j` equals the kernel-reducible count `KS.cntP 0 (T_j + 1)`. -/
theorem A439_eq (j : ℕ) : A262439 j = KS.cntP 0 (j * (j + 1) / 2 + 2) := by
  unfold A262439
  rw [← KS.cntP_eq_primeCounting]

/-- `A262446` rewritten using the reducible count. -/
def A446B (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k =>
    (Ico (k + 1) n).sum fun m =>
      if KS.cntP 0 (n * (n + 1) / 2 + 2)
          = KS.cntP 0 (k * (k + 1) / 2 + 2) + KS.cntP 0 (m * (m + 1) / 2 + 2)
        then 1 else 0

theorem A446_eq (n : ℕ) : A262446 n = A446B n := by
  simp only [A262446, A446B, A439_eq]

set_option maxHeartbeats 0 in
/--
%C A262446 I have verified the conjecture for n up to 10^5. - _Zhi-Wei Sun_, Sep 27 2015
The mathematical statement verified up to $10^5$ is that the full conjecture holds for $3 < n \le 100000$.
-/
theorem A262446_conjecture_verified_upto_10e5 :
  ∀ n : ℕ, 3 < n ∧ n ≤ 100000 → A262446 n > 0 ∧ (A262446 n = 1 ↔ n ∈ A262446_unique_n_set) := by
  have key : ∀ n, n ≤ 100000 → 3 < n →
      A446B n > 0 ∧ (A446B n = 1 ↔ n ∈ A262446_unique_n_set) := by
    decide
  intro n hn
  rw [A446_eq]
  exact key n hn.2 hn.1
