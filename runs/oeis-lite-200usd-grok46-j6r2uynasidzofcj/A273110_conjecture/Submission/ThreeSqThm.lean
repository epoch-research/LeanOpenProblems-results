import FormalConjectures.Util.ProblemImports
import Submission.HilbertConic
import Submission.Dev

open scoped NumberTheorySymbols
open Nat Int

/-! Three-square theorem via Dirichlet + Hilbert symbols + Davenport–Cassels. -/

lemma exists_jacobi_eq_neg {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ a : ℕ, 0 < a ∧ a < p ∧ jacobiSym a p = -1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar
  have hx0 : x ≠ 0 := fun h => hx (h ▸ ⟨0, by simp⟩)
  refine ⟨x.val, ZMod.val_pos.mpr hx0, ZMod.val_lt x, ?_⟩
  have : ¬ IsSquare ((x.val : ℤ) : ZMod p) := by
    rw [ZMod.natCast_zmod_val]
    exact hx
  exact (ZMod.nonsquare_iff_jacobiSym_eq_neg_one (a := (x.val : ℤ))).mp this

lemma exists_jacobi_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) :
    ∃ a : ℕ, 0 < a ∧ a < p ∧ jacobiSym a p = ε := by
  rcases hε with rfl | rfl
  · refine ⟨1, by decide, Fact.out.one_lt, jacobiSym.one_left p⟩
  · exact exists_jacobi_eq_neg hp2

lemma ModEq.gcd_eq' {a b n : ℕ} (h : a ≡ b [MOD n]) : a.gcd n = b.gcd n := by
  rw [Nat.gcd_rec a n, Nat.gcd_rec b n, h]

lemma ModEq.coprime_iff' {a b n : ℕ} (h : a ≡ b [MOD n]) :
    a.Coprime n ↔ b.Coprime n := by
  simp [Nat.Coprime, ModEq.gcd_eq' h]

lemma odd_of_mul_odd_left {a b : ℕ} (h : Odd (a * b)) : Odd b := by
  rw [Nat.odd_mul] at h
  exact h.2

lemma exists_mod_odd (n0 : ℕ) (target : ℕ → ℤ)
    (hn0 : 0 < n0) (hodd : Odd n0) (hsf : Squarefree n0)
    (ht : ∀ q, q.Prime → q ∣ n0 → target q = 1 ∨ target q = -1) :
    ∃ a : ℕ, a.Coprime n0 ∧
      ∀ q, q.Prime → q ∣ n0 → jacobiSym a q = target q := by
  induction n0 using Nat.strong_induction_on with
  | h n0 ih =>
    rcases eq_or_ne n0 1 with rfl | hn1
    · refine ⟨1, by decide, ?_⟩
      intro q hq hqd
      have : q = 1 := Nat.eq_one_of_dvd_one hqd
      exact absurd this hq.ne_one
    obtain ⟨q, hq, hqd⟩ := n0.exists_prime_and_dvd hn1
    haveI : Fact q.Prime := ⟨hq⟩
    have hq2 : q ≠ 2 := by
      intro h2
      subst h2
      have : Even n0 := (even_iff_two_dvd).2 hqd
      exact Nat.not_even_iff_odd.mpr hodd this
    obtain ⟨m, hm⟩ := hqd
    have hmpos : 0 < m :=
      Nat.pos_of_ne_zero fun hm0 => by
        subst hm0
        simp at hm
        exact hn0.ne' hm
    have hq_ndvd : ¬ q ∣ m := by
      intro hqm
      have : q * q ∣ n0 := by
        rw [hm]; exact mul_dvd_mul_left q hqm
      exact (squarefree_iff_prime_squarefree.mp hsf) q hq this
    have hcopqm : q.Coprime m := hq.coprime_iff_not_dvd.mpr hq_ndvd
    have hsfm : Squarefree m := by
      have : m ∣ n0 := ⟨q, by rw [hm, mul_comm]⟩
      exact hsf.squarefree_of_dvd this
    have hmodd : Odd m := by
      have : Odd (q * m) := by rwa [← hm]
      exact odd_of_mul_odd_left this
    have hmlt : m < n0 := by
      rw [hm]
      exact (Nat.lt_mul_iff_one_lt_left hmpos).mpr hq.one_lt
    obtain ⟨a1, ha1cop, ha1⟩ :=
      ih m hmlt hmpos hmodd hsfm fun q' hq' hqd' =>
        ht q' hq' (hqd'.trans ⟨q, by rw [hm, mul_comm]⟩)
    obtain ⟨r, hrpos, hrlt, hrjac⟩ :=
      exists_jacobi_eq hq2 (ht q hq (by rw [hm]; exact dvd_mul_right _ _))
    obtain ⟨a, haq, ham⟩ := Nat.chineseRemainder hcopqm r a1
    refine ⟨a, ?_, ?_⟩
    · have hacopm : a.Coprime m := (ModEq.coprime_iff' ham).mpr ha1cop
      have hrcop : r.Coprime q :=
        (hq.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hrpos hrlt)
      have hacopq : a.Coprime q := (ModEq.coprime_iff' haq).mpr hrcop
      have : a.Coprime (q * m) :=
        Nat.coprime_mul_iff_right.mpr ⟨hacopq, hacopm⟩
      rwa [← hm]
    · intro q' hq' hqd'
      haveI : Fact q'.Prime := ⟨hq'⟩
      by_cases hqq : q' = q
      · subst hqq
        have : a ≡ r [MOD q] := haq
        have : (a : ℤ) % q = (r : ℤ) % q := by
          exact_mod_cast this
        rw [jacobiSym.mod_left', hrjac]
        exact this
      · have hqd'm : q' ∣ m := by
          have : q' ∣ q * m := by rwa [← hm]
          exact hq'.dvd_mul.mp this |>.resolve_left fun h =>
            hqq (hq.dvd_iff_eq (by exact hq'.ne_one) |>.mp h).symm
        have h1 : jacobiSym a1 q' = target q' := ha1 q' hq' hqd'm
        have : a ≡ a1 [MOD m] := ham
        have : a ≡ a1 [MOD q'] := this.of_dvd hqd'm
        have : (a : ℤ) % q' = (a1 : ℤ) % q' := by exact_mod_cast this
        rw [jacobiSym.mod_left' this, h1]
