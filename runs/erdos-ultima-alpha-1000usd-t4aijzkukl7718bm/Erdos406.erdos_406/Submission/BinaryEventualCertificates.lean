import Submission.BinaryCertificates

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
