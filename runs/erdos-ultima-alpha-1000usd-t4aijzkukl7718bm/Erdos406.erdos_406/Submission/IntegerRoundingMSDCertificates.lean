import Submission.IntegerRoundingBarrierCertificates

/-! Finite carry checks for integer rounding barriers read most-significant
ternary digit first. No separating integer-weight table is supplied. -/
namespace Erdos406IntegerRounding
open Erdos406AffineCertificate Erdos406GroupedCertificate Erdos406AffinePotential

lemma intWeightFrom_append_singleton {σ : Type*} (D : DFA ℕ σ)
    (w : σ → ℕ → ℤ) (s : σ) (u : List ℕ) (d : ℕ) :
    intWeightFrom D w s (u++[d]) = intWeightFrom D w s u + w (D.evalFrom s u) d := by
  induction u generalizing s with
  | nil => simp [intWeightFrom]
  | cons a u ih => simp only [List.cons_append,intWeightFrom,DFA.evalFrom_cons,ih]; ring

def intWeightNat {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℤ) (n : ℕ) : ℤ :=
  intWeightFrom D w D.start (Nat.digits 3 n).reverse

@[simp] lemma intWeightNat_zero {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℤ) :
    intWeightNat D w 0 = 0 := by simp [intWeightNat,intWeightFrom]

lemma intWeightNat_pos {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℤ)
    {n : ℕ} (hn : 0 < n) :
    intWeightNat D w n = intWeightNat D w (n/3) + w (evalNat 3 D (n/3)) (n%3) := by
  rw [intWeightNat,Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn,
    List.reverse_cons,intWeightFrom_append_singleton]
  rfl

lemma cast_intWeightNat {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℤ) (n : ℕ) :
    (intWeightNat D w n : ℝ) = weightNat D (fun s d => (w s d : ℝ)) n :=
  cast_intWeightFrom D w D.start (Nat.digits 3 n).reverse

structure MSDCore (σ : Type*) where
  D : DFA ℕ σ
  w : σ → ℕ → ℤ
  p : ℤ
  q : ℤ
  p_pos : 0 < p
  q_pos : 0 < q
  R : σ → σ → ℕ → Prop
  H : σ → σ → ℕ → ℤ
  relation_start : ∀ c, c < 4 → R D.start (evalNat 3 D c) c
  relation_step : ∀ s t c d e c', c < 4 → d < 3 → e < 3 → c' < 4 →
    4*d+c' = 3*c+e → R s t c → R (D.step s d) (D.step t e) c'
  lower_start : ∀ c, c < 4 → H D.start (evalNat 3 D c) c ≤ q*intWeightNat D w c
  lower_step : ∀ s t c d e c', c < 4 → d < 3 → e < 3 → c' < 4 →
    4*d+c' = 3*c+e → R s t c →
    H (D.step s d) (D.step t e) c' ≤ H s t c + q*w t e - p*w s d
  lower_finish : ∀ s t, R s t 1 → 1-p ≤ H s t 1

namespace MSDCore
variable {σ : Type*} (C : MSDCore σ)

lemma relation_potential (n c : ℕ) (hc : c < 4) :
    C.R (evalNat 3 C.D n) (evalNat 3 C.D (4*n+c)) c ∧
    C.H (evalNat 3 C.D n) (evalNat 3 C.D (4*n+c)) c ≤
      C.q*intWeightNat C.D C.w (4*n+c) - C.p*intWeightNat C.D C.w n := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [mul_zero,zero_add,evalNat_zero,intWeightNat_zero,sub_zero] using
        And.intro (C.relation_start c hc) (C.lower_start c hc)
    · have hnpos := Nat.pos_of_ne_zero hn
      let d := n%3
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
      rw [evalNat_pos 3 C.D (by decide) hnpos,evalNat_pos 3 C.D (by decide) hout,hq,hm,
        intWeightNat_pos C.D C.w hnpos,intWeightNat_pos C.D C.w hout,hq,hm]
      refine ⟨hr, ?_⟩
      dsimp only [d,cp,e] at hi hp ⊢
      nlinarith [hi.2]

lemma rounding_lower (n : ℕ) :
    C.p*intWeightNat C.D C.w n-C.p+1 ≤ C.q*intWeightNat C.D C.w (4*n+1) := by
  have hh := C.relation_potential n 1 (by decide)
  have hf := C.lower_finish _ _ hh.1
  linarith

end MSDCore

/-- A finite integral carry witness would prove the exact conjecture.
The existence of such a witness is not asserted here. -/
theorem msd_integer_rounding_criterion {σ : Type*} (C : MSDCore σ)
    (U : GoodBound C.D (fun s d => (C.w s d : ℝ)))
    (hc : U.c = 0) (hB : U.B = 0) (E : ℕ)
    (hseed : 0 < intWeightNat C.D C.w (orbit 4 1 E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply integer_rounding_criterion (intWeightNat C.D C.w) C.p C.q E
    C.p_pos C.q_pos C.rounding_lower ?_ hseed
  intro n hn
  have hh := U.good_bound n hn
  rw [hc,hB,zero_mul,zero_add,← cast_intWeightNat] at hh
  exact_mod_cast hh

#print axioms MSDCore.rounding_lower
#print axioms msd_integer_rounding_criterion
end Erdos406IntegerRounding
