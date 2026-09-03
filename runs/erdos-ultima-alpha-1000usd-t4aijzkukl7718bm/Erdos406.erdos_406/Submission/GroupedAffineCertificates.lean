import Submission.AffineCertificates
import Submission.SparseTriple

/-! Soundness of affine-orbit certificates in bases 3^h. Grouping ternary
digits changes the finite-state representation, not the conjecture.
No certificate witness is asserted in this file. -/

namespace Erdos406GroupedCertificate
open Erdos406AffineCertificate

abbrev Good (n : ℕ) : Prop := Nat.digits 3 n ⊆ [0, 1]
abbrev GoodBlock (h d : ℕ) : Prop := d < 3 ^ h ∧ Good d

lemma good_grouped_digits (h : ℕ) (hh : 0 < h) {n : ℕ} (hn : Good n) :
    ∀ d ∈ Nat.digits (3 ^ h) n, GoodBlock h d := by
  have hb : 2 ≤ 3 ^ h := by
    have hp := one_lt_pow₀ (by decide : 1 < (3 : ℕ)) (Nat.ne_of_gt hh)
    omega
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz]
    rw [Nat.digits_of_two_le_of_pos hb (Nat.pos_of_ne_zero hz)]
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨Nat.mod_lt n (by positivity), Erdos406SparseTriple.good_mod_pow hn h⟩
    · exact ih (n / 3 ^ h) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) hb)
        (Erdos406SparseTriple.good_div_pow hn h) d hd

lemma goodBlock_two_iff (d : ℕ) : GoodBlock 2 d ↔ d ∈ ([0, 1, 3, 4] : List ℕ) := by
  by_cases hd : d < 9
  · interval_cases d <;> norm_num [GoodBlock, Good, Nat.digits_of_two_le_of_pos]
  · constructor
    · intro h; exact False.elim (hd h.1)
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      omega

lemma goodBlock_three_iff (d : ℕ) :
    GoodBlock 3 d ↔ d ∈ ([0, 1, 3, 4, 9, 10, 12, 13] : List ℕ) := by
  by_cases hd : d < 27
  · interval_cases d <;> norm_num [GoodBlock, Good, Nat.digits_of_two_le_of_pos]
  · constructor
    · intro h; exact False.elim (hd h.1)
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      omega

def evalNat {σ : Type*} (b : ℕ) (D : DFA ℕ σ) (n : ℕ) : σ :=
  D.eval (Nat.digits b n).reverse

lemma evalNat_zero {σ : Type*} (b : ℕ) (D : DFA ℕ σ) : evalNat b D 0 = D.start := by
  simp [evalNat]

lemma evalNat_pos {σ : Type*} (b : ℕ) (D : DFA ℕ σ) (hb : 2 ≤ b)
    {n : ℕ} (hn : 0 < n) : evalNat b D n = D.step (evalNat b D (n / b)) (n % b) := by
  rw [evalNat, Nat.digits_of_two_le_of_pos hb hn,
    List.reverse_cons, DFA.eval_append_singleton]
  rfl

lemma affine_div_mod (b q n c : ℕ) (hb : 0 < b) :
    (q * n + c) / b = q * (n / b) + (q * (n % b) + c) / b ∧
    (q * n + c) % b = (q * (n % b) + c) % b := by
  have he : q * n + c = q * (n % b) + c + b * (q * (n / b)) := by
    calc
      _ = q * (n % b + b * (n / b)) + c := by rw [Nat.mod_add_div]
      _ = _ := by ring
  rw [he, Nat.add_mul_div_left _ _ hb, Nat.add_mul_mod_self_left]
  exact ⟨by omega, rfl⟩

structure Core (σ : Type*) where
  D : DFA ℕ σ
  base : ℕ
  base_ge_two : 2 ≤ base
  q : ℕ
  c : ℕ
  q_pos : 0 < q
  c_lt_q : c < q
  R : σ → σ → ℕ → Prop
  relation_start : ∀ c', c' < q → R D.start (evalNat base D c') c'
  relation_step : ∀ s t c' d e c'', c' < q → d < base → e < base →
    c'' < q → q * d + c'' = base * c' + e → R s t c' →
    R (D.step s d) (D.step t e) c''
  relation_finish : ∀ s t, R s t c → s ∈ D.accept → t ∈ D.accept
  seed : D.start ∈ D.accept

namespace Core
variable {σ : Type*} (C : Core σ)

lemma relation (n c : ℕ) (hc : c < C.q) :
    C.R (evalNat C.base C.D n) (evalNat C.base C.D (C.q * n + c)) c := by
  have hb : 0 < C.base := by have := C.base_ge_two; omega
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [mul_zero, zero_add, evalNat_zero] using C.relation_start c hc
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let d := n % C.base
      let cp := (C.q * d + c) / C.base
      let e := (C.q * d + c) % C.base
      have hd : d < C.base := Nat.mod_lt n hb
      have he : e < C.base := Nat.mod_lt _ hb
      have hcp : cp < C.q := by
        apply (Nat.div_lt_iff_lt_mul hb).mpr
        nlinarith
      have hrel := ih (n / C.base) (Nat.div_lt_self hnpos C.base_ge_two) cp hcp
      have hstep := C.relation_step _ _ cp d e c hcp hd he hc
        (by dsimp only [cp, e]; have := Nat.mod_add_div (C.q * d + c) C.base; omega) hrel
      obtain ⟨hq, hm⟩ := affine_div_mod C.base C.q n c hb
      have hpos : 0 < C.q * n + c := by have := C.q_pos; positivity
      rw [evalNat_pos C.base C.D C.base_ge_two hnpos,
        evalNat_pos C.base C.D C.base_ge_two hpos, hq, hm]
      exact hstep

lemma affine_closed {n : ℕ} (hn : evalNat C.base C.D n ∈ C.D.accept) :
    evalNat C.base C.D (C.q * n + C.c) ∈ C.D.accept :=
  C.relation_finish _ _ (C.relation n C.c C.c_lt_q) hn

lemma accepts_orbit (t : ℕ) : evalNat C.base C.D (orbit C.q C.c t) ∈ C.D.accept := by
  induction t with
  | zero => simpa only [orbit_zero, evalNat_zero] using C.seed
  | succ t ih => exact C.affine_closed ih

end Core

lemma reachable_word {σ : Type*} (D : DFA ℕ σ) (P : ℕ → Prop) (G : σ → Prop)
    (hs : ∀ s d, P d → G s → G (D.step s d))
    (w : List ℕ) (hw : ∀ d ∈ w, P d) (s : σ) (hg : G s) :
    G (D.evalFrom s w) := by
  induction w generalizing s with
  | nil => simpa using hg
  | cons d w ih =>
    exact ih (fun e he => hw e (List.mem_cons_of_mem _ he)) _
      (hs s d (hw d (List.mem_cons_self ..)) hg)

lemma coaccessible_word {σ : Type*} (D : DFA ℕ σ) (P : ℕ → Prop) (K : σ → Prop)
    (ha : ∀ s, s ∈ D.accept → K s)
    (hs : ∀ s d, P d → K (D.step s d) → K s)
    (w : List ℕ) (hw : ∀ d ∈ w, P d) (s : σ)
    (hacc : D.evalFrom s w ∈ D.accept) : K s := by
  induction w generalizing s with
  | nil => exact ha s hacc
  | cons d w ih =>
    exact hs s d (hw d (List.mem_cons_self ..))
      (ih (fun e he => hw e (List.mem_cons_of_mem _ he)) _ hacc)

lemma rank_word_bound {σ : Type*} (D : DFA ℕ σ) (P : ℕ → Prop)
    (G K : σ → Prop) (rank : σ → ℕ)
    (hgstep : ∀ s d, P d → G s → G (D.step s d))
    (hkacc : ∀ s, s ∈ D.accept → K s)
    (hkstep : ∀ s d, P d → K (D.step s d) → K s)
    (hrstep : ∀ s d, P d → G s → K (D.step s d) → rank (D.step s d) < rank s)
    (w : List ℕ) (hw : ∀ d ∈ w, P d) (s : σ) (hg : G s)
    (ha : D.evalFrom s w ∈ D.accept) : w.length ≤ rank s := by
  induction w generalizing s with
  | nil => simp
  | cons d w ih =>
    have hd := hw d (List.mem_cons_self ..)
    have hw' : ∀ e ∈ w, P e := fun e he => hw e (List.mem_cons_of_mem _ he)
    have hb := ih hw' (D.step s d) (hgstep s d hd hg) ha
    have hk := coaccessible_word D P K hkacc hkstep w hw' (D.step s d) ha
    have hr := hrstep s d hd hg hk
    simpa only [List.length_cons] using (by omega : w.length + 1 ≤ rank s)

lemma digit_length_bound {σ : Type*} (b : ℕ) (D : DFA ℕ σ) (P : ℕ → Prop)
    (G K : σ → Prop) (rank : σ → ℕ) (bound : ℕ)
    (hgstart : ∀ d, P d → d ≠ 0 → G (D.step D.start d))
    (hgstep : ∀ s d, P d → G s → G (D.step s d))
    (hkacc : ∀ s, s ∈ D.accept → K s)
    (hkstep : ∀ s d, P d → K (D.step s d) → K s)
    (hrstep : ∀ s d, P d → G s → K (D.step s d) → rank (D.step s d) < rank s)
    (hrbound : ∀ s, rank s ≤ bound)
    {n : ℕ} (hn : 0 < n) (hd : ∀ d ∈ Nat.digits b n, P d)
    (ha : evalNat b D n ∈ D.accept) : (Nat.digits b n).length ≤ bound + 1 := by
  have hne : Nat.digits b n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt hn)
  let a := (Nat.digits b n).getLast hne
  have hPa : P a := hd _ (List.getLast_mem hne)
  have ha0 : a ≠ 0 := Nat.getLast_digit_ne_zero b (ne_of_gt hn)
  have he := List.dropLast_append_getLast hne
  have hre : (Nat.digits b n).reverse = a :: (Nat.digits b n).dropLast.reverse := by
    conv_lhs => rw [← he, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append]
    rfl
  have hw : ∀ d ∈ (Nat.digits b n).dropLast.reverse, P d := by
    intro d hd'
    exact hd _ (List.mem_of_mem_dropLast (List.mem_reverse.mp hd'))
  have ha' : D.evalFrom (D.step D.start a) (Nat.digits b n).dropLast.reverse ∈ D.accept := by
    simpa only [evalNat, hre, DFA.eval, DFA.evalFrom_cons] using ha
  have hb := rank_word_bound D P G K rank hgstep hkacc hkstep hrstep
    (Nat.digits b n).dropLast.reverse hw _ (hgstart a hPa ha0) ha'
  have hl := congrArg List.length he
  simp only [List.length_append, List.length_singleton] at hl
  simp only [List.length_reverse] at hb
  have hbound := hrbound (D.step D.start a)
  omega

/-- A verified grouped-digit affine certificate would imply the required
finiteness for this orbit. This theorem supplies no such certificate. -/
theorem finite_language_criterion {σ : Type*} (C : Core σ) (h : ℕ) (hh : 0 < h)
    (hbase : C.base = 3 ^ h)
    (G K : σ → Prop) (rank : σ → ℕ) (bound : ℕ)
    (hgstart : ∀ d, GoodBlock h d → d ≠ 0 → G (C.D.step C.D.start d))
    (hgstep : ∀ s d, GoodBlock h d → G s → G (C.D.step s d))
    (hkacc : ∀ s, s ∈ C.D.accept → K s)
    (hkstep : ∀ s d, GoodBlock h d → K (C.D.step s d) → K s)
    (hrstep : ∀ s d, GoodBlock h d → G s → K (C.D.step s d) → rank (C.D.step s d) < rank s)
    (hrbound : ∀ s, rank s ≤ bound) :
    {n : ℕ | (∃ t, n = orbit C.q C.c t) ∧ Good n}.Finite := by
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨C.base ^ (bound + 1), ?_⟩
  rintro n ⟨⟨t, rfl⟩, hd⟩
  by_cases hn : orbit C.q C.c t = 0
  · simp [hn]
  · have ha := C.accepts_orbit t
    have hdigits : ∀ d ∈ Nat.digits C.base (orbit C.q C.c t), GoodBlock h d := by
      rw [hbase]
      exact good_grouped_digits h hh hd
    have hl := digit_length_bound C.base C.D (GoodBlock h) G K rank bound
      hgstart hgstep hkacc hkstep hrstep hrbound (Nat.pos_of_ne_zero hn) hdigits ha
    have hlt := Nat.lt_base_pow_length_digits (b := C.base) (m := orbit C.q C.c t) C.base_ge_two
    exact (Nat.le_of_lt hlt).trans (Nat.pow_le_pow_right (by have := C.base_ge_two; omega) hl)

#print axioms good_grouped_digits
#print axioms finite_language_criterion
end Erdos406GroupedCertificate
