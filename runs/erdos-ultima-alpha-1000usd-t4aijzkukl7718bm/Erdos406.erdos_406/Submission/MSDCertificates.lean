import FormalConjecturesUtil

/-! Soundness of most-significant-digit ternary certificates with strided
multiplication and either eventual exclusion or a finite good-word language.
No certificate witness is asserted. -/

namespace Erdos406MSDCertificate

def evalNat {σ : Type*} (D : DFA ℕ σ) (n : ℕ) : σ :=
  D.eval (Nat.digits 3 n).reverse

lemma evalNat_zero {σ : Type*} (D : DFA ℕ σ) : evalNat D 0 = D.start := by
  simp [evalNat]

lemma evalNat_pos {σ : Type*} (D : DFA ℕ σ) {n : ℕ} (hn : 0 < n) :
    evalNat D n = D.step (evalNat D (n / 3)) (n % 3) := by
  rw [evalNat, Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn,
    List.reverse_cons, DFA.eval_append_singleton]
  rfl

lemma affine_div_mod (q n c : ℕ) :
    (q * n + c) / 3 = q * (n / 3) + (q * (n % 3) + c) / 3 ∧
    (q * n + c) % 3 = (q * (n % 3) + c) % 3 := by
  have he : q * n + c = q * (n % 3) + c + 3 * (q * (n / 3)) := by
    calc
      _ = q * (n % 3 + 3 * (n / 3)) + c := by rw [Nat.mod_add_div]
      _ = _ := by ring
  rw [he, Nat.add_mul_div_left _ _ (by decide), Nat.add_mul_mod_self_left]
  exact ⟨by omega, rfl⟩

structure Core (σ : Type*) where
  D : DFA ℕ σ
  stride : ℕ
  stride_pos : 0 < stride
  cutoff : ℕ
  R : σ → σ → ℕ → Prop
  relation_start : ∀ c, c < 4 ^ stride → R D.start (evalNat D c) c
  relation_step : ∀ s t c d e c', c < 4 ^ stride → d < 3 → e < 3 →
    c' < 4 ^ stride → 4 ^ stride * d + c' = 3 * c + e → R s t c →
    R (D.step s d) (D.step t e) c'
  relation_finish : ∀ s t, R s t 0 → s ∈ D.accept → t ∈ D.accept
  seeds : ∀ r, r < stride → evalNat D (4 ^ (cutoff + r)) ∈ D.accept

namespace Core
variable {σ : Type*} (C : Core σ)

lemma relation (n c : ℕ) (hc : c < 4 ^ C.stride) :
    C.R (evalNat C.D n) (evalNat C.D (4 ^ C.stride * n + c)) c := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [mul_zero, zero_add, evalNat_zero] using C.relation_start c hc
    · have hnpos : 0 < n := by omega
      let d := n % 3
      let cp := (4 ^ C.stride * d + c) / 3
      let e := (4 ^ C.stride * d + c) % 3
      have hd : d < 3 := Nat.mod_lt n (by decide)
      have he : e < 3 := Nat.mod_lt _ (by decide)
      have hcp : cp < 4 ^ C.stride := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr
        nlinarith
      have hrel := ih (n / 3) (Nat.div_lt_self hnpos (by decide)) cp hcp
      have hstep := C.relation_step _ _ cp d e c hcp hd he hc
        (by dsimp [cp, e]; omega) hrel
      obtain ⟨hq, hm⟩ := affine_div_mod (4 ^ C.stride) n c
      have hpos : 0 < 4 ^ C.stride * n + c := by positivity
      rw [evalNat_pos C.D hnpos, evalNat_pos C.D hpos, hq, hm]
      exact hstep

lemma mul_closed {n : ℕ} (hn : evalNat C.D n ∈ C.D.accept) :
    evalNat C.D (4 ^ C.stride * n) ∈ C.D.accept := by
  have hh := C.relation_finish _ _ (C.relation n 0 (by positivity)) hn
  simpa only [add_zero] using hh

lemma iterate_closed {n : ℕ} (hn : evalNat C.D n ∈ C.D.accept) (t : ℕ) :
    evalNat C.D ((4 ^ C.stride) ^ t * n) ∈ C.D.accept := by
  induction t with
  | zero => simpa using hn
  | succ t ih => simpa only [pow_succ', mul_assoc] using C.mul_closed ih

lemma accepts_tail {m : ℕ} (hm : C.cutoff ≤ m) :
    evalNat C.D (4 ^ m) ∈ C.D.accept := by
  have hs := C.seeds ((m - C.cutoff) % C.stride)
    (Nat.mod_lt _ C.stride_pos)
  have hh := C.iterate_closed hs ((m - C.cutoff) / C.stride)
  have he : C.stride * ((m - C.cutoff) / C.stride) +
      (C.cutoff + (m - C.cutoff) % C.stride) = m := by
    have hdiv := Nat.mod_add_div (m - C.cutoff) C.stride
    omega
  simpa only [← pow_mul, ← pow_add, he] using hh
end Core

lemma even_exponent {k : ℕ} (h : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) : Even k := by
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) (by positivity : 0 < 2 ^ k)] at h
  have hm : 2 ^ k % 3 = 0 ∨ 2 ^ k % 3 = 1 := by
    simpa using h (List.mem_cons_self ..)
  rcases Nat.even_or_odd k with he | ⟨j, rfl⟩
  · exact he
  · simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at hm

lemma binary_reachable {σ : Type*} (D : DFA ℕ σ) (G : σ → Prop)
    (hs : ∀ s d, d < 2 → G s → G (D.step s d))
    (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (s : σ) (hg : G s) :
    G (D.evalFrom s w) := by
  induction w generalizing s with
  | nil => simpa using hg
  | cons d w ih =>
    exact ih (fun e he => hw e (by simp [he])) _ (hs s d (hw d (by simp)) hg)

lemma binary_coaccessible {σ : Type*} (D : DFA ℕ σ) (K : σ → Prop)
    (ha : ∀ s, s ∈ D.accept → K s)
    (hs : ∀ s d, d < 2 → K (D.step s d) → K s)
    (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (s : σ)
    (hacc : D.evalFrom s w ∈ D.accept) : K s := by
  induction w generalizing s with
  | nil => exact ha s hacc
  | cons d w ih =>
    exact hs s d (hw d (by simp)) (ih (fun e he => hw e (by simp [he])) _ hacc)

lemma binary_rank_bound {σ : Type*} (D : DFA ℕ σ) (G K : σ → Prop) (rank : σ → ℕ)
    (hgstep : ∀ s d, d < 2 → G s → G (D.step s d))
    (hkacc : ∀ s, s ∈ D.accept → K s)
    (hkstep : ∀ s d, d < 2 → K (D.step s d) → K s)
    (hrstep : ∀ s d, d < 2 → G s → K (D.step s d) → rank (D.step s d) < rank s)
    (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (s : σ) (hg : G s)
    (ha : D.evalFrom s w ∈ D.accept) : w.length ≤ rank s := by
  induction w generalizing s with
  | nil => simp
  | cons d w ih =>
    have hd := hw d (by simp)
    have hw' : ∀ e ∈ w, e < 2 := fun e he => hw e (by simp [he])
    have hb := ih hw' (D.step s d) (hgstep s d hd hg) ha
    have hk := binary_coaccessible D K hkacc hkstep w hw' (D.step s d) ha
    have hr := hrstep s d hd hg hk
    simpa only [List.length_cons] using (by omega : w.length + 1 ≤ rank s)

lemma good_length_bound {σ : Type*} (D : DFA ℕ σ)
    (G K : σ → Prop) (rank : σ → ℕ) (hgstart : G (D.step D.start 1))
    (hgstep : ∀ s d, d < 2 → G s → G (D.step s d))
    (hkacc : ∀ s, s ∈ D.accept → K s)
    (hkstep : ∀ s d, d < 2 → K (D.step s d) → K s)
    (hrstep : ∀ s d, d < 2 → G s → K (D.step s d) → rank (D.step s d) < rank s)
    {n : ℕ} (hn : 0 < n) (hd : Nat.digits 3 n ⊆ [0, 1])
    (ha : evalNat D n ∈ D.accept) :
    (Nat.digits 3 n).length ≤ rank (D.step D.start 1) + 1 := by
  have hne : Nat.digits 3 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt hn)
  have hlast : (Nat.digits 3 n).getLast hne = 1 := by
    have hm := hd (List.getLast_mem hne)
    have hz := Nat.getLast_digit_ne_zero 3 (ne_of_gt hn)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he := List.dropLast_append_getLast hne
  rw [hlast] at he
  have hre : (Nat.digits 3 n).reverse = 1 :: (Nat.digits 3 n).dropLast.reverse := by
    rw [← he, List.reverse_append]
    simp
  have hw : ∀ d ∈ (Nat.digits 3 n).dropLast.reverse, d < 2 := by
    intro d hd'
    have hh := hd (List.mem_of_mem_dropLast (List.mem_reverse.mp hd'))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    omega
  have ha' : D.evalFrom (D.step D.start 1) (Nat.digits 3 n).dropLast.reverse ∈ D.accept := by
    simpa only [evalNat, hre, DFA.eval, DFA.evalFrom_cons] using ha
  have hb := binary_rank_bound D G K rank hgstep hkacc hkstep hrstep
    (Nat.digits 3 n).dropLast.reverse hw _ hgstart ha'
  have hl := congrArg List.length he
  simp only [List.length_append, List.length_singleton] at hl
  simp only [List.length_reverse] at hb
  omega

/-- Sufficient finite-language certificate criterion. This does not supply a
Core or the required reachability predicates and rank. -/
theorem finite_language_criterion {σ : Type*} (C : Core σ)
    (G K : σ → Prop) (rank : σ → ℕ) (hgstart : G (C.D.step C.D.start 1))
    (hgstep : ∀ s d, d < 2 → G s → G (C.D.step s d))
    (hkacc : ∀ s, s ∈ C.D.accept → K s)
    (hkstep : ∀ s d, d < 2 → K (C.D.step s d) → K s)
    (hrstep : ∀ s d, d < 2 → G s → K (C.D.step s d) → rank (C.D.step s d) < rank s) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨max (4 ^ C.cutoff) (3 ^ (rank (C.D.step C.D.start 1) + 1)), ?_⟩
  rintro n ⟨⟨k, rfl⟩, hd⟩
  obtain ⟨m, hm⟩ := even_exponent hd
  have he : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    rfl
  rw [he] at hd ⊢
  by_cases hmC : m < C.cutoff
  · exact (Nat.pow_le_pow_right (by decide) (by omega)).trans (le_max_left _ _)
  · have ha := C.accepts_tail (by omega : C.cutoff ≤ m)
    have hl := good_length_bound C.D G K rank hgstart hgstep hkacc hkstep hrstep
      (by positivity : 0 < 4 ^ m) hd ha
    have hlt := Nat.lt_base_pow_length_digits (b := 3) (m := 4 ^ m) (by decide)
    exact ((Nat.le_of_lt hlt).trans (Nat.pow_le_pow_right (by decide) hl)).trans (le_max_right _ _)

/-- Sufficient eventual-exclusion criterion, with all exponent classes
covered by the strided seeds of Core. No witness is asserted. -/
theorem eventual_criterion {σ : Type*} (C : Core σ) (G : σ → Prop)
    (hstart : G C.D.start)
    (hstep : ∀ s d, d < 2 → G s → G (C.D.step s d))
    (hreject : ∀ s, G s → s ∉ C.D.accept) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨4 ^ C.cutoff, ?_⟩
  rintro n ⟨⟨k, rfl⟩, hd⟩
  obtain ⟨m, hm⟩ := even_exponent hd
  have he : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    rfl
  rw [he] at hd ⊢
  by_cases hmC : m < C.cutoff
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · have ha := C.accepts_tail (by omega : C.cutoff ≤ m)
    have hw : ∀ d ∈ (Nat.digits 3 (4 ^ m)).reverse, d < 2 := by
      intro d hd'
      have hh := hd (List.mem_reverse.mp hd')
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      omega
    exact False.elim (hreject _ (binary_reachable C.D G hstep _ hw _ hstart) ha)

#print axioms finite_language_criterion
#print axioms eventual_criterion
end Erdos406MSDCertificate
