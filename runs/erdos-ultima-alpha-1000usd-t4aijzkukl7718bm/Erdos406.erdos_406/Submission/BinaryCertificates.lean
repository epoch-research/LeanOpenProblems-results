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
