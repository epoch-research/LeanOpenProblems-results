import Submission.MSDCertificates

/-! A reduction of the conjecture to two affine orbits, and soundness of
finite-language certificates for those orbits. No certificate is asserted. -/

namespace Erdos406AffineCertificate
open Erdos406MSDCertificate

def orbit (q c : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => q * orbit q c t + c

@[simp] lemma orbit_zero (q c : ℕ) : orbit q c 0 = 0 := rfl
@[simp] lemma orbit_succ (q c t : ℕ) : orbit q c (t + 1) = q * orbit q c t + c := rfl

lemma orbit_seven_identity (t : ℕ) : 9 * orbit 64 7 t + 1 = 4 ^ (3 * t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, pow_add, orbit_succ]
    norm_num
    nlinarith

lemma orbit_twenty_eight_identity (t : ℕ) :
    9 * orbit 64 28 t + 4 = 4 ^ (3 * t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he : 3 * (t + 1) + 1 = (3 * t + 1) + 3 := by omega
    rw [he, pow_add, orbit_succ]
    norm_num
    nlinarith

lemma good_div_three {n : ℕ} (h : Nat.digits 3 n ⊆ [0, 1]) :
    Nat.digits 3 (n / 3) ⊆ [0, 1] := by
  by_cases hn : n = 0
  · simp [hn]
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) (by omega : 0 < n)] at h
  exact fun d hd => h (List.mem_cons_of_mem _ hd)

lemma good_div_nine {n : ℕ} (h : Nat.digits 3 n ⊆ [0, 1]) :
    Nat.digits 3 (n / 9) ⊆ [0, 1] := by
  simpa only [Nat.div_div_eq_div_mul] using good_div_three (good_div_three h)

lemma good_unit_mod_three {n : ℕ} (hn : 0 < n) (h : Nat.digits 3 n ⊆ [0, 1]) :
    n % 3 = 0 ∨ n % 3 = 1 := by
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn] at h
  simpa using h (List.mem_cons_self ..)

lemma good_four_exponent_mod_three {m : ℕ} (h : Nat.digits 3 (4 ^ m) ⊆ [0, 1]) :
    m % 3 = 0 ∨ m % 3 = 1 := by
  have hr : m % 3 < 3 := Nat.mod_lt _ (by decide)
  by_contra hn
  have hm : m % 3 = 2 := by omega
  have he : m = 3 * (m / 3) + 2 := by omega
  have hp : 4 ^ m % 9 = 7 := by
    rw [he, pow_add, pow_mul]
    simp [Nat.mul_mod, Nat.pow_mod]
  have hdiv := good_div_three h
  have hp_le := Nat.mod_le (4 ^ m) 9
  have hdpos : 0 < 4 ^ m / 3 := by omega
  have hd := good_unit_mod_three hdpos hdiv
  have heq := Nat.mod_add_div (4 ^ m) 3
  have hm3 : 4 ^ m % 3 < 3 := Nat.mod_lt _ (by decide)
  have hrem := Nat.mod_add_div (4 ^ m / 3) 3
  omega

/-- Finiteness of the good values in each affine orbit suffices for the exact
original conjecture. This theorem does not supply the two finiteness premises. -/
theorem affine_orbits_criterion
    (h7 : {n : ℕ | (∃ t, n = orbit 64 7 t) ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite)
    (h28 : {n : ℕ | (∃ t, n = orbit 64 28 t) ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  refine ((h7.image (fun n => 9 * n + 1)).union
    (h28.image (fun n => 9 * n + 4))).subset ?_
  rintro n ⟨⟨k, rfl⟩, hd⟩
  obtain ⟨m, hm⟩ := even_exponent hd
  have he : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    rfl
  rw [he] at hd ⊢
  have hquot := good_div_nine hd
  rcases good_four_exponent_mod_three hd with h0 | h1
  · have hexp : m = 3 * (m / 3) := by omega
    have hid : 4 ^ m = 9 * orbit 64 7 (m / 3) + 1 := by
      conv_lhs => rw [hexp]
      exact (orbit_seven_identity _).symm
    have hq : 4 ^ m / 9 = orbit 64 7 (m / 3) := by omega
    rw [hq] at hquot
    exact Or.inl ⟨orbit 64 7 (m / 3), ⟨⟨m / 3, rfl⟩, hquot⟩, hid.symm⟩
  · have hexp : m = 3 * (m / 3) + 1 := by omega
    have hid : 4 ^ m = 9 * orbit 64 28 (m / 3) + 4 := by
      conv_lhs => rw [hexp]
      exact (orbit_twenty_eight_identity _).symm
    have hq : 4 ^ m / 9 = orbit 64 28 (m / 3) := by omega
    rw [hq] at hquot
    exact Or.inr ⟨orbit 64 28 (m / 3), ⟨⟨m / 3, rfl⟩, hquot⟩, hid.symm⟩

lemma good_three_mul_add {n d : ℕ} (hn : Nat.digits 3 n ⊆ [0, 1])
    (hd : d ∈ ([0, 1] : List ℕ)) : Nat.digits 3 (3 * n + d) ⊆ [0, 1] := by
  have hlt : d < 3 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega
  by_cases hz : 3 * n + d = 0
  · simp [hz]
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) (by omega : 0 < 3 * n + d)]
  have hm : (3 * n + d) % 3 = d := by omega
  have hq : (3 * n + d) / 3 = n := by omega
  rw [hm, hq]
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hd
  · exact hn ha

lemma good_nine_mul_add_one {n : ℕ} (hn : Nat.digits 3 n ⊆ [0, 1]) :
    Nat.digits 3 (9 * n + 1) ⊆ [0, 1] := by
  have h0 := good_three_mul_add hn (by simp : 0 ∈ ([0, 1] : List ℕ))
  have h1 := good_three_mul_add h0 (by simp : 1 ∈ ([0, 1] : List ℕ))
  rwa [show 3 * (3 * n + 0) + 1 = 9 * n + 1 by ring] at h1

lemma good_nine_mul_add_four {n : ℕ} (hn : Nat.digits 3 n ⊆ [0, 1]) :
    Nat.digits 3 (9 * n + 4) ⊆ [0, 1] := by
  have h1 := good_three_mul_add hn (by simp : 1 ∈ ([0, 1] : List ℕ))
  have h2 := good_three_mul_add h1 (by simp : 1 ∈ ([0, 1] : List ℕ))
  rwa [show 3 * (3 * n + 1) + 1 = 9 * n + 4 by ring] at h2

lemma four_power_isPowerOfTwo (m : ℕ) : (4 ^ m).isPowerOfTwo := by
  exact ⟨2 * m, by rw [pow_mul]; rfl⟩

/-- The two-orbit reformulation is equivalent to, not a weakening of, the
conjecture. Neither direction supplies the finiteness assertion. -/
theorem affine_orbits_iff :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite ↔
    {n : ℕ | (∃ t, n = orbit 64 7 t) ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite ∧
    {n : ℕ | (∃ t, n = orbit 64 28 t) ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  constructor
  · intro h
    have himage := h.image (fun n => n / 9)
    constructor
    · refine himage.subset ?_
      rintro n ⟨⟨t, rfl⟩, hd⟩
      have hid := orbit_seven_identity t
      refine ⟨4 ^ (3 * t), ⟨four_power_isPowerOfTwo _, ?_⟩, ?_⟩
      · rw [← hid]
        exact good_nine_mul_add_one hd
      · dsimp only
        omega
    · refine himage.subset ?_
      rintro n ⟨⟨t, rfl⟩, hd⟩
      have hid := orbit_twenty_eight_identity t
      refine ⟨4 ^ (3 * t + 1), ⟨four_power_isPowerOfTwo _, ?_⟩, ?_⟩
      · rw [← hid]
        exact good_nine_mul_add_four hd
      · dsimp only
        omega
  · rintro ⟨h7, h28⟩
    exact affine_orbits_criterion h7 h28

lemma orbit_divisible {q c d : ℕ} (hc : d ∣ c) (t : ℕ) : d ∣ orbit q c t := by
  induction t with
  | zero => simp
  | succ t ih => exact dvd_add (dvd_mul_of_dvd_right ih q) hc

lemma affine_orbits_divisible_seven (t : ℕ) :
    7 ∣ orbit 64 7 t ∧ 7 ∣ orbit 64 28 t := by
  exact ⟨orbit_divisible (by decide) t, orbit_divisible (by decide) t⟩

structure Core (σ : Type*) where
  D : DFA ℕ σ
  q : ℕ
  c : ℕ
  q_pos : 0 < q
  c_lt_q : c < q
  R : σ → σ → ℕ → Prop
  relation_start : ∀ c', c' < q → R D.start (evalNat D c') c'
  relation_step : ∀ s t c' d e c'', c' < q → d < 3 → e < 3 →
    c'' < q → q * d + c'' = 3 * c' + e → R s t c' →
    R (D.step s d) (D.step t e) c''
  relation_finish : ∀ s t, R s t c → s ∈ D.accept → t ∈ D.accept
  seed : D.start ∈ D.accept

namespace Core
variable {σ : Type*} (C : Core σ)

lemma relation (n c : ℕ) (hc : c < C.q) :
    C.R (evalNat C.D n) (evalNat C.D (C.q * n + c)) c := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [mul_zero, zero_add, evalNat_zero] using C.relation_start c hc
    · have hnpos : 0 < n := by omega
      let d := n % 3
      let cp := (C.q * d + c) / 3
      let e := (C.q * d + c) % 3
      have hd : d < 3 := Nat.mod_lt n (by decide)
      have he : e < 3 := Nat.mod_lt _ (by decide)
      have hcp : cp < C.q := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr
        nlinarith
      have hrel := ih (n / 3) (Nat.div_lt_self hnpos (by decide)) cp hcp
      have hstep := C.relation_step _ _ cp d e c hcp hd he hc
        (by dsimp [cp, e]; omega) hrel
      obtain ⟨hq, hm⟩ := affine_div_mod C.q n c
      have hpos : 0 < C.q * n + c := by have := C.q_pos; positivity
      rw [evalNat_pos C.D hnpos, evalNat_pos C.D hpos, hq, hm]
      exact hstep

lemma affine_closed {n : ℕ} (hn : evalNat C.D n ∈ C.D.accept) :
    evalNat C.D (C.q * n + C.c) ∈ C.D.accept :=
  C.relation_finish _ _ (C.relation n C.c C.c_lt_q) hn

lemma accepts_orbit (t : ℕ) : evalNat C.D (orbit C.q C.c t) ∈ C.D.accept := by
  induction t with
  | zero => simpa only [orbit_zero, evalNat_zero] using C.seed
  | succ t ih => exact C.affine_closed ih

end Core

/-- The acyclic good-word part of an affine invariant yields a finite set of
good orbit values. The structure and rank data must still be supplied. -/
theorem finite_language_criterion {σ : Type*} (C : Core σ)
    (G K : σ → Prop) (rank : σ → ℕ) (hgstart : G (C.D.step C.D.start 1))
    (hgstep : ∀ s d, d < 2 → G s → G (C.D.step s d))
    (hkacc : ∀ s, s ∈ C.D.accept → K s)
    (hkstep : ∀ s d, d < 2 → K (C.D.step s d) → K s)
    (hrstep : ∀ s d, d < 2 → G s → K (C.D.step s d) → rank (C.D.step s d) < rank s) :
    {n : ℕ | (∃ t, n = orbit C.q C.c t) ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨3 ^ (rank (C.D.step C.D.start 1) + 1), ?_⟩
  rintro n ⟨⟨t, rfl⟩, hd⟩
  by_cases hn : orbit C.q C.c t = 0
  · simp [hn]
  · have ha := C.accepts_orbit t
    have hl := good_length_bound C.D G K rank hgstart hgstep hkacc hkstep hrstep
      (by omega) hd ha
    have hlt := Nat.lt_base_pow_length_digits (b := 3) (m := orbit C.q C.c t) (by decide)
    exact (Nat.le_of_lt hlt).trans (Nat.pow_le_pow_right (by decide) hl)

#print axioms affine_orbits_criterion
#print axioms affine_orbits_iff
#print axioms affine_orbits_divisible_seven
#print axioms finite_language_criterion
end Erdos406AffineCertificate
