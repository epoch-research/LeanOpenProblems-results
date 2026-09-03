import Submission.MinplusCertificates
import Submission.BinaryWeightedCertificates

/-! Soundness of binary minimum-path certificates. No supercritical instance
is supplied, so this module does not settle Erdős 406. -/
namespace Erdos406BinaryMinplus
open Erdos406GroupedCertificate
open Erdos406Tropical (Automaton Run)
open Erdos406Minplus (valueFrom valueFrom_le_run exists_min_run)

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def value (D : Automaton σ) (n : ℕ) : ℝ :=
  valueFrom D D.start (Nat.digits 2 n).reverse

/-- Every input path has a matching output path with bounded additional cost.
This quantifier direction is essential for a minimum-path upper bound. -/
structure Construction (D : Automaton σ) where
  R : σ → σ → ℕ → Prop
  H : σ → σ → ℕ → ℝ
  seed : ∀ c, c < 3 → ∃ t v, Run D D.start (Nat.digits 2 c).reverse t v ∧
    R D.start t c ∧ v ≤ H D.start t c
  step : ∀ s t c d e cp, c < 3 → d < 2 → e < 2 → cp < 3 →
    3 * d + cp = 2 * c + e → R s t c → ∀ sp, sp ∈ D.next s d →
    ∃ tp, tp ∈ D.next t e ∧ R sp tp cp ∧
      H s t c + D.weight t e tp - D.weight s d sp ≤ H sp tp cp
  finish : ∀ s t c, c < 2 → R s t c → H s t c ≤ 1

namespace Construction
variable {D : Automaton σ} (C : Construction D)
include C

lemma simulate (n c : ℕ) (hc : c < 3) {s v}
    (hin : Run D D.start (Nat.digits 2 n).reverse s v) :
    ∃ t u, Run D D.start (Nat.digits 2 (3 * n + c)).reverse t u ∧
      C.R s t c ∧ u - v ≤ C.H s t c := by
  induction n using Nat.strong_induction_on generalizing c s v with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [Nat.digits_zero, List.reverse_nil] at hin
      cases hin
      obtain ⟨t, u, hu, hr, hh⟩ := C.seed c hc
      exact ⟨t, u, by simpa using hu, hr, by simpa using hh⟩
    · have hnpos := Nat.pos_of_ne_zero hn
      let d := n % 2
      let cp := (3 * d + c) / 2
      let e := (3 * d + c) % 2
      have hd : d < 2 := Nat.mod_lt _ (by decide)
      have he : e < 2 := Nat.mod_lt _ (by decide)
      have hcp : cp < 3 := by dsimp [cp]; omega
      have hid : 3 * d + c = 2 * cp + e := by dsimp [cp, e]; omega
      rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hnpos,
        List.reverse_cons] at hin
      obtain ⟨p, a, hp, hs, hv⟩ := hin.split_last
      obtain ⟨q, b, hq, hr, hh⟩ := ih (n / 2)
        (Nat.div_lt_self hnpos (by decide)) cp hcp hp
      obtain ⟨t, ht, hr', hh'⟩ := C.step p q cp d e c hcp hd he hc hid hr s hs
      have hout : 0 < 3 * n + c := by omega
      obtain ⟨heq, hmod⟩ := affine_div_mod 2 3 n c (by decide)
      refine ⟨t, b + D.weight q e t, ?_, hr', ?_⟩
      · rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hout,
          List.reverse_cons, heq, hmod]
        exact hq.snoc ht
      · dsimp only [d] at hh'
        linarith

lemma construction_bound (n d : ℕ) (hd : d < 2) :
    value D (3 * n + d) ≤ value D n + 1 := by
  obtain ⟨s, hs⟩ := exists_min_run D D.start (Nat.digits 2 n).reverse
  obtain ⟨t, u, hu, hr, hh⟩ := C.simulate n d (by omega) hs
  have hf := C.finish s t d hd hr
  have hb := valueFrom_le_run hu
  change value D (3 * n + d) ≤ u at hb
  change u - value D n ≤ C.H s t d at hh
  linarith
end Construction

/-- The lower estimate applies to every zero-tail path, not merely one path. -/
structure PowerBound (D : Automaton σ) where
  a : ℝ
  B : ℝ
  G : σ → Prop
  J : σ → ℝ
  start : ∀ s, s ∈ D.next D.start 1 → G s
  step : ∀ s t, G s → t ∈ D.next s 0 → G t
  lower_step : ∀ s t, G s → t ∈ D.next s 0 →
    a + J t - J s ≤ D.weight s 0 t
  lower_end : ∀ s t, s ∈ D.next D.start 1 → G t →
    -B ≤ D.weight D.start 1 s + J t - J s

namespace PowerBound
variable {D : Automaton σ} (P : PowerBound D)

lemma zero_run_lower (k : ℕ) {s t v} (h : Run D s (List.replicate k 0) t v)
    (hs : P.G s) : P.G t ∧ P.a * k + P.J t - P.J s ≤ v := by
  induction k generalizing s v with
  | zero =>
    simp only [List.replicate_zero] at h
    cases h
    exact ⟨hs, by simp⟩
  | succ k ih =>
    rw [List.replicate_succ] at h
    cases h with
    | @cons _ u _ _ _ w hu hw =>
      have hgu := P.step s u hs hu
      obtain ⟨ht, hb⟩ := ih hw hgu
      have he := P.lower_step s u hs hu
      refine ⟨ht, ?_⟩
      push_cast
      linarith

lemma power_run_lower (k : ℕ) {t v}
    (h : Run D D.start (1 :: List.replicate k 0) t v) : P.a * k - P.B ≤ v := by
  cases h with
  | @cons _ s _ _ _ v hs hv =>
    obtain ⟨hg, hb⟩ := P.zero_run_lower k hv (P.start s hs)
    have he := P.lower_end s t hs hg
    linarith

lemma power_lower (k : ℕ) : P.a * k - P.B ≤ value D (2 ^ k) := by
  have hword : (Nat.digits 2 (2 ^ k)).reverse = 1 :: List.replicate k 0 := by
    have h := Nat.digits_base_pow_mul (b := 2) (k := k) (m := 1) (by decide) (by decide)
    simpa using congrArg List.reverse h
  obtain ⟨t, ht⟩ := exists_min_run D D.start (Nat.digits 2 (2 ^ k)).reverse
  have hb := P.power_run_lower k (hword ▸ ht)
  simpa only [value, hword] using hb
end PowerBound

/-- The strict rate remains an explicit premise. A complete finite instance
would prove the original conjecture, but no such instance is asserted. -/
theorem binary_minplus_criterion (D : Automaton σ) (C : Construction D)
    (P : PowerBound D) (hcrit : Real.log 2 < P.a * Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite :=
  Erdos406BinaryWeighted.construction_potential_criterion (value D) P.a P.B
    C.construction_bound P.power_lower hcrit

#print axioms Construction.simulate
#print axioms Construction.construction_bound
#print axioms PowerBound.power_lower
#print axioms binary_minplus_criterion
end Erdos406BinaryMinplus
