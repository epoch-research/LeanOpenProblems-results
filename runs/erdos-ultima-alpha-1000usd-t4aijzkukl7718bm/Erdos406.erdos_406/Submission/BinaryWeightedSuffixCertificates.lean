import Submission.BinaryWeightedCertificates
import Submission.BinaryCertificates

/-! Soundness for a binary weighted certificate whose construction inequality
is required only on a fixed ternary-good suffix. No supercritical instance is
asserted, and this module does not settle Erdős 406. -/
namespace Erdos406BinaryWeightedSuffix
open Erdos406AffineCertificate Erdos406GroupedCertificate Erdos406BinaryWeighted

lemma construction_good_bound (V : ℕ → ℝ) (r : ℕ)
    (hstep : ∀ n d : ℕ, Nat.digits 3 (n % 3 ^ r) ⊆ [0, 1] → d < 2 →
      V (3 * n + d) ≤ V n + 1)
    (n : ℕ) (hn : Nat.digits 3 n ⊆ [0, 1]) :
    V n ≤ V 0 + (Nat.digits 3 n).length := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz]
    have hp : 0 < n := Nat.pos_of_ne_zero hz
    have hg := good_div_three hn
    have hq := ih (n / 3) (Nat.div_lt_self hp (by decide)) hg
    have hd : n % 3 < 2 := by
      rcases good_unit_mod_three hp hn with h | h <;> omega
    have hs := hstep (n / 3) (n % 3) (Erdos406BinaryCertificate.good_mod hg r) hd
    have he : 3 * (n / 3) + n % 3 = n := by omega
    rw [he] at hs
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hp]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- The suffix guard is sound because every prefix of a good ternary word
also has a good suffix. The strict rate is an essential, unsupplied hypothesis. -/
theorem guarded_construction_potential_criterion (V : ℕ → ℝ) (r : ℕ) (a B : ℝ)
    (hstep : ∀ n d : ℕ, Nat.digits 3 (n % 3 ^ r) ⊆ [0, 1] → d < 2 →
      V (3 * n + d) ≤ V n + 1)
    (hpower : ∀ k : ℕ, a * k - B ≤ V (2 ^ k))
    (hcrit : Real.log 2 < a * Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hgap : 0 < a * Real.log 3 - Real.log 2 := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt
    ((V 0 + B + 1) * Real.log 3 / (a * Real.log 3 - Real.log 2))
  have hlarge := (div_lt_iff₀ hgap).mp hM
  have hcut (k : ℕ) (hk : M ≤ k) : ¬ Nat.digits 3 (2 ^ k) ⊆ [0, 1] := by
    intro hg
    have hb := (hpower k).trans (construction_good_bound V r hstep _ hg)
    have hbl := mul_le_mul_of_nonneg_right hb hlog.le
    have hlen := ternary_power_length_log k
    have hMk : (M : ℝ) ≤ k := by exact_mod_cast hk
    have hkm := mul_le_mul_of_nonneg_right hMk hgap.le
    nlinarith
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨2 ^ M, ?_⟩
  rintro n ⟨⟨k, rfl⟩, hg⟩
  by_cases hk : k < M
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact (hcut k (by omega)) hg |>.elim

structure GuardedConstruction (σ : Type*) where
  D : DFA ℕ σ
  w : σ → ℕ → ℝ
  depth : ℕ
  R : σ → σ → ℕ → ℕ → Prop
  P : σ → σ → ℕ → ℕ → ℝ
  relation_start : ∀ c, c < 3 → R D.start (evalNat 2 D c) c 0
  relation_step : ∀ s t c v d e cp, c < 3 → v < 3 ^ depth →
    d < 2 → e < 2 → cp < 3 → 3 * d + cp = 2 * c + e → R s t c v →
    R (D.step s d) (D.step t e) cp ((2 * v + d) % 3 ^ depth)
  upper_start : ∀ c, c < 3 → weightNat D w c ≤ P D.start (evalNat 2 D c) c 0
  upper_step : ∀ s t c v d e cp, c < 3 → v < 3 ^ depth →
    d < 2 → e < 2 → cp < 3 → 3 * d + cp = 2 * c + e → R s t c v →
    P s t c v + w t e - w s d ≤
      P (D.step s d) (D.step t e) cp ((2 * v + d) % 3 ^ depth)
  upper_finish : ∀ s t c v, c < 2 → v < 3 ^ depth →
    Nat.digits 3 v ⊆ [0, 1] → R s t c v → P s t c v ≤ 1

namespace GuardedConstruction
variable {σ : Type*} (C : GuardedConstruction σ)

lemma relation_upper (n c : ℕ) (hc : c < 3) :
    C.R (evalNat 2 C.D n) (evalNat 2 C.D (3 * n + c)) c (n % 3 ^ C.depth) ∧
    weightNat C.D C.w (3 * n + c) - weightNat C.D C.w n ≤
      C.P (evalNat 2 C.D n) (evalNat 2 C.D (3 * n + c)) c (n % 3 ^ C.depth) := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [mul_zero, zero_add, Nat.zero_mod, evalNat_zero, weightNat_zero,
        sub_zero] using And.intro (C.relation_start c hc) (C.upper_start c hc)
    · have hnpos := Nat.pos_of_ne_zero hn
      let d := n % 2
      let cp := (3 * d + c) / 2
      let e := (3 * d + c) % 2
      have hd : d < 2 := Nat.mod_lt _ (by decide)
      have he : e < 2 := Nat.mod_lt _ (by decide)
      have hcp : cp < 3 := by dsimp [cp]; omega
      have hi := ih (n / 2) (Nat.div_lt_self hnpos (by decide)) cp hcp
      have hv : n / 2 % 3 ^ C.depth < 3 ^ C.depth := Nat.mod_lt _ (by positivity)
      have hid : 3 * d + c = 2 * cp + e := by dsimp [cp, e]; omega
      have hr := C.relation_step _ _ cp _ d e c hcp hv hd he hc hid hi.1
      have hp := C.upper_step _ _ cp _ d e c hcp hv hd he hc hid hi.1
      have hv' : (2 * (n / 2 % 3 ^ C.depth) + d) % 3 ^ C.depth = n % 3 ^ C.depth := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
        congr 1
        dsimp [d]
        omega
      rw [hv'] at hr hp
      have hout : 0 < 3 * n + c := by omega
      obtain ⟨hq, hm⟩ := affine_div_mod 2 3 n c (by decide)
      rw [evalNat_pos 2 C.D (by decide) hnpos, evalNat_pos 2 C.D (by decide) hout,
        hq, hm, weightNat_pos C.D C.w hnpos, weightNat_pos C.D C.w hout, hq, hm]
      exact ⟨hr, by dsimp only [d, cp, e] at hi hp ⊢; linarith⟩

lemma construction_bound (n d : ℕ)
    (hg : Nat.digits 3 (n % 3 ^ C.depth) ⊆ [0, 1]) (hd : d < 2) :
    weightNat C.D C.w (3 * n + d) ≤ weightNat C.D C.w n + 1 := by
  have hh := C.relation_upper n d (by omega)
  have hf := C.upper_finish _ _ d _ hd (Nat.mod_lt _ (by positivity)) hg hh.1
  linarith

end GuardedConstruction

theorem weighted_binary_suffix_criterion {σ : Type*} (C : GuardedConstruction σ)
    (S : PowerBound C.D C.w) (hcrit : Real.log 2 < S.a * Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite :=
  guarded_construction_potential_criterion (weightNat C.D C.w) C.depth S.a S.B
    C.construction_bound S.power_lower hcrit

#print axioms guarded_construction_potential_criterion
#print axioms GuardedConstruction.relation_upper
#print axioms weighted_binary_suffix_criterion
end Erdos406BinaryWeightedSuffix
