import Submission.AffinePotentialCertificates

/-! Soundness of binary weighted certificates for ternary-good construction.
The strict supercritical rate remains a hypothesis; no such certificate is
asserted in this module. -/

namespace Erdos406BinaryWeighted
open Erdos406AffineCertificate Erdos406GroupedCertificate Erdos406AffinePotential

lemma construction_good_bound (V : ℕ → ℝ)
    (hstep : ∀ n d : ℕ, d < 2 → V (3 * n + d) ≤ V n + 1)
    (n : ℕ) (hn : Nat.digits 3 n ⊆ [0, 1]) :
    V n ≤ V 0 + (Nat.digits 3 n).length := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz]
    have hp : 0 < n := Nat.pos_of_ne_zero hz
    have hq := ih (n / 3) (Nat.div_lt_self hp (by decide)) (good_div_three hn)
    have hd : n % 3 < 2 := by
      rcases good_unit_mod_three hp hn with h | h <;> omega
    have hs := hstep (n / 3) (n % 3) hd
    have he : 3 * (n / 3) + n % 3 = n := by omega
    rw [he] at hs
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hp]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

lemma ternary_power_length_log (k : ℕ) :
    ((Nat.digits 3 (2 ^ k)).length : ℝ) * Real.log 3 ≤
      (k : ℝ) * Real.log 2 + Real.log 3 := by
  have hh := Nat.base_pow_length_digits_le 3 (2 ^ k) (by decide) (by positivity)
  have hp : (3 : ℝ) ^ (Nat.digits 3 (2 ^ k)).length ≤ 3 * (2 : ℝ) ^ k := by
    exact_mod_cast hh
  have hl := Real.log_le_log (by positivity) hp
  rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
  linarith

lemma rational_supercritical (p q : ℕ) (hq : 0 < q) (h : 2 ^ q < 3 ^ p) :
    Real.log 2 < ((p : ℝ) / q) * Real.log 3 := by
  have hh : (2 : ℝ) ^ q < (3 : ℝ) ^ p := by exact_mod_cast h
  have hl := Real.log_lt_log (by positivity) hh
  rw [Real.log_pow, Real.log_pow] at hl
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mpr
  nlinarith

/-- A global upper cost for the two ternary construction maps, together with
a strictly supercritical lower cost on binary powers, suffices for finiteness. -/
theorem construction_potential_criterion (V : ℕ → ℝ) (a B : ℝ)
    (hstep : ∀ n d : ℕ, d < 2 → V (3 * n + d) ≤ V n + 1)
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
    have hb := (hpower k).trans (construction_good_bound V hstep _ hg)
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
  · exact (hcut k (by omega) hg).elim

/-- A lower bound at the same rate on ALL positive binary words cannot be
supercritical. A successful power-specific certificate must avoid this
stronger, global lower bound. -/
theorem not_supercritical_of_global_binary_lower_bound (V : ℕ → ℝ) (a B : ℝ)
    (hstep : ∀ n d : ℕ, d < 2 → V (3 * n + d) ≤ V n + 1)
    (hlower : ∀ n : ℕ, 0 < n → a * (Nat.digits 2 n).length - B ≤ V n) :
    ¬ Real.log 2 < a * Real.log 3 := by
  intro hcrit
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha : 0 < a := by nlinarith
  have hgap : 0 < a * Real.log 3 - Real.log 2 := by linarith
  have hthree : ∀ k : ℕ, V (3 ^ k) ≤ V 1 + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := hstep (3 ^ k) 0 (by decide)
      rw [pow_succ']
      simp only [add_zero] at hh
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt
    ((V 1 + B) * Real.log 2 / (a * Real.log 3 - Real.log 2))
  have hbig := (div_lt_iff₀ hgap).mp hk
  have hn := Nat.lt_base_pow_length_digits (m := 3 ^ k) (by decide : 1 < 2)
  have hnR : (3 : ℝ) ^ k < 2 ^ (Nat.digits 2 (3 ^ k)).length := by exact_mod_cast hn
  have hlen := Real.log_lt_log (by positivity) hnR
  rw [Real.log_pow, Real.log_pow] at hlen
  have hlenA := mul_lt_mul_of_pos_left hlen ha
  have hv := (hlower (3 ^ k) (by positivity)).trans (hthree k)
  have hvL := mul_le_mul_of_nonneg_right hv hlog2.le
  nlinarith

def weightNat {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (n : ℕ) : ℝ :=
  weightFrom D w D.start (Nat.digits 2 n).reverse

lemma weightNat_zero {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) :
    weightNat D w 0 = 0 := by simp [weightNat, weightFrom]

lemma weightNat_one {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) :
    weightNat D w 1 = w D.start 1 := by
  simp [weightNat, weightFrom]

lemma evalNat_one {σ : Type*} (D : DFA ℕ σ) : evalNat 2 D 1 = D.step D.start 1 := by
  simp [evalNat, DFA.eval, DFA.evalFrom]

lemma weightNat_pos {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ)
    {n : ℕ} (hn : 0 < n) :
    weightNat D w n = weightNat D w (n / 2) + w (evalNat 2 D (n / 2)) (n % 2) := by
  rw [weightNat, Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hn,
    List.reverse_cons, weightFrom_append_singleton]
  rfl

structure Construction (σ : Type*) where
  D : DFA ℕ σ
  w : σ → ℕ → ℝ
  R : σ → σ → ℕ → Prop
  P : σ → σ → ℕ → ℝ
  relation_start : ∀ c, c < 3 → R D.start (evalNat 2 D c) c
  relation_step : ∀ s t c d e cp, c < 3 → d < 2 → e < 2 → cp < 3 →
    3 * d + cp = 2 * c + e → R s t c → R (D.step s d) (D.step t e) cp
  upper_start : ∀ c, c < 3 → weightNat D w c ≤ P D.start (evalNat 2 D c) c
  upper_step : ∀ s t c d e cp, c < 3 → d < 2 → e < 2 → cp < 3 →
    3 * d + cp = 2 * c + e → R s t c →
    P s t c + w t e - w s d ≤ P (D.step s d) (D.step t e) cp
  upper_finish : ∀ s t c, c < 2 → R s t c → P s t c ≤ 1

namespace Construction
variable {σ : Type*} (C : Construction σ)

lemma relation_upper (n c : ℕ) (hc : c < 3) :
    C.R (evalNat 2 C.D n) (evalNat 2 C.D (3 * n + c)) c ∧
    weightNat C.D C.w (3 * n + c) - weightNat C.D C.w n ≤
      C.P (evalNat 2 C.D n) (evalNat 2 C.D (3 * n + c)) c := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [mul_zero, zero_add, evalNat_zero, weightNat_zero, sub_zero] using
        And.intro (C.relation_start c hc) (C.upper_start c hc)
    · have hnpos := Nat.pos_of_ne_zero hn
      let d := n % 2
      let cp := (3 * d + c) / 2
      let e := (3 * d + c) % 2
      have hd : d < 2 := Nat.mod_lt _ (by decide)
      have he : e < 2 := Nat.mod_lt _ (by decide)
      have hcp : cp < 3 := by dsimp [cp]; omega
      have hi := ih (n / 2) (Nat.div_lt_self hnpos (by decide)) cp hcp
      have hid : 3 * d + c = 2 * cp + e := by dsimp [cp, e]; omega
      have hr := C.relation_step _ _ cp d e c hcp hd he hc hid hi.1
      have hp := C.upper_step _ _ cp d e c hcp hd he hc hid hi.1
      have hout : 0 < 3 * n + c := by omega
      obtain ⟨hq, hm⟩ := affine_div_mod 2 3 n c (by decide)
      rw [evalNat_pos 2 C.D (by decide) hnpos, evalNat_pos 2 C.D (by decide) hout, hq, hm,
        weightNat_pos C.D C.w hnpos, weightNat_pos C.D C.w hout, hq, hm]
      exact ⟨hr, by dsimp only [d, cp, e] at hi hp ⊢; linarith⟩

lemma construction_bound (n d : ℕ) (hd : d < 2) :
    weightNat C.D C.w (3 * n + d) ≤ weightNat C.D C.w n + 1 := by
  have hh := C.relation_upper n d (by omega)
  have hf := C.upper_finish _ _ d hd hh.1
  linarith

end Construction

structure PowerBound {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) where
  a : ℝ
  B : ℝ
  G : σ → Prop
  J : σ → ℝ
  start : G (D.step D.start 1)
  step : ∀ s, G s → G (D.step s 0)
  lower_step : ∀ s, G s → a + J (D.step s 0) - J s ≤ w s 0
  lower_end : ∀ s, G s → -B ≤ w D.start 1 + J s - J (D.step D.start 1)

namespace PowerBound
variable {σ : Type*} {D : DFA ℕ σ} {w : σ → ℕ → ℝ} (S : PowerBound D w)

lemma power_lower (k : ℕ) : S.a * k - S.B ≤ weightNat D w (2 ^ k) := by
  have hrec (k : ℕ) :
      evalNat 2 D (2 ^ (k + 1)) = D.step (evalNat 2 D (2 ^ k)) 0 ∧
      weightNat D w (2 ^ (k + 1)) = weightNat D w (2 ^ k) + w (evalNat 2 D (2 ^ k)) 0 := by
    rw [pow_succ']
    rw [evalNat_pos 2 D (by decide) (by positivity), weightNat_pos D w (by positivity)]
    simp
  have hboth : ∀ k : ℕ, S.G (evalNat 2 D (2 ^ k)) ∧
      S.a * k + w D.start 1 + S.J (evalNat 2 D (2 ^ k)) - S.J (D.step D.start 1) ≤
        weightNat D w (2 ^ k) := by
    intro k
    induction k with
    | zero => simpa only [pow_zero, evalNat_one, weightNat_one, Nat.cast_zero, mul_zero,
        zero_add, add_sub_cancel_right] using And.intro S.start (le_refl (w D.start 1))
    | succ k ih =>
      obtain ⟨he, hw⟩ := hrec k
      have hh := S.lower_step _ ih.1
      refine ⟨he ▸ S.step _ ih.1, ?_⟩
      rw [he, hw]
      push_cast
      linarith [ih.2]
  have hh := hboth k
  have hb := S.lower_end _ hh.1
  linarith

end PowerBound

/-- Every hypothesis here has a finite table-checking interpretation. The
strict rate inequality is essential and is not supplied by this theorem. -/
theorem weighted_binary_criterion {σ : Type*} (C : Construction σ) (S : PowerBound C.D C.w)
    (hcrit : Real.log 2 < S.a * Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite :=
  construction_potential_criterion (weightNat C.D C.w) S.a S.B C.construction_bound
    S.power_lower hcrit

#print axioms construction_potential_criterion
#print axioms weighted_binary_criterion
end Erdos406BinaryWeighted
