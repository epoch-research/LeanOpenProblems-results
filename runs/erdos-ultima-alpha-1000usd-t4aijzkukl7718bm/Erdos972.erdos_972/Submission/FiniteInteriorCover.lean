import FormalConjecturesUtil

/-! A finite, exact prime-pair covering certificate. This is not a proof of
infinitude and does not settle Erdős 972. -/
namespace Erdos972FiniteInteriorCover

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Each entry covers the current left endpoint and advances the uncovered
part to the right endpoint of its prime-pair interval. -/
def coverCertificate (B M : ℕ) (hi : ℚ) : ℚ → List (ℕ × ℕ) → Prop
  | lo, [] => hi < lo
  | lo, (p, q) :: xs =>
      B < p ∧ p ≤ M ∧ p.Prime ∧ q.Prime ∧
        (q : ℚ) ≤ lo * p ∧ coverCertificate B M hi ((q + 1 : ℚ) / p) xs

instance (B M : ℕ) (hi lo : ℚ) (xs : List (ℕ × ℕ)) :
    Decidable (coverCertificate B M hi lo xs) := by
  induction xs generalizing lo with
  | nil => unfold coverCertificate; infer_instance
  | cons x xs ih =>
    rcases x with ⟨p, q⟩
    unfold coverCertificate
    exact instDecidableAnd

/-- Soundness uses real interval inequalities, not floating-point calculations. -/
theorem coverCertificate_sound {B M : ℕ} {hi lo : ℚ} {xs : List (ℕ × ℕ)}
    (hc : coverCertificate B M hi lo xs) {α : ℝ}
    (hlo : (lo : ℝ) ≤ α) (hhi : α ≤ (hi : ℝ)) :
    ∃ p : ℕ, B < p ∧ p ≤ M ∧ p.Prime ∧ Nat.Prime ⌊α * p⌋₊ := by
  induction xs generalizing lo with
  | nil =>
    have hbad : (hi : ℝ) < lo := by exact_mod_cast hc
    linarith
  | cons x xs ih =>
    rcases x with ⟨p, q⟩
    obtain ⟨hBp, hpM, hp, hq, hqlo, hrest⟩ := hc
    have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    have hqloR : (q : ℝ) ≤ (lo : ℝ) * p := by exact_mod_cast hqlo
    by_cases h : α < ((q : ℝ) + 1) / p
    · refine ⟨p, hBp, hpM, hp, ?_⟩
      have hlow : (q : ℝ) ≤ α * p :=
        hqloR.trans (mul_le_mul_of_nonneg_right hlo hpR.le)
      have hupp : α * p < (q : ℝ) + 1 := (lt_div_iff₀ hpR).mp h
      have hf : ⌊α * p⌋₊ = q :=
        (Nat.floor_eq_iff' hq.ne_zero).mpr ⟨hlow, hupp⟩
      simpa only [hf] using hq
    · apply ih hrest
      simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
        using le_of_not_gt h

/-- Explicit entries selected by exact rational interval comparisons. -/
def interiorChain : List (ℕ × ℕ) :=
  [
  (131, 157),
  (109, 131),
  (163, 197),
  (113, 137),
  (163, 199),
  (107, 131),
  (103, 127),
  (223, 277),
  (131, 163),
  (191, 239),
  (157, 197),
  (101, 127),
  (151, 191),
  (157, 199),
  (103, 131),
  (107, 137),
  (139, 179),
  (163, 211),
  (107, 139),
  (137, 179),
  (173, 227),
  (151, 199),
  (173, 229),
  (419, 557),
  (103, 137),
  (113, 151),
  (157, 211),
  (103, 139),
  (101, 137),
  (197, 269),
  (109, 149),
  (139, 191),
  (101, 139),
  (109, 151),
  (107, 149),
  (433, 607),
  (193, 271),
  (137, 193),
  (107, 151),
  (157, 223),
  (127, 181),
  (139, 199),
  (137, 197),
  (113, 163),
  (173, 251),
  (193, 281),
  (131, 191),
  (241, 353),
  (107, 157),
  (101, 149),
  (157, 233),
  (257, 383),
  (401, 599),
  (101, 151),
  (127, 191),
  (223, 337),
  (229, 347),
  (131, 199),
  (103, 157),
  (109, 167),
  (137, 211),
  (271, 419),
  (251, 389),
  (127, 197),
  (101, 157),
  (149, 233),
  (179, 281),
  (167, 263),
  (197, 311),
  (103, 163),
  (109, 173),
  (151, 241),
  (113, 181),
  (223, 359),
  (101, 163),
  (103, 167),
  (137, 223),
  (139, 227),
  (191, 313),
  (109, 179),
  (163, 269),
  (101, 167),
  (109, 181),
  (227, 379),
  (107, 179),
  (103, 173),
  (383, 647),
  (107, 181),
  (137, 233),
  (113, 193),
  (101, 173),
  (139, 239),
  (157, 271),
  (347, 601),
  (139, 241),
  (103, 179),
  (113, 197),
  (181, 317),
  (127, 223),
  (113, 199),
  (211, 373),
  (101, 179),
  (151, 269),
  (127, 227),
  (101, 181)
  ]

lemma interiorChain_certificate :
    coverCertificate 100 433 (9/5) (6/5) interiorChain := by
  decide +kernel

/-- Every real slope in [6/5,9/5], rational or irrational, has a genuine
prime pair with input strictly beyond 100 and at most 433. This is finite. -/
theorem prime_pair_beyond_100 {α : ℝ} (hlo : 6/5 ≤ α) (hhi : α ≤ 9/5) :
    ∃ p : ℕ, 100 < p ∧ p ≤ 433 ∧ p.Prime ∧ Nat.Prime ⌊α * p⌋₊ := by
  apply coverCertificate_sound interiorChain_certificate
  · norm_num at *
    exact hlo
  · norm_num at *
    exact hhi

#print axioms coverCertificate_sound
#print axioms interiorChain_certificate
#print axioms prime_pair_beyond_100

end Erdos972FiniteInteriorCover
