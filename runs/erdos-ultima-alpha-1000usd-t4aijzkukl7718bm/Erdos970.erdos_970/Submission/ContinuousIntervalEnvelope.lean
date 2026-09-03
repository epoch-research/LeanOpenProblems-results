import Submission.IntervalRecursiveSieve

/-! Convex/concave interval envelopes. This file establishes their regularity,
not the uniform positivity needed for the quadratic Jacobsthal conjecture. -/
namespace Erdos970.ContinuousInterval

/-- Clip both the input and output to the nonnegative half-line. -/
def clip (g : ℝ → ℝ) (x : ℝ) : ℝ := max 0 (g (max 0 x))

theorem monotoneOn_of_convex_nonneg_zero {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0)
    (hn : ∀ x, 0 ≤ x → 0 ≤ f x) : MonotoneOn f (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simpa [h0] using hn y hy
  · exact hf.le_right_of_left_le'' (by simp) hy hx' hxy (by simpa [h0] using hn x hx)

theorem clip_regular {g : ℝ → ℝ} (hg : ConvexOn ℝ (Set.Ici 0) g) (hg0 : g 0 ≤ 0) :
    ConvexOn ℝ Set.univ (clip g) ∧ Monotone (clip g) ∧
      (∀ x, 0 ≤ clip g x) ∧ (∀ x, x ≤ 0 → clip g x = 0) := by
  let f (x : ℝ) := max 0 (g x)
  have hf : ConvexOn ℝ (Set.Ici 0) f := (convexOn_const 0 (convex_Ici 0)).sup hg
  have hf0 : f 0 = 0 := max_eq_left hg0
  have hfn (x : ℝ) : 0 ≤ f x := le_max_left _ _
  have hfm := monotoneOn_of_convex_nonneg_zero hf hf0 (fun x _ => hfn x)
  refine ⟨?_, ?_, fun x => le_max_left _ _, ?_⟩
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have hc : max 0 (a * x + b * y) ≤ a * max 0 x + b * max 0 y := by
      apply max_le
      · positivity
      · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right 0 x) ha)
          (mul_le_mul_of_nonneg_left (le_max_right 0 y) hb)
    have hm := hfm (le_max_left 0 (a * x + b * y))
      (show 0 ≤ a * max 0 x + b * max 0 y by positivity) hc
    have hh := hf.2 (le_max_left 0 x) (le_max_left 0 y) ha hb hab
    exact hm.trans hh
  · intro x y hxy
    exact hfm (le_max_left 0 x) (le_max_left 0 y) (max_le_max_left 0 hxy)
  · intro x hx
    simp [clip, max_eq_left hx, max_eq_left hg0]

theorem clip_lipschitz {g : ℝ → ℝ} {d : ℝ} (hd : 0 ≤ d)
    (hg : ∀ x y, 0 ≤ x → x ≤ y → g y - g x ≤ d * (y - x))
    (x y : ℝ) (hxy : x ≤ y) : clip g y - clip g x ≤ d * (y - x) := by
  have hm := max_le_max_left (0 : ℝ) hxy
  have hh := hg (max 0 x) (max 0 y) (le_max_left _ _) hm
  have hdiff : 0 ≤ max 0 y - max 0 x := sub_nonneg.mpr hm
  have hmax := max_sub_max_le_max 0 (g (max 0 y)) 0 (g (max 0 x))
  have hb : max 0 (g (max 0 y) - g (max 0 x)) ≤ d * (max 0 y - max 0 x) :=
    max_le (mul_nonneg hd hdiff) hh
  have hinput : max 0 y - max 0 x ≤ y - x := by
    have h := max_sub_max_le_max (0 : ℝ) y 0 x
    simpa only [sub_self, max_eq_right (sub_nonneg.mpr hxy)] using h
  exact (hmax.trans (by simpa only [sub_self] using hb)).trans
    (mul_le_mul_of_nonneg_left hinput hd)

/-- Simultaneous shape and one-sided slope controls. -/
structure Regular (d : ℝ) (L U : ℝ → ℝ) : Prop where
  density_nonneg : 0 ≤ d
  lower_nonneg : ∀ x, 0 ≤ L x
  lower_zero : ∀ x, x ≤ 0 → L x = 0
  lower_convex : ConvexOn ℝ Set.univ L
  lower_mono : Monotone L
  lower_lip : ∀ x y, x ≤ y → L y - L x ≤ d * (y - x)
  upper_zero : U 0 = 0
  upper_concave : ConcaveOn ℝ (Set.Ici 0) U
  upper_growth : ∀ x y, 0 ≤ x → x ≤ y → d * (y - x) ≤ U y - U x

theorem Regular.upper_nonneg {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ U x := by
  have hh := h.upper_growth 0 x (by norm_num) hx
  rw [h.upper_zero] at hh
  have := mul_nonneg h.density_nonneg hx
  linarith

theorem Regular.upper_mono {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U) :
    MonotoneOn U (Set.Ici 0) := by
  intro x hx y hy hxy
  have hh := h.upper_growth x y hx hxy
  have := mul_nonneg h.density_nonneg (sub_nonneg.mpr hxy)
  linarith

def stepLower (q : ℝ) (L U : ℝ → ℝ) : ℝ → ℝ :=
  clip (fun x => L x - U (1 + (x - 1) * q))

def stepUpper (q : ℝ) (L U : ℝ → ℝ) (x : ℝ) : ℝ :=
  U x - L ((x + 1) * q - 1)

theorem Regular.step {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Regular (d * (1 - q)) (stepLower q L U) (stepUpper q L U) := by
  let A (x : ℝ) := 1 + (x - 1) * q
  let B (x : ℝ) := (x + 1) * q - 1
  have hA (x : ℝ) (hx : 0 ≤ x) : 0 ≤ A x := by
    have hh := mul_nonneg hx hq0
    dsimp [A]
    nlinarith
  have hAm {x y : ℝ} (hxy : x ≤ y) : A x ≤ A y := by
    dsimp [A]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hq0]
  have hBm {x y : ℝ} (hxy : x ≤ y) : B x ≤ B y := by
    dsimp [B]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hq0]
  have hAc (x y a b : ℝ) (hab : a + b = 1) :
      A (a * x + b * y) = a * A x + b * A y := by dsimp [A]; nlinarith [hab]
  have hBc (x y a b : ℝ) (hab : a + b = 1) :
      B (a * x + b * y) = a * B x + b * B y := by dsimp [B]; nlinarith [hab]
  have hgc : ConvexOn ℝ (Set.Ici 0) (fun x => L x - U (A x)) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    have hl := h.lower_convex.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have hu := h.upper_concave.2 (hA x hx) (hA y hy) ha hb hab
    simp only [smul_eq_mul] at hl hu ⊢
    rw [← hAc x y a b hab] at hu
    nlinarith
  have hg0 : L 0 - U (A 0) ≤ 0 := by
    rw [h.lower_zero 0 le_rfl]
    exact sub_nonpos.mpr (h.upper_nonneg _ (hA 0 le_rfl))
  have hc := clip_regular hgc hg0
  have hd : 0 ≤ d * (1 - q) := mul_nonneg h.density_nonneg (sub_nonneg.mpr hq1)
  refine ⟨hd, hc.2.2.1, hc.2.2.2, hc.1, hc.2.1, ?_, ?_, ?_, ?_⟩
  · apply clip_lipschitz hd
    intro x y hx hxy
    have hl := h.lower_lip x y hxy
    have hu := h.upper_growth (A x) (A y) (hA x hx) (hAm hxy)
    change (L y - U (A y)) - (L x - U (A x)) ≤ d * (1 - q) * (y - x)
    dsimp [A] at hu
    nlinarith
  · dsimp [stepUpper]
    rw [h.upper_zero, h.lower_zero _ (by nlinarith)]
    ring
  · refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    have hu := h.upper_concave.2 hx hy ha hb hab
    have hl := h.lower_convex.2 (Set.mem_univ (B x)) (Set.mem_univ (B y)) ha hb hab
    simp only [smul_eq_mul] at hl hu ⊢
    rw [← hBc x y a b hab] at hl
    change a * (U x - L (B x)) + b * (U y - L (B y)) ≤
      U (a * x + b * y) - L (B (a * x + b * y))
    nlinarith
  · intro x y hx hxy
    have hu := h.upper_growth x y hx hxy
    have hl := h.lower_lip (B x) (B y) (hBm hxy)
    dsimp [B] at hl
    dsimp [stepUpper]
    nlinarith

def envelope (q : ℕ → ℝ) : ℕ → ℝ → ℝ × ℝ
  | 0, x => (max 0 x, x)
  | k + 1, x =>
      (stepLower (q k) (fun y => (envelope q k y).1) (fun y => (envelope q k y).2) x,
       stepUpper (q k) (fun y => (envelope q k y).1) (fun y => (envelope q k y).2) x)

def density (q : ℕ → ℝ) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (1 - q i)

theorem envelope_regular (q : ℕ → ℝ) (k : ℕ) (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) :
    Regular (density q k) (fun x => (envelope q k x).1) (fun x => (envelope q k x).2) := by
  induction k with
  | zero =>
    simp only [density, Finset.range_zero, Finset.prod_empty, envelope]
    refine ⟨by norm_num, fun x => le_max_left _ _, fun x hx => max_eq_left hx,
      (convexOn_const 0 convex_univ).sup (convexOn_id convex_univ),
      fun x y hxy => max_le_max_left 0 hxy, ?_, rfl, concaveOn_id (convex_Ici 0), ?_⟩
    · intro x y hxy
      have h := max_sub_max_le_max (0 : ℝ) y 0 x
      simpa only [sub_self, max_eq_right (sub_nonneg.mpr hxy), one_mul] using h
    · intro x y hx hxy
      simp
  | succ k ih =>
    have hh := (ih (fun i hi => hq i (by omega))).step (q k) (hq k (by omega)).1
      (hq k (by omega)).2
    simpa only [density, Finset.prod_range_succ, envelope] using hh

/-- The lower branch vanishes up to the number of sieve coordinates. This
justifies pruning without making a conjectural numerical assumption. -/
theorem lower_at_card_zero (q : ℕ → ℝ) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) : (envelope q k (k : ℝ)).1 = 0 := by
  induction k with
  | zero => simp [envelope]
  | succ k ih =>
    have hprev := ih (fun i hi => hq i (by omega))
    have hreg := envelope_regular q k (fun i hi => hq i (by omega))
    have hqk := hq k (by omega)
    have hl := hreg.lower_lip (k : ℝ) ((k : ℝ) + 1) (by linarith)
    rw [hprev] at hl
    let a := 1 + (((k : ℝ) + 1) - 1) * q k
    have ha : 1 ≤ a := by
      dsimp [a]
      have hh := mul_nonneg (Nat.cast_nonneg k) hqk.1
      nlinarith
    have hu := hreg.upper_growth 0 a (by norm_num) (by linarith)
    rw [hreg.upper_zero] at hu
    have hd := mul_le_mul_of_nonneg_left ha hreg.density_nonneg
    have hnonpos : (envelope q k ((k : ℝ) + 1)).1 - (envelope q k a).2 ≤ 0 := by
      nlinarith
    simp only [envelope, stepLower, clip, Nat.cast_add, Nat.cast_one,
      max_eq_right (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
    exact max_eq_left hnonpos

theorem lower_zero_of_le_card (q : ℕ → ℝ) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) (x : ℝ) (hx : x ≤ k) :
    (envelope q k x).1 = 0 := by
  have h := envelope_regular q k hq
  have hh := h.lower_mono hx
  rw [lower_at_card_zero q k hq] at hh
  exact le_antisymm hh (h.lower_nonneg x)

#print axioms envelope_regular
end Erdos970.ContinuousInterval
