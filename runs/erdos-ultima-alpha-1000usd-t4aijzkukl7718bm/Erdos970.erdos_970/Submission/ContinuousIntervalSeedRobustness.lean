import Submission.ContinuousIntervalDilation

/-! A fixed, valid regular seed is dominated by a fixed dilation of the ordinary
recursion. This is a comparison theorem, not an asymptotic positivity theorem.
In particular, the tail recursion in this file has no chord patches. -/
namespace Erdos970.ContinuousInterval
open IntervalRescaling

lemma IntervalBounds.lower_at_card {L U : ℝ → ℝ} {p : ℕ → ℕ} {b : ℕ}
    (h : IntervalBounds L U 1 p b) : L b ≤ 0 := by
  have hz : count p (fun i => i) b b = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨hx, hs⟩ := Finset.mem_filter.mp hx
    exact hs x (Finset.mem_range.mp hx) (Nat.ModEq.refl x)
  simpa only [hz, Nat.cast_zero, one_mul] using (h b (fun i => i)).1

lemma IntervalBounds.one_le_upper_one {L U : ℝ → ℝ} {p : ℕ → ℕ} {b : ℕ}
    (h : IntervalBounds L U 1 p b) (hp : ∀ i < b, 1 < p i) : 1 ≤ U 1 := by
  have hs : ∀ i < b, ¬0 ≡ 1 [MOD p i] := by
    intro i hi hh
    have hh' : (0 : ℕ) = 1 := by
      simpa only [Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt (hp i hi)] using hh
    omega
  have hz : count p (fun _ => 1) b 1 = 1 := by
    unfold count
    rw [Finset.filter_eq_self.mpr]
    · exact Finset.card_range 1
    · intro x hx
      have hx0 : x = 0 := by have := Finset.mem_range.mp hx; omega
      simpa only [hx0] using hs
  simpa only [hz, Nat.cast_one, one_mul] using (h 1 (fun _ => 1)).2

lemma Regular.lower_le_delayed_line {d b : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (hb : L b ≤ 0) (x : ℝ) :
    L x ≤ d * max 0 (x - b) := by
  by_cases hx : x ≤ b
  · rw [max_eq_left (sub_nonpos.mpr hx), mul_zero]
    exact (h.lower_mono hx).trans hb
  · have hbx : b ≤ x := le_of_not_ge hx
    rw [max_eq_right (sub_nonneg.mpr hbx)]
    linarith [h.lower_lip b x hbx]

lemma Regular.min_le_upper {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (h1 : 1 ≤ U 1) (x : ℝ) (hx : 0 ≤ x) :
    min x (d * x + 1 - d) ≤ U x := by
  by_cases hx1 : x ≤ 1
  · have hh := h.upper_concave.2 (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      (show (1 : ℝ) ∈ Set.Ici 0 by simp) (sub_nonneg.mpr hx1) hx
      (show 1 - x + x = 1 by ring)
    simp only [smul_eq_mul, h.upper_zero, mul_zero, zero_add, mul_one] at hh
    have hmul := mul_le_mul_of_nonneg_left h1 hx
    exact (min_le_left _ _).trans (by nlinarith)
  · have hg := h.upper_growth 1 x (by norm_num) (le_of_not_ge hx1)
    exact (min_le_right _ _).trans (by nlinarith)

/-- The two unavoidable small-length constraints on a valid seed suffice for
comparison with a large enough dilation of the original prefix. -/
theorem regularSeed_dilation_exists (q : ℕ → ℝ) (b : ℕ) (L U : ℝ → ℝ)
    (hq : ∀ i < b, 0 ≤ q i ∧ q i ≤ 1) (hb : 0 < b)
    (hd0 : 0 < density q b) (hd1 : density q b < 1)
    (hr : Regular (density q b) L U) (hL : L b ≤ 0) (hU : 1 ≤ U 1) :
    ∃ c : ℝ, 1 ≤ c ∧
      Dominates (fun x => (envelope q b (c * x)).1 / c)
        (fun x => (envelope q b (c * x)).2 / c) L U := by
  let d := density q b
  let E := coarseError b
  have hdb : 0 < d * (b : ℝ) := mul_pos hd0 (by exact_mod_cast hb)
  have h1d : 0 < 1 - d := sub_pos.mpr hd1
  let c := max 1 (max (E / (d * b)) (E / (1 - d)))
  have hc : 1 ≤ c := le_max_left _ _
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hEc1 : E ≤ (d * b) * c := by
    rw [mul_comm]
    apply (div_le_iff₀ hdb).mp
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hEc2 : E ≤ (1 - d) * c := by
    rw [mul_comm]
    apply (div_le_iff₀ h1d).mp
    exact (le_max_right _ _).trans (le_max_right _ _)
  have ha := envelope_affine_bound q b hq
  have ho := envelope_regular q b hq
  refine ⟨c, hc, ?_, ?_⟩
  · intro x
    have hl := hr.lower_le_delayed_line hL x
    by_cases hx : x ≤ (b : ℝ)
    · rw [max_eq_left (sub_nonpos.mpr hx), mul_zero] at hl
      exact hl.trans (div_nonneg (ho.lower_nonneg _) hc0.le)
    · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge hx))] at hl
      have hmul := mul_le_mul_of_nonneg_right hl hc0.le
      have haL := ha.1 (c * x)
      apply (le_div_iff₀ hc0).mpr
      change L x * c ≤ _
      change E ≤ (density q b * b) * c at hEc1
      nlinarith
  · intro x hx
    have hu := hr.min_le_upper hU x hx
    apply le_trans _ hu
    apply le_min
    · apply (div_le_iff₀ hc0).mpr
      simpa only [mul_comm] using envelope_upper_le_input q b hq (c * x)
        (mul_nonneg hc0.le hx)
    · apply (div_le_iff₀ hc0).mpr
      have haU := ha.2 (c * x) (mul_nonneg hc0.le hx)
      change E ≤ (1 - density q b) * c at hEc2
      nlinarith

/-- Any valid fixed-prefix regular seed is dominated, at every unpatched tail
stage, by one fixed dilation of the original continuous recursion. -/
theorem fixedSeed_dilation (q : ℕ → ℝ) (p : ℕ → ℕ) (b : ℕ) (L U : ℝ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hb : 0 < b)
    (hd0 : 0 < density q b) (hd1 : density q b < 1)
    (hp : ∀ i < b, 1 < p i)
    (hr : Regular (density q b) L U) (hs : IntervalBounds L U 1 p b) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ t : ℕ,
      Dominates (fun x => (envelope q (b + t) (c * x)).1 / c)
        (fun x => (envelope q (b + t) (c * x)).2 / c)
        (seedRun q (fun _ => []) b L U t).1
        (seedRun q (fun _ => []) b L U t).2 := by
  obtain ⟨c, hc, hbase⟩ := regularSeed_dilation_exists q b L U
    (fun i _ => hq i) hb hd0 hd1 hr hs.lower_at_card (hs.one_le_upper_one hp)
  exact ⟨c, hc, fun t => seedRun_dilation_dominates q b t c L U hc
    (fun i _ => hq i) hbase⟩

/-- If any fixed valid regular seed proves uniform quadratic positivity by
unpatched tail iteration, then the ordinary recurrence already has uniform
quadratic positivity (possibly with a larger constant). -/
theorem quadratic_positive_of_fixedSeed (q : ℕ → ℝ) (p : ℕ → ℕ)
    (b : ℕ) (L U : ℝ → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hb : 0 < b)
    (hd0 : 0 < density q b) (hd1 : density q b < 1)
    (hp : ∀ i < b, 1 < p i)
    (hr : Regular (density q b) L U) (hs : IntervalBounds L U 1 p b)
    (hpos : ∃ D : ℝ, 0 < D ∧ ∀ t : ℕ, 0 < t →
      0 < (seedRun q (fun _ => []) b L U t).1 (D * (t : ℝ) ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      0 < (envelope q k (C * (k : ℝ) ^ 2)).1 := by
  obtain ⟨D, hD, hpos⟩ := hpos
  obtain ⟨c, hc, hdom⟩ := fixedSeed_dilation q p b L U hq hb hd0 hd1 hp hr hs
  have hc0 : 0 < c := by linarith
  let M := (coarseError b + 1) / density q b
  have hM : 0 < (envelope q b M).1 := by
    have ha := (envelope_affine_bound q b (fun i _ => hq i)).1 M
    have he : density q b * M - coarseError b = 1 := by
      dsimp [M]
      field_simp
      ring
    rw [he] at ha
    linarith
  let C := max (c * D) M
  have hC : 0 < C := (mul_pos hc0 hD).trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hx : 0 ≤ C * (k : ℝ) ^ 2 := mul_nonneg hC.le (sq_nonneg _)
  by_cases hkb : k ≤ b
  · have hMC : M ≤ C * (k : ℝ) ^ 2 := by
      have hMC : M ≤ C := le_max_right _ _
      nlinarith
    have hm := (envelope_regular q b (fun i _ => hq i)).lower_mono hMC
    exact (hM.trans_le hm).trans_le (envelope_lower_antitone q hq _ hx hkb)
  · let t := k - b
    have ht : 0 < t := by dsimp [t]; omega
    have he : b + t = k := by dsimp [t]; omega
    have hseed := (hpos t ht).trans_le ((hdom t).1 (D * (t : ℝ) ^ 2))
    have horig := (div_pos_iff_of_pos_right hc0).mp hseed
    rw [he] at horig
    have htk : (t : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k b
    have htk2 : (t : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg t) htk 2
    have harg : c * (D * (t : ℝ) ^ 2) ≤ C * (k : ℝ) ^ 2 := by
      have hCD : c * D ≤ C := le_max_left _ _
      calc
        _ = (c * D) * (t : ℝ) ^ 2 := by ring
        _ ≤ (c * D) * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left htk2 (mul_pos hc0 hD).le
        _ ≤ _ := mul_le_mul_of_nonneg_right hCD (sq_nonneg _)
    exact horig.trans_le ((envelope_regular q k (fun i _ => hq i)).lower_mono harg)

#print axioms quadratic_positive_of_fixedSeed
#print axioms regularSeed_dilation_exists
#print axioms fixedSeed_dilation
end Erdos970.ContinuousInterval
