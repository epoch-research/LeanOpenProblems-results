import Submission.WindowConstraintClosure

/-! A finite-period reduction for exact window closure. A periodic signed
distance admits all lower block bounds whose densities do not exceed its own.
The minimizing repetition index may then be restricted to one finite period.
No prime-residue realization is asserted. -/
namespace Erdos970.WindowConstraintClosure

lemma periodic_iterate {d : ℤ → ℤ} {Q : ℕ} {R : ℤ}
    (hper : ∀ z, d (z + Q) = d z + R) (z : ℤ) (t : ℕ) :
    d (z + (t : ℤ) * Q) = d z + (t : ℤ) * R := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he : z + ((t + 1 : ℕ) : ℤ) * Q = z + (t : ℤ) * Q + Q := by push_cast; ring
    rw [he, hper, ih]
    push_cast
    ring

lemma periodic_multiple {d : ℤ → ℤ} {Q : ℕ} {R : ℤ}
    (hzero : d 0 = 0) (hper : ∀ z, d (z + Q) = d z + R) (z : ℤ) :
    d (z * Q) = z * R := by
  cases z with
  | ofNat n => simpa only [zero_add, hzero] using periodic_iterate hper 0 n
  | negSucc n =>
    have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hn]
    have hh := periodic_iterate hper (-((n + 1 : ℕ) : ℤ) * Q) (n + 1)
    rw [show -((n + 1 : ℕ) : ℤ) * Q + ((n + 1 : ℕ) : ℤ) * Q = 0 by ring,
      hzero] at hh
    nlinarith

lemma IsDistance.nat_mul_le {d : ℤ → ℤ} (hd : IsDistance d) (z : ℤ) (t : ℕ) :
    d ((t : ℤ) * z) ≤ (t : ℤ) * d z := by
  induction t with
  | zero => simp [hd.zero]
  | succ t ih =>
    have hh := hd.subadd ((t : ℤ) * z) z
    have he : ((t + 1 : ℕ) : ℤ) * z = (t : ℤ) * z + z := by push_cast; ring
    rw [he]
    push_cast
    nlinarith

lemma IsDistance.periodic_slope_le {d : ℤ → ℤ} {Q : ℕ} {R : ℤ}
    (hd : IsDistance d) (hper : ∀ z, d (z + Q) = d z + R) (z : ℤ) :
    z * R ≤ (Q : ℤ) * d z := by
  have hh := hd.nat_mul_le z Q
  rw [mul_comm (Q : ℤ) z, periodic_multiple hd.zero hper] at hh
  exact hh

/-- The balanced cumulative profile at the prescribed rational density. -/
def balanced (Q : ℕ) (R : ℤ) (a : ℤ) : ℤ := a * R / Q

lemma balanced_admissible {d : ℤ → ℤ} {Q : ℕ} {R : ℤ}
    (hd : IsDistance d) (hQ : 0 < Q) (hper : ∀ z, d (z + Q) = d z + R) :
    Admissible d (balanced Q R) := by
  intro a z
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hh : (a + z) * R ≤ a * R + d z * Q := by
    have hs := hd.periodic_slope_le hper z
    nlinarith
  have hh' := Int.ediv_le_ediv hQ' hh
  rw [Int.add_mul_ediv_right _ _ hQ'.ne'] at hh'
  change (a + z) * R / Q - a * R / Q ≤ d z
  omega

lemma balanced_lowerBlock {Q : ℕ} {R g b : ℤ}
    (hQ : 0 < Q) (hb : b * Q ≤ g * R) : LowerBlock (balanced Q R) g b := by
  intro a
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hh : a * R + b * Q ≤ (a + g) * R := by nlinarith
  have hh' := Int.ediv_le_ediv hQ' hh
  rw [Int.add_mul_ediv_right _ _ hQ'.ne'] at hh'
  change b ≤ (a + g) * R / Q - a * R / Q
  omega

/-- Consistency of periodic distance constraints with one block lower bound is
exactly the elementary density inequality. -/
theorem periodic_consistent_iff {d : ℤ → ℤ} {Q g : ℕ} {R b : ℤ}
    (hd : IsDistance d) (hQ : 0 < Q) (hper : ∀ z, d (z + Q) = d z + R) :
    (∃ F : ℤ → ℤ, Admissible d F ∧ LowerBlock F g b) ↔ b * Q ≤ (g : ℤ) * R := by
  constructor
  · rintro ⟨F, hF, hB⟩
    have h₁ := hB.iterate 0 Q
    have h₂ := hF 0 ((Q : ℤ) * g)
    rw [mul_comm (Q : ℤ) (g : ℤ), periodic_multiple hd.zero hper] at h₂
    simp only [zero_add] at h₁ h₂
    rw [mul_comm (Q : ℤ) (g : ℤ)] at h₁
    nlinarith
  · intro hb
    exact ⟨balanced Q R, balanced_admissible hd hQ hper, balanced_lowerBlock hQ hb⟩

lemma periodic_candidate_mod {d : ℤ → ℤ} {Q g : ℕ} {R b : ℤ}
    (hper : ∀ z, d (z + Q) = d z + R) (z : ℤ) (t : ℕ) :
    d (z + (t : ℤ) * g) - (t : ℤ) * b =
      d (z + ((t % Q : ℕ) : ℤ) * g) - ((t % Q : ℕ) : ℤ) * b +
        ((t / Q : ℕ) : ℤ) * ((g : ℤ) * R - (Q : ℤ) * b) := by
  have ht : (t : ℤ) = (t % Q : ℕ) + (Q : ℤ) * (t / Q : ℕ) := by
    exact_mod_cast (Nat.mod_add_div t Q).symm
  have he : z + (t : ℤ) * g = z + ((t % Q : ℕ) : ℤ) * g +
      (((t / Q) * g : ℕ) : ℤ) * Q := by simp only [Nat.cast_mul]; rw [ht]; ring
  rw [he, periodic_iterate hper]
  simp only [Nat.cast_mul]
  rw [ht]
  ring

/-- The infinite minimum has a minimizer below Q. Thus a periodic profile can be
closed exactly by testing a finite period, rather than a heuristic lookahead. -/
theorem periodic_attained_below {d : ℤ → ℤ} {Q g : ℕ} {R b : ℤ}
    (hd : IsDistance d) (hQ : 0 < Q) (hper : ∀ z, d (z + Q) = d z + R)
    (hb : b * Q ≤ (g : ℤ) * R) (z : ℤ) :
    ∃ t : ℕ, t < Q ∧ addLower d g b z = d (z + (t : ℤ) * g) - (t : ℤ) * b := by
  have hF := balanced_admissible hd hQ hper
  have hB := balanced_lowerBlock hQ hb
  obtain ⟨t, ht⟩ := addLower_attained hF hB z
  refine ⟨t % Q, Nat.mod_lt _ hQ, ?_⟩
  apply le_antisymm
  · exact addLower_le_candidate hF hB z (t % Q)
  · rw [ht, periodic_candidate_mod hper z t]
    have hpos : 0 ≤ ((t / Q : ℕ) : ℤ) * ((g : ℤ) * R - (Q : ℤ) * b) :=
      mul_nonneg (Int.natCast_nonneg _) (by nlinarith)
    omega

theorem periodic_addLower_eq_finset_min {d : ℤ → ℤ} {Q g : ℕ} {R b : ℤ}
    (hd : IsDistance d) (hQ : 0 < Q) (hper : ∀ z, d (z + Q) = d z + R)
    (hb : b * Q ≤ (g : ℤ) * R) (z : ℤ) :
    addLower d g b z = (Finset.range Q).inf'
      ⟨0, Finset.mem_range.mpr hQ⟩
      (fun t : ℕ => d (z + (t : ℤ) * g) - (t : ℤ) * b) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro t ht
    exact addLower_le_candidate (balanced_admissible hd hQ hper)
      (balanced_lowerBlock hQ hb) z t
  · obtain ⟨t, ht, he⟩ := periodic_attained_below hd hQ hper hb z
    rw [he]
    exact Finset.inf'_le _ (Finset.mem_range.mpr ht)

/-- Closing preserves the exact period and its increment. Thus subsequent
consistent block constraints may use the same finite-period reduction. -/
theorem periodic_addLower {d : ℤ → ℤ} {Q g : ℕ} {R b : ℤ}
    (hd : IsDistance d) (hQ : 0 < Q) (hper : ∀ z, d (z + Q) = d z + R)
    (hb : b * Q ≤ (g : ℤ) * R) (z : ℤ) :
    addLower d g b (z + Q) = addLower d g b z + R := by
  have hF := balanced_admissible hd hQ hper
  have hB := balanced_lowerBlock hQ hb
  have candidate (t : ℕ) : d (z + Q + (t : ℤ) * g) - (t : ℤ) * b =
      d (z + (t : ℤ) * g) - (t : ℤ) * b + R := by
    rw [show z + Q + (t : ℤ) * g = (z + (t : ℤ) * g) + Q by ring, hper]
    ring
  apply le_antisymm
  · obtain ⟨t, ht⟩ := addLower_attained hF hB z
    have hh := addLower_le_candidate hF hB (z + Q) t
    rw [candidate, ← ht] at hh
    exact hh
  · obtain ⟨t, ht⟩ := addLower_attained hF hB (z + Q)
    have hh := addLower_le_candidate hF hB z t
    rw [candidate] at ht
    omega

/-- A proposed strengthened lower count has a finite certificate using fewer
than Q repetitions. -/
theorem periodic_lower_certificate_iff {d : ℤ → ℤ} {Q g : ℕ} {R b : ℤ}
    (hd : IsDistance d) (hQ : 0 < Q) (hper : ∀ z, d (z + Q) = d z + R)
    (hb : b * Q ≤ (g : ℤ) * R) (n : ℕ) (v : ℤ) :
    v ≤ -addLower d g b (-(n : ℤ)) ↔
      ∃ t : ℕ, t < Q ∧ v ≤ (t : ℤ) * b - d ((t : ℤ) * g - n) := by
  have hF := balanced_admissible hd hQ hper
  have hB := balanced_lowerBlock hQ hb
  constructor
  · intro hv
    obtain ⟨t, ht, he⟩ := periodic_attained_below hd hQ hper hb (-(n : ℤ))
    refine ⟨t, ht, ?_⟩
    rw [he] at hv
    rw [show (t : ℤ) * g - n = -(n : ℤ) + (t : ℤ) * g by ring]
    omega
  · rintro ⟨t, ht, hv⟩
    have hh := addLower_le_candidate hF hB (-(n : ℤ)) t
    rw [show (t : ℤ) * g - n = -(n : ℤ) + (t : ℤ) * g by ring] at hv
    omega

#print axioms periodic_consistent_iff
#print axioms periodic_addLower_eq_finset_min
#print axioms periodic_addLower
#print axioms periodic_lower_certificate_iff
end Erdos970.WindowConstraintClosure
