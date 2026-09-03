import Submission.WindowCarryRigidity
import Submission.AffinePotentialCertificates

/-! No subcritical certificate of the full-window additive template.
This does not rule out arbitrary automata, nor settle Erdős 406. -/
namespace Erdos406WindowCarry
open Erdos406AffinePotential Erdos406AffineCertificate

noncomputable def windowScore (f : ℕ → ℝ) (B : ℕ) : ℕ → List ℕ → ℝ
  | _, [] => 0
  | s, d :: w => f (3 * s + d) + windowScore f B ((3 * s + d) % B) w

noncomputable def windowValue (r : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  windowScore f (3 ^ r) 0 (Nat.digits 3 n).reverse

lemma windowScore_coboundary (B : ℕ) (hB : 0 < B) (f g : ℕ → ℝ) (μ : ℝ)
    (hf : ∀ j < 3 * B, f j = μ + g (j % B) - g (j / 3))
    (s : ℕ) (hs : s < B) (w : List ℕ) (hw : ∀ d ∈ w, d < 3) :
    ∃ t < B, windowScore f B s w = μ * w.length + g t - g s := by
  induction w generalizing s with
  | nil => exact ⟨s, hs, by simp [windowScore]⟩
  | cons d w ih =>
    have hd := hw d (List.mem_cons_self ..)
    obtain ⟨t, ht, he⟩ := ih ((3 * s + d) % B) (Nat.mod_lt _ hB)
      (fun a ha => hw a (List.mem_cons_of_mem _ ha))
    refine ⟨t, ht, ?_⟩
    have hdiv : (3 * s + d) / 3 = s := by omega
    rw [windowScore, hf _ (by omega), hdiv, he]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- A bulk carry certificate forces the same upper slope on all digit words,
not just on the good ones. The slope is its all-zero-block weight. -/
theorem windowValue_global_bound (r : ℕ) (f P : ℕ → ℝ)
    (hstep : ∀ j < 12 * 3 ^ r,
      P (j % (4 * 3 ^ r)) ≤ P (j / 3) + f (j % (3 * 3 ^ r)) - f (j / 4)) :
    ∃ K : ℝ, ∀ n, windowValue r f n ≤ f 0 * (Nat.digits 3 n).length + K := by
  obtain ⟨g, μ, ν, hg, _hp⟩ := full_window_inequality_cohomology r f P hstep
  have hB : 0 < 3 ^ r := by positivity
  have hμ : f 0 = μ := by
    have hh := hg 0 (by positivity)
    simpa using hh
  obtain ⟨K, hK⟩ := (Set.finite_range (fun t : Fin (3 ^ r) => g t.val - g 0)).bddAbove
  refine ⟨K, ?_⟩
  intro n
  have hw : ∀ d ∈ (Nat.digits 3 n).reverse, d < 3 := by
    intro d hd
    exact Nat.digits_lt_base (by decide) (List.mem_reverse.mp hd)
  obtain ⟨t, ht, he⟩ := windowScore_coboundary (3 ^ r) hB f g μ hg 0 hB
    (Nat.digits 3 n).reverse hw
  have hb : g t - g 0 ≤ K := hK ⟨⟨t, ht⟩, rfl⟩
  rw [windowValue, he, List.length_reverse, hμ]
  linarith

lemma affine_global_bound_not_subcritical (V : ℕ → ℝ) (c K : ℝ) (hc : 0 ≤ c)
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1))
    (hbound : ∀ n, V n ≤ c * (Nat.digits 3 n).length + K) :
    ¬ c * Real.log 4 < Real.log 3 := by
  intro hcrit
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hgap : 0 < Real.log 3 - c * Real.log 4 := by linarith
  have horbit : ∀ t : ℕ, V 0 + (t : ℝ) ≤ V (orbit 4 1 t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hs := hgrow (orbit 4 1 t)
      rw [orbit_succ]
      push_cast
      linarith
  obtain ⟨t, ht⟩ := exists_nat_gt ((K - V 0) * Real.log 3 /
    (Real.log 3 - c * Real.log 4))
  have hlarge := (div_lt_iff₀ hgap).mp ht
  have hb := (horbit t).trans (hbound _)
  have hb' := mul_le_mul_of_nonneg_right hb hlog.le
  have hl := mul_le_mul_of_nonneg_left (orbit_length_log_le t) hc
  nlinarith

/-- No full-window additive certificate can meet the strict slope threshold.
The hypothesis `f 0 ≤ c` is forced by the good all-zero-block self-loop in
standard good-word cycle bounds. Growth is an explicit hypothesis here. -/
theorem no_subcritical_full_window (r : ℕ) (f P : ℕ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hzero : f 0 ≤ c)
    (hstep : ∀ j < 12 * 3 ^ r,
      P (j % (4 * 3 ^ r)) ≤ P (j / 3) + f (j % (3 * 3 ^ r)) - f (j / 4))
    (hgrow : ∀ n, windowValue r f n + 1 ≤ windowValue r f (4 * n + 1)) :
    ¬ c * Real.log 4 < Real.log 3 := by
  obtain ⟨K, hK⟩ := windowValue_global_bound r f P hstep
  apply affine_global_bound_not_subcritical (windowValue r f) c K hc hgrow
  intro n
  have hh := hK n
  have hm := mul_le_mul_of_nonneg_right hzero
    (show (0 : ℝ) ≤ (Nat.digits 3 n).length by positivity)
  linarith

theorem windowValue_bounded_correction (r : ℕ) (f P : ℕ → ℝ)
    (hstep : ∀ j < 12 * 3 ^ r,
      P (j % (4 * 3 ^ r)) ≤ P (j / 3) + f (j % (3 * 3 ^ r)) - f (j / 4)) :
    ∃ K : ℝ, ∀ n,
      |windowValue r f n - f 0 * (Nat.digits 3 n).length| ≤ K := by
  obtain ⟨g, μ, ν, hg, _hp⟩ := full_window_inequality_cohomology r f P hstep
  have hB : 0 < 3 ^ r := by positivity
  have hμ : f 0 = μ := by
    have hh := hg 0 (by positivity)
    simpa using hh
  obtain ⟨K, hK⟩ := (Set.finite_range
    (fun t : Fin (3 ^ r) => |g t.val - g 0|)).bddAbove
  refine ⟨K, ?_⟩
  intro n
  have hw : ∀ d ∈ (Nat.digits 3 n).reverse, d < 3 := by
    intro d hd
    exact Nat.digits_lt_base (by decide) (List.mem_reverse.mp hd)
  obtain ⟨t, ht, he⟩ := windowScore_coboundary (3 ^ r) hB f g μ hg 0 hB
    (Nat.digits 3 n).reverse hw
  have hb : |g t - g 0| ≤ K := hK ⟨⟨t, ht⟩, rfl⟩
  rw [windowValue, he, List.length_reverse, hμ]
  convert hb using 1
  congr 1
  ring

lemma zero_weight_le_good_slope (r : ℕ) (f P : ℕ → ℝ) (c K : ℝ)
    (hstep : ∀ j < 12 * 3 ^ r,
      P (j % (4 * 3 ^ r)) ≤ P (j / 3) + f (j % (3 * 3 ^ r)) - f (j / 4))
    (hgood : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      windowValue r f n ≤ c * (Nat.digits 3 n).length + K) :
    f 0 ≤ c := by
  obtain ⟨C, hC⟩ := windowValue_bounded_correction r f P hstep
  have hlong : ∀ L : ℕ, (f 0 - c) * ((L : ℝ) + 1) ≤ K + C := by
    intro L
    have hd : Nat.digits 3 (3 ^ L) = List.replicate L 0 ++ [1] := by
      have hh := Nat.digits_base_pow_mul (b := 3) (k := L) (m := 1)
        (by decide) (by decide)
      simpa only [Nat.mul_one,
        show Nat.digits 3 1 = [1] from by decide +kernel] using hh
    have hg : Nat.digits 3 (3 ^ L) ⊆ [0, 1] := by
      rw [hd]
      intro d hm
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hm
      rcases hm with ⟨_, rfl⟩ | rfl <;> simp
    have hu := hgood (3 ^ L) hg
    have hl := (abs_le.mp (hC (3 ^ L))).1
    rw [hd] at hu hl
    simp only [List.length_append, List.length_replicate, List.length_singleton,
      Nat.cast_add, Nat.cast_one] at hu hl
    linarith
  by_contra hn
  have hp : 0 < f 0 - c := by linarith
  obtain ⟨L, hL⟩ := exists_nat_gt ((K + C) / (f 0 - c))
  have hh := (div_lt_iff₀ hp).mp hL
  have hl := hlong L
  nlinarith

/-- Even if the linear upper bound is required only on canonical good words,
this full-window carry template cannot attain a subcritical slope. -/
theorem no_subcritical_full_window_good_bound (r : ℕ) (f P : ℕ → ℝ) (c K : ℝ)
    (hc : 0 ≤ c)
    (hstep : ∀ j < 12 * 3 ^ r,
      P (j % (4 * 3 ^ r)) ≤ P (j / 3) + f (j % (3 * 3 ^ r)) - f (j / 4))
    (hgrow : ∀ n, windowValue r f n + 1 ≤ windowValue r f (4 * n + 1))
    (hgood : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      windowValue r f n ≤ c * (Nat.digits 3 n).length + K) :
    ¬ c * Real.log 4 < Real.log 3 :=
  no_subcritical_full_window r f P c hc
    (zero_weight_le_good_slope r f P c K hstep hgood) hstep hgrow

#print axioms no_subcritical_full_window_good_bound
#print axioms windowValue_bounded_correction
#print axioms windowValue_global_bound
#print axioms no_subcritical_full_window
end Erdos406WindowCarry
