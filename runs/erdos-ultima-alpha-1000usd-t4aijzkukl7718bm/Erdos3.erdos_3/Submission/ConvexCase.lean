import FormalConjecturesUtil

/-! An unconditional special case: divergent reciprocal sums along increasing sequences
with nondecreasing gaps force arithmetic progressions of every finite length.
No reduction of the general conjecture to this special case is assumed. -/

namespace Erdos3ConvexCase

def gap (f : ℕ → ℕ) (n : ℕ) : ℕ := f (n + 1) - f n

lemma gap_pos {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) : 0 < gap f n := by
  have := hf (show n < n + 1 by omega)
  dsimp [gap]
  omega

lemma add_gap {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) :
    f n + gap f n = f (n + 1) := by
  have := hf.monotone (show n ≤ n + 1 by omega)
  dsimp [gap]
  omega

lemma linear_lower_bound {f : ℕ → ℕ} (hf : StrictMono f)
    (hg : Monotone (gap f)) (n m : ℕ) : f n + m * gap f n ≤ f (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hle := hg (show n ≤ n + m by omega)
    have heq := add_gap hf (n + m)
    have hind : f n + (m + 1) * gap f n ≤ f (n + m + 1) := by nlinarith
    simpa [Nat.add_assoc] using hind

/-- A fixed positive increase in the gap every K steps forces reciprocal convergence. -/
theorem summable_of_uniform_gap_increase {f : ℕ → ℕ} (hf : StrictMono f)
    (hg : Monotone (gap f)) {K : ℕ} (hK : 0 < K)
    (hincrease : ∀ n, gap f n < gap f (n + K)) :
    Summable (fun n : ℕ ↦ 1 / (f n : ℝ)) := by
  have hstrict : StrictMono (fun n : ℕ ↦ gap f (n * K)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    simpa [Nat.succ_mul] using hincrease (n * K)
  have hquad (n : ℕ) : n ^ 2 ≤ f (2 * K * n) := by
    have hgap : n ≤ gap f (n * K) := hstrict.id_le n
    calc
      n ^ 2 ≤ n * K * n := by
        have := Nat.mul_le_mul_left (n * n) (show 1 ≤ K by omega)
        nlinarith
      _ ≤ (n * K) * gap f (n * K) := Nat.mul_le_mul_left _ hgap
      _ ≤ f (n * K + n * K) := by
        have := linear_lower_bound hf hg (n * K) (n * K)
        omega
      _ = f (2 * K * n) := congrArg f (by ring)
  let u : ℕ → ℕ := fun n ↦ 2 * K * (n + 1)
  have huadd (n : ℕ) : u (n + 1) = u n + 2 * K := by dsimp [u]; ring
  have hup (n : ℕ) : 0 < u n := by dsimp [u]; positivity
  have hust : StrictMono u := by
    intro m n hmn
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
  have hudiff : SuccDiffBounded 1 u := by
    intro n
    simp only [one_smul]
    have h2 : u (n + 2) = u (n + 1) + 2 * K := by
      simpa [Nat.add_assoc] using huadd (n + 1)
    rw [h2, huadd n]
    simp
  have hs : Summable (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hsub : Summable (fun n : ℕ ↦ 1 / (f (u n) : ℝ)) := by
    apply hs.of_nonneg_of_le (fun _ ↦ by positivity)
    intro n
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hquad (n + 1)
  have himono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → 1 / (f n : ℝ) ≤ 1 / (f m : ℝ) := by
    intro m n hm hmn
    apply one_div_le_one_div_of_le
    · exact_mod_cast hm.trans_le (hf.id_le m)
    · exact_mod_cast hf.monotone hmn
  apply (summable_schlomilch_iff_of_nonneg (f := fun n ↦ 1 / (f n : ℝ))
    (fun _ ↦ by positivity) himono hup hust
    (by norm_num : (1 : ℕ) ≠ 0) hudiff).mp
  apply (hsub.mul_left ((2 * K : ℕ) : ℝ)).congr
  intro n
  rw [huadd]
  push_cast
  ring

/-- A divergent convex sequence must have arbitrarily long runs of equal gaps. -/
theorem divergence_forces_gap_runs {f : ℕ → ℕ} (hf : StrictMono f)
    (hg : Monotone (gap f)) (hs : ¬ Summable (fun n : ℕ ↦ 1 / (f n : ℝ))) (K : ℕ) :
    ∃ n : ℕ, ∀ i < K, gap f (n + i) = gap f n := by
  classical
  by_cases hK : K = 0
  · subst K
    exact ⟨0, by simp⟩
  by_contra! hno
  apply hs (summable_of_uniform_gap_increase hf hg (by omega : 0 < K) ?_)
  intro n
  obtain ⟨i, hi, hne⟩ := hno n
  have h1 := hg (show n ≤ n + i by omega)
  have h2 := hg (show n + i ≤ n + K by omega)
  omega

theorem divergent_convex_sequence_contains_ap {f : ℕ → ℕ} (hf : StrictMono f)
    (hg : Monotone (gap f)) (hs : ¬ Summable (fun n : ℕ ↦ 1 / (f n : ℝ))) (k : ℕ) :
    ∃ S ⊆ Set.range f, S.IsAPOfLength k := by
  obtain ⟨n, hn⟩ := divergence_forces_gap_runs hf hg hs k
  let a := f n
  let d := gap f n
  have hd : 0 < d := gap_pos hf n
  have hterms (i : ℕ) (hi : i ≤ k) : f (n + i) = a + i * d := by
    induction i with
    | zero => simp [a]
    | succ i ih =>
      have hi' : i < k := by omega
      have heq := add_gap hf (n + i)
      rw [hn i hi', ih (by omega)] at heq
      dsimp [d] at *
      have hres : f (n + i + 1) = a + (i + 1) * gap f n := by nlinarith
      simpa [Nat.add_assoc] using hres
  let g : ℕ → ℕ := fun i ↦ a + i * d
  have hgi : Function.Injective g := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  refine ⟨g '' Set.Iio k, ?_, a, d, ?_, ?_⟩
  · rintro x ⟨i, hi, rfl⟩
    exact ⟨n + i, hterms i hi.le⟩
  · change (g '' Set.Iio k).encard = (k : ℕ∞)
    rw [hgi.encard_image]
    exact Set.Nat.encard_range k
  · ext x
    simp [g]

/-- The original conclusion for a set enumerated by an increasing convex sequence. -/
theorem convex_range_case {f : ℕ → ℕ} (hf : StrictMono f)
    (hg : Monotone (gap f))
    (hs : ¬ Summable (fun a : Set.range f ↦ 1 / (a : ℝ))) :
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ Set.range f, S.IsAPOfLength k := by
  have hseq : ¬ Summable (fun n : ℕ ↦ 1 / (f n : ℝ)) := by
    intro h
    exact hs ((Equiv.ofInjective f hf.injective).summable_iff.mp h)
  apply Filter.frequently_atTop.mpr
  intro k
  exact ⟨k, le_rfl, divergent_convex_sequence_contains_ap hf hg hseq k⟩

#print axioms summable_of_uniform_gap_increase
#print axioms divergence_forces_gap_runs
#print axioms divergent_convex_sequence_contains_ap
#print axioms convex_range_case

end Erdos3ConvexCase
