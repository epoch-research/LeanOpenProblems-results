import Submission.Reductions

/-!
# A conditional bounded-average potential reduction

This file does not import the specification and does not prove its conjecture.
It proves the extraction implication and checks an obstruction to periodic
potential constructions. The unrestricted potential hypothesis is not assumed
as an axiom and is not proved here.
-/

namespace Erdos1206

/-- A potential separates all nontrivial equal cube pairs on `A`. -/
def CubePairSeparating (A : Finset ℕ) (w : ℕ → ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 →
    w a + w b = w c + w d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A level set of a separating potential is cube-Sidon. -/
theorem CubePairSeparating.fiber {A : Finset ℕ} {w : ℕ → ℕ}
    (h : CubePairSeparating A w) (v : ℕ) :
    CubeSidon (A.filter fun n => w n = v) := by
  intro a ha b hb c hc d hd heq
  simp only [Finset.mem_filter] at ha hb hc hd
  exact h a ha.1 b hb.1 c hc.1 d hd.1 heq (by
    rw [ha.2, hb.2, hc.2, hd.2])

/-- An elementary Markov bound, including the case `K = 0`. -/
theorem card_le_twice_low_potential (A : Finset ℕ) (w : ℕ → ℕ) (K : ℕ)
    (hmean : ∑ n ∈ A, w n ≤ K * A.card) :
    A.card ≤ 2 * (A.filter fun n => w n ≤ 2 * K).card := by
  classical
  let B := A.filter fun n => w n ≤ 2 * K
  let D := A.filter fun n => ¬w n ≤ 2 * K
  have hpartition : B.card + D.card = A.card := by
    exact Finset.card_filter_add_card_filter_not (fun n => w n ≤ 2 * K)
  have hsum : D.card * (2 * K + 1) ≤ ∑ n ∈ A, w n := by
    calc
      D.card * (2 * K + 1) = ∑ _n ∈ D, (2 * K + 1) := by simp
      _ ≤ ∑ n ∈ D, w n := Finset.sum_le_sum fun n hn => by
        have hn' := (Finset.mem_filter.mp hn).2
        omega
      _ ≤ ∑ n ∈ A, w n := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (by intros; omega)
  have hDB : D.card ≤ B.card := by
    by_contra h
    have hCB : B.card + 1 ≤ D.card := by omega
    have hm := Nat.mul_le_mul_left K hCB
    nlinarith
  change A.card ≤ 2 * B.card
  omega

/-- Bounded average plus pair separation gives an explicit proportional extraction. -/
theorem exists_cubeSidon_of_potential (A : Finset ℕ) (w : ℕ → ℕ) (K : ℕ)
    (hsep : CubePairSeparating A w)
    (hmean : ∑ n ∈ A, w n ≤ K * A.card) :
    ∃ B : Finset ℕ, B ⊆ A ∧ CubeSidon B ∧
      (A.card : ℝ) ≤ (2 * (2 * K + 1) : ℕ) * (B.card : ℝ) := by
  classical
  let D := A.filter fun n => w n ≤ 2 * K
  let T := Finset.range (2 * K + 1)
  have hD := card_le_twice_low_potential A w K hmean
  have hT : T.Nonempty := by
    refine ⟨0, ?_⟩
    simp [T]
  have hmaps : ∀ n ∈ D, w n ∈ T := by
    intro n hn
    have hn' := (Finset.mem_filter.mp hn).2
    simp only [T, Finset.mem_range]
    omega
  have hpos : (0 : ℝ) < (2 * K + 1 : ℕ) := by positivity
  have hpigeon : T.card • ((D.card : ℝ) / (2 * K + 1 : ℕ)) ≤
      (D.card : ℝ) := by
    simp only [T, Finset.card_range, nsmul_eq_mul]
    exact le_of_eq (mul_div_cancel₀ _ (ne_of_gt hpos))
  obtain ⟨v, hv, hcard⟩ :=
    Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps hT hpigeon
  refine ⟨D.filter fun n => w n = v,
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _), ?_, ?_⟩
  · apply (hsep.fiber v).subset
    intro n hn
    simp only [D, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1.1, hn.2⟩
  · have hcard' := (div_le_iff₀ hpos).mp hcard
    have hD' : (A.card : ℝ) ≤ 2 * (D.card : ℝ) := by exact_mod_cast hD
    push_cast at hcard' ⊢
    nlinarith

/-- The exact original conclusion, conditional on an explicitly supplied uniform
potential bound. This theorem does not assert that its hypothesis holds. -/
theorem erdos_1206_of_eventual_average_potential
    (h : ∃ K : ℕ, ∀ᶠ N in Filter.atTop, ∃ w : ℕ → ℕ,
      CubePairSeparating (Finset.Icc 1 N) w ∧
      ∑ n ∈ Finset.Icc 1 N, w n ≤ K * N) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in Filter.atTop, ∃ S : Finset ℕ,
      S ⊆ (Finset.Icc 1 N).image (fun n => n ^ 3) ∧
      IsSidon (S : Set ℕ) ∧ c * (N : ℝ) ≤ (S.card : ℝ) := by
  obtain ⟨K, hK⟩ := h
  let C : ℝ := (2 * (2 * K + 1) : ℕ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨1 / C, by positivity, ?_⟩
  filter_upwards [hK] with N hN
  obtain ⟨w, hsep, hmean⟩ := hN
  have hI : (Finset.Icc 1 N).card = N := by simp
  obtain ⟨B, hBI, hB, hcard⟩ := exists_cubeSidon_of_potential
    (Finset.Icc 1 N) w K hsep (by simpa only [hI] using hmean)
  apply (exists_sidon_subset_cubes_iff N ((1 / C) * (N : ℝ))).mpr
  refine ⟨B, hBI, hB, ?_⟩
  have hcard' : (N : ℝ) ≤ C * (B.card : ℝ) := by simpa [hI, C] using hcard
  rw [one_div_mul_eq_div]
  exact (div_le_iff₀ hC).mpr (by simpa [mul_comm] using hcard')

/-- Every positive modulus admits an explicit nontrivial cube collision whose
four roots all have residue one. No asymptotic counting input is used. -/
theorem exists_cube_collision_congruent_one (m : ℕ) (hm : 0 < m) :
    ∃ a b c d : ℕ, 0 < a ∧ a < b ∧ b < c ∧ c < d ∧
      a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3 ∧
      a % m = 1 % m ∧ b % m = 1 % m ∧
      c % m = 1 % m ∧ d % m = 1 % m := by
  refine ⟨576 * m ^ 3 + 220 * m ^ 2 + 26 * m + 1,
    920 * m ^ 3 + 272 * m ^ 2 + 28 * m + 1,
    1320 * m ^ 3 + 352 * m ^ 2 + 32 * m + 1,
    1424 * m ^ 3 + 380 * m ^ 2 + 34 * m + 1,
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [Nat.zero_le (m ^ 3)]
  · nlinarith [Nat.zero_le (m ^ 3)]
  · nlinarith [Nat.zero_le (m ^ 3)]
  · ring
  all_goals simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- A potential factoring through one fixed residue modulus cannot separate
cube pairs on all sufficiently long initial intervals. This does not rule out
nonperiodic, interval-dependent potentials. -/
theorem eventually_not_cubePairSeparating_residue (m : ℕ) (hm : 0 < m)
    (f : ℕ → ℕ) :
    ∀ᶠ N in Filter.atTop,
      ¬ CubePairSeparating (Finset.Icc 1 N) (fun n => f (n % m)) := by
  obtain ⟨a, b, c, d, ha, hab, hbc, hcd, heq, ham, hbm, hcm, hdm⟩ :=
    exists_cube_collision_congruent_one m hm
  filter_upwards [Filter.eventually_ge_atTop d] with N hN
  intro hsep
  have hmem : ∀ n : ℕ, a ≤ n → n ≤ d → n ∈ Finset.Icc 1 N := by
    intro n hna hnd
    simp only [Finset.mem_Icc]
    omega
  have hpairs := hsep a (hmem a (by omega) (by omega))
    d (hmem d (by omega) (by omega))
    b (hmem b (by omega) (by omega))
    c (hmem c (by omega) (by omega)) heq (by
      simp only [ham, hbm, hcm, hdm])
  rcases hpairs with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

end Erdos1206
