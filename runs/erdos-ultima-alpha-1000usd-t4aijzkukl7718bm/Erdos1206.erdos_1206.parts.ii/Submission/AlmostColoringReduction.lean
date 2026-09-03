import Submission.ColoringReduction

/-!
A global limitation on an almost-coloring approach: finite cube-Sidon coloring
on a set of upper natural density one already implies finite coloring of all
positive roots. No such coloring is constructed here.
-/

namespace Erdos1206

open Filter
open scoped Topology

lemma partialDensity_compl_add {S : Set ℕ} {N : ℕ} (hN : 0 < N) :
    Sᶜ.partialDensity Set.univ N + S.partialDensity Set.univ N = 1 := by
  have hc : (Sᶜ ∩ Set.Iio N).ncard + (S ∩ Set.Iio N).ncard = N := by
    have h := Set.ncard_diff_add_ncard_of_subset
      (s := S ∩ Set.Iio N) (t := Set.Iio N) Set.inter_subset_right
    have he : Set.Iio N \ (S ∩ Set.Iio N) = Sᶜ ∩ Set.Iio N := by
      ext n
      simp only [Set.mem_diff, Set.mem_Iio, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    simpa only [he, Nat.ncard_Iio] using h
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  rw [← add_div, ← Nat.cast_add, hc]
  exact div_self (by exact_mod_cast hN.ne')

lemma upperDensity_lt_one_of_compl_lowerDensity_pos {S : Set ℕ}
    (hS : 0 < Sᶜ.lowerDensity) : S.upperDensity < 1 := by
  obtain ⟨δ, hδ, hδS⟩ := exists_between hS
  have hlow : ∀ᶠ N : ℕ in atTop, δ < Sᶜ.partialDensity Set.univ N :=
    eventually_lt_of_lt_liminf hδS (isBoundedUnder_of ⟨0, fun _ => by positivity⟩)
  have hupp : ∀ᶠ N : ℕ in atTop, S.partialDensity Set.univ N ≤ 1 - δ := by
    filter_upwards [hlow, eventually_ge_atTop 1] with N hN hn
    have := partialDensity_compl_add (S := S) (show 0 < N by omega)
    linarith
  have hb : S.upperDensity ≤ 1 - δ :=
    limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun N =>
      (show (0 : ℝ) ≤ S.partialDensity Set.univ N by positivity))) hupp
  linarith

/-- Upper natural density one implies that every finite initial interval has
an integer dilation contained in the set. The dilation is not bounded uniformly
in the interval length. -/
lemma finite_prefix_dilation_of_upperDensity_one {S : Set ℕ}
    (hS : S.upperDensity = 1) (M : ℕ) :
    ∃ q : ℕ, 0 < q ∧ ∀ n : ℕ, 0 < n → n ≤ M → q * n ∈ S := by
  by_cases hM : M = 0
  · exact ⟨1, by omega, fun n hn hnM => False.elim (by omega)⟩
  by_contra h
  push_neg at h
  have hcover : ∀ q : ℕ, 0 < q →
      ∃ n : ℕ, 0 < n ∧ n ≤ M ∧ n * q ∈ Sᶜ := by
    intro q hq
    obtain ⟨n, hn, hnM, hqn⟩ := h q hq
    exact ⟨n, hn, hnM, by simpa [Nat.mul_comm] using hqn⟩
  have hpos := positive_lowerDensity_of_bounded_dilation_cover
    (Nat.pos_of_ne_zero hM) hcover
  have hlt := upperDensity_lt_one_of_compl_lowerDensity_pos hpos
  rw [hS] at hlt
  exact lt_irrefl _ hlt

/-- A finite cube-Sidon coloring on a set of upper density one can be pulled
back along larger and larger dilations and compactness then gives a coloring
of all positive natural numbers, with the same number of colors. -/
lemma goodCubeColoring_of_upperDensity_one {k : ℕ} {S : Set ℕ} {c : ℕ → Fin k}
    (hS : S.upperDensity = 1)
    (hc : ∀ i, IsSidon ((fun a : ℕ => a ^ 3) ''
      {n | 0 < n ∧ n ∈ S ∧ c n = i})) :
    ∃ d : ℕ → Fin k, GoodCubeColoring d := by
  classical
  choose q hq hqS using finite_prefix_dilation_of_upperDensity_one hS
  let f : ℕ → ℕ → Fin k := fun M n => c (q M * n)
  obtain ⟨d, φ, hφ, hd⟩ := SeqCompactSpace.tendsto_subseq f
  have hev (n : ℕ) : ∀ᶠ j : ℕ in atTop, f (φ j) n = d n := by
    have hn := (tendsto_pi_nhds.mp hd) n
    exact hn.eventually (isOpen_discrete {d n} |>.mem_nhds (by simp))
  refine ⟨d, ?_⟩
  intro i
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩ heq
  have hlarge : ∀ᶠ j : ℕ in atTop, a + b + r + s ≤ φ j :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop (a + b + r + s))
  obtain ⟨j, hj, hja, hjb, hjr, hjs⟩ :=
    (hlarge.and ((hev a).and ((hev b).and ((hev r).and (hev s))))).exists
  have heq' : (q (φ j) * a) ^ 3 + (q (φ j) * r) ^ 3 =
      (q (φ j) * b) ^ 3 + (q (φ j) * s) ^ 3 := by
    simpa only [mul_pow, ← mul_add] using
      congrArg (fun n : ℕ => q (φ j) ^ 3 * n) heq
  have h := hc i
    _ ⟨q (φ j) * a, ⟨Nat.mul_pos (hq _) ha.1, hqS _ a ha.1 (by omega),
        hja.trans ha.2⟩, rfl⟩
    _ ⟨q (φ j) * b, ⟨Nat.mul_pos (hq _) hb.1, hqS _ b hb.1 (by omega),
        hjb.trans hb.2⟩, rfl⟩
    _ ⟨q (φ j) * r, ⟨Nat.mul_pos (hq _) hr.1, hqS _ r hr.1 (by omega),
        hjr.trans hr.2⟩, rfl⟩
    _ ⟨q (φ j) * s, ⟨Nat.mul_pos (hq _) hs.1, hqS _ s hs.1 (by omega),
        hjs.trans hs.2⟩, rfl⟩ heq'
  simp only [mul_pow] at h
  have hq3 : 0 < q (φ j) ^ 3 := pow_pos (hq _) _
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left hq3 h₁, Nat.eq_of_mul_eq_mul_left hq3 h₂⟩
  · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left hq3 h₁, Nat.eq_of_mul_eq_mul_left hq3 h₂⟩

lemma finite_cube_coloring_upperDensity_one_suffices {k : ℕ} {S : Set ℕ}
    {c : ℕ → Fin k} (hS : S.upperDensity = 1)
    (hc : ∀ i, IsSidon ((fun a : ℕ => a ^ 3) ''
      {n | 0 < n ∧ n ∈ S ∧ c n = i})) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  obtain ⟨d, hd⟩ := goodCubeColoring_of_upperDensity_one hS hc
  exact finite_cube_coloring_suffices d hd

end Erdos1206

#print axioms Erdos1206.finite_prefix_dilation_of_upperDensity_one
#print axioms Erdos1206.goodCubeColoring_of_upperDensity_one
#print axioms Erdos1206.finite_cube_coloring_upperDensity_one_suffices
