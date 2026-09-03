import FormalConjecturesUtil

/-! Verified auxiliary criteria; no finite cube-Sidon coloring is constructed here. -/

open Filter
open scoped Topology

namespace Erdos1206

lemma positive_lowerDensity_of_bounded_dilation_cover {A : Set ℕ} {B : ℕ}
    (hB : 0 < B)
    (hA : ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ k ≤ B ∧ k * n ∈ A) :
    0 < A.lowerDensity := by
  classical
  have hk : ∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ k ≤ B ∧ (0 < n → k * n ∈ A) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨k, hk, hkB, hkn⟩ := hA n hn
      exact ⟨k, hk, hkB, fun _ => hkn⟩
    · exact ⟨1, by omega, by omega, fun h => False.elim (hn h)⟩
  choose k hkpos hkB hkmem using hk
  have hcount (N : ℕ) : N ≤ B * B * ((A ∩ Set.Iio N).ncard) + 2 * B := by
    let T : Set ℕ := Set.Iio (N / B) \ {0}
    have hinj : Set.InjOn (fun n => (k n, k n * n)) T := by
      intro n hn m hm heq
      have hk' : k n = k m := congrArg Prod.fst heq
      have hmul : k n * n = k m * m := congrArg Prod.snd heq
      rw [← hk'] at hmul
      exact Nat.eq_of_mul_eq_mul_left (hkpos n) hmul
    have hmap : ∀ n ∈ T, (k n, k n * n) ∈ Set.Icc 1 B ×ˢ (A ∩ Set.Iio N) := by
      intro n hn
      have hn0 : 0 < n := Nat.pos_of_ne_zero (by simpa using hn.2)
      refine ⟨⟨hkpos n, hkB n⟩, hkmem n hn0, ?_⟩
      have hnN : n < N / B := hn.1
      have hlt : k n * n < k n * (N / B) := Nat.mul_lt_mul_of_pos_left hnN (hkpos n)
      exact hlt.trans_le ((Nat.mul_le_mul_right (N / B) (hkB n)).trans (Nat.mul_div_le N B))
    have hcard := Set.ncard_le_ncard_of_injOn (fun n => (k n, k n * n)) hmap hinj
    have hsmall : N / B ≤ T.ncard + 1 := by
      have h := Set.pred_ncard_le_ncard_diff_singleton (Set.Iio (N / B)) 0
      simp only [Nat.ncard_Iio] at h
      change N / B ≤ (Set.Iio (N / B) \ {0}).ncard + 1
      omega
    have hcardB : (Set.Icc 1 B).ncard = B := by
      rw [← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]
      omega
    rw [Set.ncard_prod, hcardB] at hcard
    have hdiv : N < B * (N / B + 1) := Nat.lt_mul_div_succ N hB
    have hmul := Nat.mul_le_mul_left B (hsmall.trans (Nat.add_le_add_right hcard 1))
    nlinarith
  let δ : ℝ := 1 / ((B : ℝ) * B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hevent : ∀ᶠ N : ℕ in atTop, δ / 2 ≤ A.partialDensity Set.univ N := by
    apply eventually_atTop.mpr
    refine ⟨4 * B + 1, fun N hN => ?_⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hcountR : (N : ℝ) ≤ (B : ℝ) * B * (A ∩ Set.Iio N).ncard + 2 * B := by
      exact_mod_cast hcount N
    have hNR : (4 : ℝ) * B < N := by exact_mod_cast (show 4 * B < N by omega)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    apply (le_div_iff₀ hNpos).mpr
    dsimp [δ]
    have hBR : (0 : ℝ) < (B : ℝ) * B := by positivity
    rw [div_div, one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) * B * 2)).mpr
    nlinarith
  have hlim : δ / 2 ≤ A.lowerDensity :=
    le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n => Set.partialDensity_le_one A Set.univ n)) hevent
  exact (half_pos hδ).trans_le hlim

/-- A coloring whose positive-root fibers have Sidon cubes. -/
def GoodCubeColoring {ι : Type*} (c : ℕ → ι) : Prop :=
  ∀ i, IsSidon ((fun a : ℕ => a ^ 3) '' {n | 0 < n ∧ c n = i})

lemma GoodCubeColoring.dilate {ι : Type*} {c : ℕ → ι}
    (hc : GoodCubeColoring c) {q : ℕ} (hq : 0 < q) :
    GoodCubeColoring (fun n => c (q * n)) := by
  intro i
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ heq
  have heq' : (q * a) ^ 3 + (q * d) ^ 3 = (q * b) ^ 3 + (q * e) ^ 3 := by
    simpa only [mul_pow, ← mul_add] using congrArg (fun n : ℕ => q ^ 3 * n) heq
  have h := hc i _ ⟨q * a, ⟨Nat.mul_pos hq ha.1, ha.2⟩, rfl⟩
    _ ⟨q * b, ⟨Nat.mul_pos hq hb.1, hb.2⟩, rfl⟩
    _ ⟨q * d, ⟨Nat.mul_pos hq hd.1, hd.2⟩, rfl⟩
    _ ⟨q * e, ⟨Nat.mul_pos hq he.1, he.2⟩, rfl⟩ heq'
  simp only [mul_pow] at h
  have hqp : 0 < q ^ 3 := pow_pos hq _
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left hqp h₁, Nat.eq_of_mul_eq_mul_left hqp h₂⟩
  · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left hqp h₁, Nat.eq_of_mul_eq_mul_left hqp h₂⟩

lemma goodCubeColoring_of_eventually_eq {ι : Type*} {f : ℕ → ℕ → ι} {c : ℕ → ι}
    (hf : ∀ j, GoodCubeColoring (f j))
    (hevent : ∀ n, ∀ᶠ j in atTop, f j n = c n) : GoodCubeColoring c := by
  intro i
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ heq
  obtain ⟨j, hja, hjb, hjd, hje⟩ :=
    ((hevent a).and ((hevent b).and ((hevent d).and (hevent e)))).exists
  exact hf j i _ ⟨a, ⟨ha.1, hja.trans ha.2⟩, rfl⟩
    _ ⟨b, ⟨hb.1, hjb.trans hb.2⟩, rfl⟩
    _ ⟨d, ⟨hd.1, hjd.trans hd.2⟩, rfl⟩
    _ ⟨e, ⟨he.1, hje.trans he.2⟩, rfl⟩ heq

lemma erase_color_of_no_bounded_dilation_cover {k : ℕ} {c : ℕ → Fin k}
    {S : Finset (Fin k)} (hc : GoodCubeColoring c)
    (hS : ∀ n : ℕ, 0 < n → c n ∈ S) (i : Fin k)
    (hcover : ¬ ∃ B : ℕ, ∀ n : ℕ, 0 < n →
      ∃ m : ℕ, 0 < m ∧ m ≤ B ∧ c (m * n) = i) :
    ∃ d : ℕ → Fin k, GoodCubeColoring d ∧
      ∀ n : ℕ, 0 < n → d n ∈ S.erase i := by
  classical
  push_neg at hcover
  choose q hq havoid using hcover
  let f : ℕ → ℕ → Fin k := fun j n => c (q j * n)
  obtain ⟨d, φ, hφ, hd⟩ := SeqCompactSpace.tendsto_subseq f
  have hevent (n : ℕ) : ∀ᶠ j in atTop, f (φ j) n = d n := by
    have hn := (tendsto_pi_nhds.mp hd) n
    exact hn.eventually (isOpen_discrete {d n} |>.mem_nhds (by simp))
  refine ⟨d, goodCubeColoring_of_eventually_eq
    (fun j => hc.dilate (hq (φ j))) hevent, ?_⟩
  intro n hn
  have hlarge : ∀ᶠ j : ℕ in atTop, n ≤ φ j :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop n)
  obtain ⟨j, hj, hjn⟩ := ((hevent n).and hlarge).exists
  change c (q (φ j) * n) = d n at hj
  apply Finset.mem_erase.mpr
  constructor
  · rw [← hj, Nat.mul_comm]
    exact havoid (φ j) n hn hjn
  · rw [← hj]
    exact hS _ (Nat.mul_pos (hq (φ j)) hn)

lemma bounded_dilation_cover_of_finite_cube_coloring {k : ℕ} (c : ℕ → Fin k)
    (hc : GoodCubeColoring c) :
    ∃ A : Set ℕ, IsSidon ((fun a : ℕ => a ^ 3) '' A) ∧
      ∃ B : ℕ, 0 < B ∧ ∀ n : ℕ, 0 < n →
        ∃ m : ℕ, 0 < m ∧ m ≤ B ∧ m * n ∈ A := by
  classical
  have hmain : ∀ S : Finset (Fin k), ∀ c : ℕ → Fin k,
      GoodCubeColoring c → (∀ n : ℕ, 0 < n → c n ∈ S) →
      ∃ A : Set ℕ, IsSidon ((fun a : ℕ => a ^ 3) '' A) ∧
        ∃ B : ℕ, 0 < B ∧ ∀ n : ℕ, 0 < n →
          ∃ m : ℕ, 0 < m ∧ m ≤ B ∧ m * n ∈ A := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro c hc hS
      let i := c 1
      by_cases hcover : ∃ B : ℕ, ∀ n : ℕ, 0 < n →
          ∃ m : ℕ, 0 < m ∧ m ≤ B ∧ c (m * n) = i
      · obtain ⟨B, hB⟩ := hcover
        have hBpos : 0 < B := by
          obtain ⟨m, hm, hmB, _⟩ := hB 1 (by omega)
          omega
        refine ⟨{n | 0 < n ∧ c n = i}, hc i, B, hBpos, ?_⟩
        intro n hn
        obtain ⟨m, hm, hmB, hmi⟩ := hB n hn
        exact ⟨m, hm, hmB, Nat.mul_pos hm hn, hmi⟩
      · obtain ⟨d, hd, hdS⟩ := erase_color_of_no_bounded_dilation_cover hc hS i hcover
        exact ih (S.erase i) (Finset.erase_ssubset (hS 1 (by omega))) d hd hdS
  exact hmain Finset.univ c hc (by simp)

lemma finite_cube_coloring_suffices {k : ℕ} (c : ℕ → Fin k)
    (hc : GoodCubeColoring c) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  obtain ⟨A, hsid, B, hB, hcover⟩ := bounded_dilation_cover_of_finite_cube_coloring c hc
  have hpos := positive_lowerDensity_of_bounded_dilation_cover hB hcover
  refine ⟨A, ?_, hpos, hsid⟩
  by_contra hfin
  have hzero : A.lowerDensity = 0 :=
    (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
  simp [hzero] at hpos

/-- A uniform bound on the number of colors in finite prefixes suffices.
The existence of such a bound is not proved here. -/
lemma finite_prefix_cube_colorings_suffice {k : ℕ}
    (h : ∀ N : ℕ, ∃ c : ℕ → Fin k,
      ∀ i, IsSidon ((fun a : ℕ => a ^ 3) '' {n | 0 < n ∧ n ≤ N ∧ c n = i})) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  classical
  choose f hf using h
  obtain ⟨c, φ, hφ, hc⟩ := SeqCompactSpace.tendsto_subseq f
  have hevent (n : ℕ) : ∀ᶠ j in atTop, f (φ j) n = c n := by
    have hn := (tendsto_pi_nhds.mp hc) n
    exact hn.eventually (isOpen_discrete {c n} |>.mem_nhds (by simp))
  apply finite_cube_coloring_suffices c
  intro i
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ heq
  have hlarge : ∀ᶠ j : ℕ in atTop, a + b + d + e ≤ φ j :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop (a + b + d + e))
  obtain ⟨j, hj, hja, hjb, hjd, hje⟩ :=
    (hlarge.and ((hevent a).and ((hevent b).and ((hevent d).and (hevent e))))).exists
  exact hf (φ j) i _ ⟨a, ⟨ha.1, by omega, hja.trans ha.2⟩, rfl⟩
    _ ⟨b, ⟨hb.1, by omega, hjb.trans hb.2⟩, rfl⟩
    _ ⟨d, ⟨hd.1, by omega, hjd.trans hd.2⟩, rfl⟩
    _ ⟨e, ⟨he.1, by omega, hje.trans he.2⟩, rfl⟩ heq

end Erdos1206
