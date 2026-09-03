import Submission.SummableDivisorCover

/-!
A finite cube-Sidon coloring of the squarefree integers would suffice for
Erdős 1206. The density extraction uses squarefree multipliers coprime to
successively longer finite prefixes. No such finite coloring is constructed.
-/

namespace Erdos1206
open Filter Finset
open scoped Classical Topology

private lemma sf_prefix_from_density {A : Set ℕ} (hA : 0 < A.lowerDensity) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ n : ℕ, δ * n ≤ ((A ∩ Set.Iio n).ncard : ℝ) + C := by
  let δ := A.lowerDensity / 2
  have hδ : 0 < δ := half_pos hA
  have hδA : δ < A.lowerDensity := half_lt_self hA
  have hev : ∀ᶠ n : ℕ in atTop, δ < A.partialDensity Set.univ n :=
    eventually_lt_of_lt_liminf hδA (isBoundedUnder_of ⟨0, fun _ => by positivity⟩)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine ⟨δ, hδ, δ * M, fun n => ?_⟩
  by_cases hn : n < M
  · have hle : (n : ℝ) ≤ M := by exact_mod_cast hn.le
    have hmul := mul_le_mul_of_nonneg_left hle hδ.le
    have hcard : (0 : ℝ) ≤ ((A ∩ Set.Iio n).ncard : ℝ) := by positivity
    linarith
  · by_cases hn0 : n = 0
    · subst n
      simpa using mul_nonneg hδ.le (Nat.cast_nonneg M)
    have hp := hM n (by omega)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio] at hp
    have hmul := (lt_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn0)).mp hp
    have hC : (0 : ℝ) ≤ δ * M := by positivity
    linarith

private lemma sf_density_from_prefix {A : Set ℕ} {δ C : ℝ} (hδ : 0 < δ)
    (h : ∀ n : ℕ, δ * n ≤ ((A ∩ Set.Iio n).ncard : ℝ) + C) :
    0 < A.lowerDensity := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * C / δ)
  have hev : ∀ᶠ n : ℕ in atTop, δ / 2 ≤ A.partialDensity Set.univ n := by
    apply eventually_atTop.mpr
    refine ⟨M + 1, fun n hn => ?_⟩
    have hn0 : 0 < n := by omega
    have hMn : (M : ℝ) < n := by exact_mod_cast (show M < n by omega)
    have hC : 2 * C < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp (hM.trans hMn)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn0)).mpr
    nlinarith [h n]
  have hlim : δ / 2 ≤ A.lowerDensity :=
    le_liminf_of_le (isCoboundedUnder_ge_of_le atTop
      (fun n => Set.partialDensity_le_one A Set.univ n)) hev
  exact (half_pos hδ).trans_le hlim

/-- A bounded family of dilations covering a positive-density source suffices;
the source need not be all positive integers. -/
lemma positive_density_of_dilation_cover_on {A D : Set ℕ} {B : ℕ}
    (hD : 0 < D.lowerDensity) (hB : 0 < B)
    (hcover : ∀ n ∈ D, ∃ k : ℕ, 0 < k ∧ k ≤ B ∧ k * n ∈ A) :
    0 < A.lowerDensity := by
  classical
  have hk : ∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ k ≤ B ∧ (n ∈ D → k * n ∈ A) := by
    intro n
    by_cases hn : n ∈ D
    · obtain ⟨k, hk, hkB, hkn⟩ := hcover n hn
      exact ⟨k, hk, hkB, fun _ => hkn⟩
    · exact ⟨1, by omega, hB, fun hh => (hn hh).elim⟩
  choose k hkpos hkB hkmem using hk
  have hcount (N : ℕ) : (D ∩ Set.Iio (N / B)).ncard ≤
      B * (A ∩ Set.Iio N).ncard := by
    let T := D ∩ Set.Iio (N / B)
    have hinj : Set.InjOn (fun n => (k n, k n * n)) T := by
      intro n hn m hm heq
      have hk' : k n = k m := congrArg Prod.fst heq
      have hmul : k n * n = k m * m := congrArg Prod.snd heq
      rw [← hk'] at hmul
      exact Nat.eq_of_mul_eq_mul_left (hkpos n) hmul
    have hmap : ∀ n ∈ T, (k n, k n * n) ∈ Set.Icc 1 B ×ˢ (A ∩ Set.Iio N) := by
      intro n hn
      refine ⟨⟨hkpos n, hkB n⟩, hkmem n hn.1, ?_⟩
      exact (Nat.mul_lt_mul_of_pos_left hn.2 (hkpos n)).trans_le
        ((Nat.mul_le_mul_right (N / B) (hkB n)).trans (Nat.mul_div_le N B))
    have hc := Set.ncard_le_ncard_of_injOn (fun n => (k n, k n * n)) hmap hinj
    have hcardB : (Set.Icc 1 B).ncard = B := by
      rw [← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]
      omega
    simpa only [Set.ncard_prod, hcardB] using hc
  obtain ⟨δ, hδ, C, hpre⟩ := sf_prefix_from_density hD
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  apply sf_density_from_prefix (δ := δ / ((B : ℝ) * B))
    (C := ((B : ℝ) * C + B * δ) / ((B : ℝ) * B)) (by positivity)
  intro N
  have hd := hpre (N / B)
  have hc : ((D ∩ Set.Iio (N / B)).ncard : ℝ) ≤
      B * (A ∩ Set.Iio N).ncard := by exact_mod_cast hcount N
  have hn : (N : ℝ) < (B : ℝ) * ((N / B : ℕ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ N hB
  have hbd : δ * N ≤ (B : ℝ) * B * (A ∩ Set.Iio N).ncard + B * C + B * δ := by
    nlinarith [mul_le_mul_of_nonneg_left (show δ * (N / B : ℕ) ≤ (B : ℝ) * (A ∩ Set.Iio N).ncard + C by linarith) hBR.le]
  convert div_le_div_of_nonneg_right hbd (mul_pos hBR hBR).le using 1 <;>
    field_simp
  all_goals ring

/-- Squarefree integers have positive lower density, by the summable square-divisor sieve. -/
lemma squarefree_lowerDensity_pos :
    0 < ({n : ℕ | Squarefree n} : Set ℕ).lowerDensity := by
  classical
  let f : ℕ → ℕ := fun m => (m + 2) ^ 2
  let B : Set ℕ := Set.range f
  have hinj : Function.Injective f := by
    intro m n h
    dsimp [f] at h
    nlinarith
  have h1 : 1 ∉ B := by
    rintro ⟨m, hm⟩
    dsimp [f] at hm
    have hh : (2 : ℕ) ^ 2 ≤ (m + 2) ^ 2 := Nat.pow_le_pow_left (show 2 ≤ m + 2 by omega) 2
    omega
  have hs : Summable (fun n : ℕ => if n ∈ B then (1 : ℝ) / n else 0) := by
    apply (hinj.summable_iff (f := fun n : ℕ => if n ∈ B then (1 : ℝ) / n else 0)
      (fun n hn => if_neg hn)).mp
    have hh : Summable (fun m : ℕ => (1 : ℝ) / (m + 2) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    convert hh using 1
    funext m
    simp [B, f]
  have heq : divisorAvoider B = {n : ℕ | Squarefree n} := by
    ext n
    constructor
    · rintro ⟨hn, h⟩
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro p hp hpd
      have hp2 : 2 ≤ p := hp.two_le
      have he : (p - 2 + 2) ^ 2 = p * p := by rw [Nat.sub_add_cancel hp2, pow_two]
      apply h (p * p) ⟨p - 2, he⟩ hpd
    · intro hn
      refine ⟨Nat.pos_of_ne_zero hn.ne_zero, ?_⟩
      rintro _ ⟨m, rfl⟩ hm
      have hunit := hn (m + 2) (by simpa only [f, pow_two] using hm)
      have hone : m + 2 = 1 := Nat.isUnit_iff.mp hunit
      omega
  rw [← heq]
  exact divisorAvoider_positive_density_of_summable h1 hs

/-- For each finite prefix there is a positive-density set of multipliers
preserving squarefreeness throughout that prefix. -/
lemma squarefree_prefix_multipliers (N : ℕ) :
    ∃ D : Set ℕ, 0 < D.lowerDensity ∧
      ∀ q ∈ D, 0 < q ∧ ∀ n : ℕ, Squarefree n → n ≤ N → Squarefree (q * n) := by
  let A : Set ℕ := {n | Squarefree n}
  let S := (range (N + 1)).filter (fun n => 1 < n)
  let D := A ∩ {q | ∀ b ∈ S, ¬ b ∣ q}
  have hclosed : PositiveDivisorClosed A := by
    intro n hn m hmn hm
    exact hn.squarefree_of_dvd hmn
  have hden : 0 < D.lowerDensity := remove_finite_divisors_preserves_positive_density
    hclosed (fun n hn => Nat.pos_of_ne_zero hn.ne_zero) squarefree_lowerDensity_pos S
    (fun b hb => (mem_filter.mp hb).2)
  refine ⟨D, hden, fun q hq => ⟨Nat.pos_of_ne_zero hq.1.ne_zero, ?_⟩⟩
  intro n hn hnN
  have hcop : Nat.Coprime q n := by
    apply Nat.coprime_of_dvd
    intro p hp hpq hpn
    have hpN := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hpn).trans hnN
    exact hq.2 p (mem_filter.mpr ⟨mem_range.mpr (by omega), hp.one_lt⟩) hpq
  exact (Nat.squarefree_mul hcop).mpr ⟨hq.1, hn⟩

/-- A coloring only of squarefree roots; no condition is imposed at other roots. -/
def GoodSquarefreeCubeColoring {ι : Type*} (c : ℕ → ι) : Prop :=
  ∀ i, IsSidon ((fun n : ℕ => n ^ 3) '' {n | Squarefree n ∧ c n = i})

private lemma erase_squarefree_color {k : ℕ} {c : ℕ → Fin k}
    {S : Finset (Fin k)} (hc : GoodSquarefreeCubeColoring c)
    (hS : ∀ n : ℕ, Squarefree n → c n ∈ S) (i : Fin k)
    (hlow : ¬ 0 < ({n : ℕ | Squarefree n ∧ c n = i} : Set ℕ).lowerDensity) :
    ∃ d : ℕ → Fin k, GoodSquarefreeCubeColoring d ∧
      ∀ n : ℕ, Squarefree n → d n ∈ S.erase i := by
  classical
  have hex (N : ℕ) : ∃ q : ℕ, 0 < q ∧
      (∀ n : ℕ, Squarefree n → n ≤ N + 1 → Squarefree (q * n)) ∧
      ∀ n : ℕ, Squarefree n → n ≤ N + 1 → c (q * n) ≠ i := by
    obtain ⟨D, hDden, hD⟩ := squarefree_prefix_multipliers (N + 1)
    by_contra hnot
    have hcover : ∀ q ∈ D, ∃ m : ℕ, 0 < m ∧ m ≤ N + 1 ∧
        m * q ∈ ({n : ℕ | Squarefree n ∧ c n = i} : Set ℕ) := by
      intro q hq
      have hh : ¬ ∀ n : ℕ, Squarefree n → n ≤ N + 1 → c (q * n) ≠ i := by
        intro hh
        exact hnot ⟨q, (hD q hq).1, (hD q hq).2, hh⟩
      push_neg at hh
      obtain ⟨m, hm, hmN, hmc⟩ := hh
      refine ⟨m, Nat.pos_of_ne_zero hm.ne_zero, hmN, ?_⟩
      simpa only [mul_comm] using And.intro ((hD q hq).2 m hm hmN) hmc
    exact hlow (positive_density_of_dilation_cover_on hDden (by omega) hcover)
  choose q hq hpres havoid using hex
  let f : ℕ → ℕ → Fin k := fun j n => c (q j * n)
  obtain ⟨d, φ, hφ, hd⟩ := SeqCompactSpace.tendsto_subseq f
  have hevent (n : ℕ) : ∀ᶠ j in atTop, f (φ j) n = d n := by
    have hn := (tendsto_pi_nhds.mp hd) n
    exact hn.eventually (isOpen_discrete {d n} |>.mem_nhds (by simp))
  refine ⟨d, ?_, ?_⟩
  · intro i
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩ heq
    have hlarge : ∀ᶠ j : ℕ in atTop, a + b + r + s ≤ φ j :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop (a + b + r + s))
    obtain ⟨j, hj, hja, hjb, hjr, hjs⟩ :=
      (hlarge.and ((hevent a).and ((hevent b).and ((hevent r).and (hevent s))))).exists
    change c (q (φ j) * a) = d a at hja
    change c (q (φ j) * b) = d b at hjb
    change c (q (φ j) * r) = d r at hjr
    change c (q (φ j) * s) = d s at hjs
    have heq' : (q (φ j) * a) ^ 3 + (q (φ j) * r) ^ 3 =
        (q (φ j) * b) ^ 3 + (q (φ j) * s) ^ 3 := by
      simpa only [mul_pow, ← mul_add] using congrArg (fun n : ℕ => q (φ j) ^ 3 * n) heq
    have hh := hc i
      _ ⟨q (φ j) * a, ⟨hpres (φ j) a ha.1 (by omega), hja.trans ha.2⟩, rfl⟩
      _ ⟨q (φ j) * b, ⟨hpres (φ j) b hb.1 (by omega), hjb.trans hb.2⟩, rfl⟩
      _ ⟨q (φ j) * r, ⟨hpres (φ j) r hr.1 (by omega), hjr.trans hr.2⟩, rfl⟩
      _ ⟨q (φ j) * s, ⟨hpres (φ j) s hs.1 (by omega), hjs.trans hs.2⟩, rfl⟩ heq'
    simp only [mul_pow] at hh
    have hqp : 0 < q (φ j) ^ 3 := pow_pos (hq (φ j)) _
    rcases hh with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left hqp h₁, Nat.eq_of_mul_eq_mul_left hqp h₂⟩
    · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left hqp h₁, Nat.eq_of_mul_eq_mul_left hqp h₂⟩
  · intro n hn
    have hlarge : ∀ᶠ j : ℕ in atTop, n ≤ φ j :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop n)
    obtain ⟨j, hj, hjn⟩ := ((hevent n).and hlarge).exists
    change c (q (φ j) * n) = d n at hj
    apply Finset.mem_erase.mpr
    constructor
    · rw [← hj]
      exact havoid (φ j) n hn (by omega)
    · rw [← hj]
      exact hS _ (hpres (φ j) n hn (by omega))

/-- Finite cube-Sidon coloring of the squarefree integers already suffices.
No coloring bound or coloring construction is asserted. -/
lemma finite_squarefree_cube_coloring_suffices {k : ℕ} (c : ℕ → Fin k)
    (hc : GoodSquarefreeCubeColoring c) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  classical
  have hmain : ∀ S : Finset (Fin k), ∀ c : ℕ → Fin k,
      GoodSquarefreeCubeColoring c → (∀ n : ℕ, Squarefree n → c n ∈ S) →
      ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
        IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro c hc hS
      let i := c 1
      by_cases hden : 0 < ({n : ℕ | Squarefree n ∧ c n = i} : Set ℕ).lowerDensity
      · refine ⟨{n : ℕ | Squarefree n ∧ c n = i}, ?_, hden, hc i⟩
        by_contra hfin
        have hz : ({n : ℕ | Squarefree n ∧ c n = i} : Set ℕ).lowerDensity = 0 :=
          (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
        rw [hz] at hden
        exact (lt_irrefl 0) hden
      · obtain ⟨d, hd, hdS⟩ := erase_squarefree_color hc hS i hden
        exact ih (S.erase i) (Finset.erase_ssubset (hS 1 (by simp))) d hd hdS
  exact hmain Finset.univ c hc (by simp)

/-- The number of colors must be bounded uniformly over all finite prefixes. -/
lemma finite_prefix_squarefree_cube_colorings_suffice {k : ℕ}
    (h : ∀ N : ℕ, ∃ c : ℕ → Fin k, ∀ i,
      IsSidon ((fun a : ℕ => a ^ 3) '' {n | Squarefree n ∧ n ≤ N ∧ c n = i})) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  classical
  choose f hf using h
  obtain ⟨c, φ, hφ, hc⟩ := SeqCompactSpace.tendsto_subseq f
  have hevent (n : ℕ) : ∀ᶠ j in atTop, f (φ j) n = c n := by
    have hn := (tendsto_pi_nhds.mp hc) n
    exact hn.eventually (isOpen_discrete {c n} |>.mem_nhds (by simp))
  apply finite_squarefree_cube_coloring_suffices c
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

#print axioms Erdos1206.finite_squarefree_cube_coloring_suffices
#print axioms Erdos1206.finite_prefix_squarefree_cube_colorings_suffice
