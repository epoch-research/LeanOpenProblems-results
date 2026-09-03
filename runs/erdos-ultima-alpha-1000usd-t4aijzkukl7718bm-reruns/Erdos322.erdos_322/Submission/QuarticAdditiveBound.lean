import Submission.Spec
import Submission.BinaryNormBound

/-! Uniform subpolynomial bounds on the quartic additive-relation locus. -/
namespace Erdos322Research

private def fixedAdditiveQuarticReps (n : ℕ) : Finset (Fin 4 → Fin (n + 1)) :=
  Finset.univ.filter (fun a ↦ (∑ i, (a i : ℕ) ^ 4 = n) ∧
    (a 2 : ℕ) = (a 0 : ℕ) + (a 1 : ℕ))

def fixedAdditiveQuarticCount (n : ℕ) : ℕ := (fixedAdditiveQuarticReps n).card

private def outerNormPair {n : ℕ} (a : Fin 4 → Fin (n + 1)) : ℕ × ℕ :=
  ((a 3 : ℕ) ^ 2, (a 0 : ℕ) ^ 2 + (a 0 : ℕ) * (a 1 : ℕ) + (a 1 : ℕ) ^ 2)

private def innerNormPair {n : ℕ} (a : Fin 4 → Fin (n + 1)) : ℕ × ℕ :=
  (2 * (a 0 : ℕ) + (a 1 : ℕ), (a 1 : ℕ))

private lemma outerNormPair_mem {n : ℕ} {a : Fin 4 → Fin (n + 1)}
    (ha : a ∈ fixedAdditiveQuarticReps n) :
    outerNormPair a ∈ binaryNormSolutions 2 n := by
  simp only [fixedAdditiveQuarticReps, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  apply (mem_binaryNormSolutions (by decide) _).mpr
  dsimp [outerNormPair]
  have hsum := ha.1
  simp only [Fin.sum_univ_four, ha.2] at hsum
  calc
    ((a 3 : ℕ) ^ 2) ^ 2 + 2 * ((a 0 : ℕ) ^ 2 + (a 0 : ℕ) * (a 1 : ℕ) + (a 1 : ℕ) ^ 2) ^ 2 =
        (a 0 : ℕ) ^ 4 + (a 1 : ℕ) ^ 4 + ((a 0 : ℕ) + (a 1 : ℕ)) ^ 4 + (a 3 : ℕ) ^ 4 := by ring
    _ = n := hsum

private lemma outerNormPair_snd_le {n : ℕ} {a : Fin 4 → Fin (n + 1)}
    (ha : a ∈ fixedAdditiveQuarticReps n) : (outerNormPair a).2 ≤ n := by
  have h := (mem_binaryNormSolutions (by decide) _).mp (outerNormPair_mem ha)
  have hp := Nat.le_pow (by decide : 0 < 2) (a := (outerNormPair a).2)
  omega

private lemma innerNormPair_mem {n : ℕ} (a : Fin 4 → Fin (n + 1)) :
    innerNormPair a ∈ binaryNormSolutions 3 (4 * (outerNormPair a).2) := by
  apply (mem_binaryNormSolutions (by decide) _).mpr
  dsimp [innerNormPair, outerNormPair]
  ring

private lemma innerNormPair_fiber_injective {n : ℕ} (q : ℕ × ℕ) :
    Set.InjOn (innerNormPair (n := n))
      ((fixedAdditiveQuarticReps n).filter (fun a ↦ outerNormPair a = q) :
        Set (Fin 4 → Fin (n + 1))) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_filter, fixedAdditiveQuarticReps,
    Finset.mem_univ, true_and] at ha hb
  have h0 := congrArg Prod.fst hab
  have h1 := congrArg Prod.snd hab
  dsimp [innerNormPair] at h0 h1
  have ha0 : (a 0 : ℕ) = (b 0 : ℕ) := by omega
  have ha1 : (a 1 : ℕ) = (b 1 : ℕ) := h1
  have ha2 : (a 2 : ℕ) = (b 2 : ℕ) := by omega
  have h3 := congrArg Prod.fst (ha.2.trans hb.2.symm)
  have ha3 : (a 3 : ℕ) = (b 3 : ℕ) := Nat.pow_left_injective (by decide : 2 ≠ 0) h3
  funext i
  apply Fin.ext
  fin_cases i <;> assumption

/-- This bounds every quartic representation with `a₂ = a₀ + a₁`, allowing the
fourth coordinate and all norm factors to vary with the target. -/
theorem fixed_additive_quartic_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (fixedAdditiveQuarticCount n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  have hδ : 0 < ε / 2 := by linarith
  obtain ⟨A,hA,houter⟩ := binary_norm_subpolynomial (by decide : 2 ≤ 2) (ε / 2) hδ
  obtain ⟨B,hB,hinner⟩ := binary_norm_subpolynomial_up_to (by decide : 2 ≤ 3) (ε / 2) hδ
  refine ⟨A * B * (5 : ℝ) ^ (ε / 2), by positivity, fun n hn ↦ ?_⟩
  let S := fixedAdditiveQuarticReps n
  let I := S.image outerNormPair
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsubset : I ⊆ binaryNormSolutions 2 n := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    exact outerNormPair_mem ha
  have hfiber (q : ℕ × ℕ) (hq : q ∈ I) :
      (((S.filter (fun a ↦ outerNormPair a = q)).card : ℕ) : ℝ) ≤
        B * (4 * n + 1 : ℝ) ^ (ε / 2) := by
    have hcard : (S.filter (fun a ↦ outerNormPair a = q)).card ≤
        (binaryNormSolutions 3 (4 * q.2)).card := by
      apply Finset.card_le_card_of_injOn innerNormPair
      · intro a ha
        simp only [Finset.mem_coe, Finset.mem_filter] at ha
        have h := innerNormPair_mem a
        rwa [ha.2] at h
      · exact innerNormPair_fiber_injective q
    have hqle : q.2 ≤ n := by
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
      exact outerNormPair_snd_le ha
    calc
      (((S.filter (fun a ↦ outerNormPair a = q)).card : ℕ) : ℝ) ≤
          (binaryNormSolutions 3 (4 * q.2)).card := by exact_mod_cast hcard
      _ ≤ B * (4 * n + 1 : ℝ) ^ (ε / 2) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          hinner (4 * n) (4 * q.2) (by omega)
  have himage : (I.card : ℝ) ≤ A * (n : ℝ) ^ (ε / 2) := by
    have hc : (I.card : ℝ) ≤ (binaryNormSolutions 2 n).card := by
      exact_mod_cast Finset.card_le_card hsubset
    exact hc.trans (houter n hn)
  have hpow : (4 * n + 1 : ℝ) ^ (ε / 2) ≤
      (5 : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hnr.le]
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hp : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) = (n : ℝ) ^ ε := by
    rw [← Real.rpow_add hnr]
    congr 1
    ring
  calc
    (fixedAdditiveQuarticCount n : ℝ) =
        ∑ q ∈ I, (((S.filter (fun a ↦ outerNormPair a = q)).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image outerNormPair S
    _ ≤ ∑ q ∈ I, B * (4 * n + 1 : ℝ) ^ (ε / 2) := Finset.sum_le_sum hfiber
    _ = (I.card : ℝ) * (B * (4 * n + 1 : ℝ) ^ (ε / 2)) := by simp
    _ ≤ (A * (n : ℝ) ^ (ε / 2)) *
        (B * ((5 : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2))) := by
      exact mul_le_mul himage (mul_le_mul_of_nonneg_left hpow hB.le)
        (by positivity) (by positivity)
    _ = (A * B * (5 : ℝ) ^ (ε / 2)) * (n : ℝ) ^ ε := by
      calc
        _ = (A * B * (5 : ℝ) ^ (ε / 2)) *
          ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [hp]


private def permAdditiveQuarticReps (n : ℕ) (σ : Equiv.Perm (Fin 4)) :
    Finset (Fin 4 → Fin (n + 1)) :=
  Finset.univ.filter (fun a ↦ (∑ i, (a i : ℕ) ^ 4 = n) ∧
    (a (σ 2) : ℕ) = (a (σ 0) : ℕ) + (a (σ 1) : ℕ))

private lemma permAdditiveQuarticReps_card (n : ℕ) (σ : Equiv.Perm (Fin 4)) :
    (permAdditiveQuarticReps n σ).card = fixedAdditiveQuarticCount n := by
  classical
  apply Finset.card_nbij (fun a i ↦ a (σ i))
  · intro a ha
    simp only [Finset.mem_coe, permAdditiveQuarticReps, fixedAdditiveQuarticReps,
      Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨(Equiv.sum_comp σ (fun i ↦ (a i : ℕ) ^ 4)).trans ha.1, ha.2⟩
  · intro a ha b hb hab
    funext i
    have h := congrArg (fun f ↦ f (σ.symm i)) hab
    simpa using h
  · intro a ha
    simp only [Finset.mem_coe, fixedAdditiveQuarticReps,
      Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine ⟨fun i ↦ a (σ.symm i), ?_, ?_⟩
    · simp only [Finset.mem_coe, permAdditiveQuarticReps,
        Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      exact ⟨(Equiv.sum_comp σ.symm (fun i ↦ (a i : ℕ) ^ 4)).trans ha.1, ha.2⟩
    · funext i
      simp

/-- Some three distinct coordinates obey an additive relation. -/
def HasAdditiveTriple {n : ℕ} (a : Fin 4 → Fin (n + 1)) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), (a (σ 2) : ℕ) = (a (σ 0) : ℕ) + (a (σ 1) : ℕ)

instance {n : ℕ} (a : Fin 4 → Fin (n + 1)) : Decidable (HasAdditiveTriple a) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin 4),
    (a (σ 2) : ℕ) = (a (σ 0) : ℕ) + (a (σ 1) : ℕ)))

def additiveQuarticCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n + 1) ↦
    (∑ i, (a i : ℕ) ^ 4 = n) ∧ HasAdditiveTriple a)).card

def nonadditiveQuarticCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n + 1) ↦
    (∑ i, (a i : ℕ) ^ 4 = n) ∧ ¬ HasAdditiveTriple a)).card

lemma quartic_count_split (n : ℕ) :
    additiveQuarticCount n + nonadditiveQuarticCount n = Erdos322.representationCount 4 n := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
    (fun a : Fin 4 → Fin (n + 1) ↦ ∑ i, (a i : ℕ) ^ 4 = n)) HasAdditiveTriple
  simpa only [Finset.filter_filter, additiveQuarticCount, nonadditiveQuarticCount,
    Erdos322.representationCount] using h

lemma additiveQuarticCount_le (n : ℕ) :
    additiveQuarticCount n ≤ 24 * fixedAdditiveQuarticCount n := by
  classical
  have heq : Finset.univ.filter (fun a : Fin 4 → Fin (n + 1) ↦
      (∑ i, (a i : ℕ) ^ 4 = n) ∧ HasAdditiveTriple a) =
      Finset.univ.biUnion (permAdditiveQuarticReps n) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      permAdditiveQuarticReps, HasAdditiveTriple]
    tauto
  change (Finset.univ.filter _).card ≤ _
  rw [heq]
  have h := Finset.card_biUnion_le (s := (Finset.univ : Finset (Equiv.Perm (Fin 4))))
    (t := permAdditiveQuarticReps n)
  simp only [permAdditiveQuarticReps_card, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, smul_eq_mul] at h
  norm_num at h
  exact h

/-- All additive-triple quartic representations, not just the previously
constructed ones, satisfy a uniform subpolynomial bound. -/
theorem additive_quartic_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (additiveQuarticCount n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C,hC,hbound⟩ := fixed_additive_quartic_subpolynomial ε hε
  refine ⟨24 * C, by positivity, fun n hn ↦ ?_⟩
  calc
    (additiveQuarticCount n : ℝ) ≤ 24 * (fixedAdditiveQuarticCount n : ℝ) := by
      exact_mod_cast additiveQuarticCount_le n
    _ ≤ 24 * (C * (n : ℝ) ^ ε) := mul_le_mul_of_nonneg_left (hbound n hn) (by norm_num)
    _ = (24 * C) * (n : ℝ) ^ ε := by ring

/-- Deleting the entire additive-triple locus does not change whether the
quartic count has positive-power peaks. -/
theorem quartic_peaks_iff_nonadditive_peaks :
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < Erdos322.representationCount 4 n}.Infinite) ↔
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < nonadditiveQuarticCount n}.Infinite) := by
  constructor
  · rintro ⟨c,hc,hinf⟩
    have hhalf : 0 < c / 2 := by linarith
    obtain ⟨C,hC,hadd⟩ := additive_quartic_subpolynomial (c / 2) hhalf
    have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (c / 2)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop (C + 1))
    refine ⟨c / 2, hhalf, ?_⟩
    apply (hinf.diff (Set.finite_Iio (max N 1))).mono
    intro n hn
    have hlarge : max N 1 ≤ n := by
      have hnot := hn.2
      simpa only [Set.mem_Iio, not_lt] using hnot
    have hnpos : 0 < n := by omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hsmall := hadd n hnpos
    have hdom := hN n (by omega)
    have hsplit : (additiveQuarticCount n : ℝ) + nonadditiveQuarticCount n =
        Erdos322.representationCount 4 n := by exact_mod_cast quartic_count_split n
    have hp : ((n : ℝ) ^ (c / 2)) ^ 2 = (n : ℝ) ^ c := by
      rw [pow_two, ← Real.rpow_add hnr]
      congr 1
      ring
    have hmain := hn.1
    change (n : ℝ) ^ c < (Erdos322.representationCount 4 n : ℝ) at hmain
    change (n : ℝ) ^ (c / 2) < (nonadditiveQuarticCount n : ℝ)
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) ^ (c / 2) by positivity)
      (show 0 ≤ (n : ℝ) ^ (c / 2) - (C + 1) by linarith)]
  · rintro ⟨c,hc,hinf⟩
    refine ⟨c,hc,hinf.mono ?_⟩
    intro n hn
    have hle : (nonadditiveQuarticCount n : ℝ) ≤ Erdos322.representationCount 4 n := by
      exact_mod_cast (show nonadditiveQuarticCount n ≤ Erdos322.representationCount 4 n from
        by have := quartic_count_split n; omega)
    exact lt_of_lt_of_le hn hle

end Erdos322Research
