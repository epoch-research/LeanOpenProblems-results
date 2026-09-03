import Submission.ShortTranslatedIntersection

/-!
Iterating short overlaps extracts a subset-sum pattern with a large set of
base points. Subset sums are not assumed distinct. This is a structural
reduction only, not a settlement of Erdős 773.
-/
namespace Erdos773.IteratedShortTranslatedIntersection
open Finset TranslatedIntersectionSelection ShortTranslatedIntersection
set_option maxHeartbeats 1000000

/-- All subset sums of a list, without multiplicity. -/
def cube : List ℕ → Finset ℕ
  | [] => {0}
  | h :: hs => cube hs ∪ (cube hs).image (fun t => t + h)

lemma zero_mem_cube (hs : List ℕ) : 0 ∈ cube hs := by
  induction hs with
  | nil => simp [cube]
  | cons h hs ih => exact mem_union_left _ ih

lemma cube_le_sum {hs : List ℕ} {t : ℕ} (ht : t ∈ cube hs) : t ≤ hs.sum := by
  induction hs generalizing t with
  | nil => simpa [cube] using ht
  | cons h hs ih =>
    rcases mem_union.mp ht with ht | ht
    · exact (ih ht).trans (by simp)
    · obtain ⟨s, hs', rfl⟩ := mem_image.mp ht
      simpa [List.sum_cons, Nat.add_comm] using Nat.add_le_add_right (ih hs') h

lemma card_eight_of_threshold (N k : ℕ) (hN : 0 < N) (M : ℕ) (hMN : M ≤ N)
    (h : 8 * (8 * N) ^ (2 ^ k - 1) ≤ M ^ (2 ^ k)) : 8 ≤ M := by
  have hp : 0 < 2 ^ k := by positivity
  have hD : 0 < (8 * N) ^ (2 ^ k - 1) := by positivity
  have hM : M ≤ 8 * N := by omega
  have hpow := Nat.pow_le_pow_left hM (2 ^ k - 1)
  have he : M ^ (2 ^ k) = M * M ^ (2 ^ k - 1) := by
    conv_lhs => rw [show 2 ^ k = (2 ^ k - 1) + 1 by omega]
    rw [pow_succ, Nat.mul_comm]
  have hb : M ^ (2 ^ k) ≤ M * (8 * N) ^ (2 ^ k - 1) := by
    rw [he]
    exact Nat.mul_le_mul_left M hpow
  exact Nat.le_of_mul_le_mul_right (h.trans hb) hD

/-- A finite, explicitly quantitative short-shift cube extraction. -/
theorem exists_cube (N k : ℕ) (hN : 0 < N) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N)
    (hdense : 8 * (8 * N) ^ (2 ^ k - 1) ≤ A.card ^ (2 ^ k)) :
    ∃ (B : Finset ℕ) (hs : List ℕ),
      B ⊆ A ∧ hs.length = k ∧
      (∀ h ∈ hs, 0 < h ∧ h * B.card ≤ 5 * N) ∧
      (∀ b ∈ B, ∀ t ∈ cube hs, b + t ∈ A) ∧
      A.card ^ (2 ^ k) ≤ (8 * N) ^ (2 ^ k - 1) * B.card := by
  induction k generalizing A with
  | zero =>
    refine ⟨A, [], Subset.refl _, rfl, by simp, ?_, ?_⟩
    · intro b hb t ht
      have : t = 0 := by simpa [cube] using ht
      simpa [this] using hb
    · simp
  | succ k ih =>
    have hMN : A.card ≤ N := by simpa using card_le_card hA
    have hcard := card_eight_of_threshold N (k+1) hN A.card hMN hdense
    obtain ⟨h, hh, hsmall, hbig⟩ := exists_short_overlap N A hA hcard
    let C := overlap A h
    have hCA : C ⊆ A := overlap_subset A h
    have hp : 0 < 2 ^ k := by positivity
    have hexp : 2 ^ (k+1) - 1 = 2 ^ k + (2 ^ k - 1) := by
      rw [pow_succ]
      omega
    have hpow : A.card ^ (2 ^ (k+1)) ≤ (8 * N) ^ (2 ^ k) * C.card ^ (2 ^ k) := by
      have := Nat.pow_le_pow_left hbig (2 ^ k)
      simpa only [mul_pow, ← pow_mul, show 2 * 2 ^ k = 2 ^ (k+1) by rw [pow_succ]; omega]
        using this
    have hCdense : 8 * (8 * N) ^ (2 ^ k - 1) ≤ C.card ^ (2 ^ k) := by
      apply Nat.le_of_mul_le_mul_left ?_ (show 0 < (8 * N) ^ (2 ^ k) by positivity)
      calc
        (8 * N) ^ (2 ^ k) * (8 * (8 * N) ^ (2 ^ k - 1)) =
            8 * (8 * N) ^ (2 ^ (k+1) - 1) := by rw [hexp, pow_add]; ring
        _ ≤ A.card ^ (2 ^ (k+1)) := hdense
        _ ≤ _ := hpow
    obtain ⟨B, hs, hBC, hlen, hshifts, hpattern, hsize⟩ := ih C (hCA.trans hA) hCdense
    refine ⟨B, h :: hs, hBC.trans hCA, by simp [hlen], ?_, ?_, ?_⟩
    · intro s hs'
      rcases List.mem_cons.mp hs' with rfl | hs'
      · refine ⟨(mem_Icc.mp hh).1, ?_⟩
        calc
          s * B.card ≤ s * A.card := Nat.mul_le_mul_left s (card_le_card (hBC.trans hCA))
          _ ≤ 4 * N + A.card := hsmall
          _ ≤ 5 * N := by omega
      · exact hshifts s hs'
    · intro b hb t ht
      rcases mem_union.mp ht with ht | ht
      · exact hCA (hpattern b hb t ht)
      · obtain ⟨s, hs', rfl⟩ := mem_image.mp ht
        have := (mem_filter.mp (hpattern b hb s hs')).2
        simpa only [Nat.add_assoc] using this
    · calc
        A.card ^ (2 ^ (k+1)) ≤ (8 * N) ^ (2 ^ k) * C.card ^ (2 ^ k) := hpow
        _ ≤ (8 * N) ^ (2 ^ k) * ((8 * N) ^ (2 ^ k - 1) * B.card) :=
          Nat.mul_le_mul_left _ hsize
        _ = _ := by rw [hexp, pow_add]; ring

lemma sum_mem_cube (hs : List ℕ) : hs.sum ∈ cube hs := by
  induction hs with
  | nil => simp [cube]
  | cons h hs ih =>
    apply mem_union_right
    exact mem_image.mpr ⟨hs.sum, ih, by simp [Nat.add_comm]⟩

/-- Positive shifts yield at least `k+1` offsets, but not necessarily `2^k`. -/
lemma length_add_one_le_card_cube (hs : List ℕ) (hpos : ∀ h ∈ hs, 0 < h) :
    hs.length + 1 ≤ (cube hs).card := by
  induction hs with
  | nil => simp [cube]
  | cons h hs ih =>
    have hh : 0 < h := hpos h (by simp)
    have hnot : hs.sum + h ∉ cube hs := by
      intro ht
      have := cube_le_sum ht
      omega
    have hsub : insert (hs.sum + h) (cube hs) ⊆ cube (h :: hs) := by
      intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact mem_union_right _ (mem_image.mpr ⟨hs.sum, sum_mem_cube hs, rfl⟩)
      · exact mem_union_left _ ht
    have hc := card_le_card hsub
    rw [card_insert_of_notMem hnot] at hc
    have hi := ih (fun s hs' => hpos s (List.mem_cons_of_mem _ hs'))
    simp only [List.length_cons]
    omega

/-- The whole translated pattern, not merely each translate, is Sidon in squares. -/
theorem exists_sidon_cube (N k : ℕ) (hN : 0 < N) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N)
    (hdense : 8 * (8 * N) ^ (2 ^ k - 1) ≤ A.card ^ (2 ^ k))
    (hSidon : IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ)) :
    ∃ (B : Finset ℕ) (hs : List ℕ),
      B ⊆ A ∧ hs.length = k ∧ 8 ≤ B.card ∧
      (∀ h ∈ hs, 0 < h ∧ h * B.card ≤ 5 * N) ∧
      (B ×ˢ cube hs).image (fun p => p.1 + p.2) ⊆ A ∧
      A.card ^ (2 ^ k) ≤ (8 * N) ^ (2 ^ k - 1) * B.card ∧
      IsSidon (((((B ×ˢ cube hs).image (fun p => p.1 + p.2)).image
        (fun a => a ^ 2)) : Finset ℕ) : Set ℕ) := by
  obtain ⟨B, hs, hBA, hlen, hshifts, hpattern, hsize⟩ := exists_cube N k hN A hA hdense
  have hsub : (B ×ˢ cube hs).image (fun p => p.1 + p.2) ⊆ A := by
    intro a ha
    obtain ⟨⟨b,t⟩, hp, rfl⟩ := mem_image.mp ha
    exact hpattern b (mem_product.mp hp).1 t (mem_product.mp hp).2
  refine ⟨B, hs, hBA, hlen, ?_, hshifts, hsub, hsize, ?_⟩
  · apply Nat.le_of_mul_le_mul_right ?_ (show 0 < (8 * N) ^ (2 ^ k - 1) by positivity)
    simpa only [Nat.mul_comm] using hdense.trans hsize
  · apply Set.IsSidon.subset hSidon
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨a, hsub ha, rfl⟩

private lemma power_identity (N : ℝ) (hN : 0 < N) (η : ℝ) (r : ℕ) (hr : 0 < r) :
    (N ^ (1 - η)) ^ r = N ^ (r - 1) * N ^ (1 - (r : ℝ) * η) := by
  rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_natCast, ← Real.rpow_add hN]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ r)]
  norm_num
  ring

/-- Real-power bookkeeping with an explicit threshold. -/
theorem power_scale_extraction (N k : ℕ) (hN : 0 < N) (η : ℝ) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N) (hlarge : (N : ℝ) ^ (1 - η) ≤ A.card)
    (hthreshold : (8 : ℝ) ^ (2 ^ k) ≤ (N : ℝ) ^ (1 - (2 ^ k : ℕ) * η))
    (hSidon : IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ)) :
    ∃ (B : Finset ℕ) (hs : List ℕ),
      B ⊆ A ∧ hs.length = k ∧ 8 ≤ B.card ∧
      (∀ h ∈ hs, 0 < h ∧
        (h : ℝ) ≤ 5 * (8 : ℝ) ^ (2 ^ k - 1) * (N : ℝ) ^ ((2 ^ k : ℕ) * η)) ∧
      (B ×ˢ cube hs).image (fun p => p.1 + p.2) ⊆ A ∧
      (N : ℝ) ^ (1 - (2 ^ k : ℕ) * η) ≤ (8 : ℝ) ^ (2 ^ k - 1) * B.card ∧
      IsSidon (((((B ×ˢ cube hs).image (fun p => p.1 + p.2)).image
        (fun a => a ^ 2)) : Finset ℕ) : Set ℕ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < 2 ^ k := by positivity
  have hpow : ((N : ℝ) ^ (1 - η)) ^ (2 ^ k) ≤ (A.card : ℝ) ^ (2 ^ k) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hNr.le _) hlarge _
  have hdenseR : (8 : ℝ) * (8 * N) ^ (2 ^ k - 1) ≤ (A.card : ℝ) ^ (2 ^ k) := by
    calc
      (8 : ℝ) * (8 * N) ^ (2 ^ k - 1) =
          (N : ℝ) ^ (2 ^ k - 1) * (8 : ℝ) ^ (2 ^ k) := by
        have he8 : (8 : ℝ) ^ (2 ^ k) = (8 : ℝ) ^ (2 ^ k - 1) * 8 := by
          conv_lhs => rw [show 2 ^ k = (2 ^ k - 1) + 1 by omega]
          rw [pow_succ]
        rw [mul_pow, he8]
        ring
      _ ≤ (N : ℝ) ^ (2 ^ k - 1) * (N : ℝ) ^ (1 - (2 ^ k : ℕ) * η) :=
        mul_le_mul_of_nonneg_left hthreshold (by positivity)
      _ = ((N : ℝ) ^ (1 - η)) ^ (2 ^ k) := (power_identity _ hNr η _ hr).symm
      _ ≤ _ := hpow
  have hdense : 8 * (8 * N) ^ (2 ^ k - 1) ≤ A.card ^ (2 ^ k) := by exact_mod_cast hdenseR
  obtain ⟨B, hs, hBA, hlen, hB, hshifts, hsub, hsize, hS⟩ :=
    exists_sidon_cube N k hN A hA hdense hSidon
  have hsizeR : (A.card : ℝ) ^ (2 ^ k) ≤ (8 * N : ℝ) ^ (2 ^ k - 1) * B.card := by
    exact_mod_cast hsize
  have hBlower : (N : ℝ) ^ (1 - (2 ^ k : ℕ) * η) ≤ (8 : ℝ) ^ (2 ^ k - 1) * B.card := by
    apply le_of_mul_le_mul_left (a := (N : ℝ) ^ (2 ^ k - 1)) ?_ (by positivity)
    calc
      _ = ((N : ℝ) ^ (1 - η)) ^ (2 ^ k) := (power_identity _ hNr η _ hr).symm
      _ ≤ (A.card : ℝ) ^ (2 ^ k) := hpow
      _ ≤ _ := hsizeR
      _ = _ := by rw [mul_pow]; ring
  refine ⟨B, hs, hBA, hlen, hB, ?_, hsub, hBlower, hS⟩
  intro h hh
  obtain ⟨hpos, hsmall⟩ := hshifts h hh
  refine ⟨hpos, ?_⟩
  have hsmallR : (h : ℝ) * B.card ≤ 5 * N := by exact_mod_cast hsmall
  apply le_of_mul_le_mul_right (a := (N : ℝ) ^ (1 - (2 ^ k : ℕ) * η)) ?_ (by positivity)
  calc
    (h : ℝ) * (N : ℝ) ^ (1 - (2 ^ k : ℕ) * η) ≤
        h * ((8 : ℝ) ^ (2 ^ k - 1) * B.card) :=
      mul_le_mul_of_nonneg_left hBlower (Nat.cast_nonneg _)
    _ = (8 : ℝ) ^ (2 ^ k - 1) * (h * B.card) := by ring
    _ ≤ (8 : ℝ) ^ (2 ^ k - 1) * (5 * N) :=
      mul_le_mul_of_nonneg_left hsmallR (by positivity)
    _ = (5 * (8 : ℝ) ^ (2 ^ k - 1) * (N : ℝ) ^ ((2 ^ k : ℕ) * η)) *
        (N : ℝ) ^ (1 - (2 ^ k : ℕ) * η) := by
      rw [mul_assoc, ← Real.rpow_add hNr, add_sub_cancel, Real.rpow_one]
      ring

/-- For any fixed dimension with `2^k * η < 1`, the numerical threshold
holds eventually, uniformly over all candidate root sets. -/
theorem eventually_power_scale_extraction (k : ℕ) (η : ℝ)
    (hη : (2 ^ k : ℕ) * η < 1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ A : Finset ℕ,
      A ⊆ Icc 1 N → (N : ℝ) ^ (1 - η) ≤ A.card →
      IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ) →
      ∃ (B : Finset ℕ) (hs : List ℕ),
        B ⊆ A ∧ hs.length = k ∧ 8 ≤ B.card ∧
        (∀ h ∈ hs, 0 < h ∧
          (h : ℝ) ≤ 5 * (8 : ℝ) ^ (2 ^ k - 1) * (N : ℝ) ^ ((2 ^ k : ℕ) * η)) ∧
        (B ×ˢ cube hs).image (fun p => p.1 + p.2) ⊆ A ∧
        (N : ℝ) ^ (1 - (2 ^ k : ℕ) * η) ≤ (8 : ℝ) ^ (2 ^ k - 1) * B.card ∧
        IsSidon (((((B ×ˢ cube hs).image (fun p => p.1 + p.2)).image
          (fun a => a ^ 2)) : Finset ℕ) : Set ℕ) := by
  have hgrowth : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - (2 ^ k : ℕ) * η))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hgrowth.eventually_ge_atTop ((8 : ℝ) ^ (2 ^ k)),
    Filter.eventually_ge_atTop 1] with N hthreshold hN
  intro A hA hlarge hSidon
  exact power_scale_extraction N k (by omega) η A hA hlarge hthreshold hSidon

#print axioms exists_cube
#print axioms length_add_one_le_card_cube
#print axioms exists_sidon_cube
#print axioms power_scale_extraction
#print axioms eventually_power_scale_extraction
end Erdos773.IteratedShortTranslatedIntersection
