import Submission.TranslatedIntersectionSelection

/-! Short translated intersections. These are conditional reductions, not a
proof or disproof of the original square-Sidon conjecture. -/
namespace Erdos773.ShortTranslatedIntersection
open Finset
open TranslatedIntersectionSelection
set_option maxHeartbeats 1000000

/-- Cauchy--Schwarz applied to the partition into blocks of length `H`. -/
theorem block_pair_bound (N H K : ℕ) (hH : 0 < H) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N)
    (hK : ∀ h ∈ Icc 1 H, (overlap A h).card ≤ K) :
    A.card ^ 2 ≤ (N / H + 1) * (A.card + 2 * H * K) := by
  let C := range (N / H + 1)
  let Q := (A ×ˢ A).filter (fun p => p.1 / H = p.2 / H)
  let P := (A ×ˢ A).filter (fun p => p.1 < p.2 ∧ p.2 - p.1 ≤ H)
  have hC {a : ℕ} (ha : a ∈ A) : a / H ∈ C := by
    apply mem_range.mpr
    have := Nat.div_le_div_right (mem_Icc.mp (hA ha)).2 (c := H)
    omega
  have hsum : A.card = ∑ r ∈ C, (A.filter (fun a => a / H = r)).card :=
    card_eq_sum_card_fiberwise (fun _ ha => hC ha)
  have hsum2 : Q.card = ∑ r ∈ C, (A.filter (fun a => a / H = r)).card ^ 2 := by
    have hm : Set.MapsTo (fun p : ℕ × ℕ => p.1 / H) (Q : Set (ℕ × ℕ)) C := by
      intro p hp
      exact hC (mem_product.mp (mem_filter.mp hp).1).1
    rw [card_eq_sum_card_fiberwise hm]
    apply sum_congr rfl
    intro r hr
    have hf : Q.filter (fun p => p.1 / H = r) =
        (A.filter (fun a => a / H = r)) ×ˢ (A.filter (fun a => a / H = r)) := by
      ext p
      simp only [Q, mem_filter, mem_product]
      aesop
    rw [hf, card_product, pow_two]
  have hCS : A.card ^ 2 ≤ (N / H + 1) * Q.card := by
    rw [hsum2, hsum]
    simpa [C] using (sq_sum_le_card_mul_sum_sq (s := C)
      (f := fun r => (A.filter (fun a => a / H = r)).card))
  have hclose {a b : ℕ} (he : a / H = b / H) : b - a ≤ H := by
    have ha := Nat.mod_lt a hH
    have hb := Nat.mod_lt b hH
    have hda := Nat.mod_add_div a H
    have hdb := Nat.mod_add_div b H
    have hm := congrArg (H * ·) he
    dsimp only at hm
    omega
  have hcover : Q ⊆ A.diag ∪ (P ∪ P.image Prod.swap) := by
    intro p hp
    obtain ⟨hp, he⟩ := mem_filter.mp hp
    obtain ⟨ha, hb⟩ := mem_product.mp hp
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · exact mem_union_right _ (mem_union_left _
        (mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩, h, hclose he⟩))
    · exact mem_union_left _ (mem_diag.mpr ⟨ha, h⟩)
    · apply mem_union_right
      apply mem_union_right
      exact mem_image.mpr ⟨p.swap,
        mem_filter.mpr ⟨mem_product.mpr ⟨hb, ha⟩, h, hclose he.symm⟩,
        Prod.swap_swap p⟩
  have hQ : Q.card ≤ A.card + 2 * P.card := by
    have h1 := card_le_card hcover
    have h2 := card_union_le A.diag (P ∪ P.image Prod.swap)
    have h3 := card_union_le P (P.image Prod.swap)
    have h4 := card_image_le (s := P) (f := Prod.swap)
    rw [diag_card] at h2
    omega
  have hgap {p : ℕ × ℕ} (hp : p ∈ P) : p.2 - p.1 ∈ Icc 1 H := by
    obtain ⟨_, hlt, hle⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨by omega, hle⟩
  have hsumP : P.card = ∑ h ∈ Icc 1 H,
      (P.filter (fun p => p.2 - p.1 = h)).card :=
    card_eq_sum_card_fiberwise (fun _ hp => hgap hp)
  have hfiber (h : ℕ) (hh : h ∈ Icc 1 H) :
      (P.filter (fun p => p.2 - p.1 = h)).card ≤ K := by
    apply le_trans ?_ (hK h hh)
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      obtain ⟨hp, he⟩ := mem_filter.mp hp
      obtain ⟨hp, hlt, _⟩ := mem_filter.mp hp
      obtain ⟨ha, hb⟩ := mem_product.mp hp
      exact mem_filter.mpr ⟨ha, by convert hb using 1; omega⟩
    · intro p hp q hq he
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      have hp'' := (mem_filter.mp (mem_filter.mp hp).1).2.1
      have hq'' := (mem_filter.mp (mem_filter.mp hq).1).2.1
      apply Prod.ext he
      omega
  have hP : P.card ≤ H * K := by
    rw [hsumP]
    calc
      _ ≤ ∑ h ∈ Icc 1 H, K := sum_le_sum hfiber
      _ = _ := by simp
  apply hCS.trans
  apply Nat.mul_le_mul_left
  calc
    _ ≤ A.card + 2 * P.card := hQ
    _ ≤ A.card + 2 * (H * K) := Nat.add_le_add_left (Nat.mul_le_mul_left 2 hP) _
    _ = _ := by ring

/-- If the number of blocks is at most half of `|A|`, a short overlap has
size at least `|A|²/(8N)`. -/
theorem exists_short_overlap_of_blocks (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hblocks : 2 * (N / H + 1) ≤ A.card) :
    ∃ h ∈ Icc 1 H, A.card ^ 2 ≤ 8 * N * (overlap A h).card := by
  obtain ⟨h, hh, hmax⟩ := exists_max_image (Icc 1 H)
    (fun h => (overlap A h).card) (nonempty_Icc.mpr hH)
  refine ⟨h, hh, ?_⟩
  have hb := block_pair_bound N H _ hH A hA hmax
  have hLH : (N / H + 1) * H ≤ 2 * N := by
    have := Nat.div_mul_le_self N H
    nlinarith only [this, hHN]
  have hm := Nat.mul_le_mul_right A.card hblocks
  have hk := Nat.mul_le_mul_right (4 * (overlap A h).card) hLH
  nlinarith only [hb, hm, hk]

/-- A set of at least eight roots has a large overlap at a shift of order
`N/|A|`, rather than merely a shift bounded by `N`. -/
theorem exists_short_overlap (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hcard : 8 ≤ A.card) :
    ∃ h ∈ Icc 1 N,
      h * A.card ≤ 4 * N + A.card ∧
      A.card ^ 2 ≤ 8 * N * (overlap A h).card := by
  let H := 4 * N / A.card + 1
  have hM : 0 < A.card := by omega
  have hMN : A.card ≤ N := by simpa using card_le_card hA
  have hN : 0 < N := by omega
  have hH : 0 < H := Nat.succ_pos _
  have hstrict : 4 * N < A.card * H := by
    dsimp [H]
    have := Nat.mod_lt (4 * N) hM
    have := Nat.mod_add_div (4 * N) A.card
    nlinarith only [‹4 * N % A.card < A.card›, this]
  have hHsmall : H ≤ N := by
    have hh : 4 * N < N * A.card := by nlinarith only [hcard, hN]
    have hd : 4 * N / A.card < N := (Nat.div_lt_iff_lt_mul hM).mpr hh
    dsimp [H]
    omega
  have hblocks : 2 * (N / H + 1) ≤ A.card := by
    have hn := Nat.div_mul_le_self N H
    have hq : 4 * (N / H) < A.card := by
      apply (Nat.mul_lt_mul_right hH).mp
      nlinarith only [hn, hstrict]
    omega
  obtain ⟨h, hh, hb⟩ := exists_short_overlap_of_blocks N H hH hHsmall A hA hblocks
  refine ⟨h, mem_Icc.mpr ⟨(mem_Icc.mp hh).1, (mem_Icc.mp hh).2.trans hHsmall⟩, ?_, hb⟩
  have hm := Nat.mul_le_mul_right A.card (mem_Icc.mp hh).2
  have hd := Nat.div_mul_le_self (4 * N) A.card
  dsimp [H] at hm
  nlinarith only [hm, hd]

/-- The short-shift extraction preserves Sidonness of the entire union. -/
theorem extract_short_sidon_union (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hcard : 8 ≤ A.card)
    (hSidon : IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ)) :
    ∃ h ∈ Icc 1 N, ∃ B : Finset ℕ,
      B ∪ B.image (fun a => a + h) ⊆ A ∧
      h * A.card ≤ 4 * N + A.card ∧ A.card ^ 2 ≤ 8 * N * B.card ∧
      IsSidon ((((B ∪ B.image (fun a => a + h)).image
        (fun a => a ^ 2)) : Finset ℕ) : Set ℕ) := by
  obtain ⟨h, hh, hsmall, hlarge⟩ := exists_short_overlap N A hA hcard
  have hsub : overlap A h ∪ (overlap A h).image (fun a => a + h) ⊆ A :=
    union_subset (overlap_subset A h) (translate_overlap_subset A h)
  refine ⟨h, hh, overlap A h, hsub, hsmall, hlarge, ?_⟩
  apply Set.IsSidon.subset hSidon
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
  exact mem_image.mpr ⟨a, hsub ha, rfl⟩

/-- Explicit exponent bookkeeping: a near-linear set gives a near-linear
Sidon union with a subpower-sized selected translation. -/
theorem power_scale_extraction (N : ℕ) (η : ℝ) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N) (hcard : 8 ≤ A.card)
    (hlarge : (N : ℝ) ^ (1 - η) ≤ A.card)
    (hSidon : IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ)) :
    ∃ h ∈ Icc 1 N, ∃ B : Finset ℕ,
      B ∪ B.image (fun a => a + h) ⊆ A ∧
      (h : ℝ) ≤ 5 * (N : ℝ) ^ η ∧ (N : ℝ) ^ (1 - 2 * η) ≤ 8 * B.card ∧
      IsSidon ((((B ∪ B.image (fun a => a + h)).image
        (fun a => a ^ 2)) : Finset ℕ) : Set ℕ) := by
  obtain ⟨h, hh, B, hBA, hsmall, hbig, hs⟩ :=
    extract_short_sidon_union N A hA hcard hSidon
  have hMN : A.card ≤ N := by simpa using card_le_card hA
  have hN : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hMNr : (A.card : ℝ) ≤ N := by exact_mod_cast hMN
  have hsmallR : (h : ℝ) * A.card ≤ 4 * N + A.card := by exact_mod_cast hsmall
  have hbigR : (A.card : ℝ) ^ 2 ≤ 8 * N * B.card := by exact_mod_cast hbig
  refine ⟨h, hh, B, hBA, ?_, ?_, hs⟩
  · apply le_of_mul_le_mul_right (a := (N : ℝ) ^ (1 - η)) ?_
      (Real.rpow_pos_of_pos hN (1 - η))
    calc
      (h : ℝ) * (N : ℝ) ^ (1 - η) ≤ h * A.card :=
        mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg _)
      _ ≤ 5 * N := by linarith
      _ = (5 * (N : ℝ) ^ η) * (N : ℝ) ^ (1 - η) := by
        rw [mul_assoc, ← Real.rpow_add hN]
        have he : η + (1 - η) = 1 := by ring
        rw [he, Real.rpow_one]
  · apply le_of_mul_le_mul_left (a := (N : ℝ)) ?_ hN
    calc
      (N : ℝ) * (N : ℝ) ^ (1 - 2 * η) = ((N : ℝ) ^ (1 - η)) ^ 2 := by
        rw [← Real.rpow_mul_natCast hN.le]
        have he : (1 - η) * ((2 : ℕ) : ℝ) = 1 + (1 - 2 * η) := by
          norm_num
          ring
        rw [he, Real.rpow_add hN, Real.rpow_one]
      _ ≤ (A.card : ℝ) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hlarge _
      _ ≤ 8 * N * B.card := hbigR
      _ = (N : ℝ) * (8 * B.card) := by ring

#print axioms block_pair_bound
#print axioms exists_short_overlap_of_blocks
#print axioms exists_short_overlap
#print axioms extract_short_sidon_union
#print axioms power_scale_extraction
end Erdos773.ShortTranslatedIntersection
