import Submission.ShortTranslatedIntersection
import Submission.SimultaneousAffineSquares

/-! Normalizing a selected short translation to adjacent indices. None of the
statements here asserts an upper bound for arbitrary adjacent-index sets. -/
namespace Erdos773.AdjacentQuadraticReduction
open Finset
open SimultaneousAffineSquares
set_option maxHeartbeats 1000000

def adjacent (C : Finset ℕ) : Finset ℕ := C ∪ C.image (fun n => n + 1)

/-- Selecting one residue class and dividing by the shift loses a factor at
most equal to the shift, and turns it into adjacency of indices. -/
theorem normalize_union (q : ℕ) (hq : 0 < q) (A B : Finset ℕ)
    (hBA : B ∪ B.image (fun a => a + q) ⊆ A) :
    ∃ r < q, ∃ C : Finset ℕ,
      B.card ≤ q * C.card ∧ (adjacent C).image (fun n => q * n + r) ⊆ A := by
  let D (r : ℕ) := B.filter (fun a => a % q = r)
  obtain ⟨r, hr, hmax⟩ := exists_max_image (range q) (fun r => (D r).card)
    (nonempty_range_iff.mpr hq.ne')
  let C := (D r).image (fun a => a / q)
  have hDC : C.card = (D r).card := by
    apply card_image_of_injOn
    intro a ha b hb he
    dsimp only at he
    have har := (mem_filter.mp ha).2
    have hbr := (mem_filter.mp hb).2
    have hda := Nat.mod_add_div a q
    have hdb := Nat.mod_add_div b q
    rw [har] at hda
    rw [hbr, ← he] at hdb
    omega
  have hsum : B.card = ∑ s ∈ range q, (D s).card :=
    card_eq_sum_card_fiberwise (fun a _ => mem_range.mpr (Nat.mod_lt a hq))
  have hcard : B.card ≤ q * C.card := by
    rw [hsum, hDC]
    calc
      _ ≤ ∑ s ∈ range q, (D r).card := sum_le_sum hmax
      _ = _ := by simp
  have hroot {n : ℕ} (hn : n ∈ C) : q * n + r ∈ B := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
    have har := (mem_filter.mp ha).2
    have he := Nat.mod_add_div a q
    rw [har, add_comm] at he
    rw [he]
    exact (mem_filter.mp ha).1
  refine ⟨r, mem_range.mp hr, C, hcard, ?_⟩
  intro a ha
  obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
  rcases mem_union.mp hn with hn | hn
  · exact hBA (mem_union_left _ (hroot hn))
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    have hh := hBA (mem_union_right _ (mem_image.mpr
      ⟨q * m + r, hroot hm, rfl⟩))
    have he : q * (m + 1) + r = (q * m + r) + q := by ring
    rw [he]
    exact hh

/-- Removing the common factor and constant from affine squares preserves
Sidonness of their normalized quadratic values. -/
theorem normalized_sidon (q r : ℕ) (hq : 0 < q) (C : Finset ℕ)
    (hs : IsSidon ((C.image (fun n => (q * n + r) ^ 2) : Finset ℕ) : Set ℕ)) :
    IsSidon ((C.image (quadratic q r) : Finset ℕ) : Set ℕ) := by
  intro a ha b hb c hc d hd he
  obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hc
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hd
  have hnorm (n : ℕ) : (q * n + r) ^ 2 = q * quadratic q r n + r ^ 2 := by
    simp only [quadratic]
    ring
  have he' : (q * i + r) ^ 2 + (q * k + r) ^ 2 =
      (q * j + r) ^ 2 + (q * l + r) ^ 2 := by
    simp only [hnorm]
    nlinarith only [congrArg (q * ·) he]
  have hmem {n : ℕ} (hn : n ∈ C) : (q * n + r) ^ 2 ∈
      ((C.image (fun n => (q * n + r) ^ 2) : Finset ℕ) : Set ℕ) :=
    mem_image.mpr ⟨n, hn, rfl⟩
  have hcancel {m n : ℕ} (h : (q * m + r) ^ 2 = (q * n + r) ^ 2) :
      quadratic q r m = quadratic q r n := by
    simp only [hnorm] at h
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel h)
  rcases hs _ (hmem hi) _ (hmem hj) _ (hmem hk) _ (hmem hl) he' with h | h
  · exact Or.inl ⟨hcancel h.1, hcancel h.2⟩
  · exact Or.inr ⟨hcancel h.1, hcancel h.2⟩

/-- If all lifted adjacent indices are at most N, the starting indices lie
in [0,floor(N/q)-1]. No claim that this interval is filled is made. -/
theorem indices_bound (N q r : ℕ) (hq : 0 < q) (C : Finset ℕ)
    (hC : (adjacent C).image (fun n => q * n + r) ⊆ Icc 1 N) :
    C ⊆ range (N / q) := by
  intro n hn
  have hm : n + 1 ∈ adjacent C :=
    mem_union_right _ (mem_image.mpr ⟨n, hn, rfl⟩)
  have hh := (mem_Icc.mp (hC (mem_image.mpr ⟨n + 1, hm, rfl⟩))).2
  have hmul : (n + 1) * q ≤ N := by nlinarith only [hh]
  have hd := (Nat.le_div_iff_mul_le hq).mpr hmul
  exact mem_range.mpr (by omega)

/-- Finite reduction from the original Sidon-root problem to a sparse set of
adjacent indices for one normalized quadratic with small coefficients. -/
theorem extract_adjacent_quadratic (N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N) (hcard : 8 ≤ A.card)
    (hSidon : IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ)) :
    ∃ q ∈ Icc 1 N, ∃ r < q, ∃ C : Finset ℕ,
      C ⊆ range (N / q) ∧
      (adjacent C).image (fun n => q * n + r) ⊆ A ∧
      q * A.card ≤ 4 * N + A.card ∧ A.card ^ 2 ≤ 8 * N * q * C.card ∧
      IsSidon (((adjacent C).image (quadratic q r) : Finset ℕ) : Set ℕ) := by
  obtain ⟨q, hq, B, hBA, hsmall, hbig, _⟩ :=
    ShortTranslatedIntersection.extract_short_sidon_union N A hA hcard hSidon
  have hq0 : 0 < q := by have := (mem_Icc.mp hq).1; omega
  obtain ⟨r, hr, C, hBC, hCA⟩ := normalize_union q hq0 A B hBA
  refine ⟨q, hq, r, hr, C, indices_bound N q r hq0 C (hCA.trans hA), hCA,
    hsmall, ?_, ?_⟩
  · calc
      _ ≤ 8 * N * B.card := hbig
      _ ≤ 8 * N * (q * C.card) := Nat.mul_le_mul_left (8 * N) hBC
      _ = _ := by ring
  · apply normalized_sidon q r hq0
    apply Set.IsSidon.subset hSidon
    intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨q * n + r, hCA (mem_image.mpr ⟨n, hn, rfl⟩), rfl⟩

/-- The reduction loses only a subpower factor when supplied with a
near-linear original root set. -/
theorem power_scale_reduction (N : ℕ) (η : ℝ) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N) (hcard : 8 ≤ A.card)
    (hlarge : (N : ℝ) ^ (1 - η) ≤ A.card)
    (hSidon : IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ)) :
    ∃ q ∈ Icc 1 N, ∃ r < q, ∃ C : Finset ℕ,
      C ⊆ range (N / q) ∧ (q : ℝ) ≤ 5 * (N : ℝ) ^ η ∧
      (N : ℝ) ^ (1 - 3 * η) ≤ 40 * C.card ∧
      IsSidon (((adjacent C).image (quadratic q r) : Finset ℕ) : Set ℕ) := by
  obtain ⟨q, hq, B, hBA, hsmall, hbig, _⟩ :=
    ShortTranslatedIntersection.power_scale_extraction N η A hA hcard hlarge hSidon
  have hq0 : 0 < q := by have := (mem_Icc.mp hq).1; omega
  obtain ⟨r, hr, C, hBC, hCA⟩ := normalize_union q hq0 A B hBA
  have hMN : A.card ≤ N := by simpa using card_le_card hA
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBCr : (B.card : ℝ) ≤ q * C.card := by exact_mod_cast hBC
  refine ⟨q, hq, r, hr, C, indices_bound N q r hq0 C (hCA.trans hA), hsmall, ?_, ?_⟩
  · apply le_of_mul_le_mul_left (a := (N : ℝ) ^ η) ?_ (Real.rpow_pos_of_pos hN η)
    calc
      (N : ℝ) ^ η * (N : ℝ) ^ (1 - 3 * η) = (N : ℝ) ^ (1 - 2 * η) := by
        rw [← Real.rpow_add hN]
        congr 1
        ring
      _ ≤ 8 * B.card := hbig
      _ ≤ 8 * (q * C.card) := mul_le_mul_of_nonneg_left hBCr (by norm_num)
      _ ≤ 8 * ((5 * (N : ℝ) ^ η) * C.card) := by
        gcongr
      _ = (N : ℝ) ^ η * (40 * C.card) := by ring
  · apply normalized_sidon q r hq0
    apply Set.IsSidon.subset hSidon
    intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨q * n + r, hCA (mem_image.mpr ⟨n, hn, rfl⟩), rfl⟩

#print axioms normalize_union
#print axioms normalized_sidon
#print axioms indices_bound
#print axioms extract_adjacent_quadratic
#print axioms power_scale_reduction
end Erdos773.AdjacentQuadraticReduction
