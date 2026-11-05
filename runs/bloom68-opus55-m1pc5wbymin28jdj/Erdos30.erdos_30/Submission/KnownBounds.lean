import Submission.Spec

/-!
# Erdős Problem 30 — known partial bounds (variants)

This file does **not** settle `Erdos30.erdos_30` (an open problem). It formalizes some of the
classical known bounds requested by the `TODO` in `Submission/Spec.lean`:

* `Erdos30.h_le_sqrt_add_rpow_quarter_add_one`: Lindström's bound `h(N) ≤ √N + N^{1/4} + 1`,
  proved by the Erdős–Turán window (double counting + Cauchy–Schwarz) argument.
* `Erdos30.h_sub_sqrt_le`: hence the upper-bound half of the conjecture holds with exponent `1/4`.
* `Erdos30.erdos_30_of_half_le`: the conjecture's statement for every `ε ≥ 1/2`.
-/

namespace Erdos30

open Filter Finset

namespace KnownBounds

lemma sidon_diff_injOn {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) :
    Set.InjOn (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2) (A.offDiag : Set (ℕ × ℕ)) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe] at hab hcd
  simp only at heq
  have h1 : a + d = c + b := by omega
  rcases hA a hab.1 c hcd.1 d hcd.2.1 b hab.2.1 h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · simp [h2, h3]
  · exact absurd h2 hab.2.2

/-- The window of `A` ending at `s` of length `L`. -/
def W (A : Finset ℕ) (L s : ℕ) : Finset ℕ := A.filter (fun a => a ≤ s ∧ s < a + L)

lemma sum_card_W {A : Finset ℕ} {N L : ℕ} (hAN : ∀ a ∈ A, a ≤ N) :
    ∑ s ∈ range (N + L), (W A L s).card = A.card * L := by
  unfold W
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm, Finset.card_eq_sum_ones A, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [one_mul, ← Finset.card_filter]
  have : (range (N + L)).filter (fun s => a ≤ s ∧ s < a + L) = Ico a (a + L) := by
    ext s
    simp only [mem_filter, mem_range, mem_Ico]
    have := hAN a ha
    omega
  rw [this, Nat.card_Ico]
  omega

lemma sum_offDiag_W_le {A : Finset ℕ} {N L : ℕ} (hA : IsSidon (A : Set ℕ)) :
    ∑ s ∈ range (N + L), (W A L s).offDiag.card ≤ L * L - L := by
  rw [← Finset.card_sigma]
  have hT : (range L).offDiag.card = L * L - L := by
    rw [Finset.offDiag_card, card_range]
  rw [← hT]
  apply Finset.card_le_card_of_injOn (fun x => (x.1 - x.2.1, x.1 - x.2.2))
  · rintro ⟨s, a, b⟩ hx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, mem_range,
      Finset.mem_offDiag, W, mem_filter] at hx
    simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe, mem_range]
    omega
  · rintro ⟨s, a, b⟩ hx ⟨s', a', b'⟩ hx' heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, mem_range,
      Finset.mem_offDiag, W, mem_filter] at hx hx'
    simp only [Prod.mk.injEq] at heq
    have hd : ((a : ℤ) - b) = ((a' : ℤ) - b') := by omega
    have m1 : ((a, b) : ℕ × ℕ) ∈ (A.offDiag : Set (ℕ × ℕ)) := by
      simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe]
      exact ⟨hx.2.1.1, hx.2.2.1.1, hx.2.2.2⟩
    have m2 : ((a', b') : ℕ × ℕ) ∈ (A.offDiag : Set (ℕ × ℕ)) := by
      simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe]
      exact ⟨hx'.2.1.1, hx'.2.2.1.1, hx'.2.2.2⟩
    have hab := sidon_diff_injOn hA m1 m2 hd
    simp only [Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    have : s = s' := by omega
    subst this
    rfl

/-- Erdős–Turán window inequality: `k² L ≤ (N + L)(k + L - 1)`. -/
lemma window_ineq {A : Finset ℕ} {N L : ℕ} (hAN : ∀ a ∈ A, a ≤ N) (hA : IsSidon (A : Set ℕ))
    (hL : 1 ≤ L) :
    A.card * A.card * L ≤ (N + L) * (A.card + L - 1) := by
  set k := A.card
  have h1 := sum_card_W (L := L) hAN
  have h2 := sum_offDiag_W_le (N := N) (L := L) hA
  have hCS := sq_sum_le_card_mul_sum_sq (s := range (N + L)) (f := fun s => (W A L s).card)
  rw [card_range, h1, Nat.cast_id] at hCS
  have h3 : ∑ s ∈ range (N + L), (W A L s).card ^ 2 =
      ∑ s ∈ range (N + L), (W A L s).offDiag.card + ∑ s ∈ range (N + L), (W A L s).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.offDiag_card, sq]
    have : (W A L s).card ≤ (W A L s).card * (W A L s).card := Nat.le_mul_self _
    omega
  rw [h3, h1] at hCS
  -- hCS : (k * L) ^ 2 ≤ (N + L) * (S + k * L), S ≤ L*L - L
  have h4 : (k * L) ^ 2 ≤ (N + L) * (L * L - L + k * L) := by
    calc (k * L) ^ 2 ≤ _ := hCS
      _ ≤ _ := by gcongr
  have h5 : L * L - L + k * L = L * (k + L - 1) := by
    obtain ⟨l, rfl⟩ : ∃ l, L = l + 1 := ⟨L - 1, by omega⟩
    have e1 : (l + 1) * (l + 1) - (l + 1) = (l + 1) * l :=
      Nat.sub_eq_of_eq_add (by ring)
    rw [e1, show k + (l + 1) - 1 = k + l by omega]
    ring
  rw [h5] at h4
  have h6 : (k * k * L) * L ≤ ((N + L) * (k + L - 1)) * L := by
    calc (k * k * L) * L = (k * L) ^ 2 := by ring
      _ ≤ (N + L) * (L * (k + L - 1)) := h4
      _ = ((N + L) * (k + L - 1)) * L := by ring
  exact Nat.le_of_mul_le_mul_right h6 (by omega)

/-- Real-number consequence of the window inequality (Lindström-type bound). -/
lemma card_le_sqrt_add {A : Finset ℕ} {N : ℕ} (hAN : ∀ a ∈ A, a ≤ N) (hA : IsSidon (A : Set ℕ))
    (hN : 1 ≤ N) :
    (A.card : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ ((1:ℝ)/4) + 1 := by
  set k := A.card with hk
  set t : ℝ := (N : ℝ) ^ ((1:ℝ)/4) with ht
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : 1 ≤ t := Real.one_le_rpow hN' (by norm_num)
  have htN : t ^ 4 = N := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hsq : Real.sqrt N = t ^ 2 := by
    rw [← htN, show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsq]
  set L := Nat.ceil (t ^ 3) with hLdef
  have hL1 : t ^ 3 ≤ L := Nat.le_ceil _
  have hL2 : (L : ℝ) < t ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
  have ht3 : (1:ℝ) ≤ t ^ 3 := one_le_pow₀ ht1
  have hLpos : 1 ≤ L := by
    have : (1:ℝ) ≤ L := ht3.trans hL1
    exact_mod_cast this
  have hw := window_ineq hAN hA hLpos
  have hwR : (k:ℝ) * k * L ≤ (N + L) * (k + L - 1) := by
    have := (Nat.cast_le (α := ℝ)).mpr hw
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_add,
      Nat.cast_sub (by omega : 1 ≤ A.card + L), Nat.cast_add, Nat.cast_one] at this
    exact this
  rw [← htN] at hwR
  have hLR : (1:ℝ) ≤ L := by exact_mod_cast hLpos
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  by_contra hcon
  push_neg at hcon
  -- hcon : t^2 + t + 1 < k
  have hQ : 0 < (k:ℝ) ^ 2 - (t + 1) * k - t ^ 4 - t ^ 3 - 1 := by
    have e1 : 0 < (k:ℝ) - (t ^ 2 + t + 1) := by linarith
    have e2 : 0 < (k:ℝ) + (t ^ 2 + t + 1) - t - 1 := by nlinarith
    have e3 := mul_pos e1 e2
    nlinarith
  have hQ' : 0 < (k:ℝ) ^ 2 - (t + 1) * k - t ^ 4 - L := by linarith
  have hQL : 0 < (L:ℝ) * ((k:ℝ) ^ 2 - (t + 1) * k - t ^ 4 - L) := mul_pos (by linarith) hQ'
  have h4 : t ^ 4 * k ≤ t * L * k := by
    have : t ^ 4 = t * t ^ 3 := by ring
    rw [this]
    have ht0 : (0:ℝ) ≤ t := by linarith
    have := mul_le_mul_of_nonneg_left hL1 ht0
    exact mul_le_mul_of_nonneg_right this hk0
  nlinarith

end KnownBounds

open KnownBounds

/-- `h N` is attained by a Sidon subset of `{1,…,N}`. -/
theorem exists_sidon_card_eq_h (N : ℕ) :
    ∃ B ⊆ Finset.Icc 1 N, IsSidon (B : Set ℕ) ∧ B.card = h N := by
  have hne : ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)).Nonempty :=
    ⟨∅, by simp [IsSidon]⟩
  obtain ⟨B, hB, hBeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hB
  exact ⟨B, hB.1, hB.2, hBeq.symm⟩

/-- Every Sidon subset of `{1,…,N}` has at most `h N` elements. -/
theorem card_le_h {N : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Icc 1 N) (hS : IsSidon (B : Set ℕ)) :
    B.card ≤ h N :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hB, hS⟩)

/-- **Lindström's bound** (1969), via the Erdős–Turán window argument:
`h(N) ≤ √N + N^{1/4} + 1` for every `N`. -/
theorem h_le_sqrt_add_rpow_quarter_add_one (N : ℕ) :
    (h N : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ ((1:ℝ)/4) + 1 := by
  obtain ⟨B, hB, hS, hc⟩ := exists_sidon_card_eq_h N
  rw [← hc]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : B = ∅ := by
      ext a; constructor
      · intro ha; have := hB ha; simp at this
      · simp
    subst this
    simp only [Finset.card_empty, CharP.cast_eq_zero, Real.sqrt_zero, zero_add]
    positivity
  · exact card_le_sqrt_add (fun a ha => (Finset.mem_Icc.1 (hB ha)).2) hS hN

/-- The upper-bound half of Erdős Problem 30 holds with exponent `1/4`. -/
theorem h_sub_sqrt_le (N : ℕ) : (h N : ℝ) - Real.sqrt N ≤ (N : ℝ) ^ ((1:ℝ)/4) + 1 := by
  have := h_le_sqrt_add_rpow_quarter_add_one N
  linarith

/-- The trivial range `ε ≥ 1/2` of Erdős Problem 30 (both directions). -/
theorem erdos_30_of_half_le (ε : ℝ) (hε : 1/2 ≤ ε) :
    (fun N => (h N : ℝ) - (N : Real).sqrt) =O[atTop] fun N => (N : ℝ)^(ε : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 3 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hup := h_le_sqrt_add_rpow_quarter_add_one N
  have hq : (N : ℝ) ^ ((1:ℝ)/4) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN' (by norm_num)
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact hN'
  have hse : Real.sqrt N ≤ (N : ℝ) ^ ε := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN' hε
  have hh0 : (0:ℝ) ≤ h N := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ) ^ ε),
    abs_le]
  constructor <;> nlinarith

end Erdos30

