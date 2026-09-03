import Submission.MixedCyclicThickeningExplore

/-! Exact integer block formulas. These do not assert a compatible infinite
choice of the finite cyclic patterns. -/
namespace Erdos66IntegerBlock
open AdditiveCombinatorics
open scoped Classical

lemma sumRep_range (A : Set ℕ) (n : ℕ) :
    sumRep A n = ∑ a ∈ Finset.range (n + 1), if a ∈ A ∧ n - a ∈ A then 1 else 0 := by
  classical
  rw [sumRep_def, Finset.card_filter, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  rfl

lemma sum_range_blocks (q M : ℕ) (f : ℕ → ℕ) :
    ∑ a ∈ Finset.range (q * M), f a =
      ∑ k ∈ Finset.range q, ∑ x ∈ Finset.range M, f (k * M + x) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

variable (M : ℕ) [NeZero M]

def blockSet (C : ℕ → Finset (ZMod M)) : Set ℕ :=
  {a | (a : ZMod M) ∈ C (a / M)}

lemma mem_blockSet (C : ℕ → Finset (ZMod M)) (k x : ℕ) (hx : x < M) :
    k * M + x ∈ blockSet M C ↔ (x : ZMod M) ∈ C k := by
  simp [blockSet, Nat.mul_comm k M, Nat.mul_add_div (NeZero.pos M), Nat.div_eq_of_lt hx]

lemma subtract_lower (q k t x : ℕ) (hk : k ≤ q) (hx : x ≤ t) :
    q * M + t - (k * M + x) = (q - k) * M + (t - x) := by
  have hk' := Nat.sub_add_cancel hk
  have hx' := Nat.sub_add_cancel hx
  have he : q * M + t = (q - k) * M + (t - x) + (k * M + x) := by nlinarith
  omega

lemma subtract_upper (q k t x : ℕ) (hk : k < q) (hx : t < x) (hxM : x < M) :
    q * M + t - (k * M + x) = (q - k - 1) * M + (M + t - x) := by
  have hk' : q - k - 1 + k + 1 = q := by omega
  have hx' : M + t - x + x = M + t := by omega
  have he : q * M + t = (q - k - 1) * M + (M + t - x) + (k * M + x) := by nlinarith
  omega

lemma sub_cast_lower (t x : ℕ) (hx : x ≤ t) :
    ((t - x : ℕ) : ZMod M) = (t : ZMod M) - x := Nat.cast_sub hx

lemma sub_cast_upper (t x : ℕ) (hx : x < M) :
    ((M + t - x : ℕ) : ZMod M) = (t : ZMod M) - x := by
  rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, zero_add]

noncomputable def lower (C D : Finset (ZMod M)) (t : ℕ) : ℕ :=
  ∑ x ∈ Finset.range M,
    if x ≤ t ∧ (x : ZMod M) ∈ C ∧ (t : ZMod M) - x ∈ D then 1 else 0

noncomputable def upper (C D : Finset (ZMod M)) (t : ℕ) : ℕ :=
  ∑ x ∈ Finset.range M,
    if t < x ∧ (x : ZMod M) ∈ C ∧ (t : ZMod M) - x ∈ D then 1 else 0

lemma lower_add_upper (C D : Finset (ZMod M)) (t : ℕ) :
    lower M C D t + upper M C D t =
      (C.filter (fun a ↦ (t : ZMod M) - a ∈ D)).card := by
  classical
  have he : (Finset.range M).image (fun x : ℕ ↦ (x : ZMod M)) = Finset.univ := by
    ext z
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
    exact ⟨z.val, ZMod.val_lt z, ZMod.natCast_zmod_val z⟩
  have hi : Set.InjOn (fun x : ℕ ↦ (x : ZMod M)) ↑(Finset.range M) := by
    intro x hx y hy hh
    have hv := congrArg ZMod.val hh
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp hx),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hy)] using hv
  rw [lower, upper, ← Finset.sum_add_distrib]
  calc
    _ = ∑ x ∈ Finset.range M,
        if (x : ZMod M) ∈ C ∧ (t : ZMod M) - x ∈ D then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxt : x ≤ t
      · simp [hxt, show ¬t < x by omega]
      · simp [hxt, show t < x by omega]
    _ = ∑ x : ZMod M, if x ∈ C ∧ (t : ZMod M) - x ∈ D then 1 else 0 := by
      rw [← he, Finset.sum_image hi]
    _ = _ := by
      simp only [ite_and, Finset.sum_ite_mem, Finset.univ_inter, Finset.card_filter]

lemma lower_mono {C C' D D' : Finset (ZMod M)} (hC : C ⊆ C') (hD : D ⊆ D') (t : ℕ) :
    lower M C D t ≤ lower M C' D' t := by
  apply Finset.sum_le_sum
  intro x hx
  split_ifs with h h' h'
  · rfl
  · exact False.elim (h' ⟨h.1, hC h.2.1, hD h.2.2⟩)
  · omega
  · rfl

lemma upper_mono {C C' D D' : Finset (ZMod M)} (hC : C ⊆ C') (hD : D ⊆ D') (t : ℕ) :
    upper M C D t ≤ upper M C' D' t := by
  apply Finset.sum_le_sum
  intro x hx
  split_ifs with h h' h'
  · rfl
  · exact False.elim (h' ⟨h.1, hC h.2.1, hD h.2.2⟩)
  · omega
  · rfl

/-- The lower and upper carry fibers use different pairs of block indices. -/
theorem block_formula (C : ℕ → Finset (ZMod M)) (q t : ℕ) (ht : t < M) :
    sumRep (blockSet M C) (q * M + t) =
      (∑ k ∈ Finset.range (q + 1), lower M (C k) (C (q - k)) t) +
        ∑ k ∈ Finset.range q, upper M (C k) (C (q - k - 1)) t := by
  classical
  rw [sumRep_range, show q * M + t + 1 = q * M + (t + 1) by omega,
    Finset.sum_range_add, sum_range_blocks]
  have hfull (k : ℕ) (hk : k < q) :
      (∑ x ∈ Finset.range M,
        if k * M + x ∈ blockSet M C ∧ q * M + t - (k * M + x) ∈ blockSet M C then 1 else 0) =
      lower M (C k) (C (q - k)) t + upper M (C k) (C (q - k - 1)) t := by
    rw [lower, upper, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hxM := Finset.mem_range.mp hx
    rw [mem_blockSet M C k x hxM]
    by_cases hxt : x ≤ t
    · rw [subtract_lower M q k t x hk.le hxt,
        mem_blockSet M C (q - k) (t - x) (by omega), sub_cast_lower M t x hxt]
      simp [hxt, show ¬t < x by omega]
    · rw [subtract_upper M q k t x hk (by omega) hxM,
        mem_blockSet M C (q - k - 1) (M + t - x) (by omega), sub_cast_upper M t x hxM]
      simp [hxt, show t < x by omega]
  have hlast :
      (∑ x ∈ Finset.range (t + 1),
        if q * M + x ∈ blockSet M C ∧ q * M + t - (q * M + x) ∈ blockSet M C then 1 else 0) =
      lower M (C q) (C 0) t := by
    rw [lower]
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono (by omega))
    · intro x hx
      have hn : ¬x ≤ t := by
        have hh := (Finset.mem_sdiff.mp hx).2
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hh
      simp [hn]
    · intro x hx
      have hxt : x ≤ t := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hx
      rw [mem_blockSet M C q x (by omega), subtract_lower M q q t x le_rfl hxt]
      simp only [Nat.sub_self, zero_mul, zero_add]
      rw [show t - x ∈ blockSet M C ↔ ((t - x : ℕ) : ZMod M) ∈ C 0 by
        simpa only [zero_mul, zero_add] using mem_blockSet M C 0 (t - x) (by omega)]
      rw [sub_cast_lower M t x hxt]
      simp [hxt]
  have hs : (∑ k ∈ Finset.range q, ∑ x ∈ Finset.range M,
        if k * M + x ∈ blockSet M C ∧ q * M + t - (k * M + x) ∈ blockSet M C then 1 else 0) =
      ∑ k ∈ Finset.range q, (lower M (C k) (C (q - k)) t + upper M (C k) (C (q - k - 1)) t) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hfull k (Finset.mem_range.mp hk)
  rw [hs]
  rw [hlast, Finset.sum_add_distrib, Finset.sum_range_succ]
  simp only [Nat.sub_self]
  omega

/-- With decreasing blocks, the carry split is bracketed by two neighboring
full cyclic convolutions. Only a single endpoint fiber is lost on either side. -/
theorem block_brackets (C : ℕ → Finset (ZMod M)) (hC : Antitone C)
    (q t : ℕ) (ht : t < M) :
    (∑ k ∈ Finset.range (q + 1),
        ((C k).filter (fun a ↦ (t : ZMod M) - a ∈ C (q - k))).card) ≤
      sumRep (blockSet M C) (q * M + t) + upper M (C q) (C 0) t ∧
    sumRep (blockSet M C) (q * M + t) ≤
      (∑ k ∈ Finset.range q,
        ((C k).filter (fun a ↦ (t : ZMod M) - a ∈ C (q - k - 1))).card) +
          lower M (C q) (C 0) t := by
  have hlo : (∑ k ∈ Finset.range q, lower M (C k) (C (q - k)) t) ≤
      ∑ k ∈ Finset.range q, lower M (C k) (C (q - k - 1)) t := by
    apply Finset.sum_le_sum
    intro k hk
    exact lower_mono M (Finset.Subset.refl _) (hC (by omega)) t
  have hhi : (∑ k ∈ Finset.range q, upper M (C k) (C (q - k)) t) ≤
      ∑ k ∈ Finset.range q, upper M (C k) (C (q - k - 1)) t := by
    apply Finset.sum_le_sum
    intro k hk
    exact upper_mono M (Finset.Subset.refl _) (hC (by omega)) t
  simp_rw [← lower_add_upper M]
  rw [block_formula M C q t ht]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun k ↦ lower M (C k) (C (q - k)) t),
    Finset.sum_range_succ (fun k ↦ upper M (C k) (C (q - k)) t)]
  simp only [Nat.sub_self]
  constructor <;> omega

end Erdos66IntegerBlock
