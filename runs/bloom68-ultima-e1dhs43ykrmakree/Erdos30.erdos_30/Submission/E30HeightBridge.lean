import Submission.E30Bridge

/-!
# All-height integer Sidon lifting: conditional criteria only

Heights are unrestricted integers. The finite index consists of a heavy fibre
at residue zero and one point in every other residue. Edge rows use ordinary
integer heights, with a literal `-1` carry on wrapping; no height modulus occurs.
No existence of a compressed family, and no resolution of Erdős 30, is asserted.
This file is independent of `Submission.Spec`.
-/

open Filter Asymptotics

namespace Erdos30Research

/-- Strong Sidonicity, including doubled summands, is equivalent to uniqueness
of nonzero ordered differences. -/
theorem int_isSidon_iff_differences (S : Set ℤ) :
    IsSidon S ↔ ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≠ b → a - b = c - d → a = c ∧ b = d := by
  constructor
  · intro h a ha b hb c hc d hd hab he
    rcases h a ha c hc d hd b hb (by omega) with h | h
    · exact ⟨h.1, h.2.symm⟩
    · exact (hab h.1).elim
  · intro h a ha b hb c hc d hd he
    by_cases hab : a = b
    · exact Or.inl ⟨hab, by omega⟩
    · obtain ⟨had, hbc⟩ := h a ha b hb d hd c hc hab (by omega)
      exact Or.inr ⟨had, hbc.symm⟩

variable {ι : Type*}

/-- Canonical horizontal difference in `[0,m)`. -/
def edgeResidue (m : ℤ) (r : ι → ℤ) (e : ι × ι) : ℤ :=
  r e.1 - r e.2 + if r e.1 < r e.2 then m else 0

/-- Ordinary high difference. The negative carry is essential. -/
def edgeHeight (r v : ι → ℤ) (e : ι × ι) : ℤ :=
  v e.1 - v e.2 + if r e.1 < r e.2 then -1 else 0

/-- The actual integer marks, not marks modulo a parent period. -/
def heightMark (m : ℤ) (r v : ι → ℤ) (i : ι) : ℤ := r i + m * v i

/-- This is an indexed distinctness test, retaining multiplicities of edges. -/
def EdgeRowsInjective (m : ℤ) (r v : ι → ℤ) : Prop :=
  ∀ t : ℤ, 0 < t → t < m → Function.Injective
    (fun e : {e : ι × ι // edgeResidue m r e = t} => edgeHeight r v e.val)

theorem edge_data {m : ℤ} {r v : ι → ℤ}
    (hr : ∀ i, 0 ≤ r i ∧ r i < m) (e : ι × ι) :
    (0 ≤ edgeResidue m r e ∧ edgeResidue m r e < m) ∧
    heightMark m r v e.1 - heightMark m r v e.2 =
      edgeResidue m r e + m * edgeHeight r v e := by
  have h₁ := hr e.1
  have h₂ := hr e.2
  dsimp [edgeResidue, edgeHeight, heightMark]
  split_ifs <;> constructor
  all_goals first | omega | ring

/-- Uniqueness of the integer residue/high-coordinate representation. -/
theorem residue_height_unique {m a b x y : ℤ} (hm : 0 < m)
    (ha : 0 ≤ a ∧ a < m) (hb : 0 ≤ b ∧ b < m)
    (he : a + m * x = b + m * y) : a = b ∧ x = y := by
  have hab : a = b := by
    have := congrArg (fun z : ℤ => z % m) he
    simpa only [Int.add_mul_emod_self_left, Int.emod_eq_of_lt ha.1 ha.2,
      Int.emod_eq_of_lt hb.1 hb.2] using this
  refine ⟨hab, (mul_left_cancel₀ (ne_of_gt hm)) ?_⟩
  omega

theorem heightMark_injective {m : ℤ} {r v : ι → ℤ} (hm : 0 < m)
    (hr : ∀ i, 0 ≤ r i ∧ r i < m)
    (hinj : Function.Injective (fun i => (r i, v i))) :
    Function.Injective (heightMark m r v) := by
  intro i j he
  obtain ⟨h₁, h₂⟩ := residue_height_unique hm (hr i) (hr j) he
  exact hinj (Prod.ext h₁ h₂)

/-- A general finite-fibre criterion (finiteness is needed only for counting).
The zero row tests within-fibre differences globally; other rows test the
explicit carry-adjusted high differences, not an assumed Sidon mark set. -/
theorem isSidon_of_edge_rows {m : ℤ} {r v : ι → ℤ} (hm : 0 < m)
    (hr : ∀ i, 0 ≤ r i ∧ r i < m)
    (hzero : ∀ i j k l, i ≠ j → k ≠ l → r i = r j → r k = r l →
      v i - v j = v k - v l → i = k ∧ j = l)
    (hrows : EdgeRowsInjective m r v) : IsSidon (Set.range (heightMark m r v)) := by
  rw [int_isSidon_iff_differences]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ hne he
  have hij : i ≠ j := fun h => hne (congrArg _ h)
  have hkl : k ≠ l := by
    intro h
    apply hne
    rw [h, sub_self] at he
    exact sub_eq_zero.mp he
  have h₁ := edge_data (v := v) hr (i, j)
  have h₂ := edge_data (v := v) hr (k, l)
  have hh := residue_height_unique hm h₁.1 h₂.1 (h₁.2.symm.trans (he.trans h₂.2))
  have hp : i = k ∧ j = l := by
    by_cases hz : edgeResidue m r (i, j) = 0
    · have hz' : edgeResidue m r (k, l) = 0 := hh.1.symm.trans hz
      have rij : r i = r j := by
        have := hr i; have := hr j
        dsimp [edgeResidue] at hz
        split_ifs at hz <;> omega
      have rkl : r k = r l := by
        have := hr k; have := hr l
        dsimp [edgeResidue] at hz'
        split_ifs at hz' <;> omega
      apply hzero i j k l hij hkl rij rkl
      simpa [edgeHeight, rij, rkl] using hh.2
    · have ht : 0 < edgeResidue m r (i, j) := by omega
      have hp := hrows _ ht h₁.1.2
        (show edgeHeight r v (i, j) = edgeHeight r v (k, l) from hh.2)
          (a₁ := ⟨(i, j), rfl⟩) (a₂ := ⟨(k, l), hh.1.symm⟩)
      have hp' : (i, j) = (k, l) := congrArg Subtype.val hp
      exact ⟨congrArg Prod.fst hp', congrArg Prod.snd hp'⟩
  exact ⟨congrArg _ hp.1, congrArg _ hp.2⟩

/-- Explicit finite index: one index per heavy height and per light residue. -/
abbrev HeightIndex (m : ℕ) (A : Finset ℤ) := A ⊕ Fin (m - 1)

def liftResidue {m : ℕ} {A : Finset ℤ} : HeightIndex m A → ℤ
  | .inl _ => 0
  | .inr s => (s.val : ℤ) + 1

def liftHeight {m : ℕ} {A : Finset ℤ} (b : ℤ → ℤ) : HeightIndex m A → ℤ
  | .inl a => a.val
  | .inr s => b ((s.val : ℤ) + 1)

theorem liftResidue_bounds {m : ℕ} {A : Finset ℤ} (hm : 0 < m)
    (i : HeightIndex m A) : 0 ≤ liftResidue i ∧ liftResidue i < m := by
  cases i with
  | inl a => simp only [liftResidue]; omega
  | inr s => have := s.isLt; dsimp [liftResidue]; omega

theorem lift_coordinates_injective {m : ℕ} {A : Finset ℤ} (b : ℤ → ℤ) :
    Function.Injective (fun i : HeightIndex m A => (liftResidue i, liftHeight b i)) := by
  intro i j he
  have hr := congrArg Prod.fst he
  have hv := congrArg Prod.snd he
  cases i <;> cases j <;> simp only [liftResidue, liftHeight] at hr hv
  · exact congrArg Sum.inl (Subtype.ext hv)
  · omega
  · omega
  · congr 1
    apply Fin.ext
    omega

/-- The explicit all-height marking map is injective for every positive modulus. -/
theorem liftMark_injective {m : ℕ} {A : Finset ℤ} (hm : 0 < m) (b : ℤ → ℤ) :
    Function.Injective (heightMark (m : ℤ) (@liftResidue m A) (liftHeight b)) :=
  heightMark_injective (by exact_mod_cast hm) (liftResidue_bounds hm)
    (lift_coordinates_injective b)

/-- A nonzero edge within one residue must be a heavy-heavy edge. -/
theorem same_residue_heavy {m : ℕ} {A : Finset ℤ} {i j : HeightIndex m A}
    (hne : i ≠ j) (hr : liftResidue i = liftResidue j) :
    ∃ a b : A, i = .inl a ∧ j = .inl b := by
  cases i with
  | inl a =>
    cases j with
    | inl b => exact ⟨a, b, rfl, rfl⟩
    | inr b => simp only [liftResidue] at hr; omega
  | inr a =>
    cases j with
    | inl b => simp only [liftResidue] at hr; omega
    | inr b =>
      exfalso
      apply hne
      congr 1
      apply Fin.ext
      simp only [liftResidue] at hr
      omega

/-- All-height sufficient criterion. The light heights have no restrictions
other than the nonzero edge-row injections; the heavy heights are strong Sidon. -/
theorem allHeight_isSidon {m : ℕ} {A : Finset ℤ} {b : ℤ → ℤ} (hm : 2 ≤ m)
    (hA : IsSidon (A : Set ℤ))
    (hrows : EdgeRowsInjective (m : ℤ) (@liftResidue m A) (liftHeight b)) :
    IsSidon (Set.range (heightMark (m : ℤ) (@liftResidue m A) (liftHeight b))) := by
  apply isSidon_of_edge_rows (by exact_mod_cast (by omega : 0 < m))
    (liftResidue_bounds (by omega)) _ hrows
  intro i j k l hij hkl rij rkl he
  obtain ⟨a, b', rfl, rfl⟩ := same_residue_heavy hij rij
  obtain ⟨c, d, rfl, rfl⟩ := same_residue_heavy hkl rkl
  have hab : (a : ℤ) ≠ b' := by
    intro h
    exact hij (congrArg Sum.inl (Subtype.ext h))
  obtain ⟨hac, hbd⟩ := (int_isSidon_iff_differences _).mp hA
    a a.property b' b'.property c c.property d d.property hab he
  exact ⟨congrArg Sum.inl (Subtype.ext hac), congrArg Sum.inl (Subtype.ext hbd)⟩

/-- The explicit branch carry is exactly integer quotient/remainder division.
In a row `t`, the tested values are therefore the high coordinates of differences. -/
theorem edge_quotient_remainder {m : ℤ} {r v : ι → ℤ} (hm : 0 < m)
    (hr : ∀ i, 0 ≤ r i ∧ r i < m) (e : ι × ι) :
    edgeResidue m r e = (r e.1 - r e.2) % m ∧
    edgeHeight r v e = v e.1 - v e.2 + (r e.1 - r e.2) / m := by
  have hd := edge_data (v := fun _ => 0) hr e
  have he : edgeResidue m r e + m * edgeHeight r (fun _ => 0) e =
      (r e.1 - r e.2) % m + m * ((r e.1 - r e.2) / m) := by
    rw [← hd.2, Int.emod_add_mul_ediv]
    simp [heightMark]
  obtain ⟨h₁, h₂⟩ := residue_height_unique hm hd.1
    ⟨Int.emod_nonneg _ (ne_of_gt hm), Int.emod_lt_of_pos _ hm⟩ he
  exact ⟨h₁, by simpa [edgeHeight] using congrArg (fun z => v e.1 - v e.2 + z) h₂⟩

/-- Heavy/light rows give `b_r - a` and `a - b_(m-r) - 1`.
Light/light edges give `b_(s+r)-b_s` without wrapping and
`b_(s+r-m)-b_s-1` with wrapping, directly by `edgeHeight`.
Thus the row injection tests the four-part multiset E_r, without discarding
edge multiplicities. The seam ending at residue zero is in the second part. -/
theorem heavy_light_carries {m : ℕ} {A : Finset ℤ} (b : ℤ → ℤ)
    (a : A) (s : Fin (m - 1)) :
    edgeHeight (@liftResidue m A) (liftHeight b) (.inr s, .inl a) =
      b ((s.val : ℤ) + 1) - a ∧
    edgeHeight (@liftResidue m A) (liftHeight b) (.inl a, .inr s) =
      (a : ℤ) - b ((s.val : ℤ) + 1) - 1 := by
  have hs : (0 : ℤ) < s.val + 1 := by omega
  simp [edgeHeight, liftResidue, liftHeight, hs, not_lt.mpr hs.le, sub_eq_add_neg]

/-- Light/light edges: the carry is `-1` precisely when the destination
residue is below the source residue. -/
theorem light_light_carry {m : ℕ} {A : Finset ℤ} (b : ℤ → ℤ) (s t : Fin (m - 1)) :
    edgeHeight (@liftResidue m A) (liftHeight b) (.inr s, .inr t) =
      b ((s.val : ℤ) + 1) - b ((t.val : ℤ) + 1) + if s.val < t.val then -1 else 0 := by
  simp only [edgeHeight, liftResidue, liftHeight, add_lt_add_iff_right, Nat.cast_lt]

/-- Translate a finite injectively indexed integer mark set in `[0,N)` by `+1`
and then cast to naturals, preserving cardinality and strong Sidonicity. -/
theorem nat_set_of_integer_marks [Fintype ι] {f : ι → ℤ} {N : ℕ}
    (hinj : Function.Injective f) (hbox : ∀ i, 0 ≤ f i ∧ f i < N)
    (hS : IsSidon (Set.range f)) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 N ∧ IsSidon (B : Set ℕ) ∧
      B.card = Fintype.card ι := by
  classical
  let g : ι → ℕ := fun i => (f i + 1).toNat
  have hg (i : ι) : (g i : ℤ) = f i + 1 := Int.toNat_of_nonneg (by have := hbox i; omega)
  have hginj : Function.Injective g := by
    intro i j he
    apply hinj
    have he' : (g i : ℤ) = g j := congrArg (fun n : ℕ => (n : ℤ)) he
    rw [hg, hg] at he'
    omega
  refine ⟨Finset.univ.image g, ?_, ?_, by simp [Finset.card_image_of_injective _ hginj]⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have := hg i; have := hbox i
    rw [Finset.mem_Icc]
    omega
  · intro a ha b hb c hc d hd he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hd
    have he' : (g i : ℤ) + g k = g j + g l := by exact_mod_cast he
    simp only [hg] at he'
    rcases hS _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ (by omega) with h | h
    · exact Or.inl ⟨congrArg g (hinj h.1), congrArg g (hinj h.2)⟩
    · exact Or.inr ⟨congrArg g (hinj h.1), congrArg g (hinj h.2)⟩

/-- The box endpoint is exactly `m*(L+1)`, and there are `m-1+|A|` marks. -/
theorem allHeight_nat_set {m L : ℕ} {A : Finset ℤ} {b : ℤ → ℤ}
    (hm : 2 ≤ m) (hA : IsSidon (A : Set ℤ))
    (hrows : EdgeRowsInjective (m : ℤ) (@liftResidue m A) (liftHeight b))
    (hAbox : ∀ a ∈ A, 0 ≤ a ∧ a ≤ (L : ℤ))
    (hbbox : ∀ s : ℤ, 1 ≤ s → s < m → 0 ≤ b s ∧ b s ≤ (L : ℤ)) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 (m * (L + 1)) ∧ IsSidon (B : Set ℕ) ∧
      B.card = m - 1 + A.card := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
  have hr := @liftResidue_bounds m A (by omega)
  have hv (i : HeightIndex m A) : 0 ≤ liftHeight b i ∧ liftHeight b i ≤ (L : ℤ) := by
    cases i with
    | inl a => exact hAbox a a.property
    | inr s => exact hbbox _ (by omega) (hr (.inr s)).2
  have hbox (i : HeightIndex m A) :
      0 ≤ heightMark (m : ℤ) liftResidue (liftHeight b) i ∧
      heightMark (m : ℤ) liftResidue (liftHeight b) i < (m * (L + 1) : ℕ) := by
    have hri := hr i
    have hvi := hv i
    dsimp [heightMark]
    constructor <;> nlinarith [mul_nonneg hm'.le hvi.1,
      mul_le_mul_of_nonneg_left hvi.2 hm'.le]
  obtain ⟨B, hBN, hB, hcard⟩ := nat_set_of_integer_marks
    (liftMark_injective (by omega) b)
    hbox (allHeight_isSidon hm hA hrows)
  exact ⟨B, hBN, hB, by simpa [HeightIndex, Nat.add_comm] using hcard⟩

/-- Natural subtraction in the target modulus is harmless for `p ≥ 2`. -/
theorem target_modulus_card {p : ℕ} (hp : 2 ≤ p) :
    2 ≤ p ^ 2 - p + 1 ∧ (p ^ 2 - p + 1) - 1 + (p + 1) = p ^ 2 + 1 := by
  have : p + 1 ≤ p ^ 2 := by nlinarith
  omega

/-- Exact integer accounting: `k²-N = p²+mG`, where `L+1 = u-G`.
Subtraction here is integer subtraction, not truncated natural subtraction. -/
theorem target_diameter_identity {p L : ℕ} (hp : 2 ≤ p) {G : ℤ}
    (hgap : (L : ℤ) + 1 = (p : ℤ) ^ 2 + p + 1 - G) :
    ((p ^ 2 + 1 : ℕ) : ℤ) ^ 2 - (((p ^ 2 - p + 1) * (L + 1) : ℕ) : ℤ) =
      (p : ℤ) ^ 2 + ((p ^ 2 - p + 1 : ℕ) : ℤ) * G := by
  have hpp : p ≤ p ^ 2 := by nlinarith
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_sub hpp]
  rw [hgap]
  ring

/-- A finite certificate, NOT an assertion that such certificates exist.
Its only Sidon hypothesis concerns the heavy set; light compatibility is the
explicit carry-row injection test. All heights are in the ordinary integer box. -/
structure AllHeightBox (p L : ℕ) where
  A : Finset ℤ
  b : ℤ → ℤ
  heavy_sidon : IsSidon (A : Set ℤ)
  heavy_card : A.card = p + 1
  rows : EdgeRowsInjective ((p ^ 2 - p + 1 : ℕ) : ℤ)
    (@liftResidue (p ^ 2 - p + 1) A) (liftHeight b)
  heavy_box : ∀ a ∈ A, 0 ≤ a ∧ a ≤ (L : ℤ)
  light_box : ∀ s : ℤ, 1 ≤ s → s < (p ^ 2 - p + 1 : ℕ) →
    0 ≤ b s ∧ b s ≤ (L : ℤ)

theorem AllHeightBox.nat_set {p L : ℕ} (C : AllHeightBox p L) (hp : 2 ≤ p) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 ((p ^ 2 - p + 1) * (L + 1)) ∧
      IsSidon (B : Set ℕ) ∧ B.card = p ^ 2 + 1 := by
  obtain ⟨B, hBN, hB, hc⟩ := allHeight_nat_set (target_modulus_card hp).1
    C.heavy_sidon C.rows C.heavy_box C.light_box
  exact ⟨B, hBN, hB, by rw [hc, C.heavy_card, (target_modulus_card hp).2]⟩

/-- Direct connection to the existing conditional disproof bridge. Unbounded
`p` supplies unbounded `k=p²+1`; the real saving is an explicit hypothesis. -/
theorem not_all_power_bounds_of_allHeight_saving {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hfamily : ∀ P : ℕ, ∃ p ≥ P, 2 ≤ p ∧ ∃ L : ℕ, ∃ _ : AllHeightBox p L,
      (((p ^ 2 - p + 1) * (L + 1) : ℕ) : ℝ) ≤
        ((p ^ 2 + 1 : ℕ) : ℝ) ^ 2 - c * ((p ^ 2 + 1 : ℕ) : ℝ) ^ (1 + α)) :
    ¬ (∀ ε : ℝ, 0 < ε →
      (fun N : ℕ => (h N : ℝ) - Real.sqrt (N : ℝ)) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ ε)) := by
  apply not_all_power_bounds_of_diameter_saving hα hc
  intro K
  obtain ⟨p, hpK, hp, L, C, hsave⟩ := hfamily K
  obtain ⟨B, hBN, hB, hcard⟩ := C.nat_set hp
  refine ⟨p ^ 2 + 1, ?_, (p ^ 2 - p + 1) * (L + 1), B, hBN, hB, hcard.ge, hsave⟩
  nlinarith

/-- A polynomial height gap gives a diameter saving with `α = β/2`.
The deliberately loose constant is `c = (c₀/2) / 2^(1+β/2) > 0`.
Only the elementary bounds `m ≥ p²/2` and `k ≤ 2p²` are used. -/
theorem diameter_saving_of_height_gap {p L G c₀ β : ℝ}
    (hp : 2 ≤ p) (hc₀ : 0 < c₀) (hβ : 0 < β)
    (hgap : L + 1 = p ^ 2 + p + 1 - G) (hG : c₀ * p ^ β ≤ G) :
    (p ^ 2 - p + 1) * (L + 1) ≤ (p ^ 2 + 1) ^ 2 -
      ((c₀ / 2) / (2 : ℝ) ^ (1 + β / 2)) * (p ^ 2 + 1) ^ (1 + β / 2) := by
  have hp0 : 0 < p := by linarith
  have htwo : 0 < (2 : ℝ) ^ (1 + β / 2) := by positivity
  have hm : p ^ 2 / 2 ≤ p ^ 2 - p + 1 := by nlinarith [sq_nonneg (p - 1)]
  have hpow : (p ^ 2 + 1) ^ (1 + β / 2) ≤
      (2 : ℝ) ^ (1 + β / 2) * (p ^ 2 * p ^ β) := by
    calc
      _ ≤ (2 * p ^ 2) ^ (1 + β / 2) :=
        Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg p), ← Real.rpow_natCast_mul hp0.le]
        rw [Nat.cast_ofNat, show (2 : ℝ) * (1 + β / 2) = 2 + β by ring,
          Real.rpow_add hp0, Real.rpow_two]
  have hs : ((c₀ / 2) / (2 : ℝ) ^ (1 + β / 2)) * (p ^ 2 + 1) ^ (1 + β / 2) ≤
      (p ^ 2 - p + 1) * G := by
    calc
      _ ≤ ((c₀ / 2) / (2 : ℝ) ^ (1 + β / 2)) *
          ((2 : ℝ) ^ (1 + β / 2) * (p ^ 2 * p ^ β)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (p ^ 2 / 2) * (c₀ * p ^ β) := by field_simp [ne_of_gt htwo]
      _ ≤ _ := mul_le_mul hm hG (by positivity) (by nlinarith [sq_nonneg p])
  rw [hgap]
  nlinarith only [hs, sq_nonneg p]

/-- Full conditional payoff of unbounded all-height certificates with
`G ≥ c₀*p^β`. This theorem does NOT construct any such family. -/
theorem not_all_power_bounds_of_allHeight_gap {β c₀ : ℝ} (hβ : 0 < β) (hc₀ : 0 < c₀)
    (hfamily : ∀ P : ℕ, ∃ p ≥ P, 2 ≤ p ∧ ∃ L : ℕ, ∃ _ : AllHeightBox p L, ∃ G : ℤ,
      (L : ℤ) + 1 = (p : ℤ) ^ 2 + p + 1 - G ∧ c₀ * (p : ℝ) ^ β ≤ (G : ℝ)) :
    ¬ (∀ ε : ℝ, 0 < ε →
      (fun N : ℕ => (h N : ℝ) - Real.sqrt (N : ℝ)) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ ε)) := by
  apply not_all_power_bounds_of_allHeight_saving (α := β / 2)
    (c := (c₀ / 2) / (2 : ℝ) ^ (1 + β / 2)) (by positivity) (by positivity)
  intro P
  obtain ⟨p, hpP, hp, L, C, G, hgap, hG⟩ := hfamily P
  refine ⟨p, hpP, hp, L, C, ?_⟩
  have hgap' : (L : ℝ) + 1 = (p : ℝ) ^ 2 + p + 1 - (G : ℝ) := by exact_mod_cast hgap
  have hsave := diameter_saving_of_height_gap (by exact_mod_cast hp) hc₀ hβ hgap' hG
  have hpp : p ≤ p ^ 2 := by nlinarith
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_sub hpp]
    using hsave

end Erdos30Research
