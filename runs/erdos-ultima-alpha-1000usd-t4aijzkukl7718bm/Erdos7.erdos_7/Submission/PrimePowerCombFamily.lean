import FormalConjecturesUtil

/-! A canonical irredundant partial box family on arbitrary finite distinct
prime-power patterns. This does not give a cover; the constant point -1 is
uncovered. The construction is useful for testing proposed shape-counting
arguments while retaining private points and divisor closure. -/
namespace Erdos7PrimePowerCombFamily
open scoped BigOperators
open Finset
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- A nonzero digit at the last constrained level, above a stem of -1 digits. -/
def exitValue (p e c : ℕ) : ℤ := (c : ℤ) * (p : ℤ) ^ (e - 1) - 1

lemma exit_bounds {p e c : ℕ} (hp : 0 < p) (he : 0 < e)
    (hc : 0 < c) (hcp : c < p) :
    0 < exitValue p e c + 1 ∧ exitValue p e c + 1 < (p : ℤ) ^ e := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hcz : (0 : ℤ) < c := by exact_mod_cast hc
  have hcpz : (c : ℤ) < p := by exact_mod_cast hcp
  have heq : e = (e - 1) + 1 := by omega
  constructor
  · simpa [exitValue] using mul_pos hcz (pow_pos hpz (e - 1))
  · have hmul := mul_lt_mul_of_pos_right hcpz (pow_pos hpz (e - 1))
    conv_rhs => rw [heq, pow_succ']
    simpa [exitValue] using hmul

lemma exit_not_stem {p e c : ℕ} (hp : 0 < p) (he : 0 < e)
    (hc : 0 < c) (hcp : c < p) :
    ¬ (p : ℤ) ^ e ∣ exitValue p e c + 1 := by
  intro hd
  have hb := exit_bounds hp he hc hcp
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt hb.1.le hb.2 hd
  omega

lemma higher_exit_stem {p e f c : ℕ} (hef : e < f) :
    (p : ℤ) ^ e ∣ exitValue p f c + 1 := by
  have he : e ≤ f - 1 := by omega
  simpa [exitValue] using dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) he) (c : ℤ)

lemma bounded_congruent_eq {m u v : ℤ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hum : u < m) (hvm : v < m) (h : m ∣ u - v) : u = v := by
  by_cases huv : u ≤ v
  · have hd : m ∣ v - u := by simpa only [neg_sub] using dvd_neg.mpr h
    have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ v - u)
      (by omega : v - u < m) hd
    omega
  · have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ u - v)
      (by omega : u - v < m) h
    omega

/-- Two comb cylinders intersect only when both depth and nonzero digit agree. -/
theorem exit_congruent_iff {p e f c d : ℕ} (hp : 0 < p)
    (he : 0 < e) (hf : 0 < f) (hc : 0 < c) (hd : 0 < d)
    (hcp : c < p) (hdp : d < p) :
    ((p : ℤ) ^ min e f ∣ exitValue p e c - exitValue p f d) ↔ e = f ∧ c = d := by
  constructor
  · intro h
    have hef : e = f := by
      rcases lt_trichotomy e f with hlt | heq | hgt
      · rw [min_eq_left hlt.le] at h
        have hs := higher_exit_stem (p := p) (c := d) hlt
        have hz : (p : ℤ) ^ e ∣ exitValue p e c + 1 := by
          convert dvd_add h hs using 1
          ring
        exact (exit_not_stem hp he hc hcp hz).elim
      · exact heq
      · rw [min_eq_right hgt.le] at h
        have hs := higher_exit_stem (p := p) (c := c) hgt
        have hz : (p : ℤ) ^ f ∣ exitValue p f d + 1 := by
          convert dvd_sub hs h using 1
          ring
        exact (exit_not_stem hp hf hd hdp hz).elim
    subst f
    simp only [min_self] at h
    have hcB := exit_bounds hp he hc hcp
    have hdB := exit_bounds hp he hd hdp
    have hv : exitValue p e c + 1 = exitValue p e d + 1 :=
      bounded_congruent_eq hcB.1.le hdB.1.le hcB.2 hdB.2 (by simpa using h)
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp
    have heq : (c : ℤ) = d := by
      apply mul_right_cancel₀ (pow_ne_zero (e - 1) hpz.ne')
      simpa [exitValue] using hv
    exact ⟨rfl, by exact_mod_cast heq⟩
  · rintro ⟨rfl, rfl⟩
    simp

section Patterns
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def support (e : I → ℕ) : Finset I := univ.filter (fun i => e i ≠ 0)

lemma mem_support (e : I → ℕ) (i : I) : i ∈ support e ↔ e i ≠ 0 := by
  simp [support]

/-- Larger supports use larger exit digits wherever the alphabet permits it. -/
noncomputable def color (p e : I → ℕ) (i : I) : ℕ := min (support e).card (p i - 1)

noncomputable def point (p e : I → ℕ) (i : I) : ℤ :=
  if e i = 0 then -1 else exitValue (p i) (e i) (color p e i)

lemma color_bounds (p e : I → ℕ) (hp : ∀ i, 3 ≤ p i) (i : I)
    (hi : i ∈ support e) : 0 < color p e i ∧ color p e i < p i := by
  have hcard : 0 < (support e).card := card_pos.mpr ⟨i, hi⟩
  have hpi := hp i
  dsimp [color]
  omega

/-- A set of n distinct natural bases all at least three contains one at
least n+2. This is why a proper support inclusion can be distinguished. -/
lemma exists_large_base (p : I → ℕ) (hp : ∀ i, 3 ≤ p i)
    (hpi : Function.Injective p) (S : Finset I) (hS : S.Nonempty) :
    ∃ i ∈ S, S.card + 2 ≤ p i := by
  obtain ⟨i, hi, hmax⟩ := exists_max_image S p hS
  have hsub : S.image p ⊆ Icc 3 (p i) := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
    exact mem_Icc.mpr ⟨hp j, hmax j hj⟩
  have hh := card_le_card hsub
  rw [card_image_of_injective _ hpi, Nat.card_Icc] at hh
  exact ⟨i, hi, by have := hp i; omega⟩

/-- Every nonempty exponent pattern has a private point, simultaneously for
all other nonempty patterns. This asserts noncoverage, not coverage. -/
theorem private_pattern (p : I → ℕ) (hp : ∀ i, 3 ≤ p i) (hpi : Function.Injective p)
    (e f : I → ℕ) (hf : (support f).Nonempty) :
    (∀ i ∈ support f, (p i : ℤ) ^ f i ∣ point p e i -
      exitValue (p i) (f i) (color p f i)) ↔ e = f := by
  classical
  constructor
  · intro h
    have local_eq (i : I) (hi : i ∈ support f) :
        e i = f i ∧ color p e i = color p f i := by
      have hfi : 0 < f i := Nat.pos_of_ne_zero ((mem_support f i).mp hi)
      have hpi0 : 0 < p i := by have := hp i; omega
      have hcf := color_bounds p f hp i hi
      have hei : e i ≠ 0 := by
        intro hei
        have hh := h i hi
        simp only [point, if_pos hei] at hh
        have hd : (p i : ℤ) ^ f i ∣ exitValue (p i) (f i) (color p f i) + 1 := by
          convert dvd_neg.mpr hh using 1
          ring
        exact exit_not_stem hpi0 hfi hcf.1 hcf.2 hd
      have hce := color_bounds p e hp i ((mem_support e i).mpr hei)
      have hh := h i hi
      simp only [point, if_neg hei] at hh
      exact (exit_congruent_iff hpi0 (Nat.pos_of_ne_zero hei) hfi
        hce.1 hcf.1 hce.2 hcf.2).mp ((pow_dvd_pow (p i : ℤ) (min_le_right _ _)).trans hh)
    have hsub : support f ⊆ support e := by
      intro i hi
      exact (mem_support e i).mpr ((local_eq i hi).1.symm ▸ (mem_support f i).mp hi)
    have hsame : support f = support e := by
      by_contra hne
      have hcard : (support f).card < (support e).card :=
        card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      obtain ⟨i, hi, hlarge⟩ := exists_large_base p hp hpi (support f) hf
      have hc := (local_eq i hi).2
      dsimp [color] at hc
      omega
    funext i
    by_cases hi : i ∈ support f
    · exact (local_eq i hi).1
    · have hfi : f i = 0 := by simpa [mem_support] using hi
      have hei : e i = 0 := by
        have : i ∉ support e := by rwa [← hsame]
        simpa [mem_support] using this
      rw [hei, hfi]
  · rintro rfl i hi
    simp only [point, if_neg ((mem_support e i).mp hi), sub_self, dvd_zero]

/-- The all-stem point misses every nonempty pattern. -/
theorem stem_uncovered (p : I → ℕ) (hp : ∀ i, 3 ≤ p i)
    (e : I → ℕ) (he : (support e).Nonempty) :
    ¬ ∀ i ∈ support e, (p i : ℤ) ^ e i ∣ -1 - exitValue (p i) (e i) (color p e i) := by
  intro h
  obtain ⟨i, hi⟩ := he
  have hc := color_bounds p e hp i hi
  have hd : (p i : ℤ) ^ e i ∣ exitValue (p i) (e i) (color p e i) + 1 := by
    convert dvd_neg.mpr (h i hi) using 1
    ring
  exact exit_not_stem (by have := hp i; omega)
    (Nat.pos_of_ne_zero ((mem_support e i).mp hi)) hc.1 hc.2 hd
end Patterns

#print axioms exit_congruent_iff
#print axioms private_pattern
#print axioms stem_uncovered
end Erdos7PrimePowerCombFamily
