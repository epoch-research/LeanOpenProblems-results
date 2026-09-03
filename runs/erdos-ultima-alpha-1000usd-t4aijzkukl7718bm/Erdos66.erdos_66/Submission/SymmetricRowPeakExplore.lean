import Submission.CarryExplore
import Submission.TranslateExplore
import Submission.OriginRepairExplore
import Submission.TranslatedPrefixPaletteExplore

/-! A local restriction on literal row-based curve encodings. A row invariant
under a cyclic reflection forces a large integer representation count at one
of its two carry targets. This is not a nonexistence theorem for arbitrary
sets of natural numbers. -/
namespace Erdos66SymmetricRowPeak
open AdditiveCombinatorics Erdos66Carry Erdos66Translate Erdos66Explore
  Erdos66OriginRepair Erdos66TranslatedPrefixPalette
open scoped Classical

variable (p : ℕ) [NeZero p]

noncomputable def integerRow (X : Finset (ZMod p)) (a : ℕ) : Set ℕ :=
  Erdos66Translate.shift (↑(X.image ZMod.val)) a

/-- The two carry targets account for every reflected partner in a row. -/
theorem symmetric_row_split (X : Finset (ZMod p)) (t : ZMod p) (a : ℕ)
    (hX : ∀ x ∈ X, t-x ∈ X) :
    X.card = sumRep (integerRow p X a) (t.val+2*a) +
      sumRep (integerRow p X a) (t.val+p+2*a) := by
  have he : X.filter (fun x ↦ (t.val : ZMod p)-x ∈ X) = X := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    simpa using hX x hx
  have hh := cyclic_periodization p X t.val (ZMod.val_lt t)
  rw [he] at hh
  simpa only [integerRow, sumRep_shift] using hh

/-- A super-set of a reflected row inherits a peak at a target below twice
its right endpoint. The phase can be arbitrary. -/
theorem symmetric_row_peak (X : Finset (ZMod p)) (t : ZMod p) (a : ℕ)
    (hX : ∀ x ∈ X, t-x ∈ X) (A : Set ℕ) (hA : integerRow p X a ⊆ A) :
    ∃ n : ℕ, 2*a ≤ n ∧ n < 2*(a+p) ∧ X.card ≤ 2*sumRep A n := by
  have hh := symmetric_row_split p X t a hX
  have h₀ := sumRep_mono hA (t.val+2*a)
  have h₁ := sumRep_mono hA (t.val+p+2*a)
  have ht := ZMod.val_lt t
  by_cases hc : X.card ≤ 2*sumRep A (t.val+2*a)
  · exact ⟨t.val+2*a, by omega, by omega, hc⟩
  · exact ⟨t.val+p+2*a, by omega, by omega, by omega⟩

/-- Uniform logarithmic upper envelopes therefore bound the size of every
whole reflected row, not merely its average density. -/
theorem symmetric_row_envelope (X : Finset (ZMod p)) (t : ZMod p) (a : ℕ)
    (hX : ∀ x ∈ X, t-x ∈ X) (A : Set ℕ) (hA : integerRow p X a ⊆ A)
    (K : ℝ) (hK : ∀ n, 2*a ≤ n → n < 2*(a+p) → (sumRep A n : ℝ) ≤ K) :
    (X.card : ℝ) ≤ 2*K := by
  obtain ⟨n, hn₀, hn₁, hn⟩ := symmetric_row_peak p X t a hX A hA
  have hc : (X.card : ℝ) ≤ 2*(sumRep A n : ℝ) := by exact_mod_cast hn
  linarith [hK n hn₀ hn₁]

/-- The preceding peak estimate with a global logarithmic envelope. -/
theorem symmetric_row_log_envelope (X : Finset (ZMod p)) (t : ZMod p) (a : ℕ)
    (hX : ∀ x ∈ X, t-x ∈ X) (A : Set ℕ) (hA : integerRow p X a ⊆ A)
    (K C : ℝ) (hC : 0 ≤ C)
    (henv : ∀ n : ℕ, (sumRep A n : ℝ) ≤ K+C*Real.log (n+2)) :
    (X.card : ℝ) ≤ 2*(K+C*Real.log (2*(a+p)+2)) := by
  apply symmetric_row_envelope p X t a hX A hA
  intro n _ hn
  have hlog : Real.log ((n:ℝ)+2) ≤ Real.log (2*((a:ℝ)+p)+2) := by
    apply Real.log_le_log (by positivity)
    have hh : (n:ℝ) < 2*((a:ℝ)+p) := by exact_mod_cast hn
    linarith
  exact (henv n).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hC))

lemma shifted_reflection (X : Finset (ZMod p)) (s t : ZMod p)
    (hX : ∀ x ∈ X, t-x ∈ X) :
    ∀ x ∈ Erdos66TranslatedPrefixPalette.shift p X s,
      (2*s+t)-x ∈ Erdos66TranslatedPrefixPalette.shift p X s := by
  intro x hx
  rw [mem_shift] at hx ⊢
  have he : (2*s+t)-x-s = t-(x-s) := by ring
  rw [he]
  exact hX _ hx

noncomputable def parabolaRow [Fact p.Prime] (U : Finset (ZMod p)) (y : ZMod p) :
    Finset (ZMod p) := Finset.univ.filter (fun x ↦ (x,y) ∈ parabolaSet U)

lemma parabolaRow_neg [Fact p.Prime] (U : Finset (ZMod p)) (y : ZMod p) :
    ∀ x ∈ parabolaRow p U y, -x ∈ parabolaRow p U y := by
  intro x hx
  simpa only [parabolaRow, parabolaSet, Finset.mem_filter, Finset.mem_univ,
    true_and, neg_sq] using hx

/-- Horizontal phases do not remove the reflection peak of a full curve row.
No assertion is made here about arbitrary clipped portions of a row, or about
arbitrary phase changes at each individual point. -/
theorem translated_parabola_row_peak [Fact p.Prime] (U : Finset (ZMod p))
    (y s : ZMod p) (a : ℕ) (A : Set ℕ)
    (hA : integerRow p (Erdos66TranslatedPrefixPalette.shift p (parabolaRow p U y) s) a ⊆ A) :
    ∃ n : ℕ, 2*a ≤ n ∧ n < 2*(a+p) ∧ (parabolaRow p U y).card ≤ 2*sumRep A n := by
  have hh := symmetric_row_peak p
    (Erdos66TranslatedPrefixPalette.shift p (parabolaRow p U y) s) (2*s+0) a
    (shifted_reflection p (parabolaRow p U y) s 0 (fun x hx ↦ by
      simpa only [zero_sub] using parabolaRow_neg p U y x hx)) A hA
  simpa only [shift_card] using hh

end Erdos66SymmetricRowPeak
