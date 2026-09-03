import Submission.RecursiveSieve
import Submission.SieveCertificateTransfer

/-! Transfer a first-hit numerical sieve from dominating reference marginals. -/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Adding independent virtual hits preserves the unit moment error. -/
theorem added_hits_moment_error (a q : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) -
        (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) (T : Finset ι) :
    |(∑ j ∈ Finset.range m, average a (fun η =>
        hitMonomial T (fun i => ω j i || η i))) -
      (m : ℝ) * ∏ i ∈ T, (a i + (1 - a i) * q i)| ≤ 1 := by
  let f (η : ι → Bool) :=
    (∑ j ∈ Finset.range m, hitMonomial (T.filter (fun i => η i = false)) (ω j)) -
      (m : ℝ) * ∏ i ∈ T.filter (fun i => η i = false), q i
  have hb (η : ι → Bool) : |f η| ≤ 1 := herr _
  have hl := average_mono a ha (fun _ => (-1 : ℝ)) f
    (fun η => (abs_le.mp (hb η)).1)
  have hu := average_mono a ha f (fun _ => (1 : ℝ))
    (fun η => (abs_le.mp (hb η)).2)
  rw [average_const] at hl hu
  have he : average a f =
      (∑ j ∈ Finset.range m, average a (fun η =>
        hitMonomial T (fun i => ω j i || η i))) -
      (m : ℝ) * ∏ i ∈ T, (a i + (1 - a i) * q i) := by
    unfold f
    rw [average_sub, average_sum, average_mul_const, average_restricted_prod]
    simp_rw [hitMonomial_or]
  rw [he] at hl hu
  exact abs_le.mpr ⟨hl, hu⟩

end Erdos970.FiniteSelberg

namespace Erdos970.RecursiveSieve
open FiniteSelberg

/-- Restrict natural-number indices to a finite initial segment. -/
def liftSet (k : ℕ) (T : Finset ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i.val ∈ T)

/-- Outside the finite index range, the extended pattern is identically hit. -/
def extendPattern {k : ℕ} (ω : Fin k → Bool) (i : ℕ) : Bool :=
  if h : i < k then ω ⟨i,h⟩ else true

theorem hit_extendPattern {k : ℕ} (T : Finset ℕ) (ω : Fin k → Bool) :
    hit T (extendPattern ω) = hitMonomial (liftSet k T) ω := by
  have he : (∀ i ∈ T, extendPattern ω i = true) ↔
      ∀ i ∈ liftSet k T, ω i = true := by
    constructor
    · intro h i hi
      have ht : i.val ∈ T := (Finset.mem_filter.mp hi).2
      simpa [extendPattern, i.isLt] using h i.val ht
    · intro h i hi
      unfold extendPattern
      split_ifs with hik
      · exact h ⟨i,hik⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      · rfl
  simp only [hit, hitMonomial_eq, he]
  split_ifs <;> rfl

/-- Moment bounds for the weighted population obtained by adjoining virtual hits. -/
theorem boosted_moment (k m : ℕ) (a : Fin k → ℝ) (ω : ℕ → Fin k → Bool)
    (T : Finset ℕ) :
    moment ((Finset.range m) ×ˢ (Finset.univ : Finset (Fin k → Bool)))
      (fun x => probability a x.2)
      (fun x => extendPattern (fun i => ω x.1 i || x.2 i)) T =
    ∑ j ∈ Finset.range m, average a (fun η =>
      hitMonomial (liftSet k T) (fun i => ω j i || η i)) := by
  unfold moment
  rw [Finset.sum_product]
  simp only [hit_extendPattern, average]

/-- Any positive recursive envelope at larger marginals forces a survivor at smaller
marginals. The numerical positivity requirement is explicit, not inferred here. -/
theorem survivor_from_dominating_envelope (k m : ℕ) (q q' : Fin k → ℝ)
    (hq : ∀ i, q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1)
    (ω : ℕ → Fin k → Bool)
    (herr : ∀ T : Finset (Fin k),
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) -
        (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (keep : ℕ → Finset ℕ → Bool)
    (hpos : 0 < (envelope
      (fun T => (m : ℝ) * ∏ i ∈ liftSet k T, q' i - 1)
      (fun T => (m : ℝ) * ∏ i ∈ liftSet k T, q' i + 1) keep k ∅).1) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  let a (i : Fin k) := (q' i - q i) / (1 - q i)
  have ha (i : Fin k) : 0 ≤ a i ∧ a i ≤ 1 := by
    have hd : 0 < 1 - q i := sub_pos.mpr (hq i).1
    refine ⟨div_nonneg (sub_nonneg.mpr (hq i).2.1) hd.le, ?_⟩
    exact (div_le_one hd).mpr (by linarith [(hq i).2.2])
  have hp (i : Fin k) : a i + (1 - a i) * q i = q' i := by
    have hd : 1 - q i ≠ 0 := (sub_pos.mpr (hq i).1).ne'
    dsimp [a]
    field_simp
    ring
  let A := (Finset.range m) ×ˢ (Finset.univ : Finset (Fin k → Bool))
  let w (x : ℕ × (Fin k → Bool)) := probability a x.2
  let v (x : ℕ × (Fin k → Bool)) := extendPattern (fun i => ω x.1 i || x.2 i)
  have hw : ∀ x ∈ A, 0 ≤ w x := by
    intro x hx
    apply Finset.prod_nonneg
    intro i hi
    split_ifs
    · exact (ha i).1
    · exact sub_nonneg.mpr (ha i).2
  have he (T : Finset ℕ) :
      |moment A w v T - (m : ℝ) * ∏ i ∈ liftSet k T, q' i| ≤ 1 := by
    have hh := added_hits_moment_error a q ha m ω herr (liftSet k T)
    simpa only [hp, A, w, v, boosted_moment] using hh
  obtain ⟨x, hx, hxall⟩ := weighted_survivor_of_positive_envelope A w v hw
    (fun T => (m : ℝ) * ∏ i ∈ liftSet k T, q' i - 1)
    (fun T => (m : ℝ) * ∏ i ∈ liftSet k T, q' i + 1) keep
    (fun T => by linarith [(abs_le.mp (he T)).1])
    (fun T => by linarith [(abs_le.mp (he T)).2]) k hpos
  refine ⟨x.1, Finset.mem_range.mp (Finset.mem_product.mp hx).1, ?_⟩
  intro i
  have hh := hxall i.val i.isLt
  simp only [v, extendPattern, i.isLt, ↓reduceDIte] at hh
  exact (Bool.or_eq_false_iff.mp hh).1

#print axioms added_hits_moment_error
#print axioms survivor_from_dominating_envelope
end Erdos970.RecursiveSieve
