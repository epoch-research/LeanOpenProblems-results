import Submission.ContinuousIntervalSeeded
import Submission.ContinuousIntervalReference

/-! Adjoining any missing initial primes makes an exact wheel seed legitimate.
A b-prime seed followed by k tail stages bounds arbitrary original k-prime sets.
The numerical positivity premise remains explicit. -/
namespace Erdos970.ContinuousInterval
open IntervalRescaling

/-- If all initial b primes occur in an increasing prime list, they are exactly
its first b entries. -/
theorem sorted_prime_prefix_eq {K : ℕ} (p : Fin K → ℕ)
    (hp : ∀ i, (p i).Prime) (hm : StrictMono p) (b : ℕ) (hb : b ≤ K)
    (hmem : ∀ i < b, ∃ j : Fin K, p j = Nat.nth Nat.Prime i) :
    ∀ i : ℕ, (hi : i < b) → p ⟨i, hi.trans_le hb⟩ = Nat.nth Nat.Prime i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have hlo := FiniteSelberg.nth_prime_le_sorted p hp hm ⟨i, hi.trans_le hb⟩
    obtain ⟨j, hj⟩ := hmem i hi
    have hij : i ≤ j.val := by
      by_contra hbad
      have hji : j.val < i := by omega
      have he := ih j.val hji (hji.trans hi)
      have heq : Nat.nth Nat.Prime j.val = Nat.nth Nat.Prime i := he.symm.trans hj
      have hidx := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective heq
      omega
    exact le_antisymm ((hm.monotone hij).trans_eq hj) hlo

/-- The bounds of a fixed prefix depend only on its indexed moduli. -/
lemma IntervalBounds.congr_prefix {L U : ℝ → ℝ} {α : ℝ} {p q : ℕ → ℕ} {b : ℕ}
    (h : IntervalBounds L U α p b) (hpq : ∀ i < b, q i = p i) :
    IntervalBounds L U α q b := by
  intro m r
  have he : count q r b m = count p r b m := by
    unfold count
    congr 1
    apply Finset.filter_congr
    intro x hx
    constructor <;> intro hh i hi
    · simpa only [hpq i hi] using hh i hi
    · simpa only [hpq i hi] using hh i hi
  rw [he]
  exact h m r

/-- Force the initial b primes by adjoining those missing from the original
set, then pad to b+k primes. The exact seed is used only for that actual prefix.
All k later stages transfer to larger primes by the proved Jensen argument. -/
theorem isJacobsthalBound_of_seedRun {d : ℝ} {L U : ℝ → ℝ}
    (b k m : ℕ) (cells : ℕ → List ℕ)
    (hr : Regular d L U) (hs : IntervalBounds L U 1 (Nat.nth Nat.Prime) b)
    (hpos : 0 < (seedRun (fun i => (referenceMarginal i : ℝ)) cells b L U k).1 m) :
    IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  let B : Finset ℕ := (Finset.range b).image (Nat.nth Nat.Prime)
  have hB : ∀ q ∈ B, q.Prime := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.prime_nth_prime i
  have hBcard : B.card = b := by
    rw [Finset.card_image_of_injective _ (Nat.nth_strictMono Nat.infinite_setOf_prime).injective]
    exact Finset.card_range b
  let A := P ∪ B
  have hA : ∀ q ∈ A, q.Prime := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hP q hq
    · exact hB q hq
  have hAc : A.card ≤ b + k := by
    have hh := Finset.card_union_le P B
    dsimp [A]
    omega
  obtain ⟨R, hR, hRc⟩ := Nat.infinite_setOf_prime.exists_subset_card_eq (b + k)
  have hlarge : b + k ≤ (A ∪ R).card := by
    rw [← hRc]
    exact Finset.card_le_card Finset.subset_union_right
  obtain ⟨T, hAT, hTAR, hTc⟩ :=
    Finset.exists_subsuperset_card_eq Finset.subset_union_left hAc hlarge
  have hT : ∀ q ∈ T, q.Prime := by
    intro q hq
    rcases Finset.mem_union.mp (hTAR hq) with hq | hq
    · exact hA q hq
    · exact hR hq
  let p : Fin (b + k) → ℕ := T.orderEmbOfFin hTc
  have hpp : ∀ i, (p i).Prime := fun i => hT _ (T.orderEmbOfFin_mem hTc i)
  have hpm : StrictMono p := (T.orderEmbOfFin hTc).strictMono
  have hprange : Set.range p = (↑T : Set ℕ) := T.range_orderEmbOfFin hTc
  have hprefix : ∀ i < b, ∃ j : Fin (b + k), p j = Nat.nth Nat.Prime i := by
    intro i hi
    change Nat.nth Nat.Prime i ∈ Set.range p
    rw [hprange]
    apply hAT
    exact Finset.mem_union_right P (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
  have hpre := sorted_prime_prefix_eq p hpp hpm b (by omega) hprefix
  let p' (i : ℕ) := if h : i < b + k then p ⟨i, h⟩ else 2
  have hpp' : ∀ i < b + k, 1 < p' i := by
    intro i hi
    simpa only [p', dif_pos hi] using (hpp ⟨i, hi⟩).one_lt
  have hcc : ∀ i < b + k, ∀ j < i, (p' i).Coprime (p' j) := by
    intro i hi j hj
    have hjK : j < b + k := hj.trans hi
    simp only [p', dif_pos hi, dif_pos hjK]
    exact (Nat.coprime_primes (hpp ⟨i, hi⟩) (hpp ⟨j, hjK⟩)).mpr (ne_of_gt (hpm hj))
  have hseed : IntervalBounds L U 1 p' b := hs.congr_prefix (by
    intro i hi
    simp only [p', dif_pos (show i < b + k by omega), hpre i hi])
  have hQ : ∀ i < k, 1 / (p' (b + i) : ℝ) ≤ (referenceMarginal (b + i) : ℝ) ∧
      (referenceMarginal (b + i) : ℝ) ≤ 1 := by
    intro i hi
    have hiK : b + i < b + k := by omega
    have hn := FiniteSelberg.nth_prime_le_sorted p hpp hpm ⟨b + i, hiK⟩
    have hnpos : (0 : ℝ) < Nat.nth Nat.Prime (b + i) := by
      exact_mod_cast (Nat.prime_nth_prime (b + i)).pos
    simp only [referenceMarginal, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, p', dif_pos hiK]
    exact ⟨one_div_le_one_div_of_le hnpos (by exact_mod_cast hn),
      (div_le_one hnpos).mpr (by exact_mod_cast (Nat.prime_nth_prime (b + i)).one_lt.le)⟩
  obtain ⟨x, hx, hxa⟩ := survivor_of_positive_seedRun p'
    (fun i => (referenceMarginal i : ℝ)) cells b k hr hseed hpp' hcc hQ m hpos
    (fun i => r (p' i))
  obtain ⟨q, hqP, hxq⟩ := hcover x hx
  have hqT : q ∈ T := hAT (Finset.mem_union_left B hqP)
  have hqrange : q ∈ Set.range p := hprange.symm ▸ hqT
  obtain ⟨i, rfl⟩ := hqrange
  have hh := hxa i.val i.isLt
  simp only [p', dif_pos i.isLt] at hh
  exact hh hxq

theorem jacobsthalFunction_le_of_seedRun {d : ℝ} {L U : ℝ → ℝ}
    (b k m : ℕ) (cells : ℕ → List ℕ)
    (hr : Regular d L U) (hs : IntervalBounds L U 1 (Nat.nth Nat.Prime) b)
    (hpos : 0 < (seedRun (fun i => (referenceMarginal i : ℝ)) cells b L U k).1 m) :
    jacobsthalFunction k ≤ m :=
  (jacobsthalFunction_le_iff k m).mpr (isJacobsthalBound_of_seedRun b k m cells hr hs hpos)

#print axioms sorted_prime_prefix_eq
#print axioms isJacobsthalBound_of_seedRun
end Erdos970.ContinuousInterval
