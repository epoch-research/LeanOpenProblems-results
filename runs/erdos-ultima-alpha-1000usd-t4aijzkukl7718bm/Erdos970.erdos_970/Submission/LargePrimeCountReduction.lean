import Submission.ParitySeparation

/-! Exact count criteria for adjoining several one-hit prime classes.
This does not prove the largest-prime increment estimate. It identifies
higher-survivor-count consequences that any proof of that estimate must meet. -/
namespace Erdos970.IncrementReduction
open Finset OptimalCoverCore

/-- Every phase leaves at least t positions in the interval. -/
def PrimeSetCountBound (P : Finset ℕ) (m t : ℕ) : Prop :=
  ∀ r : ℕ → ℕ, t ≤ (survivors m P r).card

lemma primeSetCountBound_one (P : Finset ℕ) (m : ℕ) :
    PrimeSetCountBound P m 1 ↔ PrimeSetBound P m := by
  constructor
  · intro h r
    obtain ⟨i, hi⟩ := card_pos.mp (show 0 < (survivors m P r).card from h r)
    exact ⟨i, (mem_survivors _ _ _ _).mp hi⟩
  · intro h r
    obtain ⟨i, hi, ha⟩ := h r
    exact card_pos.mpr ⟨i, (mem_survivors _ _ _ _).mpr ⟨hi, ha⟩⟩

/-- A prescribed supply of distinct unused moduli can fill any population
of no greater cardinality. No primality or size condition is needed here. -/
lemma cover_remaining_with_prescribed_moduli (m : ℕ) (P R : Finset ℕ)
    (hdis : Disjoint P R) (r : ℕ → ℕ)
    (hcard : (survivors m P r).card ≤ R.card) :
    ∃ s : ℕ → ℕ, (∀ p ∈ P, s p = r p) ∧
      ∀ i < m, ∃ p ∈ P ∪ R, i ≡ s p [MOD p] := by
  classical
  let S := survivors m P r
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card S ≤ Fintype.card R by simpa only [Fintype.card_coe] using hcard)
  let s : ℕ → ℕ := fun p => if h : ∃ x : S, (f x).val = p then
    (Classical.choose h).val else r p
  have hsP (p : ℕ) (hp : p ∈ P) : s p = r p := by
    have hn : ¬∃ x : S, (f x).val = p := by
      rintro ⟨x, hx⟩
      exact disjoint_left.mp hdis hp (hx ▸ (f x).property)
    simp only [s, dif_neg hn]
  have hsR (x : S) : s (f x).val = x.val := by
    have hex : ∃ y : S, (f y).val = (f x).val := ⟨x, rfl⟩
    have he : Classical.choose hex = x :=
      f.injective (Subtype.ext (Classical.choose_spec hex))
    simp only [s, dif_pos hex, he]
  refine ⟨s, hsP, fun i hi => ?_⟩
  by_cases hiS : i ∈ S
  · let x : S := ⟨i, hiS⟩
    refine ⟨(f x).val, mem_union_right _ (f x).property, ?_⟩
    rw [hsR x]
  · have hnot : ¬∀ p ∈ P, ¬i ≡ r p [MOD p] := by
      intro ha
      exact hiS ((mem_survivors _ _ _ _).mpr ⟨hi, ha⟩)
    push_neg at hnot
    obtain ⟨p, hp, hip⟩ := hnot
    exact ⟨p, mem_union_left _ hp, by rwa [hsP p hp]⟩

/-- In the other direction, one-hit coordinates cannot cover more old
survivors than there are new coordinates. -/
lemma survivor_card_le_of_oneHit_cover (m : ℕ) (P R : Finset ℕ) (r : ℕ → ℕ)
    (hinj : ∀ p ∈ R, Set.InjOn (fun i => i % p) (↑(survivors m P r) : Set ℕ))
    (hcover : ∀ i < m, ∃ p ∈ P ∪ R, i ≡ r p [MOD p]) :
    (survivors m P r).card ≤ R.card := by
  classical
  let S := survivors m P r
  have hex (x : S) : ∃ p : R, x.val ≡ r p.val [MOD p.val] := by
    obtain ⟨hxm, hxa⟩ := (mem_survivors _ _ _ _).mp x.property
    obtain ⟨p, hp, hxp⟩ := hcover x.val hxm
    rcases mem_union.mp hp with hp | hp
    · exact False.elim (hxa p hp hxp)
    · exact ⟨⟨p, hp⟩, hxp⟩
  choose f hf using hex
  apply card_le_card_of_injective (f := f)
  intro x y hxy
  apply Subtype.ext
  apply hinj (f x).val (f x).property x.property y.property
  exact (hf x).trans (by simpa only [hxy] using (hf y).symm)

/-- Exact criterion whenever every new modulus is one-hit on every old phase. -/
theorem primeSetBound_union_iff_count_of_injective (m : ℕ) (P R : Finset ℕ)
    (hdis : Disjoint P R)
    (hinj : ∀ r : ℕ → ℕ, ∀ p ∈ R,
      Set.InjOn (fun i => i % p) (↑(survivors m P r) : Set ℕ)) :
    PrimeSetBound (P ∪ R) m ↔ PrimeSetCountBound P m (R.card + 1) := by
  classical
  constructor
  · intro hb r
    by_contra hcount
    obtain ⟨s, _, hs⟩ := cover_remaining_with_prescribed_moduli m P R hdis r (by omega)
    obtain ⟨i, hi, ha⟩ := hb s
    obtain ⟨p, hp, hip⟩ := hs i hi
    exact ha p hp hip
  · intro hc r
    by_contra hbad
    push_neg at hbad
    have h := survivor_card_le_of_oneHit_cover m P R r (hinj r) hbad
    have := hc r
    omega

/-- Prescribed primes at least the interval length are one-hit, so the
criterion is exactly an old survivor count, not merely a sufficient bound. -/
theorem primeSetBound_union_large_iff_count (m : ℕ) (P R : Finset ℕ)
    (hdis : Disjoint P R) (hlarge : ∀ p ∈ R, m ≤ p) :
    PrimeSetBound (P ∪ R) m ↔ PrimeSetCountBound P m (R.card + 1) := by
  apply primeSetBound_union_iff_count_of_injective m P R hdis
  intro r p hp i hi j hj hij
  have him := ((mem_survivors _ _ _ _).mp hi).1
  have hjm := ((mem_survivors _ _ _ _).mp hj).1
  exact Nat.ModEq.eq_of_lt_of_lt hij (him.trans_le (hlarge p hp)) (hjm.trans_le (hlarge p hp))

/-- With parity already present, all new odd primes only need 2p>=m. -/
theorem primeSetBound_union_half_large_iff_count (m : ℕ) (P R : Finset ℕ)
    (h2 : 2 ∈ P) (hdis : Disjoint P R)
    (hR : ∀ p ∈ R, p.Prime) (hlarge : ∀ p ∈ R, m ≤ 2 * p) :
    PrimeSetBound (P ∪ R) m ↔ PrimeSetCountBound P m (R.card + 1) := by
  apply primeSetBound_union_iff_count_of_injective m P R hdis
  intro r p hp i hi j hj hij
  have hip := (mem_survivors _ _ _ _).mp hi
  have hjp := (mem_survivors _ _ _ _).mp hj
  have hp2 : p ≠ 2 := by rintro rfl; exact disjoint_left.mp hdis h2 hp
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := two_mul_le_sub_of_modEq (hR p hp) hp2 hlt (hip.2 2 h2) (hjp.2 2 h2) hij
    have := hlarge p hp
    omega
  · have h := two_mul_le_sub_of_modEq (hR p hp) hp2 hgt (hjp.2 2 h2) (hip.2 2 h2) hij.symm
    have := hlarge p hp
    omega

#print axioms primeSetBound_union_large_iff_count
#print axioms primeSetBound_union_half_large_iff_count
end Erdos970.IncrementReduction
