import Submission.IntervalRescaling
import Submission.OptimalCoverCore

/-! Exact rescaling of required hits together with forbidden hits. Unlike an
intersection moment, a mixed pattern retains avoidance of the other primes.
These are structural and conditional bounds, not a uniform quadratic estimate. -/
namespace Erdos970.MixedPattern
open IntervalRescaling OptimalCoverCore BlockSieve.SievePolynomial BrunCriterion

noncomputable def positions (m : ℕ) (A B : Finset ℕ) (r : ℕ → ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun x =>
    (∀ p ∈ A, x ≡ r p [MOD p]) ∧ ∀ q ∈ B, ¬x ≡ r q [MOD q])

noncomputable def mixedCount (m : ℕ) (A B : Finset ℕ) (r : ℕ → ℕ) : ℕ :=
  (positions m A B r).card

lemma survivors_mono_length (P : Finset ℕ) (r : ℕ → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    survivors m P r ⊆ survivors n P r := by
  intro x hx
  obtain ⟨hxm, hxP⟩ := (mem_survivors _ _ _ _).mp hx
  exact (mem_survivors _ _ _ _).mpr ⟨hxm.trans_le hmn, hxP⟩

/-- The product of required primes is coprime to every disjoint avoided prime. -/
lemma product_coprime {A B : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hB : ∀ p ∈ B, p.Prime) (hdis : Disjoint A B) {q : ℕ} (hq : q ∈ B) :
    (∏ p ∈ A, p).Coprime q := by
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply (Nat.coprime_primes (hA p hp) (hB q hq)).mpr
  intro he
  exact Finset.disjoint_left.mp hdis hp (he ▸ hq)

/-- A mixed pattern is one CRT progression sifted by the avoided prime set.
Both its actual length and the pulled-back residues are retained explicitly. -/
theorem mixedCount_rescale_exact (m : ℕ) (A B : Finset ℕ) (r : ℕ → ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hB : ∀ p ∈ B, p.Prime) (hdis : Disjoint A B) :
    ∃ c : ℕ, ∃ s : ℕ → ℕ,
      m / (∏ p ∈ A, p) ≤ c ∧ c ≤ ceilQuotient m (∏ p ∈ A, p) ∧
      c = mixedCount m A ∅ r ∧ mixedCount m A B r = (survivors c B s).card := by
  classical
  let D := ∏ p ∈ A, p
  have hD : 0 < D := Finset.prod_pos (fun p hp => (hA p hp).pos)
  obtain ⟨a₀, ha₀⟩ := intersection_residue A hA r
  let a := a₀ % D
  let c := progressionLength m D a hD
  have hex (q : B) : ∃ s : ℕ, ∀ t : ℕ,
      a + D * t ≡ r q [MOD q.val] ↔ t ≡ s [MOD q.val] :=
    exists_affine_residue a D q.val (r q) (hB q q.property).pos
      (product_coprime hA hB hdis q.property)
  choose s₀ hs₀ using hex
  let s : ℕ → ℕ := fun q => if hq : q ∈ B then s₀ ⟨q, hq⟩ else 0
  have hs (q : ℕ) (hq : q ∈ B) (t : ℕ) :
      a + D * t ≡ r q [MOD q] ↔ t ≡ s q [MOD q] := by
    simpa only [s, dif_pos hq] using hs₀ ⟨q, hq⟩ t
  obtain ⟨hcl, hcu⟩ := progressionLength_bounds m D a₀ hD
  refine ⟨c, s, hcl, hcu, ?_, ?_⟩
  · change progressionLength m D (a₀ % D) hD = _
    rw [progressionLength_eq_card]
    congr 1
    ext x
    simp only [positions, Finset.mem_filter, Finset.mem_range,
      Finset.notMem_empty, false_implies, forall_const, and_true]
    exact and_congr_right (fun _ => (ha₀ x).symm)
  have he : positions m A B r = (survivors c B s).image (fun t => a + D * t) := by
    ext x
    simp only [positions, Finset.mem_filter, Finset.mem_range, Finset.mem_image,
      mem_survivors]
    constructor
    · rintro ⟨hxm, hxA, hxB⟩
      have hxmem : x ∈ (Finset.range m).filter (fun x => x ≡ a₀ [MOD D]) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxm, (ha₀ x).mp hxA⟩
      rw [residueClass_eq_image m D a₀ hD] at hxmem
      obtain ⟨t, ht, htx⟩ := Finset.mem_image.mp hxmem
      refine ⟨t, ⟨Finset.mem_range.mp ht, ?_⟩, htx⟩
      intro q hq hbad
      apply hxB q hq
      rw [← htx]
      exact (hs q hq t).mpr hbad
    · rintro ⟨t, ⟨ht, htB⟩, rfl⟩
      refine ⟨(lt_progressionLength_iff m D a hD t).mp ht, ?_, ?_⟩
      · apply (ha₀ _).mpr
        change a₀ % D + D * t ≡ a₀ [MOD D]
        simp [Nat.ModEq]
      · intro q hq hbad
        exact htB q hq ((hs q hq t).mp hbad)
  rw [mixedCount, he, Finset.card_image_of_injective]
  intro t u htu
  exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel htu)

/-- The version that keeps only the floor/ceiling enclosure. -/
theorem mixedCount_rescale (m : ℕ) (A B : Finset ℕ) (r : ℕ → ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hB : ∀ p ∈ B, p.Prime) (hdis : Disjoint A B) :
    ∃ c : ℕ, ∃ s : ℕ → ℕ,
      m / (∏ p ∈ A, p) ≤ c ∧ c ≤ ceilQuotient m (∏ p ∈ A, p) ∧
      mixedCount m A B r = (survivors c B s).card := by
  obtain ⟨c, s, hl, hu, hc, he⟩ := mixedCount_rescale_exact m A B r hA hB hdis
  exact ⟨c, s, hl, hu, he⟩

/-- Any universal interval bounds for the avoided set transfer to the mixed
count at the floor and ceiling lengths. -/
theorem mixedCount_bounds (m : ℕ) (A B : Finset ℕ) (r : ℕ → ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hB : ∀ p ∈ B, p.Prime) (hdis : Disjoint A B)
    (L U : ℕ → ℕ)
    (hL : ∀ n s, L n ≤ (survivors n B s).card)
    (hU : ∀ n s, (survivors n B s).card ≤ U n) :
    L (m / (∏ p ∈ A, p)) ≤ mixedCount m A B r ∧
      mixedCount m A B r ≤ U (ceilQuotient m (∏ p ∈ A, p)) := by
  obtain ⟨c, s, hcl, hcu, he⟩ := mixedCount_rescale m A B r hA hB hdis
  rw [he]
  exact ⟨(hL _ s).trans (Finset.card_le_card (survivors_mono_length B s hcl)),
    (Finset.card_le_card (survivors_mono_length B s hcu)).trans (hU _ s)⟩

/-- Integer counts between adjacent endpoints have an exact affine expression.
No continuity or regularity assumption on f is needed. -/
lemma interpolate_adjacent (f : ℕ → ℤ) {l h c : ℕ}
    (hl : l ≤ c) (hu : c ≤ h) (hh : h ≤ l + 1) :
    f c = f l + ((c : ℤ) - l) * (f h - f l) := by
  by_cases he : h = l
  · have hc : c = l := by omega
    simp [he, hc]
  · have he' : h = l + 1 := by omega
    have hc : c = l ∨ c = h := by omega
    rcases hc with rfl | rfl
    · simp
    · rw [he']
      push_cast
      ring

/-- A stronger pair of LINEAR constraints retains the actual required-hit count
instead of independently replacing each child length by the worst endpoint.
This uses integrality of that count, not a fractional interpolation assumption. -/
theorem mixedCount_bounds_interpolated (m : ℕ) (A B : Finset ℕ) (r : ℕ → ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hB : ∀ p ∈ B, p.Prime) (hdis : Disjoint A B)
    (L U : ℕ → ℕ)
    (hL : ∀ n s, L n ≤ (survivors n B s).card)
    (hU : ∀ n s, (survivors n B s).card ≤ U n) :
    let l := m / (∏ p ∈ A, p)
    let h := ceilQuotient m (∏ p ∈ A, p)
    (L l : ℤ) + ((mixedCount m A ∅ r : ℤ) - l) * ((L h : ℤ) - L l) ≤
      (mixedCount m A B r : ℤ) ∧
    (mixedCount m A B r : ℤ) ≤
      (U l : ℤ) + ((mixedCount m A ∅ r : ℤ) - l) * ((U h : ℤ) - U l) := by
  dsimp only
  obtain ⟨c, s, hcl, hcu, hc, he⟩ := mixedCount_rescale_exact m A B r hA hB hdis
  have hh : ceilQuotient m (∏ p ∈ A, p) ≤ m / (∏ p ∈ A, p) + 1 := by
    unfold ceilQuotient
    split_ifs <;> omega
  have hli := interpolate_adjacent (fun n => (L n : ℤ)) hcl hcu hh
  have hui := interpolate_adjacent (fun n => (U n : ℤ)) hcl hcu hh
  rw [← hc, ← hli, ← hui, he]
  dsimp only
  constructor
  · exact_mod_cast hL c s
  · exact_mod_cast hU c s

/-- Required hits and forbidden hits on overlapping prime sets are inconsistent. -/
lemma positions_eq_empty_of_not_disjoint {m : ℕ} {A B : Finset ℕ} {r : ℕ → ℕ}
    (h : ¬Disjoint A B) : positions m A B r = ∅ := by
  classical
  obtain ⟨p, hpA, hpB⟩ := Finset.not_disjoint_iff.mp h
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨_, hxA, hxB⟩ := Finset.mem_filter.mp hx
  exact hxB p hpB (hxA p hpA)

#print axioms mixedCount_rescale_exact
#print axioms mixedCount_rescale
#print axioms mixedCount_bounds
#print axioms mixedCount_bounds_interpolated
end Erdos970.MixedPattern
