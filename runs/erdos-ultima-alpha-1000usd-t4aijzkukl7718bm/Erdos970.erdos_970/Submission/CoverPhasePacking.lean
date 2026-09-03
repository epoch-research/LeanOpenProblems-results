import Submission.OptimalCoverCore

/-! A simultaneous-CRT constraint on two covers. This retains the agreement
of the phases on a common core. It is not an unrestricted quadratic bound. -/
namespace Erdos970.CoverPhasePacking
open Finset OptimalCoverCore

/-- Both phases cover U using primes in D, and choose different residues at
each prime. If distinct prime products exceed the ambient interval length,
then U injects into ordered pairs of distinct primes. -/
theorem card_le_offDiag_of_two_covers
    (U D : Finset ℕ) (m : ℕ) (r s : ℕ → ℕ)
    (hUm : U ⊆ range m) (hD : ∀ p ∈ D, p.Prime)
    (hprod : ∀ p ∈ D, ∀ q ∈ D, p ≠ q → m ≤ p * q)
    (hne : ∀ p ∈ D, ¬r p ≡ s p [MOD p])
    (hr : ∀ x ∈ U, ∃ p ∈ D, x ≡ r p [MOD p])
    (hs : ∀ x ∈ U, ∃ p ∈ D, x ≡ s p [MOD p]) :
    U.card ≤ D.card * (D.card - 1) := by
  classical
  have hex (x : U) : ∃ a : D.offDiag,
      x.val ≡ r a.val.1 [MOD a.val.1] ∧
      x.val ≡ s a.val.2 [MOD a.val.2] := by
    obtain ⟨p, hp, hxp⟩ := hr x.val x.property
    obtain ⟨q, hq, hxq⟩ := hs x.val x.property
    have hpq : p ≠ q := by
      rintro rfl
      exact hne p hp (hxp.symm.trans hxq)
    exact ⟨⟨(p, q), mem_offDiag.mpr ⟨hp, hq, hpq⟩⟩, hxp, hxq⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y he
    have hx := hf x
    have hy := hf y
    rw [← he] at hy
    obtain ⟨hp, hq, hpq⟩ := mem_offDiag.mp (f x).property
    have hcop : (f x).val.1.Coprime (f x).val.2 :=
      (Nat.coprime_primes (hD _ hp) (hD _ hq)).mpr hpq
    have hxy := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩
    have hlen := hprod _ hp _ hq hpq
    exact Subtype.ext (hxy.eq_of_lt_of_lt
      ((mem_range.mp (hUm x.property)).trans_le hlen)
      ((mem_range.mp (hUm y.property)).trans_le hlen))
  have hh := card_le_card_of_injective hinj
  simpa only [offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one] using hh

/-- Coordinates where two residue phases actually differ. -/
noncomputable def differing (P : Finset ℕ) (r s : ℕ → ℕ) : Finset ℕ :=
  P.filter (fun p => ¬r p ≡ s p [MOD p])

/-- On the common core, the survivor set is the same for the two phases. -/
lemma common_survivors_eq (P : Finset ℕ) (m : ℕ) (r s : ℕ → ℕ) :
    survivors m (P \ differing P r s) r = survivors m (P \ differing P r s) s := by
  classical
  ext x
  simp only [mem_survivors]
  constructor <;> rintro ⟨hx, ha⟩ <;> refine ⟨hx, fun p hp hxp => ?_⟩
  · have hpP := (mem_sdiff.mp hp).1
    have he : r p ≡ s p [MOD p] := by
      by_contra hn
      exact (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨hpP, hn⟩)
    exact ha p hp (hxp.trans he.symm)
  · have hpP := (mem_sdiff.mp hp).1
    have he : r p ≡ s p [MOD p] := by
      by_contra hn
      exact (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨hpP, hn⟩)
    exact ha p hp (hxp.trans he)

/-- The shared core of two covers can have at most j(j-1) survivors, where j
is the number of changed coordinates. The large-product assumption applies
only to these changed coordinates, not to the common core. -/
theorem common_core_card_le
    (P : Finset ℕ) (m : ℕ) (r s : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ differing P r s, ∀ q ∈ differing P r s,
      p ≠ q → m ≤ p * q)
    (hr : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p])
    (hs : ∀ x < m, ∃ p ∈ P, x ≡ s p [MOD p]) :
    (survivors m (P \ differing P r s) r).card ≤
      (differing P r s).card * ((differing P r s).card - 1) := by
  classical
  apply card_le_offDiag_of_two_covers _ _ m r s
  · exact filter_subset _ _
  · intro p hp
    exact hP p (mem_filter.mp hp).1
  · exact hprod
  · intro p hp
    exact (mem_filter.mp hp).2
  · intro x hx
    obtain ⟨hxm, hxcore⟩ := (mem_survivors _ _ _ _).mp hx
    obtain ⟨p, hp, hxp⟩ := hr x hxm
    refine ⟨p, ?_, hxp⟩
    by_contra hpD
    exact hxcore p (mem_sdiff.mpr ⟨hp, hpD⟩) hxp
  · intro x hx
    rw [common_survivors_eq] at hx
    obtain ⟨hxm, hxcore⟩ := (mem_survivors _ _ _ _).mp hx
    obtain ⟨p, hp, hxp⟩ := hs x hxm
    refine ⟨p, ?_, hxp⟩
    by_contra hpD
    exact hxcore p (mem_sdiff.mpr ⟨hp, hpD⟩) hxp

#print axioms card_le_offDiag_of_two_covers
#print axioms common_survivors_eq
#print axioms common_core_card_le
end Erdos970.CoverPhasePacking
