import FormalConjecturesUtil

/-!
A finite-unit-residue certificate interface for arithmetic covering systems.
This is conditional: no odd certificate is instantiated in this file.
-/

namespace Erdos7FiniteUnitCover
open Set Pointwise

/-- A cover of the coprime residues, together with every prime-divisor class,
already covers the whole finite period. No higher pure-power geometry is fixed. -/
theorem finite_cover_of_unit_cover {I : Type*} (m : I → ℕ) (a : I → ℤ) (N : ℕ)
    (hprime : ∀ p, p.Prime → p ∣ N → ∃ i, m i=p ∧ (p : ℤ) ∣ a i)
    (hunit : ∀ r : Fin N, r.val.Coprime N → ∃ i, (m i : ℤ) ∣ (r.val : ℤ)-a i) :
    ∀ r : Fin N, ∃ i, (m i : ℤ) ∣ (r.val : ℤ)-a i := by
  intro r
  by_cases hr : r.val.Coprime N
  · exact hunit r hr
  · obtain ⟨p, hp, hpr, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hr
    obtain ⟨i, hi, ha⟩ := hprime p hp hpN
    refine ⟨i, ?_⟩
    rw [hi]
    exact dvd_sub (by exact_mod_cast hpr) ha

/-- The finite certificate transfers to every integer using a common period. -/
theorem arithmetic_cover_of_finite_cover {I : Type*}
    (m : I → ℕ) (a : I → ℤ) (N : ℕ) (hN : 0 < N)
    (hd : ∀ i, m i ∣ N)
    (hf : ∀ r : Fin N, ∃ i, (m i : ℤ) ∣ (r.val : ℤ)-a i) :
    ∀ z : ℤ, ∃ i, (m i : ℤ) ∣ z-a i := by
  intro z
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have h0 := Int.emod_nonneg z hNz.ne'
  have hlt := Int.emod_lt_of_pos z hNz
  let r : Fin N := ⟨(z % (N : ℤ)).toNat, by omega⟩
  have hr : (r.val : ℤ) = z % (N : ℤ) := Int.toNat_of_nonneg h0
  obtain ⟨i, hi⟩ := hf r
  have hz : (N : ℤ) ∣ z-z%(N : ℤ) := ⟨z/(N : ℤ), by have h := Int.emod_add_mul_ediv z (N : ℤ); omega⟩
  have hdi : (m i : ℤ) ∣ (N : ℤ) := by exact_mod_cast hd i
  refine ⟨i, ?_⟩
  have hh := dvd_add (hdi.trans hz) hi
  rw [hr] at hh
  convert hh using 1; ring

/-- Arithmetic wrapper with exactly the unit-domain obligations used by the
free-pure-power construction search. -/
theorem arithmetic_cover_of_unit_cover {I : Type*}
    (m : I → ℕ) (a : I → ℤ) (N : ℕ) (hN : 0 < N)
    (hd : ∀ i, m i ∣ N)
    (hprime : ∀ p, p.Prime → p ∣ N → ∃ i, m i=p ∧ (p : ℤ) ∣ a i)
    (hunit : ∀ r : Fin N, r.val.Coprime N → ∃ i, (m i : ℤ) ∣ (r.val : ℤ)-a i) :
    ∀ z : ℤ, ∃ i, (m i : ℤ) ∣ z-a i :=
  arithmetic_cover_of_finite_cover m a N hN hd
    (finite_cover_of_unit_cover m a N hprime hunit)

lemma span_norm (n : ℕ) : (Ideal.span {(n : ℤ)}).absNorm = n := by
  simp [Ideal.absNorm_span_singleton]

/-- A fully checked finite odd unit-domain certificate supplies precisely the
existential in Erdos7.erdos_7. This theorem does NOT assert that one exists. -/
theorem odd_strict_cover_of_unit_cover {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (N : ℕ) (hN : 0 < N)
    (hinj : Function.Injective m) (hm : ∀ i, 1 < m i ∧ Odd (m i))
    (hd : ∀ i, m i ∣ N)
    (hprime : ∀ p, p.Prime → p ∣ N → ∃ i, m i=p ∧ (p : ℤ) ∣ a i)
    (hunit : ∀ r : Fin N, r.val.Coprime N → ∃ i, (m i : ℤ) ∣ (r.val : ℤ)-a i) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  have hc := arithmetic_cover_of_unit_cover m a N hN hd hprime hunit
  let C : StrictCoveringSystem ℤ := {
    ι := I
    residue := a
    moduli := fun i => Ideal.span {(m i : ℤ)}
    unionCovers := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨i, hi⟩ := hc z
      refine ⟨i, ?_⟩
      rw [Set.mem_add]
      refine ⟨a i, Set.mem_singleton _, z-a i, ?_, by ring⟩
      exact Ideal.mem_span_singleton.mpr hi
    ne_bot := by
      intro i hi
      have hh := congrArg Ideal.absNorm hi
      simp only [span_norm, Ideal.absNorm_bot] at hh
      have := (hm i).1
      omega
    ne_top := by
      intro i hi
      have hh := congrArg Ideal.absNorm hi
      simp only [span_norm, Ideal.absNorm_top] at hh
      have := (hm i).1
      omega
    injective_moduli := by
      intro i j hi
      apply hinj
      have hh := congrArg Ideal.absNorm hi
      simpa only [span_norm] using hh }
  refine ⟨C, fun i => ⟨?_, C.ne_top i⟩⟩
  change ¬ Ideal.span {(m i : ℤ)} ≤ Ideal.span {2}
  rw [Ideal.span_singleton_le_span_singleton, ← even_iff_two_dvd,
    Int.not_even_iff_odd, Int.odd_coe_nat]
  exact (hm i).2

#print axioms finite_cover_of_unit_cover
#print axioms arithmetic_cover_of_unit_cover
#print axioms odd_strict_cover_of_unit_cover

end Erdos7FiniteUnitCover
