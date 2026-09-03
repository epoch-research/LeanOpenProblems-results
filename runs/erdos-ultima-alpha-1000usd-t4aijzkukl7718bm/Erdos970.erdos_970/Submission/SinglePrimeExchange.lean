import Submission.OptimalCoreExchange

/-! A limitation of one-new-prime exchanges: private points of large retained
classes cannot be eliminated by one different large-prime class. -/
namespace Erdos970.OptimalCoverCore

/-- Private positions belonging to different retained primes are disjoint. -/
theorem privatePositions_disjoint (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    {p q : ℕ} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    Disjoint (privatePositions m P r p) (privatePositions m P r q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj
  exact ((mem_survivors m (P.erase p) r i).mp hi'.1).2 q
    (Finset.mem_erase.mpr ⟨hpq.symm, hq⟩) hj'.2

/-- Two distinct primes whose product is at least the interval length have at
most one common hit. In particular this bounds the new hits among private points. -/
theorem private_new_prime_hit_card_le_one (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p q a : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hprod : m ≤ p * q) :
    ((privatePositions m P r p).filter (fun i => i ≡ a [MOD q])).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, hiq⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, hjq⟩ := Finset.mem_filter.mp hj
  obtain ⟨hi, hip⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, hjp⟩ := Finset.mem_filter.mp hj
  have him := ((mem_survivors m (P.erase p) r i).mp hi).1
  have hjm := ((mem_survivors m (P.erase p) r j).mp hj).1
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have he : i ≡ j [MOD p * q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      ⟨hip.trans hjp.symm, hiq.trans hjq.symm⟩
  exact he.eq_of_lt_of_lt (him.trans_le hprod) (hjm.trans_le hprod)

/-- At least one private point survives any such new prime class. -/
theorem exists_private_missed_by_new_prime (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p q a : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hprod : m ≤ p * q) (hprivate : 2 ≤ (privatePositions m P r p).card) :
    ∃ i ∈ privatePositions m P r p, ¬i ≡ a [MOD q] := by
  classical
  have hc := private_new_prime_hit_card_le_one m P r p q a hp hq hpq hprod
  have hh := Finset.card_filter_add_card_filter_not
    (s := privatePositions m P r p) (fun i => i ≡ a [MOD q])
  have hpos : 0 < ((privatePositions m P r p).filter (fun i => ¬i ≡ a [MOD q])).card := by
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

/-- One missed private point for each removed class gives distinct new survivors. -/
theorem removed_card_le_replacement_survivors (m : ℕ) (P E : Finset ℕ)
    (hE : E ⊆ P) (r s : ℕ → ℕ) (q : ℕ)
    (hagrees : ∀ p ∈ P \ E, s p = r p)
    (hmiss : ∀ p ∈ E, ∃ i ∈ privatePositions m P r p, ¬i ≡ s q [MOD q]) :
    E.card ≤ (survivors m ((P \ E) ∪ {q}) s).card := by
  classical
  choose f hf using fun p : E => hmiss p.val p.property
  have hmem (p : E) : f p ∈ survivors m ((P \ E) ∪ {q}) s := by
    obtain ⟨hi, hiq⟩ := hf p
    obtain ⟨hi, hip⟩ := Finset.mem_filter.mp hi
    obtain ⟨him, hiP⟩ := (mem_survivors m (P.erase p.val) r (f p)).mp hi
    apply (mem_survivors _ _ _ _).mpr
    refine ⟨him, ?_⟩
    intro v hv hiv
    rcases Finset.mem_union.mp hv with hv | hv
    · have hvP := Finset.mem_sdiff.mp hv
      have hvp : v ≠ p.val := by intro he; exact hvP.2 (he ▸ p.property)
      apply hiP v (Finset.mem_erase.mpr ⟨hvp, hvP.1⟩)
      simpa [hagrees v hv] using hiv
    · exact hiq (by simpa only [Finset.mem_singleton.mp hv] using hiv)
  let g : E → survivors m ((P \ E) ∪ {q}) s := fun p => ⟨f p, hmem p⟩
  have hinj : Function.Injective g := by
    intro p t heq
    have he : f p = f t := congrArg Subtype.val heq
    apply Subtype.ext
    by_contra hne
    have hd := privatePositions_disjoint m P r (hE p.property) (hE t.property) hne
    have ht := (hf t).1
    rw [← he] at ht
    exact Finset.disjoint_left.mp hd (hf p).1 ht
  exact Finset.card_le_card_of_injective hinj

/-- For a full cover, such an exchange strictly worsens the total budget. This
requires no global optimality hypothesis: the obstruction is purely positional. -/
theorem budget_lt_single_prime_replacement (m : ℕ) (P E : Finset ℕ)
    (hE : E ⊆ P) (r s : ℕ → ℕ) (q : ℕ) (hqP : q ∉ P)
    (hagrees : ∀ p ∈ P \ E, s p = r p)
    (hcover : survivors m P r = ∅)
    (hmiss : ∀ p ∈ E, ∃ i ∈ privatePositions m P r p, ¬i ≡ s q [MOD q]) :
    budget m P r < budget m ((P \ E) ∪ {q}) s := by
  classical
  have hc := removed_card_le_replacement_survivors m P E hE r s q hagrees hmiss
  have he := Finset.card_sdiff_add_card_eq_card hE
  have hdisj : Disjoint (P \ E) {q} := by
    simp only [Finset.disjoint_singleton_right]
    exact fun hh => hqP (Finset.mem_sdiff.mp hh).1
  simp only [budget, hcover, Finset.card_empty, Nat.add_zero,
    Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
  omega

/-- Thus a full cover with two private points per erased prime cannot be
improved by any one-new-prime exchange when all relevant products are large. -/
theorem budget_lt_single_large_prime_replacement (m : ℕ) (P E : Finset ℕ)
    (hE : E ⊆ P) (r s : ℕ → ℕ) (q : ℕ) (hq : q.Prime) (hqP : q ∉ P)
    (hprime : ∀ p ∈ E, p.Prime)
    (hagrees : ∀ p ∈ P \ E, s p = r p)
    (hcover : survivors m P r = ∅)
    (hprivate : ∀ p ∈ E, 2 ≤ (privatePositions m P r p).card)
    (hprod : ∀ p ∈ E, m ≤ p * q) :
    budget m P r < budget m ((P \ E) ∪ {q}) s := by
  apply budget_lt_single_prime_replacement m P E hE r s q hqP hagrees hcover
  intro p hp
  apply exists_private_missed_by_new_prime m P r p q (s q)
    (hprime p hp) hq _ (hprod p hp) (hprivate p hp)
  intro he
  exact hqP (he ▸ hE hp)

#print axioms budget_lt_single_large_prime_replacement
end Erdos970.OptimalCoverCore
