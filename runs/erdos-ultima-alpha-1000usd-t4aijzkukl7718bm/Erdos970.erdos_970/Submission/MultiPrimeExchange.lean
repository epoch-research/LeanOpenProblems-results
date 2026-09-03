import Submission.SinglePrimeExchange

/-! Necessary conditions for multi-prime budget improvements. These do not
assert existence of improving exchanges. -/
namespace Erdos970.OptimalCoverCore

noncomputable def fullyReplaced (m : ℕ) (P E R : Finset ℕ) (r s : ℕ → ℕ) : Finset ℕ :=
  E.filter (fun p => ∀ i ∈ privatePositions m P r p, ∃ q ∈ R, i ≡ s q [MOD q])

/-- Private witnesses for any subset of the erased primes are distinct survivors. -/
theorem private_witness_card_le (m : ℕ) (P E R U : Finset ℕ)
    (hE : E ⊆ P) (hU : U ⊆ E) (r s : ℕ → ℕ)
    (hagrees : ∀ p ∈ P \ E, s p = r p)
    (hmiss : ∀ p ∈ U, ∃ i ∈ privatePositions m P r p,
      ∀ q ∈ R, ¬i ≡ s q [MOD q]) :
    U.card ≤ (survivors m ((P \ E) ∪ R) s).card := by
  classical
  choose f hf using fun p : U => hmiss p.val p.property
  have hmem (p : U) : f p ∈ survivors m ((P \ E) ∪ R) s := by
    obtain ⟨hi, hiR⟩ := hf p
    obtain ⟨hi, hip⟩ := Finset.mem_filter.mp hi
    obtain ⟨him, hiP⟩ := (mem_survivors m (P.erase p.val) r (f p)).mp hi
    apply (mem_survivors _ _ _ _).mpr
    refine ⟨him, ?_⟩
    intro v hv hiv
    rcases Finset.mem_union.mp hv with hv | hv
    · have hvP := Finset.mem_sdiff.mp hv
      have hvp : v ≠ p.val := by intro he; exact hvP.2 (he ▸ hU p.property)
      apply hiP v (Finset.mem_erase.mpr ⟨hvp, hvP.1⟩)
      simpa [hagrees v hv] using hiv
    · exact hiR v hv hiv
  let g : U → survivors m ((P \ E) ∪ R) s := fun p => ⟨f p, hmem p⟩
  have hinj : Function.Injective g := by
    intro p t heq
    have he : f p = f t := congrArg Subtype.val heq
    apply Subtype.ext
    by_contra hne
    have hd := privatePositions_disjoint m P r (hE (hU p.property))
      (hE (hU t.property)) hne
    have ht := (hf t).1
    rw [← he] at ht
    exact Finset.disjoint_left.mp hd (hf p).1 ht
  exact Finset.card_le_card_of_injective hinj

/-- Each erased prime whose private positions are not fully replaced costs a
separate new survivor. -/
theorem exchange_budget_inequality (m : ℕ) (P E R : Finset ℕ)
    (hE : E ⊆ P) (r s : ℕ → ℕ) (hdisj : Disjoint (P \ E) R)
    (hagrees : ∀ p ∈ P \ E, s p = r p)
    (hcover : survivors m P r = ∅) :
    budget m P r + R.card ≤
      budget m ((P \ E) ∪ R) s + (fullyReplaced m P E R r s).card := by
  classical
  let K := fullyReplaced m P E R r s
  have hK : K ⊆ E := Finset.filter_subset _ E
  have hc : (E \ K).card ≤ (survivors m ((P \ E) ∪ R) s).card := by
    apply private_witness_card_le m P E R (E \ K) hE Finset.sdiff_subset r s hagrees
    intro p hp
    obtain ⟨hpE, hpK⟩ := Finset.mem_sdiff.mp hp
    have hh : ¬∀ i ∈ privatePositions m P r p, ∃ q ∈ R, i ≡ s q [MOD q] := by
      intro hbad
      exact hpK (Finset.mem_filter.mpr ⟨hpE, hbad⟩)
    push_neg at hh
    exact hh
  have he := Finset.card_sdiff_add_card_eq_card hE
  have hk := Finset.card_sdiff_add_card_eq_card hK
  simp only [budget, hcover, Finset.card_empty, Nat.add_zero,
    Finset.card_union_of_disjoint hdisj]
  change P.card + R.card ≤ (P \ E).card + R.card +
    (survivors m ((P \ E) ∪ R) s).card + K.card
  omega

/-- A budget improvement using `r` new classes must completely replace private
positions of at least `r+1` erased classes. -/
theorem new_card_lt_fullyReplaced_of_improvement (m : ℕ) (P E R : Finset ℕ)
    (hE : E ⊆ P) (r s : ℕ → ℕ) (hdisj : Disjoint (P \ E) R)
    (hagrees : ∀ p ∈ P \ E, s p = r p)
    (hcover : survivors m P r = ∅)
    (hbetter : budget m ((P \ E) ∪ R) s < budget m P r) :
    R.card < (fullyReplaced m P E R r s).card := by
  have hh := exchange_budget_inequality m P E R hE r s hdisj hagrees hcover
  omega

/-- Under large-product separation, covering every private point of one old
prime with `r` new primes requires at most `r` private points in that class. -/
theorem private_card_le_new_card_of_fully_replaced (m : ℕ) (P R : Finset ℕ)
    (r s : ℕ → ℕ) (p : ℕ) (hp : p.Prime)
    (hR : ∀ q ∈ R, q.Prime ∧ p ≠ q ∧ m ≤ p * q)
    (hfull : ∀ i ∈ privatePositions m P r p, ∃ q ∈ R, i ≡ s q [MOD q]) :
    (privatePositions m P r p).card ≤ R.card := by
  classical
  choose f hf using fun i : privatePositions m P r p => hfull i.val i.property
  let g : privatePositions m P r p → R := fun i => ⟨f i, (hf i).1⟩
  have hinj : Function.Injective g := by
    intro i j heq
    have he : f i = f j := congrArg Subtype.val heq
    apply Subtype.ext
    have hq := hR (f i) (hf i).1
    have hc := private_new_prime_hit_card_le_one m P r p (f i) (s (f i))
      hp hq.1 hq.2.1 hq.2.2
    apply Finset.card_le_one.mp hc
    · exact Finset.mem_filter.mpr ⟨i.property, (hf i).2⟩
    · exact Finset.mem_filter.mpr ⟨j.property, by simpa [he] using (hf j).2⟩
  exact Finset.card_le_card_of_injective hinj

/-- In the large-product regime, an improving `r`-prime exchange needs at least
`r+1` erased primes with at most `r` private positions each. This is a necessary
condition only, not a claim that the condition yields an exchange. -/
theorem many_small_private_classes_of_improvement (m : ℕ) (P E R : Finset ℕ)
    (hE : E ⊆ P) (r s : ℕ → ℕ) (hdisj : Disjoint (P \ E) R)
    (hagrees : ∀ p ∈ P \ E, s p = r p)
    (hcover : survivors m P r = ∅)
    (hprime : ∀ p ∈ E, p.Prime)
    (hR : ∀ p ∈ E, ∀ q ∈ R, q.Prime ∧ p ≠ q ∧ m ≤ p * q)
    (hbetter : budget m ((P \ E) ∪ R) s < budget m P r) :
    R.card < (E.filter (fun p => (privatePositions m P r p).card ≤ R.card)).card := by
  classical
  have hc := new_card_lt_fullyReplaced_of_improvement m P E R hE r s
    hdisj hagrees hcover hbetter
  apply hc.trans_le
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpE, hpfull⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hpE,
    private_card_le_new_card_of_fully_replaced m P R r s p (hprime p hpE)
      (hR p hpE) hpfull⟩

#print axioms exchange_budget_inequality
#print axioms many_small_private_classes_of_improvement
end Erdos970.OptimalCoverCore
