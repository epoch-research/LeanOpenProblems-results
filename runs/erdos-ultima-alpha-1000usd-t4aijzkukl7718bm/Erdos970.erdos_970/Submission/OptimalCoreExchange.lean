import Submission.OptimalCoverCore

/-! Exact exchange inequalities for an optimal prime-class cover core.
No growth estimate for the optimal budget is asserted here. -/
namespace Erdos970.OptimalCoverCore

/-- Secondary minimization makes every smaller retained core strictly more costly. -/
theorem budget_lt_of_smaller_core {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (s : ℕ → ℕ) (hcard : Q.card < P.card) :
    budget m P r < budget m Q s := by
  have hle := h.2.1 Q hQ s
  by_contra hbad
  have heq : budget m Q s = budget m P r := by omega
  have hh := h.2.2 Q hQ s heq
  omega

/-- Replacing a block of residues leaves exactly the old unhit positions not
hit by any replacement residue, provided the retained residues agree. -/
theorem survivors_replacement (m : ℕ) (A R : Finset ℕ) (r s : ℕ → ℕ)
    (hagrees : ∀ p ∈ A, s p = r p) :
    survivors m (A ∪ R) s =
      (survivors m A r).filter (fun i => ¬∃ p ∈ R, i ≡ s p [MOD p]) := by
  classical
  ext i
  simp only [mem_survivors, Finset.mem_filter, Finset.forall_mem_union,
    not_exists, not_and]
  constructor
  · rintro ⟨him, hiA, hiR⟩
    exact ⟨⟨him, fun p hp => by simpa [hagrees p hp] using hiA p hp⟩, hiR⟩
  · rintro ⟨⟨him, hiA⟩, hiR⟩
    exact ⟨him, (fun p hp => by simpa [hagrees p hp] using hiA p hp), hiR⟩

/-- Erasing `E` and inserting disjoint `R` cannot hit too many of the newly
available positions. This includes the original survivors in the count. -/
theorem replacement_hit_card_le {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (E R : Finset ℕ) (hE : E ⊆ P)
    (hR : ∀ p ∈ R, p.Prime) (hdisj : Disjoint (P \ E) R)
    (s : ℕ → ℕ) (hagrees : ∀ p ∈ P \ E, s p = r p) :
    (survivors m P r).card + E.card +
      ((survivors m (P \ E) r).filter
        (fun i => ∃ p ∈ R, i ≡ s p [MOD p])).card ≤
      (survivors m (P \ E) r).card + R.card := by
  classical
  have hpr : ∀ p ∈ (P \ E) ∪ R, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact h.1 p (Finset.mem_sdiff.mp hp).1
    · exact hR p hp
  have hb := h.2.1 ((P \ E) ∪ R) hpr s
  have he := Finset.card_sdiff_add_card_eq_card hE
  have hc := Finset.card_filter_add_card_filter_not
    (s := survivors m (P \ E) r) (fun i => ∃ p ∈ R, i ≡ s p [MOD p])
  rw [budget, budget, Finset.card_union_of_disjoint hdisj,
    survivors_replacement m (P \ E) R r s hagrees] at hb
  omega

/-- The exchange bound is strict if the replacement uses fewer retained primes.
This uses secondary minimization, not merely minimality of the total budget. -/
theorem replacement_hit_card_lt {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (E R : Finset ℕ) (hE : E ⊆ P)
    (hR : ∀ p ∈ R, p.Prime) (hdisj : Disjoint (P \ E) R)
    (s : ℕ → ℕ) (hagrees : ∀ p ∈ P \ E, s p = r p)
    (hfewer : R.card < E.card) :
    (survivors m P r).card + E.card +
      ((survivors m (P \ E) r).filter
        (fun i => ∃ p ∈ R, i ≡ s p [MOD p])).card <
      (survivors m (P \ E) r).card + R.card := by
  classical
  have hpr : ∀ p ∈ (P \ E) ∪ R, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact h.1 p (Finset.mem_sdiff.mp hp).1
    · exact hR p hp
  have he := Finset.card_sdiff_add_card_eq_card hE
  have hcard : ((P \ E) ∪ R).card < P.card := by
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  have hb := budget_lt_of_smaller_core h ((P \ E) ∪ R) hpr s hcard
  have hc := Finset.card_filter_add_card_filter_not
    (s := survivors m (P \ E) r) (fun i => ∃ p ∈ R, i ≡ s p [MOD p])
  rw [budget, budget, Finset.card_union_of_disjoint hdisj,
    survivors_replacement m (P \ E) R r s hagrees] at hb
  omega

#print axioms replacement_hit_card_le
#print axioms replacement_hit_card_lt
end Erdos970.OptimalCoverCore
