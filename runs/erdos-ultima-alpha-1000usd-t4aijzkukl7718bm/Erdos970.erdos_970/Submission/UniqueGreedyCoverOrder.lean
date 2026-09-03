import Submission.EssentialCoverOrder
import Submission.SymmetricIsolation

/-! Essential covers can have exactly one residue-preserving greedy encoding,
even when interval length divided by the number of primes is arbitrarily
large. This does not address intervals longer than a fixed multiple of the
square of that number, and does not disprove the Jacobsthal conjecture. -/
namespace Erdos970.GreedyCoverOrder
open Finset Filter

/-- A full greedy encoding preserving the given residues. -/
def Encodes (U P : Finset ℕ) (r : ℕ → ℕ) (l : List ℕ) : Prop :=
  l.Nodup ∧ l.toFinset = P ∧ greedyResidual U l = ∅ ∧
    ∀ p ∈ P, r p ≡ greedyResidues U l p [MOD p]

/-- When each least nonnegative residue is itself a private point, every
residue-preserving greedy order must increase those residues. -/
theorem pairwise_residues_of_private_representatives (U : Finset ℕ)
    (r : ℕ → ℕ) (l : List ℕ) (hl : l.Nodup)
    (hnorm : ∀ p ∈ l, r p < p) (hmem : ∀ p ∈ l, r p ∈ U)
    (hprivate : ∀ p ∈ l, ∀ q ∈ l, q ≠ p → ¬r p ≡ r q [MOD q])
    (hres : ∀ p ∈ l, r p ≡ greedyResidues U l p [MOD p]) :
    l.Pairwise (fun p q => r p < r q) := by
  induction l generalizing U with
  | nil => simp
  | cons p l ih =>
    obtain ⟨hpl, hln⟩ := List.nodup_cons.mp hl
    have hpfirst : r p ≡ firstPosition U [MOD p] := by
      simpa only [greedyResidues, Function.update_self] using hres p (by simp)
    have hfirst : r p ≤ firstPosition U := by
      have he : r p = firstPosition U % p := by
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hnorm p (by simp))] using hpfirst
      rw [he]
      exact Nat.mod_le _ _
    have hqp (q : ℕ) (hq : q ∈ l) : q ≠ p := by
      rintro rfl
      exact hpl hq
    apply List.pairwise_cons.mpr
    constructor
    · intro q hq
      have hle := hfirst.trans (firstPosition_le (hmem q (by simp [hq])))
      have hne : r p ≠ r q := by
        intro he
        apply hprivate q (by simp [hq]) p (by simp) (hqp q hq).symm
        rw [he]
      omega
    · apply ih (greedyStep U p) hln
      · intro q hq
        exact hnorm q (by simp [hq])
      · intro q hq
        apply mem_filter.mpr
        refine ⟨hmem q (by simp [hq]), ?_⟩
        intro hh
        exact hprivate q (by simp [hq]) p (by simp) (hqp q hq).symm
          (hh.trans hpfirst.symm)
      · intro q hq v hv hvq
        exact hprivate q (by simp [hq]) v (by simp [hv]) hvq
      · intro q hq
        simpa only [greedyResidues, Function.update_of_ne (hqp q hq)] using
          hres q (by simp [hq])

/-- Private normalized representatives force uniqueness of the entire
residue-preserving greedy order, not just its first prime. -/
theorem encodings_unique_of_private_representatives (U P : Finset ℕ)
    (r : ℕ → ℕ) (hnorm : ∀ p ∈ P, r p < p) (hmem : ∀ p ∈ P, r p ∈ U)
    (hprivate : ∀ p ∈ P, ∀ q ∈ P, q ≠ p → ¬r p ≡ r q [MOD q])
    {l₁ l₂ : List ℕ} (h₁ : Encodes U P r l₁) (h₂ : Encodes U P r l₂) :
    l₁ = l₂ := by
  have hpw (l : List ℕ) (hl : Encodes U P r l) :
      l.Pairwise (fun p q => r p < r q) := by
    have hP (p : ℕ) (hp : p ∈ l) : p ∈ P := by
      rw [← hl.2.1]
      exact List.mem_toFinset.mpr hp
    exact pairwise_residues_of_private_representatives U r l hl.1
      (fun p hp => hnorm p (hP p hp)) (fun p hp => hmem p (hP p hp))
      (fun p hp q hq hqp => hprivate p (hP p hp) q (hP q hq) hqp)
      (fun p hp => hl.2.2.2 p (hP p hp))
  have hperm := List.perm_of_nodup_nodup_toFinset_eq h₁.1 h₂.1
    (h₁.2.1.trans h₂.2.1.symm)
  exact hperm.eq_of_pairwise (fun _ _ _ _ hxy hyx => (Nat.lt_asymm hxy hyx).elim)
    (hpw l₁ h₁) (hpw l₂ h₂)

/-- Shifted zero classes through m, and one fresh prime at zero. The shifted
prime itself is a private witness for each old class. -/
theorem exists_unique_order_cover (m : ℕ) (hm : 2 ≤ m) :
    ∃ P : Finset ℕ, ∃ r : ℕ → ℕ,
      (∀ p ∈ P, p.Prime) ∧ P.card = m.primeCounting + 1 ∧
      EssentialCover (range m) P r ∧ ∃! l : List ℕ, Encodes (range m) P r l := by
  classical
  let Q := (m + 1).primesBelow
  obtain ⟨q, hmq, hq⟩ := Nat.exists_infinite_primes (m + 1)
  have hqQ : q ∉ Q := by
    intro hh
    have := (Nat.mem_primesBelow.mp hh).1
    omega
  let P := insert q Q
  let r : ℕ → ℕ := fun p => if p = q then 0 else p - 1
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime ∧ p ≤ m := by
    have hh := Nat.mem_primesBelow.mp hp
    exact ⟨hh.2, by omega⟩
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := by
    rcases mem_insert.mp hp with rfl | hp
    · exact hq
    · exact (hQ p hp).1
  have hr (p : ℕ) (hp : p ∈ Q) : r p = p - 1 := by
    have hpq : p ≠ q := by rintro rfl; exact hqQ hp
    simp [r, hpq]
  have hnorm (p : ℕ) (hp : p ∈ P) : r p < p := by
    rcases mem_insert.mp hp with rfl | hp
    · simpa [r] using hq.pos
    · rw [hr p hp]
      have := (hQ p hp).1.pos
      omega
  have hmem (p : ℕ) (hp : p ∈ P) : r p ∈ range m := by
    apply mem_range.mpr
    rcases mem_insert.mp hp with rfl | hp
    · simp [r]; omega
    · rw [hr p hp]
      have hh := hQ p hp
      omega
  have hprivate (p : ℕ) (hp : p ∈ P) (v : ℕ) (hv : v ∈ P)
      (hvp : v ≠ p) : ¬r p ≡ r v [MOD v] := by
    intro hh
    rcases mem_insert.mp hp with hpq | hp
    · subst p
      have hvQ : v ∈ Q := (mem_insert.mp hv).resolve_left hvp
      have hv2 := (hQ v hvQ).1.two_le
      have he := hh.eq_of_lt_of_lt (by simpa [r] using (hQ v hvQ).1.pos) (hnorm v hv)
      rw [hr v hvQ] at he
      simp only [r, if_pos rfl] at he
      omega
    · have hpp := (hQ p hp).1
      rcases mem_insert.mp hv with hvq | hv
      · subst v
        have hlt : r p < q := by
          rw [hr p hp]
          have := (hQ p hp).2
          omega
        have he := hh.eq_of_lt_of_lt hlt (by simpa [r] using hq.pos)
        rw [hr p hp] at he
        simp only [r, if_pos rfl] at he
        have := hpp.two_le
        omega
      · rw [hr p hp, hr v hv] at hh
        have hvp' := (hQ v hv).1
        have hadd := hh.add_right 1
        have hpm1 : p - 1 + 1 = p := Nat.sub_add_cancel hpp.pos
        have hvm1 : v - 1 + 1 = v := Nat.sub_add_cancel hvp'.pos
        rw [hpm1, hvm1] at hadd
        have hzero : v ≡ 0 [MOD v] := Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)
        have hd : v ∣ p := Nat.modEq_zero_iff_dvd.mp (hadd.trans hzero)
        exact hvp ((hpp.dvd_iff_eq hvp'.ne_one).mp hd).symm
  have hcover : Covers (range m) P r := by
    intro i hi
    have him := mem_range.mp hi
    by_cases hi0 : i = 0
    · exact ⟨q, mem_insert_self _ _, by simp [hi0, r, Nat.ModEq]⟩
    · obtain ⟨p, hp, hpi⟩ := Nat.exists_prime_and_dvd (by omega : i + 1 ≠ 1)
      have hple := Nat.le_of_dvd (by omega : 0 < i + 1) hpi
      have hpQ : p ∈ Q := Nat.mem_primesBelow.mpr ⟨by omega, hp⟩
      refine ⟨p, mem_insert_of_mem hpQ, ?_⟩
      rw [hr p hpQ]
      apply Nat.ModEq.add_right_cancel' 1
      rw [Nat.sub_add_cancel hp.pos]
      exact (Nat.modEq_zero_iff_dvd.mpr hpi).trans
        (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)).symm
  have hessential : EssentialCover (range m) P r := by
    refine ⟨hcover, ?_⟩
    intro p hp
    exact ⟨r p, hmem p hp, Nat.ModEq.refl _, fun v hv hvp => hprivate p hp v hv hvp⟩
  refine ⟨P, r, hP, ?_, hessential, ?_⟩
  · have hc : Q.card = m.primeCounting := by
      simp only [Q, Nat.primesBelow, Nat.primeCounting, Nat.primeCounting',
        Nat.count_eq_card_filter_range]
    dsimp only [P]
    rw [card_insert_of_notMem hqQ, hc]
  · obtain ⟨l, hl, hlP, hrem, hres⟩ := exists_essential_order (range m) P r hessential
    refine ⟨l, ⟨hl, hlP, hrem, hres⟩, ?_⟩
    intro l' hl'
    exact encodings_unique_of_private_representatives (range m) P r hnorm hmem hprivate
      hl' ⟨hl, hlP, hrem, hres⟩

/-- Unique encodings persist for unbounded prime budgets and arbitrarily
large length/budget ratios. No quadratic-scale length is claimed. -/
theorem arbitrarily_long_unique_order_covers (A K : ℕ) :
    ∃ m : ℕ, ∃ P : Finset ℕ, ∃ r : ℕ → ℕ,
      (∀ p ∈ P, p.Prime) ∧ K ≤ P.card ∧ A * P.card < m ∧
      EssentialCover (range m) P r ∧ ∃! l : List ℕ, Encodes (range m) P r l := by
  obtain ⟨H, hbudget, hH⟩ := ((SymmetricIsolation.eventually_small_budget A).and
    (eventually_ge_atTop (Nat.nth Nat.Prime K + 1))).exists
  obtain ⟨P, r, hP, hcard, hcover, hunique⟩ := exists_unique_order_cover (H + 1) (by
    have := (Nat.prime_nth_prime K).pos
    omega)
  have hcount := Nat.monotone_primeCounting (show Nat.nth Nat.Prime K ≤ H + 1 by omega)
  rw [PrimeCountingLower.primeCounting_nth] at hcount
  refine ⟨H + 1, P, r, hP, ?_, ?_, hcover, hunique⟩
  · omega
  · rw [hcard]
    omega

/-- No fixed length-to-budget threshold guarantees even two encodings for
every essential cover, including after discarding finitely many budgets. -/
theorem no_linear_length_order_multiplicity :
    ¬∃ A K : ℕ, ∀ (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ),
      (∀ p ∈ P, p.Prime) → K ≤ P.card → A * P.card < m →
      EssentialCover (range m) P r →
      ∃ l₁ l₂ : List ℕ, Encodes (range m) P r l₁ ∧
        Encodes (range m) P r l₂ ∧ l₁ ≠ l₂ := by
  rintro ⟨A, K, hh⟩
  obtain ⟨m, P, r, hP, hK, hA, hcover, l, hl, hunique⟩ :=
    arbitrarily_long_unique_order_covers A K
  obtain ⟨l₁, l₂, h₁, h₂, hne⟩ := hh m P r hP hK hA hcover
  exact hne ((hunique l₁ h₁).trans (hunique l₂ h₂).symm)

#print axioms no_linear_length_order_multiplicity
#print axioms pairwise_residues_of_private_representatives
#print axioms encodings_unique_of_private_representatives
#print axioms exists_unique_order_cover
#print axioms arbitrarily_long_unique_order_covers
end Erdos970.GreedyCoverOrder
