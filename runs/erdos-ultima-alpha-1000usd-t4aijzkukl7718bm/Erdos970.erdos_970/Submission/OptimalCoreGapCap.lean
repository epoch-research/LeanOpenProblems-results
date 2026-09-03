import Submission.ParitySeparation

/-! Gap-based bounds on the moduli in an optimal core. They refine the old
length cap, but are not a uniform quadratic bound on the optimal budget. -/
namespace Erdos970.OptimalCoverCore
open Finset IncrementReduction

/-- If an old sieve has gap bound g and all its survivors in an open interval
also survive the new sieve, that interval has length at most g*(s+1), where s
is the total number of new survivors. -/
lemma interval_length_le_gap_mul_survivor_card (P Q : Finset ℕ) (m g a L : ℕ)
    (r : ℕ → ℕ) (hQ : ∀ q ∈ Q, 0 < q) (hg : PrimeSetBound Q g)
    (ham : a + L ≤ m)
    (hkeep : ∀ x, a < x → x < a + L →
      (∀ q ∈ Q, ¬x ≡ r q [MOD q]) → ∀ p ∈ P, ¬x ≡ r p [MOD p]) :
    L ≤ g * ((survivors m P r).card + 1) := by
  classical
  by_contra hbad
  have hL : g * ((survivors m P r).card + 1) < L := by omega
  let S := survivors m P r
  obtain ⟨z, hz, _⟩ := hg (fun _ => 0)
  have hgpos : 0 < g := by omega
  have hex (j : Fin (S.card + 1)) : ∃ t < g,
      ∀ q ∈ Q, ¬(a + 1 + g * j.val + t) ≡ r q [MOD q] :=
    primeSetBound_translate hQ hg r (a + 1 + g * j.val)
  choose t ht hta using hex
  let f (j : Fin (S.card + 1)) := a + 1 + g * j.val + t j
  have hwin (j : Fin (S.card + 1)) : a < f j ∧ f j < a + L := by
    have hj := j.isLt
    have hh := Nat.mul_le_mul_left g (show j.val + 1 ≤ S.card + 1 by omega)
    have htj := ht j
    change g * (S.card + 1) < L at hL
    dsimp only [f]
    constructor <;> nlinarith
  have hmem (j : Fin (S.card + 1)) : f j ∈ S := by
    apply (mem_survivors m P r _).mpr
    exact ⟨by have := (hwin j).2; omega,
      hkeep _ (hwin j).1 (hwin j).2 (hta j)⟩
  let F : Fin (S.card + 1) → S := fun j => ⟨f j, hmem j⟩
  have hinj : Function.Injective F := by
    intro i j he
    have hef : f i = f j := congrArg Subtype.val he
    apply Fin.ext
    by_contra hij
    have hti := ht i
    have htj := ht j
    dsimp only [f] at hef
    rcases lt_or_gt_of_ne hij with hij | hij
    · have hh := Nat.mul_le_mul_left g (show i.val + 1 ≤ j.val by omega)
      nlinarith
    · have hh := Nat.mul_le_mul_left g (show j.val + 1 ≤ i.val by omega)
      nlinarith
  have hc := Fintype.card_le_of_injective F hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  omega

/-- Two private positions produce an open p-interval in which an old survivor
cannot be hit by p. This applies even when some final survivors remain. -/
theorem prime_le_gap_mul_survivor_card (P : Finset ℕ) (m p g : ℕ)
    (r : ℕ → ℕ) (hpos : ∀ q ∈ P.erase p, 0 < q)
    (hg : PrimeSetBound (P.erase p) g)
    (hprivate : 2 ≤ (privatePositions m P r p).card) :
    p ≤ g * ((survivors m P r).card + 1) := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
    (show 1 < (privatePositions m P r p).card by omega)
  wlog hijlt : i < j generalizing i j
  · exact this j hj i hi hij.symm (by omega)
  obtain ⟨hiS, hip⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjS, hjp⟩ := Finset.mem_filter.mp hj
  have hjm := ((mem_survivors m (P.erase p) r j).mp hjS).1
  have hd : p ∣ j - i := (Nat.modEq_iff_dvd' hijlt.le).mp (hip.trans hjp.symm)
  have hsep : p ≤ j - i := Nat.le_of_dvd (Nat.sub_pos_of_lt hijlt) hd
  apply interval_length_le_gap_mul_survivor_card P (P.erase p) m g i p r hpos hg (by omega)
  intro x hix hxp hxQ q hq hxq
  by_cases hqp : q = p
  · subst q
    have hdx : p ∣ x - i := (Nat.modEq_iff_dvd' hix.le).mp (hip.trans hxq.symm)
    have hh := Nat.le_of_dvd (Nat.sub_pos_of_lt hix) hdx
    omega
  · exact hxQ q (Finset.mem_erase.mpr ⟨hqp, hq⟩) hxq

/-- An optimal retained modulus is bounded using the old gap and the number
of final survivors, not just the full interval length. -/
theorem used_prime_le_gap_mul_survivor_card {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (p g : ℕ) (hp : p ∈ P)
    (hg : PrimeSetBound (P.erase p) g) :
    p ≤ g * ((survivors m P r).card + 1) :=
  prime_le_gap_mul_survivor_card P m p g r
    (fun q hq => (h.1 q (Finset.mem_of_mem_erase hq)).pos) hg
    (used_prime_private_card_ge_two h p hp)

/-- When parity is retained, same-class old survivors are at least 2p apart.
Consequently the gap-based cap improves by a factor of two. -/
theorem two_mul_prime_le_gap_mul_survivor_card (P : Finset ℕ) (m p g : ℕ)
    (r : ℕ → ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h2 : 2 ∈ P)
    (hpos : ∀ q ∈ P.erase p, 0 < q) (hg : PrimeSetBound (P.erase p) g)
    (hprivate : 2 ≤ (privatePositions m P r p).card) :
    2 * p ≤ g * ((survivors m P r).card + 1) := by
  classical
  have h2e : 2 ∈ P.erase p := Finset.mem_erase.mpr ⟨hp2.symm, h2⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
    (show 1 < (privatePositions m P r p).card by omega)
  wlog hijlt : i < j generalizing i j
  · exact this j hj i hi hij.symm (by omega)
  obtain ⟨hiS, hip⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjS, hjp⟩ := Finset.mem_filter.mp hj
  have hia := (mem_survivors m (P.erase p) r i).mp hiS
  have hja := (mem_survivors m (P.erase p) r j).mp hjS
  have hsep := two_mul_le_sub_of_modEq hp hp2 hijlt (hia.2 2 h2e) (hja.2 2 h2e)
    (hip.trans hjp.symm)
  apply interval_length_le_gap_mul_survivor_card P (P.erase p) m g i (2 * p) r hpos hg (by omega)
  intro x hix hxp hxQ q hq hxq
  by_cases hqp : q = p
  · subst q
    have hh := two_mul_le_sub_of_modEq hp hp2 hix (hia.2 2 h2e) (hxQ 2 h2e)
      (hip.trans hxq.symm)
    omega
  · exact hxQ q (Finset.mem_erase.mpr ⟨hqp, hq⟩) hxq

theorem two_mul_used_prime_le_gap_mul_survivor_card {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (h2 : 2 ∈ P) (p g : ℕ) (hp : p ∈ P) (hp2 : p ≠ 2)
    (hg : PrimeSetBound (P.erase p) g) :
    2 * p ≤ g * ((survivors m P r).card + 1) :=
  two_mul_prime_le_gap_mul_survivor_card P m p g r (h.1 p hp) hp2 h2
    (fun q hq => (h.1 q (Finset.mem_of_mem_erase hq)).pos) hg
    (used_prime_private_card_ge_two h p hp)

lemma primeSetBound_jacobsthal_card (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    PrimeSetBound P (jacobsthalFunction P.card) := by
  intro r
  by_contra hbad
  push_neg at hbad
  exact ((not_isJacobsthalBound_iff_cover P.card (jacobsthalFunction P.card)).mpr
    ⟨P, hP, le_rfl, r, hbad⟩) (isJacobsthalBound_jacobsthalFunction P.card)

/-- The smaller-cardinality Jacobsthal function supplies the old gap bound. -/
theorem used_prime_le_previous_jacobsthal {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (p : ℕ) (hp : p ∈ P) :
    p ≤ jacobsthalFunction (P.card - 1) * ((survivors m P r).card + 1) := by
  have hh := used_prime_le_gap_mul_survivor_card h p
    (jacobsthalFunction (P.erase p).card) hp
    (primeSetBound_jacobsthal_card _ (fun q hq => h.1 q (Finset.mem_of_mem_erase hq)))
  rwa [Finset.card_erase_of_mem hp] at hh

theorem used_prime_le_previous_jacobsthal_of_full_cover {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (hs : survivors m P r = ∅) (p : ℕ) (hp : p ∈ P) :
    p ≤ jacobsthalFunction (P.card - 1) := by
  simpa only [hs, Finset.card_empty, Nat.zero_add, Nat.mul_one] using
    used_prime_le_previous_jacobsthal h p hp

theorem two_mul_used_prime_le_previous_jacobsthal {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (h2 : 2 ∈ P) (p : ℕ) (hp : p ∈ P) (hp2 : p ≠ 2) :
    2 * p ≤ jacobsthalFunction (P.card - 1) * ((survivors m P r).card + 1) := by
  have hh := two_mul_used_prime_le_gap_mul_survivor_card h h2 p
    (jacobsthalFunction (P.erase p).card) hp hp2
    (primeSetBound_jacobsthal_card _ (fun q hq => h.1 q (Finset.mem_of_mem_erase hq)))
  rwa [Finset.card_erase_of_mem hp] at hh

theorem two_mul_used_prime_le_previous_jacobsthal_of_full_cover
    {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ} (h : IsOptimal m P r) (h2 : 2 ∈ P)
    (hs : survivors m P r = ∅) (p : ℕ) (hp : p ∈ P) (hp2 : p ≠ 2) :
    2 * p ≤ jacobsthalFunction (P.card - 1) := by
  simpa only [hs, Finset.card_empty, Nat.zero_add, Nat.mul_one] using
    two_mul_used_prime_le_previous_jacobsthal h h2 p hp hp2

#print axioms used_prime_le_gap_mul_survivor_card
#print axioms two_mul_used_prime_le_gap_mul_survivor_card
#print axioms used_prime_le_previous_jacobsthal
#print axioms used_prime_le_previous_jacobsthal_of_full_cover
#print axioms two_mul_used_prime_le_previous_jacobsthal_of_full_cover
end Erdos970.OptimalCoverCore
