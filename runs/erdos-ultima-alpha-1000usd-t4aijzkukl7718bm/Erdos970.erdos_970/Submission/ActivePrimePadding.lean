import Submission.QuadraticScaleConcentration
import Submission.IntervalRescaling

/-! Greedy insertion of genuinely active prime classes, preserving designated
positions and two private witnesses for each old class. -/
namespace Erdos970.ActivePrimePadding
open Finset OptimalCoverCore

lemma residue_card_le (m q a : ℕ) (hq : 0 < q) :
    ((range m).filter (fun x => x ≡ a [MOD q])).card ≤ m / q + 1 := by
  have hh := (BlockSieve.SievePolynomial.residue_count_bounds m q a hq).2
  exact hh.trans (by unfold BlockSieve.SievePolynomial.ceilQuotient; split_ifs <;> omega)

/-- A class containing two candidates can be chosen to avoid every protected
position, provided the elementary counting budget is positive. -/
theorem exists_safe_pair (m q d : ℕ) (hq : 0 < q) (S Z : Finset ℕ)
    (hS : S ⊆ range m)
    (hd : ∀ a, ((range m).filter (fun x => x ≡ a [MOD q])).card ≤ d)
    (hroom : q + Z.card * d < S.card) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ x ≡ y [MOD q] ∧
      ∀ z ∈ Z, ¬z ≡ x [MOD q] := by
  classical
  let bad := Z.biUnion (fun z => (range m).filter (fun x => x ≡ z [MOD q]))
  have hb : bad.card ≤ Z.card * d := by
    apply card_biUnion_le.trans
    exact (sum_le_sum (fun z _ => hd z)).trans_eq (by simp)
  have hgood : q < (S \ bad).card := by
    have hh := card_sdiff_add_card S bad
    have hs := card_le_card (subset_union_left (s₂ := bad) : S ⊆ S ∪ bad)
    omega
  obtain ⟨x, hx, y, hy, hxy, hmod⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to
      (t := range q) (s := S \ bad) (by simpa using hgood)
      (f := fun i => i % q) (fun i _ => mem_range.mpr (Nat.mod_lt i hq))
  refine ⟨x, (mem_sdiff.mp hx).1, y, (mem_sdiff.mp hy).1, hxy, hmod, ?_⟩
  intro z hz hzmod
  apply (mem_sdiff.mp hx).2
  exact mem_biUnion.mpr ⟨z, hz, mem_filter.mpr ⟨hS (mem_sdiff.mp hx).1, hzmod.symm⟩⟩

lemma mem_private_iff (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ) (p x : ℕ) :
    x ∈ privatePositions m P r p ↔
      x < m ∧ x ≡ r p [MOD p] ∧ ∀ q ∈ P, q ≠ p → ¬x ≡ r q [MOD q] := by
  simp only [privatePositions, mem_filter, mem_survivors, mem_erase]
  aesop

def HasWitnesses (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ) (W : Finset ℕ) : Prop :=
  ∀ p ∈ P, ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
    x ∈ privatePositions m P r p ∧ y ∈ privatePositions m P r p

lemma HasWitnesses.two_private {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ} {W : Finset ℕ}
    (h : HasWitnesses m P r W) :
    ∀ p ∈ P, 2 ≤ (privatePositions m P r p).card := by
  intro p hp
  obtain ⟨x, _, y, _, hxy, hx, hy⟩ := h p hp
  exact (one_lt_card.mpr ⟨x, hx, y, hy, hxy⟩)

lemma private_preserved {m q a p x : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (hq : q ∉ P) (hp : p ∈ P) (hx : x ∈ privatePositions m P r p)
    (hsafe : ¬x ≡ a [MOD q]) :
    x ∈ privatePositions m (insert q P) (Function.update r q a) p := by
  rw [mem_private_iff] at hx ⊢
  have hpq : p ≠ q := by rintro rfl; exact hq hp
  refine ⟨hx.1, ?_, ?_⟩
  · simpa [Function.update_of_ne hpq] using hx.2.1
  · intro t ht htp
    rcases mem_insert.mp ht with heq | htP
    · subst t
      simpa using hsafe
    · have htq : t ≠ q := fun he => hq (he ▸ htP)
      simpa [Function.update_of_ne htq] using hx.2.2 t htP htp

lemma new_private {m q a x : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (hx : x ∈ survivors m P r) (hxa : x ≡ a [MOD q]) :
    x ∈ privatePositions m (insert q P) (Function.update r q a) q := by
  rw [mem_private_iff]
  obtain ⟨hxm, hxs⟩ := (mem_survivors _ _ _ _).mp hx
  refine ⟨hxm, by simpa using hxa, ?_⟩
  intro t ht htq
  have htP : t ∈ P := (mem_insert.mp ht).resolve_left htq
  simpa [Function.update_of_ne htq] using hxs t htP

lemma survivor_loss {m q a d : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (hq : q ∉ P)
    (hd : ((range m).filter (fun x => x ≡ a [MOD q])).card ≤ d) :
    (survivors m P r).card ≤
      (survivors m (insert q P) (Function.update r q a)).card + d := by
  rw [survivors_insert_update m P r q a hq]
  have hb : ((survivors m P r).filter (fun x => x ≡ a [MOD q])).card ≤ d := by
    apply (card_le_card ?_).trans hd
    intro x hx
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_survivors _ _ _ _).mp
      (mem_filter.mp hx).1).1, (mem_filter.mp hx).2⟩
  have hh := card_filter_add_card_filter_not (s := survivors m P r)
    (fun x => x ≡ a [MOD q])
  omega

/-- A supply of new moduli can be made active without disturbing protected
positions or the private witnesses of old classes. The loss budget is explicit.
Primality is unnecessary for this combinatorial insertion lemma. -/
theorem pad_active (m H d : ℕ) (R : Finset ℕ) :
    ∀ (P : Finset ℕ) (r : ℕ → ℕ) (W Z : Finset ℕ),
      Disjoint P R → HasWitnesses m P r W →
      (∀ q ∈ R, 0 < q ∧ q ≤ H ∧
        ∀ a, ((range m).filter (fun x => x ≡ a [MOD q])).card ≤ d) →
      H + (3 * R.card + W.card + Z.card) * d < (survivors m P r).card →
      ∃ s : ℕ → ℕ, (∀ p ∈ P, s p = r p) ∧
        (∀ q ∈ R, ∀ z ∈ Z, ¬z ≡ s q [MOD q]) ∧
        (∀ p ∈ P ∪ R, 2 ≤ (privatePositions m (P ∪ R) s p).card) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro P r W Z hdis hw hR hroom
    exact ⟨r, by simp, by simp, by simpa using hw.two_private⟩
  | @insert q R hqR ih =>
    intro P r W Z hdis hw hR hroom
    have hqP : q ∉ P := by
      intro hqP
      exact (disjoint_left.mp hdis) hqP (mem_insert_self _ _)
    have hq := hR q (mem_insert_self _ _)
    have hsub : survivors m P r ⊆ range m := by
      intro x hx; exact mem_range.mpr ((mem_survivors _ _ _ _).mp hx).1
    have hroom' : q + (W ∪ Z).card * d < (survivors m P r).card := by
      have hwz := Nat.mul_le_mul_right d (card_union_le W Z)
      rw [card_insert_of_notMem hqR] at hroom
      nlinarith
    obtain ⟨x, hx, y, hy, hxy, hmod, hsafe⟩ :=
      exists_safe_pair m q d hq.1 (survivors m P r) (W ∪ Z) hsub hq.2.2 hroom'
    let r' := Function.update r q x
    let W' := insert x (insert y W)
    have hW' : W'.card ≤ W.card + 2 := by
      have h1 := card_insert_le x (insert y W)
      have h2 := card_insert_le y W
      dsimp only [W']; omega
    have hw' : HasWitnesses m (insert q P) r' W' := by
      intro p hp
      rcases mem_insert.mp hp with rfl | hp
      · exact ⟨x, by simp [W'], y, by simp [W'], hxy,
          new_private hx (Nat.ModEq.refl x), new_private hy hmod.symm⟩
      · obtain ⟨u, hu, v, hv, huv, hup, hvp⟩ := hw p hp
        exact ⟨u, by simp [W', hu], v, by simp [W', hv], huv,
          private_preserved hqP hp hup (hsafe u (mem_union_left _ hu)),
          private_preserved hqP hp hvp (hsafe v (mem_union_left _ hv))⟩
    have hdis' : Disjoint (insert q P) R := by
      rw [disjoint_left]
      intro p hp hpR
      rcases mem_insert.mp hp with rfl | hp
      · exact hqR hpR
      · exact (disjoint_left.mp hdis) hp (mem_insert_of_mem hpR)
    have hroom'' : H + (3 * R.card + W'.card + Z.card) * d <
        (survivors m (insert q P) r').card := by
      have hloss := survivor_loss (r := r) hqP (hq.2.2 x)
      change (survivors m P r).card ≤ (survivors m (insert q P) r').card + d at hloss
      rw [card_insert_of_notMem hqR] at hroom
      nlinarith
    obtain ⟨s, hs, hz, hprivate⟩ := ih (insert q P) r' W' Z hdis' hw'
      (fun p hp => hR p (mem_insert_of_mem hp)) hroom''
    have he : insert q P ∪ R = P ∪ insert q R := by ext p; simp [or_left_comm]
    refine ⟨s, ?_, ?_, ?_⟩
    · intro p hp
      have hpq : p ≠ q := fun he => hqP (he ▸ hp)
      rw [hs p (mem_insert_of_mem hp)]
      simp [r', Function.update_of_ne hpq]
    · intro p hp z hzZ
      rcases mem_insert.mp hp with heq | hpR
      · subst p
        rw [hs q (mem_insert_self _ _)]
        simpa [r'] using hsafe z (mem_union_right _ hzZ)
      · exact hz p hpR z hzZ
    · simpa only [he] using hprivate

#print axioms exists_safe_pair
#print axioms pad_active
end Erdos970.ActivePrimePadding
