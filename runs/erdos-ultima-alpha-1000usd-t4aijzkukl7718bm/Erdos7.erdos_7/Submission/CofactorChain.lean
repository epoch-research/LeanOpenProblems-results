import Submission.ArithmeticReduction

/-! Residue separation along a cofactor chain. This is a necessary condition,
not a solution of the odd covering problem. -/
namespace Erdos7CofactorChain
open Erdos7Reduction
set_option maxHeartbeats 1000000

/-- At a common cofactor point, comparable disjoint classes must use different
residues in the complementary coordinate. -/
theorem residue_injective {κ : Type*} (q : ℕ) (n : κ → ℕ) (a : κ → ℤ)
    (hcop : ∀ i, Nat.Coprime q (n i))
    (hchain : ∀ i j, n i ∣ n j ∨ n j ∣ n i)
    (hsep : ∀ i j, i ≠ j → n i ∣ n j → ¬ ((q * n i : ℕ) : ℤ) ∣ a j - a i)
    (x : ℤ) (hx : ∀ i, (n i : ℤ) ∣ x - a i) :
    Function.Injective (fun i => (a i : ZMod q)) := by
  have helper (i j : κ) (hij : i ≠ j) (hd : n i ∣ n j)
      (heq : (a i : ZMod q) = (a j : ZMod q)) : False := by
    have hq : (q : ℤ) ∣ a j - a i :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a i) (a j) q).mp heq
    have hdz : (n i : ℤ) ∣ (n j : ℤ) := by exact_mod_cast hd
    have hn : (n i : ℤ) ∣ a j - a i := by
      have hh := dvd_sub (hx i) (hdz.trans (hx j))
      convert hh using 1
      ring
    have hprod := (hcop i).isCoprime.mul_dvd hq hn
    apply hsep i j hij hd
    simpa only [Nat.cast_mul] using hprod
  intro i j heq
  by_contra hij
  rcases hchain i j with hd | hd
  · exact helper i j hij hd heq
  · exact helper j i (Ne.symm hij) hd heq.symm

/-- A chain of active cofactors contains at most as many classes as there are
residues in the complementary coordinate. -/
theorem card_le {κ : Type*} [Fintype κ] (q : ℕ) (hq : 0 < q)
    (n : κ → ℕ) (a : κ → ℤ)
    (hcop : ∀ i, Nat.Coprime q (n i))
    (hchain : ∀ i j, n i ∣ n j ∨ n j ∣ n i)
    (hsep : ∀ i j, i ≠ j → n i ∣ n j → ¬ ((q * n i : ℕ) : ℤ) ∣ a j - a i)
    (x : ℤ) (hx : ∀ i, (n i : ℤ) ∣ x - a i) :
    Fintype.card κ ≤ q := by
  letI : NeZero q := ⟨by omega⟩
  have hh := Fintype.card_le_of_injective (fun i => (a i : ZMod q))
    (residue_injective q n a hcop hchain hsep x hx)
  simpa only [ZMod.card] using hh

/-- The same injection counts only the complementary residues still available.
This permits previously excluded pure-power residue classes to be charged. -/
theorem card_le_available {κ : Type*} [Fintype κ] (q : ℕ) (hq : 0 < q)
    (n : κ → ℕ) (a : κ → ℤ)
    (hcop : ∀ i, Nat.Coprime q (n i))
    (hchain : ∀ i j, n i ∣ n j ∨ n j ∣ n i)
    (hsep : ∀ i j, i ≠ j → n i ∣ n j → ¬ ((q * n i : ℕ) : ℤ) ∣ a j - a i)
    (x : ℤ) (hx : ∀ i, (n i : ℤ) ∣ x - a i)
    (F : Finset (ZMod q)) (havoid : ∀ i, (a i : ZMod q) ∉ F) :
    Fintype.card κ ≤ q - F.card := by
  classical
  letI : NeZero q := ⟨by omega⟩
  have hinj := residue_injective q n a hcop hchain hsep x hx
  have hsub : (Finset.univ.image (fun i => (a i : ZMod q))) ⊆ Finset.univ \ F := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, havoid i⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj,
    Finset.card_sdiff_of_subset (Finset.subset_univ F)] at hh
  simpa only [Finset.card_univ, ZMod.card] using hh

/-- Application to a selected family inside an arbitrary irredundant arithmetic
cover. No oddness assumption is needed. -/
theorem irredundant_cover_chain_bound {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x - a j)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (s : Finset ι) (q : ℕ) (hq : 0 < q) (n : ι → ℕ)
    (hfac : ∀ i ∈ s, m i = q * n i)
    (hcop : ∀ i ∈ s, Nat.Coprime q (n i))
    (hchain : ∀ i ∈ s, ∀ j ∈ s, n i ∣ n j ∨ n j ∣ n i)
    (x : ℤ) (hx : ∀ i ∈ s, (n i : ℤ) ∣ x - a i) :
    s.card ≤ q := by
  classical
  have hh := card_le q hq (fun i : s => n i.val) (fun i : s => a i.val)
    (fun i => hcop i.val i.property)
    (fun i j => hchain i.val i.property j.val j.property) (by
      intro i j hij hd
      have hij' : i.val ≠ j.val := fun heq => hij (Subtype.ext heq)
      have hmd : m i.val ∣ m j.val := by
        rw [hfac i.val i.property, hfac j.val j.property]
        exact Nat.mul_dvd_mul_left q hd
      have h := residue_not_congruent_of_proper_modulus_divisor m a hpriv hc hij' hmd
      simpa only [hfac i.val i.property] using h)
    x (fun i => hx i.val i.property)
  simpa only [Fintype.card_coe] using hh

#print axioms residue_injective
#print axioms card_le
#print axioms card_le_available
#print axioms irredundant_cover_chain_bound
end Erdos7CofactorChain
