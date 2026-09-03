import Submission.CompanionExchange

/-!
# Private-point transfer during a safe companion exchange

An unchanged class can lose all of its old private points and nevertheless
remain essential: old points covered by exactly it and the departing lower
class can become new private points. We record this transfer exactly.
-/

namespace Erdos7ExchangePrivateTransfer
open scoped BigOperators
open Erdos7CompanionExchange

section Abstract
variable {I X : Type*}

/-- Private relative to the unchanged classes alone. -/
def Within (F : I → X → Prop) (i : I) (x : X) : Prop :=
  F i x ∧ ∀ j, j ≠ i → ¬ F j x

/-- Private relative to the complete family, including the two distinguished
classes. -/
def Private (F : I → X → Prop) (L U : X → Prop) (i : I) (x : X) : Prop :=
  Within F i x ∧ ¬ L x ∧ ¬ U x

/-- Points covered by exactly the old lower class and unchanged class `i`. -/
def Double (F : I → X → Prop) (L U : X → Prop) (i : I) (x : X) : Prop :=
  Within F i x ∧ L x ∧ ¬ U x

lemma within_unique (F : I → X → Prop) (i j : I) (x : X)
    (hi : Within F i x) (hj : Within F j x) : i = j := by
  by_contra h
  exact hi.2 j (Ne.symm h) hj.1

/-- Exact private-point transfer. This is valid for partial families too;
coverage and minimality are not needed for the identity. -/
theorem private_transfer_iff (F : I → X → Prop) (L U A B : X → Prop)
    (hu : ∀ x, U x → A x) (hb : ∀ x, B x → L x)
    (hdis : ∀ x, L x → ¬ A x) (i : I) (x : X) :
    Private F A B i x ↔
      (Private F L U i x ∧ ¬ A x) ∨ (Double F L U i x ∧ ¬ B x) := by
  constructor
  · rintro ⟨hw, hA, hB⟩
    have hU : ¬ U x := fun h => hA (hu x h)
    by_cases hL : L x
    · exact Or.inr ⟨⟨hw, hL, hU⟩, hB⟩
    · exact Or.inl ⟨⟨hw, hL, hU⟩, hA⟩
  · rintro (⟨⟨hw, hL, hU⟩, hA⟩ | ⟨⟨hw, hL, hU⟩, hB⟩)
    · exact ⟨hw, hA, fun h => hL (hb x h)⟩
    · exact ⟨hw, hdis x hL, hB⟩

/-- When all old private points are swallowed by the enlarged lower class,
only old double-covered points can provide replacement private points. -/
theorem swallowed_private_iff (F : I → X → Prop) (L U A B : X → Prop)
    (hu : ∀ x, U x → A x) (hb : ∀ x, B x → L x)
    (hdis : ∀ x, L x → ¬ A x) (i : I)
    (hswallow : ∀ x, Private F L U i x → A x) (x : X) :
    Private F A B i x ↔ Double F L U i x ∧ ¬ B x := by
  rw [private_transfer_iff F L U A B hu hb hdis]
  constructor
  · rintro (⟨hp, hn⟩ | h)
    · exact False.elim (hn (hswallow x hp))
    · exact h
  · exact Or.inr

/-- A swallowed class remains essential precisely when a suitable old double
point exists. Minimality must therefore control double points as well as
original private points. -/
theorem swallowed_essential_iff (F : I → X → Prop) (L U A B : X → Prop)
    (hu : ∀ x, U x → A x) (hb : ∀ x, B x → L x)
    (hdis : ∀ x, L x → ¬ A x) (i : I)
    (hswallow : ∀ x, Private F L U i x → A x) :
    (∃ x, Private F A B i x) ↔ (∃ x, Double F L U i x ∧ ¬ B x) := by
  exact exists_congr (swallowed_private_iff F L U A B hu hb hdis i hswallow)

/-- Distinct swallowed classes need distinct replacement private points, all
in the portion of the old lower class vacated by the new upper class. -/
theorem swallowed_card_bound [Fintype X] [DecidableEq I]
    (F : I → X → Prop) (L U A B : X → Prop)
    (hu : ∀ x, U x → A x) (hb : ∀ x, B x → L x)
    (hdis : ∀ x, L x → ¬ A x) (J : Finset I)
    (hswallow : ∀ i ∈ J, ∀ x, Private F L U i x → A x)
    (hessential : ∀ i ∈ J, ∃ x, Private F A B i x) :
    letI : DecidablePred L := Classical.decPred L
    letI : DecidablePred B := Classical.decPred B
    J.card ≤ (Finset.univ.filter (fun x => L x ∧ ¬ B x)).card := by
  classical
  have hx (i : {i // i ∈ J}) : ∃ x, Double F L U i.val x ∧ ¬ B x :=
    (swallowed_essential_iff F L U A B hu hb hdis i.val
      (hswallow i.val i.property)).mp (hessential i.val i.property)
  let R : Finset X := Finset.univ.filter (fun x => L x ∧ ¬ B x)
  let f : {i // i ∈ J} → {x // x ∈ R} := fun i =>
    ⟨Classical.choose (hx i), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Classical.choose_spec (hx i)).1.2.1,
        (Classical.choose_spec (hx i)).2⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    have he : Classical.choose (hx i) = Classical.choose (hx j) :=
      congrArg Subtype.val hij
    exact within_unique F i.val j.val _ (Classical.choose_spec (hx i)).1.1
      (he.symm ▸ (Classical.choose_spec (hx j)).1.1)
  simpa only [Fintype.card_coe, R] using Fintype.card_le_of_injective f hf

/-- A point private to one of the distinguished classes. -/
def SidePrivate (F : I → X → Prop) (R S : X → Prop) (x : X) : Prop :=
  R x ∧ ¬ S x ∧ ∀ i, ¬ F i x

/-- Under full coverage and a safe exchange, the private sets of the two
exchanged labels are exactly interchanged. Other labels obey the separate
transfer formula, and need not retain the same private sets. -/
theorem distinguished_private_swap (F : I → X → Prop) (L U A B : X → Prop)
    (hu : ∀ x, U x → A x) (hb : ∀ x, B x → L x)
    (hdis : ∀ x, L x → ¬ A x)
    (hcover : ∀ x, (∃ i, F i x) ∨ L x ∨ U x)
    (hsafe : ∀ x, SidePrivate F L U x → B x) (x : X) :
    (SidePrivate F A B x ↔ SidePrivate F U L x) ∧
    (SidePrivate F B A x ↔ SidePrivate F L U x) := by
  constructor
  · constructor
    · rintro ⟨hA, hB, hF⟩
      have hL : ¬ L x := fun h => hdis x h hA
      have hU : U x := by
        rcases hcover x with ⟨i, hi⟩ | h | h
        · exact False.elim (hF i hi)
        · exact False.elim (hL h)
        · exact h
      exact ⟨hU, hL, hF⟩
    · rintro ⟨hU, hL, hF⟩
      exact ⟨hu x hU, fun h => hL (hb x h), hF⟩
  · constructor
    · rintro ⟨hB, hA, hF⟩
      exact ⟨hb x hB, fun h => hA (hu x h), hF⟩
    · intro hx
      exact ⟨hsafe x hx, hdis x hx.1, hx.2.2⟩

end Abstract

section Minimality

/-- No residue assignment to these fixed modulus labels covers after any one
label is deleted. This follows from global minimum cardinality, but is a weaker
condition, permitting a small finite control. -/
def LabelMinimal {I : Type*} (m : I → ℕ) : Prop :=
  ∀ (a : I → ℤ) (j : I), ∃ x : ℤ, ∀ k, k ≠ j → ¬ Hit (m k) (a k) x

/-- Under label minimality every covering residue assignment is irredundant.
This applies to a new assignment after a coverage-preserving exchange. -/
theorem private_of_label_minimal {I : Type*} (m : I → ℕ) (hm : LabelMinimal m)
    (a : I → ℤ) (hc : ∀ x : ℤ, ∃ i, Hit (m i) (a i) x) (j : I) :
    ∃ x : ℤ, Hit (m j) (a j) x ∧ ∀ k, k ≠ j → ¬ Hit (m k) (a k) x := by
  obtain ⟨x, hx⟩ := hm a j
  obtain ⟨i, hi⟩ := hc x
  have hij : i=j := by
    by_contra h
    exact hx i h hi
  subst i
  exact ⟨x, hi, hx⟩

/-- An odd lower modulus prevents an incompatible companion exchange from
being a common translation of the old two classes. -/
theorem odd_exchange_not_translation (d : ℕ) (hd : Odd d) (p a b t : ℤ)
    (hne : ¬ (d : ℤ) ∣ a-b) :
    ¬ ∃ c : ℤ, (d : ℤ) ∣ b+c-a ∧ p*(d : ℤ) ∣ a+c-(b+t*(d : ℤ)) := by
  rintro ⟨c, hcL, hcU⟩
  have hcU' : (d : ℤ) ∣ a+c-(b+t*(d : ℤ)) :=
    (dvd_mul_left (d : ℤ) p).trans hcU
  have ht : (d : ℤ) ∣ t*(d : ℤ) := dvd_mul_left (d : ℤ) t
  have htwo : (d : ℤ) ∣ 2*(a-b) := by
    convert dvd_sub (dvd_add hcU' ht) hcL using 1; ring
  have hcop : IsCoprime (d : ℤ) (2 : ℤ) :=
    (Nat.coprime_two_right.mpr hd).isCoprime
  exact hne (hcop.dvd_of_dvd_mul_left htwo)

end Minimality

section Control

abbrev m := Erdos7CompanionExchange.moduli
abbrev oldA := Erdos7CompanionExchange.residues

/-- Exchange 1 mod 4 and 11 mod 12 for 3 mod 4 and 5 mod 12. -/
def newA : Fin 5 → ℤ := ![0,0,3,1,5]
def newWitness : Fin 5 → ℤ := ![2,9,11,1,5]

lemma new_data : ∀ i j, Hit (m j) (newA j) (newWitness i) ↔ i=j := by
  unfold Hit
  decide +kernel

lemma new_finite_cover : ∀ r : Fin 12, ∃ i, Hit (m i) (newA i) r.val := by
  decide +kernel

theorem new_cover : ∀ x : ℤ, ∃ i, Hit (m i) (newA i) x := by
  intro x
  let r : Fin 12 := ⟨(x%12).toNat, by omega⟩
  obtain ⟨i, hi⟩ := new_finite_cover r
  have hr : (r.val : ℤ) = x%12 := by
    dsimp [r]
    exact Int.toNat_of_nonneg (by omega)
  rw [hr] at hi
  have hm : (m i : ℤ) ∣ 12 := by exact_mod_cast (control_data.2.1 i).2
  have h12 : (12 : ℤ) ∣ x-x%12 := Int.dvd_self_sub_emod
  have h := dvd_add (hm.trans h12) hi
  refine ⟨i, ?_⟩
  simpa only [Hit, sub_add_sub_cancel] using h

/-- All assignments with one of the five fixed modulus labels deleted fail.
This table quantifies over residues modulo their individual moduli. -/
lemma finite_label_minimal : ∀ a : (i : Fin 5) → Fin (m i), ∀ j : Fin 5,
    ∃ r : Fin 12, ∀ k : Fin 5, k ≠ j → ¬ Hit (m k) (a k).val r.val := by
  decide +kernel

/-- The finite table lifts to arbitrary integer residues. -/
theorem control_label_minimal : LabelMinimal m := by
  intro a j
  let b (i : Fin 5) : Fin (m i) :=
    ⟨(a i % (m i : ℤ)).toNat, by
      have hm : 1 < m i := (control_data.2.1 i).1
      have hp : 0 < (m i : ℤ) := by exact_mod_cast (show 0 < m i by omega)
      have hlo := Int.emod_nonneg (a i) (ne_of_gt hp)
      have hhi := Int.emod_lt_of_pos (a i) hp
      omega⟩
  obtain ⟨r, hr⟩ := finite_label_minimal b j
  refine ⟨r.val, fun k hkj hk => hr k hkj ?_⟩
  have hb : ((b k).val : ℤ) = a k % (m k : ℤ) := by
    dsimp [b]
    have hm : 1 < m k := (control_data.2.1 k).1
    have hp : 0 < (m k : ℤ) := by exact_mod_cast (show 0 < m k by omega)
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hp))
  rw [hb]
  have hd : (m k : ℤ) ∣ a k-a k % (m k : ℤ) := Int.dvd_self_sub_emod
  have h := dvd_add hk hd
  simpa only [Hit, sub_add_sub_cancel] using h

/-- This particular even control is in fact a common translation by six.
The odd-modulus obstruction above explains why that feature does not transfer
to an odd companion exchange. -/
lemma control_is_translation : ∀ i : Fin 5,
    (m i : ℤ) ∣ newA i-oldA i-6 := by
  decide +kernel

/-- The three unchanged classes are modulo 2, 3, and 6. -/
def others (j : Fin 3) (x : ℤ) : Prop :=
  Hit (![2,3,6] j : ℤ) (![0,0,1] j : ℤ) x

abbrev L := Hit 4 1
abbrev U := Hit 12 11
abbrev A := Hit 4 3
abbrev B := Hit 12 5

lemma exchange_geometry : (∀ x, U x → A x) ∧ (∀ x, B x → L x) ∧
    (∀ x, L x → ¬ A x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hd : (4 : ℤ) ∣ 12 := by norm_num
    have hh := dvd_add (hd.trans hx) (show (4 : ℤ) ∣ 8 by norm_num)
    change (4 : ℤ) ∣ x-3
    convert hh using 1; ring
  · intro x hx
    have hd : (4 : ℤ) ∣ 12 := by norm_num
    have hh := dvd_add (hd.trans hx) (show (4 : ℤ) ∣ 4 by norm_num)
    change (4 : ℤ) ∣ x-1
    convert hh using 1; ring
  · exact incompatible_coarse 4 3 1 (by norm_num)

/-- Old private points of both unchanged classes 3 and 6 are all swallowed by
the new lower class. The assertion is for all integers, not only witnesses. -/
lemma swallowed_three (x : ℤ) (hx : Private others L U 1 x) : A x := by
  have h3 := hx.1.1
  have h2 := hx.1.2 0 (by decide)
  have h4 := hx.2.1
  change (3 : ℤ) ∣ x-0 at h3
  change ¬ (2 : ℤ) ∣ x-0 at h2
  change ¬ (4 : ℤ) ∣ x-1 at h4
  change (4 : ℤ) ∣ x-3
  omega

lemma swallowed_six (x : ℤ) (hx : Private others L U 2 x) : A x := by
  have h6 := hx.1.1
  have h4 := hx.2.1
  change (6 : ℤ) ∣ x-1 at h6
  change ¬ (4 : ℤ) ∣ x-1 at h4
  change (4 : ℤ) ∣ x-3
  omega

lemma new_private_and_old_double :
    (Private others A B 1 9 ∧ Double others L U 1 9) ∧
    (Private others A B 2 1 ∧ Double others L U 2 1) := by
  unfold Private Double Within others L U A B Hit
  decide +kernel

/-- The capacity in the transfer bound is exactly two in this control,
equal to the number of swallowed unchanged classes. -/
lemma transfer_capacity_sharp : ({1,2} : Finset (Fin 3)).card = 2 ∧
    (Finset.univ.filter (fun x : Fin 12 => L x.val ∧ ¬ B x.val)).card = 2 := by
  unfold L B
  decide +kernel

end Control

#print axioms private_transfer_iff
#print axioms swallowed_essential_iff
#print axioms swallowed_card_bound
#print axioms distinguished_private_swap
#print axioms private_of_label_minimal
#print axioms odd_exchange_not_translation
#print axioms new_cover
#print axioms control_label_minimal
#print axioms swallowed_three
#print axioms swallowed_six
#print axioms new_private_and_old_double
#print axioms control_is_translation
#print axioms transfer_capacity_sharp

end Erdos7ExchangePrivateTransfer
