import Submission.ParabolaSquareLift

/-!
A height/cardinality ceiling for the canonical square roots in the specific
carry-aware parabola lift. It is not an upper bound for arbitrary Sidon
subsets of squares, and does not disprove the original conjecture.
-/
namespace Erdos773.ParabolaSmallRepresentatives
open Finset ParabolaSquareLift
set_option maxHeartbeats 1000000

lemma quotient_lt_label {p b : ℕ} (hp : 0 < p) (hb : 0 < b) (hbp : b < p) :
    b^2/p < b := by
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  have h := Nat.mul_lt_mul_of_pos_left hbp hb
  nlinarith only [h]

lemma highDigit_pos (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    {b : ℕ} (hb : 0 < b) (hbp : b < p) : 0 < highDigit p b := by
  have hp := (Fact.out : p.Prime).pos
  have hq := quotient_lt_label hp hb hbp
  have hc := highDigit_congruence p b h2 hb hbp
  by_contra hn
  have hz : highDigit p b=0 := by omega
  rw [hz] at hc
  simp only [mul_zero,add_zero,Nat.ModEq,Nat.mod_eq_of_lt hbp,
    Nat.mod_eq_of_lt (hq.trans hbp)] at hc
  omega

/-- A strictly increasing integer function whose value is divisible by p
on the labels with high digit a. -/
def levelValue (p a b : ℕ) : ℕ := b^2/p+(2*a-1)*b

lemma levelValue_strictMono (p : ℕ) {a : ℕ} (ha : 0 < a) :
    StrictMono (levelValue p a) := by
  intro b c hbc
  apply Nat.add_lt_add_of_le_of_lt
  · exact Nat.div_le_div_right (Nat.pow_le_pow_left hbc.le 2)
  · exact Nat.mul_lt_mul_of_pos_left hbc (by omega)

lemma levelValue_add {p a b : ℕ} (ha : 0 < a) :
    levelValue p a b+b=b^2/p+2*b*a := by
  have he : (2*a-1)+1=2*a := by omega
  have hm := congrArg (fun n : ℕ => n*b) he
  dsimp [levelValue]
  nlinarith only [hm]

lemma levelValue_dvd (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    {a b : ℕ} (hb : 0 < b) (hbp : b < p) (ha : highDigit p b=a) :
    p ∣ levelValue p a b := by
  have ha₀ : 0 < a := ha ▸ highDigit_pos p h2 hb hbp
  have hc := highDigit_congruence p b h2 hb hbp
  rw [ha,← levelValue_add ha₀] at hc
  have hm : levelValue p a b ≡ 0 [MOD p] := by
    apply Nat.ModEq.add_right_cancel' b
    simpa only [zero_add] using hc
  exact Nat.dvd_of_mod_eq_zero (by simpa only [Nat.ModEq,Nat.zero_mod] using hm)

lemma levelValue_lt {p a b : ℕ} (hp : 0 < p) (ha : 0 < a)
    (hb : 0 < b) (hbp : b < p) : levelValue p a b < 2*a*p := by
  have hq := quotient_lt_label hp hb hbp
  have he := levelValue_add (p:=p) (b:=b) ha
  have hsmall : levelValue p a b < 2*a*b := by nlinarith only [hq,he]
  exact hsmall.trans (Nat.mul_lt_mul_of_pos_left hbp (by omega))

noncomputable def level (p a : ℕ) [Fact p.Prime] : Finset ℕ :=
  (Icc 1 (p-1)).filter (fun b => highDigit p b=a)

/-- At most 2a-1 canonical nonzero labels have high digit a. In particular
there are no labels with high digit zero. -/
theorem level_card (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (a : ℕ) :
    (level p a).card ≤ 2*a-1 := by
  have hp := (Fact.out : p.Prime).pos
  have hmem {b : ℕ} (hb : b ∈ level p a) :
      0 < b ∧ b < p ∧ highDigit p b=a := by
    simp only [level,mem_filter,mem_Icc] at hb
    exact ⟨by omega,by omega,hb.2⟩
  by_cases ha : a=0
  · have he : level p a=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨hb₀,hbp,hba⟩ := hmem hb
      have hh := highDigit_pos p h2 hb₀ hbp
      omega
    simp [he]
  · have ha₀ : 0 < a := by omega
    have hh : (level p a).card ≤ (Icc 1 (2*a-1)).card := by
      apply card_le_card_of_injOn (fun b => levelValue p a b/p)
      · intro b hb
        obtain ⟨hb₀,hbp,hba⟩ := hmem hb
        have hdiv := levelValue_dvd p h2 hb₀ hbp hba
        have hpos : 0 < levelValue p a b := by
          have hh := Nat.mul_pos (show 0 < 2*a-1 by omega) hb₀
          exact hh.trans_le (Nat.le_add_left _ _)
        have hkpos := Nat.div_pos (Nat.le_of_dvd hpos hdiv) hp
        have hklt := (Nat.div_lt_iff_lt_mul hp).mpr (levelValue_lt hp ha₀ hb₀ hbp)
        exact mem_Icc.mpr ⟨hkpos,Nat.le_pred_of_lt hklt⟩
      · intro b hb c hc he
        dsimp only at he
        obtain ⟨hb₀,hbp,hba⟩ := hmem hb
        obtain ⟨hc₀,hcp,hca⟩ := hmem hc
        have hbdiv := levelValue_dvd p h2 hb₀ hbp hba
        have hcdiv := levelValue_dvd p h2 hc₀ hcp hca
        apply (levelValue_strictMono p ha₀).injective
        calc
          levelValue p a b = p*(levelValue p a b/p) :=
            (Nat.mul_div_cancel' hbdiv).symm
          _ = p*(levelValue p a c/p) := by rw [he]
          _ = levelValue p a c := Nat.mul_div_cancel' hcdiv
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hh

lemma sum_odd_range (H : ℕ) : (∑ a ∈ range (H+1), (2*a-1))=H^2 := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [show H+1+1=(H+1)+1 by omega,sum_range_succ,ih]
    rw [show 2*(H+1)-1=2*H+1 by omega]
    ring

/-- Truncating the lift at high digit H leaves at most H² labels. -/
theorem bounded_highDigit_card (p : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (B : Finset ℕ)
    (hB : ∀ b ∈ B, 0 < b ∧ b < p) (H : ℕ)
    (hH : ∀ b ∈ B, highDigit p b ≤ H) : B.card ≤ H^2 := by
  have hmap : ∀ b ∈ B, highDigit p b ∈ range (H+1) := by
    intro b hb
    exact mem_range.mpr (by have := hH b hb; omega)
  calc
    B.card = ∑ a ∈ range (H+1), (B.filter (fun b => highDigit p b=a)).card :=
      card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ a ∈ range (H+1), (2*a-1) := by
      apply sum_le_sum
      intro a ha
      apply (card_le_card (show B.filter (fun b => highDigit p b=a) ⊆ level p a from ?_)).trans
        (level_card p h2 a)
      intro b hb
      obtain ⟨hbB,hba⟩ := mem_filter.mp hb
      have hh := hB b hbB
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hba⟩
    _ = H^2 := sum_odd_range H

/-- Every subfamily of these canonical lifted roots at height N obeys a
two-thirds cardinality ceiling. No Sidon or half-band assumption is needed. -/
theorem height_card_ceiling (p : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (B : Finset ℕ)
    (hB : ∀ b ∈ B, 0 < b ∧ b < p) (N : ℕ)
    (hN : ∀ b ∈ B, root p b ≤ N) :
    ((B.image (root p)).card)^3 ≤ N^2 := by
  have hp := (Fact.out : p.Prime).pos
  let H := N/p
  have hH : ∀ b ∈ B, highDigit p b ≤ H := by
    intro b hb
    apply (Nat.le_div_iff_mul_le hp).mpr
    have hh := hN b hb
    dsimp [root] at hh
    nlinarith only [hh]
  have hsmall := bounded_highDigit_card p h2 B hB H hH
  have hlabels : B.card ≤ p := by
    have hh : B ⊆ range p := fun b hb => mem_range.mpr (hB b hb).2
    simpa only [card_range] using card_le_card hh
  rw [lift_card p B (fun b hb => (hB b hb).2)]
  have hpH : p*H ≤ N := by
    dsimp [H]
    exact Nat.mul_div_le N p
  calc
    B.card^3 = B.card^2*B.card := by ring
    _ ≤ p^2*H^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hlabels 2) hsmall
    _ = (p*H)^2 := by ring
    _ ≤ N^2 := Nat.pow_le_pow_left hpH 2

#print axioms highDigit_pos
#print axioms level_card
#print axioms bounded_highDigit_card
#print axioms height_card_ceiling
end Erdos773.ParabolaSmallRepresentatives
