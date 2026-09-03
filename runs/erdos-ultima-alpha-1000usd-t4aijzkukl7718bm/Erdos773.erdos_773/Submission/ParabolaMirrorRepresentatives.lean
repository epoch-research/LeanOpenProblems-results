import Submission.ParabolaSmallRepresentatives

/-!
The complementary square roots in the specific carry-aware parabola lift.
Allowing either sign does not remove that construction's two-thirds height
ceiling. No assertion about arbitrary square-Sidon sets is made.
-/
namespace Erdos773.ParabolaMirrorRepresentatives
open Finset ParabolaSquareLift ParabolaSmallRepresentatives
set_option maxHeartbeats 1500000
noncomputable section

def mirror (p : ℕ) [Fact p.Prime] (b : ℕ) : ℕ := p^2-root p b

lemma quotient_complement {p b : ℕ} (hp : 0 < p) (hb : b ≤ p) :
    (p-b)^2/p+2*b=p+b^2/p := by
  have hsum : p-b+b=p := Nat.sub_add_cancel hb
  have he : (p-b)^2+p*(2*b)=p*p+b^2 := by nlinarith only [hsum]
  have hd := congrArg (fun n : ℕ => n/p) he
  simpa only [Nat.add_mul_div_left _ _ hp,Nat.mul_add_div hp] using hd

/-- The two high digits at complementary nonzero labels add to p. -/
theorem highDigit_complement (p : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) {b : ℕ} (hb : 0 < b) (hbp : b < p) :
    highDigit p b+highDigit p (p-b)=p := by
  have hp := (Fact.out : p.Prime).pos
  have hc : 0 < p-b := by omega
  have hcp : p-b < p := by omega
  have hq := quotient_complement hp hbp.le
  have hcmod : ((p-b : ℕ) : ZMod p)=-(b : ZMod p) := by
    rw [Nat.cast_sub hbp.le,ZMod.natCast_self,zero_sub]
  have hqmod : (((p-b)^2/p : ℕ) : ZMod p)+2*(b : ZMod p)=((b^2/p : ℕ) : ZMod p) := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hq
    simpa using h
  have hbmod : ((b^2/p : ℕ) : ZMod p)+2*(b : ZMod p)*(highDigit p b : ℕ)=(b : ZMod p) := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (highDigit_congruence p b h2 hb hbp)
  have hcmod' : (((p-b)^2/p : ℕ) : ZMod p)+2*((p-b : ℕ) : ZMod p)*
      (highDigit p (p-b) : ℕ)=((p-b : ℕ) : ZMod p) := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (highDigit_congruence p (p-b) h2 hc hcp)
  rw [hcmod] at hcmod'
  have he : 2*(b : ZMod p)*((highDigit p b : ℕ)+(highDigit p (p-b) : ℕ))=0 := by
    linear_combination hbmod-hcmod'+hqmod
  have hbne : (b : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff b p).mp h
    have hle := Nat.le_of_dvd hb hd
    omega
  have hzero := (mul_eq_zero.mp he).resolve_left (mul_ne_zero h2 hbne)
  have hdiv : p ∣ highDigit p b+highDigit p (p-b) := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    simpa only [Nat.cast_add] using hzero
  have ha₀ := highDigit_pos p h2 hb hbp
  have ha : highDigit p b < p := ZMod.val_lt _
  have hac : highDigit p (p-b) < p := ZMod.val_lt _
  exact Nat.eq_of_dvd_of_lt_two_mul (by omega) hdiv (by omega)

/-- Taking the complementary canonical root is the same as subtracting p
from the usual lifted root at the complementary label. -/
theorem mirror_add (p : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) {b : ℕ} (hb : 0 < b) (hbp : b < p) :
    mirror p b+p=root p (p-b) := by
  have hhigh := highDigit_complement p h2 hb hbp
  have hlabel : b+(p-b)=p := Nat.add_sub_of_le hbp.le
  have hroots : root p b+root p (p-b)=p^2+p := by
    dsimp [root]
    nlinarith only [hhigh,hlabel]
  have hrootlt := root_lt p b hbp
  dsimp [mirror]
  omega

lemma mirror_pos (p : ℕ) [Fact p.Prime] {b : ℕ} (hbp : b < p) :
    0 < mirror p b := Nat.sub_pos_of_lt (root_lt p b hbp)

/-- With complementary roots of height N, at most (floor(N/p)+1)² labels
can occur. This count does not assume pair matching or Sidonness. -/
theorem bounded_mirror_card (p : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (B : Finset ℕ)
    (hB : ∀ b ∈ B, 0 < b ∧ b < p) (N : ℕ)
    (hN : ∀ b ∈ B, mirror p b ≤ N) : B.card ≤ (N/p+1)^2 := by
  have hp := (Fact.out : p.Prime).pos
  let C := B.image (fun b => p-b)
  have hC : ∀ c ∈ C, 0 < c ∧ c < p := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hc
    have hh := hB b hb
    omega
  have hcard : C.card=B.card := by
    apply card_image_of_injOn
    intro b hb c hc he
    have hb' := hB b hb
    have hc' := hB c hc
    dsimp only at he
    omega
  have hheight : ∀ c ∈ C, root p c ≤ N+p := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hc
    rw [← mirror_add p h2 (hB b hb).1 (hB b hb).2]
    exact Nat.add_le_add_right (hN b hb) _
  have hhigh : ∀ c ∈ C, highDigit p c ≤ N/p+1 := by
    intro c hc
    have hh := hheight c hc
    have hm : highDigit p c*p ≤ N+p := by dsimp [root] at hh; nlinarith only [hh]
    have hdiv := (Nat.le_div_iff_mul_le hp).mpr hm
    simpa only [Nat.add_div_right N hp] using hdiv
  rw [← hcard]
  exact bounded_highDigit_card p h2 C hC (N/p+1) hhigh

/-- A label-dependent sign choice: true selects the original root, false
its complementary canonical representative. -/
def chosenRoot (p : ℕ) [Fact p.Prime] (σ : ℕ → Bool) (b : ℕ) : ℕ :=
  if σ b then root p b else mirror p b

/-- Even choosing the sign separately for every label cannot give a
near-linear family at small root height through this particular lift. -/
theorem signed_height_card_ceiling (p : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (B : Finset ℕ)
    (hB : ∀ b ∈ B, 0 < b ∧ b < p) (σ : ℕ → Bool) (N : ℕ)
    (hN : ∀ b ∈ B, chosenRoot p σ b ≤ N) :
    ((B.image (chosenRoot p σ)).card)^3 ≤ 5*N^2 := by
  have hp := (Fact.out : p.Prime).pos
  let H := N/p
  let L := B.filter (fun b => σ b=true)
  let R := B.filter (fun b => ¬ σ b=true)
  have hLR : L.card+R.card=B.card := card_filter_add_card_filter_not _
  have hL : L.card ≤ H^2 := by
    apply bounded_highDigit_card p h2 L (fun b hb => hB b (mem_filter.mp hb).1) H
    intro b hb
    obtain ⟨hbB,hσ⟩ := mem_filter.mp hb
    have hn := hN b hbB
    simp only [chosenRoot,hσ,↓reduceIte] at hn
    apply (Nat.le_div_iff_mul_le hp).mpr
    dsimp [root] at hn
    nlinarith only [hn]
  have hR : R.card ≤ (H+1)^2 := by
    apply bounded_mirror_card p h2 R (fun b hb => hB b (mem_filter.mp hb).1) N
    intro b hb
    obtain ⟨hbB,hσ⟩ := mem_filter.mp hb
    have hn := hN b hbB
    simpa only [chosenRoot,hσ,↓reduceIte] using hn
  have hlabels : B.card ≤ p := by
    have hh : B ⊆ range p := fun b hb => mem_range.mpr (hB b hb).2
    simpa only [card_range] using card_le_card hh
  have himage : (B.image (chosenRoot p σ)).card ≤ B.card := card_image_le
  apply (Nat.pow_le_pow_left himage 3).trans
  by_cases hzero : N=0
  · subst N
    have he : B=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      have hn := hN b hb
      have hpos : 0 < chosenRoot p σ b := by
        unfold chosenRoot
        split
        · exact root_pos p b (hB b hb).1
        · exact mirror_pos p (hB b hb).2
      omega
    simp [he]
  · have hN₀ : 1 ≤ N := Nat.pos_of_ne_zero hzero
    by_cases hHz : H=0
    · rw [hHz] at hL hR
      have hL0 : L.card=0 := Nat.eq_zero_of_le_zero (by simpa only [zero_pow (by decide : 2 ≠ 0)] using hL)
      have hR1 : R.card ≤ 1 := by simpa only [zero_add,one_pow] using hR
      have hm : B.card ≤ 1 := by omega
      have hn : 1 ≤ N^2 := Nat.one_le_pow _ _ hN₀
      have hh : B.card^3 ≤ 1 := by simpa only [one_pow] using Nat.pow_le_pow_left hm 3
      exact hh.trans (hn.trans (by omega))
    · have hH₀ : 1 ≤ H := Nat.pos_of_ne_zero hHz
      have hsmall : B.card ≤ 5*H^2 := by nlinarith only [hL,hR,hLR,hH₀]
      have hpH : p*H ≤ N := Nat.mul_div_le N p
      calc
        B.card^3 = B.card^2*B.card := by ring
        _ ≤ p^2*(5*H^2) := Nat.mul_le_mul (Nat.pow_le_pow_left hlabels 2) hsmall
        _ = 5*(p*H)^2 := by ring
        _ ≤ 5*N^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpH 2)

#print axioms highDigit_complement
#print axioms mirror_add
#print axioms bounded_mirror_card
#print axioms signed_height_card_ceiling
end
end Erdos773.ParabolaMirrorRepresentatives
