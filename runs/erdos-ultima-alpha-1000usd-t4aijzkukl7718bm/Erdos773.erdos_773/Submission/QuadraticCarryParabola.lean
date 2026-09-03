import Submission.ParabolaSquareLift

/-!
Quadratic shears of the carry-aware parabola. This file provides a
sufficient criterion for modular square-pair matching, but does not
assert enough small root representatives to settle Erdős 773.
-/
namespace Erdos773.QuadraticCarryParabola
open Finset ParabolaSquareLift
set_option maxHeartbeats 1500000
noncomputable section

def digit (p : ℕ) [Fact p.Prime] (kap lam mu : ZMod p) (b : ℕ) : ℕ :=
  (kap*(b:ZMod p)^2+lam*b+mu).val

def target (p : ℕ) [Fact p.Prime] (kap lam mu : ZMod p) (b : ℕ) : ℕ :=
  b^2%p+p*digit p kap lam mu b

def highDigit (p : ℕ) [Fact p.Prime] (kap lam mu : ZMod p) (b : ℕ) : ℕ :=
  ((kap*(b:ZMod p)^2+lam*b+mu-((b^2/p:ℕ):ZMod p))/(2*(b:ZMod p))).val

def root (p : ℕ) [Fact p.Prime] (kap lam mu : ZMod p) (b : ℕ) : ℕ :=
  b+p*highDigit p kap lam mu b

lemma root_mod (p b : ℕ) [Fact p.Prime] (kap lam mu : ZMod p) (hb : b<p) :
    root p kap lam mu b%p=b := by
  simp [root,Nat.add_mod,Nat.mod_eq_of_lt hb]

lemma root_pos (p b : ℕ) [Fact p.Prime] (kap lam mu : ZMod p) (hb : 0<b) :
    0<root p kap lam mu b := by
  dsimp [root]
  omega

lemma root_lt (p b : ℕ) [Fact p.Prime] (kap lam mu : ZMod p) (hb : b<p) :
    root p kap lam mu b<p^2 := by
  have hd : highDigit p kap lam mu b<p := ZMod.val_lt _
  dsimp [root]
  nlinarith

lemma highDigit_congruence (p b : ℕ) [Fact p.Prime] (kap lam mu : ZMod p)
    (h2 : (2:ZMod p) ≠ 0) (hb : 0<b) (hbp : b<p) :
    b^2/p+2*b*highDigit p kap lam mu b ≡ digit p kap lam mu b [MOD p] := by
  have hb0 : (b:ZMod p) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    simp [ZMod.val_natCast,Nat.mod_eq_of_lt hbp] at hh
    omega
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  rw [highDigit,digit,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,
    mul_div_cancel₀ _ (mul_ne_zero h2 hb0)]
  ring

lemma root_square_congruence (p b : ℕ) [Fact p.Prime] (kap lam mu : ZMod p)
    (h2 : (2:ZMod p) ≠ 0) (hb : 0<b) (hbp : b<p) :
    (root p kap lam mu b)^2 ≡ target p kap lam mu b [MOD p^2] := by
  have hd := highDigit_congruence p b kap lam mu h2 hb hbp
  have he : b^2/p+2*b*highDigit p kap lam mu b+p*(highDigit p kap lam mu b)^2 ≡
      digit p kap lam mu b [MOD p] := by
    simpa only [Nat.ModEq,Nat.add_mod,Nat.mul_mod_right,add_zero,Nat.mod_mod] using hd
  have he' := (he.mul_left' p).add_left (b^2%p)
  have hi : (root p kap lam mu b)^2 = b^2%p+
      p*(b^2/p+2*b*highDigit p kap lam mu b+p*(highDigit p kap lam mu b)^2) := by
    have hh := Nat.mod_add_div (b^2) p
    dsimp [root]
    nlinarith only [hh]
  change b^2%p+p*(b^2/p+2*b*highDigit p kap lam mu b+p*(highDigit p kap lam mu b)^2) ≡
    target p kap lam mu b [MOD p*p] at he'
  rw [← hi] at he'
  simpa only [pow_two] using he'

/-- The quadratic shear cancels from the high-digit sum. The half-band
condition is still required: low-digit carries cannot be ignored. -/
theorem target_pair_matching (p : ℕ) [Fact p.Prime] (kap lam mu : ZMod p)
    (h2 : (2:ZMod p) ≠ 0) (hlam : lam ≠ 0)
    {a b c d : ℕ} (ha : a<p) (hb : b<p) (hc : c<p) (hd : d<p)
    (hab : (2*(b^2%p)<p) ↔ (2*(a^2%p)<p))
    (hac : (2*(c^2%p)<p) ↔ (2*(a^2%p)<p))
    (had : (2*(d^2%p)<p) ↔ (2*(a^2%p)<p))
    (he : target p kap lam mu a+target p kap lam mu b ≡
      target p kap lam mu c+target p kap lam mu d [MOD p^2]) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hp := (Fact.out : p.Prime).pos
  have hl : a^2%p+b^2%p ≡ c^2%p+d^2%p [MOD p] := by
    have hh := he.of_dvd (show p ∣ p^2 from ⟨p,by ring⟩)
    simpa only [target,Nat.ModEq,Nat.add_mod,Nat.mul_mod_right,
      add_zero,Nat.mod_mod] using hh
  have hlow := same_half_sum (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)
    (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hab hac had hl
  have hh : (a^2%p+b^2%p)+p*(digit p kap lam mu a+digit p kap lam mu b) ≡
      (c^2%p+d^2%p)+p*(digit p kap lam mu c+digit p kap lam mu d) [MOD p^2] := by
    convert he using 1 <;> dsimp [target] <;> ring
  rw [hlow] at hh
  have hhi := Nat.ModEq.add_left_cancel' (c^2%p+d^2%p) hh
  have hs : digit p kap lam mu a+digit p kap lam mu b ≡
      digit p kap lam mu c+digit p kap lam mu d [MOD p] := by
    apply Nat.ModEq.mul_left_cancel' (by omega : p ≠ 0)
    simpa only [pow_two] using hhi
  have hsq : a^2+b^2 ≡ c^2+d^2 [MOD p] := by
    simpa only [Nat.ModEq,Nat.add_mod,Nat.mod_mod] using hl
  have hsq' : (a:ZMod p)^2+b^2=c^2+d^2 := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr hsq
  have hs' := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hs
  simp only [Nat.cast_add,digit,ZMod.natCast_zmod_val] at hs'
  have hmul : lam*((a:ZMod p)+b-c-d)=0 := by
    linear_combination hs' - kap*hsq'
  have hsum : (a:ZMod p)+b=c+d := by
    have hz := (mul_eq_zero.mp hmul).resolve_left hlam
    linear_combination hz
  have hinj {x y : ℕ} (hx : x<p) (hy : y<p)
      (heq : (x:ZMod p)=(y:ZMod p)) : x=y := by
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using hv
  rcases pair_eq_of_sum_and_square_sum h2 hsum hsq' with h | h
  · exact Or.inl ⟨hinj ha hc h.1,hinj hb hd h.2⟩
  · exact Or.inr ⟨hinj ha hd h.1,hinj hb hc h.2⟩

/-- A sufficient criterion for arbitrary chosen root representatives; the
representatives need not be the canonical lift defined above. -/
theorem chosen_pair_matching (p : ℕ) [Fact p.Prime] (kap lam mu : ZMod p)
    (h2 : (2:ZMod p) ≠ 0) (hlam : lam ≠ 0)
    (B : Finset ℕ) (f : ℕ → ℕ) (hB : ∀ b∈B, b<p)
    (hhalf : ∀ a∈B, ∀ b∈B, (2*(a^2%p)<p) ↔ (2*(b^2%p)<p))
    (hf : ∀ b∈B, (f b)^2 ≡ target p kap lam mu b [MOD p^2]) :
    MatchedResidueLifting.PairMatching (p^2) (B.image f) := by
  intro r hr s hs t ht u hu he
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hr
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hs
  obtain ⟨c,hc,rfl⟩ := mem_image.mp ht
  obtain ⟨d,hd,rfl⟩ := mem_image.mp hu
  have he' := ((hf a ha).add (hf b hb)).symm.trans
    (he.trans ((hf c hc).add (hf d hd)))
  rcases target_pair_matching p kap lam mu h2 hlam
    (hB a ha) (hB b hb) (hB c hc) (hB d hd)
    (hhalf b hb a ha) (hhalf c hc a ha) (hhalf d hd a ha) he' with h | h
  · exact Or.inl ⟨congrArg f h.1,congrArg f h.2⟩
  · exact Or.inr ⟨congrArg f h.1,congrArg f h.2⟩

lemma root_card (p : ℕ) [Fact p.Prime] (kap lam mu : ZMod p)
    (B : Finset ℕ) (hB : ∀ b∈B, b<p) :
    (B.image (root p kap lam mu)).card=B.card := by
  apply card_image_of_injOn
  intro a ha b hb he
  have hh := congrArg (fun n : ℕ => n%p) he
  simpa only [root_mod p a kap lam mu (hB a ha),root_mod p b kap lam mu (hB b hb)] using hh

/-- Modular pair matching already implies ordinary Sidonness of the
square values, with repeated entries included. -/
lemma squares_sidon_of_pair_matching (q : ℕ) (R : Finset ℕ)
    (hM : MatchedResidueLifting.PairMatching q R) :
    IsSidon ((R.image (fun n => n^2) : Finset ℕ) : Set ℕ) := by
  intro a ha c hc b hb d hd he
  obtain ⟨r,hr,rfl⟩ := mem_image.mp ha
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hc
  obtain ⟨s,hs,rfl⟩ := mem_image.mp hb
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hd
  have hm : r^2+s^2 ≡ t^2+u^2 [MOD q] := by rw [he]
  rcases hM r hr s hs t ht u hu hm with h | h
  · exact Or.inl ⟨congrArg (fun n => n^2) h.1,congrArg (fun n => n^2) h.2⟩
  · exact Or.inr ⟨congrArg (fun n => n^2) h.1,congrArg (fun n => n^2) h.2⟩

/-- The canonical quadratic-shear lift gives an actual Sidon set for any
chosen labels in one half-band. No useful small-height count is assumed. -/
theorem lift_squares_sidon (p : ℕ) [Fact p.Prime] (kap lam mu : ZMod p)
    (h2 : (2:ZMod p) ≠ 0) (hlam : lam ≠ 0)
    (B : Finset ℕ) (hB : ∀ b∈B, 0<b ∧ b<p)
    (hhalf : ∀ a∈B, ∀ b∈B, (2*(a^2%p)<p) ↔ (2*(b^2%p)<p)) :
    IsSidon (((B.image (root p kap lam mu)).image (fun n => n^2) : Finset ℕ) : Set ℕ) := by
  apply squares_sidon_of_pair_matching (p^2)
  apply chosen_pair_matching p kap lam mu h2 hlam B (root p kap lam mu)
    (fun b hb => (hB b hb).2) hhalf
  intro b hb
  exact root_square_congruence p b kap lam mu h2 (hB b hb).1 (hB b hb).2

lemma chosen_root_card (p : ℕ) [Fact p.Prime] (kap lam mu : ZMod p)
    (h2 : (2:ZMod p) ≠ 0) (hlam : lam ≠ 0)
    (B : Finset ℕ) (f : ℕ → ℕ) (hB : ∀ b∈B, b<p)
    (hhalf : ∀ a∈B, ∀ b∈B, (2*(a^2%p)<p) ↔ (2*(b^2%p)<p))
    (hf : ∀ b∈B, (f b)^2 ≡ target p kap lam mu b [MOD p^2]) :
    (B.image f).card=B.card := by
  apply card_image_of_injOn
  intro a ha b hb he
  have he' : target p kap lam mu a ≡ target p kap lam mu b [MOD p^2] := by
    apply (hf a ha).symm.trans
    rw [he]
    exact hf b hb
  rcases target_pair_matching p kap lam mu h2 hlam
    (hB a ha) (hB a ha) (hB b hb) (hB b hb) Iff.rfl
    (hhalf b hb a ha) (hhalf b hb a ha) (he'.add he') with h | h
  · exact h.1
  · exact h.1

/-- A height-count transfer for any chosen representatives, including
independent sign choices. Every hypothesis is retained explicitly. -/
theorem finite_lower (p N : ℕ) [Fact p.Prime] (kap lam mu : ZMod p)
    (h2 : (2:ZMod p) ≠ 0) (hlam : lam ≠ 0)
    (B : Finset ℕ) (f : ℕ → ℕ) (hB : ∀ b∈B, b<p)
    (hhalf : ∀ a∈B, ∀ b∈B, (2*(a^2%p)<p) ↔ (2*(b^2%p)<p))
    (hf : ∀ b∈B, (f b)^2 ≡ target p kap lam mu b [MOD p^2])
    (hN : ∀ b∈B, 0<f b ∧ f b≤N) :
    B.card ≤ maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) := by
  let R := B.image f
  have hcard : (R.image (fun n => n^2)).card=B.card := by
    rw [card_image_of_injective _ (Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0))]
    exact chosen_root_card p kap lam mu h2 hlam B f hB hhalf hf
  have hR : R ⊆ Icc 1 N := by
    intro r hr
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hr
    exact mem_Icc.mpr (hN b hb)
  have hs : IsSidon ((R.image (fun n => n^2) : Finset ℕ) : Set ℕ) :=
    squares_sidon_of_pair_matching (p^2) R
      (chosen_pair_matching p kap lam mu h2 hlam B f hB hhalf hf)
  rw [← hcard]
  apply le_sup
  exact mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image hR),hs⟩

/-- A half-band can always be selected at a loss of at most two. This
reduces a positive construction to counting small representatives. -/
theorem height_count_transfer (p N : ℕ) [Fact p.Prime] (kap lam mu : ZMod p)
    (h2 : (2:ZMod p) ≠ 0) (hlam : lam ≠ 0)
    (B : Finset ℕ) (f : ℕ → ℕ) (hB : ∀ b∈B, b<p)
    (hf : ∀ b∈B, (f b)^2 ≡ target p kap lam mu b [MOD p^2])
    (hN : ∀ b∈B, 0<f b ∧ f b≤N) :
    B.card ≤ 2*maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) := by
  let L := B.filter (fun b => 2*(b^2%p)<p)
  let U := B.filter (fun b => ¬2*(b^2%p)<p)
  have hLU : L.card+U.card=B.card := card_filter_add_card_filter_not _
  have hL : L.card ≤ maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) := by
    apply finite_lower p N kap lam mu h2 hlam L f
    · exact fun b hb => hB b (mem_filter.mp hb).1
    · intro a ha b hb
      exact iff_of_true (mem_filter.mp ha).2 (mem_filter.mp hb).2
    · exact fun b hb => hf b (mem_filter.mp hb).1
    · exact fun b hb => hN b (mem_filter.mp hb).1
  have hU : U.card ≤ maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) := by
    apply finite_lower p N kap lam mu h2 hlam U f
    · exact fun b hb => hB b (mem_filter.mp hb).1
    · intro a ha b hb
      exact iff_of_false (mem_filter.mp ha).2 (mem_filter.mp hb).2
    · exact fun b hb => hf b (mem_filter.mp hb).1
    · exact fun b hb => hN b (mem_filter.mp hb).1
  omega

#print axioms root_square_congruence
#print axioms target_pair_matching
#print axioms chosen_pair_matching
#print axioms root_card
#print axioms lift_squares_sidon
#print axioms finite_lower
#print axioms height_count_transfer
end
end Erdos773.QuadraticCarryParabola
