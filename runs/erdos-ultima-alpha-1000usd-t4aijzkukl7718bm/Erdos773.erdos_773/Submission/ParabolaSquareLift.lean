import Submission.MatchedResidueLifting

/-!
Carry-aware lifting of the prime-field parabola to quadratic residues modulo p².
This supplies modular pair matching, not a near-linear Sidon subset of integer squares.
-/
namespace Erdos773.ParabolaSquareLift
open Finset
set_option maxHeartbeats 1000000

lemma pair_eq_of_sum_and_square_sum {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {a b c d : K} (hs : a+b=c+d) (hq : a^2+b^2=c^2+d^2) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hb : b=c+d-a := by linear_combination hs
  rw [hb] at hq
  have he : (2 : K)*((a-c)*(a-d))=0 := by linear_combination hq
  have hf := (mul_eq_zero.mp he).resolve_left h2
  rcases mul_eq_zero.mp hf with h | h
  · left
    have ha := sub_eq_zero.mp h
    exact ⟨ha, by linear_combination hs - ha⟩
  · right
    have ha := sub_eq_zero.mp h
    exact ⟨ha, by linear_combination hs - ha⟩

/-- The high digit needed to put the lifted square on the parabola. -/
noncomputable def highDigit (p : ℕ) [Fact p.Prime] (b : ℕ) : ℕ :=
  (((b : ZMod p) - ((b^2/p : ℕ) : ZMod p)) / (2*(b : ZMod p))).val

noncomputable def root (p : ℕ) [Fact p.Prime] (b : ℕ) : ℕ := b+p*highDigit p b

def target (p b : ℕ) : ℕ := b^2%p+p*b

lemma root_mod (p b : ℕ) [Fact p.Prime] (hb : b<p) : root p b % p=b := by
  simp [root, Nat.add_mod, Nat.mod_eq_of_lt hb]

lemma root_pos (p b : ℕ) [Fact p.Prime] (hb : 0<b) : 0<root p b := by
  dsimp [root]
  omega

lemma root_lt (p b : ℕ) [Fact p.Prime] (hb : b<p) : root p b<p^2 := by
  have hd : highDigit p b<p := by
    dsimp [highDigit]
    exact ZMod.val_lt _
  dsimp [root]
  nlinarith

lemma highDigit_congruence (p b : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (hb : 0<b) (hbp : b<p) :
    b^2/p+2*b*highDigit p b ≡ b [MOD p] := by
  have hb0 : (b : ZMod p) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hbp] at hh
    omega
  have hv : ((highDigit p b : ℕ) : ZMod p) =
      ((b : ZMod p) - ((b^2/p : ℕ) : ZMod p))/(2*(b : ZMod p)) := by
    exact ZMod.natCast_zmod_val _
  have he : (((b^2/p+2*b*highDigit p b : ℕ)) : ZMod p) = (b : ZMod p) := by
    push_cast
    rw [hv, mul_div_cancel₀ _ (mul_ne_zero h2 hb0)]
    ring
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp he

lemma root_square_congruence (p b : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (hb : 0<b) (hbp : b<p) :
    (root p b)^2 ≡ target p b [MOD p^2] := by
  have hd := highDigit_congruence p b h2 hb hbp
  have he : b^2/p+2*b*highDigit p b+p*(highDigit p b)^2 ≡ b [MOD p] := by
    simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero,
      Nat.mod_mod] using hd
  have he' := (he.mul_left' p).add_left (b^2%p)
  have hi : (root p b)^2 = b^2%p+p*(b^2/p+2*b*highDigit p b+p*(highDigit p b)^2) := by
    have hh := Nat.mod_add_div (b^2) p
    dsimp [root]
    nlinarith only [hh]
  change b^2%p+p*(b^2/p+2*b*highDigit p b+p*(highDigit p b)^2) ≡
    target p b [MOD p*p] at he'
  rw [← hi] at he'
  simpa only [pow_two] using he'

/-- Using one half-interval eliminates the carry ambiguity in a pair sum. -/
lemma same_half_sum {p a b c d : ℕ}
    (ha : a<p) (hb : b<p) (hc : c<p) (hd : d<p)
    (hab : (2*b<p) ↔ (2*a<p)) (hac : (2*c<p) ↔ (2*a<p))
    (had : (2*d<p) ↔ (2*a<p)) (he : a+b ≡ c+d [MOD p]) :
    a+b=c+d := by
  have hrange : (a+b<p ∧ c+d<p) ∨ (p≤a+b ∧ p≤c+d) := by
    by_cases h : 2*a<p
    · have hb' := hab.mpr h
      have hc' := hac.mpr h
      have hd' := had.mpr h
      left; omega
    · have hb' : ¬2*b<p := fun hh => h (hab.mp hh)
      have hc' : ¬2*c<p := fun hh => h (hac.mp hh)
      have hd' : ¬2*d<p := fun hh => h (had.mp hh)
      right; omega
  rcases lt_trichotomy (a+b) (c+d) with h | h | h
  · have hh := he.add_le_of_lt h
    rcases hrange with hh' | hh' <;> omega
  · exact h
  · have hh := he.symm.add_le_of_lt h
    rcases hrange with hh' | hh' <;> omega

lemma target_pair_matching (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    {a b c d : ℕ} (ha : a<p) (hb : b<p) (hc : c<p) (hd : d<p)
    (hab : (2*(b^2%p)<p) ↔ (2*(a^2%p)<p))
    (hac : (2*(c^2%p)<p) ↔ (2*(a^2%p)<p))
    (had : (2*(d^2%p)<p) ↔ (2*(a^2%p)<p))
    (he : target p a+target p b ≡ target p c+target p d [MOD p^2]) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hp := (Fact.out : p.Prime).pos
  have hl : a^2%p+b^2%p ≡ c^2%p+d^2%p [MOD p] := by
    have hh := he.of_dvd (show p ∣ p^2 from ⟨p, by ring⟩)
    simpa only [target, Nat.ModEq, Nat.add_mod, Nat.mul_mod_right,
      add_zero, Nat.mod_mod] using hh
  have hlow := same_half_sum (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)
    (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hab hac had hl
  have hh : (a^2%p+b^2%p)+p*(a+b) ≡
      (c^2%p+d^2%p)+p*(c+d) [MOD p^2] := by
    convert he using 1 <;> dsimp [target] <;> ring
  rw [hlow] at hh
  have hhi := Nat.ModEq.add_left_cancel' (c^2%p+d^2%p) hh
  have hs : a+b ≡ c+d [MOD p] := by
    apply Nat.ModEq.mul_left_cancel' (by omega : p ≠ 0)
    simpa only [pow_two] using hhi
  have hsq : a^2+b^2 ≡ c^2+d^2 [MOD p] := by
    simpa only [Nat.ModEq, Nat.add_mod, Nat.mod_mod] using hl
  have hs' : (a : ZMod p)+b=c+d := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr hs
  have hsq' : (a : ZMod p)^2+b^2=c^2+d^2 := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr hsq
  have hinj {x y : ℕ} (hx : x<p) (hy : y<p)
      (heq : (x : ZMod p)=(y : ZMod p)) : x=y := by
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hv
  rcases pair_eq_of_sum_and_square_sum h2 hs' hsq' with h | h
  · exact Or.inl ⟨hinj ha hc h.1, hinj hb hd h.2⟩
  · exact Or.inr ⟨hinj ha hd h.1, hinj hb hc h.2⟩

/-- An arbitrary collection of labels in one half-band lifts to pair matching. -/
theorem lift_pair_matching (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (B : Finset ℕ) (hB : ∀ b∈B, 0<b ∧ b<p)
    (hhalf : ∀ a∈B, ∀ b∈B, (2*(a^2%p)<p) ↔ (2*(b^2%p)<p)) :
    MatchedResidueLifting.PairMatching (p^2) (B.image (root p)) := by
  intro r hr s hs t ht u hu he
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hr
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hs
  obtain ⟨c,hc,rfl⟩ := mem_image.mp ht
  obtain ⟨d,hd,rfl⟩ := mem_image.mp hu
  have ha' := hB a ha
  have hb' := hB b hb
  have hc' := hB c hc
  have hd' := hB d hd
  have hmod : target p a+target p b ≡ target p c+target p d [MOD p^2] :=
    ((root_square_congruence p a h2 ha'.1 ha'.2).add
      (root_square_congruence p b h2 hb'.1 hb'.2)).symm.trans
      (he.trans ((root_square_congruence p c h2 hc'.1 hc'.2).add
        (root_square_congruence p d h2 hd'.1 hd'.2)))
  rcases target_pair_matching p h2 ha'.2 hb'.2 hc'.2 hd'.2
    (hhalf b hb a ha) (hhalf c hc a ha) (hhalf d hd a ha) hmod with h | h
  · exact Or.inl ⟨congrArg (root p) h.1, congrArg (root p) h.2⟩
  · exact Or.inr ⟨congrArg (root p) h.1, congrArg (root p) h.2⟩

lemma lift_card (p : ℕ) [Fact p.Prime] (B : Finset ℕ) (hB : ∀ b∈B, b<p) :
    (B.image (root p)).card=B.card := by
  apply card_image_of_injOn
  intro a ha b hb he
  have hh := congrArg (fun n : ℕ => n%p) he
  simpa only [root_mod p a (hB a ha), root_mod p b (hB b hb)] using hh

lemma root_unit (p b : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hb : 0<b) (hbp : b<p) : (p^2).Coprime (2*root p b) := by
  have hp := (Fact.out : p.Prime)
  have hpr : p.Coprime (root p b) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdiv
    have hz := Nat.mod_eq_zero_of_dvd hdiv
    rw [root_mod p b hbp] at hz
    omega
  have hpTwo : p.Coprime 2 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdiv
    have hle := Nat.le_of_dvd (by decide : 0<2) hdiv
    have hge := hp.two_le
    omega
  exact (hpTwo.mul_right hpr).pow_left 2

/-- Explicitly, a canonical unit root set of size at least (p-1)/2 can have
square-pair matching modulo p². This is only a modular construction. -/
theorem exists_pair_matching (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ R : Finset ℕ, p-1 ≤ 2*R.card ∧
      (∀ r∈R, 0<r ∧ r<p^2 ∧ (p^2).Coprime (2*r)) ∧
      MatchedResidueLifting.PairMatching (p^2) R := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro he
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp he
    have hle := Nat.le_of_dvd (by decide : 0<2) hdiv
    have hge := hp.two_le
    omega
  let A := Icc 1 (p-1)
  let L := A.filter (fun b => 2*(b^2%p)<p)
  let U := A.filter (fun b => ¬2*(b^2%p)<p)
  have htotal : L.card+U.card=p-1 := by
    have hh := card_filter_add_card_filter_not (s:=A) (fun b => 2*(b^2%p)<p)
    simpa only [A, Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hmem {b : ℕ} (hb : b∈A) : 0<b ∧ b<p := by
    simp only [A, mem_Icc] at hb
    omega
  have hmake (B : Finset ℕ) (hBA : B⊆A) (hcard : p-1 ≤ 2*B.card)
      (hhalf : ∀ a∈B, ∀ b∈B, (2*(a^2%p)<p) ↔ (2*(b^2%p)<p)) :
      ∃ R : Finset ℕ, p-1 ≤ 2*R.card ∧
        (∀ r∈R, 0<r ∧ r<p^2 ∧ (p^2).Coprime (2*r)) ∧
        MatchedResidueLifting.PairMatching (p^2) R := by
    refine ⟨B.image (root p), ?_, ?_, ?_⟩
    · rw [lift_card p B (fun b hb => (hmem (hBA hb)).2)]
      exact hcard
    · intro r hr
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hr
      exact ⟨root_pos p b (hmem (hBA hb)).1, root_lt p b (hmem (hBA hb)).2,
        root_unit p b hp2 (hmem (hBA hb)).1 (hmem (hBA hb)).2⟩
    · exact lift_pair_matching p h2 B (fun b hb => hmem (hBA hb)) hhalf
  by_cases h : U.card ≤ L.card
  · apply hmake L (filter_subset _ _) (by omega)
    intro a ha b hb
    exact iff_of_true (mem_filter.mp ha).2 (mem_filter.mp hb).2
  · apply hmake U (filter_subset _ _) (by omega)
    intro a ha b hb
    exact iff_of_false (mem_filter.mp ha).2 (mem_filter.mp hb).2

section BaseThree
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

lemma root_three_values : root 3 1=7 ∧ root 3 2=5 := by
  have h2 : (2 : ZMod 3)⁻¹ = 2 := by decide +kernel
  have h4 : (4 : ZMod 3)⁻¹ = 1 := by decide +kernel
  norm_num [root, highDigit]
  rw [h2, h4]
  decide +kernel

lemma three_lift_image : (Icc 1 2).image (root 3) = {5,7} := by
  have he : Icc 1 2 = ({1,2} : Finset ℕ) := by decide
  rw [he]
  simp only [image_insert, image_singleton, root_three_values.1, root_three_values.2]
  exact pair_comm _ _

/-- Even the actual parabola lift does not allow its complete short fibers
 to be combined without additional cross-fiber control. -/
theorem full_fiber_obstruction :
    MatchedResidueLifting.PairMatching 9 {5,7} ∧
    ¬ IsSidon (((MatchedResidueLifting.roots 9 9 {5,7}).image
      (fun n => n^2)) : Set ℕ) := by
  constructor
  · unfold MatchedResidueLifting.PairMatching
    decide +kernel
  · intro hs
    have he := hs (41^2) (by decide) (7^2) (by decide)
      (43^2) (by decide) (59^2) (by decide) (by norm_num)
    norm_num at he

end BaseThree

#print axioms root_unit
#print axioms root_square_congruence
#print axioms target_pair_matching
#print axioms lift_pair_matching
#print axioms exists_pair_matching
#print axioms three_lift_image
#print axioms full_fiber_obstruction
end Erdos773.ParabolaSquareLift
