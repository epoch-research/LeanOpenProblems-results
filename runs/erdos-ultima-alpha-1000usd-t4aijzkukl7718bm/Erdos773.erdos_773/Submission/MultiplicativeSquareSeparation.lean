import Submission.PrivateModulusPacking

/-! Prime-power separation of scaled square fibers. This module does not
assert that all mixed-fiber square-sum collisions have matching labels. -/
namespace Erdos773.MultiplicativeSquareSeparation
open Finset PartialResidueFibers PrivateModulusPacking
set_option maxHeartbeats 1000000

lemma prime_power_square_divisibility {p k x y : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hx : ¬ p ∣ x) (hxy : x ≤ y)
    (hdiv : p^k ∣ y^2-x^2) : p^k ∣ y-x ∨ p^k ∣ y+x := by
  have hfactor : y^2-x^2=(y-x)*(y+x) := by
    have hsub : y-x+x=y := Nat.sub_add_cancel hxy
    have hsq : x^2 ≤ y^2 := Nat.pow_le_pow_left hxy 2
    have hsub2 := Nat.sub_add_cancel hsq
    nlinarith
  rw [hfactor] at hdiv
  by_cases hd : p ∣ y-x
  · have hn : ¬ p ∣ y+x := by
      intro hs
      have htw : p ∣ 2*x := by
        have h := Nat.dvd_sub hs hd
        have he : y+x-(y-x)=2*x := by omega
        rwa [he] at h
      rcases hp.dvd_mul.mp htw with htwo | hxx
      · exact hp2 ((Nat.dvd_prime Nat.prime_two).mp htwo |>.resolve_left hp.ne_one)
      · exact hx hxx
    exact Or.inl (((hp.coprime_iff_not_dvd.mpr hn).pow_left k).dvd_mul_right.mp hdiv)
  · exact Or.inr (((hp.coprime_iff_not_dvd.mpr hd).pow_left k).dvd_mul_left.mp hdiv)

/-- On a short positive interval of units, square residues modulo an odd
prime power identify the root itself. -/
theorem square_residue_injective {p k H : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hH : 2*H < p^k) :
    Set.InjOn (fun x : ℕ => x^2 % (p^k)) {x | x ≤ H ∧ ¬ p ∣ x} := by
  have ordered (x y : ℕ) (hx : x ≤ H ∧ ¬ p ∣ x)
      (hy : y ≤ H ∧ ¬ p ∣ y) (hxy : x ≤ y)
      (he : x^2 % (p^k)=y^2 % (p^k)) : x=y := by
    have hdiv : p^k ∣ y^2-x^2 :=
      (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left hxy 2)).mp he
    rcases prime_power_square_divisibility hp hp2 hx.2 hxy hdiv with hd | hs
    · have hsmall : y-x < p^k := by omega
      have hz := Nat.eq_zero_of_dvd_of_lt hd hsmall
      omega
    · have hsmall : y+x < p^k := by omega
      have hz := Nat.eq_zero_of_dvd_of_lt hs hsmall
      omega
  intro x hx y hy he
  rcases le_total x y with hxy | hyx
  · exact ordered x y hx hy hxy he
  · exact (ordered y x hy hx hyx he.symm).symm

/-- Multiplying the roots by a unit does not affect the injectivity test. -/
theorem scaled_square_residue_injective {p k H t : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ht : ¬ p ∣ t) (hH : 2*H < p^k) :
    Set.InjOn (fun x : ℕ => (t*x)^2 % (p^k)) {x | x ≤ H ∧ ¬ p ∣ x} := by
  intro x hx y hy he
  apply square_residue_injective hp hp2 hH hx hy
  have hcop : Nat.Coprime (p^k) (t^2) :=
    ((hp.coprime_iff_not_dvd.mpr ht).pow_left k).pow_right 2
  have he' : t^2*x^2 ≡ t^2*y^2 [MOD p^k] := by
    simpa only [Nat.ModEq, mul_pow] using he
  exact (Nat.ModEq.cancel_left_of_coprime hcop he' :
    x^2 ≡ y^2 [MOD p^k])

def scaledValues (t : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.image (fun a => (t*a)^2)

/-- All differences in the first fiber are divisible by p^(2k), while none
of the positive differences in the second fiber have that divisibility. -/
theorem separate_scaled_fibers {p k H s t : ℕ} (A B : Finset ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hs : p^k ∣ s) (ht : ¬ p ∣ t)
    (hB : ∀ b ∈ B, b ≤ H ∧ ¬ p ∣ b) (hH : 2*H < p^(2*k)) :
    Disjoint (positiveDiffs (scaledValues s A))
      (positiveDiffs (scaledValues t B)) := by
  apply separate_by_modulus (p^(2*k)) 0
  · intro a ha
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    have hd : p^(2*k) ∣ (s*x)^2 := by
      have h := pow_dvd_pow_of_dvd (dvd_mul_of_dvd_left hs x) 2
      simpa only [← pow_mul, Nat.mul_comm k 2] using h
    exact Nat.modEq_zero_iff_dvd.mpr hd
  · intro a ha b hb he
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hb
    have hxy := scaled_square_residue_injective hp hp2 ht hH (hB x hx) (hB y hy) he
    simp [hxy]

#print axioms prime_power_square_divisibility
#print axioms square_residue_injective
#print axioms scaled_square_residue_injective
#print axioms separate_scaled_fibers


lemma scaled_sidon {t : ℕ} (A : Finset ℕ) (ht : 0<t)
    (hA : IsSidon ((A.image (fun x => x^2) : Finset ℕ) : Set ℕ)) :
    IsSidon ((scaledValues t A : Finset ℕ) : Set ℕ) := by
  intro a ha c hc b hb d hd he
  obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hc
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hb
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hd
  have he' : x^2+y^2=z^2+w^2 := Nat.eq_of_mul_eq_mul_left (pow_pos ht 2) (by
    simpa only [mul_pow, Nat.mul_add] using he)
  rcases hA (x^2) (mem_image.mpr ⟨x,hx,rfl⟩)
    (z^2) (mem_image.mpr ⟨z,hz,rfl⟩)
    (y^2) (mem_image.mpr ⟨y,hy,rfl⟩)
    (w^2) (mem_image.mpr ⟨w,hw,rfl⟩) he' with h | h
  · exact Or.inl ⟨by simp only [mul_pow, h.1], by simp only [mul_pow, h.2]⟩
  · exact Or.inr ⟨by simp only [mul_pow, h.1], by simp only [mul_pow, h.2]⟩

/-- A genuine Sidon union of prime-scaled copies, provided the common seed
is Sidon and the distinct scale labels have modular pair matching. -/
theorem prime_scaled_union {q H : ℕ} (R A : Finset ℕ)
    (hA : A ⊆ Icc 1 H)
    (hSidon : IsSidon ((A.image (fun x => x^2) : Finset ℕ) : Set ℕ))
    (hclass : ∀ a ∈ A, a ≡ 1 [MOD q])
    (hM : MatchedResidueLifting.PairMatching q R)
    (hprime : ∀ p ∈ R, p.Prime ∧ p≠2)
    (hunit : ∀ p ∈ R, ∀ a ∈ A, ¬p∣a)
    (hshort : ∀ p ∈ R, 2*H < p^2) :
    IsSidon ((R.biUnion (fun p => scaledValues p A) : Finset ℕ) : Set ℕ) := by
  apply (sidon_iff_compatible q R (fun p => scaledValues p A) hM ?_).mpr
  · refine ⟨fun p hp => scaled_sidon A (hprime p hp).1.pos hSidon, ?_⟩
    intro p hp s hs hps
    have hnot : ¬p∣s := by
      intro hd
      rcases (Nat.dvd_prime (hprime s hs).1).mp hd with h | h
      · exact (hprime p hp).1.ne_one h
      · exact hps h
    apply separate_scaled_fibers (k := 1) A A (hprime p hp).1 (hprime p hp).2
      (by simp) hnot
    · intro a ha
      exact ⟨(mem_Icc.mp (hA ha)).2, hunit p hp a ha⟩
    · simpa using hshort p hp
  · intro p hp a ha
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    simpa using (Nat.ModEq.mul_left p (hclass x hx)).pow 2

lemma union_card_le (R A : Finset ℕ) :
    (R.biUnion (fun p => scaledValues p A)).card ≤ R.card*A.card := by
  calc
    _ ≤ ∑ p ∈ R, (scaledValues p A).card := card_biUnion_le
    _ ≤ ∑ _p ∈ R, A.card := sum_le_sum (fun p _ => card_image_le)
    _ = _ := by simp

/-- The common-residue and pair-matching costs alone bound the output mass.
This is a bound on this particular construction, not on arbitrary square sets. -/
theorem common_residue_mass {q H : ℕ} (R A : Finset ℕ) (hq : 0<q)
    (hA : A ⊆ Icc 1 H) (hcard : 2≤A.card)
    (hclass : ∀ a ∈ A, a ≡ 1 [MOD q])
    (hM : MatchedResidueLifting.PairMatching q R) :
    R.card*A.card ≤ 2*H := by
  have hAi : A ⊆ Icc 0 H := fun a ha => by
    have hh := mem_Icc.mp (hA ha)
    exact mem_Icc.mpr ⟨by omega,hh.2⟩
  have hm := residue_class_card q 1 H A hAi hclass
  have hmH : A.card ≤ H := by
    have h := card_le_card hA
    simpa using h
  have hquot : A.card-1 ≤ H/q := by omega
  have hcost : (A.card-1)*q ≤ H :=
    (Nat.mul_le_mul_right q hquot).trans (Nat.div_mul_le_self H q)
  have hcost' : A.card*q ≤ 2*H := by
    have hhalf : A.card ≤ 2*(A.card-1) := by omega
    nlinarith [Nat.mul_le_mul_right q hhalf]
  have hlabels := MatchedResidueLifting.pairMatching_card q R hq hM
  have hsquare : (R.card*A.card)^2 ≤ (2*H)^2 := by
    calc
      _ = R.card^2*A.card^2 := mul_pow _ _ _
      _ ≤ (2*q)*A.card^2 := Nat.mul_le_mul_right _ hlabels
      _ ≤ 4*H*A.card := by nlinarith [Nat.mul_le_mul_right A.card hcost']
      _ ≤ (2*H)^2 := by nlinarith [Nat.mul_le_mul_left (4*H) hmH]
  nlinarith

/-- At the declared root height P*H, the prime-square separation condition
leaves a two-thirds ceiling whenever the seed has at least two roots. -/
theorem construction_cube_bound {q H P : ℕ} (R A : Finset ℕ) (hq : 0<q)
    (hA : A ⊆ Icc 1 H) (hcard : 2≤A.card)
    (hclass : ∀ a ∈ A, a ≡ 1 [MOD q])
    (hM : MatchedResidueLifting.PairMatching q R)
    (hP : 2*H ≤ P^2) :
    (R.biUnion (fun p => scaledValues p A)).card^3 ≤ 4*(P*H)^2 := by
  have hmass := (union_card_le R A).trans (common_residue_mass R A hq hA hcard hclass hM)
  have hcube := Nat.pow_le_pow_left hmass 3
  have hheight := Nat.mul_le_mul_right (4*H^2) hP
  nlinarith

#print axioms prime_scaled_union
#print axioms common_residue_mass
#print axioms construction_cube_bound

/-- The declared product height really bounds every root used by the union. -/
theorem union_subset_squares {P H : ℕ} (R A : Finset ℕ)
    (hR : R ⊆ Icc 1 P) (hA : A ⊆ Icc 1 H) :
    R.biUnion (fun p => scaledValues p A) ⊆
      (Icc 1 (P*H)).image (fun x : ℕ => x^2) := by
  intro z hz
  obtain ⟨p,hp,a,ha,rfl⟩ := (by
    simpa only [mem_biUnion, scaledValues, mem_image] using hz :
      ∃ p ∈ R, ∃ a ∈ A, (p*a)^2=z)
  have hp' := mem_Icc.mp (hR hp)
  have ha' := mem_Icc.mp (hA ha)
  exact mem_image.mpr ⟨p*a,mem_Icc.mpr ⟨by nlinarith [hp'.1,ha'.1],
    Nat.mul_le_mul hp'.2 ha'.2⟩,rfl⟩

lemma scaled_card {t : ℕ} (A : Finset ℕ) (ht : 0<t) :
    (scaledValues t A).card=A.card := by
  apply card_image_of_injective
  intro a b he
  exact Nat.eq_of_mul_eq_mul_left ht (Nat.pow_left_injective (by decide : 2≠0) he)

/-- With prime scales and unit seed roots, different fibers do not overlap. -/
theorem prime_union_card (R A : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime)
    (hunit : ∀ p ∈ R, ∀ a ∈ A, ¬p∣a) :
    (R.biUnion (fun p => scaledValues p A)).card=R.card*A.card := by
  have hd : (R:Set ℕ).PairwiseDisjoint (fun p => scaledValues p A) := by
    intro p hp s hs hps
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    obtain ⟨b,hb,he⟩ := mem_image.mp hz'
    have he' : s*b=p*a := Nat.pow_left_injective (by decide : 2≠0) he
    have hpdiv : p ∣ s*b := he'.symm ▸ dvd_mul_right p a
    rcases (hprime p hp).dvd_mul.mp hpdiv with h | h
    · rcases (Nat.dvd_prime (hprime s hs)).mp h with h | h
      · exact (hprime p hp).ne_one h
      · exact hps h
    · exact hunit p hp b hb h
  rw [card_biUnion hd]
  calc
    _ = ∑ _p ∈ R, A.card := sum_congr rfl (fun p hp => scaled_card A (hprime p hp).pos)
    _ = _ := by simp

/-- Difference separation is not enough without matching the two scale labels.
Here 3²+14²=6²+13², with the common seed {1,2}. -/
theorem unmatched_prime_example :
    (∀ p ∈ ({3,7,13}:Finset ℕ), p.Prime ∧ p≠2 ∧ 2*2<p^2 ∧
      ∀ a ∈ ({1,2}:Finset ℕ), ¬p∣a) ∧
    ¬ IsSidon ((({3,7,13}:Finset ℕ).biUnion
      (fun p => scaledValues p {1,2}) : Finset ℕ) : Set ℕ) := by
  constructor
  · decide +kernel
  · intro h
    have ha : 9 ∈ ({3,7,13}:Finset ℕ).biUnion (fun p => scaledValues p {1,2}) := by decide +kernel
    have hb : 196 ∈ ({3,7,13}:Finset ℕ).biUnion (fun p => scaledValues p {1,2}) := by decide +kernel
    have hc : 169 ∈ ({3,7,13}:Finset ℕ).biUnion (fun p => scaledValues p {1,2}) := by decide +kernel
    have hd : 36 ∈ ({3,7,13}:Finset ℕ).biUnion (fun p => scaledValues p {1,2}) := by decide +kernel
    rcases h 9 ha 169 hc 196 hb 36 hd (by norm_num) with hh | hh <;> omega

#print axioms union_subset_squares
#print axioms prime_union_card
#print axioms unmatched_prime_example
end Erdos773.MultiplicativeSquareSeparation
