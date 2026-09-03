import Submission.PartialResidueFibers

/-!
A private-modulus way to separate actual difference spectra, together with
its cardinality cost. The cost theorem is conditional on this particular
selector and is NOT an upper bound for arbitrary square-Sidon sets.
-/
namespace Erdos773.PrivateModulusPacking
open Finset PartialResidueFibers MatchedResidueLifting
set_option maxHeartbeats 1000000

/-- A common residue in U and injective residues in V separate their positive
integer differences. No division by the modulus is implicit here. -/
theorem separate_by_modulus (p c : ℕ) (U V : Finset ℕ)
    (hU : ∀ a ∈ U, a ≡ c [MOD p])
    (hV : Set.InjOn (fun a : ℕ => a%p) (V : Set ℕ)) :
    Disjoint (positiveDiffs U) (positiveDiffs V) := by
  apply disjoint_left.mpr
  intro D hDU hDV
  obtain ⟨a,ha,b,hb,hab,heab⟩ := mem_positiveDiffs.mp hDU
  obtain ⟨x,hx,y,hy,hxy,hexy⟩ := mem_positiveDiffs.mp hDV
  have habmod : a ≡ b [MOD p] := (hU a ha).trans (hU b hb).symm
  have hdvd : p ∣ b-a := (Nat.modEq_iff_dvd' hab.le).mp habmod
  have hxydiv : p ∣ y-x := by rwa [heab,← hexy] at hdvd
  have hmod : x ≡ y [MOD p] := (Nat.modEq_iff_dvd' hxy.le).mpr hxydiv
  have h := hV hx hy hmod
  omega

/-- Positive affine-square differences can be separated by a modulus private
to one fiber. Other fibers must then have injective square residues modulo it. -/
theorem separate_affine_fibers (q r s p c : ℕ) (A B : Finset ℕ)
    (hA : ∀ a ∈ A, a ≡ c [MOD p])
    (hB : Set.InjOn (fun b : ℕ => ((q*b+s)^2)%p) (B : Set ℕ)) :
    Disjoint (positiveDiffs (fiberValues q r A))
      (positiveDiffs (fiberValues q s B)) := by
  apply separate_by_modulus p ((q*c+r)^2)
  · intro a ha
    obtain ⟨k,hk,rfl⟩ := mem_image.mp ha
    exact Nat.ModEq.pow 2 (Nat.ModEq.add_right r (Nat.ModEq.mul_left q (hA k hk)))
  · intro a ha b hb he
    obtain ⟨k,hk,rfl⟩ := mem_image.mp ha
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hb
    have h := hB hk hl he
    simp [h]

/-- A valid Sidon union construction, assuming each chosen fiber is Sidon.
The private moduli are one sufficient way, not a necessary way, to make the
actual difference sets compatible. -/
theorem private_moduli_sidon_union (q : ℕ) (R : Finset ℕ)
    (B : ℕ → Finset ℕ) (P C : ℕ → ℕ) (hM : PairMatching q R)
    (hSidon : ∀ r ∈ R, IsSidon (fiberValues q r (B r) : Set ℕ))
    (hclass : ∀ r ∈ R, ∀ k ∈ B r, k ≡ C r [MOD P r])
    (hinj : ∀ r ∈ R, ∀ s ∈ R, r ≠ s →
      Set.InjOn (fun k : ℕ => ((q*k+s)^2)%(P r)) (B s : Set ℕ)) :
    IsSidon ((R.biUnion (fun r => fiberValues q r (B r)) : Finset ℕ) : Set ℕ) := by
  apply (partial_square_iff q R B hM).mpr
  refine ⟨hSidon,?_⟩
  intro r hr s hs hrs
  exact separate_affine_fibers q r s (P r) (C r) (B r) (B s)
    (hclass r hr) (hinj r hr s hs hrs)

/-- A residue class contains at most H/p+1 selected indices in [0,H]. -/
theorem residue_class_card (p c H : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Icc 0 H) (hmod : ∀ a ∈ A, a ≡ c [MOD p]) :
    A.card ≤ H/p+1 := by
  have hc : A.card ≤ (range (H/p+1)).card := by
    apply card_le_card_of_injOn (fun a : ℕ => a/p)
    · intro a ha
      have hh := Nat.div_le_div_right (mem_Icc.mp (hA ha)).2 (c := p)
      apply mem_range.mpr
      change a/p < H/p+1
      omega
    · intro a ha b hb he
      change a/p=b/p at he
      have hrem : a%p=b%p := (hmod a ha).trans (hmod b hb).symm
      calc
        a = a%p+p*(a/p) := (Nat.mod_add_div a p).symm
        _ = b%p+p*(b/p) := by rw [hrem,he]
        _ = b := Nat.mod_add_div b p
  simpa using hc

/-- The second half of the selector has at most p indices. -/
theorem injective_square_residue_card (q r p : ℕ) (B : Finset ℕ) (hp : 0 < p)
    (hB : Set.InjOn (fun b : ℕ => ((q*b+r)^2)%p) (B : Set ℕ)) :
    B.card ≤ p := by
  have hc : B.card ≤ (range p).card := by
    apply card_le_card_of_injOn (fun b : ℕ => ((q*b+r)^2)%p)
    · intro b hb
      exact mem_range.mpr (Nat.mod_lt _ hp)
    · exact hB
  simpa using hc

/-- The actual root-index cardinality cost, not a bound on the number of
modular collision types. In particular, two large fibers cannot both be kept
near the full index length by this private-modulus selector. -/
theorem private_modulus_card_cost (q s p c H : ℕ) (A B : Finset ℕ) (hp : 0 < p)
    (hA : A ⊆ Icc 0 H) (hmod : ∀ a ∈ A, a ≡ c [MOD p])
    (hB : Set.InjOn (fun b : ℕ => ((q*b+s)^2)%p) (B : Set ℕ)) :
    (A.card-1)*B.card ≤ H := by
  have hAc := residue_class_card p c H A hA hmod
  have hBc := injective_square_residue_card q s p B hp hB
  have hAc' : A.card-1 ≤ H/p := by
    simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right hAc 1
  calc
    _ ≤ (H/p)*p := Nat.mul_le_mul hAc' hBc
    _ ≤ H := Nat.div_mul_le_self H p

private lemma square_bound (n H : ℕ) (h : (n-1)*n ≤ H) : n^2 ≤ 2*H+1 := by
  by_cases hn : n=0
  · simp [hn]
  · have hs : n-1+1=n := Nat.sub_add_cancel (by omega)
    nlinarith only [h,hs,Nat.zero_le ((n-1)^2)]

/-- Abstract packing cost: under modular pair matching, the private-modulus
pairwise cardinality inequalities leave at most O(sqrt(qH)) indices outside
one largest fiber. There is no restriction asserted on that largest fiber. -/
theorem capacity_tail_bound (q H : ℕ) (R : Finset ℕ) (m : ℕ → ℕ)
    (hq : 0 < q) (hR : R.Nonempty) (hM : PairMatching q R)
    (hcost : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → (m r-1)*m s ≤ H) :
    ∃ r₀ ∈ R, (∀ s ∈ R, m s ≤ m r₀) ∧
      (∑ s ∈ R.erase r₀, m s)^2 ≤ 4*q*(H+1) := by
  obtain ⟨r₀,hr₀,hmax⟩ := exists_max_image R m hR
  refine ⟨r₀,hr₀,hmax,?_⟩
  have hsmall : ∀ s ∈ R.erase r₀, (m s)^2 ≤ 2*H+1 := by
    intro s hs
    obtain ⟨hsne,hsR⟩ := mem_erase.mp hs
    have hm := hmax s hsR
    apply square_bound
    calc
      _ ≤ (m r₀-1)*m s := Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hm 1)
      _ ≤ H := hcost r₀ hr₀ s hsR hsne.symm
  have hsum : (∑ s ∈ R.erase r₀, (m s)^2) ≤ (R.erase r₀).card*(2*H+1) := by
    calc
      _ ≤ ∑ _s ∈ R.erase r₀, (2*H+1) := sum_le_sum hsmall
      _ = _ := by simp
  have hk : (R.erase r₀).card^2 ≤ 2*q :=
    (Nat.pow_le_pow_left (card_le_card (erase_subset r₀ R)) 2).trans
      (pairMatching_card q R hq hM)
  calc
    _ ≤ (R.erase r₀).card*(∑ s ∈ R.erase r₀, (m s)^2) := sq_sum_le_card_mul_sum_sq
    _ ≤ (R.erase r₀).card*((R.erase r₀).card*(2*H+1)) := Nat.mul_le_mul_left _ hsum
    _ = (R.erase r₀).card^2*(2*H+1) := by ring
    _ ≤ (2*q)*(2*H+1) := Nat.mul_le_mul_right _ hk
    _ ≤ 4*q*(H+1) := by nlinarith

/-- The tail bound expressed on the ACTUAL square-value union. No upper bound
on the largest selected fiber is asserted. -/
theorem capacity_union_tail (q H : ℕ) (R : Finset ℕ) (B : ℕ → Finset ℕ)
    (hq : 0 < q) (hR : R.Nonempty) (hM : PairMatching q R)
    (hcost : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ((B r).card-1)*(B s).card ≤ H) :
    ∃ r₀ ∈ R, (∀ s ∈ R, (B s).card ≤ (B r₀).card) ∧
      ((R.biUnion (fun r => fiberValues q r (B r))).card-(B r₀).card)^2 ≤
        4*q*(H+1) := by
  obtain ⟨r₀,hr₀,hmax,hbound⟩ := capacity_tail_bound q H R (fun r => (B r).card) hq hR hM hcost
  refine ⟨r₀,hr₀,hmax,?_⟩
  rw [partial_card q R B hq hM]
  have hs := sum_erase_add R (fun r => (B r).card) hr₀
  change (∑ r ∈ R.erase r₀, (B r).card)+(B r₀).card = ∑ r ∈ R, (B r).card at hs
  have he : (∑ r ∈ R, (B r).card)-(B r₀).card = ∑ r ∈ R.erase r₀, (B r).card := by omega
  rw [he]
  exact hbound

/-- Application of the cost bound to actual selected index sets and private
moduli. It does not assume that arbitrary Sidon fibers admit such moduli. -/
theorem private_modulus_tail (q H : ℕ) (R : Finset ℕ)
    (B : ℕ → Finset ℕ) (P C : ℕ → ℕ) (hq : 0 < q) (hR : R.Nonempty)
    (hM : PairMatching q R)
    (hP : ∀ r ∈ R, 0 < P r)
    (hB : ∀ r ∈ R, B r ⊆ Icc 0 H)
    (hclass : ∀ r ∈ R, ∀ k ∈ B r, k ≡ C r [MOD P r])
    (hinj : ∀ r ∈ R, ∀ s ∈ R, r ≠ s →
      Set.InjOn (fun k : ℕ => ((q*k+s)^2)%(P r)) (B s : Set ℕ)) :
    ∃ r₀ ∈ R, (∀ s ∈ R, (B s).card ≤ (B r₀).card) ∧
      (∑ s ∈ R.erase r₀, (B s).card)^2 ≤ 4*q*(H+1) := by
  apply capacity_tail_bound q H R (fun r => (B r).card) hq hR hM
  intro r hr s hs hrs
  exact private_modulus_card_cost q s (P r) (C r) H (B r) (B s) (hP r hr)
    (hB r hr) (hclass r hr) (hinj r hr s hs hrs)

#print axioms private_moduli_sidon_union
#print axioms capacity_union_tail
#print axioms separate_by_modulus
#print axioms separate_affine_fibers
#print axioms private_modulus_card_cost
#print axioms capacity_tail_bound
#print axioms private_modulus_tail
end Erdos773.PrivateModulusPacking
