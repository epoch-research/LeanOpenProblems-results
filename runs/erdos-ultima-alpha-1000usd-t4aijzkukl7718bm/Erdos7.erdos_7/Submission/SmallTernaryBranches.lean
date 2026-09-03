import Submission.MultipleExceptionCompression
import Submission.MinimumTernaryClass

/-!
# Small ternary branches cannot occur in a global minimum odd cover

Two exceptional odd classes can be removed even when their moduli have a
factor 3: first avoid their coarse ternary residues, then compress the
remaining no-3 exceptions. This gives a conditional branch-size bound.
-/
namespace Erdos7SmallTernaryBranches
open Erdos7Reduction Erdos7MultipleExceptionCompression Erdos7MinimumTernaryClass
set_option maxHeartbeats 4000000

/-- At most two prescribed integer residues leave a ternary residue free. -/
lemma free_ternary_residue {J : Type*} [Fintype J] (b : J → ℤ)
    (hJ : Fintype.card J ≤ 2) :
    ∃ r : ℤ, ∀ j, ¬ (3 : ℤ) ∣ b j-r := by
  classical
  let S : Finset (ZMod 3) := Finset.univ.image (fun j => (b j : ZMod 3))
  have hcard : S.card < Fintype.card (ZMod 3) := by
    have hs : S.card ≤ Fintype.card J := Finset.card_image_le.trans_eq Finset.card_univ
    rw [ZMod.card]
    omega
  have hex : ∃ r : ZMod 3, r ∉ S := by
    by_contra! hn
    have he : S=Finset.univ := Finset.eq_univ_iff_forall.mpr hn
    rw [he,Finset.card_univ] at hcard
    omega
  obtain ⟨r,hr⟩ := hex
  refine ⟨r.val,fun j hj => ?_⟩
  have he := (ZMod.intCast_eq_intCast_iff_dvd_sub (r.val : ℤ) (b j) 3).mpr hj
  apply hr
  apply Finset.mem_image.mpr
  refine ⟨j,Finset.mem_univ _,?_⟩
  simpa using he.symm

/-- At most two arbitrary nontrivial odd exceptions over a distinct no-3 base
can be removed, leaving a strict odd arithmetic cover on the base index type. -/
theorem odd_cover_from_two_odd_exceptions {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hJ : Fintype.card J ≤ 2)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) :
    ∃ (n : I → ℕ) (c : I → ℤ), IsOddArithmeticCover n c := by
  classical
  obtain ⟨r,hr⟩ := free_ternary_residue b hJ
  choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
  let K := {j : J // ¬ 3 ∣ d j}
  choose b' hb' using fun j : K => affine_residue (d j) j.property (b j) r
  apply odd_cover_from_two_exceptions m a' hinj hm h3 (fun j : K => d j) b'
    (fun j => hd j) (fun j => j.property) ((Fintype.card_subtype_le _).trans hJ)
  intro x
  rcases hcover (3*x+r) with ⟨i,hi⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨i,ha' i x hi⟩
  · have hj3 : ¬ 3 ∣ d j := by
      intro h
      have hz : (3 : ℤ) ∣ (d j : ℤ) := Int.natCast_dvd_natCast.mpr h
      have hh := hz.trans hj
      exact hr j (by omega)
    exact Or.inr ⟨⟨j,hj3⟩,hb' ⟨j,hj3⟩ x hj⟩

/-- Pulling an active 3-divisible class back along a ternary progression
removes exactly one factor of 3 from its modulus. -/
lemma quotient_residue (m : ℕ) (a r : ℤ) (hm : 3 ∣ m) (ha : (3 : ℤ) ∣ a-r)
    (x : ℤ) (hx : (m : ℤ) ∣ 3*x+r-a) :
    ((m/3 : ℕ) : ℤ) ∣ x-(a-r)/3 := by
  obtain ⟨t,ht⟩ := hx
  refine ⟨t,?_⟩
  have hmod : (m : ℤ) = 3*((m/3 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hm).symm
  have hres := Int.ediv_mul_cancel ha
  rw [hmod] at ht
  nlinarith

/-- Restricting a cover to a ternary residue gives the no-3 base together
with the active 3-divisible branch, each modulus divided by 3. -/
lemma restrict_ternary_branch {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) (r : ℤ) :
    ∃ b : {i // ¬ 3 ∣ m i} → ℤ,
      ∀ x : ℤ, (∃ i : {i // ¬ 3 ∣ m i}, (m i : ℤ) ∣ x-b i) ∨
        ∃ j : {j // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r},
          ((m j/3 : ℕ) : ℤ) ∣ x-(a j-r)/3 := by
  classical
  obtain ⟨b,hb⟩ := restrict_base m a r
  refine ⟨b,fun x => ?_⟩
  obtain ⟨j,hj⟩ := hc.2.2 (3*x+r)
  by_cases hj3 : 3 ∣ m j
  · have h3 : (3 : ℤ) ∣ (m j : ℤ) := Int.natCast_dvd_natCast.mpr hj3
    have hres : (3 : ℤ) ∣ a j-r := by have := h3.trans hj; omega
    exact Or.inr ⟨⟨j,hj3,hres⟩,quotient_residue (m j) (a j) r hj3 hres x hj⟩
  · exact Or.inl ⟨⟨j,hj3⟩,hb ⟨j,hj3⟩ x hj⟩

/-- A ternary branch without modulus3, in a globally minimum-cardinality odd
cover, contains at least three classes. -/
theorem minimum_ternary_branch_card {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j ≠ 3) :
    3 ≤ Fintype.card {j // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r} := by
  classical
  by_contra hsmall
  let K := {i : I // ¬ 3 ∣ m i}
  let J := {j : I // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r}
  obtain ⟨b,hb⟩ := restrict_ternary_branch m a hc r
  have hd (j : J) : 1 < m j/3 ∧ Odd (m j/3) := by
    have he : 3*(m j/3)=m j := Nat.mul_div_cancel' j.property.1
    have hm := hc.2.1 j
    have hne := hno j j.property.2
    refine ⟨by omega,hm.2.of_dvd_nat ?_⟩
    exact Nat.div_dvd_of_dvd j.property.1
  obtain ⟨n,c,hc'⟩ := odd_cover_from_two_odd_exceptions
    (fun i : K => m i) b (hc.1.comp Subtype.val_injective)
    (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : J => m j/3) (fun j => (a j-r)/3) hd (by
      simp only [J,Fintype.card_subtype] at hsmall ⊢
      omega) hb
  obtain ⟨N,hN⟩ := has_period n c hc'
  have hle : Fintype.card I ≤ Fintype.card K := hmin N _ hN
  obtain ⟨j,hj⟩ := Erdos7No23Sieve.arithmetic_exists_three m a hc
  have hlt : Fintype.card K < Fintype.card I :=
    Fintype.card_subtype_lt (x := j) (by simpa using hj)
  omega

#print axioms free_ternary_residue
#print axioms odd_cover_from_two_odd_exceptions
#print axioms restrict_ternary_branch
#print axioms minimum_ternary_branch_card
end Erdos7SmallTernaryBranches
