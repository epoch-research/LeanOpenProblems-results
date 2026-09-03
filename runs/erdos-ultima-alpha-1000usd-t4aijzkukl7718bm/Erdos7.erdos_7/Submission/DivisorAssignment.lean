import Submission.ArithmeticReduction

/-! Divisor reassignment of congruence classes preserves coverage. The matching
hypothesis is substantive; a saturated finite divisor set prevents repair. -/
namespace Erdos7DivisorAssignment
open scoped BigOperators
open Erdos7Reduction
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A finite resource set already occupied by one distinct source per resource
cannot also accept an extra source, even after arbitrary reassignment. -/
theorem saturated_obstruction {I A : Type*} [DecidableEq A]
    (R : Finset A) (P : I → Prop) (key f : I → A)
    (hinj : ∀ i j, P i → P j → f i=f j → i=j)
    (hbase : ∀ r ∈ R, ∃ i, P i ∧ key i=r ∧ f i ∈ R)
    (k : I) (hk : P k) (hf : f k ∈ R) (hkey : key k ∉ R) : False := by
  classical
  choose b hb using fun r : ↥R => hbase r.val r.property
  let g : ↥R → ↥R := fun r => ⟨f (b r),(hb r).2.2⟩
  have hg : Function.Injective g := by
    intro r s hrs
    have hbs := hinj (b r) (b s) (hb r).1 (hb s).1 (congrArg Subtype.val hrs)
    apply Subtype.ext
    exact (hb r).2.1.symm.trans ((congrArg key hbs).trans (hb s).2.1)
  obtain ⟨r,hr⟩ := Finite.surjective_of_injective hg ⟨f k,hf⟩
  have hbk := hinj (b r) k (hb r).1 hk (congrArg Subtype.val hr)
  apply hkey
  rw [←hbk,(hb r).2.1]
  exact r.property

/-- Enlarge each active congruence to a distinct nontrivial divisor modulus. -/
theorem cover_of_assignment {I : Type} [Fintype I]
    (n : I → ℕ) (b : I → ℤ) (P : I → Prop) (f : I → ℕ)
    (hf : ∀ k, P k → 1 < f k ∧ f k ∣ n k)
    (hi : ∀ k l, P k → P l → f k=f l → k=l)
    (N K : ℕ) (hN : 0 < N) (hodd : Odd N)
    (hdiv : ∀ k, P k → n k ∣ N) (hcard : Fintype.card I ≤ K)
    (hc : ∀ x : ℤ, ∃ k, P k ∧ (n k : ℤ) ∣ x-b k) :
    HasOddArithmeticCover N K := by
  classical
  refine ⟨hN,{k // P k},inferInstance,(fun k => f k.val),(fun k => b k.val),
    ?_,?_,?_,?_,(Fintype.card_subtype_le P).trans hcard⟩
  · intro k l hkl
    exact Subtype.ext (hi k.val l.val k.property l.property hkl)
  · intro k
    exact ⟨(hf k.val k.property).1,
      hodd.of_dvd_nat ((hf k.val k.property).2.trans (hdiv k.val k.property))⟩
  · intro x
    obtain ⟨k,hk,hx⟩ := hc x
    refine ⟨⟨k,hk⟩,?_⟩
    exact (show (f k : ℤ) ∣ (n k : ℤ) by exact_mod_cast (hf k hk).2).trans hx
  · intro k
    exact (hf k.val k.property).2.trans (hdiv k.val k.property)

/-- Hall's condition, with the unit removed from every divisor list, is a
sufficient condition for the required reassignment. -/
theorem cover_of_hall {I : Type} [Fintype I]
    (n : I → ℕ) (b : I → ℤ) (hn : ∀ k, 0 < n k)
    (N K : ℕ) (hN : 0 < N) (hodd : Odd N)
    (hdiv : ∀ k, n k ∣ N) (hcard : Fintype.card I ≤ K)
    (hc : ∀ x : ℤ, ∃ k, (n k : ℤ) ∣ x-b k)
    (hHall : ∀ s : Finset I,
      s.card ≤ (s.biUnion (fun k => (n k).divisors.erase 1)).card) :
    HasOddArithmeticCover N K := by
  classical
  obtain ⟨f,hfi,hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun k => (n k).divisors.erase 1)).mp hHall
  apply cover_of_assignment n b (fun _ => True) f _ (fun k l _ _ h => hfi h)
    N K hN hodd (fun k _ => hdiv k) hcard
    (fun x => by obtain ⟨k,hk⟩ := hc x; exact ⟨k,True.intro,hk⟩)
  intro k _
  have hh := Finset.mem_erase.mp (hf k)
  have hd := (Nat.mem_divisors.mp hh.2).1
  have hp : 0 < f k := Nat.pos_of_ne_zero (by intro h; rw [h] at hd; exact (hn k).ne' (by simpa using hd))
  exact ⟨by omega,hd⟩

#print axioms saturated_obstruction
#print axioms cover_of_assignment
#print axioms cover_of_hall
end Erdos7DivisorAssignment
