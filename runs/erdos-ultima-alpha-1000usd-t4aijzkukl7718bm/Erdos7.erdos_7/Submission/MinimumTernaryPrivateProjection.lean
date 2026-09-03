import Submission.CommonPrimeExceptionCompression
import Submission.MinimumTernaryPrivate
import Submission.PurePowerPrivatePeriod

/-! In a globally minimum-cardinality hypothetical odd cover, the private
points of its modulus-three class have a large projection modulo every prime
larger than three. This is a necessary condition, not a nonexistence proof. -/
namespace Erdos7MinimumTernaryPrivateProjection
open Erdos7Reduction Erdos7PrivateReplacement Erdos7MinimumTernaryClass
open Erdos7CommonPrimeExceptionCompression
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- If all private points project into `S`, at least `p-2` residues are needed.
Global minimality is essential: the compression may change the period. -/
theorem private_projection_large {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K)
    (i : I) (hi : m i = 3)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (S : Finset (ZMod p))
    (hS : ∀ x : ℤ, Private m a i x → (x : ZMod p) ∈ S) :
    p-2 ≤ S.card := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hn
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpno3 : ¬ 3 ∣ p := by
    intro hh
    rcases (Nat.dvd_prime hp).mp hh with hh | hh <;> omega
  let B := {k : I // ¬ 3 ∣ m k}
  obtain ⟨b,hb⟩ := restrict_base m a (a i)
  choose c hc' using fun r : S =>
    affine_residue p hpno3 (r.val.val : ℤ) (a i)
  have hnear : ∀ y : ℤ, (∃ k : B, (m k : ℤ) ∣ y-b k) ∨
      ∃ r : S, (p : ℤ) ∣ y-c r := by
    intro y
    by_cases hbase : ∃ k : B, (m k : ℤ) ∣ y-b k
    · exact Or.inl hbase
    · right
      let x : ℤ := 3*y+a i
      have hxi : (m i : ℤ) ∣ x-a i := by simp [x,hi]
      have hpriv : Private m a i x := by
        refine ⟨hxi,?_⟩
        intro k hki hk
        by_cases hk3 : 3 ∣ m k
        · exact Erdos7PurePowerPrivatePeriod.disjoint_of_dvd m a
            (global_minimum_private m a hc hmin) hki
            (by simpa only [hi] using hk3) x hxi hk
        · exact hbase ⟨⟨k,hk3⟩,hb ⟨k,hk3⟩ y hk⟩
      let r : S := ⟨(x : ZMod p),hS x hpriv⟩
      refine ⟨r,hc' r y ?_⟩
      change (p : ℤ) ∣ x-(r.val.val : ℤ)
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (r.val.val : ℤ) x p).mp
      simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using
        (show r.val = (x : ZMod p) from rfl)
  have hgap : 3 + Fintype.card ↥S ≤ p := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨n,c',hcov⟩ := odd_cover_from_common_prime_exceptions
    (fun k : B => m k) b (hc.1.comp Subtype.val_injective)
    (fun k => hc.2.1 k) (fun k => k.property)
    (fun _ : S => p) c (fun _ => show 1 < p ∧ Odd p from ⟨by omega,hpodd⟩)
    (fun _ => hpno3) p ⟨hp,hpodd,hp3⟩ (fun _ => dvd_rfl) hgap hnear
  obtain ⟨N,hN⟩ := has_period n c' hcov
  have hle : Fintype.card I ≤ Fintype.card B := hmin N _ hN
  have hlt : Fintype.card B < Fintype.card I :=
    Fintype.card_subtype_lt (x := i) (by simp [hi])
  omega

/-- In particular, two residues modulo a prime at least five cannot contain
all private points of the ternary class. -/
theorem private_escapes_two_residues {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K)
    (i : I) (hi : m i = 3)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) (r s : ZMod p) :
    ∃ x : ℤ, Private m a i x ∧ (x : ZMod p) ≠ r ∧ (x : ZMod p) ≠ s := by
  classical
  by_contra hn
  have hS : ∀ x : ℤ, Private m a i x → (x : ZMod p) ∈ ({r,s} : Finset (ZMod p)) := by
    intro x hx
    by_contra hh
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hh
    exact hn ⟨x,hx,hh.1,hh.2⟩
  have hh := private_projection_large m a hc hmin i hi p hp hp3 {r,s} hS
  have hcard : ({r,s} : Finset (ZMod p)).card ≤ 2 := by
    calc
      ({r,s} : Finset (ZMod p)).card ≤ ({s} : Finset (ZMod p)).card+1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  have hne4 : p ≠ 4 := by intro he; subst p; norm_num at hp
  omega

#print axioms private_projection_large
#print axioms private_escapes_two_residues
end Erdos7MinimumTernaryPrivateProjection
