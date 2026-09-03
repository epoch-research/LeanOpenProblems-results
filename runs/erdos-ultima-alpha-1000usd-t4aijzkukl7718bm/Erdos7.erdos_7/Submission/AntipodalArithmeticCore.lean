import Submission.ThinTwoValueCore
import Submission.SymmetricPureArithmetic

/-! A necessary Boolean core on whole prime-power coordinates. This does not
assert a covering witness or an unrestricted noncoverage theorem. -/
namespace Erdos7AntipodalArithmeticCore
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

def opposite (u : ℤ) (r : Fin 2) : ℤ := if r = 0 then u else -u

def support {I J : Type*} [Fintype I] (e : J → I → ℕ) (j : J) : Finset I :=
  Finset.univ.filter (fun i => e j i ≠ 0)

lemma mem_support {I J : Type*} [Fintype I] (e : J → I → ℕ) (j : J) (i : I) :
    i ∈ support e j ↔ e j i ≠ 0 := by simp [support]

lemma opposite_thin (p e : ℕ) (hp : Odd p) (he : 0 < e) (u a : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (r s : Fin 2)
    (hr : ((p^e : ℕ) : ℤ) ∣ opposite u r-a)
    (hs : ((p^e : ℕ) : ℤ) ∣ opposite u s-a) : r = s := by
  have hpd : (p : ℤ) ∣ ((p^e : ℕ) : ℤ) := by
    exact_mod_cast dvd_pow_self p (Nat.ne_of_gt he)
  have hn : ¬ (((p^e : ℕ) : ℤ) ∣ u-a ∧ ((p^e : ℕ) : ℤ) ∣ -u-a) := by
    rintro ⟨h₁, h₂⟩
    apply hu
    have ht : (p : ℤ) ∣ 2*u := by
      convert dvd_sub (hpd.trans h₁) (hpd.trans h₂) using 1 <;> ring
    have hc : IsCoprime (p : ℤ) (2 : ℤ) := (Nat.coprime_two_right.mpr hp).isCoprime
    exact hc.dvd_of_dvd_mul_left ht
  fin_cases r <;> fin_cases s <;> norm_num [opposite] at hr hs ⊢
  · exact hn ⟨hr, hs⟩
  · exact hn ⟨hs, hr⟩

/-- Restrict each whole prime-power coordinate to opposite units. Each active
arithmetic class becomes one atomic Boolean box on its prime support. -/
theorem exists_core {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (p E : I → ℕ) (hp : ∀ i, 0 < p i) (hodd : ∀ i, Odd (p i))
    (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : J → I → ℕ) (he : ∀ j i, e j i ≤ E i) (a : J → ℤ)
    (hc : ∀ x : ℤ, ∃ j, ((∏ i, p i^e j i : ℕ) : ℤ) ∣ x-a j)
    (u : I → ℤ) (hu : ∀ i, ¬ (p i : ℤ) ∣ u i) :
    ∃ s : Finset J,
      (∀ v : I → Fin 2, ∃ j ∈ s, ∀ i ∈ support e j,
        ((p i^e j i : ℕ) : ℤ) ∣ opposite (u i) (v i)-a j) ∧
      (s.biUnion (support e)).card < s.card ∧
      (∀ j ∈ s, ∀ i ∈ support e j, ∃ r : Fin 2,
        ((p i^e j i : ℕ) : ℤ) ∣ opposite (u i) r-a j) ∧
      (∀ i ∈ s.biUnion (support e), ∀ r : Fin 2, ∃ j ∈ s,
        i ∈ support e j ∧ ((p i^e j i : ℕ) : ℤ) ∣ opposite (u i) r-a j) := by
  classical
  letI (i : I) : NeZero (p i) := ⟨Nat.ne_of_gt (hp i)⟩
  let B (j : J) (i : I) : Set ℤ := {x | ((p i^e j i : ℕ) : ℤ) ∣ x-a j}
  have hbox : ∀ x : I → ℤ, ∃ j, ∀ i ∈ support e j, x i ∈ B j i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i : ZMod (p i^E i)).val)
      (fun i => p i^E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ k _ hik => (hcop hik).pow _ _)
    have hz (i : I) : ((p i^E i : ℕ) : ℤ) ∣ (z.val : ℤ)-x i := by
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (z.val : ℤ) (p i^E i)).mp
      have hh : (z.val : ZMod (p i^E i)) = x i := by
        rw [← ZMod.natCast_zmod_val (x i : ZMod (p i^E i))]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
      simpa only [Int.cast_natCast] using hh.symm
    obtain ⟨j, hj⟩ := hc (z.val : ℤ)
    refine ⟨j, ?_⟩
    intro i _
    have hi : p i^e j i ∣ ∏ k, p k^e j k :=
      Finset.dvd_prod_of_mem (fun k => p k^e j k) (Finset.mem_univ i)
    have hi' : ((p i^e j i : ℕ) : ℤ) ∣ ((∏ k, p k^e j k : ℕ) : ℤ) := by
      exact_mod_cast hi
    have hE : ((p i^e j i : ℕ) : ℤ) ∣ ((p i^E i : ℕ) : ℤ) := by
      exact_mod_cast pow_dvd_pow (p i) (he j i)
    change ((p i^e j i : ℕ) : ℤ) ∣ x i-a j
    convert dvd_sub (hi'.trans hj) (hE.trans (hz i)) using 1 <;> ring
  exact Erdos7ThinTwoValueCore.exists_thin_two_value_core (fun _ : I => ℤ)
    (support e) B hbox (fun i => opposite (u i))
    (fun j i hi r s hr hs => opposite_thin (p i) (e j i) (hodd i)
      (Nat.pos_of_ne_zero ((mem_support e j i).mp hi)) (u i) (a j) (hu i) r s hr hs)


/-- Choose whole-coordinate opposite pairs that miss every pure class. Only
uniqueness of the exponent patterns and normalization of prime classes are used.
Higher pure classes may be absent; they are padded by arbitrary residues. -/
theorem exists_units_avoid_pure {I J : Type*} [Fintype I] [DecidableEq I]
    (p E : I → ℕ) (hp : ∀ i, 3 ≤ p i)
    (e : J → I → ℕ) (he : ∀ j i, e j i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ j, ∃ i, e j i ≠ 0) (a : J → ℤ)
    (hprime : ∀ j i, e j i = 1 → (∀ k, k ≠ i → e j k = 0) → (p i : ℤ) ∣ a j) :
    ∃ u : I → ℤ, (∀ i, ¬ (p i : ℤ) ∣ u i) ∧
      ∀ j, (support e j).card ≤ 1 → ∃ i ∈ support e j,
        ∀ r : Fin 2, ¬ ((p i^e j i : ℕ) : ℤ) ∣ opposite (u i) r-a j := by
  classical
  letI (i : I) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let P (i : I) (t : ℕ) (j : J) := e j i = t ∧ ∀ k, k ≠ i → e j k = 0
  let R (i : I) (t : ℕ) : ℤ := if h : ∃ j, P i t j then a (Classical.choose h) else 0
  have hR (j : J) (i : I) (hother : ∀ k, k ≠ i → e j k = 0) :
      R i (e j i) = a j := by
    have hex : ∃ k, P i (e j i) k := ⟨j, rfl, hother⟩
    have hch := Classical.choose_spec hex
    have heq : Classical.choose hex = j := by
      apply hei
      funext k
      by_cases hk : k = i
      · subst k
        exact hch.1
      · exact (hch.2 k hk).trans (hother k hk).symm
    simp only [R, dif_pos hex, heq]
  have hex (i : I) := Erdos7SymmetricPureArithmetic.exists_unit_opposite_pair
    (p i) (E i+1) (hp i) (by omega) (R i)
  choose u hu using hex
  refine ⟨u, fun i => (hu i).1, ?_⟩
  intro j hj
  obtain ⟨i, hi⟩ := he0 j
  have him : i ∈ support e j := (mem_support e j i).mpr hi
  have hother : ∀ k, k ≠ i → e j k = 0 := by
    intro k hki
    by_contra hk
    exact hki ((Finset.card_le_one.mp hj) k ((mem_support e j k).mpr hk) i him)
  refine ⟨i, him, ?_⟩
  have hboth : ¬ ((p i^e j i : ℕ) : ℤ) ∣ u i-a j ∧
      ¬ ((p i^e j i : ℕ) : ℤ) ∣ -u i-a j := by
    by_cases he1 : e j i = 1
    · have ha := hprime j i he1 hother
      simp only [he1, pow_one]
      constructor
      · intro hd
        apply (hu i).1
        convert dvd_add hd ha using 1 <;> ring
      · intro hd
        apply (hu i).1
        have hh : (p i : ℤ) ∣ -u i := by
          convert dvd_add hd ha using 1 <;> ring
        exact dvd_neg.mp hh
    · have he2 : 2 ≤ e j i := by omega
      have hh := (hu i).2 (e j i) he2 (by have := he j i; omega)
      rwa [hR j i hother] at hh
  intro r
  by_cases hr : r = 0
  · simpa only [opposite, if_pos hr] using hboth.1
  · simpa only [opposite, if_neg hr] using hboth.2

/-- Every normalized strict odd arithmetic cover has an antipodal restriction
with no unary boxes and a Boolean covering core. The deficiency counts whole
prime coordinates, not their digits. Distinct supports in this Boolean core
are NOT asserted: different exponents can have the same prime support. -/
theorem exists_nonunary_core {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (p E : I → ℕ) (hp : ∀ i, 3 ≤ p i) (hodd : ∀ i, Odd (p i))
    (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : J → I → ℕ) (he : ∀ j i, e j i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ j, ∃ i, e j i ≠ 0) (a : J → ℤ)
    (hprime : ∀ j i, e j i = 1 → (∀ k, k ≠ i → e j k = 0) → (p i : ℤ) ∣ a j)
    (hc : ∀ x : ℤ, ∃ j, ((∏ i, p i^e j i : ℕ) : ℤ) ∣ x-a j) :
    ∃ (u : I → ℤ) (s : Finset J),
      (∀ i, ¬ (p i : ℤ) ∣ u i) ∧
      (∀ v : I → Fin 2, ∃ j ∈ s, ∀ i ∈ support e j,
        ((p i^e j i : ℕ) : ℤ) ∣ opposite (u i) (v i)-a j) ∧
      (s.biUnion (support e)).card < s.card ∧
      (∀ j ∈ s, 2 ≤ (support e j).card) ∧
      (∀ i ∈ s.biUnion (support e), ∀ r : Fin 2, ∃ j ∈ s,
        i ∈ support e j ∧ ((p i^e j i : ℕ) : ℤ) ∣ opposite (u i) r-a j) := by
  obtain ⟨u, hu, hpure⟩ := exists_units_avoid_pure p E hp e he hei he0 a hprime
  obtain ⟨s, hcover, hcard, hactive, hbalanced⟩ := exists_core p E
    (fun i => by have := hp i; omega) hodd hcop e he a hc u hu
  refine ⟨u, s, hu, hcover, hcard, ?_, hbalanced⟩
  intro j hj
  by_contra hn
  obtain ⟨i, hi, hmiss⟩ := hpure j (by omega)
  obtain ⟨r, hr⟩ := hactive j hj i hi
  exact hmiss r hr

#print axioms opposite_thin
#print axioms exists_core
#print axioms exists_units_avoid_pure
#print axioms exists_nonunary_core
end Erdos7AntipodalArithmeticCore
