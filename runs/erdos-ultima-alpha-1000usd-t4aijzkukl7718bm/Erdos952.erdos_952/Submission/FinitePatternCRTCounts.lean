import Submission.FinitePatternLocalCounts

/-! Exact product counts for finite-pattern translates in a finite Gaussian
sieve. The modulus and box-counting loss remain explicit. These identities
do not assert a uniform upper bound for long actual-prime paths. -/
namespace Erdos952Investigation.FinitePatternCRTCounts
open AdmissibleRay FinitePatternAdmissibility FinitePatternLocalCounts
set_option maxHeartbeats 0

variable {τ : Type*} [Fintype τ]

def modulus (q : τ → ℕ) : ℕ := ∏ j, q j

lemma divides_modulus (q : τ → ℕ) (j : τ) : q j ∣ modulus q := by
  classical
  exact Finset.dvd_prod_of_mem q (Finset.mem_univ j)

def reduce (q : τ → ℕ) (j : τ) : ZMod (modulus q) →+* ZMod (q j) :=
  ZMod.castHom (divides_modulus q j) (ZMod (q j))

noncomputable def coordinateCRT (q : τ → ℕ)
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) :
    ZMod (modulus q) ≃+* (∀ j, ZMod (q j)) := ZMod.prodEquivPi q hc

lemma coordinateCRT_apply (q : τ → ℕ)
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (a : ZMod (modulus q)) (j : τ) : coordinateCRT q hc a j = reduce q j a := by
  obtain ⟨k,rfl⟩ := ZMod.intCast_surjective a
  simp only [map_intCast,Pi.intCast_apply]

noncomputable def residueCRT (q : τ → ℕ)
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) :
    ZMod (modulus q) × ZMod (modulus q) ≃ (∀ j, ZMod (q j) × ZMod (q j)) where
  toFun ab j := (coordinateCRT q hc ab.1 j,coordinateCRT q hc ab.2 j)
  invFun f := ((coordinateCRT q hc).symm (fun j => (f j).1),
    (coordinateCRT q hc).symm (fun j => (f j).2))
  left_inv ab := by
    apply Prod.ext <;> simp
  right_inv f := by
    funext j
    apply Prod.ext <;> simp

def GoodResidue {ι : Type*} (z : ι → GaussianInt) (q : τ → ℕ)
    (ab : ZMod (modulus q) × ZMod (modulus q)) : Prop :=
  ∀ j i, Good (q j) (reduce q j ab.1) (reduce q j ab.2) (z i)

noncomputable def periodicCount {ι : Type*} (z : ι → GaussianInt) (q : τ → ℕ) : ℕ :=
  Nat.card {ab : ZMod (modulus q) × ZMod (modulus q) // GoodResidue z q ab}

/-- CRT gives a product of the exact local counts, including projection
collisions within each local factor. -/
theorem periodicCount_eq_product {ι : Type*} (z : ι → GaussianInt) (q : τ → ℕ)
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) :
    periodicCount z q = ∏ j, localCount z (q j) := by
  let e := residueCRT q hc
  have he (ab : ZMod (modulus q) × ZMod (modulus q)) :
      GoodResidue z q ab ↔ ∀ j i, Good (q j) ((e ab j).1) ((e ab j).2) (z i) := by
    simp only [GoodResidue,e,residueCRT,Equiv.coe_fn_mk,coordinateCRT_apply]
  let ee : {ab : ZMod (modulus q) × ZMod (modulus q) // GoodResidue z q ab} ≃
      {f : ∀ j, ZMod (q j) × ZMod (q j) // ∀ j i, Good (q j) (f j).1 (f j).2 (z i)} :=
    e.subtypeEquiv he
  have hh := Nat.card_congr (ee.trans (Equiv.subtypePiEquivPi
    (p := fun j (ab : ZMod (q j) × ZMod (q j)) =>
      ∀ i, Good (q j) ab.1 ab.2 (z i))))
  simpa only [periodicCount,localCount,Nat.card_pi] using hh

lemma goodResidue_integer_iff {ι : Type*} (z : ι → GaussianInt) (q : τ → ℕ)
    (t : GaussianInt) :
    GoodResidue z q ((t.re : ZMod (modulus q)),(t.im : ZMod (modulus q))) ↔
      ∀ j i, ¬ (q j : ℤ) ∣ (t+z i).norm := by
  simp only [GoodResidue,map_intCast]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro i
  have he : (((t+z i).norm : ℤ) : ZMod (q j)) =
      (t.re+(z i).re : ZMod (q j))^2+(t.im+(z i).im : ZMod (q j))^2 := by
    simp [gaussian_norm_sq]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,he]
  rfl

/-- Passing the finite admissibility test makes every product of distinct
prime local tests nonempty. It does not produce actual prime translates. -/
theorem periodicCount_pos_of_admissible {ι : Type*} (z : ι → GaussianInt)
    (hz : FiniteAdmissible z) (q : τ → ℕ) (hq : ∀ j, (q j).Prime)
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) :
    0 < periodicCount z q := by
  rw [periodicCount_eq_product z q hc]
  apply Finset.prod_pos
  intro j _
  letI : NeZero (q j) := ⟨(hq j).ne_zero⟩
  obtain ⟨a,b,hab⟩ := hz (q j) (hq j)
  letI : Nonempty {ab : ZMod (q j) × ZMod (q j) // ∀ i, Good (q j) ab.1 ab.2 (z i)} :=
    ⟨⟨(a,b),hab⟩⟩
  exact Nat.card_pos

/-- For a collision-free family of split primes, the exact product has the
familiar squared factors. No estimate on its size relative to the modulus is
asserted here. -/
theorem periodicCount_split_product {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (hz : Function.Injective z)
    (q : τ → ℕ) (hq : ∀ j, (q j).Prime) (h2 : ∀ j, q j ≠ 2)
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (r : ∀ j, ZMod (q j)) (hr : ∀ j, (r j)^2 = -1)
    (hb : ∀ j a b, (z a-z b).norm < (q j : ℤ)) :
    periodicCount z q = ∏ j, (q j-Fintype.card ι)^2 := by
  rw [periodicCount_eq_product z q hc]
  apply Finset.prod_congr rfl
  intro j _
  exact split_local_count_of_norm_bound z hz (hq j) (h2 j) (r j) (hr j) (hb j)

#print axioms periodicCount_eq_product
#print axioms goodResidue_integer_iff
#print axioms periodicCount_pos_of_admissible
#print axioms periodicCount_split_product
end Erdos952Investigation.FinitePatternCRTCounts
