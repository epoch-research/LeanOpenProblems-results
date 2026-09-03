import Submission.PrivateReplacement
import Submission.CompanionExchange

/-!
# Private fibers of a pure prime-power class

In an irredundant arithmetic family, private points of a class modulo `p^e`
meet every finer `p`-adic residue compatible with that class. The result does
not assume coverage or oddness. In particular it is an obstruction to, not a
justification for, a covering-preserving companion exchange.
-/

namespace Erdos7PurePowerPrivateFibers
open Erdos7PrivateReplacement

variable {I : Type*}

/-- Irredundance is expressed by an actual private point for every label. -/
def Irredundant (m : I → ℕ) (a : I → ℤ) : Prop :=
  ∀ i, ∃ x, Private m a i x

/-- Comparable classes in an irredundant family are disjoint. -/
theorem comparable_disjoint (m : I → ℕ) (a : I → ℤ)
    (h : Irredundant m a) (i j : I) (hji : j ≠ i) (hdiv : m i ∣ m j)
    (y : ℤ) (hi : (m i : ℤ) ∣ y-a i) : ¬ (m j : ℤ) ∣ y-a j := by
  intro hj
  obtain ⟨x, hx⟩ := h j
  apply hx.2 i (Ne.symm hji)
  have hd : (m i : ℤ) ∣ (m j : ℤ) := Int.natCast_dvd_natCast.mpr hdiv
  have hh := dvd_add (dvd_sub hi (hd.trans hj)) (hd.trans hx.1)
  convert hh using 1 <;> ring

/-- A period only needs to preserve the incomparable classes: comparable
upper classes cannot meet the lower class in the first place. -/
theorem private_shift (m : I → ℕ) (a : I → ℤ)
    (h : Irredundant m a) (i : I) (T : ℕ) (hiT : m i ∣ T)
    (hT : ∀ j, ¬ m i ∣ m j → m j ∣ T)
    (x : ℤ) (hx : Private m a i x) (t : ℤ) :
    Private m a i (x+(T : ℤ)*t) := by
  have hshift (j : I) (hj : m j ∣ T) : (m j : ℤ) ∣ (T : ℤ)*t :=
    (Int.natCast_dvd_natCast.mpr hj).trans (dvd_mul_right (T : ℤ) t)
  have hy : (m i : ℤ) ∣ (x+(T : ℤ)*t)-a i := by
    convert dvd_add hx.1 (hshift i hiT) using 1 <;> ring
  refine ⟨hy, ?_⟩
  intro j hji hj
  by_cases hd : m i ∣ m j
  · exact comparable_disjoint m a h i j hji hd _ hy hj
  · apply hx.2 j hji
    convert dvd_sub hj (hshift j (hT j hd)) using 1 <;> ring

/-- All divisors of `N` with smaller `p`-valuation divide the period consisting
of `p^e` times the prime-to-`p` part of `N`. -/
lemma lower_valuation_period {N p e n : ℕ} (hp : p.Prime) (hN : N ≠ 0)
    (hn : n ∣ N) (he : ¬ p^e ∣ n) : n ∣ p^e * ordCompl[p] N := by
  have hn0 : n ≠ 0 := ne_zero_of_dvd_ne_zero hN hn
  have hv : n.factorization p < e := by
    simpa only [hp.pow_dvd_iff_le_factorization hn0, not_le] using he
  have ha : ordProj[p] n ∣ p^e := pow_dvd_pow p hv.le
  have hb : ordCompl[p] n ∣ ordCompl[p] N :=
    Nat.ordCompl_dvd_ordCompl_of_dvd hn p
  simpa only [Nat.ordProj_mul_ordCompl_eq_self] using Nat.mul_dvd_mul ha hb

/-- A complete arithmetic progression of private points. Its step has exactly
`e` factors of `p`, independently of the largest `p`-power in the family. -/
theorem private_prime_power_shift (m : I → ℕ) (a : I → ℤ)
    (h : Irredundant m a) (N p e : ℕ) (hN : N ≠ 0) (hp : p.Prime)
    (hm : ∀ j, m j ∣ N) (i : I) (hi : m i = p^e)
    (x : ℤ) (hx : Private m a i x) (t : ℤ) :
    Private m a i (x+((p^e * ordCompl[p] N : ℕ) : ℤ)*t) := by
  apply private_shift m a h i (p^e * ordCompl[p] N) _ _ x hx t
  · rw [hi]
    exact dvd_mul_right _ _
  · intro j hj
    apply lower_valuation_period hp hN (hm j)
    simpa only [hi] using hj

/-- Every compatible finer `p`-adic residue contains a private point. The
reference point `x` may be any originally private point, and `f` is arbitrary. -/
theorem private_all_finer_residues (m : I → ℕ) (a : I → ℤ)
    (h : Irredundant m a) (N p e : ℕ) (hN : N ≠ 0) (hp : p.Prime)
    (hm : ∀ j, m j ∣ N) (i : I) (hi : m i = p^e)
    (x : ℤ) (hx : Private m a i x) (f : ℕ) (r : ℤ) :
    ∃ y : ℤ, Private m a i y ∧
      ((p^(e+f) : ℕ) : ℤ) ∣ y-(x+((p^e : ℕ) : ℤ)*r) := by
  have hc : Nat.Coprime (ordCompl[p] N) (p^f) :=
    (Nat.coprime_ordCompl hp hN).symm.pow_right f
  have hcz : IsCoprime ((ordCompl[p] N : ℕ) : ℤ) ((p^f : ℕ) : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using hc
  obtain ⟨u,v,huv⟩ := hcz
  refine ⟨x+((p^e * ordCompl[p] N : ℕ) : ℤ)*(u*r),
    private_prime_power_shift m a h N p e hN hp hm i hi x hx (u*r), ?_⟩
  refine ⟨-v*r, ?_⟩
  push_cast at huv ⊢
  rw [pow_add]
  nlinarith [congrArg (fun z : ℤ => (p : ℤ)^e*r*z) huv]

/-- Two private points are always separated by the next `p`-adic digit. -/
theorem private_separated_pair (m : I → ℕ) (a : I → ℤ)
    (h : Irredundant m a) (N p e : ℕ) (hN : N ≠ 0) (hp : p.Prime)
    (hm : ∀ j, m j ∣ N) (i : I) (hi : m i = p^e) :
    ∃ x y : ℤ, Private m a i x ∧ Private m a i y ∧
      ¬ ((p^(e+1) : ℕ) : ℤ) ∣ x-y := by
  obtain ⟨x,hx⟩ := h i
  let T := p^e * ordCompl[p] N
  refine ⟨x, x+(T : ℤ), hx, ?_, ?_⟩
  · simpa only [mul_one] using
      private_prime_power_shift m a h N p e hN hp hm i hi x hx 1
  · intro hf
    have ht : ((p^(e+1) : ℕ) : ℤ) ∣ (T : ℤ) := by
      convert dvd_neg.mpr hf using 1 <;> ring
    have ht' : p^(e+1) ∣ T := Int.natCast_dvd_natCast.mp ht
    have he0 : p^e ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hb : p ∣ ordCompl[p] N := by
      simpa only [T, pow_succ, Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero he0)] using ht'
    exact Nat.not_dvd_ordCompl hp hN hb

/-- No single next-level residue contains all private points of a pure
prime-power class. -/
theorem private_escape_every_fine_class (m : I → ℕ) (a : I → ℤ)
    (h : Irredundant m a) (N p e : ℕ) (hN : N ≠ 0) (hp : p.Prime)
    (hm : ∀ j, m j ∣ N) (i : I) (hi : m i = p^e) (b : ℤ) :
    ∃ x : ℤ, Private m a i x ∧ ¬ ((p^(e+1) : ℕ) : ℤ) ∣ x-b := by
  classical
  obtain ⟨x,y,hx,hy,hsep⟩ := private_separated_pair m a h N p e hN hp hm i hi
  by_cases hxb : ((p^(e+1) : ℕ) : ℤ) ∣ x-b
  · refine ⟨y,hy,fun hyb => hsep ?_⟩
    convert dvd_sub hxb hyb using 1 <;> ring
  · exact ⟨x,hx,hxb⟩

/-- Exchanging the coarse residues of a pure `p^e` class and its `p^(e+1)`
companion always leaves a hole, regardless of the chosen finer phase. This
uses the actual changed residue assignment, with the modulus labels fixed. -/
theorem every_companion_exchange_loses [DecidableEq I]
    (m : I → ℕ) (a : I → ℤ) (h : Irredundant m a)
    (N p e : ℕ) (hN : N ≠ 0) (hp : p.Prime) (hm : ∀ j, m j ∣ N)
    (i j : I) (hji : j ≠ i) (hi : m i = p^e) (hj : m j = p^(e+1)) :
    ∀ t : ℤ, ∃ x : ℤ, ∀ k,
      ¬ (m k : ℤ) ∣ x-Function.update (Function.update a i (a j)) j
        (a i+t*(m i : ℤ)) k := by
  intro t
  obtain ⟨x,hx,hfine⟩ := private_escape_every_fine_class m a h N p e hN hp hm
    i hi (a i+t*(m i : ℤ))
  have hd : m i ∣ m j := by
    rw [hi,hj,pow_succ]
    exact dvd_mul_right _ _
  have ha : ¬ (m i : ℤ) ∣ a j-a i := by
    intro ha
    exact comparable_disjoint m a h i j hji hd (a j) ha (by simp)
  refine ⟨x,fun k hk => ?_⟩
  by_cases hki : k=i
  · subst k
    have hnew : (m i : ℤ) ∣ x-a j := by simpa [Ne.symm hji] using hk
    exact Erdos7CompanionExchange.incompatible_coarse
      (m i : ℤ) (a j) (a i) ha x hx.1 hnew
  · by_cases hkj : k=j
    · subst k
      apply hfine
      simpa [hj] using hk
    · apply hx.2 k hki
      simpa [hki,hkj] using hk

#print axioms private_all_finer_residues
#print axioms private_separated_pair
#print axioms every_companion_exchange_loses

end Erdos7PurePowerPrivateFibers
