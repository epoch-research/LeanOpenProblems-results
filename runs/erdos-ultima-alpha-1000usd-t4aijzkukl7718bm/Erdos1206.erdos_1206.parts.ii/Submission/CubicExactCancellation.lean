import Submission.CubicCancellationTables

/-! Exact cancellation formula for primitive integral cubic certificates.
This does not provide the missing global density estimate. -/

namespace Erdos1206.CubicBaseLocus

private lemma primitive_residues {a b t : ℤ} {p m : ℕ} [NeZero m]
    (hp : p.Prime) (hpm : p ∣ m)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1) :
    ¬ ((a : ZMod m).val % p = 0 ∧ (b : ZMod m).val % p = 0 ∧
      (t : ZMod m).val % p = 0) := by
  simp only [val_mod_iff_dvd hpm]
  exact triple_primitive_at_prime hprim hp

private lemma val_mod_eq_iff {m d n : ℕ} [NeZero m] (hd : d ∣ m) (a : ℤ) :
    (a : ZMod m).val % d = n ↔ a % (d : ℤ) = (n : ℤ) := by
  rw [← val_mod_eq_int_mod hd a]
  exact Int.natCast_inj.symm

private lemma extraTwo_residue (a b t : ℤ) :
    (if (a : ZMod 16).val % 2 = 1 ∧ (b : ZMod 16).val % 2 = 0 ∧
      (t : ZMod 16).val % 2 = 1 then 1 else 0) = extraTwo a b t := by
  simp only [extraTwo,val_mod_eq_iff (by norm_num : 2 ∣ 16)]
  norm_num

private lemma extraThree_residue (a b t : ℤ) :
    (if (t : ZMod 27).val % 3 = 0 ∧ (b : ZMod 27).val % 3 ≠ 0 then 1 else 0) =
      extraThree a b t := by
  simp only [extraThree,ne_eq,val_mod_eq_iff (by norm_num : 3 ∣ 27)]
  norm_num

private lemma certificate_shift_of_table {a b t g : ℤ} {x y z w : ℕ}
    (ht : 0 < t) (hg : 0 < g)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hpRoots : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w)
    {p K : ℕ} (hp : p.Prime) (hK : 0 < K)
    (r : ZMod (p^K) → ZMod (p^K) → ZMod (p^K) → ℕ) (e : ℕ)
    (hr : r (a : ZMod (p^K)) b t = e)
    (htable : ∀ a b t : ZMod (p^K),
      ¬ (a.val % p = 0 ∧ b.val % p = 0 ∧ t.val % p = 0) →
      ∀ k : Fin (K+1), commonResidueDivisibility a b t (p^k.val) ↔
        locusResidueDivisibility a b t (p^(k.val-r a b t)))
    (hbound : g.natAbs.factorization p < K) :
    g.natAbs.factorization p = (locusLcm a b t).factorization p + e := by
  letI : NeZero (p^K) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpK : p ∣ p^K := dvd_pow_self _ hK.ne'
  have hres := primitive_residues hp hpK hprim
  have hg0 : g.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hg.ne'
  have hL0 : locusLcm a b t ≠ 0 := (locusLcm_pos ht).ne'
  have heq (k : ℕ) (hk : k ≤ K) :
      k ≤ g.natAbs.factorization p ↔ k ≤ (locusLcm a b t).factorization p + e := by
    have hh := htable (a : ZMod (p^K)) b t hres ⟨k,by omega⟩
    change commonResidueDivisibility (a : ZMod (p^K)) b t (p^k) ↔
      locusResidueDivisibility (a : ZMod (p^K)) b t (p^(k-r (a : ZMod (p^K)) b t)) at hh
    rw [hr,commonResidueDivisibility_iff (Nat.pow_dvd_pow p hk),
      certificate_common_divisibility hpRoots hA hB hC hD] at hh
    rw [locusResidueDivisibility_iff (Nat.pow_dvd_pow p ((Nat.sub_le k e).trans hk))] at hh
    simp only [Nat.cast_pow] at hh
    rw [← pow_dvd_locusLcm_iff ht hp (k-e),
      hp.pow_dvd_iff_le_factorization hg0,hp.pow_dvd_iff_le_factorization hL0,
      Nat.sub_le_iff_le_add] at hh
    exact hh
  have hright : (locusLcm a b t).factorization p + e < K := by
    have hh := heq K le_rfl
    omega
  exact Nat.le_antisymm ((heq _ hbound.le).mp le_rfl) ((heq _ hright.le).mpr le_rfl)

lemma certificate_two_factorization {a b t g : ℤ} {x y z w : ℕ}
    (ht : 0 < t) (hg : 0 < g)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hpRoots : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w) :
    g.natAbs.factorization 2 = (locusLcm a b t).factorization 2 + extraTwo a b t := by
  have hbound : g.natAbs.factorization 2 < 4 := by
    have hh := (certificate_small_prime_bounds hprim hA hB hC hD).1
    have hh' : ¬ 2^4 ∣ g.natAbs := by
      intro hd
      exact hh (by simpa using Int.natCast_dvd.mpr hd)
    rw [(by norm_num : Nat.Prime 2).pow_dvd_iff_le_factorization
      (Int.natAbs_ne_zero.mpr hg.ne')] at hh'
    omega
  exact certificate_shift_of_table ht hg hprim hpRoots hA hB hC hD
    (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4)
    (fun a b t => if a.val%2=1 ∧ b.val%2=0 ∧ t.val%2=1 then 1 else 0)
    (extraTwo a b t) (extraTwo_residue a b t) two_table hbound

lemma certificate_three_factorization {a b t g : ℤ} {x y z w : ℕ}
    (ht : 0 < t) (hg : 0 < g)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hpRoots : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w) :
    g.natAbs.factorization 3 = (locusLcm a b t).factorization 3 + extraThree a b t := by
  have hbound : g.natAbs.factorization 3 < 3 := by
    have hh := (certificate_small_prime_bounds hprim hA hB hC hD).2
    have hh' : ¬ 3^3 ∣ g.natAbs := by
      intro hd
      exact hh (by simpa using Int.natCast_dvd.mpr hd)
    rw [(by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization
      (Int.natAbs_ne_zero.mpr hg.ne')] at hh'
    omega
  exact certificate_shift_of_table ht hg hprim hpRoots hA hB hC hD
    (by norm_num : Nat.Prime 3) (by norm_num : 0 < 3)
    (fun a b t => if t.val%3=0 ∧ b.val%3≠0 then 1 else 0)
    (extraThree a b t) (extraThree_residue a b t) three_table hbound

lemma certificate_other_factorization {a b t g : ℤ} {x y z w : ℕ}
    (ht : 0 < t) (hg : 0 < g)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hpRoots : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    g.natAbs.factorization p = (locusLcm a b t).factorization p := by
  have heq (k : ℕ) : k ≤ g.natAbs.factorization p ↔ k ≤ (locusLcm a b t).factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hg.ne'),
      ← hp.pow_dvd_iff_le_factorization (locusLcm_pos ht).ne',
      ← Int.natCast_dvd,Nat.cast_pow,
      certificate_prime_power_iff hprim hpRoots hA hB hC hD hp hp2 hp3 k,
      pow_dvd_locusLcm_iff ht hp]
  exact Nat.le_antisymm ((heq _).mp le_rfl) ((heq _).mpr le_rfl)

/-- The cancellation factor is the lcm of the three locus divisors, times
one of `1,2,3,6`, with the extra factors determined by the displayed residues. -/
theorem certificate_cancellation_exact {a b t g : ℤ} {x y z w : ℕ}
    (ht : 0 < t) (hg : 0 < g)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hpRoots : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w) :
    g.natAbs = 2^(extraTwo a b t)*3^(extraThree a b t)*locusLcm a b t := by
  have hL : locusLcm a b t ≠ 0 := (locusLcm_pos ht).ne'
  apply Nat.eq_of_factorization_eq (Int.natAbs_ne_zero.mpr hg.ne') (by positivity)
  intro p
  rw [Nat.factorization_mul (by positivity) hL,
    Nat.factorization_mul (by positivity) (by positivity),Nat.factorization_pow,Nat.factorization_pow]
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  by_cases hp2 : p = 2
  · subst p
    have hh := certificate_two_factorization ht hg hprim hpRoots hA hB hC hD
    norm_num at ⊢
    omega
  by_cases hp3 : p = 3
  · subst p
    have hh := certificate_three_factorization ht hg hprim hpRoots hA hB hC hD
    norm_num at ⊢
    omega
  have h2 : Nat.factorization 2 p = 0 := by
    rw [Nat.Prime.factorization (by norm_num : Nat.Prime 2),Finsupp.single_apply]
    simp [Ne.symm hp2]
  have h3 : Nat.factorization 3 p = 0 := by
    rw [Nat.Prime.factorization (by norm_num : Nat.Prime 3),Finsupp.single_apply]
    simp [Ne.symm hp3]
  simp only [h2,h3,mul_zero,zero_add]
  by_cases hp : p.Prime
  · exact certificate_other_factorization ht hg hprim hpRoots hA hB hC hD hp hp2 hp3
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]

#print axioms certificate_two_factorization
#print axioms certificate_three_factorization
#print axioms certificate_cancellation_exact

end Erdos1206.CubicBaseLocus
