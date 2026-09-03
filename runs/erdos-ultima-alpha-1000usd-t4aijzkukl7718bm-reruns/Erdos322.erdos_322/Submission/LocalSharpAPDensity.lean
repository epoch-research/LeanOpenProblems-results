import Submission.LocalSharpSeedDensity
import Submission.LocalAPDensity

/-! Reduced progressions of large primes with nearly doubled local density. -/
namespace Erdos322Research.LocalSharpAPDensity
noncomputable section
open Finset LocalPeakCounting LocalSeedDensity LocalOddSeedDensity
open LocalCRTConcentration LocalAPDensity LocalSharpSeedDensity APPrimeProducts
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

/-- Small primes can be excluded by enlarging the progression modulus. -/
theorem exists_large_progression (k M : ℕ) :
    ∃ q : ℕ, ∃ _hq : NeZero q, ∃ a : ZMod q, IsUnit a ∧
      ∀ p : ℕ, primeClass a p →
        ¬p ∣ k+2 ∧ M*(k+2) ≤ p ∧ p^(k+1) ≤ rootCount (k+2) p := by
  let q := 2*(k+2)*(M+1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hdK : k+2 ∣ q := by dsimp [q]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hqbound : M*(k+2)+2 ≤ q := by dsimp [q]; nlinarith
  letI : NeZero q := ⟨hq.ne'⟩
  rcases Nat.even_or_odd (k+2) with he | ho
  · refine ⟨q,inferInstance,1,isUnit_one,?_⟩
    intro p hp
    letI : Fact p.Prime := ⟨hp.1⟩
    have hm : p ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hp.2
    have hd : q ∣ p-1 := Nat.modEq_zero_iff_dvd.mp (by
      simpa using Nat.ModEq.sub_right hp.1.one_lt.le (by omega : 1 ≤ 1) hm)
    have hpq : p.Coprime q := by
      change Nat.gcd p q=1
      rw [hm.gcd_eq]
      simp
    have hpk : ¬p ∣ k+2 := by
      exact hp.1.coprime_iff_not_dvd.mp (hpq.of_dvd_right hdK)
    have hqp : q ≤ p-1 := Nat.le_of_dvd (by have := hp.1.two_le; omega) hd
    have h2K : 2*(k+2) ∣ p-1 :=
      (show 2*(k+2) ∣ q from dvd_mul_right _ _).trans hd
    obtain ⟨a,ha⟩ := exists_power_neg_one p (k+2) (by omega) h2K
    refine ⟨hpk,by omega,?_⟩
    simpa only [Nat.add_sub_cancel] using even_root_count_lower (k+2) p (by omega) he a ha
  · refine ⟨q,inferInstance,-1,isUnit_one.neg,?_⟩
    intro p hp
    letI : Fact p.Prime := ⟨hp.1⟩
    have hd : q ∣ p+1 := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [Nat.cast_add,Nat.cast_one,hp.2,neg_add_cancel]
    have hpq : q ≤ p+1 := Nat.le_of_dvd (by omega) hd
    have hdKp : k+2 ∣ p+1 := hdK.trans hd
    have hpk : ¬p ∣ k+2 := by
      intro h
      have h1 : p ∣ 1 := by
        have hh := Nat.dvd_sub (h.trans hdKp) (dvd_refl p)
        simpa using hh
      exact hp.1.not_dvd_one h1
    have hcop : (p-1).Coprime (k+2) := by
      apply Nat.coprime_of_dvd'
      intro l _ hl1 hlK
      have hl2 : l ∣ 2 := by
        have hh := Nat.dvd_sub (hlK.trans hdKp) hl1
        have hh' : p+1-(p-1)=2 := by have := hp.1.two_le; omega
        rwa [hh'] at hh
      have hlone : l=1 := ((Nat.coprime_two_right.mpr ho).of_dvd_left hlK).eq_one_of_dvd hl2
      simp [hlone]
    exact ⟨hpk,by omega,permutation_root_count_lower k p hcop⟩

/-- The local factor may be chosen arbitrarily close to two. -/
theorem exists_density_progression (k M : ℕ) (hM : 1 ≤ M) :
    ∃ q : ℕ, ∃ _hq : NeZero q, ∃ a : ZMod q, IsUnit a ∧
      ∀ p : ℕ, primeClass a p →
        (2*M-1)*(p^(k+2))^(k+1) ≤ M*rootCount (k+2) (p^(k+2)) := by
  obtain ⟨q,hq,a,ha,h⟩ := exists_large_progression k M
  letI : NeZero q := hq
  refine ⟨q,hq,a,ha,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨hpk,hpM,hroot⟩ := h p hp
  exact density_at_degree k p M hpk hM hpM hroot

/-- CRT multiplies these degree-depth density gains without a prime-size loss. -/
theorem product_density (k M : ℕ) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime)
    (hd : ∀ p ∈ S, (2*M-1)*(p^(k+2))^(k+1) ≤ M*rootCount (k+2) (p^(k+2))) :
    (2*M-1)^S.card*((∏ p ∈ S,p)^(k+2))^(k+1) ≤
      M^S.card*rootCount (k+2) ((∏ p ∈ S,p)^(k+2)) := by
  induction S using Finset.induction_on with
  | empty => simp [rootCount,Roots]
  | @insert p S hnot ih =>
    have hpp : p.Prime := hp p (mem_insert_self _ _)
    have hpS : ∀ t ∈ S, t.Prime := fun t ht ↦ hp t (mem_insert_of_mem ht)
    have hpos : 0 < ∏ t ∈ S,t := prod_pos fun t ht ↦ (hpS t ht).pos
    have hcop : p.Coprime (∏ t ∈ S,t) := Nat.Coprime.prod_right fun t ht ↦ by
      apply hpp.coprime_iff_not_dvd.mpr
      intro hdiv
      have heq := (Nat.prime_dvd_prime_iff_eq hpp (hpS t ht)).mp hdiv
      exact hnot (heq ▸ ht)
    have h1 := hd p (mem_insert_self _ _)
    have h2 := ih hpS (fun t ht ↦ hd t (mem_insert_of_mem ht))
    have hh := Nat.mul_le_mul h1 h2
    rw [card_insert_of_notMem hnot,prod_insert hnot,mul_pow,
      rootCount_mul _ _ _ (pow_pos hpp.pos _) (pow_pos hpos _) (hcop.pow _ _)]
    calc
      _ = ((2*M-1)*(p^(k+2))^(k+1))*
          ((2*M-1)^S.card*((∏ t ∈ S,t)^(k+2))^(k+1)) := by
        rw [pow_succ,mul_pow]; ring
      _ ≤ (M*rootCount (k+2) (p^(k+2)))*
          (M^S.card*rootCount (k+2) ((∏ t ∈ S,t)^(k+2))) := hh
      _ = _ := by rw [pow_succ]; ring

end
end Erdos322Research.LocalSharpAPDensity
