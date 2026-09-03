import Submission.LocalOddSeedDensity
import Submission.APPrimeProducts

/-! A reduced arithmetic progression with uniform critical local density
exists for every exponent at least two. -/
namespace Erdos322Research.LocalAPDensity
noncomputable section
open Finset LocalPeakCounting LocalSeedDensity LocalSeedLifting LocalOddSeedDensity APPrimeProducts
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

/-- If 2K divides p-1, the prime field contains a Kth root of minus one. -/
theorem exists_power_neg_one (p K : ℕ) [Fact p.Prime] (hK : 0 < K)
    (hd : 2*K ∣ p-1) : ∃ a : ZMod p, a^K+1=0 := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hg' : orderOf g = p-1 := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hg
  let u : (ZMod p)ˣ := g^(orderOf g/(2*K))
  have hu : orderOf u=2*K := orderOf_pow_orderOf_div (by rw [hg']; have := (Fact.out : p.Prime).two_le; omega)
    (by simpa only [hg'] using hd)
  have hpow : u^(2*K)=1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hne : u^K ≠ 1 := by
    intro hh
    have hh' := orderOf_dvd_of_pow_eq_one hh
    rw [hu] at hh'
    exact Nat.not_dvd_of_pos_of_lt hK (by omega) hh'
  have hs : ((u : ZMod p)^K)^2=1 := by
    have hh := congrArg Units.val hpow
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, ← pow_mul, mul_comm K 2] using hh
  have hneg : (u : ZMod p)^K = -1 := (sq_eq_one_iff.mp hs).resolve_left
    (fun hh ↦ hne (Units.ext hh))
  exact ⟨u,by rw [hneg, neg_add_cancel]⟩

/-- The progression depends on parity: 1 modulo 2K for even K, and 2 modulo
K for odd K. Both are reduced residue classes. -/
theorem exists_progression (k : ℕ) :
    ∃ q : ℕ, ∃ _hq : NeZero q, ∃ a : ZMod q, IsUnit a ∧
      ∀ p : ℕ, primeClass a p → ∀ d : ℕ,
        (d+1)*(p^((k+2)*d+1))^(k+1) ≤
          (2*(k+2))*rootCount (k+2) (p^((k+2)*d+1)) := by
  rcases Nat.even_or_odd (k+2) with he | ho
  · refine ⟨2*(k+2),⟨by omega⟩,1,isUnit_one,?_⟩
    intro p hp d
    letI : Fact p.Prime := ⟨hp.1⟩
    have hm : p ≡ 1 [MOD 2*(k+2)] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hp.2
    have hm' : p-1 ≡ 0 [MOD 2*(k+2)] := by
      simpa using Nat.ModEq.sub_right hp.1.one_lt.le (by omega : 1 ≤ 1) hm
    have hd : 2*(k+2) ∣ p-1 := Nat.modEq_zero_iff_dvd.mp hm'
    have hcop : p.Coprime (2*(k+2)) := by
      change Nat.gcd p (2*(k+2))=1
      rw [hm.gcd_eq]
      simp
    have hpk : ¬p ∣ k+2 := by
      intro h
      exact (hp.1.coprime_iff_not_dvd.mp hcop) (dvd_mul_of_dvd_right h 2)
    obtain ⟨a,ha⟩ := exists_power_neg_one p (k+2) (by omega) hd
    exact uniform_even_local_density p k hpk he a ha d
  · refine ⟨k+2,⟨by omega⟩,2,?_,?_⟩
    · exact (ZMod.isUnit_iff_coprime 2 (k+2)).mpr (Nat.coprime_two_left.mpr ho)
    · intro p hp d
      letI : Fact p.Prime := ⟨hp.1⟩
      have hm : p ≡ 2 [MOD k+2] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hp.2
      have hm' : p-1 ≡ 1 [MOD k+2] := by
        simpa using Nat.ModEq.sub_right hp.1.one_lt.le (by omega : 1 ≤ 2) hm
      have hcop : (p-1).Coprime (k+2) := by
        change Nat.gcd (p-1) (k+2)=1
        rw [hm'.gcd_eq]
        simp
      have hpk : ¬p ∣ k+2 := by
        apply hp.1.coprime_iff_not_dvd.mp
        change Nat.gcd p (k+2)=1
        rw [hm.gcd_eq]
        exact Nat.coprime_two_left.mpr ho
      exact uniform_permutation_local_density p k hpk hcop d

end
end Erdos322Research.LocalAPDensity
