import Submission.LocalAPDensity
import Submission.LocalPowerPeaks

/-! Exact-count peaks from polynomially bounded prime sets. These bounds
reach divisor-function scale, not any fixed positive power of the target. -/
namespace Erdos322Research.LocalDivisorScaleFamily
noncomputable section
open Finset LocalPeakCounting LocalCRTConcentration LocalPowerPeaks
open APPrimeProducts LocalAPDensity
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

lemma product_density (k d : ℕ) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime)
    (hd : ∀ p ∈ S, (d+1)*(p^((k+2)*d+1))^(k+1) ≤
      (2*(k+2))*rootCount (k+2) (p^((k+2)*d+1))) :
    (d+1)^S.card*((∏ p ∈ S, p)^((k+2)*d+1))^(k+1) ≤
      (2*(k+2))^S.card*rootCount (k+2) ((∏ p ∈ S, p)^((k+2)*d+1)) := by
  induction S using Finset.induction_on with
  | empty => simp [rootCount, Roots]
  | @insert p S hnot ih =>
    have hpp : p.Prime := hp p (mem_insert_self _ _)
    have hpS : ∀ t ∈ S, t.Prime := fun t ht ↦ hp t (mem_insert_of_mem ht)
    have hpos : 0 < ∏ t ∈ S, t := prod_pos fun t ht ↦ (hpS t ht).pos
    have hcop : p.Coprime (∏ t ∈ S, t) := Nat.Coprime.prod_right fun t ht ↦ by
      apply hpp.coprime_iff_not_dvd.mpr
      intro hdiv
      have heq := (Nat.prime_dvd_prime_iff_eq hpp (hpS t ht)).mp hdiv
      exact hnot (heq ▸ ht)
    have h1 := hd p (mem_insert_self _ _)
    have h2 := ih hpS (fun t ht ↦ hd t (mem_insert_of_mem ht))
    have hh := Nat.mul_le_mul h1 h2
    rw [card_insert_of_notMem hnot, prod_insert hnot, mul_pow,
      rootCount_mul _ _ _ (pow_pos hpp.pos _) (pow_pos hpos _) (hcop.pow _ _)]
    calc
      _ = ((d+1)*(p^((k+2)*d+1))^(k+1))*
          ((d+1)^S.card*((∏ t ∈ S,t)^((k+2)*d+1))^(k+1)) := by
        rw [pow_succ, mul_pow]; ring
      _ ≤ ((2*(k+2))*rootCount (k+2) (p^((k+2)*d+1)))*
          ((2*(k+2))^S.card*rootCount (k+2) ((∏ t ∈ S,t)^((k+2)*d+1))) := hh
      _ = _ := by rw [pow_succ]; ring

/-- An explicit exponent controlling the target height. -/
def heightExponent (k : ℕ) : ℕ := 4*((k+2)*(8*(k+2))+1)*(k+2)+1

/-- Arbitrarily large r admit an exact target with more than 2^r ordered
representations and target at most r^(A*r), where A depends only on k. -/
theorem divisor_scale_family (k R : ℕ) :
    ∃ r n : ℕ, R ≤ r ∧ k+3 ≤ r ∧ 0 < n ∧
      2^r < Erdos322.representationCount (k+2) n ∧ n ≤ r^(heightExponent k*r) := by
  obtain ⟨m,hm,a,ha,hgood⟩ := exists_progression k
  letI : NeZero m := hm
  obtain ⟨S,hR,hS,hp,hB⟩ := exists_prime_set_small_product a ha (max R (k+3))
  let r := S.card
  let B := ∏ p ∈ S,p
  let C := 2*(k+2)
  let d := 8*(k+2)
  let E := (k+2)*d+1
  let q := B^E
  have hRr : R ≤ r := (le_max_left _ _).trans hR
  have hkr : k+3 ≤ r := (le_max_right _ _).trans hR
  have hrpos : 0 < r := hS
  have hrone : 1 ≤ r := by omega
  have hBpos : 0 < B := prod_pos fun p hp' ↦ (hp p hp').1.pos
  have hqpos : 0 < q := pow_pos hBpos _
  have hqp : 0 < q^(k+1) := pow_pos hqpos _
  have hCpos : 0 < C := by dsimp [C]; omega
  have hCp : 0 < C^r := pow_pos hCpos _
  have hden : k+3 ≤ 2^r := hkr.trans Nat.lt_two_pow_self.le
  have hdC : d=4*C := by dsimp [d,C]; ring
  have hsize : ((k+2)*q^(k+1)+1)*2^r < rootCount (k+2) q := by
    have hcount := product_density k d S (fun p hp' ↦ (hp p hp').1)
      (fun p hp' ↦ hgood p (hp p hp') d)
    change (d+1)^r*q^(k+1) ≤ C^r*rootCount (k+2) q at hcount
    apply Nat.lt_of_mul_lt_mul_left (a := C^r)
    calc
      C^r*(((k+2)*q^(k+1)+1)*2^r) ≤ C^r*((k+3)*q^(k+1)*2^r) := by
        gcongr
        nlinarith
      _ ≤ C^r*(2^r*q^(k+1)*2^r) := by gcongr
      _ = d^r*q^(k+1) := by
        have htwo : (2 : ℕ)^r*2^r=4^r := by rw [← mul_pow]; norm_num
        rw [hdC, mul_pow 4 C, ← htwo]
        ring
      _ < (d+1)^r*q^(k+1) := by
        apply Nat.mul_lt_mul_of_pos_right _ hqp
        exact Nat.pow_lt_pow_left (by omega) hrpos.ne'
      _ ≤ _ := hcount
  obtain ⟨n,hn,hpeak,hnq⟩ := peak_of_rootCount (k+2) q (2^r) (by omega) hqpos
    (one_le_pow₀ (by omega)) (by simpa using hsize)
  refine ⟨r,n,hRr,hkr,hn,hpeak,hnq.trans ?_⟩
  have hBB : B ≤ r^(4*r) := hB
  calc
    (k+2)*q^(k+2) ≤ r*(r^(4*r))^(E*(k+2)) := by
      dsimp only [q]
      rw [← pow_mul]
      exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hBB _)
    _ = r^(1+4*r*(E*(k+2))) := by rw [← pow_mul, ← pow_succ']; congr 1; omega
    _ ≤ r^(heightExponent k*r) := by
      apply Nat.pow_le_pow_right hrone
      dsimp [heightExponent,E,d]
      nlinarith

end
end Erdos322Research.LocalDivisorScaleFamily
