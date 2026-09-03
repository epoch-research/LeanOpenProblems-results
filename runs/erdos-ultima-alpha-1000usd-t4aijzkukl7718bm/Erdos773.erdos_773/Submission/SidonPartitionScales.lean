import Submission.SidonDifferenceGraph

/-! Explicit polynomial scales for the Sidon-seed partition estimate. These
scales apply to arbitrary integer sets, not specifically to square values. -/
namespace Erdos773.SidonPartitionScales
open Finset SidonPartitionFunction SidonDifferenceGraph
set_option maxHeartbeats 3000000
noncomputable section

def branchDegree (n : ℕ) : ℕ := 3*(n/12)*n^25
def fugacity (n : ℕ) : ℝ := 1/(4*(n:ℝ)^23)
def base (n : ℕ) : ℝ := 1+1/(n:ℝ)^25

lemma branchDegree_bound (n : ℕ) : (branchDegree n:ℝ) ≤ (n:ℝ)^26/4 := by
  have hq : (12:ℝ)*(n/12:ℕ) ≤ n := by exact_mod_cast Nat.mul_div_le n 12
  have hh := mul_le_mul_of_nonneg_right hq (pow_nonneg (Nat.cast_nonneg n: (0:ℝ) ≤ n) 25)
  dsimp [branchDegree]
  push_cast
  nlinarith only [hh]

lemma seed_dense {n : ℕ} (hn : 2 ≤ n) {T : Finset ℕ}
    (hT : IsSidon (T:Set ℕ)) (hTm : T ⊆ Icc 1 (n^40)) (hcard : T.card=n^14) :
    ∀ W ⊆ Icc 1 (n^40), n^38<W.card →
      ∃ v ∈ W, branchDegree n ≤ (neighbors (Adj T) W v).card := by
  intro W hWm hW
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  have hW0 : (0:ℝ)<W.card := by exact_mod_cast (show 0<W.card by omega)
  have hWR : (n:ℝ)^38 < W.card := by exact_mod_cast hW
  have hD := branchDegree_bound n
  have hDm := mul_le_mul_of_nonneg_right hD (pow_nonneg hn0.le 40)
  have hfour : (4:ℝ) ≤ (n:ℝ)^12 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hnR 12
    norm_num at hh
    linarith only [hh]
  have hfourm := mul_le_mul_of_nonneg_right hfour (pow_nonneg hn0.le 54)
  have hpre : 2*(n:ℝ)^40*((n:ℝ)^14+branchDegree n) ≤ ((n:ℝ)^14)^2*(n:ℝ)^38 := by
    nlinarith only [hDm,hfourm]
  have hstrict := mul_lt_mul_of_pos_left hWR (sq_pos_of_pos (pow_pos hn0 14))
  by_contra! hnothigh
  have hb := density_bound hT hTm hWm (branchDegree n:ℝ) (fun v hv => by
    exact_mod_cast (hnothigh v hv).le)
  rw [hcard] at hb
  push_cast at hb
  have hb' : (W.card:ℝ)*((W.card:ℝ)*((n:ℝ)^14)^2) ≤
      (W.card:ℝ)*(2*(n:ℝ)^40*((n:ℝ)^14+branchDegree n)) := by nlinarith only [hb]
  have hh := le_of_mul_le_mul_left hb' hW0
  nlinarith only [hh,hpre,hstrict]

lemma branching {n : ℕ} (hn : 1000 ≤ n) :
    fugacity n ≤ (base n-1)*(base n)^branchDegree n := by
  have hnR : (1000:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  have hq : (n:ℝ)/12 ≤ (n/12:ℕ)+1 := by
    have hh : (n:ℝ)<12*((n/12:ℕ)+1) := by exact_mod_cast Nat.lt_mul_div_succ n (by omega : 0<12)
    linarith only [hh]
  have hnon : (0:ℝ) ≤ 1/(n:ℝ)^25 := by positivity
  have hB := one_add_mul_le_pow (show (-2:ℝ) ≤ 1/(n:ℝ)^25 by linarith only [hnon]) (n^25*(n/12))
  have he : (1:ℝ)+(n^25*(n/12):ℕ)*(1/(n:ℝ)^25)=1+(n/12:ℕ) := by push_cast; field_simp
  rw [he] at hB
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+(n/12:ℕ)) hB 3
  have hexp : (n^25*(n/12))*3=branchDegree n := by unfold branchDegree; ring
  rw [← pow_mul,hexp] at hp
  have hq3 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ n/12) hq 3
  have hn2 := mul_nonneg (show (0:ℝ) ≤ (n:ℝ)-432 by linarith only [hnR]) (sq_nonneg (n:ℝ))
  have hpow : (n:ℝ)^2/4 ≤ (base n)^branchDegree n := by
    change (n:ℝ)^2/4 ≤ (1+1/(n:ℝ)^25)^branchDegree n
    nlinarith only [hp,hq3,hn2]
  have hc : 0 ≤ base n-1 := by unfold base; linarith only [hnon]
  have hm := mul_le_mul_of_nonneg_left hpow hc
  have hid : (base n-1)*((n:ℝ)^2/4)=fugacity n := by unfold base fugacity; field_simp; ring
  rwa [hid] at hm

lemma exponential_budget {n : ℕ} (hn : 0<n) :
    (base n)^(n^40)*(1+fugacity n)^(n^38) ≤ Real.exp ((5/4:ℝ)*(n:ℝ)^15) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hc : 0 ≤ base n := by unfold base; positivity
  have hz : 0 ≤ 1+fugacity n := by unfold fugacity; positivity
  have h₁ : base n ≤ Real.exp (1/(n:ℝ)^25) := by
    unfold base
    simpa only [add_comm] using Real.add_one_le_exp (1/(n:ℝ)^25)
  have h₂ : 1+fugacity n ≤ Real.exp (fugacity n) := by
    simpa only [add_comm] using Real.add_one_le_exp (fugacity n)
  have hp := mul_le_mul (pow_le_pow_left₀ hc h₁ (n^40)) (pow_le_pow_left₀ hz h₂ (n^38))
    (pow_nonneg hz _) (pow_nonneg (Real.exp_pos _).le _)
  rw [← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add] at hp
  have he : ((n^40:ℕ):ℝ)*(1/(n:ℝ)^25)+((n^38:ℕ):ℝ)*fugacity n=(5/4:ℝ)*(n:ℝ)^15 := by
    unfold fugacity
    push_cast
    field_simp
    ring
  rwa [he] at hp

/-- The independent-set partition function for every Sidon seed of the
specified size has a uniform explicit exponential bound. -/
theorem seed_partition_bound {n : ℕ} (hn : 1000 ≤ n) {T : Finset ℕ}
    (hT : IsSidon (T:Set ℕ)) (hTm : T ⊆ Icc 1 (n^40)) (hcard : T.card=n^14) :
    Z (Adj T) (Icc 1 (n^40)) (fugacity n) ≤ Real.exp ((5/4:ℝ)*(n:ℝ)^15) := by
  have hh := partition_bound (Adj T) (adj_symm T) (adj_irrefl T) (Icc 1 (n^40))
    (n^38) (branchDegree n) (fugacity n) (base n)
    (by unfold fugacity; positivity) (by unfold base; exact le_add_of_nonneg_right (by positivity))
    (branching hn) (seed_dense (by omega) hT hTm hcard)
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at hh
  exact hh.trans (exponential_budget (by omega))

#print axioms branchDegree_bound
#print axioms seed_dense
#print axioms branching
#print axioms exponential_budget
#print axioms seed_partition_bound
end
end Erdos773.SidonPartitionScales
