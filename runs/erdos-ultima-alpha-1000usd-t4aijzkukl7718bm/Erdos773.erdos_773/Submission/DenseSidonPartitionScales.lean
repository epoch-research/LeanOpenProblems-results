import Submission.SidonDifferenceGraph

/-! Explicit polynomial scales for the Sidon-seed partition estimate. These
scales apply to arbitrary integer sets, not specifically to square values.
The ambient length is n^100 and the large-Sidon threshold will be n^40. -/
namespace Erdos773.DenseSidonPartitionScales
open Finset SidonPartitionFunction SidonDifferenceGraph
set_option maxHeartbeats 3000000
noncomputable section

def branchDegree (n : ℕ) : ℕ := 12*(n^2/48)*n^60
def fugacity (n : ℕ) : ℝ := 1/(4*(n:ℝ)^50)
def base (n : ℕ) : ℝ := 1+1/(n:ℝ)^60

lemma branchDegree_bound (n : ℕ) : (branchDegree n:ℝ) ≤ (n:ℝ)^62/4 := by
  have hq : (48:ℝ)*(n^2/48:ℕ) ≤ (n:ℝ)^2 := by exact_mod_cast Nat.mul_div_le (n^2) 48
  have hh := mul_le_mul_of_nonneg_right hq (pow_nonneg (Nat.cast_nonneg n: (0:ℝ) ≤ n) 60)
  dsimp [branchDegree]
  push_cast
  nlinarith only [hh]

lemma seed_dense {n : ℕ} (hn : 2 ≤ n) {T : Finset ℕ}
    (hT : IsSidon (T:Set ℕ)) (hTm : T ⊆ Icc 1 (n^100)) (hcard : T.card=n^36) :
    ∀ W ⊆ Icc 1 (n^100), n^90<W.card →
      ∃ v ∈ W, branchDegree n ≤ (neighbors (Adj T) W v).card := by
  intro W hWm hW
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  have hW0 : (0:ℝ)<W.card := by exact_mod_cast (show 0<W.card by omega)
  have hWR : (n:ℝ)^90 < W.card := by exact_mod_cast hW
  have hD := branchDegree_bound n
  have hDm := mul_le_mul_of_nonneg_right hD (pow_nonneg hn0.le 100)
  have hfour : (4:ℝ) ≤ (n:ℝ)^26 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hnR 26
    norm_num at hh
    linarith only [hh]
  have hfourm := mul_le_mul_of_nonneg_right hfour (pow_nonneg hn0.le 136)
  have hpre : 2*(n:ℝ)^100*((n:ℝ)^36+branchDegree n) ≤ ((n:ℝ)^36)^2*(n:ℝ)^90 := by
    nlinarith only [hDm,hfourm]
  have hstrict := mul_lt_mul_of_pos_left hWR (sq_pos_of_pos (pow_pos hn0 36))
  by_contra! hnothigh
  have hb := density_bound hT hTm hWm (branchDegree n:ℝ) (fun v hv => by
    exact_mod_cast (hnothigh v hv).le)
  rw [hcard] at hb
  push_cast at hb
  have hb' : (W.card:ℝ)*((W.card:ℝ)*((n:ℝ)^36)^2) ≤
      (W.card:ℝ)*(2*(n:ℝ)^100*((n:ℝ)^36+branchDegree n)) := by nlinarith only [hb]
  have hh := le_of_mul_le_mul_left hb' hW0
  nlinarith only [hh,hpre,hstrict]

lemma branching {n : ℕ} (hn : 1000 ≤ n) :
    fugacity n ≤ (base n-1)*(base n)^branchDegree n := by
  have hnR : (1000:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  have hq : (n:ℝ)^2/48 ≤ (n^2/48:ℕ)+1 := by
    have hh : (n:ℝ)^2<48*((n^2/48:ℕ)+1) := by
      exact_mod_cast Nat.lt_mul_div_succ (n^2) (by omega : 0<48)
    linarith only [hh]
  have hnon : (0:ℝ) ≤ 1/(n:ℝ)^60 := by positivity
  have hB := one_add_mul_le_pow (show (-2:ℝ) ≤ 1/(n:ℝ)^60 by linarith only [hnon])
    (n^60*(n^2/48))
  have he : (1:ℝ)+(n^60*(n^2/48):ℕ)*(1/(n:ℝ)^60)=1+(n^2/48:ℕ) := by
    push_cast
    field_simp
  rw [he] at hB
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+(n^2/48:ℕ)) hB 12
  have hexp : (n^60*(n^2/48))*12=branchDegree n := by unfold branchDegree; ring
  rw [← pow_mul,hexp] at hp
  have hq12 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (n:ℝ)^2/48) hq 12
  have h14 : (48:ℝ)^12/4 ≤ (n:ℝ)^14 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hnR 14
    norm_num at hh ⊢
    linarith only [hh]
  have hnum := mul_le_mul_of_nonneg_right h14 (pow_nonneg hn0.le 10)
  have hpow : (n:ℝ)^10/4 ≤ (base n)^branchDegree n := by
    change (n:ℝ)^10/4 ≤ (1+1/(n:ℝ)^60)^branchDegree n
    nlinarith only [hp,hq12,hnum]
  have hc : 0 ≤ base n-1 := by unfold base; linarith only [hnon]
  have hm := mul_le_mul_of_nonneg_left hpow hc
  have hid : (base n-1)*((n:ℝ)^10/4)=fugacity n := by
    unfold base fugacity
    field_simp
    ring
  rwa [hid] at hm

lemma exponential_budget {n : ℕ} (hn : 0<n) :
    (base n)^(n^100)*(1+fugacity n)^(n^90) ≤ Real.exp ((5/4:ℝ)*(n:ℝ)^40) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hc : 0 ≤ base n := by unfold base; positivity
  have hz : 0 ≤ 1+fugacity n := by unfold fugacity; positivity
  have h₁ : base n ≤ Real.exp (1/(n:ℝ)^60) := by
    unfold base
    simpa only [add_comm] using Real.add_one_le_exp (1/(n:ℝ)^60)
  have h₂ : 1+fugacity n ≤ Real.exp (fugacity n) := by
    simpa only [add_comm] using Real.add_one_le_exp (fugacity n)
  have hp := mul_le_mul (pow_le_pow_left₀ hc h₁ (n^100)) (pow_le_pow_left₀ hz h₂ (n^90))
    (pow_nonneg hz _) (pow_nonneg (Real.exp_pos _).le _)
  rw [← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add] at hp
  have he : ((n^100:ℕ):ℝ)*(1/(n:ℝ)^60)+((n^90:ℕ):ℝ)*fugacity n=(5/4:ℝ)*(n:ℝ)^40 := by
    unfold fugacity
    push_cast
    field_simp
    ring
  rwa [he] at hp

/-- The independent-set partition function for every Sidon seed of the
specified size has a uniform explicit exponential bound. -/
theorem seed_partition_bound {n : ℕ} (hn : 1000 ≤ n) {T : Finset ℕ}
    (hT : IsSidon (T:Set ℕ)) (hTm : T ⊆ Icc 1 (n^100)) (hcard : T.card=n^36) :
    Z (Adj T) (Icc 1 (n^100)) (fugacity n) ≤ Real.exp ((5/4:ℝ)*(n:ℝ)^40) := by
  have hh := partition_bound (Adj T) (adj_symm T) (adj_irrefl T) (Icc 1 (n^100))
    (n^90) (branchDegree n) (fugacity n) (base n)
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
end Erdos773.DenseSidonPartitionScales
