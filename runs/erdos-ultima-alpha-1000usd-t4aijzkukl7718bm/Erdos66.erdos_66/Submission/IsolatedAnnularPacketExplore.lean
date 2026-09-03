import Submission.TemplatePacketExplore
import Submission.ShiftedUpperAnnulusExplore
import Submission.CompactnessExplore

/-! Finite logarithmic annular packets with small self-counts outside one
specified coarse block. No bound on mixed counts with an old set is claimed. -/
namespace Erdos66IsolatedAnnularPacket
open Filter AdditiveCombinatorics Erdos66TemplatePacket Erdos66ShiftedUpperAnnulus
  Erdos66Compactness Erdos66Counting
open scoped Topology Classical
set_option maxHeartbeats 2000000

lemma tensor_log_bound (M : ℕ) (hM : 0 < M) (P S : Finset ℕ)
    (hS : ∀ x∈S, x < M) (hSS : ∀ x∈S, ∀ y∈S, x+y < M)
    (V b : ℝ) (hV : 0 ≤ V) (hb : 0 ≤ b)
    (hSb : ∀ t, (sumRep (S : Set ℕ) t : ℝ) ≤ b*Real.log t)
    (n : ℕ) (hPn : (sumRep (P : Set ℕ) (n/M) : ℝ) ≤ V) :
    (sumRep (tensor M P S : Set ℕ) n : ℝ)/Real.log n ≤ V*b := by
  have he := Nat.div_add_mod' n M
  have hr : sumRep (tensor M P S : Set ℕ) n =
      sumRep (P : Set ℕ) (n/M)*sumRep (S : Set ℕ) (n%M) := by
    simpa only [he] using tensor_rep M hM P S hS hSS (n/M) (n%M) (Nat.mod_lt _ hM)
  by_cases hn : n < 2
  · have hz : Real.log (n : ℝ)=0 := by interval_cases n <;> norm_num
    rw [hz,div_zero]
    positivity
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  apply (div_le_iff₀ hlogn).mpr
  rw [hr,Nat.cast_mul]
  have hh := mul_le_mul hPn (hSb (n%M)) (Nat.cast_nonneg _) hV
  have ht : Real.log ((n%M : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    by_cases hz : n%M=0
    · rw [hz,Nat.cast_zero,Real.log_zero]
      exact hlogn.le
    · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hz))
        (by exact_mod_cast Nat.mod_le n M)
  have hm := mul_le_mul_of_nonneg_left ht (mul_nonneg hV hb)
  nlinarith

/-- Amplification can make the entire off-block logarithmic self-envelope
arbitrarily small, while retaining a positive-length interval of accuracy.
The amplification index is fixed before the lower support bound. -/
theorem exists_isolated_annular_packet (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (R : ℕ) (hR : 1 ≤ R) :
    ∃ m : ℕ, 4 ≤ m ∧ ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧ ∃ D : Finset ℕ,
        (∀ a∈D, N₀ ≤ a) ∧
        (∀ n : ℕ, (sumRep (D : Set ℕ) n : ℝ)/Real.log n < c+ε) ∧
        (∀ n : ℕ, n/(2*(R*N+1)) ≠ 2*(m^4+1) →
          (sumRep (D : Set ℕ) n : ℝ)/Real.log n < ε) ∧
        ∀ t : ℕ, N ≤ t → t ≤ R*N →
          |(sumRep (D : Set ℕ) ((2*(m^4+1))*(2*(R*N+1))+t) : ℝ)/
              Real.log (((2*(m^4+1))*(2*(R*N+1))+t : ℕ) : ℝ)-c| < ε := by
  let η := min (ε/16) (c/16)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηε : η ≤ ε/16 := min_le_left _ _
  obtain ⟨m,hm⟩ := exists_nat_gt (max (4 : ℝ) (12*c/ε))
  have hm4r : (4 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hm4 : 4 ≤ m := by exact_mod_cast hm4r.le
  have hm0 : (0 : ℝ) < m := by linarith
  have hmc : 12*c < ε*m := by
    have hh := lt_of_le_of_lt (le_max_right _ _) hm
    nlinarith [(div_lt_iff₀ hε).mp hh]
  let b := c/(2*m)+η/m
  have hb : 0 < b := by dsimp [b]; positivity
  have hmain : 2*(m : ℝ)*b=c+2*η := by dsimp [b]; field_simp <;> ring
  have hoff : 6*b < ε := by
    have hh : 6*b*m=3*c+6*η := by dsimp [b]; field_simp <;> ring
    nlinarith
  let K : ℕ := 4*(m^4+1)*(R+1)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hdecay : Tendsto (fun n : ℕ ↦ c*Real.log (K : ℝ)/Real.log n) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop _
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hdecay.eventually_lt_const hη)
  refine ⟨m,hm4,fun N₀ ↦ ?_⟩
  obtain ⟨N,hN,hNpos,A,hAfin,hAsupp,hAup,hAgood⟩ :=
    exists_upper_logarithmic_annulus (c/(2*m)) (η/m) (by positivity) (by positivity)
      R (max L (max N₀ 2)) hR
  have hNL : L ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  let W := R*N+1
  let S : Finset ℕ := (Finset.range W).filter (fun a ↦ a∈A)
  have hW : 0 < W := by dsimp [W]; positivity
  have hSbound : ∀ x∈S, x < W := fun x hx ↦ Finset.mem_range.mp (Finset.mem_filter.mp hx).1
  have hSsub : (S : Set ℕ) ⊆ A := by
    intro x hx
    change x∈S at hx
    exact (Finset.mem_filter.mp hx).2
  have hSsupp : ∀ x∈S, max L (max N₀ 2) ≤ x := fun x hx ↦ hAsupp (hSsub hx)
  have hSzero (t : ℕ) (ht : t < 2) : sumRep (S : Set ℕ) t=0 := by
    rw [←Erdos66NatPairAlgebra.pairs_self]
    apply Erdos66NatPairAlgebra.pairs_zero_of_lower S S 2 2 t
    · intro x hx
      have hh := hSsupp x hx
      omega
    · intro x hx
      have hh := hSsupp x hx
      omega
    · omega
  have hSb : ∀ t, (sumRep (S : Set ℕ) t : ℝ) ≤ b*Real.log t := by
    intro t
    by_cases ht : t < 2
    · rw [hSzero t ht,Nat.cast_zero]
      exact mul_nonneg hb.le (Real.log_natCast_nonneg t)
    have hlog : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    have hh := (div_lt_iff₀ hlog).mp (hAup t)
    have hr : (sumRep (S : Set ℕ) t : ℝ) ≤ sumRep A t := by
      exact_mod_cast Erdos66Explore.sumRep_mono hSsub t
    exact hr.trans hh.le
  have hSrep (t : ℕ) (ht : t ≤ R*N) : sumRep (S : Set ℕ) t=sumRep A t := by
    apply sumRep_congr_below
    intro a ha
    simp only [Finset.mem_coe,Finset.mem_filter,Finset.mem_range,S]
    exact and_iff_right (by dsimp [W]; omega)
  obtain ⟨P,hPc,hPb,hPcenter,hPoff⟩ := exists_coarse_packet m
  let M := 2*W
  have hM : 0 < M := by dsimp [M]; omega
  have hS' : ∀ x∈S, x < M := by intro x hx; have := hSbound x hx; dsimp [M]; omega
  have hSS : ∀ x∈S, ∀ y∈S, x+y < M := by
    intro x hx y hy
    have := hSbound x hx
    have := hSbound y hy
    dsimp [M]
    omega
  refine ⟨N,by omega,hNpos,tensor M P S,?_,?_,?_,?_⟩
  · intro a ha
    obtain ⟨ax,hax,rfl⟩ := Finset.mem_image.mp ha
    have hh := hSsupp ax.2 (Finset.mem_product.mp hax).2
    omega
  · intro n
    have hp : (sumRep (P : Set ℕ) (n/M) : ℝ) ≤ 2*m := by
      by_cases hn : n/M=2*(m^4+1)
      · rw [hn,hPcenter]; push_cast; rfl
      · have hh := hPoff (n/M) hn
        have hh' : (sumRep (P : Set ℕ) (n/M) : ℝ) ≤ 6 := by exact_mod_cast hh
        linarith
    have hh := tensor_log_bound M hM P S hS' hSS (2*m) b (by positivity) hb.le hSb n hp
    rw [hmain] at hh
    linarith
  · intro n hn
    have hp : (sumRep (P : Set ℕ) (n/M) : ℝ) ≤ 6 := by exact_mod_cast hPoff (n/M) hn
    exact (tensor_log_bound M hM P S hS' hSS 6 b (by norm_num) hb.le hSb n hp).trans_lt hoff
  · intro t htlo hthi
    have htM : t < M := by dsimp [M,W]; omega
    let n := (2*(m^4+1))*M+t
    have hlogt : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    have htn : t ≤ n := by dsimp [n]; omega
    have hlogtn : Real.log (t : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < t by omega)) (by exact_mod_cast htn)
    have hlogn : 0 < Real.log (n : ℝ) := hlogt.trans_le hlogtn
    have hnK : n ≤ K*t := by
      have hWt : W ≤ (R+1)*t := by dsimp [W]; nlinarith
      have hh := Nat.mul_le_mul_left (4*(m^4+1)) hWt
      dsimp [n,M,K]
      nlinarith
    have hlogK : Real.log (n : ℝ) ≤ Real.log (K : ℝ)+Real.log (t : ℝ) := by
      have hh := Real.log_le_log (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)
        (by exact_mod_cast hnK : (n : ℝ) ≤ ((K*t : ℕ) : ℝ))
      push_cast at hh
      rw [Real.log_mul (by exact_mod_cast hK.ne') (by exact_mod_cast (show t≠0 by omega))] at hh
      exact hh
    have hsmall : c*Real.log (K : ℝ) < η*Real.log (t : ℝ) := by
      exact (div_lt_iff₀ hlogt).mp (hL t (by omega))
    have he := hAgood t htlo hthi
    have hscaled : |(2*m : ℝ)*(sumRep A t : ℝ)-c*Real.log t| < 2*η*Real.log t := by
      have hh := mul_lt_mul_of_pos_left he (show (0 : ℝ) < 2*m by positivity)
      have habs : (2*m : ℝ)*|((sumRep A t : ℝ)/Real.log t-c/(2*m))| =
          |(2*m : ℝ)*((sumRep A t : ℝ)/Real.log t-c/(2*m))| := by
        rw [abs_mul,abs_of_pos (show (0 : ℝ) < 2*m by positivity)]
      rw [habs] at hh
      have hcalc : (2*m : ℝ)*((sumRep A t : ℝ)/Real.log t-c/(2*m)) =
          ((2*m : ℝ)*(sumRep A t : ℝ)-c*Real.log t)/Real.log t := by
        field_simp
        <;> ring
      have hcanc : (2*m : ℝ)*(η/m)=2*η := by field_simp <;> ring
      rw [hcalc,hcanc,abs_div,abs_of_pos hlogt] at hh
      exact (div_lt_iff₀ hlogt).mp hh
    have hrep : sumRep (tensor M P S : Set ℕ) n=2*m*sumRep A t := by
      rw [tensor_rep M hM P S hS' hSS _ t htM,hPcenter,hSrep t hthi]
    change |(sumRep (tensor M P S : Set ℕ) n : ℝ)/Real.log n-c| < ε
    rw [hrep]
    have htotal : |((2*m : ℕ) : ℝ)*(sumRep A t : ℝ)-c*Real.log n| < 3*η*Real.log n := by
      have htri := abs_sub_le ((2*m : ℝ)*(sumRep A t : ℝ)) (c*Real.log t) (c*Real.log n)
      have habs : |c*Real.log t-c*Real.log n|=c*(Real.log n-Real.log t) := by
        rw [abs_of_nonpos (by nlinarith)]
        ring
      rw [habs] at htri
      have hm₁ := mul_le_mul_of_nonneg_left hlogtn (show 0 ≤ 2*η by positivity)
      have hm₂ := mul_le_mul_of_nonneg_left hlogtn hη.le
      push_cast
      nlinarith
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat,div_sub' hlogn.ne',abs_div,abs_of_pos hlogn]
    apply (div_lt_iff₀ hlogn).mpr
    have hh := mul_lt_mul_of_pos_right (show 3*η < ε by linarith) hlogn
    simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_comm (Real.log (n : ℝ)) c] using htotal.trans hh

end Erdos66IsolatedAnnularPacket
