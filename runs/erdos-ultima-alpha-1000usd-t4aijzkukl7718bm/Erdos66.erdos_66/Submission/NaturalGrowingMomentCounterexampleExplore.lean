import Submission.FiniteGrowingMomentCounterexampleExplore
import Submission.UpperBaireExplore

/-! Growing-order Gaussian moment lower bounds also fail on arbitrarily
late ordinary integer annuli of one upper-bounded set. This set has holes,
so it is neither a witness nor a disproof of the original conjecture. -/
namespace Erdos66NaturalGrowingMomentCounterexample
open Filter AdditiveCombinatorics Erdos66FiniteGrowingMomentCounterexample
  Erdos66UpperBaire Erdos66LogTuning
open scoped Classical Topology
set_option maxHeartbeats 1400000

lemma pointwise_even_power_lt_factorial (e μ : ℝ) (hμ : 0<μ)
    (k : ℕ) (hk : k≠0) (hsize : μ/2≤(k:ℝ)) (he : |e|≤μ/16) :
    e^(2*k)<(k.factorial:ℝ)*μ^k := by
  simpa using even_moment_lt_factorial (fun _ : Unit ↦ e) μ hμ k hk hsize (fun _ ↦ he)

lemma log_double_le (N : ℕ) (hN : 0<N) :
    Real.log ((2*N:ℕ):ℝ)≤Real.log (N:ℝ)+1 := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have h₂ : Real.log (2:ℝ)≤1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) hNp.ne']
  linarith

/-- One set obeys the exact upper bound r(n)/log n≤1 everywhere and has
arbitrarily late holes. Nevertheless, on arbitrarily late [N,2N] its errors
violate the pointwise lower bound k! log(n)^k simultaneously for every n,
with k arbitrarily large and k≤log N. -/
theorem exists_upper_bounded_counterexample : ∃ A : Set ℕ,
    (∀ n : ℕ, (sumRep A n:ℝ)/Real.log n≤1) ∧
    (∀ K : ℕ, ∃ n≥K, sumRep A n=0) ∧
    ∀ N₀ K₀ : ℕ, ∃ N : ℕ, N₀≤N ∧ 0<N ∧ ∃ k : ℕ,
      K₀<k ∧ (k:ℝ)≤Real.log N ∧
      ∀ n : ℕ, N≤n → n≤2*N →
        ((sumRep A n:ℝ)-Real.log n)^(2*k)<(k.factorial:ℝ)*(Real.log n)^k := by
  obtain ⟨A,hupper,hgood,hholes⟩ := exists_upper_annuli_and_holes 1 (by norm_num)
  refine ⟨A,hupper,hholes,fun N₀ K₀ ↦ ?_⟩
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    (log_nat_atTop.eventually_gt_atTop (8*((K₀:ℝ)+2)))
  obtain ⟨N,hNP,hN,hann⟩ := hgood (1/16) (by norm_num) 2 (max N₀ (max L 2)) (by omega)
  have hNN : N₀≤N := by omega
  have hN2 : 2≤N := by omega
  have hlogbig : 8*((K₀:ℝ)+2)<Real.log (N:ℝ) := hL N (by omega)
  have hlN : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  let k : ℕ := ⌊Real.log (N:ℝ)⌋₊
  have hklo : Real.log (N:ℝ)<(k:ℝ)+1 := Nat.lt_floor_add_one _
  have hkhi : (k:ℝ)≤Real.log (N:ℝ) := Nat.floor_le hlN.le
  have hkK : K₀<k := by
    have hh : (K₀:ℝ)<k := by nlinarith [Nat.cast_nonneg (α := ℝ) K₀]
    exact_mod_cast hh
  refine ⟨N,hNN,hN,k,hkK,hkhi,fun n hn hn' ↦ ?_⟩
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hlogle : Real.log (n:ℝ)≤Real.log (N:ℝ)+1 := by
    apply (Real.log_le_log hnp (show (n:ℝ)≤((2*N:ℕ):ℝ) by exact_mod_cast hn')).trans
    exact log_double_le N hN
  have hkhalf : Real.log (n:ℝ)/2≤(k:ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) K₀]
  have he := hann n hn hn'
  have he' : |(sumRep A n:ℝ)-Real.log n|≤Real.log n/16 := by
    have hquot : ((sumRep A n:ℝ)-Real.log n)/Real.log n=
        (sumRep A n:ℝ)/Real.log n-1 := by field_simp
    rw [←hquot,abs_div,abs_of_pos hln] at he
    have hh := (div_lt_iff₀ hln).mp he
    linarith
  exact pointwise_even_power_lt_factorial _ _ hln k (by omega) hkhalf he'

noncomputable def finiteMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ i, f i)/(Fintype.card α:ℝ)

lemma finiteMean_bounds {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (L U : ℝ) (hf : ∀ i, L≤f i ∧ f i≤U) :
    L≤finiteMean f ∧ finiteMean f≤U := by
  have hp : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ (hf i).1)
  have hhi := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ (hf i).2)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hlo hhi
  exact ⟨(le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hlo),
    (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hhi)⟩

/-- The same failure can be centered at the ACTUAL mean on an ordinary
integer annulus, not just at its nominal logarithmic profile. -/
theorem exists_actual_window_mean_counterexample : ∃ A : Set ℕ,
    (∀ n : ℕ, (sumRep A n:ℝ)/Real.log n≤1) ∧
    (∀ K : ℕ, ∃ n≥K, sumRep A n=0) ∧
    ∀ N₀ K₀ : ℕ, ∃ N : ℕ, N₀≤N ∧ 0<N ∧ ∃ k : ℕ,
      K₀<k ∧ (k:ℝ)≤Real.log N ∧
      let f : Fin (N+1) → ℝ := fun j ↦ (sumRep A (N+j.val):ℝ)
      let μ := finiteMean f
      0<μ ∧ Real.log N/2≤μ ∧ μ≤2*Real.log N ∧
      (∑ j, (f j-μ)^(2*k))/((N+1:ℕ):ℝ)<(k.factorial:ℝ)*μ^k := by
  obtain ⟨A,hupper,hgood,hholes⟩ := exists_upper_annuli_and_holes 1 (by norm_num)
  refine ⟨A,hupper,hholes,fun N₀ K₀ ↦ ?_⟩
  obtain ⟨P,hP⟩ := eventually_atTop.mp
    (log_nat_atTop.eventually_gt_atTop (128*((K₀:ℝ)+2)))
  obtain ⟨N,hNP,hN,hann⟩ := hgood (1/64) (by norm_num) 2 (max N₀ (max P 2)) (by omega)
  have hN2 : 2≤N := by omega
  let L := Real.log (N:ℝ)
  have hLbig : 128*((K₀:ℝ)+2)<L := hP N (by omega)
  have hL : 0<L := by nlinarith [Nat.cast_nonneg (α := ℝ) K₀]
  let f : Fin (N+1) → ℝ := fun j ↦ (sumRep A (N+j.val):ℝ)
  have hf (j : Fin (N+1)) : (63/64)*L≤f j ∧ f j≤L+1 := by
    let n := N+j.val
    have hn : N≤n := by dsimp [n]; omega
    have hn' : n≤2*N := by have := j.isLt; dsimp [n]; omega
    have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have hlo : L≤Real.log (n:ℝ) :=
      Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast hn)
    have hhi : Real.log (n:ℝ)≤L+1 :=
      (Real.log_le_log hnp (show (n:ℝ)≤((2*N:ℕ):ℝ) by exact_mod_cast hn')).trans
        (log_double_le N hN)
    have he := (abs_lt.mp (hann n hn hn')).1
    have hrlo : (63/64)*Real.log (n:ℝ)<f j := by
      apply (lt_div_iff₀ hln).mp
      change 63/64<(sumRep A n:ℝ)/Real.log n
      linarith
    have hrhi : f j≤Real.log (n:ℝ) := by
      have hu := (div_le_iff₀ hln).mp (hupper n)
      simpa only [one_mul] using hu
    constructor <;> linarith
  let μ := finiteMean f
  have hm := finiteMean_bounds f ((63/64)*L) (L+1) hf
  change (63/64)*L≤μ ∧ μ≤L+1 at hm
  have hμ : 0<μ := by linarith
  let k : ℕ := ⌊L⌋₊
  have hklo : L<(k:ℝ)+1 := Nat.lt_floor_add_one _
  have hkhi : (k:ℝ)≤L := Nat.floor_le hL.le
  have hkK : K₀<k := by
    have hh : (K₀:ℝ)<k := by nlinarith [Nat.cast_nonneg (α := ℝ) K₀]
    exact_mod_cast hh
  have hkhalf : μ/2≤(k:ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) K₀]
  have he (j : Fin (N+1)) : |f j-μ|≤μ/16 := by
    have hj := hf j
    have hwidth : L/64+1≤μ/16 := by nlinarith [Nat.cast_nonneg (α := ℝ) K₀]
    rw [abs_le]
    constructor <;> linarith
  refine ⟨N,by omega,hN,k,hkK,hkhi,hμ,by linarith,?_,?_⟩
  · nlinarith [Nat.cast_nonneg (α := ℝ) K₀]
  · simpa only [Fintype.card_fin] using even_moment_lt_factorial
      (fun j : Fin (N+1) ↦ f j-μ) μ hμ k (by omega) hkhalf he

end Erdos66NaturalGrowingMomentCounterexample
