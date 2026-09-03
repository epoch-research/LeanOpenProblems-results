import Submission.FiniteBrunSieve
import Submission.Explore

/-! A finite upper-bound sieve for arbitrary residue sets at pairwise coprime
moduli. The CRT intersection error used here is deliberately coarse. -/

namespace Erdos371
namespace FiniteSieve

open Finset
variable {ι : Type*}

lemma modEq_finset_prod_iff (S : Finset ι) (s : ι → ℕ)
    (hc : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s)) (a b : ℕ) :
    Nat.ModEq (∏ i ∈ S, s i) a b ↔ ∀ i ∈ S, Nat.ModEq (s i) a b := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Nat.ModEq]; omega
  | @insert i S hi ih =>
    have hcS : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s) :=
      hc.mono (by simp)
    have hic : (s i).Coprime (∏ j ∈ S, s j) := Nat.coprime_prod_right_iff.mpr fun j hj =>
      hc (by simp) (by simp [hj]) (by intro he; subst j; contradiction)
    rw [prod_insert hi, ← Nat.modEq_and_modEq_iff_modEq_mul hic, ih hcS]
    simp

/-- Exact independence of congruence conditions in one full CRT period. -/
lemma intersectionCount_full_period (S : Finset ι) (s : ι → ℕ)
    (R : ι → Finset ℕ) (hs : ∀ i ∈ S, s i ≠ 0)
    (hc : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s))
    (hR : ∀ i ∈ S, R i ⊆ range (s i)) :
    intersectionCount (range (∏ i ∈ S, s i)) (fun i n => n % s i ∈ R i) S =
      ∏ i ∈ S, (R i).card := by
  classical
  rw [← card_pi S R]
  simp only [intersectionCount]
  rw [filter_congr_decidable]
  apply card_bij (fun n _ i _ => n % s i)
  · intro n hn
    exact mem_pi.mpr (mem_filter.mp hn).2
  · intro a ha b hb hab
    apply ((modEq_finset_prod_iff S s hc a b).mpr ?_).eq_of_lt_of_lt
      (mem_range.mp (mem_filter.mp ha).1) (mem_range.mp (mem_filter.mp hb).1)
    intro i hi
    exact congrFun (congrFun hab i) hi
  · intro f hf
    let a : ι → ℕ := fun i => if hi : i ∈ S then f i hi else 0
    let n := Nat.chineseRemainderOfFinset a s S hs hc
    have hnmod (i : ι) (hi : i ∈ S) : n.val % s i = f i hi := by
      have h : n.val % s i = a i % s i := n.property i hi
      have hfR := mem_pi.mp hf i hi
      have hlt := mem_range.mp (hR i hi hfR)
      simpa [a, hi, Nat.mod_eq_of_lt hlt] using h
    have hn : n.val ∈ (range (∏ i ∈ S, s i)).filter (fun n => ∀ i ∈ S, n % s i ∈ R i) := by
      refine mem_filter.mpr ⟨mem_range.mpr (Nat.chineseRemainderOfFinset_lt_prod a s hs hc), ?_⟩
      intro i hi
      rw [hnmod i hi]
      exact mem_pi.mp hf i hi
    exact ⟨n.val, hn, by funext i hi; exact hnmod i hi⟩

lemma localDensity_bounds (S : Finset ι) (s : ι → ℕ) (R : ι → Finset ℕ)
    (hs : ∀ i ∈ S, s i ≠ 0) (hR : ∀ i ∈ S, R i ⊆ range (s i)) :
    ∀ i ∈ S, 0 ≤ (R i).card / (s i : ℝ) ∧ (R i).card / (s i : ℝ) ≤ 1 := by
  intro i hi
  constructor
  · positivity
  · apply (div_le_one (show (0 : ℝ) < s i by exact_mod_cast Nat.pos_of_ne_zero (hs i hi))).mpr
    exact_mod_cast (card_le_card (hR i hi)).trans_eq (card_range _)

/-- The discrepancy of an intersection of coprime residue conditions is
bounded by one full CRT period. -/
lemma intersectionCount_residue_error (S : Finset ι) (s : ι → ℕ)
    (R : ι → Finset ℕ) (hs : ∀ i ∈ S, s i ≠ 0)
    (hc : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s))
    (hR : ∀ i ∈ S, R i ⊆ range (s i)) (N : ℕ) :
    |(intersectionCount (range N) (fun i n => n % s i ∈ R i) S : ℝ) -
      N * ∏ i ∈ S, ((R i).card / (s i : ℝ))| ≤ ∏ i ∈ S, (s i : ℝ) := by
  classical
  let Q := ∏ i ∈ S, s i
  let d : ℝ := ∏ i ∈ S, ((R i).card / (s i : ℝ))
  let f : ℕ → ℝ := fun n => (if ∀ i ∈ S, n % s i ∈ R i then 1 else 0) - d
  have hQ : 0 < Q := prod_pos fun i hi => Nat.pos_of_ne_zero (hs i hi)
  have hd0 : 0 ≤ d := prod_nonneg fun _ _ => by positivity
  have hd1 : d ≤ 1 := prod_le_one (fun i hi => (localDensity_bounds S s R hs hR i hi).1)
    (fun i hi => (localDensity_bounds S s R hs hR i hi).2)
  have hp : Function.Periodic f Q := by
    intro n
    have hm (i : ι) (hi : i ∈ S) : (n+Q) % s i = n % s i := by
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (dvd_prod_of_mem s hi), Nat.add_zero, Nat.mod_mod]
    have he : (∀ i ∈ S, (n+Q) % s i ∈ R i) ↔ (∀ i ∈ S, n % s i ∈ R i) :=
      forall₂_congr fun i hi => by rw [hm i hi]
    simp only [f, he]
  have hsum (M : ℕ) : (∑ n ∈ range M, f n) =
      (intersectionCount (range M) (fun i n => n % s i ∈ R i) S : ℝ) - M*d := by
    simp [f, sum_sub_distrib, intersectionCount]
    congr 1
    ext n
    simp
  have hz : (∑ n ∈ range Q, f n) = 0 := by
    rw [hsum, intersectionCount_full_period S s R hs hc hR]
    have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
    have he : d = (∏ i ∈ S, (R i).card : ℕ) / (Q : ℝ) := by
      simp [d, Q, prod_div_distrib]
    rw [he]
    field_simp
    ring
  have hb (n : ℕ) : ‖f n‖ ≤ 1 := by
    dsimp [f]
    rw [abs_le]
    split_ifs <;> constructor <;> linarith
  have h := periodic_sum_zero_bound f Q hQ hp hz hb N
  rw [hsum, Real.norm_eq_abs] at h
  simpa [d, Q] using h

/-- Pure Brun sieve for arbitrary local residue restrictions. -/
theorem residue_brun_upper_bound (S : Finset ι) (s : ι → ℕ)
    (R : ι → Finset ℕ) (hs : ∀ i ∈ S, s i ≠ 0)
    (hc : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s))
    (hR : ∀ i ∈ S, R i ⊆ range (s i)) (N k : ℕ)
    (hk : 3 * (∑ i ∈ S, (R i).card / (s i : ℝ)) ≤ (2*k+1 : ℕ) * Real.log 2) :
    (avoidanceCount (range N) (fun i n => n % s i ∈ R i) S : ℝ) ≤
      2 * N * Real.exp (-(∑ i ∈ S, (R i).card / (s i : ℝ))) +
      ∑ T ∈ S.powerset, if T.card ≤ 2*k then ∏ i ∈ T, (s i : ℝ) else 0 := by
  apply brun_upper_bound_exp (range N) (fun i n => n % s i ∈ R i) S
    (fun i => (R i).card / (s i : ℝ)) k N (fun T => ∏ i ∈ T, (s i : ℝ))
    (by positivity) (localDensity_bounds S s R hs hR) hk
  intro T hT _
  have hTS := mem_powerset.mp hT
  exact intersectionCount_residue_error T s R (fun i hi => hs i (hTS hi))
    (hc.mono hTS) (fun i hi => hR i (hTS hi)) N

#print axioms residue_brun_upper_bound

end FiniteSieve
end Erdos371
