import Submission.NaturalPrimeGapTransfer
import Submission.PrimeLogQuantization

/-! Arithmetic instantiation of the entropy transfer for multiplier-stable
largest-prime-factor labels. The shorter adjacent endpoints are retained. -/
namespace Erdos371.FiniteInformation
open Finset Filter BlockPrimes EntropyScales
open scoped Topology

/-- Without p|N, rounding introduces a vanishing error, but still gives N/p. -/
lemma conditioned_prefix_dilation_error {A : Type*} (L : ℕ → A) (C : A → A → ℝ)
    (q N : ℕ) (hq : 0 < q) (hqN : q ≤ N)
    (hC : ∀ a b, |C a b| ≤ 1) (hL : ∀ m, L (q*m) = L m) :
    |q * prefixMean N (fun n => if q ∣ n then C (L n) (L (n+q)) else 0) -
      prefixMean (N/q) (fun m => C (L m) (L (m+1)))| ≤ 2*(q : ℝ)^2/N := by
  classical
  let M := q*(N/q)
  have hT : 0 < N/q := Nat.div_pos hqN hq
  have hM : 0 < M := Nat.mul_pos hq hT
  have hMN : M ≤ N := Nat.mul_div_le N q
  have htail : N-M ≤ q := by
    have he := Nat.div_add_mod N q
    have hr := Nat.mod_lt N hq
    dsimp [M]
    omega
  have hd : q ∣ M := dvd_mul_right q (N/q)
  have h := conditioned_prefix_dilation L C q M hq hM hd hL
  have hquot : M/q = N/q := Nat.mul_div_right _ hq
  rw [hquot] at h
  rw [← h, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  have hb := prefixMean_endpoint_bound M N hM hMN
    (fun n => if q ∣ n then C (L n) (L (n+q)) else 0) 1
    (fun n _ => by dsimp only; split_ifs <;> simp_all)
  simp only [mul_one] at hb
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) q)
  calc
    _ ≤ (q : ℝ)*(2*(N-M : ℕ)/N) := hm
    _ ≤ (q : ℝ)*(2*q/N) := by gcongr
    _ = _ := by ring

lemma stable_natural_gap_error {A : Type*} (L : ℕ → A) (C : A → A → ℝ)
    (q N : ℕ) (hq : 0 < q) (hqN : q ≤ N)
    (hC : ∀ a b, |C a b| ≤ 1) (hL : ∀ m, L (q*m) = L m) :
    |naturalGapDiscrepancy N q L C -
      (prefixMean (N/q) (fun m => C (L m) (L (m+1))) -
        prefixMean N (fun m => C (L m) (L (m+q))))| ≤ 2*(q : ℝ)^2/N := by
  unfold naturalGapDiscrepancy
  rw [sub_sub_sub_cancel_right]
  exact conditioned_prefix_dilation_error L C q N hq hqN hC hL

/-- The entropy transfer is now instantiated for the actual prime-factor
labels, for every fixed finite quantization and every bounded pair observable.
This is not cancellation of the adjacent correlation at endpoint N. -/
theorem primeQuantLabel_prime_transfer (Q H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∃ n < K,
      ∀ C : Fin (Q+1) → Fin (Q+1) → ℝ, (∀ a b, |C a b| ≤ 1) →
        |(∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
          (prefixMean (N/p) (fun m => C (primeQuantLabel Q N m) (primeQuantLabel Q N (m+1))) -
            prefixMean N (fun m => C (primeQuantLabel Q N m) (primeQuantLabel Q N (m+p))))) /
              (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  obtain ⟨K,hK,htrans⟩ := natural_prime_gap_transfer (A := Fin (Q+1)) H₀ hH₀ (ε/2) (by positivity)
  let B := (range K).sup (factorialScale H₀)
  have hstable := primeQuantLabel_eventually_mul Q B
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2*(B : ℝ)^2)
  refine ⟨K,hK,?_⟩
  filter_upwards [htrans,hstable,eventually_ge_atTop B,
    ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2)] with N htrans hstable hNB ht
  obtain ⟨n,hn,hgap⟩ := htrans (primeQuantLabel Q N)
  refine ⟨n,hn,?_⟩
  intro C hC
  let S := halfBlockPrimes (factorialScale H₀ n)
  have hH : factorialScale H₀ n ≤ B := le_sup (mem_range.mpr hn)
  have hS : S.Nonempty := halfBlockPrimes_nonempty _
    (le_trans (by omega : 4 ≤ H₀) (factorialScale_ge H₀ n))
  let D (p : ℕ) : ℝ :=
    prefixMean (N/p) (fun m => C (primeQuantLabel Q N m) (primeQuantLabel Q N (m+1))) -
      prefixMean N (fun m => C (primeQuantLabel Q N m) (primeQuantLabel Q N (m+p)))
  have he : |(∑ p ∈ S, (naturalGapDiscrepancy N p (primeQuantLabel Q N) C-D p))/(S.card : ℝ)| ≤
      2*(B : ℝ)^2/N := by
    apply abs_finset_average_le S hS
    intro p hp
    obtain ⟨hpp,hpH⟩ := mem_halfBlockPrimes.mp hp
    have hpB : p ≤ B := by omega
    have hb := stable_natural_gap_error (primeQuantLabel Q N) C p N hpp.pos
      (hpB.trans hNB) hC (hstable p hpp.pos hpB)
    apply hb.trans
    gcongr
  rw [sum_sub_distrib,sub_div] at he
  have hg := hgap C hC
  change |(∑ p ∈ S, naturalGapDiscrepancy N p (primeQuantLabel Q N) C)/(S.card : ℝ)| < ε/2 at hg
  change |(∑ p ∈ S, D p)/(S.card : ℝ)| < ε
  have htri := abs_sub_le ((∑ p ∈ S, D p)/(S.card : ℝ))
    ((∑ p ∈ S, naturalGapDiscrepancy N p (primeQuantLabel Q N) C)/(S.card : ℝ)) 0
  simp only [sub_zero] at htri
  rw [abs_sub_comm] at he
  linarith

#print axioms conditioned_prefix_dilation_error
#print axioms primeQuantLabel_prime_transfer
end Erdos371.FiniteInformation
