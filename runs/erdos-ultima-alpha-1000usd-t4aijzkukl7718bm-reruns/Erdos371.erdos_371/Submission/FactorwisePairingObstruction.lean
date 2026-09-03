import FormalConjecturesUtil
import Submission.CofactorDensity
import Submission.PeriodicDensity

/-! An arithmetic obstruction to pairings based on termwise dominance of
prime factors. Such pairings in the counting range can cover only o(N)
inputs. This does not rule out pairings tailored to one fixed prime weight,
and it is not a disproof of Erdős 371. -/

namespace Erdos371FactorwisePairingObstruction

open Finset Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

/-- Unequal products of termwise ordered integer factors cannot be too close
relative to the largest upper factor. -/
lemma product_gap_bound {M : ℕ} {u v : List ℕ}
    (h : List.Forall₂ (fun a b => 0 < b ∧ b ≤ a) u v)
    (hM : ∀ a ∈ u, a ≤ M) (hlt : v.prod < u.prod) :
    v.prod ≤ M*(u.prod-v.prod) := by
  induction h with
  | nil => simp at hlt
  | @cons a b u v hab huv ih =>
      have haM : a ≤ M := hM a (by simp)
      have htail : ∀ c ∈ u, c ≤ M := fun c hc => hM c (by simp [hc])
      have hp : v.prod ≤ u.prod :=
        (List.Forall₂.imp (fun a b hab => hab.2) huv).flip.prod_le_prod'
      simp only [List.prod_cons] at hlt ⊢
      by_cases he : b = a
      · subst b
        have hlt' : v.prod < u.prod := Nat.lt_of_mul_lt_mul_left hlt
        have hh := Nat.mul_le_mul_left a (ih htail hlt')
        calc
          _ ≤ a*(M*(u.prod-v.prod)) := hh
          _ = _ := by rw [← Nat.mul_sub_left_distrib]; ring
      · have hba : b+1 ≤ a := by omega
        have hx : v.prod ≤ a*u.prod-b*v.prod := by
          have h₁ := Nat.mul_le_mul_left a hp
          have h₂ := Nat.mul_le_mul_right v.prod hba
          have hx : v.prod+b*v.prod ≤ a*u.prod := by nlinarith
          omega
        have h₃ := Nat.mul_le_mul_left M hx
        have h₄ := Nat.mul_le_mul_right v.prod (hab.2.trans haM)
        omega

/-- A permissive termwise-factor certificate. In particular it includes
matching each lower prime factor to a no-smaller upper prime factor, with
unused upper factors paired with ones. -/
def factorPairing (n m : ℕ) : Prop :=
  ∃ b : List ℕ,
    List.Forall₂ (fun a b => 0 < b ∧ b ≤ a)
      ((n+1).primeFactorsList ++ (m+1).primeFactorsList) b ∧ b.prod = n*m

lemma factorPairing_gap {n m : ℕ} (h : factorPairing n m) :
    n*m ≤ max (Nat.maxPrimeFac (n+1)) (Nat.maxPrimeFac (m+1)) * (n+m+1) := by
  obtain ⟨b,hb,hprod⟩ := h
  let M := max (Nat.maxPrimeFac (n+1)) (Nat.maxPrimeFac (m+1))
  have hu : ((n+1).primeFactorsList ++ (m+1).primeFactorsList).prod = (n+1)*(m+1) := by
    rw [List.prod_append, Nat.prod_primeFactorsList (by omega), Nat.prod_primeFactorsList (by omega)]
  have hM : ∀ a ∈ ((n+1).primeFactorsList ++ (m+1).primeFactorsList), a ≤ M := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · have hh := Nat.mem_primeFactors.mp (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr ha)
      exact (Nat.le_maxPrimeFac (by omega : n+1 ≠ 0) hh.1 hh.2.1).trans (le_max_left _ _)
    · have hh := Nat.mem_primeFactors.mp (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr ha)
      exact (Nat.le_maxPrimeFac (by omega : m+1 ≠ 0) hh.1 hh.2.1).trans (le_max_right _ _)
  have hh := product_gap_bound hb hM (by rw [hprod,hu]; nlinarith)
  rw [hprod,hu] at hh
  have he : (n+1)*(m+1)-n*m = n+m+1 := by
    have he : (n+1)*(m+1) = n*m+(n+m+1) := by ring
    omega
  simpa only [he] using hh

lemma min_le_three_max_prime {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : factorPairing n m) :
    min n m ≤ 3*max (Nat.maxPrimeFac (n+1)) (Nat.maxPrimeFac (m+1)) := by
  have hb := factorPairing_gap h
  let M := max (Nat.maxPrimeFac (n+1)) (Nat.maxPrimeFac (m+1))
  change n*m ≤ M*(n+m+1) at hb
  rcases le_total n m with hnm | hmn
  · rw [min_eq_left hnm]
    have he : n+m+1 ≤ 3*m := by omega
    have hh := hb.trans (Nat.mul_le_mul_left M he)
    have hh' : n*m ≤ (3*M)*m := by nlinarith
    exact Nat.le_of_mul_le_mul_right hh' hm
  · rw [min_eq_right hmn]
    have he : n+m+1 ≤ 3*n := by omega
    have hh := hb.trans (Nat.mul_le_mul_left M he)
    have hh' : m*n ≤ (3*M)*n := by nlinarith
    exact Nat.le_of_mul_le_mul_right hh' hn

/-- A short prefix together with the rare bounded-cofactor inputs. -/
def exceptional (K N : ℕ) : Finset ℕ :=
  range (N/K+1) ∪ (range N).filter
    (fun n => (n+1)/Nat.maxPrimeFac (n+1) ≤ 3*K)

lemma pair_meets_exceptional {K N n m : ℕ} (hK : 0 < K)
    (hn : n < N) (hm : m < N) (h : factorPairing n m) :
    n ∈ exceptional K N ∨ m ∈ exceptional K N := by
  by_cases hnsmall : n ≤ N/K
  · exact Or.inl (mem_union_left _ (mem_range.mpr (by omega)))
  by_cases hmsmall : m ≤ N/K
  · exact Or.inr (mem_union_left _ (mem_range.mpr (by omega)))
  have hn0 : 0 < n := (Nat.zero_le (N/K)).trans_lt (Nat.lt_of_not_ge hnsmall)
  have hm0 : 0 < m := (Nat.zero_le (N/K)).trans_lt (Nat.lt_of_not_ge hmsmall)
  have hNn : N ≤ K*n := by
    rw [Nat.le_div_iff_mul_le hK] at hnsmall
    nlinarith
  have hNm : N ≤ K*m := by
    rw [Nat.le_div_iff_mul_le hK] at hmsmall
    nlinarith
  have hh := min_le_three_max_prime hn0 hm0 h
  have hNmin : N ≤ K*min n m := by rcases le_total n m with hnm | hmn <;> simp [*]
  have hNM := hNmin.trans (Nat.mul_le_mul_left K hh)
  rcases le_total (Nat.maxPrimeFac (n+1)) (Nat.maxPrimeFac (m+1)) with hnm | hmn
  · rw [max_eq_right hnm] at hNM
    apply Or.inr
    apply mem_union_right
    apply mem_filter.mpr
    refine ⟨mem_range.mpr hm, ?_⟩
    exact Nat.div_le_of_le_mul (by nlinarith : m+1 ≤ Nat.maxPrimeFac (m+1)*(3*K))
  · rw [max_eq_left hmn] at hNM
    apply Or.inl
    apply mem_union_right
    apply mem_filter.mpr
    refine ⟨mem_range.mpr hn, ?_⟩
    exact Nat.div_le_of_le_mul (by nlinarith : n+1 ≤ Nat.maxPrimeFac (n+1)*(3*K))

lemma matching_card_bound {K N : ℕ} (hK : 0 < K) (S : Finset ℕ) (f : ℕ → ℕ)
    (hS : S ⊆ range N) (hf : ∀ n ∈ S, f n < N)
    (hinj : Set.InjOn f S) (hpair : ∀ n ∈ S, factorPairing n (f n)) :
    S.card ≤ 2*((N/K+1) + ((range N).filter
      (fun n => (n+1)/Nat.maxPrimeFac (n+1) ≤ 3*K)).card) := by
  let E := exceptional K N
  have hleft : (S.filter (fun n => n ∈ E)).card ≤ E.card :=
    card_le_card (fun n hn => (mem_filter.mp hn).2)
  have hright : (S.filter (fun n => n ∉ E)).card ≤ E.card := by
    apply card_le_card_of_injOn f
    · intro n hn
      obtain ⟨hnS,hnE⟩ := mem_filter.mp hn
      exact (pair_meets_exceptional hK (mem_range.mp (hS hnS)) (hf n hnS) (hpair n hnS)).resolve_left hnE
    · exact hinj.mono (filter_subset _ _)
  have hsplit := card_filter_add_card_filter_not (s := S) (fun n => n ∈ E)
  have hE : E.card ≤ (N/K+1) + ((range N).filter
      (fun n => (n+1)/Nat.maxPrimeFac (n+1) ≤ 3*K)).card := by
    simpa only [E,exceptional,card_range] using card_union_le (range (N/K+1))
      ((range N).filter (fun n => (n+1)/Nat.maxPrimeFac (n+1) ≤ 3*K))
  omega

/-- Even an arbitrary cutoff-dependent injective matching by these termwise
factor certificates can cover only a vanishing proportion of the inputs. -/
theorem matching_proportion_tendsto_zero (S : ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ)
    (hS : ∀ N, S N ⊆ range N) (hf : ∀ N n, n ∈ S N → f N n < N)
    (hinj : ∀ N, Set.InjOn (f N) (S N))
    (hpair : ∀ N n, n ∈ S N → factorPairing n (f N n)) :
    Tendsto (fun N : ℕ => ((S N).card : ℝ)/N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K,hKbig⟩ := exists_nat_gt (8/ε)
  have hK : 0 < K := Nat.cast_pos.mp ((by positivity : (0 : ℝ) < 8/ε).trans hKbig)
  have hk : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hsmall : 2/(K : ℝ) < ε/2 := by
    have hh := (div_lt_iff₀ hε).mp hKbig
    apply (div_lt_iff₀ hk).mpr
    nlinarith
  have hbad := Erdos371CofactorDensity.density_zero_shift
    (S := {n | n/Nat.maxPrimeFac n ≤ 3*K})
    (Erdos371CofactorDensity.bounded_cofactor_hasDensity_zero (3*K))
  have hlim : Tendsto (fun N : ℕ => 2/(N : ℝ)+2*
      {n | (n+1)/Nat.maxPrimeFac (n+1) ≤ 3*K}.partialDensity Set.univ N) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat.const_mul 2).add (hbad.const_mul 2)
  filter_upwards [hlim.eventually_lt_const (half_pos hε), eventually_gt_atTop 0] with N hlimN hN
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
  have hc : ((S N).card : ℝ) ≤ 2*(((N/K : ℕ) : ℝ)+1+
      (((range N).filter (fun n => (n+1)/Nat.maxPrimeFac (n+1) ≤ 3*K)).card : ℝ)) := by
    exact_mod_cast matching_card_bound hK (S N) (f N) (hS N) (hf N) (hinj N) (hpair N)
  have hb : ((S N).card : ℝ)/N ≤ 2/(K : ℝ)+2/(N : ℝ)+2*
      {n | (n+1)/Nat.maxPrimeFac (n+1) ≤ 3*K}.partialDensity Set.univ N := by
    rw [Erdos371Exploration.partialDensity_eq_count]
    calc
      _ ≤ 2*((N : ℝ)/K+1+
          (((range N).filter (fun n => (n+1)/Nat.maxPrimeFac (n+1) ≤ 3*K)).card : ℝ))/N := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
        linarith [Nat.cast_div_le (α := ℝ) (m := N) (n := K)]
      _ = _ := by field_simp
  linarith

end Erdos371FactorwisePairingObstruction

#print axioms Erdos371FactorwisePairingObstruction.product_gap_bound
#print axioms Erdos371FactorwisePairingObstruction.matching_proportion_tendsto_zero
