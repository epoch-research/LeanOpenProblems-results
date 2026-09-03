import Submission.InseparableDegree

/-!
A quantitative limitation of repeated target-inseparability certificates.
This is not a bound on actual common-cycle packings or a settlement of Spec.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.InseparableCycle
set_option maxHeartbeats 800000

/-- Optimizing the incidence-cost inequality over the number of targets
still leaves a quadratic ceiling on the initial common target degree. -/
lemma certificate_budget_arithmetic {C r p t : ℝ} (ht : 1 ≤ t)
    (hdegree : 2*p+t ≤ 2*r+3)
    (hbudget : r*t ≤ C*t+(t-1)*p) :
    2*r ≤ C^2+4*C+1 := by
  have hp := mul_le_mul_of_nonneg_left hdegree (show 0 ≤ t-1 by linarith)
  nlinarith [sq_nonneg (t-C-2)]

/-- The same barrier holds for the average target degree; equal degrees
are not required. Here s is the sum of all target degrees. -/
lemma certificate_total_budget_arithmetic {C s p t : ℝ} (ht : 1 ≤ t)
    (hdegree : (2*p+t)*t ≤ s+3*t)
    (hbudget : s ≤ 2*C*t+2*(t-1)*p) :
    s ≤ (C^2+4*C+1)*t := by
  have hp := mul_le_mul_of_nonneg_left hdegree (show 0 ≤ t-1 by linarith)
  have hb := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ t by linarith)
  nlinarith [mul_nonneg (show 0 ≤ t by linarith) (sq_nonneg (t-C-2))]

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Just before the last certified removal, the target degree must be at
least the number of targets minus one. After that removal it can be two
smaller; the constant three below accounts for this final step. -/
lemma packing_certificate_target_degree (he : ∀ x, Even (G.degree x))
    (T : Set V) (hT : 2 ≤ T.ncard) (p : ℕ) (hp : 0 < p)
    {a : V} (ha : a ∈ T)
    (hconn : ∀ P : Finset G.Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) →
      (∀ H ∈ P, T ⊆ H.verts) → P.card < p →
      ∀ S : Set V, S.ncard < T.ncard →
      ∀ a ∈ T, ∀ b ∈ T, ∀ haS : a ∉ S, ∀ hbS : b ∉ S,
        ((G \ unionPieces G P).induce Sᶜ).Reachable ⟨a,haS⟩ ⟨b,hbS⟩) :
    2*p+T.ncard ≤ G.degree a+3 := by
  obtain ⟨P,hc,hd,hv,hcard⟩ := packing_through_set he T hT (p-1) (by
    intro P hc hd hv hn
    exact hconn P hc hd hv (hn.trans_le (Nat.sub_le p 1)))
  have hpiece : ∀ H ∈ P, H.degree a = 2 := by
    intro H hH
    have hh := (hc H hH).2 ⟨a,hv H hH ha⟩
    rw [Subgraph.coe_degree] at hh
    simpa only [Subgraph.degree,← Nat.card_eq_fintype_card] using hh
  have hu : (unionPieces G P).degree a = 2*P.card := by
    rw [unionPieces_degree G P hd a]
    rw [Finset.sum_congr rfl hpiece]
    simp [Nat.mul_comm]
  have hres := degree_sdiff_of_le (unionPieces_le G P) a
  have hh := target_degree_lower T (hconn P hc hd hv (by omega)) ha
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hu hres hh ⊢
  omega

/-- A common-cycle packing certified at every previous step by target
inseparability cannot make the usual incidence bound fit in C per target
unless the common initial degree is at most C^2+4C+1. This is a restriction
on this certificate and this cost bound, not on other ways to eliminate
vertices or to obtain common cycles. -/
lemma regular_packing_certificate_budget_degree (he : ∀ x, Even (G.degree x))
    (T : Set V) (hT : 2 ≤ T.ncard) (C r p : ℕ) (hp : 0 < p)
    (hdegree : ∀ a ∈ T, G.degree a = 2*r)
    (hconn : ∀ P : Finset G.Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) →
      (∀ H ∈ P, T ⊆ H.verts) → P.card < p →
      ∀ S : Set V, S.ncard < T.ncard →
      ∀ a ∈ T, ∀ b ∈ T, ∀ haS : a ∉ S, ∀ hbS : b ∉ S,
        ((G \ unionPieces G P).induce Sᶜ).Reachable ⟨a,haS⟩ ⟨b,hbS⟩)
    (hbudget : r*T.ncard ≤ C*T.ncard+(T.ncard-1)*p) :
    2*r ≤ C^2+4*C+1 := by
  obtain ⟨a,ha⟩ := (Set.ncard_pos (Set.toFinite T)).mp (by omega : 0 < T.ncard)
  have hd := packing_certificate_target_degree he T hT p hp ha hconn
  rw [hdegree a ha] at hd
  have ht : (1 : ℝ) ≤ T.ncard := by exact_mod_cast (show 1 ≤ T.ncard by omega)
  have hd' : (2 : ℝ)*p+T.ncard ≤ 2*r+3 := by exact_mod_cast hd
  have hb' : (r : ℝ)*T.ncard ≤ C*T.ncard+((T.ncard : ℝ)-1)*p := by
    have hh := (show (r*T.ncard : ℝ) ≤ C*T.ncard+((T.ncard-1 : ℕ) : ℝ)*p by
      exact_mod_cast hbudget)
    simpa only [Nat.cast_sub (show 1 ≤ T.ncard by omega),Nat.cast_one] using hh
  have hh := certificate_budget_arithmetic ht hd' hb'
  exact_mod_cast hh

/-- With the same repeated certificate and the ordinary incidence cost,
even unequal target degrees have average at most C^2+4C+1. -/
lemma packing_certificate_budget_degree_sum (he : ∀ x, Even (G.degree x))
    (T : Finset V) (hT : 2 ≤ T.card) (C p : ℕ) (hp : 0 < p)
    (hconn : ∀ P : Finset G.Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) →
      (∀ H ∈ P, (T : Set V) ⊆ H.verts) → P.card < p →
      ∀ S : Set V, S.ncard < T.card →
      ∀ a ∈ T, ∀ b ∈ T, ∀ haS : a ∉ S, ∀ hbS : b ∉ S,
        ((G \ unionPieces G P).induce Sᶜ).Reachable ⟨a,haS⟩ ⟨b,hbS⟩)
    (hbudget : (∑ a ∈ T, G.degree a) ≤ 2*C*T.card+2*(T.card-1)*p) :
    (∑ a ∈ T, G.degree a) ≤ (C^2+4*C+1)*T.card := by
  have hd (a : V) (ha : a ∈ T) : 2*p+T.card ≤ G.degree a+3 := by
    have hh := packing_certificate_target_degree he (T : Set V) (by simpa using hT)
      p hp ha (by simpa using hconn)
    simpa using hh
  have hs := Finset.sum_le_sum hd
  have hsum : (2*p+T.card)*T.card ≤ (∑ a ∈ T, G.degree a)+3*T.card := by
    simpa [Finset.sum_add_distrib,Nat.mul_comm] using hs
  have ht : (1 : ℝ) ≤ T.card := by exact_mod_cast (show 1 ≤ T.card by omega)
  have hd' : (2*(p : ℝ)+T.card)*T.card ≤ (∑ a ∈ T, (G.degree a : ℝ))+3*T.card := by
    exact_mod_cast hsum
  have hb' : (∑ a ∈ T, (G.degree a : ℝ)) ≤ 2*C*T.card+2*((T.card : ℝ)-1)*p := by
    have hh : (∑ a ∈ T, (G.degree a : ℝ)) ≤ 2*C*T.card+2*((T.card-1 : ℕ) : ℝ)*p := by
      exact_mod_cast hbudget
    simpa only [Nat.cast_sub (show 1 ≤ T.card by omega),Nat.cast_one] using hh
  have hh := certificate_total_budget_arithmetic ht hd' hb'
  exact_mod_cast hh

end Erdos184.InseparableCycle
