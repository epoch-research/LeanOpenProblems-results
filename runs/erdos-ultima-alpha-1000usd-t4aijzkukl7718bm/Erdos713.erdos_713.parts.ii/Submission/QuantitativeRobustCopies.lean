import FormalConjecturesUtil
import Submission.RobustCopies

/-! Polynomial-size disjoint packings and transversal bounds from a strict
extremal exponent gap. These are necessary conditions, not rationality. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713RobustCopies

variable {U V W : Type*}

lemma bigO_eventually_lt_power {f : ℕ → ℝ} {r α b : ℝ} (hra : r < α) (hb : 0 < b)
    (h : f =O[atTop] (fun n : ℕ => (n : ℝ)^r)) :
    ∀ᶠ n : ℕ in atTop, f n < b*(n : ℝ)^α := by
  obtain ⟨C,hC⟩ := h.bound
  have htop := Erdos713FutureRecords.lower_ratio_top (f := fun n : ℕ => b*(n : ℝ)^α)
    hra hb Asymptotics.IsEquivalent.refl
  filter_upwards [hC,htop.eventually_gt_atTop C,eventually_gt_atTop (0 : ℕ)] with n hn hlarge hnp
  have hp : 0 < (n : ℝ)^r := Real.rpow_pos_of_pos (by exact_mod_cast hnp) r
  have hlow := (lt_div_iff₀ hp).mp hlarge
  rw [Real.norm_of_nonneg hp.le] at hn
  have hbound := (le_abs_self (f n)).trans (by simpa only [Real.norm_eq_abs] using hn)
  exact hbound.trans_lt hlow

lemma scaled_edge_gap (H : SimpleGraph W) (Q : SimpleGraph U) {α c r : ℝ}
    (hr : 0 ≤ r) (hra : r < α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hQ : (fun n : ℕ => (extremalNumber n Q : ℝ)) =O[atTop] (fun n => (n : ℝ)^r)) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      (envelope Q n : ℝ) < c/8*(n : ℝ)^α ∧
      c/2*(n : ℝ)^α < (extremalNumber n H : ℝ) := by
  have henv := bigO_eventually_lt_power hra (by positivity : 0 < c/8) (envelope_upper Q hr hQ)
  have hlow := (Erdos713FutureRecords.ratio_limit hH).eventually_const_lt
    (by linarith : c/2 < c)
  filter_upwards [henv,hlow,eventually_gt_atTop (0 : ℕ)] with n hn hlarge hnp
  refine ⟨hnp,hn,?_⟩
  exact (lt_div_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hnp) α)).mp hlarge

/-- An explicit polynomial-size packing, on every sufficiently dense host.
The positive constant is independent of the host and its order. -/
theorem polynomial_disjoint_copies [Fintype U] (H : SimpleGraph W) (Q : SimpleGraph U)
    {α c r : ℝ} (hr : 0 ≤ r) (hra : r < α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hQ : (fun n : ℕ => (extremalNumber n Q : ℝ)) =O[atTop] (fun n => (n : ℝ)^r)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      extremalNumber n H ≤ 2*Nat.card G.edgeSet →
        DisjointCopies ⌊δ*(n : ℝ)^(α-1)⌋₊ Q G := by
  let δ : ℝ := c/(8*((Fintype.card U : ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδq : δ*(Fintype.card U : ℝ) ≤ c/8 := by
    calc
      _ ≤ δ*((Fintype.card U : ℝ)+1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = _ := by dsimp [δ]; field_simp
  refine ⟨δ,hδ,?_⟩
  filter_upwards [scaled_edge_gap H Q hr hra hc hH hQ] with n hn
  intro G hG
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1
  let k : ℕ := ⌊δ*(n : ℝ)^(α-1)⌋₊
  have hfloor : (k : ℝ) ≤ δ*(n : ℝ)^(α-1) := Nat.floor_le (by positivity)
  have hbudget : (k : ℝ)*(Fintype.card U : ℝ)*(n : ℝ) ≤ c/8*(n : ℝ)^α := by
    calc
      _ ≤ (δ*(n : ℝ)^(α-1))*(Fintype.card U : ℝ)*(n : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg _)) hnR.le
      _ = (δ*(Fintype.card U : ℝ))*(n : ℝ)^α := by
        rw [Real.rpow_sub_one hnR.ne']
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hδq (Real.rpow_nonneg hnR.le _)
  have hG' : (extremalNumber n H : ℝ) ≤ 2*(Nat.card G.edgeSet : ℝ) := by exact_mod_cast hG
  have hbound : (envelope Q n : ℝ)+(k : ℝ)*(Fintype.card U : ℝ)*(n : ℝ) <
      (Nat.card G.edgeSet : ℝ) := by linarith [hn.2.1,hn.2.2]
  apply disjoint_copies_of_edge_bound Q G k
  simpa only [Fintype.card_fin] using (show envelope Q n+k*Fintype.card U*n < Nat.card G.edgeSet by
    exact_mod_cast hbound)

/-- Every vertex transversal of the Q copies has polynomial size. -/
theorem polynomial_transversal (H : SimpleGraph W) (Q : SimpleGraph U)
    {α c r : ℝ} (hr : 0 ≤ r) (hra : r < α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hQ : (fun n : ℕ => (extremalNumber n Q : ℝ)) =O[atTop] (fun n => (n : ℝ)^r)) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      extremalNumber n H ≤ 2*Nat.card G.edgeSet → ∀ S : Finset (Fin n),
        Q.Free (G.induce (S : Set (Fin n))ᶜ) →
          c/8*(n : ℝ)^(α-1) < (S.card : ℝ) := by
  filter_upwards [scaled_edge_gap H Q hr hra hc hH hQ] with n hn
  intro G hG S hS
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hdel : (Nat.card G.edgeSet : ℝ) ≤ (envelope Q n : ℝ)+(S.card : ℝ)*(n : ℝ) := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using edge_bound_after_deletion Q G S hS)
  have hG' : (extremalNumber n H : ℝ) ≤ 2*(Nat.card G.edgeSet : ℝ) := by exact_mod_cast hG
  have hlow : c/8*(n : ℝ)^α < (S.card : ℝ)*(n : ℝ) := by linarith [hn.2.1,hn.2.2]
  apply (mul_lt_mul_iff_left₀ hnR).mp
  calc
    _ = c/8*(n : ℝ)^α := by rw [Real.rpow_sub_one hnR.ne']; field_simp
    _ < _ := by simpa only [mul_comm (n : ℝ)] using hlow

/-- Specialization to rational-rate patterns contained in an irrational-rate
host. No rate for an identification quotient is presumed. -/
theorem known_subgraphs_polynomial [Fintype U] (H : SimpleGraph W) (Q : SimpleGraph U)
    {α c : ℝ} (ha : 1 ≤ α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hirr : α ∉ Set.range ((↑) : ℚ → ℝ)) (hQH : Q ⊑ H)
    {r : ℚ} (hQ : Erdos713Rate.HasRate Q (r : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      extremalNumber n H ≤ 2*Nat.card G.edgeSet →
        DisjointCopies ⌊δ*(n : ℝ)^(α-1)⌋₊ Q G := by
  have hrα : (r : ℝ) ≤ α := hQ.lower α ha
    ((Erdos713Rate.extremal_mono_bigO hQH).trans (Erdos713Rate.rate_of_asymptotic ha hc.ne' hH).upper)
  have hrα' : (r : ℝ) < α := lt_of_le_of_ne hrα (fun he => hirr ⟨r,he⟩)
  exact polynomial_disjoint_copies H Q (by linarith [hQ.one_le]) hrα' hc hH hQ.upper

/-- Both conclusions concern the same host, uniformly over all hosts
satisfying the lower edge bound. -/
theorem known_subgraphs_quantitative [Fintype U] (H : SimpleGraph W) (Q : SimpleGraph U)
    {α c : ℝ} (ha : 1 ≤ α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hirr : α ∉ Set.range ((↑) : ℚ → ℝ)) (hQH : Q ⊑ H)
    {r : ℚ} (hQ : Erdos713Rate.HasRate Q (r : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      extremalNumber n H ≤ 2*Nat.card G.edgeSet →
        DisjointCopies ⌊δ*(n : ℝ)^(α-1)⌋₊ Q G ∧
        ∀ S : Finset (Fin n), Q.Free (G.induce (S : Set (Fin n))ᶜ) →
          c/8*(n : ℝ)^(α-1) < (S.card : ℝ) := by
  have hrα : (r : ℝ) ≤ α := hQ.lower α ha
    ((Erdos713Rate.extremal_mono_bigO hQH).trans (Erdos713Rate.rate_of_asymptotic ha hc.ne' hH).upper)
  have hrα' : (r : ℝ) < α := lt_of_le_of_ne hrα (fun he => hirr ⟨r,he⟩)
  obtain ⟨δ,hδ,hpacking⟩ := known_subgraphs_polynomial H Q ha hc hH hirr hQH hQ
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hpacking,polynomial_transversal H Q (by linarith [hQ.one_le]) hrα' hc hH hQ.upper]
    with n hpack htrans
  exact fun G hG => ⟨hpack G hG,htrans G hG⟩

#print axioms known_subgraphs_quantitative
#print axioms polynomial_disjoint_copies
#print axioms polynomial_transversal
#print axioms known_subgraphs_polynomial
end Erdos713RobustCopies
