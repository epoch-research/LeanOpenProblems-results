import Submission.MixedDivisorCycleDichotomy

/-!
In a sufficiently narrow interval, exact equality of the two endpoint
products of a mixed walk forces equal traversal counts. This does not
force balance of the comparisons between its prime labels, and does not
exclude balanced mixed cycles.
-/
namespace Erdos371
open Finset
set_option autoImplicit false

noncomputable def consecutiveLogRatio (n : ℕ) : ℝ :=
  Real.log ((n+1 : ℝ)/(n : ℝ))

lemma consecutiveLogRatio_bounds (n : ℕ) (hn : 0 < n) :
    1/(n+1 : ℝ) ≤ consecutiveLogRatio n ∧ consecutiveLogRatio n ≤ 1/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < (n+1 : ℝ)/(n : ℝ) := div_pos (by positivity) hnR
  have hl := Real.one_sub_inv_le_log_of_pos hx
  have hu := Real.log_le_sub_one_of_pos hx
  have he1 : 1-((n+1 : ℝ)/(n : ℝ))⁻¹ = 1/(n+1 : ℝ) := by
    field_simp
    ring
  have he2 : (n+1 : ℝ)/(n : ℝ)-1 = 1/(n : ℝ) := by
    field_simp
    ring
  rw [he1] at hl
  rw [he2] at hu
  exact ⟨hl,hu⟩

lemma mixedCycle_log_difference (n : ℕ) (forward : Bool) (hn : 0 < n) :
    Real.log (mixedCycleTarget n forward : ℝ)-Real.log (mixedCycleSource n forward : ℝ) =
      if forward then consecutiveLogRatio n else -consecutiveLogRatio n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn1 : (n+1 : ℝ) ≠ 0 := by positivity
  cases forward <;>
    simp [mixedCycleTarget,mixedCycleSource,consecutiveLogRatio,Real.log_div hn1 hnR]

/-- Product equality balances the sums of logarithmic increments, not
necessarily their numbers when the indices range over a wide interval. -/
lemma mixed_equal_product_log_balance {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (forward : ι → Bool) (hn : ∀ i, 0 < n i)
    (heq : (∏ i, mixedCycleSource (n i) (forward i)) =
      (∏ i, mixedCycleTarget (n i) (forward i))) :
    (∑ i ∈ univ.filter (fun i => forward i = true), consecutiveLogRatio (n i)) =
      ∑ i ∈ univ.filter (fun i => forward i ≠ true), consecutiveLogRatio (n i) := by
  have hA (i : ι) : (mixedCycleSource (n i) (forward i) : ℝ) ≠ 0 := by
    have h := (hn i).trans_le (mixedCycleSource_bounds (n i) (forward i)).1
    exact_mod_cast h.ne'
  have hB (i : ι) : (mixedCycleTarget (n i) (forward i) : ℝ) ≠ 0 := by
    have h := (hn i).trans_le (mixedCycleTarget_bounds (n i) (forward i)).1
    exact_mod_cast h.ne'
  have hp : (∏ i, (mixedCycleSource (n i) (forward i) : ℝ)) =
      ∏ i, (mixedCycleTarget (n i) (forward i) : ℝ) := by exact_mod_cast heq
  have hh := congrArg Real.log hp
  rw [Real.log_prod (fun i _ => hA i),Real.log_prod (fun i _ => hB i)] at hh
  have hz : (∑ i, if forward i then consecutiveLogRatio (n i) else -consecutiveLogRatio (n i)) = 0 := by
    simp_rw [← mixedCycle_log_difference _ _ (hn _)]
    rw [sum_sub_distrib,hh,sub_self]
  have hf : (∑ i, if forward i then consecutiveLogRatio (n i) else -consecutiveLogRatio (n i)) =
      (∑ i ∈ univ.filter (fun i => forward i = true), consecutiveLogRatio (n i))-
        ∑ i ∈ univ.filter (fun i => forward i ≠ true), consecutiveLogRatio (n i) := by
    rw [sum_filter,sum_filter,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    cases forward i <;> simp
  rw [hf] at hz
  exact sub_eq_zero.mp hz

private lemma equal_counts_of_narrow (r s k L N : ℕ)
    (hcard : r+s=k) (_hL : 0 < L) (hLN : L ≤ N)
    (hnarrow : k*(N+1-L)<L)
    (hrs : r*L ≤ s*(N+1)) (hsr : s*L ≤ r*(N+1)) : r=s := by
  have hD : N+1-L+L=N+1 := Nat.sub_add_cancel (by omega)
  have hbound (a b : ℕ) (hab : a<b) (hak : a≤k)
      (hcross : b*L≤a*(N+1)) : False := by
    have h1 := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hab)
    have h2 := Nat.mul_le_mul_right (N+1-L) hak
    rw [← hD] at hcross
    nlinarith
  rcases lt_trichotomy r s with h | h | h
  · exact (hbound r s h (by omega) hsr).elim
  · exact h
  · exact (hbound s r h (by omega) hrs).elim

/-- If `k*(N+1-L)<L`, the logarithmic increment on one edge cannot be
compensated by the variation of the other `k` increments. -/
theorem narrow_equal_product_traversals_balanced {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (forward : ι → Bool) (L N : ℕ)
    (hL : 0 < L) (hLN : L ≤ N) (hn : ∀ i, L ≤ n i ∧ n i ≤ N)
    (hnarrow : Fintype.card ι*(N+1-L)<L)
    (heq : (∏ i, mixedCycleSource (n i) (forward i)) =
      (∏ i, mixedCycleTarget (n i) (forward i))) :
    (univ.filter (fun i => forward i = true)).card =
      (univ.filter (fun i => forward i ≠ true)).card := by
  let F : Finset ι := univ.filter (fun i => forward i = true)
  let G : Finset ι := univ.filter (fun i => forward i ≠ true)
  have hcard : F.card+G.card=Fintype.card ι := by
    simpa only [F,G,card_univ] using
      (card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i => forward i = true))
  have hlR : (0 : ℝ) < L := by exact_mod_cast hL
  have hN1 : (0 : ℝ) < N+1 := by positivity
  have hw (i : ι) : 1/(N+1 : ℝ) ≤ consecutiveLogRatio (n i) ∧
      consecutiveLogRatio (n i) ≤ 1/(L : ℝ) := by
    have hni := hL.trans_le (hn i).1
    have h := consecutiveLogRatio_bounds (n i) hni
    constructor
    · exact (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n i+1)
        (by exact_mod_cast Nat.add_le_add_right (hn i).2 1)).trans h.1
    · exact h.2.trans (one_div_le_one_div_of_le hlR (by exact_mod_cast (hn i).1))
  have he : (∑ i ∈ F, consecutiveLogRatio (n i)) = ∑ i ∈ G, consecutiveLogRatio (n i) :=
    mixed_equal_product_log_balance n forward (fun i => hL.trans_le (hn i).1) heq
  have hsum (S : Finset ι) :
      (S.card : ℝ)/(N+1) ≤ ∑ i ∈ S, consecutiveLogRatio (n i) ∧
      (∑ i ∈ S, consecutiveLogRatio (n i)) ≤ (S.card : ℝ)/L := by
    constructor
    · simpa [mul_one_div] using sum_le_sum (s := S) (fun i _ => (hw i).1)
    · simpa [mul_one_div] using sum_le_sum (s := S) (fun i _ => (hw i).2)
  have hFG : (F.card : ℝ)/(N+1) ≤ (G.card : ℝ)/L :=
    (hsum F).1.trans (he ▸ (hsum G).2)
  have hGF : (G.card : ℝ)/(N+1) ≤ (F.card : ℝ)/L :=
    (hsum G).1.trans (he.symm ▸ (hsum F).2)
  have hFGn : F.card*L ≤ G.card*(N+1) := by
    exact_mod_cast (div_le_div_iff₀ hN1 hlR).mp hFG
  have hGFn : G.card*L ≤ F.card*(N+1) := by
    exact_mod_cast (div_le_div_iff₀ hN1 hlR).mp hGF
  exact equal_counts_of_narrow F.card G.card (Fintype.card ι) L N hcard hL hLN hnarrow hFGn hGFn

theorem narrow_equal_product_card_even {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (forward : ι → Bool) (L N : ℕ)
    (hL : 0 < L) (hLN : L ≤ N) (hn : ∀ i, L ≤ n i ∧ n i ≤ N)
    (hnarrow : Fintype.card ι*(N+1-L)<L)
    (heq : (∏ i, mixedCycleSource (n i) (forward i)) =
      (∏ i, mixedCycleTarget (n i) (forward i))) :
    Even (Fintype.card ι) := by
  have he := narrow_equal_product_traversals_balanced n forward L N hL hLN hn hnarrow heq
  have hc := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i => forward i = true)
  rw [card_univ,← he] at hc
  exact ⟨_,hc.symm⟩

/-- The product-equality alternative is impossible for an odd closed walk
in this narrow interval. Thus the size bound extends to arbitrary mixed
orientations in this specific setting. -/
theorem narrow_odd_divisor_cycle_product_bound {ι : Type*} [Fintype ι]
    (σ : ι ≃ ι) (n p : ι → ℕ) (forward : ι → Bool) (L N : ℕ)
    (hL : 0 < L) (hLN : L ≤ N) (hn : ∀ i, L ≤ n i ∧ n i ≤ N)
    (hnarrow : Fintype.card ι*(N+1-L)<L) (hodd : Odd (Fintype.card ι))
    (hp : ∀ i, p i ∣ mixedCycleSource (n i) (forward i))
    (hnext : ∀ i, p (σ i) ∣ mixedCycleTarget (n i) (forward i)) :
    (∏ i, p i) ≤ Fintype.card ι*(N+1)^(Fintype.card ι-1) := by
  rcases mixed_divisor_cycle_dichotomy σ n p forward N (fun i => (hn i).2) hp hnext with he | hb
  · obtain ⟨a,ha⟩ := narrow_equal_product_card_even n forward L N hL hLN hn hnarrow he
    obtain ⟨b,hb⟩ := hodd
    omega
  · exact hb

/-- In particular, the actual largest-prime-factor label product obeys the
same bound for odd walks. No such extension is asserted for balanced even
walks, which the explicit mixed-cycle examples show can exist. -/
theorem actual_narrow_odd_cycle_product_bound {ι : Type*} [Fintype ι]
    (σ : ι ≃ ι) (n : ι → ℕ) (forward : ι → Bool) (L N : ℕ)
    (hL : 0 < L) (hLN : L ≤ N) (hn : ∀ i, L ≤ n i ∧ n i ≤ N)
    (hnarrow : Fintype.card ι*(N+1-L)<L) (hodd : Odd (Fintype.card ι))
    (hclose : ∀ i,
      Nat.maxPrimeFac (mixedCycleTarget (n i) (forward i)) =
      Nat.maxPrimeFac (mixedCycleSource (n (σ i)) (forward (σ i)))) :
    (∏ i, Nat.maxPrimeFac (mixedCycleSource (n i) (forward i))) ≤
      Fintype.card ι*(N+1)^(Fintype.card ι-1) := by
  apply narrow_odd_divisor_cycle_product_bound σ n
    (fun i => Nat.maxPrimeFac (mixedCycleSource (n i) (forward i))) forward L N
    hL hLN hn hnarrow hodd (fun _ => Nat.maxPrimeFac_dvd)
  intro i
  rw [← hclose i]
  exact Nat.maxPrimeFac_dvd

#print axioms mixed_equal_product_log_balance
#print axioms narrow_equal_product_traversals_balanced
#print axioms actual_narrow_odd_cycle_product_bound
end Erdos371
