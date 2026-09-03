import FormalConjecturesUtil
import Submission.VariablePolynomialCertificate
import Submission.PolynomialInequalityCriterion

/-! Conditional rationality from varying polynomial inequalities. No sharp
polynomial relaxation for general graph extremal numbers is asserted here. -/

open Filter Asymptotics
open scoped Topology
namespace Erdos713VariablePolynomialInequality
open Erdos713PolynomialRate Erdos713PolynomialInequality
open Erdos713VariablePolynomialCertificate
set_option maxHeartbeats 1000000

/-- With a unique leading weight and subpolynomial integer coefficients, a
nonzero leading coefficient eventually determines the polynomial's sign. -/
lemma eventually_sign_of_leading {f : ℕ → ℝ} {α c : ℝ}
    (hc : 0 < c) (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (s : Finset (ℕ × ℕ)) (a : ℕ → (ℕ × ℕ) → ℤ) {r : ℕ × ℕ}
    (hr : r ∈ s) (hmax : ∀ p ∈ s.erase r, weight α p < weight α r)
    (ha : ∀ p ∈ s, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, |(a n p : ℝ)| ≤ (n : ℝ)^ε) :
    ∀ᶠ n : ℕ in atTop, a n r ≠ 0 →
      (0 ≤ eval s (fun p => (a n p : ℝ)) n (f n) ↔ 0 < a n r) := by
  classical
  let low : ℕ → ℝ := fun n => ∑ p ∈ s.erase r,
    (a n p : ℝ)*(n : ℝ)^p.1*(f n)^p.2/(n : ℝ)^(weight α r)
  let base : ℕ → ℝ := fun n =>
    (n : ℝ)^r.1*(f n)^r.2/(n : ℝ)^(weight α r)
  have hlow : Tendsto low atTop (𝓝 0) := by
    have hterms (p : ℕ × ℕ) (hp : p ∈ s.erase r) :=
      variable_term_limit p (ratio_limit hf) (hmax p hp)
        (ha p (Finset.mem_of_mem_erase hp))
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum (s.erase r) hterms
  have hbase : Tendsto base atTop (𝓝 (c^r.2)) := by
    have hp : Tendsto (fun n : ℕ => (n : ℝ)^(weight α r-weight α r))
        atTop (𝓝 (1 : ℝ)) := by simp
    simpa only [one_mul,mul_one] using term_limit (1 : ℝ) r (ratio_limit hf) hp
  have hcpos : 0 < c^r.2 := pow_pos hc _
  have hlowSmall : ∀ᶠ n : ℕ in atTop, |low n| < c^r.2/2 := by
    have h := hlow.abs
    simp only [abs_zero] at h
    exact h.eventually_lt_const (by positivity)
  have hbaseLarge : ∀ᶠ n : ℕ in atTop, c^r.2/2 < base n :=
    hbase.eventually_const_lt (by linarith)
  filter_upwards [hlowSmall,hbaseLarge,eventually_gt_atTop (0 : ℕ)]
    with n hsmall hlarge hnp hne
  have hnpR : (0 : ℝ) < n := by exact_mod_cast hnp
  have hpow := Real.rpow_pos_of_pos hnpR (weight α r)
  have hb : 0 < base n := by linarith
  have he : eval s (fun p => (a n p : ℝ)) n (f n)/(n : ℝ)^(weight α r) =
      low n+(a n r : ℝ)*base n := by
    dsimp [eval,low,base]
    rw [Finset.sum_div,← Finset.sum_erase_add _ _ hr]
    ring
  constructor
  · intro hnonneg
    have hn := div_nonneg hnonneg hpow.le
    rw [he] at hn
    by_contra h
    have hai : a n r ≤ -1 := by omega
    have har : (a n r : ℝ) ≤ -1 := by exact_mod_cast hai
    have hh := mul_le_mul_of_nonneg_right har hb.le
    have hlo := le_abs_self (low n)
    nlinarith
  · intro hpos
    have hai : 1 ≤ a n r := by omega
    have har : (1 : ℝ) ≤ a n r := by exact_mod_cast hai
    have hh := mul_le_mul_of_nonneg_right har hb.le
    have hlo := neg_abs_le (low n)
    have hn : 0 < low n+(a n r : ℝ)*base n := by nlinarith
    rw [← he] at hn
    exact ((div_pos_iff_of_pos_right hpow).mp hn).le

/-- A finite set of strict weight comparisons persists when the exponent is
increased slightly. This statement does not require irrationality. -/
lemma exists_larger_same_order (α : ℝ) (s : Finset (ℕ × ℕ)) :
    ∃ β : ℝ, α < β ∧ ∀ r ∈ s, ∀ p ∈ s,
      weight α p < weight α r → weight β p < weight β r := by
  have hloc : ∀ᶠ β : ℝ in 𝓝 α, ∀ r ∈ s, ∀ p ∈ s,
      weight α p < weight α r → weight β p < weight β r := by
    rw [Filter.eventually_all_finset]
    intro r _
    rw [Filter.eventually_all_finset]
    intro p _
    by_cases hlt : weight α p < weight α r
    · have hcont (t : ℕ × ℕ) : Continuous (fun β : ℝ => weight β t) := by
        dsimp [weight]
        fun_prop
      exact ((hcont p).continuousAt.tendsto.eventually_lt
        (hcont r).continuousAt.tendsto hlt).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hlt h).elim)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hloc
  refine ⟨α+ε/2,by linarith,hball ?_⟩
  rw [Real.dist_eq]
  have he : α+ε/2-α = ε/2 := by ring
  rw [he,abs_of_pos (by positivity : 0 < ε/2)]
  linarith

lemma eval_active_support (s : Finset (ℕ × ℕ)) (a : (ℕ × ℕ) → ℤ)
    (x y : ℝ) :
    eval (s.filter (fun p => a p ≠ 0)) (fun p => (a p : ℝ)) x y =
      eval s (fun p => (a p : ℝ)) x y := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpt
  have hap : a p = 0 := by
    by_contra h
    exact hpt (Finset.mem_filter.mpr ⟨hp,h⟩)
  simp [hap]

/-- Two pure-power sequences have the same eventual feasibility for one
varying polynomial when its integer coefficients are subpolynomial and the
exponents induce the same strict monomial order. -/
theorem eventually_same_feasibility {f g : ℕ → ℝ} {α β c d : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (hg : g ~[atTop] (fun n : ℕ => d*(n : ℝ)^β))
    (hirr : α ∉ Set.range ((↑) : ℚ → ℝ))
    (s : Finset (ℕ × ℕ)) (a : ℕ → (ℕ × ℕ) → ℤ)
    (ha : ∀ p ∈ s, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, |(a n p : ℝ)| ≤ (n : ℝ)^ε)
    (horder : ∀ r ∈ s, ∀ p ∈ s,
      weight α p < weight α r → weight β p < weight β r) :
    ∀ᶠ n : ℕ in atTop,
      (0 ≤ eval s (fun p => (a n p : ℝ)) n (f n) ↔
        0 ≤ eval s (fun p => (a n p : ℝ)) n (g n)) := by
  classical
  have hEach (t : Finset (ℕ × ℕ)) (ht : t ∈ s.powerset) :
      ∀ᶠ n : ℕ in atTop, t = s.filter (fun p => a n p ≠ 0) →
        (0 ≤ eval t (fun p => (a n p : ℝ)) n (f n) ↔
          0 ≤ eval t (fun p => (a n p : ℝ)) n (g n)) := by
    by_cases htne : t.Nonempty
    · have hts : t ⊆ s := Finset.mem_powerset.mp ht
      obtain ⟨r,hr,hmax⟩ := t.exists_max_image (weight α) htne
      have hstrict (p : ℕ × ℕ) (hp : p ∈ t.erase r) : weight α p < weight α r := by
        obtain ⟨hne,hpt⟩ := Finset.mem_erase.mp hp
        exact lt_of_le_of_ne (hmax p hpt) (fun he => hne (weight_injective hirr he))
      have hstrictβ (p : ℕ × ℕ) (hp : p ∈ t.erase r) : weight β p < weight β r :=
        horder r (hts hr) p (hts (Finset.mem_of_mem_erase hp)) (hstrict p hp)
      have hat := fun p hp => ha p (hts hp)
      filter_upwards [eventually_sign_of_leading hc hf t a hr hstrict hat,
        eventually_sign_of_leading hd hg t a hr hstrictβ hat] with n hnF hnG heq
      have hmem : r ∈ s.filter (fun p => a n p ≠ 0) := heq ▸ hr
      have har : a n r ≠ 0 := (Finset.mem_filter.mp hmem).2
      exact (hnF har).trans (hnG har).symm
    · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htne
      simp [ht0,eval]
  have hall := (Filter.eventually_all_finset s.powerset).mpr hEach
  filter_upwards [hall] with n hn
  have h := hn (s.filter (fun p => a n p ≠ 0))
    (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) rfl
  simpa only [eval_active_support] using h

/-- Uniform subpolynomial height permits an arbitrary index type of polynomial
inequalities; in particular, their number may grow with n. -/
theorem eventually_same_feasibility_uniform {I : Type*}
    {f g : ℕ → ℝ} {α β c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (hg : g ~[atTop] (fun n : ℕ => d*(n : ℝ)^β))
    (hirr : α ∉ Set.range ((↑) : ℚ → ℝ))
    (s : Finset (ℕ × ℕ)) (a : I → ℕ → (ℕ × ℕ) → ℤ)
    (ha : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ i p, p ∈ s → |(a i n p : ℝ)| ≤ (n : ℝ)^ε)
    (horder : ∀ r ∈ s, ∀ p ∈ s,
      weight α p < weight α r → weight β p < weight β r) :
    ∀ᶠ n : ℕ in atTop, ∀ i,
      (0 ≤ eval s (fun p => (a i n p : ℝ)) n (f n) ↔
        0 ≤ eval s (fun p => (a i n p : ℝ)) n (g n)) := by
  classical
  let Bad (n : ℕ) (i : I) : Prop :=
    ¬ (0 ≤ eval s (fun p => (a i n p : ℝ)) n (f n) ↔
        0 ≤ eval s (fun p => (a i n p : ℝ)) n (g n))
  let b : ℕ → (ℕ × ℕ) → ℤ := fun n =>
    if h : ∃ i, Bad n i then a (Classical.choose h) n else fun _ => 0
  have hb : ∀ p ∈ s, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, |(b n p : ℝ)| ≤ (n : ℝ)^ε := by
    intro p hp ε hε
    filter_upwards [ha ε hε] with n hn
    by_cases h : ∃ i, Bad n i
    · simpa only [b,dif_pos h] using hn (Classical.choose h) p hp
    · simp only [b,dif_neg h,Int.cast_zero,abs_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg n) ε
  filter_upwards [eventually_same_feasibility hc hd hf hg hirr s b hb horder] with n hn i
  by_contra hni
  have h : ∃ i, Bad n i := ⟨i,hni⟩
  have hbad := Classical.choose_spec h
  apply hbad
  simpa only [b,dif_pos h] using hn

/-- A constant-factor-sharp polynomial relaxation forces rational growth even
when its constraints vary with n and their number is unbounded. Their monomial
support must be fixed and their integer heights uniformly subpolynomial. -/
theorem rational_of_variable_sharp_relaxation {I : Type*}
    {f : ℕ → ℕ} {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hf : (fun n => (f n : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (s : Finset (ℕ × ℕ)) (a : I → ℕ → (ℕ × ℕ) → ℤ)
    (ha : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ i p, p ∈ s → |(a i n p : ℝ)| ≤ (n : ℝ)^ε)
    (hfeas : ∀ᶠ n : ℕ in atTop, ∀ i,
      0 ≤ eval s (fun p => (a i n p : ℝ)) n (f n))
    (K : ℝ)
    (hsharp : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (∀ i, 0 ≤ eval s (fun p => (a i n p : ℝ)) n m) → (m : ℝ) ≤ K*f n) :
    α ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  by_contra hirr
  obtain ⟨β,hαβ,horder⟩ := exists_larger_same_order α s
  have hβ : 0 < β := hα.trans hαβ
  have hsame := eventually_same_feasibility_uniform hc (by norm_num : (0 : ℝ) < 1)
    hf (floor_rpow_asymptotic hβ) hirr s a ha horder
  have hgt := eventually_floor_rpow_gt hf hαβ hβ K
  obtain ⟨n,hnfeas,hnsame,hnsharp,hngt⟩ :=
    (hfeas.and (hsame.and (hsharp.and hgt))).exists
  have hnle := hnsharp ⌊(n : ℝ)^β⌋₊ (fun i => (hnsame i).mp (hnfeas i))
  exact (not_lt_of_ge hnle) hngt

#print axioms eventually_sign_of_leading
#print axioms exists_larger_same_order
#print axioms eventually_same_feasibility
#print axioms eventually_same_feasibility_uniform
#print axioms rational_of_variable_sharp_relaxation
end Erdos713VariablePolynomialInequality
