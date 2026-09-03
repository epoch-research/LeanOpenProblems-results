import Submission.BothLargePrimeLower

/-! Exact adjacent largest-prime-factor laws do not have dyadic endpoint
continuity in total variation. This is a limitation of a proof strategy,
not a disproof of the largest-prime comparison conjecture. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

/-- Zero-based adjacent pair, matching `bothAboveSet`. -/
def exactPrimePair (n : ℕ) : ℕ × ℕ :=
  (Nat.maxPrimeFac n, Nat.maxPrimeFac (n+1))

noncomputable def primePairProbability (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  (((range N).filter fun n => exactPrimePair n=t).card : ℝ)/N

noncomputable def primePairL1Distance (M N : ℕ) : ℝ :=
  ∑ t ∈ (range (max M N+1)) ×ˢ (range (max M N+1)),
    |primePairProbability M t-primePairProbability N t|

lemma exactPrimePair_coprime (n : ℕ) :
    (exactPrimePair n).1.Coprime (exactPrimePair n).2 :=
  Nat.Coprime.of_dvd Nat.maxPrimeFac_dvd Nat.maxPrimeFac_dvd
    (by simp)

/-- A large ordered pair cannot repeat within a shorter interval. -/
lemma exactPrimePair_unique (U m n : ℕ) (hm : m<U) (hn : n<U)
    (hprod : U ≤ (exactPrimePair n).1*(exactPrimePair n).2)
    (he : exactPrimePair m=exactPrimePair n) : m=n := by
  have hp : (exactPrimePair n).1 ∣ m := by
    rw [← he]
    exact Nat.maxPrimeFac_dvd
  have hq : (exactPrimePair n).2 ∣ m+1 := by
    rw [← he]
    exact Nat.maxPrimeFac_dvd
  have hp' : (exactPrimePair n).1 ∣ n := Nat.maxPrimeFac_dvd
  have hq' : (exactPrimePair n).2 ∣ n+1 := Nat.maxPrimeFac_dvd
  have h₁ := hp.modEq_zero_nat.trans hp'.zero_modEq_nat
  have h₂ := (hq.modEq_zero_nat.trans hq'.zero_modEq_nat).add_right_cancel' 1
  have hc := (Nat.modEq_and_modEq_iff_modEq_mul (exactPrimePair_coprime n)).mp ⟨h₁,h₂⟩
  exact hc.eq_of_lt_of_lt (hm.trans_le hprod) (hn.trans_le hprod)

lemma bothAboveSet_primePair_product (B N n : ℕ) (hn : n∈bothAboveSet B N) :
    (B+1)^2 ≤ (exactPrimePair n).1*(exactPrimePair n).2 := by
  obtain ⟨_,hp,hq⟩ := mem_filter.mp hn
  simpa only [pow_two,exactPrimePair] using
    Nat.mul_le_mul (Nat.succ_le_of_lt hp) (Nat.succ_le_of_lt hq)

lemma primePairProbability_unique (U N n : ℕ) (hNU : N≤U) (hn : n<N)
    (hprod : U ≤ (exactPrimePair n).1*(exactPrimePair n).2) :
    primePairProbability N (exactPrimePair n)=1/(N : ℝ) := by
  have hs : (range N).filter (fun m => exactPrimePair m=exactPrimePair n)={n} := by
    ext m
    simp only [mem_filter,mem_range,mem_singleton]
    constructor
    · rintro ⟨hm,he⟩
      exact exactPrimePair_unique U m n (hm.trans_le hNU) (hn.trans_le hNU) hprod he
    · rintro rfl
      exact ⟨hn,rfl⟩
  simp only [primePairProbability,hs,card_singleton,Nat.cast_one]

/-- The explicit lower bound uses a set of atoms with no repetitions up to
`2*N`. Their masses decrease exactly from `1/N` to `1/(2*N)`. -/
lemma primePairL1Distance_dyadic_lower (B N : ℕ) (hN : 0<N)
    (hprod : 2*N≤(B+1)^2) :
    ((bothAboveSet B N).card : ℝ)/(2*N) ≤ primePairL1Distance N (2*N) := by
  classical
  let S := (bothAboveSet B N).image exactPrimePair
  let T := (range (max N (2*N)+1)) ×ˢ (range (max N (2*N)+1))
  have hsub : S⊆T := by
    intro t ht
    obtain ⟨n,hn,rfl⟩ := mem_image.mp ht
    have hnN := mem_range.mp (mem_filter.mp hn).1
    have hp := Nat.maxPrimeFac_le (n := n)
    have hq := Nat.maxPrimeFac_le (n := n+1)
    apply mem_product.mpr
    simp only [mem_range,exactPrimePair]
    constructor <;> omega
  have hinj : Set.InjOn exactPrimePair (bothAboveSet B N) := by
    intro m hm n hn he
    have hmN := mem_range.mp (mem_filter.mp hm).1
    have hnN := mem_range.mp (mem_filter.mp hn).1
    exact exactPrimePair_unique (2*N) m n (by omega) (by omega)
      (hprod.trans (bothAboveSet_primePair_product B N n hn)) he
  have ht (n : ℕ) (hn : n∈bothAboveSet B N) :
      |primePairProbability N (exactPrimePair n)-primePairProbability (2*N) (exactPrimePair n)|
        =1/(2*(N : ℝ)) := by
    have hnN := mem_range.mp (mem_filter.mp hn).1
    have hh := hprod.trans (bothAboveSet_primePair_product B N n hn)
    rw [primePairProbability_unique (2*N) N n (by omega) hnN hh,
      primePairProbability_unique (2*N) (2*N) n le_rfl (by omega) hh]
    push_cast
    have hNr : (0 : ℝ)<N := by exact_mod_cast hN
    have he : 1/(N : ℝ)-1/(2*(N : ℝ))=1/(2*(N : ℝ)) := by field_simp; ring
    rw [he,abs_of_pos (by positivity)]
  have he : (∑ t∈S, |primePairProbability N t-primePairProbability (2*N) t|)=
      ((bothAboveSet B N).card : ℝ)/(2*N) := by
    rw [sum_image hinj]
    calc
      _ = ∑ _n∈bothAboveSet B N, (1 : ℝ)/(2*N) := sum_congr rfl ht
      _ = _ := by simp only [sum_const,nsmul_eq_mul,mul_one_div]
  rw [← he]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)

/-- A genuine arithmetic failure of exact pair endpoint total-variation
continuity. In contrast, the one-coordinate marginal distance tends to zero. -/
theorem primePairL1Distance_dyadic_eventually_positive :
    ∀ᶠ N : ℕ in atTop, (1/40 : ℝ) ≤ primePairL1Distance N (2*N) := by
  filter_upwards [bothAbove_upperHalf_positive_proportion,
    ceilPowerCutoff_upperHalf_product_eventually,eventually_gt_atTop (0 : ℕ)]
    with N hmass hprod hN
  have hb := primePairL1Distance_dyadic_lower (ceilPowerCutoff (21/40) N) N hN hprod
  have he : ((bothAboveSet (ceilPowerCutoff (21/40) N) N).card : ℝ)/(2*N) =
      (((bothAboveSet (ceilPowerCutoff (21/40) N) N).card : ℝ)/N)/2 := by ring
  rw [he] at hb
  linarith

theorem primePairL1Distance_dyadic_not_zero :
    ¬ Tendsto (fun N => primePairL1Distance N (2*N)) atTop (𝓝 0) := by
  intro h
  have hh := ge_of_tendsto h primePairL1Distance_dyadic_eventually_positive
  norm_num at hh

#print axioms primePairL1Distance_dyadic_eventually_positive
#print axioms primePairL1Distance_dyadic_not_zero
end Erdos371
