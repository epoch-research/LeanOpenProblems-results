import Submission.DigitMemoryParametersExplore

/-! A quantitative lower bound for nonuniform digit-program width. The
state type can change arbitrarily with word length. This is a necessary
complexity condition, not a negation of the unrestricted conjecture. -/
namespace Erdos66DigitMemoryLower
open Filter AdditiveCombinatorics Erdos66Counting Erdos66DfaCounting
  Erdos66LayeredPath Erdos66LayeredDigitProgram Erdos66DigitBlocking
  Erdos66DigitMemoryParameters Erdos66LayeredDigitAsymptotic
open scoped Topology Classical
set_option maxHeartbeats 2800000
universe u
variable {b : ℕ}

lemma grouped_prefix_card_bound {σ : Type u} [Fintype σ]
    (hb : 1 < b) {d : ℕ} (hbd : 1 < b^d) (k : ℕ)
    (E : ℕ → σ → Fin b → σ → Prop) (initial : σ) (T : Set σ) (A : Set ℕ)
    (hrec : ∀ n, n<b^(d*k) → (n∈A ↔ ∃ z∈T,
      Erdos66LayeredPath.Path E 0 (finWord hb (d*k) n) initial z))
    (M : ℕ) (hM : ∀ n<2*b^(d*k), sumRep A n≤M) :
    count A (b^(d*k))≤(Fintype.card σ)^(k+1)*M^(b*d) := by
  let P := fromEdge (blockEdge hb d E) k initial T
  have heq : accepted P=cutoff A (b^(d*k)) := by
    ext n
    constructor
    · intro hn
      have hnlt : n<(b^d)^k := accepted_lt hbd P hn
      have hnlt' : n<b^(d*k) := by simpa only [pow_mul] using hnlt
      refine mem_cutoff.mpr ⟨hnlt',(hrec n hnlt').mpr ?_⟩
      exact (mem_block_program hb hbd E k n initial T hnlt).mp hn
    · intro hn
      obtain ⟨hnlt,hnA⟩ := mem_cutoff.mp hn
      have hnlt' : n<(b^d)^k := by simpa only [pow_mul] using hnlt
      apply (mem_block_program hb hbd E k n initial T hnlt').mpr
      exact (hrec n hnlt).mp hnA
  have hh := Erdos66DigitBoxExponent.accepted_card_le hbd
    (Erdos66DigitBoxExponent.grouped_base_bound b d) P A (by
      intro n hn
      rw [heq] at hn
      exact (mem_cutoff.mp hn).2) M (by simpa only [pow_mul] using hM)
  simpa only [heq,count] using hh

/-- At length 64*b*j*2^j, width at most b^(2^j) would give an overly small
prefix under the displayed representation cap. -/
lemma small_width_count_bound {σ : Type u} [Fintype σ] (hb : 1 < b) (j : ℕ)
    (E : ℕ → σ → Fin b → σ → Prop) (initial : σ) (T : Set σ) (A : Set ℕ)
    (hrec : ∀ n, n<b^(wordLength b j) → (n∈A ↔ ∃ z∈T,
      Erdos66LayeredPath.Path E 0 (finWord hb (wordLength b j) n) initial z))
    (hwidth : Fintype.card σ≤b^(2^j))
    (hM : ∀ n<2*b^(wordLength b j), sumRep A n≤b^(2*j)) :
    count A (b^(wordLength b j))≤b^((24*b*j+1)*2^j) := by
  have hbd : 1 < b^(blockLength j) := one_lt_pow₀ hb (by unfold blockLength; positivity)
  have hh := grouped_prefix_card_bound hb hbd (numBlocks b j) E initial T A
    (by simpa only [lengths_multiply] using hrec) (b^(2*j))
    (by simpa only [lengths_multiply] using hM)
  rw [lengths_multiply] at hh
  calc
    _ ≤ (Fintype.card σ)^(numBlocks b j+1)*(b^(2*j))^(b*blockLength j) := hh
    _ ≤ (b^(2^j))^(numBlocks b j+1)*(b^(2*j))^(b*blockLength j) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hwidth _)
    _ = _ := count_bound_algebra b j

/-- The program state type, transition rules, initial state and accepting
set may all vary with j. Only recognition of the indicated finite prefix
is required. -/
theorem eventual_width_lower_of_caps (hb : 1 < b)
    (σ : ℕ → Type u) [∀ j, Fintype (σ j)]
    (E : (j : ℕ) → ℕ → σ j → Fin b → σ j → Prop)
    (initial : (j : ℕ) → σ j) (T : (j : ℕ) → Set (σ j)) (A : Set ℕ)
    (hrec : ∀ j n, n<b^(wordLength b j) → (n∈A ↔ ∃ z∈T j,
      Erdos66LayeredPath.Path (E j) 0 (finWord hb (wordLength b j) n) (initial j) z))
    (hcap : ∀ᶠ j in atTop, ∀ n<2*b^(wordLength b j), sumRep A n≤b^(2*j))
    (M : ℕ) (hM : ∀ n≥M, 1≤sumRep A n) :
    ∀ᶠ j : ℕ in atTop, b^(2^j)<Fintype.card (σ j) := by
  filter_upwards [hcap,cutoff_large hb M,eventually_ge_atTop 1] with j hj hlarge hj1
  by_contra hwidth
  have hwidth' : Fintype.card (σ j)≤b^(2^j) := by omega
  have hcount := small_width_count_bound hb j (E j) (initial j) (T j) A (hrec j) hwidth' hj
  have hhalf := count_sq_half hb hj1 hcount
  have hbase := basis_count_bound A M hM (b^(wordLength b j))
  omega

/-- Any eventual additive basis with a global logarithmic cap requires
more than b^(2^j) states at length 64*b*j*2^j, for every sufficiently large j. -/
theorem eventual_width_lower_of_log_cap (hb : 1 < b)
    (σ : ℕ → Type u) [∀ j, Fintype (σ j)]
    (E : (j : ℕ) → ℕ → σ j → Fin b → σ j → Prop)
    (initial : (j : ℕ) → σ j) (T : (j : ℕ) → Set (σ j)) (A : Set ℕ)
    (hrec : ∀ j n, n<b^(wordLength b j) → (n∈A ↔ ∃ z∈T j,
      Erdos66LayeredPath.Path (E j) 0 (finWord hb (wordLength b j) n) (initial j) z))
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C)
    (hu : ∀ n, (sumRep A n:ℝ)≤K+C*Real.log ((n:ℝ)+2))
    (M : ℕ) (hM : ∀ n≥M, 1≤sumRep A n) :
    ∀ᶠ j : ℕ in atTop, b^(2^j)<Fintype.card (σ j) := by
  obtain ⟨L,hL⟩ := logarithmic_digit_cap hb hK hC hu
  apply eventual_width_lower_of_caps hb σ E initial T A hrec ?_ M hM
  filter_upwards [eventual_cap_bound hb L] with j hj
  intro n hn
  exact (hL (wordLength b j) n hn).trans hj

/-- A necessary condition for any witness of the original conjecture.
There is no fixed-width or fixed-transition assumption in this theorem. -/
theorem witness_eventual_width_lower (hb : 1 < b)
    (σ : ℕ → Type u) [∀ j, Fintype (σ j)]
    (E : (j : ℕ) → ℕ → σ j → Fin b → σ j → Prop)
    (initial : (j : ℕ) → σ j) (T : (j : ℕ) → Set (σ j)) (A : Set ℕ)
    (hrec : ∀ j n, n<b^(wordLength b j) → (n∈A ↔ ∃ z∈T j,
      Erdos66LayeredPath.Path (E j) 0 (finWord hb (wordLength b j) n) (initial j) z))
    (c : ℝ) (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ j : ℕ in atTop, b^(2^j)<Fintype.card (σ j) := by
  obtain ⟨K,C,hK,hC,hu⟩ := global_log_upper_bound ht
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((Erdos66Explore.sumRep_tendsto_atTop hc ht).eventually_ge_atTop 1)
  exact eventual_width_lower_of_log_cap hb σ E initial T A hrec hK hC.le hu M hM

end Erdos66DigitMemoryLower
