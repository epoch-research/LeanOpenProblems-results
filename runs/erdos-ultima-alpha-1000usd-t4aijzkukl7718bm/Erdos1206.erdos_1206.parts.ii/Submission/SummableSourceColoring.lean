import Submission.SquarefreeColoringReduction

/-!
Positive-density extraction from finite cube-Sidon colorings of a summable
sieve source. This is a criterion, not a construction satisfying it.
-/

namespace Erdos1206.SummableSourceColoring
open Filter Finset
open scoped Classical Topology

/-- Divisors obtained by dividing a forbidden divisor by an integer at most N.
The value 1 is deliberately omitted. -/
def reducedDivisors (B : Set ℕ) (N : ℕ) : Set ℕ :=
  {d | 1 < d ∧ ∃ t : ℕ, 0 < t ∧ t ≤ N ∧ t*d ∈ B}

lemma reducedDivisors_summable {B : Set ℕ}
    (hB : Summable (fun n : ℕ => if n ∈ B then (1 : ℝ)/n else 0)) (N : ℕ) :
    Summable (fun d : ℕ => if d ∈ reducedDivisors B N then (1 : ℝ)/d else 0) := by
  classical
  have hs (t : ℕ) (ht : 0 < t) :
      Summable (fun d : ℕ => if t*d ∈ B then (1 : ℝ)/d else 0) := by
    have hi : Function.Injective (fun d : ℕ => t*d) := mul_right_injective₀ ht.ne'
    have hh := (hB.comp_injective hi).mul_left (t : ℝ)
    convert hh using 1
    funext d
    simp only [Function.comp_apply]
    by_cases htd : t*d ∈ B
    · simp only [if_pos htd, Nat.cast_mul]
      have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
      by_cases hd : d=0
      · simp [hd]
      · have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
        field_simp
    · simp [htd]
  have hsum : Summable (fun d : ℕ => ∑ t ∈ Icc 1 N,
      if t*d ∈ B then (1 : ℝ)/d else 0) :=
    summable_sum (fun t ht => hs t (mem_Icc.mp ht).1)
  apply Summable.of_nonneg_of_le (fun d => by split_ifs <;> positivity) _ hsum
  intro d
  by_cases hd : d ∈ reducedDivisors B N
  · rw [if_pos hd]
    obtain ⟨_,t,ht,htN,htB⟩ := hd
    have hh := single_le_sum (s := Icc 1 N)
      (f := fun t => if t*d ∈ B then (1 : ℝ)/d else 0)
      (fun t _ => by dsimp only; split_ifs <;> positivity) (mem_Icc.mpr ⟨ht,htN⟩)
    simpa only [if_pos htB] using hh
  · rw [if_neg hd]
    exact sum_nonneg (fun t _ => by split_ifs <;> positivity)

lemma reducedDivisors_preserve {B : Set ℕ} {N q n : ℕ}
    (hq : q ∈ divisorAvoider (reducedDivisors B N))
    (hn : n ∈ divisorAvoider B) (hnN : n ≤ N) : q*n ∈ divisorAvoider B := by
  refine ⟨Nat.mul_pos hq.1 hn.1, ?_⟩
  intro b hb hbnq
  have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbnq (Nat.mul_pos hq.1 hn.1)
  let g := Nat.gcd b n
  let d := b/g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right b hn.1
  have hgN : g ≤ N := (Nat.gcd_le_right b hn.1).trans hnN
  have hgd : g*d=b := Nat.mul_div_cancel' (Nat.gcd_dvd_left b n)
  have hdpos : 0 < d := Nat.div_pos (Nat.gcd_le_left n hbpos) hgpos
  have hd1 : d ≠ 1 := by
    intro he
    rw [he,mul_one] at hgd
    apply hn.2 b hb
    rw [← hgd]
    exact Nat.gcd_dvd_right b n
  have hdd : d ∣ q := by
    apply (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left b n) hgpos).mpr
    exact Nat.dvd_gcd_mul_iff_dvd_mul.mpr (by simpa [mul_comm] using hbnq)
  apply hq.2 d ⟨by omega,g,hgpos,hgN,by rwa [hgd]⟩ hdd

lemma summable_source_prefix_multipliers {B : Set ℕ}
    (hB : Summable (fun n : ℕ => if n ∈ B then (1 : ℝ)/n else 0)) (N : ℕ) :
    ∃ D : Set ℕ, 0 < D.lowerDensity ∧
      ∀ q ∈ D, 0 < q ∧ ∀ n ∈ divisorAvoider B,
        n ≤ N → q*n ∈ divisorAvoider B := by
  let D := divisorAvoider (reducedDivisors B N)
  have h1 : 1 ∉ reducedDivisors B N := by rintro ⟨h,_⟩; omega
  refine ⟨D,divisorAvoider_positive_density_of_summable h1
    (reducedDivisors_summable hB N),?_⟩
  intro q hq
  exact ⟨hq.1,fun n hn hnN => reducedDivisors_preserve hq hn hnN⟩

/-- The source condition needed for lower-density extraction. -/
structure PositivePrefixMultipliers (S : Set ℕ) : Prop where
  one_mem : 1 ∈ S
  positive : ∀ n ∈ S, 0 < n
  multipliers : ∀ N : ℕ, ∃ D : Set ℕ, 0 < D.lowerDensity ∧
    ∀ q ∈ D, 0 < q ∧ ∀ n ∈ S, n ≤ N → q*n ∈ S

lemma summable_source_multipliers {B : Set ℕ} (h1 : 1 ∉ B)
    (hB : Summable (fun n : ℕ => if n ∈ B then (1 : ℝ)/n else 0)) :
    PositivePrefixMultipliers (divisorAvoider B) := by
  refine ⟨?_,fun n hn => hn.1,summable_source_prefix_multipliers hB⟩
  refine ⟨by omega,?_⟩
  intro b hb hbd
  exact h1 ((Nat.dvd_one.mp hbd) ▸ hb)

def GoodColoringOn {ι : Type*} (S : Set ℕ) (c : ℕ → ι) : Prop :=
  ∀ i, IsSidon ((fun n : ℕ => n^3) '' {n | n ∈ S ∧ c n=i})

private lemma erase_source_color {S : Set ℕ} (hM : PositivePrefixMultipliers S)
    {k : ℕ} {c : ℕ → Fin k} {C : Finset (Fin k)} (hc : GoodColoringOn S c)
    (hC : ∀ n ∈ S, c n ∈ C) (i : Fin k)
    (hlow : ¬ 0 < ({n | n ∈ S ∧ c n=i} : Set ℕ).lowerDensity) :
    ∃ d : ℕ → Fin k, GoodColoringOn S d ∧ ∀ n ∈ S, d n ∈ C.erase i := by
  classical
  have hex (N : ℕ) : ∃ q : ℕ, 0 < q ∧
      (∀ n ∈ S, n ≤ N+1 → q*n ∈ S) ∧
      ∀ n ∈ S, n ≤ N+1 → c (q*n) ≠ i := by
    obtain ⟨D,hDden,hD⟩ := hM.multipliers (N+1)
    by_contra hnot
    have hcover : ∀ q ∈ D, ∃ m : ℕ, 0 < m ∧ m ≤ N+1 ∧
        m*q ∈ ({n | n ∈ S ∧ c n=i} : Set ℕ) := by
      intro q hq
      have hh : ¬ ∀ n ∈ S, n ≤ N+1 → c (q*n) ≠ i := by
        intro hh
        exact hnot ⟨q,(hD q hq).1,(hD q hq).2,hh⟩
      push_neg at hh
      obtain ⟨m,hm,hmN,hmc⟩ := hh
      refine ⟨m,hM.positive m hm,hmN,?_⟩
      simpa only [mul_comm] using And.intro ((hD q hq).2 m hm hmN) hmc
    exact hlow (positive_density_of_dilation_cover_on hDden (by omega) hcover)
  choose q hq hpres havoid using hex
  let f : ℕ → ℕ → Fin k := fun j n => c (q j*n)
  obtain ⟨d,φ,hφ,hd⟩ := SeqCompactSpace.tendsto_subseq f
  have hevent (n : ℕ) : ∀ᶠ j in atTop, f (φ j) n=d n := by
    have hn := (tendsto_pi_nhds.mp hd) n
    exact hn.eventually (isOpen_discrete {d n} |>.mem_nhds (by simp))
  refine ⟨d,?_,?_⟩
  · intro i
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ _ ⟨r,hr,rfl⟩ _ ⟨s,hs,rfl⟩ heq
    have hlarge : ∀ᶠ j : ℕ in atTop, a+b+r+s ≤ φ j :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop (a+b+r+s))
    obtain ⟨j,hj,hja,hjb,hjr,hjs⟩ :=
      (hlarge.and ((hevent a).and ((hevent b).and ((hevent r).and (hevent s))))).exists
    change c (q (φ j)*a)=d a at hja
    change c (q (φ j)*b)=d b at hjb
    change c (q (φ j)*r)=d r at hjr
    change c (q (φ j)*s)=d s at hjs
    have heq' : (q (φ j)*a)^3+(q (φ j)*r)^3 =
        (q (φ j)*b)^3+(q (φ j)*s)^3 := by
      simpa only [mul_pow,← mul_add] using congrArg (fun n : ℕ => q (φ j)^3*n) heq
    have hh := hc i
      _ ⟨q (φ j)*a,⟨hpres (φ j) a ha.1 (by omega),hja.trans ha.2⟩,rfl⟩
      _ ⟨q (φ j)*b,⟨hpres (φ j) b hb.1 (by omega),hjb.trans hb.2⟩,rfl⟩
      _ ⟨q (φ j)*r,⟨hpres (φ j) r hr.1 (by omega),hjr.trans hr.2⟩,rfl⟩
      _ ⟨q (φ j)*s,⟨hpres (φ j) s hs.1 (by omega),hjs.trans hs.2⟩,rfl⟩ heq'
    simp only [mul_pow] at hh
    have hqp : 0 < q (φ j)^3 := pow_pos (hq (φ j)) _
    rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left hqp h₁,Nat.eq_of_mul_eq_mul_left hqp h₂⟩
    · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left hqp h₁,Nat.eq_of_mul_eq_mul_left hqp h₂⟩
  · intro n hn
    have hlarge : ∀ᶠ j : ℕ in atTop, n ≤ φ j :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop n)
    obtain ⟨j,hj,hjn⟩ := ((hevent n).and hlarge).exists
    change c (q (φ j)*n)=d n at hj
    apply mem_erase.mpr
    constructor
    · rw [← hj]
      exact havoid (φ j) n hn (by omega)
    · rw [← hj]
      exact hC _ (hpres (φ j) n hn (by omega))

/-- Finite coloring on any source with positive-density prefix multipliers
suffices. No such coloring is constructed here. -/
theorem finite_source_coloring_suffices {S : Set ℕ} (hM : PositivePrefixMultipliers S)
    {k : ℕ} (c : ℕ → Fin k) (hc : GoodColoringOn S c) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a^3) '' A) := by
  classical
  have hmain : ∀ C : Finset (Fin k), ∀ c : ℕ → Fin k,
      GoodColoringOn S c → (∀ n ∈ S, c n ∈ C) →
      ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
        IsSidon ((fun a : ℕ => a^3) '' A) := by
    intro C
    induction C using Finset.strongInductionOn with
    | _ C ih =>
      intro c hc hC
      let i := c 1
      by_cases hden : 0 < ({n | n ∈ S ∧ c n=i} : Set ℕ).lowerDensity
      · refine ⟨{n | n ∈ S ∧ c n=i},?_,hden,hc i⟩
        by_contra hfin
        have hz : ({n | n ∈ S ∧ c n=i} : Set ℕ).lowerDensity=0 :=
          (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
        rw [hz] at hden
        exact (lt_irrefl 0) hden
      · obtain ⟨d,hd,hdC⟩ := erase_source_color hM hc hC i hden
        exact ih (C.erase i) (erase_ssubset (hC 1 hM.one_mem)) d hd hdC
  exact hmain Finset.univ c hc (by simp)

/-- A finite coloring plus a reciprocal-summable divisor deletion suffices.
The bound on the reciprocal sum need not be less than one. -/
theorem finite_coloring_summable_source_suffices {B : Set ℕ} (h1 : 1 ∉ B)
    (hB : Summable (fun n : ℕ => if n ∈ B then (1 : ℝ)/n else 0))
    {k : ℕ} (c : ℕ → Fin k) (hc : GoodColoringOn (divisorAvoider B) c) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a^3) '' A) :=
  finite_source_coloring_suffices (summable_source_multipliers h1 hB) c hc

/-- A finite coloring after deletion of the multiples of a finite divisor set. -/
def FiniteColoredSieve {k : ℕ} (N : ℕ) (B : Finset ℕ) (c : ℕ → Fin k) : Prop :=
  ∀ i, IsSidon ((fun n : ℕ => n^3) ''
    {n | 0 < n ∧ n ≤ N ∧ c n=i ∧ ∀ d ∈ B, ¬ d ∣ n})

/-- Joint compactness of the colors and forbidden divisors. Both the number
of colors and the reciprocal-cost bound must be independent of the cutoff. -/
theorem colored_sieve_compactness (k : ℕ) (C : ℝ)
    (h : ∀ N : ℕ, ∃ B : Finset ℕ, ∃ c : ℕ → Fin k,
      1 ∉ B ∧ (∑ d ∈ B, (1 : ℝ)/d) ≤ C ∧ FiniteColoredSieve N B c) :
    ∃ B : Set ℕ, ∃ c : ℕ → Fin k, 1 ∉ B ∧
      Summable (fun n : ℕ => if n ∈ B then (1 : ℝ)/n else 0) ∧
      GoodColoringOn (divisorAvoider B) c := by
  classical
  choose B c h1 hcost hgood using h
  let x : ℕ → ℕ → Bool × Fin k := fun N n => (decide (n ∈ B N),c N n)
  obtain ⟨f,φ,hφ,hf⟩ := SeqCompactSpace.tendsto_subseq x
  let D : Set ℕ := {n | (f n).1=true}
  let e : ℕ → Fin k := fun n => (f n).2
  have hevent (n : ℕ) : ∀ᶠ j in atTop,
      (n ∈ B (φ j) ↔ n ∈ D) ∧ c (φ j) n=e n := by
    have hh : ∀ᶠ j in atTop, x (φ j) n=f n := by
      have hn := (tendsto_pi_nhds.mp hf) n
      exact hn.eventually (isOpen_discrete {f n} |>.mem_nhds (by simp))
    filter_upwards [hh] with j hj
    have hb : decide (n ∈ B (φ j))=(f n).1 := congrArg Prod.fst hj
    have hc : c (φ j) n=e n := congrArg Prod.snd hj
    refine ⟨?_,hc⟩
    change (n ∈ B (φ j) ↔ (f n).1=true)
    rw [← hb]
    simp
  have hpre (M : ℕ) : ∃ j : ℕ, M ≤ φ j ∧ ∀ n ≤ M,
      (n ∈ B (φ j) ↔ n ∈ D) ∧ c (φ j) n=e n := by
    have hh : ∀ᶠ j in atTop, ∀ n ∈ range (M+1),
        (n ∈ B (φ j) ↔ n ∈ D) ∧ c (φ j) n=e n :=
      (Finset.eventually_all _).mpr (fun n _ => hevent n)
    have hb : ∀ᶠ j : ℕ in atTop, M ≤ φ j :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop M)
    obtain ⟨j,hj,hjn⟩ := (hb.and hh).exists
    exact ⟨j,hj,fun n hn => hjn n (mem_range.mpr (by omega))⟩
  refine ⟨D,e,?_,?_,?_⟩
  · obtain ⟨j,_,hj⟩ := hpre 1
    intro hD
    exact h1 (φ j) ((hj 1 le_rfl).1.mpr hD)
  · apply summable_of_sum_range_le (c := C)
    · intro n; split_ifs <;> positivity
    · intro M
      obtain ⟨j,_,hj⟩ := hpre M
      calc
        (∑ n ∈ range M, @ite ℝ (n ∈ D) (Classical.propDecidable _) (1/n) 0) =
            ∑ n ∈ (range M).filter (fun n => n ∈ B (φ j)), (1 : ℝ)/n := by
          rw [sum_filter]
          apply sum_congr rfl
          intro n hn
          have hh := (hj n (mem_range.mp hn).le).1
          by_cases hd : n ∈ D
          · have hb := hh.mpr hd
            simp [hd,hb]
          · have hb : n ∉ B (φ j) := fun h => hd (hh.mp h)
            simp [hd,hb]
        _ ≤ ∑ n ∈ B (φ j), (1 : ℝ)/n := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro n hn; exact (mem_filter.mp hn).2
          · intro n _ _; positivity
        _ ≤ C := hcost (φ j)
  · intro i
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ _ ⟨r,hr,rfl⟩ _ ⟨s,hs,rfl⟩ heq
    let M := a+b+r+s+1
    obtain ⟨j,hj,hjn⟩ := hpre M
    have hmem (n : ℕ) (hn : n ∈ divisorAvoider D ∧ e n=i) (hnM : n ≤ M) :
        0 < n ∧ n ≤ φ j ∧ c (φ j) n=i ∧ ∀ d ∈ B (φ j), ¬ d ∣ n := by
      refine ⟨hn.1.1,hnM.trans hj,(hjn n hnM).2.trans hn.2,?_⟩
      intro d hd hdn
      have hdM : d ≤ M := (Nat.le_of_dvd hn.1.1 hdn).trans hnM
      exact hn.1.2 d ((hjn d hdM).1.mp hd) hdn
    exact hgood (φ j) i
      _ ⟨a,hmem a ha (by dsimp [M]; omega),rfl⟩
      _ ⟨b,hmem b hb (by dsimp [M]; omega),rfl⟩
      _ ⟨r,hmem r hr (by dsimp [M]; omega),rfl⟩
      _ ⟨s,hmem s hs (by dsimp [M]; omega),rfl⟩ heq

/-- A uniform finite color-and-sieve construction is enough for the original
positive-lower-density conclusion. Its uniform hypothesis is not proved here. -/
theorem uniform_finite_colored_sieves_suffice (k : ℕ) (C : ℝ)
    (h : ∀ N : ℕ, ∃ B : Finset ℕ, ∃ c : ℕ → Fin k,
      1 ∉ B ∧ (∑ d ∈ B, (1 : ℝ)/d) ≤ C ∧ FiniteColoredSieve N B c) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a^3) '' A) := by
  obtain ⟨B,c,h1,hB,hc⟩ := colored_sieve_compactness k C h
  exact finite_coloring_summable_source_suffices h1 hB c hc

#print axioms summable_source_prefix_multipliers
#print axioms finite_coloring_summable_source_suffices
#print axioms colored_sieve_compactness
#print axioms uniform_finite_colored_sieves_suffice

end Erdos1206.SummableSourceColoring
