import Submission.FixedToleranceCompletionExplore

/-! A count-only sufficient condition for logarithmic completion. The
exceptional-count exponent may vary with each fixed tolerance. -/
namespace Erdos66CountingPowerCompletion
open Filter AdditiveCombinatorics Erdos66Counting Erdos66ClippedRepair
  Erdos66FixedToleranceCompletion
open scoped Classical Topology
set_option maxHeartbeats 2000000

/-- Polynomial count growth of exponent theta implies summability against
every strictly larger reciprocal power. -/
lemma power_summable_of_count_bound (E : Set ℕ) (θ s K : ℝ)
    (hθ : 0<θ) (hs : θ<s) (hK : 0<K)
    (hcount : ∀ᶠ N : ℕ in atTop, (count E N : ℝ)≤K*((N:ℝ)+2)^θ) :
    Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2)^s else 0) := by
  rcases E.finite_or_infinite with hE | hE
  · apply summable_of_finite_support
    apply hE.subset
    intro n hn
    by_contra he
    exact hn (if_neg he)
  · letI : Infinite E := hE.to_subtype
    let e : ℕ ≃o E := Nat.Subtype.orderIsoOfNat E
    let a : ℕ → ℕ := fun k ↦ (e k).val
    have ha : StrictMono a := fun i j hij ↦ e.strictMono hij
    have har : Set.range a=E := by
      ext n
      constructor
      · rintro ⟨k,rfl⟩
        exact (e k).property
      · intro hn
        obtain ⟨k,hk⟩ := e.surjective ⟨n,hn⟩
        exact ⟨k,congrArg Subtype.val hk⟩
    have hac (k : ℕ) : k≤count E (a k) := by
      have hh := Finset.card_le_card_of_injOn (s := Finset.range k)
        (t := cutoff E (a k)) a
        (fun i hi ↦ mem_cutoff.mpr ⟨ha (Finset.mem_range.mp hi),(e i).property⟩)
        ha.injective.injOn
      simpa only [Finset.card_range,count] using hh
    let t := s/θ
    have ht : 1<t := (one_lt_div hθ).mpr hs
    have ht0 : 0<t := by linarith
    have hser := (Real.summable_one_div_nat_rpow.mpr ht).mul_left (K^t)
    have hcomp : Summable (fun k ↦ 1/((a k:ℝ)+2)^s) := by
      apply hser.of_norm_bounded_eventually_nat
      filter_upwards [ha.tendsto_atTop.eventually hcount,eventually_ge_atTop 1] with k hk hk1
      have hak : (k:ℝ)≤count E (a k) := by exact_mod_cast hac k
      have hbase : (k:ℝ)≤K*((a k:ℝ)+2)^θ := hak.trans hk
      have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (α := ℝ) k) hbase ht0.le
      rw [Real.mul_rpow hK.le (Real.rpow_nonneg (by positivity) θ),
        ←Real.rpow_mul (by positivity : (0:ℝ)≤(a k:ℝ)+2),
        show θ*t=s by dsimp [t]; field_simp] at hpow
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hkp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
      rw [mul_one_div]
      apply (div_le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) s)
        (Real.rpow_pos_of_pos hkp t)).mpr
      simpa only [one_mul] using hpow
    apply (ha.injective.summable_iff (fun n hn ↦ by rw [har] at hn; exact if_neg hn)).mp
    have hea (k : ℕ) : a k∈E := (e k).property
    simpa only [Function.comp_def,hea,if_true] using hcomp

/-- The same exponent need not control all tolerances. Each lower-deviation
set may have a different count exponent below one half. -/
theorem completion_of_tolerance_dependent_count_bounds (A : Set ℕ) (c : ℝ) (hc : 0≤c)
    (hu : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop,
      (sumRep A n : ℝ)≤(c+ε)*logScale n)
    (hl : ∀ ε : ℝ, 0<ε → ∃ θ K : ℝ, 0<θ ∧ θ<1/2 ∧ 0<K ∧
      ∀ᶠ N : ℕ in atTop,
        (count {n | (sumRep A n : ℝ)≤(c-ε)*logScale n} N : ℝ)≤K*((N:ℝ)+2)^θ) :
    ∃ B : Set ℕ, A⊆B ∧
      Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 c) := by
  apply completion_of_tolerance_dependent_power_costs A c hc hu
  intro ε hε
  obtain ⟨θ,K,hθ,hθhalf,hK,hh⟩ := hl ε hε
  let s := (θ+1/2)/2
  have hθs : θ<s := by dsimp [s]; linarith
  have hshalf : s<1/2 := by dsimp [s]; linarith
  refine ⟨1-s,by linarith,by linarith,?_⟩
  have hs := power_summable_of_count_bound {n | (sumRep A n : ℝ)≤(c-ε)*logScale n}
    θ s K hθ hθs hK hh
  simpa only [sub_sub_cancel] using hs

end Erdos66CountingPowerCompletion
