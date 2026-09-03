import Submission.KernelFamilyCompression

/-! Exact capped-retention budget step for a finite coordinate kernel.
Coordinate-family compression is an explicit hypothesis, supplied for weighted
coordinate-event decompositions by normalized_family_compression. -/
namespace Erdos7CappedBudgetStep
open scoped BigOperators
open Erdos7BackwardFamilyBudget Erdos7CappedRetentionRows
open Erdos7FiniteRetentionKernel Erdos7KernelFamilyCompression
set_option maxHeartbeats 2000000

theorem exists_kernel_budget_step {Ω A Ξ α β J : Type}
    [Fintype Ω] [Nonempty Ω] [Fintype A] [Fintype Ξ] [Fintype J] [Nonempty β]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ρ : A → ℝ)
    (hρ : ∀ y, 0 ≤ ρ y) (hρmass : (∑ y, ρ y)=1)
    (bad : Ω → A → Prop) [∀ x y, Decidable (bad x y)]
    (q c K : ℝ) (hq : 0 < q) (hc : 0 ≤ c) (k : Ω → ℝ)
    (hbad : ∀ x, (∑ y, if bad x y then ρ y else 0) ≤ k x/q)
    (R : ℕ) (tail : ℕ → ℝ) (htail : ∀ j, tail (j+1) ≤ tail j)
    (X : α → Ω → ℝ) (Y : β → Ξ → ℝ) (f : Ω × A → Ξ)
    (old : β → Option (Fin R) → α) (current : J → α)
    (U V F G : ℝ → ℝ) (lo hi lo' hi' : ℝ) (hlh : lo ≤ hi)
    (hU : ConvexOn ℝ Set.univ U) (hmU : Monotone U)
    (hV : ∀ t ∈ Set.Icc lo hi, 0 ≤ V t)
    (hF : ∀ t ∈ Set.Icc lo hi, U t+V t ≤ F t)
    (hk : ∀ x, k x ∈ Set.Icc lo hi)
    (hX : ∀ b d x, X (old b d) x ∈ Set.Icc lo hi)
    (hrange : ∀ (d : Option (Fin R)) t, t ∈ Set.Icc lo hi →
      multiplier d*t ∈ Set.Icc lo' hi')
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : (∑ j, w j) ≤ 1)
    (hJensen : ∀ x, k x ≤ (1-∑ j, w j)*lo + ∑ j, w j*X (current j) x)
    (hcompression : ∀ (ν : Ω → A → ℝ), (∀ x y, 0 ≤ ν x y) →
      (∀ x y, ν x y ≤ c*μ x*ρ y) →
      (∀ x, (∑ y, ν x y)=μ x*retained q c K (k x)) →
      ∀ b (φ : ℝ → ℝ), ConvexOn ℝ Set.univ φ → Monotone φ →
      (∑ x, ∑ y, ν x y*φ (Y b (f (x,y)))) ≤
        ∑ x, μ x*(∑ d, coefficient (retained q c K (k x)) tail R d *
          φ (multiplier d*X (old b d) x)))
    (hdual : ∀ k ∈ Set.Icc lo hi, ∀ t ∈ Set.Icc lo hi,
      1-retained q c K k + (∑ d, coefficient (retained q c K k) tail R d *
        G (multiplier d*t)) ≤ U k+V t) :
    ∃ ν : Ω → A → ℝ,
      (∀ x y, 0 ≤ ν x y) ∧
      (∀ x y, ν x y ≤ c*μ x*ρ y) ∧
      (∀ x y, bad x y → ν x y=0) ∧
      (∀ x, (∑ y, ν x y)=μ x*retained q c K (k x)) ∧
      (HasBudget (push f (fun z : Ω × A => ν z.1 z.2)) Y G lo' hi' →
        HasBudget μ X F lo hi) := by
  classical
  have hα (x : Ω) : (∑ y, if bad x y then ρ y else 0) ≤ 1 := by
    calc
      _ ≤ ∑ y, ρ y := by
        apply Finset.sum_le_sum
        intro y _
        split_ifs
        · exact le_rfl
        · exact hρ y
      _ = _ := hρmass
  obtain ⟨ν, hν, hcap, hzero, hmass⟩ := exists_retention_kernel μ hμ ρ hρ hρmass
    bad (fun x => retained q c K (k x)) c hc (fun x => retained_nonneg q c K (k x))
    (fun x => retained_feasible q c K (k x) _ hc (hα x) (hbad x))
  refine ⟨ν, hν, hcap, hzero, hmass, ?_⟩
  intro hb
  have hb' := budget_of_push f (fun z : Ω × A => ν z.1 z.2) Y G lo' hi' hb
  obtain ⟨n, κ, row, hκ, hrow, heq, hrangeκ⟩ := exists_antitone_rows k
  let aa (r : ℕ) (d : Option (Fin R)) := coefficient (retained q c K (κ r)) tail R d
  let loss (r : ℕ) := 1-retained q c K (κ r)
  have haa (r : ℕ) (d : Option (Fin R)) : 0 ≤ aa r d :=
    coefficient_nonneg _ tail R htail d
  have hmaa (d : Option (Fin R)) : Monotone (fun r => aa r d) :=
    (capped_rows_antitone q c K hq hc tail R htail d).comp hκ
  apply mixture_budget_pullback μ hμ ν X (fun b z => Y b (f z)) old current
    aa multiplier multiplier_nonneg U V F G κ loss lo hi lo' hi' hlh haa hmaa
    hU hmU hV hF n row hrow hX hrange w hw hs
  · intro x
    rw [heq x]
    exact hJensen x
  · intro x
    dsimp only [loss]
    rw [heq x, hmass x]
    ring
  · intro b φ hφ hmφ
    simpa only [aa, heq] using hcompression ν hν hcap hmass b φ hφ hmφ
  · intro r _ t ht
    obtain ⟨x, hx⟩ := hrangeκ r
    have hmem : κ r ∈ Set.Icc lo hi := by rw [hx]; exact hk x
    exact hdual (κ r) hmem t ht
  · exact hb'

#print axioms exists_kernel_budget_step
end Erdos7CappedBudgetStep
