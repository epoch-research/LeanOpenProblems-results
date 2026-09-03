import Submission.DeficitFamilyBudget
import Submission.RectangleBudgetStep

/-! A single actual retention kernel transfers every deficit budget. -/
namespace Erdos7DeficitFamilyBudget
open scoped BigOperators
open Erdos7CappedRetentionRows Erdos7FiniteRetentionKernel Erdos7KernelFamilyCompression
open Erdos7CompleteFamilyModel
set_option maxHeartbeats 2500000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

lemma budget_of_push {Ω Ξ α : Type} [Fintype Ω] [Fintype Ξ]
    (δ : ℝ) (f : Ω → Ξ) (ν : Ω → ℝ) (X : α → Ξ → ℝ) (F : ℝ → ℝ) (lo hi : ℝ)
    (hb : HasBudget δ (push f ν) X F lo hi) :
    HasBudget δ ν (fun a x => X a (f x)) F lo hi := by
  obtain ⟨ι, inst, b, pick, φ, hφ, hdiag, hbound⟩ := hb
  letI : Fintype ι := inst
  refine ⟨ι, inst, b, pick, φ, hφ, hdiag, ?_⟩
  simpa only [push_mass, push_integral] using hbound

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
      (∀ δ : ℝ, HasBudget δ (push f (fun z : Ω × A => ν z.1 z.2)) Y G lo' hi' →
        HasBudget δ μ X F lo hi) := by
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
  intro δ hb
  have hb' := budget_of_push δ f (fun z : Ω × A => ν z.1 z.2) Y G lo' hi' hb
  obtain ⟨n, κ, row, hκ, hrow, heq, hrangeκ⟩ := exists_antitone_rows k
  let aa (r : ℕ) (d : Option (Fin R)) := coefficient (retained q c K (κ r)) tail R d
  let loss (r : ℕ) := 1-retained q c K (κ r)
  have haa (r : ℕ) (d : Option (Fin R)) : 0 ≤ aa r d :=
    coefficient_nonneg _ tail R htail d
  have hmaa (d : Option (Fin R)) : Monotone (fun r => aa r d) :=
    (capped_rows_antitone q c K hq hc tail R htail d).comp hκ
  apply mixture_budget_pullback δ μ hμ ν X (fun b z => Y b (f z)) old current
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


variable {n : ℕ}
variable (A : Fin n → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)]
  [∀ i,DecidableEq (A i)]
variable (E : Fin n → ℕ) (X : Pattern E → ∀ i,Finset (A i))

theorem exists_rectangle_budget_step (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℝ) (hμ : ∀ x,0 ≤ μ x)
    (ρ : A ⟨t,ht⟩ → ℝ) (hρ : ∀ y,0 ≤ ρ y) (hρmass : (∑ y,ρ y) = 1)
    (q c K : ℝ) (hq : 0 < q) (hc : 0 ≤ c)
    (r : ℕ → ℝ) (hr : ∀ j < E ⟨t,ht⟩,0 ≤ r j)
    (hrdec : ∀ j,r (j+1) ≤ r j) (hrE : r (E ⟨t,ht⟩) = 0)
    (hs : (∑ a : Fin (E ⟨t,ht⟩),q*r a.val) ≤ 1)
    (hd : ∀ k : Pattern E, exponent E k ⟨t,ht⟩ ≠ 0 →
      (∑ y,if y ∈ X k ⟨t,ht⟩ then ρ y else 0) ≤ r (exponent E k ⟨t,ht⟩-1))
    (U V F G : ℝ → ℝ) (hU : ConvexOn ℝ Set.univ U) (hmU : Monotone U)
    (hV : ∀ u ∈ Set.Icc (1:ℝ) (capacity E t),0 ≤ V u)
    (hF : ∀ u ∈ Set.Icc (1:ℝ) (capacity E t),U u+V u ≤ F u)
    (hdual : ∀ k ∈ Set.Icc (1:ℝ) (capacity E t),∀ u ∈ Set.Icc (1:ℝ) (capacity E t),
      1-retained q c K k + (∑ d : Option (Fin (E ⟨t,ht⟩)),
        coefficient (retained q c K k) (fun j => c*r j) (E ⟨t,ht⟩) d *
          G (multiplier d*u)) ≤ U k+V u) :
    ∃ ν : (∀ i,A i) → A ⟨t,ht⟩ → ℝ,
      (∀ x y,0 ≤ ν x y) ∧
      (∀ x y,ν x y ≤ c*μ x*ρ y) ∧
      (∀ x y,currentBad A E X t ht x y → ν x y = 0) ∧
      (∀ x,(∑ y,ν x y) = μ x*retained q c K (currentCount A E X t ht q r x)) ∧
      (∀ δ : ℝ, HasBudget δ (push (fun z : (∀ i,A i) × A ⟨t,ht⟩ => Function.update z.1 ⟨t,ht⟩ z.2)
        (fun z => ν z.1 z.2)) (count A X : Family E (exponent E) (t+1) → _)
        G 1 (capacity E (t+1)) →
        HasBudget δ μ (count A X : Family E (exponent E) t → _) F 1 (capacity E t)) := by
  classical
  apply exists_kernel_budget_step μ hμ ρ hρ hρmass (currentBad A E X t ht)
    q c K hq hc (currentCount A E X t ht q r)
    (currentBad_le_count A E X t ht q hq r hs ρ hρ hd)
    (E ⟨t,ht⟩) (fun j => c*r j) (fun j => mul_le_mul_of_nonneg_left (hrdec j) hc)
    (count A X) (count A X) (fun z => Function.update z.1 ⟨t,ht⟩ z.2)
    (fun b => oldFamily b ht) (currentFamily E t ht)
    U V F G 1 (capacity E t) 1 (capacity E (t+1))
    (by exact_mod_cast capacity_pos E t) hU hmU hV hF
    (currentCount_bounds A E X t ht q hq.le r hr hs) ?_ ?_
    (fun a => q*r a.val) (fun a => mul_nonneg hq.le (hr a.val a.isLt)) hs ?_ ?_ hdual
  · intro b d x
    exact ⟨count_lower A X _ x,count_upper A X (exponent_bound E) _ (Nat.le_of_lt ht) x⟩
  · intro d u hu
    have hd' := multiplier_bounds d
    constructor
    · nlinarith [hu.1,hd'.1]
    · rw [capacity_succ E t ht,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      exact (mul_le_mul_of_nonneg_left hu.2 (multiplier_nonneg d)).trans
        (mul_le_mul_of_nonneg_right hd'.2 (Nat.cast_nonneg _))
  · intro x
    dsimp only [currentCount]
    simp only [mul_one,le_refl]
  · intro ν hν hcap hmass b φ hφ hmφ
    apply complete_family_compression A X (exponent_bound E) b ht μ hμ ν hν
      (fun x => retained q c K (currentCount A E X t ht q r x))
      (fun x => retained_nonneg _ _ _ _) hmass ρ c hc hcap r hr hrE ?_ φ hφ hmφ
    intro k hk j hj he
    have hd' := hd k (by rw [he]; omega)
    simpa only [he,Nat.add_sub_cancel] using hd'


#print axioms exists_rectangle_budget_step
end Erdos7DeficitFamilyBudget
