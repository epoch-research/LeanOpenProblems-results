import Submission.FamilyBudgetStep

/-! Finite backward budgets with independently indexed count families.
This module supplies the Jensen/dual assembly, not the coordinate-compression
geometry or an unrestricted numerical certificate for Erdős 7. -/
namespace Erdos7BackwardFamilyBudget
open scoped BigOperators
open Erdos7FamilyBudgetStep
set_option maxHeartbeats 1500000

/-- A finite sum of convex monotone tests of possibly different count families
has enough integral to pay for the mass, while its diagonal is bounded by F.
Constants and individual tests may be signed. -/
def HasBudget {Ω α : Type} [Fintype Ω]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : ℝ) (pick : ι → α) (φ : ι → ℝ → ℝ),
    (∀ i, ConvexOn ℝ Set.univ (φ i) ∧ Monotone (φ i)) ∧
    (∀ t ∈ Set.Icc lo hi, b + ∑ i, φ i t ≤ F t) ∧
    ((∑ x, μ x) ≤ ∑ x, μ x * (b + ∑ i, φ i (X (pick i) x)))

lemma zero_mass_budget {Ω α : Type} [Fintype Ω]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (lo hi : ℝ)
    (hmass : (∑ x, μ x) = 0) : HasBudget μ X (fun _ => 0) lo hi := by
  refine ⟨PEmpty, inferInstance, 0, PEmpty.elim, PEmpty.elim, ?_, ?_, ?_⟩
  · intro i; exact i.elim
  · simp
  · simp [hmass]

/-- If all initial families have the same count, a strict scalar budget
contradicts positive initial mass. No common extremizer at later stages is
being asserted. -/
lemma not_budget_constant_count {Ω α : Type} [Fintype Ω]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ) (lo hi t : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hmass : 0 < ∑ x, μ x)
    (ht : t ∈ Set.Icc lo hi) (hX : ∀ a x, X a x = t) (hF : F t < 1) :
    ¬ HasBudget μ X F lo hi := by
  rintro ⟨ι, inst, b, pick, φ, hφ, hdiag, hbudget⟩
  letI : Fintype ι := inst
  have hb := hdiag t ht
  have hu : (∑ x, μ x * (b + ∑ i, φ i (X (pick i) x))) ≤
      (∑ x, μ x) * F t := by
    calc
      _ ≤ ∑ x, μ x * F t := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (by simpa only [hX] using hb) (hμ x))
      _ = _ := (Finset.sum_mul ..).symm
  have hl := mul_lt_mul_of_pos_left hF hmass
  rw [mul_one] at hl
  exact (not_lt_of_ge (hbudget.trans hu)) hl

/-- Assemble current-count Jensen terms and the ordered future-family dual
into a genuine preceding family budget. The compression premise refers to
actual independently selected old families. -/
theorem jensen_dual_pullback {Ω A α ι J : Type}
    [Fintype Ω] [Fintype A] [Fintype ι] [Fintype J]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ν future : Ω → A → ℝ)
    (X : α → Ω → ℝ) (pick : ι → α) (current : J → α)
    (φ : ι → ℝ → ℝ) (a : ℕ → ι → ℝ)
    (U V F : ℝ → ℝ) (κ loss : ℕ → ℝ) (lo hi : ℝ) (hlh : lo ≤ hi)
    (hφ : ∀ i, ConvexOn ℝ Set.univ (φ i) ∧ Monotone (φ i))
    (ha : ∀ k i, 0 ≤ a k i) (hma : ∀ i, Monotone (fun k => a k i))
    (hU : ConvexOn ℝ Set.univ U) (hmU : Monotone U)
    (hV : ∀ t ∈ Set.Icc lo hi, 0 ≤ V t)
    (hF : ∀ t ∈ Set.Icc lo hi, U t + V t ≤ F t)
    (n : ℕ) (row : Ω → ℕ) (hrow : ∀ x, row x < n)
    (hX : ∀ i x, X (pick i) x ∈ Set.Icc lo hi)
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : (∑ j, w j) ≤ 1)
    (hκ : ∀ x, κ (row x) ≤ (1-∑ j, w j)*lo + ∑ j, w j*X (current j) x)
    (hmass : ∀ x, (∑ y, ν x y) = μ x*(1-loss (row x)))
    (hfuture : (∑ x, ∑ y, ν x y) ≤ ∑ x, ∑ y, ν x y*future x y)
    (hcompression : (∑ x, ∑ y, ν x y*future x y) ≤
      ∑ x, μ x*(∑ i, a (row x) i * φ i (X (pick i) x)))
    (hdual : ∀ k < n, ∀ t ∈ Set.Icc lo hi,
      loss k + (∑ i, a k i * φ i t) ≤ U (κ k) + V t) :
    HasBudget μ X F lo hi := by
  classical
  obtain ⟨b, h, hh, hdiag, hbound⟩ := exact_retention_dual_step Finset.univ φ a
    (fun k => U (κ k)) loss V lo hi hlh (fun i _ => (hφ i).1)
    (fun i _ => (hφ i).2) (fun k i _ => ha k i) (fun i _ => hma i) n
    hV hdual μ hμ ν future row hrow (fun i x => X (pick i) x)
    (fun i _ x => hX i x) hmass hfuture hcompression
  let ψ : J ⊕ ι → ℝ → ℝ := Sum.elim (fun j t => w j*U t) h
  let pp : J ⊕ ι → α := Sum.elim current pick
  refine ⟨J ⊕ ι, inferInstance, b+(1-∑ j, w j)*U lo, pp, ψ, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | inl j =>
      refine ⟨?_, ?_⟩
      · simpa only [ψ, Sum.elim_inl, smul_eq_mul] using ConvexOn.smul (hw j) hU
      · intro s t hst
        exact mul_le_mul_of_nonneg_left (hmU hst) (hw j)
    | inr i => exact hh i (Finset.mem_univ _)
  · intro t ht
    have hb := hdiag t ht
    have hp : (1-∑ j, w j)*U lo + ∑ j, w j*U t ≤ U t := by
      rw [← Finset.sum_mul]
      have hl := mul_le_mul_of_nonneg_left (hmU ht.1) (sub_nonneg.mpr hs)
      nlinarith
    simp only [ψ, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    have hf := hF t ht
    linarith
  · have hj (x : Ω) := padded_jensen Finset.univ w (fun j => X (current j) x)
      U hU hmU lo (κ (row x)) (fun j _ => hw j) hs (hκ x)
    apply hbound.trans
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hμ x)
    simp only [ψ, pp, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    have hx := hj x
    linarith


/-- Move a signed constant into one additional constant test. -/
lemma budget_normalize {Ω α : Type} [Fintype Ω] [Nonempty α]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ) (lo hi : ℝ)
    (hb : HasBudget μ X F lo hi) :
    ∃ (ι : Type) (_ : Fintype ι) (pick : ι → α) (φ : ι → ℝ → ℝ),
      (∀ i, ConvexOn ℝ Set.univ (φ i) ∧ Monotone (φ i)) ∧
      (∀ t ∈ Set.Icc lo hi, (∑ i, φ i t) ≤ F t) ∧
      ((∑ x, μ x) ≤ ∑ x, μ x*(∑ i, φ i (X (pick i) x))) := by
  classical
  obtain ⟨ι, inst, b, pick, φ, hφ, hdiag, hbound⟩ := hb
  letI : Fintype ι := inst
  let pp : Option ι → α := fun i => i.elim (Classical.choice ‹Nonempty α›) pick
  let ψ : Option ι → ℝ → ℝ := fun i => i.elim (fun _ => b) φ
  refine ⟨Option ι, inferInstance, pp, ψ, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | none => exact ⟨convexOn_const _ (convex_univ), monotone_const⟩
    | some i => exact hφ i
  · intro t ht
    simpa [ψ, Fintype.sum_option] using hdiag t ht
  · simpa [ψ, pp, Fintype.sum_option] using hbound

lemma convex_scale (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (d : ℝ) :
    ConvexOn ℝ Set.univ (fun t => φ (d*t)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hφ.2 (Set.mem_univ (d*x)) (Set.mem_univ (d*y)) ha hb hab
  simpa only [smul_eq_mul, mul_add, mul_left_comm d a, mul_left_comm d b] using hh

/-- A genuine backward step from individual, actual fiber-compression bounds.
Different future families are compressed to different old families. Only the
positive diagonal mixture is tested against the scalar next budget. -/
theorem mixture_budget_pullback {Ω A α β D J : Type}
    [Fintype Ω] [Fintype A] [Fintype D] [Fintype J] [Nonempty β]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ν : Ω → A → ℝ)
    (X : α → Ω → ℝ) (Y : β → Ω × A → ℝ)
    (old : β → D → α) (current : J → α)
    (a : ℕ → D → ℝ) (scale : D → ℝ) (hscale : ∀ d, 0 ≤ scale d)
    (U V F G : ℝ → ℝ) (κ loss : ℕ → ℝ)
    (lo hi lo' hi' : ℝ) (hlh : lo ≤ hi)
    (ha : ∀ k d, 0 ≤ a k d) (hma : ∀ d, Monotone (fun k => a k d))
    (hU : ConvexOn ℝ Set.univ U) (hmU : Monotone U)
    (hV : ∀ t ∈ Set.Icc lo hi, 0 ≤ V t)
    (hF : ∀ t ∈ Set.Icc lo hi, U t + V t ≤ F t)
    (n : ℕ) (row : Ω → ℕ) (hrow : ∀ x, row x < n)
    (hX : ∀ b d x, X (old b d) x ∈ Set.Icc lo hi)
    (hrange : ∀ d t, t ∈ Set.Icc lo hi → scale d*t ∈ Set.Icc lo' hi')
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : (∑ j, w j) ≤ 1)
    (hκ : ∀ x, κ (row x) ≤ (1-∑ j, w j)*lo + ∑ j, w j*X (current j) x)
    (hmass : ∀ x, (∑ y, ν x y) = μ x*(1-loss (row x)))
    (hcomp : ∀ b (φ : ℝ → ℝ), ConvexOn ℝ Set.univ φ → Monotone φ →
      (∑ x, ∑ y, ν x y*φ (Y b (x,y))) ≤
        ∑ x, μ x*(∑ d, a (row x) d*φ (scale d*X (old b d) x)))
    (hdual : ∀ k < n, ∀ t ∈ Set.Icc lo hi,
      loss k + (∑ d, a k d*G (scale d*t)) ≤ U (κ k)+V t)
    (hbudget : HasBudget (fun z : Ω × A => ν z.1 z.2) Y G lo' hi') :
    HasBudget μ X F lo hi := by
  classical
  obtain ⟨ι, inst, pick, φ, hφ, hdiag, hbound⟩ :=
    budget_normalize _ Y G lo' hi' hbudget
  letI : Fintype ι := inst
  let ψ : ι × D → ℝ → ℝ := fun id t => φ id.1 (scale id.2*t)
  let pp : ι × D → α := fun id => old (pick id.1) id.2
  have hψ (id : ι × D) : ConvexOn ℝ Set.univ (ψ id) ∧ Monotone (ψ id) := by
    refine ⟨convex_scale _ (hφ id.1).1 _, ?_⟩
    intro s t hst
    exact (hφ id.1).2 (mul_le_mul_of_nonneg_left hst (hscale id.2))
  apply jensen_dual_pullback μ hμ ν (fun x y => ∑ i, φ i (Y (pick i) (x,y)))
    X pp current ψ (fun k id => a k id.2) U V F κ loss lo hi hlh hψ
    (fun k id => ha k id.2) (fun id => hma id.2) hU hmU hV hF n row hrow
    (fun id x => hX (pick id.1) id.2 x) w hw hs hκ hmass
  · simpa only [Fintype.sum_prod_type] using hbound
  · calc
      _ = ∑ i, ∑ x, ∑ y, ν x y*φ i (Y (pick i) (x,y)) := by
        simp_rw [Finset.mul_sum]
        calc
          _ = ∑ x, ∑ i, ∑ y, ν x y*φ i (Y (pick i) (x,y)) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_comm]
          _ = _ := by rw [Finset.sum_comm]
      _ ≤ ∑ i, ∑ x, μ x*(∑ d, a (row x) d*φ i (scale d*X (old (pick i) d) x)) :=
        Finset.sum_le_sum (fun i _ => hcomp (pick i) (φ i) (hφ i).1 (hφ i).2)
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        simp only [Fintype.sum_prod_type, ψ, pp, ← Finset.mul_sum]
  · intro k hk t ht
    have hh : (∑ id : ι × D, a k id.2*ψ id t) ≤ ∑ d, a k d*G (scale d*t) := by
      simp only [Fintype.sum_prod_type, ψ]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro d _
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hdiag (scale d*t) (hrange d t ht)) (ha k d)
    calc
      _ ≤ loss k + ∑ d, a k d*G (scale d*t) := by linarith [hh]
      _ ≤ _ := hdual k hk t ht


/-- Finite backward iteration. Every step may have its own state space and
its own family index type. -/
theorem budget_backward_iteration (Ω α : ℕ → Type) [∀ j, Fintype (Ω j)]
    (μ : (j : ℕ) → Ω j → ℝ) (X : (j : ℕ) → α j → Ω j → ℝ)
    (F : ℕ → ℝ → ℝ) (lo hi : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ j < n, HasBudget (μ (j+1)) (X (j+1)) (F (j+1)) (lo (j+1)) (hi (j+1)) →
      HasBudget (μ j) (X j) (F j) (lo j) (hi j))
    (hfinal : HasBudget (μ n) (X n) (F n) (lo n) (hi n)) :
    HasBudget (μ 0) (X 0) (F 0) (lo 0) (hi 0) := by
  exact Nat.decreasingInduction (motive := fun j _ =>
    HasBudget (μ j) (X j) (F j) (lo j) (hi j)) hstep hfinal (Nat.zero_le n)

/-- Abstract positive-mass criterion, ready for a verified coordinate tower.
The terminal mass cannot vanish when a strict initial scalar budget exists. -/
theorem terminal_mass_ne_zero (Ω α : ℕ → Type) [∀ j, Fintype (Ω j)]
    (μ : (j : ℕ) → Ω j → ℝ) (X : (j : ℕ) → α j → Ω j → ℝ)
    (F : ℕ → ℝ → ℝ) (lo hi : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (hstep : ∀ j < n, HasBudget (μ (j+1)) (X (j+1)) (F (j+1)) (lo (j+1)) (hi (j+1)) →
      HasBudget (μ j) (X j) (F j) (lo j) (hi j))
    (hfinal : F n = fun _ => 0)
    (hμ : ∀ x, 0 ≤ μ 0 x) (hmass : 0 < ∑ x, μ 0 x)
    (ht : t ∈ Set.Icc (lo 0) (hi 0)) (hX : ∀ a x, X 0 a x = t)
    (hF : F 0 t < 1) : (∑ x, μ n x) ≠ 0 := by
  intro hz
  have hb := zero_mass_budget (μ n) (X n) (lo n) (hi n) hz
  rw [← hfinal] at hb
  have hinit := budget_backward_iteration Ω α μ X F lo hi n hstep hb
  exact not_budget_constant_count (μ 0) (X 0) (F 0) (lo 0) (hi 0) t
    hμ hmass ht hX hF hinit

#print axioms terminal_mass_ne_zero
#print axioms mixture_budget_pullback
#print axioms jensen_dual_pullback
#print axioms not_budget_constant_count
end Erdos7BackwardFamilyBudget
