import Submission.BinaryCriticalGeneralObserver

/-! Finite minima of signed linear observers. The construction hypothesis
matches every parent observer with some child observer, not vice versa.
No sufficient instance or original-conjecture settlement is asserted. -/
namespace Erdos406BinaryCriticalMinObserver
open Erdos406BinaryCriticalGuard
open scoped Matrix BigOperators
variable {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]

noncomputable def minValue (s : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty s

lemma minValue_le (s : ι → ℝ) (i : ι) : minValue s≤s i :=
  Finset.inf'_le s (Finset.mem_univ i)

lemma le_minValue (s : ι → ℝ) (a : ℝ) (h : ∀ i, a≤s i) : a ≤ minValue s :=
  Finset.le_inf' Finset.univ_nonempty s (fun i _ => h i)

lemma minValue_attained (s : ι → ℝ) : ∃ i, minValue s=s i := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty s
  exact ⟨i,hi⟩

lemma min_construction (s t : ι → ℝ)
    (h : ∀ j, ∃ i, t i≤3*s j) : minValue t≤3*minValue s := by
  obtain ⟨j,hj⟩ := minValue_attained s
  obtain ⟨i,hi⟩ := h j
  rw [hj]
  exact (minValue_le t i).trans hi

/-- This allows a genuinely nonlinear potential, a finite minimum of
linear observers, while requiring the lower bound for EVERY observer. -/
theorem min_critical_criterion (S : ι → ℕ → ℝ) (r : ℕ) (γ B : ℝ)
    (h1 : ∀ i, 0≤S i 1) (hγ : 0<γ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, ∀ j, ∃ i, S i (3*n+d.val)≤3*S j n)
    (hpower : ∀ k : ℕ, Nat.digits 3 (2^k%3^r) ⊆ [0,1] → ∀ i,
      γ*k*(2:ℝ)^k≤S i (2^k)+B*(2:ℝ)^k) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply critical_criterion (fun n => minValue (fun i => S i n)) r γ B
    (le_minValue _ 0 h1) hγ
  · intro n hn hg d
    exact min_construction _ _ (hstep n hn hg d)
  · intro k hg
    obtain ⟨i,hi⟩ := minValue_attained (fun i => S i (2^k))
    rw [hi]
    exact hpower k hg i

/-- General-observer power soundness extends to finite minima. The global
matching inequalities remain explicit and cannot be replaced by finite tests. -/
theorem local_min_observer_finiteness (r : ℕ)
    (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (a b c : σ → ℝ) (γ z η B : ℝ) (u : Fin (3^r) → ι → σ → ℝ)
    (hγ : 0<γ) (hz : 0≤z) (hη : 0≤η)
    (ha : ∀ q, A q 0 *ᵥ a=2 • a)
    (hb : ∀ q, A q 0 *ᵥ b=2 • a+2 • b)
    (hc : ∀ q, A q 0 *ᵥ c=η • c)
    (hu : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → Nat.Coprime q.val (3^r) → ∀ i,
      1≤u q i ⬝ᵥ a ∧ -B≤u q i ⬝ᵥ b ∧ 0≤u q i ⬝ᵥ c)
    (hS1 : ∀ i, 0≤u (residueState r 1) i ⬝ᵥ (γ • b+z • c))
    (hconstruction : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, ∀ j, ∃ i,
        u (residueState r (3*n+d.val)) i ⬝ᵥ localEval r A (γ • b+z • c) (3*n+d.val)≤
          3*(u (residueState r n) j ⬝ᵥ localEval r A (γ • b+z • c) n)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  let v := localEval r A (γ • b+z • c)
  apply min_critical_criterion (fun i n => u (residueState r n) i ⬝ᵥ v n) r γ (B*γ)
    (by simpa [v] using hS1) hγ hconstruction
  intro k hg i
  obtain ⟨hua,hub,huc⟩ := hu (residueState r (2^k)) hg (power_residue_coprime r k) i
  exact general_observer_power_lower v (fun n => A (residueState r n) 0)
    a b c γ z η B (u (residueState r (2^k)) i) hγ.le hz hη
    (by simp [v]) (fun n hn => by simpa [v] using localEval_step r A (γ • b+z • c) n hn 0)
    (fun n _ => ha _) (fun n _ => hb _) (fun n _ => hc _) hua hub huc k

#print axioms min_critical_criterion
#print axioms local_min_observer_finiteness
end Erdos406BinaryCriticalMinObserver
