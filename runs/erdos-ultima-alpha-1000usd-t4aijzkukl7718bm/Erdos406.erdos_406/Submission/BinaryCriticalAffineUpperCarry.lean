import Submission.BinaryCriticalConstantTail

/-! Soundness of linear affine upper-carry certificates. The matrices driving
the auxiliary state are fixed, so the unknown upper rows and forcing rows
enter the certificate inequalities linearly. No sufficient instance is asserted. -/
namespace Erdos406BinaryCriticalAffineCarry
open scoped Matrix BigOperators

lemma dot_le_of_coordinate_le {σ : Type*} [Fintype σ]
    (r s w : σ → ℝ) (hrs : r ≤ s) (hw : 0 ≤ w) : r ⬝ᵥ w ≤ s ⬝ᵥ w := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hrs i) (hw i)

/-- Signed multiples of exact state relations may be added freely to a row. -/
lemma dot_le_mod_relations {σ κ : Type*} [Fintype σ] [Fintype κ]
    (r s w : σ → ℝ) (A : Matrix κ σ ℝ) (μ : κ → ℝ)
    (hw : 0 ≤ w) (hA : A *ᵥ w = 0)
    (hrow : r ≤ s + μ ᵥ* A) : r ⬝ᵥ w ≤ s ⬝ᵥ w := by
  have hh := dot_le_of_coordinate_le r (s + μ ᵥ* A) w hrow hw
  rw [add_dotProduct, ← Matrix.dotProduct_mulVec, hA] at hh
  simpa using hh

/-- A coefficientwise induction proving affine upper bounds for the three
carry differences. The finite set of carry indices is abstract here. -/
theorem upper_carry_invariant {σ κ ρ : Type*} [Fintype σ]
    (F : ℕ → κ → ℝ) (W : ℕ → σ → ℝ) (Q : ℕ → ρ)
    (next : ρ → Fin 2 → ρ) (parent : Fin 2 → κ → κ)
    (T : ρ → Fin 2 → Matrix σ σ ℝ)
    (G : ρ → Fin 2 → κ → σ → ℝ) (B : ρ → κ → σ → ℝ)
    (hW : ∀ n : ℕ, 0 < n → 0 ≤ W n)
    (hseed : ∀ c, F 1 c ≤ B (Q 1) c ⬝ᵥ W 1)
    (hQ : ∀ n : ℕ, 0 < n → ∀ d : Fin 2, Q (2*n+d.val) = next (Q n) d)
    (hstepW : ∀ n : ℕ, 0 < n → ∀ d : Fin 2,
      W (2*n+d.val) = T (Q n) d *ᵥ W n)
    (hstepF : ∀ n : ℕ, 0 < n → ∀ d : Fin 2, ∀ c,
      F (2*n+d.val) c = 2*F n (parent d c) + G (Q n) d c ⬝ᵥ W n)
    (hclose : ∀ q d c, (2:ℝ) • B q (parent d c) + G q d c ≤
      B (next q d) c ᵥ* T q d) :
    ∀ n : ℕ, 0 < n → ∀ c, F n c ≤ B (Q n) c ⬝ᵥ W n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn c
    by_cases h1 : n = 1
    · subst n
      exact hseed c
    have hm : 0 < n/2 := by omega
    let d : Fin 2 := ⟨n%2, Nat.mod_lt _ (by decide)⟩
    have he : 2*(n/2)+d.val = n := by dsimp [d]; omega
    have hi := ih (n/2) (Nat.div_lt_self hn (by decide)) hm (parent d c)
    have hf := hstepF (n/2) hm d c
    have hw := hstepW (n/2) hm d
    have hq := hQ (n/2) hm d
    rw [he] at hf hw hq
    have hc := dot_le_of_coordinate_le _ _ (W (n/2))
      (hclose (Q (n/2)) d c) (hW (n/2) hm)
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul,
      ← Matrix.dotProduct_mulVec, ← hw, ← hq] at hc
    rw [hf]
    linarith

/-- The upper rows imply the desired scalar construction inequality when
the target remainder is nonpositive on the nonnegative auxiliary state. -/
theorem upper_carry_target {σ κ ρ : Type*} [Fintype σ]
    (F : ℕ → κ → ℝ) (W : ℕ → σ → ℝ) (Q : ℕ → ρ)
    (B L : ρ → κ → σ → ℝ) (guard : ρ → Prop)
    (hW : ∀ n : ℕ, 0 < n → 0 ≤ W n)
    (hupper : ∀ n : ℕ, 0 < n → ∀ c, F n c ≤ B (Q n) c ⬝ᵥ W n)
    (htarget : ∀ q, guard q → ∀ c, B q c + L q c ≤ 0)
    (n : ℕ) (hn : 0 < n) (hg : guard (Q n)) (c : κ) :
    F n c + L (Q n) c ⬝ᵥ W n ≤ 0 := by
  have hi := hupper n hn c
  have ht := dot_le_of_coordinate_le _ (0 : σ → ℝ) (W n)
    (htarget (Q n) hg c) (hW n hn)
  rw [add_dotProduct] at ht
  simp only [zero_dotProduct] at ht
  linarith

#print axioms dot_le_mod_relations

/-- Exact relations in the auxiliary state may be used with arbitrary signed
multipliers in every closure row. -/
theorem upper_carry_invariant_mod_relations {σ κ ρ η : Type*}
    [Fintype σ] [Fintype η]
    (F : ℕ → κ → ℝ) (W : ℕ → σ → ℝ) (Q : ℕ → ρ)
    (next : ρ → Fin 2 → ρ) (parent : Fin 2 → κ → κ)
    (T : ρ → Fin 2 → Matrix σ σ ℝ)
    (G : ρ → Fin 2 → κ → σ → ℝ) (B : ρ → κ → σ → ℝ)
    (A : ρ → Matrix η σ ℝ) (μ : ρ → Fin 2 → κ → η → ℝ)
    (hA : ∀ n : ℕ, 0 < n → A (Q n) *ᵥ W n = 0)
    (hW : ∀ n : ℕ, 0 < n → 0 ≤ W n)
    (hseed : ∀ c, F 1 c ≤ B (Q 1) c ⬝ᵥ W 1)
    (hQ : ∀ n : ℕ, 0 < n → ∀ d : Fin 2, Q (2*n+d.val) = next (Q n) d)
    (hstepW : ∀ n : ℕ, 0 < n → ∀ d : Fin 2,
      W (2*n+d.val) = T (Q n) d *ᵥ W n)
    (hstepF : ∀ n : ℕ, 0 < n → ∀ d : Fin 2, ∀ c,
      F (2*n+d.val) c = 2*F n (parent d c) + G (Q n) d c ⬝ᵥ W n)
    (hclose : ∀ q d c, (2:ℝ) • B q (parent d c) + G q d c ≤
      B (next q d) c ᵥ* T q d + μ q d c ᵥ* A q) :
    ∀ n : ℕ, 0 < n → ∀ c, F n c ≤ B (Q n) c ⬝ᵥ W n := by
  let GG := fun q d c => G q d c - μ q d c ᵥ* A q
  have hGG (n : ℕ) (hn : 0 < n) (d : Fin 2) (c : κ) :
      GG (Q n) d c ⬝ᵥ W n = G (Q n) d c ⬝ᵥ W n := by
    dsimp [GG]
    rw [sub_dotProduct, ← Matrix.dotProduct_mulVec, hA n hn]
    simp
  apply upper_carry_invariant F W Q next parent T GG B hW hseed hQ hstepW
  · intro n hn d c
    rw [hGG n hn d c]
    exact hstepF n hn d c
  · intro q d c j
    have h := hclose q d c j
    change 2*B q (parent d c) j + G q d c j ≤
      (B (next q d) c ᵥ* T q d) j + (μ q d c ᵥ* A q) j at h
    change 2*B q (parent d c) j +
      (G q d c j - (μ q d c ᵥ* A q) j) ≤ (B (next q d) c ᵥ* T q d) j
    linarith

#print axioms upper_carry_invariant_mod_relations

#print axioms upper_carry_invariant
#print axioms upper_carry_target
end Erdos406BinaryCriticalAffineCarry
