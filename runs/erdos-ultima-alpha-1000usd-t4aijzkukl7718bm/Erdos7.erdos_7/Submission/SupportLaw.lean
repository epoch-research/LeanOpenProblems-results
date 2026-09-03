import Submission.SupportCriterion

/-! Exact two-variable laws for support-at-most-two cofactors. No numerical
certificate or unrestricted covering obstruction is asserted here. -/
namespace Erdos7SupportCompression
open scoped BigOperators
set_option maxHeartbeats 4000000

abbrev TripleState := ℕ × ℕ

def tripleCount (x : TripleState) : ℕ := 1 + x.1 + x.2

def tripleUpdate (a : ℕ) (x : TripleState) : TripleState :=
  (x.1 + a, x.2 + a * x.1)

def tripleMultiplicity (x : TripleState) : ℕ → ℕ
  | 0 => tripleCount x
  | 1 => 1 + x.1
  | 2 => 1
  | _ + 3 => 0

lemma tripleMultiplicity_initial : tripleMultiplicity (0, 0) = supportMultiplicity 2 := by
  funext r
  rcases r with _ | _ | _ | r <;> simp [tripleMultiplicity, tripleCount, supportMultiplicity]

lemma push_tripleMultiplicity (x : TripleState) (a : ℕ) :
    pushMultiplicity (tripleMultiplicity x) a = tripleMultiplicity (tripleUpdate a x) := by
  funext r
  rcases r with _ | _ | _ | r <;>
    simp [pushMultiplicity, tripleMultiplicity, tripleCount, tripleUpdate] <;> ring

def combinedCount (x y : TripleState) : ℕ :=
  1 + x.1 + x.2 + (1 + x.1) * y.1 + y.2

lemma combinedCount_update (x y : TripleState) (a : ℕ) :
    combinedCount (tripleUpdate a x) y = combinedCount x (tripleUpdate a y) := by
  simp only [combinedCount, tripleUpdate]
  ring

lemma combinedCount_zero (x : TripleState) : combinedCount x (0, 0) = tripleCount x := by
  simp [combinedCount, tripleCount]

lemma combinedCount_initial (x : TripleState) : combinedCount (0, 0) x = tripleCount x := by
  simp [combinedCount, tripleCount]

noncomputable def pairExpect (μ : TripleState →₀ ℚ) (f : TripleState → ℚ) : ℚ :=
  μ.sum (fun x w => w * f x)

lemma pairExpect_congr (μ : TripleState →₀ ℚ) {f g : TripleState → ℚ}
    (h : ∀ x, f x = g x) : pairExpect μ f = pairExpect μ g := by
  unfold pairExpect
  apply Finsupp.sum_congr
  intro x hx
  rw [h x]

lemma pairExpect_add (μ ν : TripleState →₀ ℚ) (f : TripleState → ℚ) :
    pairExpect (μ + ν) f = pairExpect μ f + pairExpect ν f := by
  unfold pairExpect
  exact Finsupp.sum_add_index (by intros; simp) (by intros; ring)

lemma pairExpect_smul (a : ℚ) (μ : TripleState →₀ ℚ) (f : TripleState → ℚ) :
    pairExpect (a • μ) f = a * pairExpect μ f := by
  unfold pairExpect
  rw [Finsupp.sum_smul_index (by intros; simp)]
  simp only [Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

lemma pairExpect_sum {ι : Type*} (s : Finset ι) (μ : ι → TripleState →₀ ℚ)
    (f : TripleState → ℚ) : pairExpect (∑ i ∈ s, μ i) f = ∑ i ∈ s, pairExpect (μ i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairExpect]
  | @insert i s hi ih => rw [Finset.sum_insert hi, pairExpect_add, Finset.sum_insert hi, ih]

lemma pairExpect_map (a : ℕ) (μ : TripleState →₀ ℚ) (f : TripleState → ℚ) :
    pairExpect (μ.mapDomain (tripleUpdate a)) f =
      pairExpect μ (fun x => f (tripleUpdate a x)) := by
  unfold pairExpect
  exact Finsupp.sum_mapDomain_index (by intros; simp) (by intros; ring)

noncomputable def tripleInitial : TripleState →₀ ℚ := Finsupp.single (0, 0) 1

noncomputable def tripleStep (E : ℕ) (q : ℕ → ℚ) (μ : TripleState →₀ ℚ) :
    TripleState →₀ ℚ :=
  (1 - q 0) • μ + ∑ g ∈ Finset.range E,
    (q g - q (g + 1)) • μ.mapDomain (tripleUpdate (g + 1))

lemma pairExpect_initial (f : TripleState → ℚ) : pairExpect tripleInitial f = f (0, 0) := by
  simp [tripleInitial, pairExpect]

lemma pairExpect_step (E : ℕ) (q : ℕ → ℚ) (μ : TripleState →₀ ℚ)
    (f : TripleState → ℚ) :
    pairExpect (tripleStep E q μ) f = (1 - q 0) * pairExpect μ f +
      ∑ g ∈ Finset.range E, (q g - q (g + 1)) *
        pairExpect μ (fun x => f (tripleUpdate (g + 1) x)) := by
  simp only [tripleStep, pairExpect_add, pairExpect_smul, pairExpect_sum, pairExpect_map]

noncomputable def triplePrefixLaw {n : ℕ} (E : Fin n → ℕ)
    (q : Fin n → ℕ → ℚ) : ℕ → (TripleState →₀ ℚ)
  | 0 => tripleInitial
  | t + 1 => if h : t < n then
      tripleStep (E ⟨t,h⟩) (q ⟨t,h⟩) (triplePrefixLaw E q t)
    else triplePrefixLaw E q t

/-- Exact law interpretation of the support-sensitive envelope. This involves
only finitely supported laws and all finite exponent levels; no tail is omitted. -/
theorem supportEnvelope_triple_eq {n : ℕ} (E : Fin n → ℕ)
    (q : Fin n → ℕ → ℚ) (φ : ℚ → ℚ) (t : ℕ) (x : TripleState) :
    supportEnvelope E q φ t (tripleMultiplicity x) =
      pairExpect (triplePrefixLaw E q t) (fun y => φ (combinedCount x y)) := by
  induction t generalizing x with
  | zero => simp [supportEnvelope, triplePrefixLaw, pairExpect_initial,
      combinedCount_zero, tripleMultiplicity]
  | succ t ih =>
    simp only [supportEnvelope, triplePrefixLaw]
    split_ifs
    · rw [pairExpect_step, ih]
      congr 1
      apply Finset.sum_congr rfl
      intro g hg
      rw [push_tripleMultiplicity, ih]
      congr 1
      apply pairExpect_congr
      intro y
      rw [combinedCount_update]
    · exact ih x

theorem supportEnvelope_two_eq {n : ℕ} (E : Fin n → ℕ)
    (q : Fin n → ℕ → ℚ) (φ : ℚ → ℚ) (t : ℕ) :
    supportEnvelope E q φ t (supportMultiplicity 2) =
      pairExpect (triplePrefixLaw E q t) (fun y => φ (tripleCount y)) := by
  rw [← tripleMultiplicity_initial, supportEnvelope_triple_eq]
  apply pairExpect_congr
  intro y
  rw [combinedCount_initial]

#print axioms supportEnvelope_triple_eq
#print axioms supportEnvelope_two_eq
end Erdos7SupportCompression
