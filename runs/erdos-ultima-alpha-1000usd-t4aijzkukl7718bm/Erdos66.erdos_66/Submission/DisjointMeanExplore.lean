import Submission.HeterogeneousSelectionExplore

/-! Factorization of uniform finite averages for disjoint coordinate supports.
This is an auxiliary lemma for matching-based repair estimates. -/
namespace Erdos66DisjointMean
open Erdos66UniformSelection
open scoped Classical
set_option maxHeartbeats 1000000

lemma mean_equiv {γ δ : Type*} [Fintype γ] [Fintype δ] (e : γ ≃ δ) (f : δ → ℝ) :
    mean (fun x ↦ f (e x)) = mean f := by
  rw [mean, mean, e.sum_comp, Fintype.card_congr e]

lemma mean_prod {γ δ : Type*} [Fintype γ] [Fintype δ] (f : γ → ℝ) (g : δ → ℝ) :
    mean (fun x : γ × δ ↦ f x.1 * g x.2) = mean f * mean g := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.mul_sum, ← Finset.sum_mul, mul_div_mul_comm]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]

lemma mean_restrict (s : Set ι) (f : (∀ i : s, α i) → ℝ) :
    mean (fun ω : ∀ i, α i ↦ f (fun i : s ↦ ω i)) = mean f := by
  let e := Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ s) α
  have h₁ := mean_equiv e (fun x ↦ f x.1 * (1 : ℝ))
  simp only [e, mul_one, Equiv.piEquivPiSubtypeProd_apply] at h₁
  rw [h₁]
  have h₂ := mean_prod f (fun _ : ∀ i : (sᶜ : Set ι), α i ↦ (1 : ℝ))
  simpa only [mul_one, mean_const] using h₂

lemma mean_mul_of_disjoint (s t : Set ι) (hst : Disjoint s t)
    (f g : (∀ i, α i) → ℝ) (hf : DependsOn f s) (hg : DependsOn g t) :
    mean (fun ω ↦ f ω * g ω) = mean f * mean g := by
  obtain ⟨f₀,rfl⟩ := dependsOn_iff_exists_comp.mp hf
  have hgc : DependsOn g sᶜ := hg.mono (fun i hi hs ↦ Set.disjoint_left.mp hst hs hi)
  obtain ⟨g₀,rfl⟩ := dependsOn_iff_exists_comp.mp hgc
  let e := Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ s) α
  change mean (fun ω : ∀ i, α i ↦ f₀ (fun i : s ↦ ω i) * g₀ (fun i : (sᶜ : Set ι) ↦ ω i)) = _
  have he := mean_equiv e (fun x ↦ f₀ x.1 * g₀ x.2)
  simp only [e, Equiv.piEquivPiSubtypeProd_apply] at he
  calc
    _ = mean (fun x : (∀ i : s, α i) × (∀ i : (sᶜ : Set ι), α i) ↦ f₀ x.1 * g₀ x.2) := by convert he using 1
    _ = mean f₀ * mean g₀ := mean_prod f₀ g₀
    _ = _ := by
      congr 1
      · exact (mean_restrict s f₀).symm
      · convert (mean_restrict sᶜ g₀).symm using 1
        congr 1
        exact Subsingleton.elim _ _

lemma dependsOn_prod (S : Finset κ) (E : κ → Finset ι) (f : κ → (∀ i, α i) → ℝ)
    (hf : ∀ k ∈ S, DependsOn (f k) (E k)) :
    DependsOn (fun ω ↦ ∏ k ∈ S, f k ω) (S.biUnion E) := by
  intro x y hxy
  apply Finset.prod_congr rfl
  intro k hk
  exact hf k hk (fun i hi ↦ hxy i (Finset.mem_biUnion.mpr ⟨k,hk,hi⟩))

lemma mean_prod_of_disjoint [DecidableEq κ] (S : Finset κ) (E : κ → Finset ι)
    (f : κ → (∀ i, α i) → ℝ)
    (hE : (S : Set κ).Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hf : ∀ k ∈ S, DependsOn (f k) (E k)) :
    mean (fun ω ↦ ∏ k ∈ S, f k ω) = ∏ k ∈ S, mean (f k) := by
  induction S using Finset.induction_on with
  | empty => simp [mean_const]
  | @insert k S hk ih =>
    simp only [Finset.prod_insert hk]
    have hd : Disjoint (E k : Set ι) (S.biUnion E : Finset ι) := by
      apply Set.disjoint_left.mpr
      intro i hi hj
      obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hj
      exact Finset.disjoint_left.mp (hE (by simp) (by simp [hj]) (fun he : k = j ↦ hk (he.symm ▸ hj))) hi hij
    rw [mean_mul_of_disjoint _ _ hd _ _ (hf k (by simp))
      (dependsOn_prod S E f (fun j hj ↦ hf j (by simp [hj])))]
    rw [ih (hE.mono (by intro j hj; simp [hj])) (fun j hj ↦ hf j (by simp [hj]))]

end Erdos66DisjointMean
