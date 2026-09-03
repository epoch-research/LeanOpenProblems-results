import Submission.FreimanModelCheck

/-! A bounded number of characteristic-three model pieces does not suffice,
even for finite 3-AP-free integer sets. This is not a disproof of Erdős 3. -/
namespace Erdos3ModelCoverCheck

open Erdos3FreimanModelCheck
set_option maxHeartbeats 1000000

abbrev W := witness

lemma witness_bound (a : W) : (a : ℕ) ≤ 24 := by
  have h : ∀ a ∈ witness, a ≤ 24 := by decide
  exact h a a.property

def code {n : ℕ} (v : Fin n → W) : ℕ :=
  Behrend.map 49 (fun i ↦ (v i : ℕ))

def cube (n : ℕ) : Set ℕ := Set.range (@code n)

lemma code_injective {n : ℕ} : Function.Injective (@code n) := by
  intro x y h
  have he : (fun i ↦ (x i : ℕ)) = (fun i ↦ (y i : ℕ)) :=
    Behrend.map_injOn (fun i ↦ by have := witness_bound (x i); omega)
      (fun i ↦ by have := witness_bound (y i); omega) h
  funext i
  exact Subtype.ext (congr_fun he i)

lemma code_pair_eq {n : ℕ} (w x y z : Fin n → W)
    (h : code w + code x = code y + code z) :
    ∀ i, (w i : ℕ) + (x i : ℕ) = (y i : ℕ) + (z i : ℕ) := by
  have he : ((fun i ↦ (w i : ℕ)) + (fun i ↦ (x i : ℕ))) =
      ((fun i ↦ (y i : ℕ)) + (fun i ↦ (z i : ℕ))) := by
    apply Behrend.map_injOn (d := 49)
    · intro i
      have := witness_bound (w i)
      have := witness_bound (x i)
      change (w i : ℕ) + (x i : ℕ) < 49
      omega
    · intro i
      have := witness_bound (y i)
      have := witness_bound (z i)
      change (y i : ℕ) + (z i : ℕ) < 49
      omega
    · simpa only [map_add, code] using h
  exact fun i ↦ congr_fun he i

lemma cube_threeAPFree (n : ℕ) : ThreeAPFree (cube n) := by
  rintro a ⟨w, rfl⟩ b ⟨x, rfl⟩ c ⟨y, rfl⟩ heq
  apply congrArg code
  funext i
  exact Subtype.ext (witness_free (w i).property (x i).property (y i).property
    (code_pair_eq w y x x heq i))

def lineMap {n : ℕ} (l : Combinatorics.Subspace Unit W (Fin n)) (a : ℕ) : ℕ :=
  Behrend.map 49 (fun i ↦ (l.idxFun i).elim (fun w : W ↦ (w : ℕ)) (fun _ ↦ a))

lemma lineMap_eq {n : ℕ} (l : Combinatorics.Subspace Unit W (Fin n)) (a : W) :
    lineMap l (a : ℕ) = code (l (fun _ ↦ a)) := by
  unfold lineMap code
  congr 1
  funext i
  cases h : l.idxFun i <;> simp [Combinatorics.Subspace.coe_apply, h]

lemma lineMap_pair_eq {n : ℕ} (l : Combinatorics.Subspace Unit W (Fin n))
    {a b c d : ℕ} (h : a+b=c+d) :
    lineMap l a + lineMap l b = lineMap l c + lineMap l d := by
  simp only [lineMap, ← map_add]
  congr 1
  funext i
  cases hi : l.idxFun i <;> simp [hi, h]

lemma lineMap_injOn {n : ℕ} (l : Combinatorics.Subspace Unit W (Fin n)) :
    Set.InjOn (lineMap l) (witness : Set ℕ) := by
  intro a ha b hb heq
  let aa : W := ⟨a,ha⟩
  let bb : W := ⟨b,hb⟩
  have he : code (l (fun _ ↦ aa)) = code (l (fun _ ↦ bb)) := by
    simpa only [← lineMap_eq] using heq
  have hl := code_injective he
  obtain ⟨i, hi⟩ := l.proper ()
  have hh := congr_fun hl i
  simp only [Combinatorics.Subspace.coe_apply, hi, Sum.elim_inr] at hh
  exact congrArg Subtype.val hh

/-- This even allows an injective Freiman homomorphism, weaker than an isomorphism. -/
def WeakThreeModel (A : Set ℕ) : Prop :=
  ∃ d : ℕ, ∃ f : ℕ → (Fin d → ZMod 3),
    IsAddFreimanHom 2 A Set.univ f ∧ Set.InjOn f A

/-- No fixed finite palette of three-modelable pieces covers all 3-AP-free sets. -/
theorem no_bounded_model_cover (r : ℕ) :
    ∃ A : Set ℕ, A.Finite ∧ ThreeAPFree A ∧
      ¬ (∃ C : ℕ → Fin r, ∀ c, WeakThreeModel (A ∩ C ⁻¹' {c})) := by
  classical
  obtain ⟨n, hn⟩ :=
    Combinatorics.Subspace.exists_mono_in_high_dimension_fin W (Fin r) Unit
  refine ⟨cube n, Set.finite_range _, cube_threeAPFree n, ?_⟩
  rintro ⟨C, hC⟩
  obtain ⟨l, c, hc⟩ := hn (fun v ↦ C (code v))
  have hmaps : Set.MapsTo (lineMap l) (witness : Set ℕ) (cube n ∩ C ⁻¹' {c}) := by
    intro a ha
    let aa : W := ⟨a,ha⟩
    have he : lineMap l a = code (l (fun _ ↦ aa)) := lineMap_eq l aa
    rw [he]
    exact ⟨⟨l (fun _ ↦ aa), rfl⟩, hc (fun _ ↦ aa)⟩
  have hl : IsAddFreimanHom 2 (witness : Set ℕ) (cube n ∩ C ⁻¹' {c}) (lineMap l) := by
    apply isAddFreimanHom_two.mpr
    exact ⟨hmaps, fun a _ b _ e _ d _ h ↦ lineMap_pair_eq l h⟩
  obtain ⟨d, f, hf, hi⟩ := hC c
  apply no_finite_field_model d
  refine ⟨f ∘ lineMap l, hf.comp hl, ?_⟩
  intro a ha b hb he
  exact lineMap_injOn l ha hb (hi (hmaps ha) (hmaps hb) he)

#print axioms cube_threeAPFree
#print axioms no_bounded_model_cover
end Erdos3ModelCoverCheck
