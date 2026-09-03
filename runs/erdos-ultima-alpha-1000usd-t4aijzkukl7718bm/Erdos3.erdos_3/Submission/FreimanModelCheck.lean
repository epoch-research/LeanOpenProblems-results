import FormalConjecturesUtil

/-! A finite obstruction to modeling every integer 3-AP-free set in characteristic three.
This is a diagnostic for a proposed reduction, not a disproof of Erdős 3. -/

namespace Erdos3FreimanModelCheck

/-- The four parallelogram relations in this set force a characteristic-three collision. -/
def witness : Finset ℕ := {0, 1, 5, 6, 8, 17, 18, 24}

lemma witness_free : ThreeAPFree (witness : Set ℕ) := by
  have h : ∀ a ∈ witness, ∀ b ∈ witness, ∀ c ∈ witness,
      a + c = b + b → a = b := by decide +kernel
  intro a ha b hb c hc heq
  exact h a ha b hb c hc heq

lemma freiman_identity {G : Type*} [AddCommGroup G] {f : ℕ → G}
    (hf : IsAddFreimanHom 2 (witness : Set ℕ) Set.univ f) :
    f 8 = f 5 + 3 • f 1 - 3 • f 0 := by
  have h1 : f 1 + f 5 = f 0 + f 6 :=
    hf.add_eq_add (by simp [witness]) (by simp [witness])
      (by simp [witness]) (by simp [witness]) (by decide)
  have h2 : f 1 + f 17 = f 0 + f 18 :=
    hf.add_eq_add (by simp [witness]) (by simp [witness])
      (by simp [witness]) (by simp [witness]) (by decide)
  have h3 : f 6 + f 18 = f 0 + f 24 :=
    hf.add_eq_add (by simp [witness]) (by simp [witness])
      (by simp [witness]) (by simp [witness]) (by decide)
  have h4 : f 17 + f 8 = f 1 + f 24 :=
    hf.add_eq_add (by simp [witness]) (by simp [witness])
      (by simp [witness]) (by simp [witness]) (by decide)
  have h6 : f 6 = f 1 + f 5 - f 0 := eq_sub_of_add_eq' h1.symm
  have h18 : f 18 = f 1 + f 17 - f 0 := eq_sub_of_add_eq' h2.symm
  have h24 : f 24 = f 6 + f 18 - f 0 := eq_sub_of_add_eq' h3.symm
  calc
    f 8 = f 1 + f 24 - f 17 := eq_sub_of_add_eq' h4
    _ = f 5 + 3 • f 1 - 3 • f 0 := by rw [h24, h6, h18]; abel

/-- Even an injective Freiman homomorphism need not exist, before asking for
an isomorphism or for any control on the size of the model. -/
theorem no_characteristic_three_model {G : Type*} [AddCommGroup G]
    (hG : ∀ x : G, 3 • x = 0) {f : ℕ → G}
    (hf : IsAddFreimanHom 2 (witness : Set ℕ) Set.univ f) :
    ¬ Set.InjOn f (witness : Set ℕ) := by
  intro hi
  have h := freiman_identity hf
  rw [hG, hG, add_zero, sub_zero] at h
  have : (8 : ℕ) = 5 := hi (by simp [witness]) (by simp [witness]) h
  omega

theorem no_finite_field_model (d : ℕ) :
    ¬ (∃ f : ℕ → (Fin d → ZMod 3),
      IsAddFreimanHom 2 (witness : Set ℕ) Set.univ f ∧
      Set.InjOn f (witness : Set ℕ)) := by
  rintro ⟨f, hf, hi⟩
  apply no_characteristic_three_model (f := f) (fun x ↦ ?_) hf hi
  ext i
  change (3 : ℕ) • x i = 0
  rw [nsmul_eq_mul]
  change (3 : ZMod 3) * x i = 0
  rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]

/-- A characteristic-three Freiman isomorphism already forces 3-AP-freeness
in the integer source. It therefore cannot by itself bootstrap longer APs. -/
theorem source_threeAPFree_of_characteristic_three_iso
    {G : Type*} [AddCommGroup G] (hG : ∀ x : G, 3 • x = 0)
    {A : Set ℕ} {B : Set G} {f : ℕ → G}
    (hf : IsAddFreimanIso 2 A B f) : ThreeAPFree A := by
  intro a ha b hb c hc heq
  have he := (hf.add_eq_add ha hc hb hb).mpr heq
  have hfc : f c = f b + f b - f a := eq_sub_of_add_eq' he
  have hcyc : f b + f a - (f c + f c) = 3 • f a - 3 • f b := by
    rw [hfc]
    abel
  rw [hG, hG, sub_self] at hcyc
  have hcyc' : f b + f a = f c + f c := sub_eq_zero.mp hcyc
  have hnat := (hf.add_eq_add hb ha hc hc).mp hcyc'
  omega

/-- The obstruction is finite and is already 3-AP-free, not merely 4-AP-free. -/
theorem finite_threeAPFree_without_model :
    ∃ A : Set ℕ, A.Finite ∧ ThreeAPFree A ∧
      ∀ d : ℕ, ¬ (∃ f : ℕ → (Fin d → ZMod 3),
        IsAddFreimanHom 2 A Set.univ f ∧ Set.InjOn f A) := by
  exact ⟨witness, witness.finite_toSet, witness_free, no_finite_field_model⟩

#print axioms witness_free
#print axioms no_characteristic_three_model
#print axioms finite_threeAPFree_without_model
#print axioms source_threeAPFree_of_characteristic_three_iso

end Erdos3FreimanModelCheck
