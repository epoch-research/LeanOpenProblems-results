import FormalConjecturesUtil

/-!
Independent checks for Erdős problem 126. These establish only the precise
meaning, existence, uniqueness, and monotonicity of the minimum in the statement,
not the conjectural asymptotic. Neither theorem from Spec.lean is imported.
-/

namespace Independent126

open Filter

-- This is the definition from Spec.lean, copied without importing either conjectural theorem.
def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop := ∀ n,
    IsGreatest
      { m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card}
      (f n)

def factorCount (A : Finset ℕ) : ℕ :=
  (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card

theorem offDiag_product_pos (A : Finset ℕ) :
    0 < ∏ ⟨a, b⟩ ∈ A.offDiag, (a + b) := by
  apply Finset.prod_pos
  intro p hp
  have hne := (Finset.mem_offDiag.mp hp).2.2
  rcases p with ⟨a, b⟩
  dsimp at *
  omega

-- In particular the ordered product has exactly the intended union of prime supports.
theorem prime_mem_iff (A : Finset ℕ) (p : ℕ) :
    p ∈ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors ↔
    p.Prime ∧ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ p ∣ a + b := by
  rw [Nat.mem_primeFactors_of_ne_zero (ne_of_gt (offDiag_product_pos A))]
  constructor
  · rintro ⟨hp, hdiv⟩
    obtain ⟨⟨a, b⟩, hab, hdiv⟩ :=
      (hp.prime.dvd_finset_prod_iff (fun q : ℕ × ℕ => q.1 + q.2)).mp hdiv
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
    exact ⟨hp, a, ha, b, hb, hne, hdiv⟩
  · rintro ⟨hp, a, ha, b, hb, hne, hdiv⟩
    exact ⟨hp, (hp.prime.dvd_finset_prod_iff (fun q : ℕ × ℕ => q.1 + q.2)).mpr
      ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩, hdiv⟩⟩

theorem factorCount_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    factorCount A ≤ factorCount B := by
  apply Finset.card_le_card
  intro p hp
  rw [prime_mem_iff] at hp ⊢
  obtain ⟨hprime, a, ha, b, hb, hne, hdiv⟩ := hp
  exact ⟨hprime, a, hAB ha, b, hAB hb, hne, hdiv⟩


theorem factorCount_attains (n : ℕ) :
    ∃ m, ∃ A : Finset ℕ, A.card = n ∧ factorCount A = m :=
  ⟨factorCount (Finset.range n), Finset.range n, Finset.card_range n, rfl⟩

noncomputable def minimum (n : ℕ) : ℕ := by
  classical
  exact Nat.find (factorCount_attains n)

theorem minimum_is_maximal : IsMaximalAddFactorsCard minimum := by
  classical
  intro n
  constructor
  · intro A hA
    exact Nat.find_min' (factorCount_attains n) ⟨A, hA, rfl⟩
  · intro m hm
    obtain ⟨A, hA, hmin⟩ := Nat.find_spec (factorCount_attains n)
    have hbound := hm A hA
    change m ≤ factorCount A at hbound
    change m ≤ minimum n
    simpa only [minimum, hmin] using hbound

theorem maximal_unique {f g : ℕ → ℕ}
    (hf : IsMaximalAddFactorsCard f) (hg : IsMaximalAddFactorsCard g) : f = g := by
  funext n
  exact le_antisymm ((hg n).2 (hf n).1) ((hf n).2 (hg n).1)

theorem exists_maximal : ∃ f, IsMaximalAddFactorsCard f :=
  ⟨minimum, minimum_is_maximal⟩

theorem maximal_attained {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ factorCount A = f n := by
  classical
  rw [maximal_unique hf minimum_is_maximal]
  exact Nat.find_spec (factorCount_attains n)

theorem maximal_monotone {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) :
    Monotone f := by
  intro m n hmn
  apply (hf n).2
  intro A hA
  obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq (hmn.trans_eq hA.symm)
  exact ((hf m).1 B hB).trans (factorCount_mono hBA)

theorem two_unit_equation (a u v : ℕ) (huv : u ≠ v) :
    ((a : ℚ) + v) / ((v : ℚ) - u) -
      ((a : ℚ) + u) / ((v : ℚ) - u) = 1 := by
  have hne : (v : ℚ) - u ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm huv)
  field_simp
  ring

theorem real_division_exact (f : ℕ → ℕ) :
    Tendsto (fun n => f n / Real.log n) atTop atTop ↔
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop := Iff.rfl

#print axioms offDiag_product_pos
#print axioms prime_mem_iff
#print axioms factorCount_mono
#print axioms minimum_is_maximal
#print axioms exists_maximal
#print axioms maximal_unique
#print axioms maximal_attained
#print axioms maximal_monotone
#print axioms two_unit_equation
#print axioms real_division_exact

end Independent126
