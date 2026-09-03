import FormalConjecturesUtil

/-! Completing a congruence cover by genuine, nonempty classes. Existing
residues and avoidance of designated divisor classes can be preserved.
Irredundance and private points are deliberately NOT asserted to survive. -/
namespace Erdos7NonemptyArithmeticCompletion
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def completedResidue {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (g : ℕ → ℤ) (n : ℕ) : ℤ := by
  classical
  exact if h : ∃ i, m i = n then a h.choose else g n

lemma completedResidue_old {I : Type*} (m : I → ℕ) (a : I → ℤ) (g : ℕ → ℤ)
    (hm : Function.Injective m) (i : I) : completedResidue m a g (m i) = a i := by
  classical
  have h : ∃ j, m j = m i := ⟨i,rfl⟩
  have he : h.choose = i := hm h.choose_spec
  simp only [completedResidue,dif_pos h,he]

lemma completedResidue_new {I : Type*} (m : I → ℕ) (a : I → ℤ) (g : ℕ → ℤ)
    (n : ℕ) (hn : ¬ ∃ i, m i=n) : completedResidue m a g n = g n := by
  classical
  simp only [completedResidue,dif_neg hn]

/-- Any pointwise property of the old and new residue assignments is retained.
No maximum over different families is being identified here. -/
lemma completed_property {I : Type*} (m : I → ℕ) (a : I → ℤ) (g : ℕ → ℤ)
    (P : ℕ → ℤ → Prop) (hold : ∀ i, P (m i) (a i))
    (hnew : ∀ n, (¬ ∃ i, m i=n) → P n (g n)) (n : ℕ) :
    P n (completedResidue m a g n) := by
  classical
  by_cases h : ∃ i, m i=n
  · rw [completedResidue,dif_pos h]
    simpa only [h.choose_spec] using hold h.choose
  · rw [completedResidue_new m a g n h]
    exact hnew n h

/-- Enlarging the modulus set with genuine classes cannot lose coverage. -/
theorem completed_cover {I : Type*} (m : I → ℕ) (a : I → ℤ) (g : ℕ → ℤ)
    (hm : Function.Injective m) (D : Finset ℕ) (hD : ∀ i, m i ∈ D)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) :
    ∀ x : ℤ, ∃ n : ↥D, (n.val : ℤ) ∣ x-completedResidue m a g n.val := by
  intro x
  obtain ⟨i,hi⟩ := hc x
  refine ⟨⟨m i,hD i⟩,?_⟩
  simpa only [completedResidue_old m a g hm i] using hi

/-- A finite modulus set comes with distinct moduli and nonempty cosets. -/
theorem completed_nonempty (D : Finset ℕ) (b : ℕ → ℤ) :
    Function.Injective (fun n : ↥D => n.val) ∧
    ∀ n : ↥D, ∃ x : ℤ, (n.val : ℤ) ∣ x-b n.val := by
  refine ⟨Subtype.val_injective,fun n => ⟨b n.val,?_⟩⟩
  simp

def nontrivialDivisors (N : ℕ) : Finset ℕ := N.divisors.erase 1

lemma mem_nontrivialDivisors (N d : ℕ) (hN : 0 < N) :
    d ∈ nontrivialDivisors N ↔ 1 < d ∧ d ∣ N := by
  rw [nontrivialDivisors,Finset.mem_erase,Nat.mem_divisors]
  constructor
  · rintro ⟨hne,hd,hNz⟩
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hN
    exact ⟨by omega,hd⟩
  · rintro ⟨h1,hd⟩
    exact ⟨by omega,hd,by omega⟩

/-- Every odd arithmetic cover can be enlarged to all nontrivial divisors of
any chosen positive odd common period. This need not be a minimal cover. -/
theorem full_divisor_completion {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (hm : Function.Injective m) (hgt : ∀ i, 1 < m i)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i)
    (N : ℕ) (hN : 0 < N) (hodd : Odd N) (hdiv : ∀ i, m i ∣ N)
    (g : ℕ → ℤ) :
    (∀ n ∈ nontrivialDivisors N, 1 < n ∧ Odd n) ∧
    (∀ i, completedResidue m a g (m i) = a i) ∧
    (∀ x : ℤ, ∃ n : ↥(nontrivialDivisors N),
      (n.val : ℤ) ∣ x-completedResidue m a g n.val) := by
  refine ⟨?_,completedResidue_old m a g hm,?_⟩
  · intro n hn
    have hh := (mem_nontrivialDivisors N n hN).mp hn
    exact ⟨hh.1,hodd.of_dvd_nat hh.2⟩
  · apply completed_cover m a g hm
    · intro i
      exact (mem_nontrivialDivisors N (m i) hN).mpr ⟨hgt i,hdiv i⟩
    · exact hc

/-- Avoidance is required only of protected classes whose modulus properly
divides the class being completed. -/
def AvoidsProtected {J : Type*} (d : J → ℕ) (c : J → ℤ)
    (n : ℕ) (b : ℤ) : Prop :=
  ∀ j, d j ≠ n → d j ∣ n → ¬ (d j : ℤ) ∣ b-c j

/-- One common integer outside the protected classes suffices to fill every
missing pattern while keeping every old residue unchanged. -/
theorem complete_avoids_protected {I J : Type*}
    (m : I → ℕ) (a : I → ℤ) (d : J → ℕ) (c : J → ℤ)
    (hold : ∀ i, AvoidsProtected d c (m i) (a i))
    (g : ℤ) (hg : ∀ j, ¬ (d j : ℤ) ∣ g-c j) (n : ℕ) :
    AvoidsProtected d c n (completedResidue m a (fun _ => g) n) := by
  apply completed_property m a (fun _ => g) (AvoidsProtected d c) hold
  intro n hn j hne hd
  exact hg j

/-- Arbitrarily large exponent extensions are legitimate for this completion:
all old moduli still divide N*q^T, and oddness is preserved. -/
theorem enlarged_odd_period (N q T : ℕ) (hN : 0 < N) (hNodd : Odd N)
    (hq : 0 < q) (hqodd : Odd q) :
    0 < N*q^T ∧ Odd (N*q^T) ∧ N ∣ N*q^T := by
  exact ⟨Nat.mul_pos hN (pow_pos hq T),hNodd.mul (hqodd.pow),dvd_mul_right N (q^T)⟩

/-- The specific common filling point for normalized pure3 and pure9. -/
lemma ternary_filling_point : ¬ (3 : ℤ) ∣ (-1)-0 ∧ ¬ (9 : ℤ) ∣ (-1)-1 := by
  norm_num

#print axioms completed_cover
#print axioms full_divisor_completion
#print axioms complete_avoids_protected
#print axioms enlarged_odd_period
end Erdos7NonemptyArithmeticCompletion
