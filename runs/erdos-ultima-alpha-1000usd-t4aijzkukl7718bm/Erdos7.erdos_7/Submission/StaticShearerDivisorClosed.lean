import Submission.StaticShearerBarrier

/-!
Divisor-closed extension of the static star-polynomial limitation.
It is a partial family with private points and an uncovered integer, not a cover.
-/
namespace Erdos7StaticShearerDivisorClosed
open Erdos7StaticShearerBarrier

abbrev Index (s : Finset Nat.Primes) := Option (Bool × s)

def modulus (s : Finset Nat.Primes) : Index s → ℕ
  | none => 3
  | some (b,p) => if b then 3 * (p.val : ℕ) else (p.val : ℕ)

def residue (s : Finset Nat.Primes) : Index s → ℕ
  | none => 0
  | some (b,_) => if b then 1 else 2

lemma prime_ne_triple (p q : Nat.Primes) (hp : 3 < (p : ℕ)) :
    (p : ℕ) ≠ 3*(q : ℕ) := by
  intro h
  have hd : 3 ∣ (p : ℕ) := h ▸ dvd_mul_right _ _
  rcases (Nat.dvd_prime p.property).mp hd with h | h <;> omega

lemma modulus_injective (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 3 < (p : ℕ)) :
    Function.Injective (modulus s) := by
  intro i j h
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some v =>
          rcases v with ⟨b,p⟩
          have hp := hs p.val p.property
          cases b <;> dsimp [modulus] at h <;> omega
  | some v =>
      rcases v with ⟨b,p⟩
      cases j with
      | none =>
          have hp := hs p.val p.property
          cases b <;> dsimp [modulus] at h <;> omega
      | some w =>
          rcases w with ⟨c,q⟩
          have hp := hs p.val p.property
          have hq := hs q.val q.property
          cases b <;> cases c <;> dsimp [modulus] at h
          · have he : p=q := Subtype.ext (Subtype.ext h)
            subst q; rfl
          · exact False.elim (prime_ne_triple p.val q.val hp h)
          · exact False.elim (prime_ne_triple q.val p.val hq h.symm)
          · have he : p=q := Subtype.ext (Subtype.ext (by omega))
            subst q; rfl

lemma odd_nontrivial (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 3 < (p : ℕ))
    (i : Index s) : Odd (modulus s i) ∧ 1 < modulus s i := by
  cases i with
  | none => change Odd (3:ℕ) ∧ 1 < (3:ℕ); decide
  | some v =>
      rcases v with ⟨b,p⟩
      have hp := hs p.val p.property
      have ho := p.val.property.odd_of_ne_two (by omega : (p.val : ℕ) ≠ 2)
      cases b
      · exact ⟨ho, by dsimp [modulus]; omega⟩
      · exact ⟨(by decide : Odd (3:ℕ)).mul ho, by dsimp [modulus]; omega⟩

lemma modEq_left_iff {n x a b : ℕ} (h : Nat.ModEq n x a) :
    Nat.ModEq n x b ↔ Nat.ModEq n a b :=
  ⟨fun hh => h.symm.trans hh, fun hh => h.trans hh⟩

lemma membership_coordinates (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 3 < (p : ℕ))
    (x c : ℕ) (a : Nat.Primes → ℕ) (h₃ : Nat.ModEq 3 x c)
    (ha : ∀ p ∈ s, Nat.ModEq (p : ℕ) x (a p)) (i : Index s) :
    Nat.ModEq (modulus s i) x (residue s i) ↔
      match i with
      | none => Nat.ModEq 3 c 0
      | some (false,p) => Nat.ModEq (p.val : ℕ) (a p.val) 2
      | some (true,p) => Nat.ModEq 3 c 1 ∧ Nat.ModEq (p.val : ℕ) (a p.val) 1 := by
  cases i with
  | none => exact modEq_left_iff h₃
  | some v =>
      rcases v with ⟨b,p⟩
      cases b
      · exact modEq_left_iff (ha p.val p.property)
      · change Nat.ModEq (3*(p.val : ℕ)) x 1 ↔ _
        have hc : Nat.Coprime 3 (p.val : ℕ) :=
          (Nat.coprime_primes (by decide) p.val.property).mpr (by have := hs p.val p.property; omega)
        rw [← Nat.modEq_and_modEq_iff_modEq_mul hc]
        exact and_congr (modEq_left_iff h₃) (modEq_left_iff (ha p.val p.property))

lemma nat_private (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 3 < (p : ℕ))
    (i : Index s) : ∃ x : ℕ, ∀ j, Nat.ModEq (modulus s j) x (residue s j) ↔ i=j := by
  classical
  cases i with
  | none =>
      refine ⟨0, ?_⟩
      intro j
      cases j with
      | none => simp [modulus, residue, Nat.ModEq]
      | some v =>
          rcases v with ⟨b,p⟩
          have hp := hs p.val p.property
          have h2 : 2 < (p.val : ℕ) := by omega
          have h1 : 1 < 3*(p.val : ℕ) := by omega
          cases b <;> simp [modulus, residue, Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  | some v =>
      rcases v with ⟨b,p⟩
      let c : ℕ := if b then 1 else 2
      let a : Nat.Primes → ℕ := fun q => if q=p.val then c else 0
      obtain ⟨x, h₃, hx⟩ := exists_coordinates s hs c a
      refine ⟨x, ?_⟩
      intro j
      rw [membership_coordinates s hs x c a h₃ hx j]
      cases j with
      | none => cases b <;> simp [c, Nat.ModEq]
      | some w =>
          rcases w with ⟨d,q⟩
          have hq := hs q.val q.property
          have h1 : 1 < (q.val : ℕ) := by omega
          have h2 : 2 < (q.val : ℕ) := by omega
          by_cases he : p=q
          · subst q
            cases b <;> cases d <;>
              simp [a, c, Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
          · have hv : q.val ≠ p.val := fun h => he (Subtype.ext h.symm)
            cases b <;> cases d <;>
              simp [a, c, hv, he, Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]

lemma private_points (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 3 < (p : ℕ)) :
    ∀ i : Index s, ∃ x : ℤ, ∀ j, (modulus s j : ℤ) ∣ x-(residue s j : ℤ) ↔ i=j := by
  intro i
  obtain ⟨x, hx⟩ := nat_private s hs i
  refine ⟨(x : ℤ), ?_⟩
  intro j
  rw [dvd_sub_comm, ← Nat.modEq_iff_dvd]
  exact hx j

lemma exists_uncovered (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 3 < (p : ℕ)) :
    ∃ z : ℤ, ∀ i : Index s, ¬ (modulus s i : ℤ) ∣ z-(residue s i : ℤ) := by
  obtain ⟨x, h₃, hx⟩ := exists_coordinates s hs 2 (fun _ => 0)
  refine ⟨(x : ℤ), ?_⟩
  intro i
  rw [dvd_sub_comm, ← Nat.modEq_iff_dvd, membership_coordinates s hs x 2 (fun _ => 0) h₃ hx i]
  cases i with
  | none => norm_num [Nat.ModEq]
  | some v =>
      rcases v with ⟨b,p⟩
      have hp := hs p.val p.property
      have h2 : 2 < (p.val : ℕ) := by omega
      cases b <;> simp [Nat.ModEq, Nat.mod_eq_of_lt h2]

lemma divisor_triple_prime {p d : ℕ} (hp : p.Prime) (hd : 1 < d) (hdiv : d ∣ 3*p) :
    d=3 ∨ d=p ∨ d=3*p := by
  by_cases h3 : 3 ∣ d
  · obtain ⟨k, rfl⟩ := h3
    have hk : k ∣ p := (Nat.mul_dvd_mul_iff_left (by decide : 0 < (3:ℕ))).mp hdiv
    rcases (Nat.dvd_prime hp).mp hk with rfl | rfl
    · simp
    · simp
  · have hc : Nat.Coprime d 3 := ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
    have hdp := hc.dvd_of_dvd_mul_left hdiv
    rcases (Nat.dvd_prime hp).mp hdp with h | h
    · omega
    · exact Or.inr (Or.inl h)

/-- Every nontrivial divisor of every modulus occurs. -/
lemma divisor_closed (s : Finset Nat.Primes) (i : Index s) (d : ℕ)
    (hd : 1 < d) (hdiv : d ∣ modulus s i) : ∃ j, modulus s j=d := by
  cases i with
  | none =>
      rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
      · omega
      · exact ⟨none, h.symm⟩
  | some v =>
      rcases v with ⟨b,p⟩
      cases b
      · rcases (Nat.dvd_prime p.val.property).mp hdiv with h | h
        · omega
        · exact ⟨some (false,p), h.symm⟩
      · rcases divisor_triple_prime p.val.property hd hdiv with h | h | h
        · exact ⟨none, h.symm⟩
        · exact ⟨some (false,p), h.symm⟩
        · exact ⟨some (true,p), h.symm⟩

def starEmbedding (s : Finset Nat.Primes) : Option s → Index s
  | none => none
  | some p => some (true,p)

lemma star_embedding_modulus (s : Finset Nat.Primes) (i : Option s) :
    modulus s (starEmbedding s i) = Erdos7StaticShearerBarrier.modulus s i := by cases i <;> rfl

lemma star_embedding_residue (s : Finset Nat.Primes) (i : Option s) :
    residue s (starEmbedding s i) = Erdos7StaticShearerBarrier.residue s i := by cases i <;> rfl

/-- The negative star polynomial remains an induced-subfamily obstruction after
passing to a divisor-closed, irredundant partial family. It is NOT a cover. -/
theorem exists_divisor_closed_barrier :
    ∃ s : Finset Nat.Primes,
      Function.Injective (modulus s) ∧
      (∀ i, Odd (modulus s i) ∧ 1 < modulus s i) ∧
      (∀ i, ∃ x : ℤ, ∀ j, (modulus s j : ℤ) ∣ x-(residue s j : ℤ) ↔ i=j) ∧
      (∀ i d, 1 < d → d ∣ modulus s i → ∃ j, modulus s j=d) ∧
      (∃ z : ℤ, ∀ i, ¬ (modulus s i : ℤ) ∣ z-(residue s i : ℤ)) ∧
      starPolynomial s < 0 := by
  obtain ⟨s, hs, hn⟩ := exists_negative_star_polynomial
  exact ⟨s, modulus_injective s hs, odd_nontrivial s hs, private_points s hs,
    divisor_closed s, exists_uncovered s hs, hn⟩

#print axioms exists_divisor_closed_barrier

lemma star_embedding_injective (s : Finset Nat.Primes) : Function.Injective (starEmbedding s) := by
  intro i j h
  cases i <;> cases j <;> simp_all [starEmbedding]

lemma induced_star_graph (s : Finset Nat.Primes) (i j : Option s) :
    (¬ ∃ z : ℤ, (modulus s (starEmbedding s i) : ℤ) ∣ z-(residue s (starEmbedding s i) : ℤ) ∧
      (modulus s (starEmbedding s j) : ℤ) ∣ z-(residue s (starEmbedding s j) : ℤ)) ↔
      (i=none ∧ j≠none) ∨ (j=none ∧ i≠none) := by
  simp only [star_embedding_modulus, star_embedding_residue]
  exact Erdos7StaticShearerBarrier.incompatibility_star s i j

#print axioms star_embedding_modulus
#print axioms star_embedding_residue
end Erdos7StaticShearerDivisorClosed
