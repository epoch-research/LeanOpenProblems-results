import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

variable {R : Type*} [CommRing R]

/-- Elementary symmetric "sum of products over k-subsets". -/
def Esym (a : ℕ → R) (k : ℕ) (s : Finset ℕ) : R := ∑ t ∈ powersetCard k s, ∏ i ∈ t, a i

/-- Power sum. -/
def Psym (a : ℕ → R) (k : ℕ) (s : Finset ℕ) : R := ∑ i ∈ s, (a i) ^ k

theorem Esym_zero (a : ℕ → R) (s : Finset ℕ) : Esym a 0 s = 1 := by
  rw [Esym, powersetCard_zero]; simp

theorem Esym_one (a : ℕ → R) (s : Finset ℕ) : Esym a 1 s = ∑ i ∈ s, a i := by
  rw [Esym, powersetCard_one, Finset.sum_map]
  simp

theorem Esym_succ_insert (a : ℕ → R) (k : ℕ) {b : ℕ} {s : Finset ℕ} (hb : b ∉ s) :
    Esym a (k + 1) (insert b s) = Esym a (k + 1) s + a b * Esym a k s := by
  rw [Esym, Esym, Esym, powersetCard_succ_insert hb, Finset.sum_union, Finset.mul_sum]
  · congr 1
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_powersetCard] at ht
      rw [Finset.prod_insert (fun hbt => hb (ht.1 hbt))]
    · intro t ht t' ht' himg
      rw [Finset.mem_coe, Finset.mem_powersetCard] at ht ht'
      have hbt : b ∉ t := fun hbt => hb (ht.1 hbt)
      have hbt' : b ∉ t' := fun hbt => hb (ht'.1 hbt)
      have := congrArg (fun u => Finset.erase u b) himg
      simpa [Finset.erase_insert hbt, Finset.erase_insert hbt'] using this
  · apply Finset.disjoint_left.mpr
    intro t ht htimg
    rw [Finset.mem_powersetCard] at ht
    rw [Finset.mem_image] at htimg
    obtain ⟨t', _, rfl⟩ := htimg
    exact hb (ht.1 (Finset.mem_insert_self b t'))

theorem newton2 (a : ℕ → R) (s : Finset ℕ) :
    2 * Esym a 2 s = (Psym a 1 s) ^ 2 - Psym a 2 s := by
  induction s using Finset.induction with
  | empty => simp [Esym, Psym, powersetCard]
  | @insert b s hb ih =>
    have hE2 := Esym_succ_insert a 1 hb
    rw [Esym_one] at hE2
    have hP1 : Psym a 1 (insert b s) = a b + Psym a 1 s := by
      rw [Psym, Psym, Finset.sum_insert hb]; simp
    have hP2 : Psym a 2 (insert b s) = (a b)^2 + Psym a 2 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hP1' : Psym a 1 s = ∑ i ∈ s, a i := by rw [Psym]; simp
    rw [hE2, hP1, hP2, ← hP1']
    rw [mul_add, ih]
    ring

theorem newton3 (a : ℕ → R) (s : Finset ℕ) :
    3 * Esym a 3 s = Esym a 2 s * Psym a 1 s - Psym a 1 s * Psym a 2 s + Psym a 3 s := by
  induction s using Finset.induction with
  | empty => simp [Esym, Psym, powersetCard]
  | @insert b s hb ih =>
    have hE3 := Esym_succ_insert a 2 hb
    have hE2 := Esym_succ_insert a 1 hb
    rw [Esym_one] at hE2
    have hP1' : (∑ i ∈ s, a i) = Psym a 1 s := by rw [Psym]; simp
    rw [hP1'] at hE2
    have hP1 : Psym a 1 (insert b s) = a b + Psym a 1 s := by
      rw [Psym, Psym, Finset.sum_insert hb]; simp
    have hP2 : Psym a 2 (insert b s) = (a b)^2 + Psym a 2 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hP3 : Psym a 3 (insert b s) = (a b)^3 + Psym a 3 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hN2 := newton2 a s
    rw [hE3, hE2, hP1, hP2, hP3]
    linear_combination ih + (a b) * hN2

theorem newton4 (a : ℕ → R) (s : Finset ℕ) :
    4 * Esym a 4 s
      = Esym a 3 s * Psym a 1 s - Esym a 2 s * Psym a 2 s
        + Psym a 1 s * Psym a 3 s - Psym a 4 s := by
  induction s using Finset.induction with
  | empty => simp [Esym, Psym, powersetCard]
  | @insert b s hb ih =>
    have hE4 := Esym_succ_insert a 3 hb
    have hE3 := Esym_succ_insert a 2 hb
    have hE2 := Esym_succ_insert a 1 hb
    rw [Esym_one] at hE2
    have hP1' : (∑ i ∈ s, a i) = Psym a 1 s := by rw [Psym]; simp
    rw [hP1'] at hE2
    have hP1 : Psym a 1 (insert b s) = a b + Psym a 1 s := by
      rw [Psym, Psym, Finset.sum_insert hb]; simp
    have hP2 : Psym a 2 (insert b s) = (a b)^2 + Psym a 2 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hP3 : Psym a 3 (insert b s) = (a b)^3 + Psym a 3 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hP4 : Psym a 4 (insert b s) = (a b)^4 + Psym a 4 s := by
      rw [Psym, Psym, Finset.sum_insert hb]
    have hN3 := newton3 a s
    rw [hE4, hE3, hE2, hP1, hP2, hP3, hP4]
    linear_combination ih + (a b) * hN3
