import Submission.SquarefreeColoringReduction

/-!
Every squarefree fiber of a completely additive ZMod 4 character has positive
lower density if 2, 3, and 5 receive odd colors. The bounded multiplier set is
{1,2,3,5,6,10,15,30}. No cube-Sidon character is constructed here.
-/
namespace Erdos1206.OddPrimeCharacterDensity

private def multiplier : Fin 8 → ℕ := ![1,2,3,5,6,10,15,30]
private def colors (a b d : ZMod 4) : Fin 8 → ZMod 4 :=
  ![0,a,b,d,a+b,a+d,b+d,a+b+d]

private lemma multiplier_bounds : ∀ i : Fin 8,
    0 < multiplier i ∧ multiplier i ≤ 30 ∧ Squarefree (multiplier i) := by
  decide +kernel

private lemma colors_surjective : ∀ a b d r : ZMod 4,
    2*a=2 → 2*b=2 → 2*d=2 → ∃ i : Fin 8, colors a b d i=r := by
  decide +kernel

private lemma multiplier_color (c : ℕ → ZMod 4)
    (hmul : ∀ a b : ℕ, 0<a → 0<b → c (a*b)=c a+c b) (i : Fin 8) :
    c (multiplier i)=colors (c 2) (c 3) (c 5) i := by
  have h1 : c 1=0 := by
    have hh := hmul 1 1 (by omega) (by omega)
    exact add_left_cancel (show c 1+c 1=c 1+0 by simpa using hh.symm)
  have h6 : c 6=c 2+c 3 := hmul 2 3 (by omega) (by omega)
  have h10 : c 10=c 2+c 5 := hmul 2 5 (by omega) (by omega)
  have h15 : c 15=c 3+c 5 := hmul 3 5 (by omega) (by omega)
  have h30 : c 30=c 2+c 3+c 5 := by
    change c (6*5)=_
    rw [hmul 6 5 (by omega) (by omega),h6]
  fin_cases i <;> simpa [multiplier,colors] using
    (by first | exact h1 | rfl | exact h6 | exact h10 | exact h15 | exact h30)

/-- Three odd prime colors suffice to make every squarefree color fiber dense.
This is a density statement only: none of these fibers is asserted cube-Sidon. -/
theorem squarefree_fiber_lowerDensity_pos (c : ℕ → ZMod 4)
    (hmul : ∀ a b : ℕ, 0<a → 0<b → c (a*b)=c a+c b)
    (h2 : 2*c 2=2) (h3 : 2*c 3=2) (h5 : 2*c 5=2) (r : ZMod 4) :
    0 < ({n : ℕ | Squarefree n ∧ c n=r} : Set ℕ).lowerDensity := by
  obtain ⟨D,hD,hpreserve⟩ := squarefree_prefix_multipliers 30
  apply positive_density_of_dilation_cover_on hD (by decide : 0<30)
  intro n hn
  obtain ⟨i,hi⟩ := colors_surjective (c 2) (c 3) (c 5) (r-c n) h2 h3 h5
  obtain ⟨hmi,hmb,hms⟩ := multiplier_bounds i
  obtain ⟨hn0,hpn⟩ := hpreserve n hn
  refine ⟨multiplier i,hmi,hmb,?_,?_⟩
  · simpa only [Nat.mul_comm] using hpn (multiplier i) hms hmb
  · rw [hmul _ _ hmi hn0,multiplier_color c hmul,hi]
    ring

/-- For this class of characters it is enough to construct just one
cube-Sidon squarefree fiber. Existence of such a character remains unproved. -/
theorem sidon_fiber_suffices (c : ℕ → ZMod 4)
    (hmul : ∀ a b : ℕ, 0<a → 0<b → c (a*b)=c a+c b)
    (h2 : 2*c 2=2) (h3 : 2*c 3=2) (h5 : 2*c 5=2) (r : ZMod 4)
    (hs : IsSidon ((fun n : ℕ => n^3) '' {n | Squarefree n ∧ c n=r})) :
    ∃ A : Set ℕ, A.Infinite ∧ 0<A.lowerDensity ∧
      IsSidon ((fun n : ℕ => n^3) '' A) := by
  have hd := squarefree_fiber_lowerDensity_pos c hmul h2 h3 h5 r
  refine ⟨{n | Squarefree n ∧ c n=r},?_,hd,hs⟩
  by_contra hn
  have hz : ({n : ℕ | Squarefree n ∧ c n=r} : Set ℕ).lowerDensity = 0 :=
    (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hn)).liminf_eq
  rw [hz] at hd
  exact (lt_irrefl 0) hd

#print axioms squarefree_fiber_lowerDensity_pos
#print axioms sidon_fiber_suffices
end Erdos1206.OddPrimeCharacterDensity
