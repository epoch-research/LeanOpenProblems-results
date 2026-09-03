import FormalConjecturesUtil

/-!
A small exact obstruction to extending one saved finite four-coloring.
The hypotheses specify seven prime colors; unrestricted four-colorability
and the positive-density conjecture remain unresolved.
-/

namespace Erdos1206.FourColorExtensionObstruction

/-- These seven prime colors, taken from a finite coloring through 30000,
force a monochromatic collision at 30010 in any multiplicative extension. -/
theorem prescribed_prime_colors_obstruct (c : ℕ → ZMod 4)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → c (a*b)=c a+c b)
    (h2 : c 2=0) (h3 : c 3=3) (h5 : c 5=3)
    (h2081 : c 2081=0) (h2399 : c 2399=3)
    (h3001 : c 3001=0) (h7517 : c 7517=0) :
    ¬ IsSidon ((fun n : ℕ => n^3) '' {n | c n=3}) := by
  have h22551 : c 22551=3 := by
    change c (3*7517)=3
    rw [hmul 3 7517 (by omega) (by omega),h3,h7517,add_zero]
  have h24972 : c 24972=3 := by
    change c (2*(2*(3*2081)))=3
    rw [hmul 2 (2*(3*2081)) (by omega) (by omega),
      hmul 2 (3*2081) (by omega) (by omega),
      hmul 3 2081 (by omega) (by omega),h2,h3,h2081]
    simp
  have h30010 : c 30010=3 := by
    change c (2*(5*3001))=3
    rw [hmul 2 (5*3001) (by omega) (by omega),
      hmul 5 3001 (by omega) (by omega),h2,h5,h3001]
    simp
  intro hs
  have hh := hs
    _ ⟨2399,h2399,rfl⟩ _ ⟨22551,h22551,rfl⟩
    _ ⟨30010,h30010,rfl⟩ _ ⟨24972,h24972,rfl⟩
    (by norm_num : (2399 : ℕ)^3+30010^3=22551^3+24972^3)
  norm_num at hh

#print axioms prescribed_prime_colors_obstruct

end Erdos1206.FourColorExtensionObstruction
