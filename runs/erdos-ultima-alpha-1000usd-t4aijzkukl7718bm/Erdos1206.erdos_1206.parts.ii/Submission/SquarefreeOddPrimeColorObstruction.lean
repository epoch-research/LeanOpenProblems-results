import FormalConjecturesUtil

/-!
Three squarefree cubic collisions obstruct a stronger edge-sum condition on
cyclic four-colorings with odd prime colors. This does not rule out ordinary
proper coloring and does not settle the density conjecture.
-/

namespace Erdos1206.SquarefreeOddPrimeColorObstruction

private lemma squarefree_witnesses :
    Squarefree 1294 ∧ Squarefree 1914 ∧ Squarefree 4453 ∧ Squarefree 4533 ∧
    Squarefree 2031 ∧ Squarefree 4529 ∧ Squarefree 6001 ∧ Squarefree 6699 ∧
    Squarefree 4062 ∧ Squarefree 12002 ∧ Squarefree 31171 ∧ Squarefree 31731 := by
  norm_num only [Nat.squarefree_iff_minSqFac]
  decide +kernel

private lemma transport_sum (c : ℕ → ZMod 4)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → c (a*b) = c a+c b) :
    (c 1294+c 1914+c 4453+c 4533) +
      (c 2031+c 4529+c 6001+c 6699) =
    (c 4062+c 12002+c 31171+c 31731) + 2*(c 647+c 957) := by
  have h1294 : c 1294 = c 2+c 647 := hmul 2 647 (by omega) (by omega)
  have h1914 : c 1914 = c 2+c 957 := hmul 2 957 (by omega) (by omega)
  have h4529 : c 4529 = c 7+c 647 := hmul 7 647 (by omega) (by omega)
  have h6699 : c 6699 = c 7+c 957 := hmul 7 957 (by omega) (by omega)
  have h4062 : c 4062 = c 2+c 2031 := hmul 2 2031 (by omega) (by omega)
  have h12002 : c 12002 = c 2+c 6001 := hmul 2 6001 (by omega) (by omega)
  have h31171 : c 31171 = c 7+c 4453 := hmul 7 4453 (by omega) (by omega)
  have h31731 : c 31731 = c 7+c 4533 := hmul 7 4533 (by omega) (by omega)
  rw [h1294,h1914,h4529,h6699,h4062,h12002,h31171,h31731]
  ring

/-- Even on squarefree roots, requiring every edge to have total color two
is stronger than ordinary proper four-coloring and can be inconsistent.
The equation `2*c p=2` means that the prime's color is odd in `ZMod 4`. -/
theorem no_uniform_edge_sum_two (c : ℕ → ZMod 4)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → c (a*b) = c a+c b)
    (hodd : ∀ p : ℕ, p.Prime → 2*c p=2) :
    ¬ (∀ a b d e : ℕ,
      Squarefree a → Squarefree b → Squarefree d → Squarefree e →
      0<a → a<b → b<d → d<e → a^3+e^3=b^3+d^3 →
      c a+c b+c d+c e=2) := by
  intro hc
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ := squarefree_witnesses
  have he1 := hc 1294 1914 4453 4533 h1 h2 h3 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he2 := hc 2031 4529 6001 6699 h5 h6 h7 h8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he3 := hc 4062 12002 31171 31731 h9 h10 h11 h12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp3 := hodd 3 (by norm_num)
  have hp11 := hodd 11 (by norm_num)
  have hp29 := hodd 29 (by norm_num)
  have hp647 := hodd 647 (by norm_num)
  have h957 : c 957 = c 3+(c 11+c 29) := by
    change c (3*(11*29)) = _
    rw [hmul 3 (11*29) (by omega) (by omega),hmul 11 29 (by omega) (by omega)]
  have hz : 2*(c 647+c 957)=0 := by
    rw [h957,mul_add,mul_add,mul_add,hp647,hp3,hp11,hp29]
    decide +kernel
  have ht := transport_sum c hmul
  rw [he1,he2,he3,hz] at ht
  exact (by decide : (2:ZMod 4)+2 ≠ 2+0) ht

#print axioms no_uniform_edge_sum_two
end Erdos1206.SquarefreeOddPrimeColorObstruction
