import Submission.LocalCubeDifferences
import Submission.RepeatedCubeDifferences

/-! Unbounded cliques in one fixed-positional-pair graph. This obstructs a
stronger coloring condition, not ordinary cube-Sidon colorings or density. -/

namespace Erdos1206.PositionalCubeCliques
open scoped Classical
set_option maxHeartbeats 1000000

/-- A common dilation of `1,...,k` is a clique in the graph whose edges are
second/fourth positional pairs of strict positive cubic collisions. -/
theorem second_fourth_cliques (k : ℕ) :
    ∃ D : ℕ, 0<D ∧ ∀ i j : Fin k, i<j → ∃ a c : ℕ,
      0<a ∧ a<D*(i.val+1) ∧ D*(i.val+1)<c ∧ c<D*(j.val+1) ∧
      a^3+(D*(j.val+1))^3=(D*(i.val+1))^3+c^3 := by
  have hex (i j : Fin k) : ∃ a c : ℚ, 0<a ∧ 0<c ∧
      (i<j → a<(i.val : ℚ)+1 ∧ (i.val : ℚ)+1<c ∧ c<(j.val : ℚ)+1 ∧
        a^3+((j.val : ℚ)+1)^3=((i.val : ℚ)+1)^3+c^3) := by
    by_cases hij : i<j
    · have hpos : (0 : ℚ)<(i.val : ℚ)+1 := by positivity
      have hijQ : (i.val : ℚ)+1<(j.val : ℚ)+1 := by exact_mod_cast (Nat.add_lt_add_right hij 1)
      obtain ⟨a,c,ha,hab,hbc,hcd,he⟩ := LocalCubeDifferences.second_fourth_pair hpos hijQ
      exact ⟨a,c,ha,hpos.trans hbc,fun _ => ⟨hab,hbc,hcd,he⟩⟩
    · exact ⟨1,1,by norm_num,by norm_num,fun hh => (hij hh).elim⟩
  choose a c ha hc hpair using hex
  let f : Fin k × Fin k × Bool → ℚ := fun p => if p.2.2 then c p.1 p.2.1 else a p.1 p.2.1
  have hf : ∀ p, 0<f p := by
    rintro ⟨i,j,e⟩
    cases e <;> simp [f,ha,hc]
  obtain ⟨D,hD,t,ht,hcast⟩ := RepeatedCubeDifferences.common_positive_denominator f hf
  have hDQ : (0 : ℚ)<D := by exact_mod_cast hD
  have hA (i j : Fin k) : (t (i,j,false) : ℚ)=(D : ℚ)*a i j := by
    simpa [f] using hcast (i,j,false)
  have hC (i j : Fin k) : (t (i,j,true) : ℚ)=(D : ℚ)*c i j := by
    simpa [f] using hcast (i,j,true)
  refine ⟨D,hD,?_⟩
  intro i j hij
  obtain ⟨hab,hbc,hcd,he⟩ := hpair i j hij
  refine ⟨t (i,j,false),t (i,j,true),ht _,?_,?_,?_,?_⟩
  · have h := mul_lt_mul_of_pos_left hab hDQ
    rw [← hA i j] at h
    exact_mod_cast h
  · have h := mul_lt_mul_of_pos_left hbc hDQ
    rw [← hC i j] at h
    exact_mod_cast h
  · have h := mul_lt_mul_of_pos_left hcd hDQ
    rw [← hC i j] at h
    exact_mod_cast h
  · have h : (t (i,j,false) : ℚ)^3+((D : ℚ)*((j.val : ℚ)+1))^3=
        ((D : ℚ)*((i.val : ℚ)+1))^3+(t (i,j,true) : ℚ)^3 := by
      rw [hA,hC]
      linear_combination (D : ℚ)^3*he
    exact_mod_cast h

/-- No fixed finite coloring can separate the second and fourth roots of
every strict cubic collision. This is stronger than Sidon coloring. -/
theorem no_finite_second_fourth_coloring (k : ℕ) (color : ℕ → Fin k) :
    ∃ a b c d : ℕ, 0<a ∧ a<b ∧ b<c ∧ c<d ∧
      a^3+d^3=b^3+c^3 ∧ color b=color d := by
  obtain ⟨D,hD,hpair⟩ := second_fourth_cliques (k+1)
  obtain ⟨i,j,hij,hcolor⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (k+1) => color (D*(i.val+1))) (by simp)
  rcases lt_or_gt_of_ne hij with h | h
  · obtain ⟨a,c,ha,hab,hbc,hcd,he⟩ := hpair i j h
    exact ⟨a,D*(i.val+1),c,D*(j.val+1),ha,hab,hbc,hcd,he,hcolor⟩
  · obtain ⟨a,c,ha,hab,hbc,hcd,he⟩ := hpair j i h
    exact ⟨a,D*(j.val+1),c,D*(i.val+1),ha,hab,hbc,hcd,he,hcolor.symm⟩

#print axioms second_fourth_cliques
#print axioms no_finite_second_fourth_coloring
end Erdos1206.PositionalCubeCliques
