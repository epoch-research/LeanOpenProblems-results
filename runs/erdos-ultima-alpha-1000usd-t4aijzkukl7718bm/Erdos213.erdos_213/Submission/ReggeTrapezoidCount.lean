import Submission.ReggeCircle

/-! The obstruction to covering every quadruple by a parallel-edge pair.
All bounds in this file concern this special family of configurations. -/
namespace Erdos213.ReggeTrapezoidCount
open ReggeCircle

/-- Six vertices cannot have all their triples covered by adjoining each
vertex to a matching on the other five vertices. -/
theorem no_six_cover {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.card = 6)
    (T : ι → Finset (Finset ι))
    (hsub : ∀ i ∈ s, ∀ e ∈ T i, e ⊆ s.erase i)
    (hcard : ∀ i ∈ s, ∀ e ∈ T i, e.card = 2)
    (hdisj : ∀ i ∈ s, (T i : Set (Finset ι)).PairwiseDisjoint id)
    (hcover : ∀ q ∈ s.powersetCard 3,
      ∃ i ∈ s, ∃ e ∈ T i, q = insert i e) : False := by
  have hbound (i : ι) (hi : i ∈ s) : (T i).card ≤ 2 := by
    have hu : (T i).biUnion id ⊆ s.erase i := by
      intro j hj
      obtain ⟨e,he,hj⟩ := Finset.mem_biUnion.mp hj
      exact hsub i hi e he hj
    have hh := Finset.card_le_card hu
    rw [Finset.card_biUnion (hdisj i hi), Finset.card_erase_of_mem hi,hs] at hh
    dsimp only [id_eq] at hh
    rw [Finset.sum_const_nat (fun e he => hcard i hi e he)] at hh
    omega
  let U : ι → Finset (Finset ι) := fun i => (T i).image (insert i)
  have hc : s.powersetCard 3 ⊆ s.biUnion U := by
    intro q hq
    obtain ⟨i,hi,e,he,rfl⟩ := hcover q hq
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩
  have h₁ := Finset.card_le_card hc
  have h₂ : (s.biUnion U).card ≤ s.card * 2 := calc
    _ ≤ ∑ i ∈ s, (U i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ s, 2 := Finset.sum_le_sum (fun i hi =>
      Finset.card_image_le.trans (hbound i hi))
    _ = _ := Finset.sum_const_nat (fun _ _ => rfl)
  rw [Finset.card_powersetCard,hs] at h₁
  rw [hs] at h₂
  norm_num [Nat.choose] at h₁ h₂
  omega

/-- Two-element constant-value subsets are disjoint when every fiber
has at most two elements. -/
lemma pairwiseDisjoint_constant_pairs {ι α : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → α)
    (hf : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s,
      f a = f b → f a = f c → a = b ∨ a = c ∨ b = c)
    (T : Finset (Finset ι))
    (hT : ∀ e ∈ T, e ⊆ s ∧ e.card = 2 ∧ ∀ a ∈ e, ∀ b ∈ e, f a = f b) :
    (T : Set (Finset ι)).PairwiseDisjoint id := by
  intro e he g hg hne
  apply Finset.disjoint_left.mpr
  intro a hae hag
  have he' := hT e he
  have hg' := hT g hg
  have hu : (e ∪ g).card ≤ 2 := by
    by_contra hn
    obtain ⟨b,hb,c,hc,d,hd,hbc,hbd,hcd⟩ := Finset.two_lt_card.mp (show 2 < (e ∪ g).card from by omega)
    have hs (x) (hx : x ∈ e ∪ g) : x ∈ s := by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact he'.1 hx
      · exact hg'.1 hx
    have hv (x) (hx : x ∈ e ∪ g) : f x = f a := by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact he'.2.2 x hx a hae
      · exact hg'.2.2 x hx a hag
    rcases hf b (hs b hb) c (hs c hc) d (hs d hd)
      ((hv b hb).trans (hv c hc).symm) ((hv b hb).trans (hv d hd).symm) with h | h | h
    · exact hbc h
    · exact hbd h
    · exact hcd h
  have heq : e = e ∪ g := Finset.eq_of_subset_of_card_le Finset.subset_union_left
    (by simpa only [he'.2.1] using hu)
  have hgq : g = e ∪ g := Finset.eq_of_subset_of_card_le Finset.subset_union_right
    (by simpa only [hg'.2.1] using hu)
  exact hne (heq.trans hgq.symm)

def area {ι : Type*} (x y : ι → ℝ) (a b c : ι) : ℝ :=
  (x b-x a)*(y c-y a)-(y b-y a)*(x c-x a)

/-- A nonzero projection has fibers of size at most two on a set with
no three collinear points. -/
lemma projection_fibers {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (htri : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
      area x y a b c ≠ 0)
    (A B : ℝ) (hn : A ≠ 0 ∨ B ≠ 0)
    (a : ι) (ha : a ∈ s) (b : ι) (hb : b ∈ s) (c : ι) (hc : c ∈ s)
    (hab : A*y a-B*x a = A*y b-B*x b)
    (hac : A*y a-B*x a = A*y c-B*x c) : a = b ∨ a = c ∨ b = c := by
  by_contra hh
  push_neg at hh
  have ht := htri a ha b hb c hc hh.1 hh.2.1 hh.2.2
  have hA : A * area x y a b c = 0 := by
    dsimp [area]
    linear_combination (x c-x a)*hab - (x b-x a)*hac
  have hB : B * area x y a b c = 0 := by
    dsimp [area]
    linear_combination (y c-y a)*hab - (y b-y a)*hac
  rcases hn with hn | hn
  · exact mul_ne_zero hn ht hA
  · exact mul_ne_zero hn ht hB

/-- Among an origin and six further distinct points, with no three of the
six further points collinear, some origin-based quadruple has no parallel
opposite edges. This is already sufficient for excluding seven-point GP
configurations all of whose quadruples come from cyclic Regge orbits. -/
theorem no_seven_trapezoids {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.card = 6) (x y : ι → ℝ)
    (hn : ∀ i ∈ s, x i ≠ 0 ∨ y i ≠ 0)
    (htri : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
      area x y a b c ≠ 0)
    (hp : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
      ∃ k, parallel (x a) (y a) (x b) (y b) (x c) (y c) k = 0) : False := by
  classical
  let val : ι → ι → ℝ := fun i j => x i*y j-y i*x j
  let T : ι → Finset (Finset ι) := fun i =>
    ((s.erase i).powersetCard 2).filter (fun e => ∀ a ∈ e, ∀ b ∈ e, val i a = val i b)
  have hT (i e) (he : e ∈ T i) :
      e ⊆ s.erase i ∧ e.card = 2 ∧ ∀ a ∈ e, ∀ b ∈ e, val i a = val i b := by
    exact ⟨(Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).1,
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2,(Finset.mem_filter.mp he).2⟩
  apply no_six_cover s hs T
  · intro i hi e he
    exact (hT i e he).1
  · intro i hi e he
    exact (hT i e he).2.1
  · intro i hi
    apply pairwiseDisjoint_constant_pairs s (val i)
    · exact projection_fibers s x y htri (x i) (y i) (hn i hi)
    · intro e he
      exact ⟨(hT i e he).1.trans (Finset.erase_subset _ _),(hT i e he).2⟩
  · intro q hq
    obtain ⟨hqs,hqc⟩ := Finset.mem_powersetCard.mp hq
    obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hqc
    have ha : a ∈ s := hqs (by simp)
    have hb : b ∈ s := hqs (by simp)
    have hc : c ∈ s := hqs (by simp)
    have pair (i j k : ι) (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s)
        (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
        (he : val i j = val i k) : ({j,k} : Finset ι) ∈ T i := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro l hl
          rcases Finset.mem_insert.mp hl with rfl | hl
          · exact Finset.mem_erase.mpr ⟨hij.symm,hj⟩
          · have hl' := Finset.mem_singleton.mp hl
            subst l
            exact Finset.mem_erase.mpr ⟨hik.symm,hk⟩
        · simp [hjk]
      · intro l hl m hm
        simp only [Finset.mem_insert,Finset.mem_singleton] at hl hm
        rcases hl with rfl | rfl <;> rcases hm with rfl | rfl
        · rfl
        · exact he
        · exact he.symm
        · rfl
    obtain ⟨k,hk⟩ := hp a ha b hb c hc hab hac hbc
    fin_cases k
    · refine ⟨a,ha,{b,c},pair a b c ha hb hc hab hac hbc ?_,rfl⟩
      change x a*(y c-y b)-y a*(x c-x b) = 0 at hk
      dsimp [val]
      linear_combination -hk
    · refine ⟨b,hb,{a,c},pair b a c hb ha hc hab.symm hbc hac ?_,?_⟩
      · change x b*(y c-y a)-y b*(x c-x a) = 0 at hk
        dsimp [val]
        linear_combination -hk
      · ext i
        simp only [Finset.mem_insert,Finset.mem_singleton]
        tauto
    · refine ⟨c,hc,{a,b},pair c a b hc ha hb hac.symm hbc.symm hab ?_,?_⟩
      · change x c*(y b-y a)-y c*(x b-x a) = 0 at hk
        dsimp [val]
        linear_combination -hk
      · ext i
        simp only [Finset.mem_insert,Finset.mem_singleton]
        tauto

/-- A coordinate-level exclusion of seven-point general-position outputs
from cyclic Regge orbits. Each origin-based quadruple can start from its
own arbitrary cyclic source and use its own arbitrary sequence of Regge
moves, vertex relabellings, and real scales. No rationality or height
restriction is imposed on either source or target. -/
theorem no_seven_cyclic_orbits {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.card = 6) (x y : ι → ℝ)
    (hn : ∀ i ∈ s, x i ≠ 0 ∨ y i ≠ 0)
    (htri : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
      area x y a b c ≠ 0)
    (hcircle : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
      circle (x a) (y a) (x b) (y b) (x c) (y c) ≠ 0)
    (hsource : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
      ∃ e f : ReggeMixed.Edges, ∃ X Y U V Z W : ℝ,
        Realizes e X Y U V Z W ∧ (∀ i, 0 < e i) ∧ circle X Y U V Z W = 0 ∧
        Orbit e f ∧ Realizes f (x a) (y a) (x b) (y b) (x c) (y c)) : False := by
  apply no_seven_trapezoids s hs x y hn htri
  intro a ha b hb c hc hab hac hbc
  obtain ⟨e,f,X,Y,U,V,Z,W,he,hpos,hc0,horbit,hf⟩ := hsource a ha b hb c hc hab hac hbc
  have he0 := special_of_circle e X Y U V Z W he hpos hc0
  exact (circle_or_parallel f (x a) (y a) (x b) (y b) (x c) (y c) hf
    (special_orbit horbit he0)).resolve_left (hcircle a ha b hb c hc hab hac hbc)

#print axioms no_six_cover
#print axioms pairwiseDisjoint_constant_pairs
#print axioms projection_fibers
#print axioms no_seven_trapezoids
#print axioms no_seven_cyclic_orbits
end Erdos213.ReggeTrapezoidCount
