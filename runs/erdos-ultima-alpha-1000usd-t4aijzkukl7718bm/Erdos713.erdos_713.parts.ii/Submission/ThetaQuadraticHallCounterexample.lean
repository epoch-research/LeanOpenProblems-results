import FormalConjecturesUtil
import Submission.ThetaQuadraticPlanes

/-! The 32-column quadratic-plane relation refutes a proposed unrestricted
heavy-pair Hall bound. It does not refute the density gap or Erdős 713. -/
open Finset
namespace Erdos713ThetaQuadraticPlanes
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyMatching Erdos713ThetaRigidHeavyMatching
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma row_eq (a : Fin 120) : row Inc a = dataRow a := by
  classical
  ext x
  simp only [mem_row,dataRow,mem_filter,mem_univ,true_and]

lemma supports_eq (p : Pair (Fin 32)) :
    supports Inc p = univ.filter (fun a : Fin 120 => p.val ⊆ dataRow a) := by
  classical
  ext a
  simp only [mem_supports,row_eq,mem_filter,mem_univ,true_and]

lemma codegree_eq (x y : Fin 32) : codegree Inc x y = count x y := by
  classical
  simp only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype,count]

lemma row_card (a : Fin 120) : (row Inc a).card = 4 := by
  rw [row_eq]
  exact dataRow_card a

theorem rigid (a b : Fin 120) (hab : a ≠ b) : (row Inc a ∩ row Inc b).card ≤ 2 := by
  rw [row_eq,row_eq]
  exact rigid_data a b hab

theorem no_theta : ¬ HasTheta Inc := by
  classical
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hab : a 0 ≠ a 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (ha h)
  have hneq (i j : Fin 4) (hij : i ≠ j) : b i ≠ b j := fun h => hij (hb h)
  have hrow (i : Fin 120) (x : Fin 32) : x ∈ dataRow i ↔ Inc i x := by
    simp only [dataRow,mem_filter,mem_univ,true_and]
  have hp : ({b 0,b 1} : Finset (Fin 32)) ⊆ dataRow (a 0) ∩ dataRow (a 1) := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact mem_inter.mpr ⟨(hrow _ _).mpr h00,(hrow _ _).mpr h10⟩
    · exact mem_inter.mpr ⟨(hrow _ _).mpr h01,(hrow _ _).mpr h11⟩
  have hpc : 2 ≤ (dataRow (a 0) ∩ dataRow (a 1)).card := by
    have h := card_le_card hp
    rwa [card_pair (hneq 0 1 (by decide))] at h
  have hx : b 2 ∉ dataRow (a 1) := by
    intro hh
    have hsub : ({b 0,b 1,b 2} : Finset (Fin 32)) ⊆ dataRow (a 0) ∩ dataRow (a 1) := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl|rfl
      · exact hp (by simp)
      · exact hp (by simp)
      · exact mem_inter.mpr ⟨(hrow _ _).mpr h02,hh⟩
    have hc := (card_le_card hsub).trans (rigid_data _ _ hab)
    have he : ({b 0,b 1,b 2} : Finset (Fin 32)).card = 3 := by
      simp [hneq 0 1 (by decide),hneq 0 2 (by decide),hneq 1 2 (by decide)]
    omega
  have hy : b 3 ∉ dataRow (a 0) := by
    intro hh
    have hsub : ({b 0,b 1,b 3} : Finset (Fin 32)) ⊆ dataRow (a 0) ∩ dataRow (a 1) := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl|rfl
      · exact hp (by simp)
      · exact hp (by simp)
      · exact mem_inter.mpr ⟨hh,(hrow _ _).mpr h13⟩
    have hc := (card_le_card hsub).trans (rigid_data _ _ hab)
    have he : ({b 0,b 1,b 3} : Finset (Fin 32)).card = 3 := by
      simp [hneq 0 1 (by decide),hneq 0 3 (by decide),hneq 1 3 (by decide)]
    omega
  have hn := cross_data (a 0) (a 1) hab hpc (b 2) ((hrow _ _).mpr h02) hx
    (b 3) ((hrow _ _).mpr h13) hy
  have hcount : count (b 2) (b 3) = 0 := by
    rw [count_data,if_neg (hneq 2 3 (by decide)),if_neg hn]
  have hpos : 0 < count (b 2) (b 3) := card_pos.mpr
    ⟨a 2,mem_filter.mpr ⟨mem_univ _,h22,h23⟩⟩
  omega

lemma supports_zero_or_three (p : Pair (Fin 32)) :
    (supports Inc p).card = 0 ∨ (supports Inc p).card = 3 := by
  classical
  obtain ⟨x,y,hxy,hp⟩ := card_eq_two.mp (pair_card p)
  have he : supports Inc p = univ.filter (fun a : Fin 120 => Inc a x ∧ Inc a y) := by
    ext a
    simp only [mem_supports,hp,insert_subset_iff,singleton_subset_iff,mem_row,
      mem_filter,mem_univ,true_and]
  have hc : (supports Inc p).card = count x y := congrArg Finset.card he
  rw [count_data,if_neg hxy] at hc
  by_cases hh : Positive x y
  · exact Or.inr (by simpa only [if_pos hh] using hc)
  · exact Or.inl (by simpa only [if_neg hh] using hc)

lemma pair_load_card (a : Fin 120) :
    ((univ : Finset (Pair (Fin 32))).filter (fun p => p.val ⊆ row Inc a)).card =
      (row Inc a).card.choose 2 := by
  classical
  rw [← card_powersetCard]
  apply card_bij (fun p _ => p.val)
  · intro p hp
    exact mem_powersetCard.mpr ⟨(mem_filter.mp hp).2,pair_card p⟩
  · intro p _ q _ h
    exact Subtype.ext h
  · intro p hp
    refine ⟨⟨p,mem_powersetCard.mpr ⟨subset_univ _,(mem_powersetCard.mp hp).2⟩⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_univ _,(mem_powersetCard.mp hp).1⟩

lemma total_supports : (∑ p : Pair (Fin 32), (supports Inc p).card) = 720 := by
  classical
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset (Fin 120))) (t := (univ : Finset (Pair (Fin 32))))
    (fun a p => p.val ⊆ row Inc a)
  have hs : (∑ a : Fin 120, ((univ : Finset (Pair (Fin 32))).filter
      (fun p => p.val ⊆ row Inc a)).card) = ∑ p : Pair (Fin 32), (supports Inc p).card := by
    simp only [bipartiteAbove,bipartiteBelow] at h
    convert h using 1
    apply sum_congr rfl
    intro x _
    congr 1
    ext y
    simp only [mem_supports,mem_filter,mem_univ,true_and]
  rw [← hs]
  simp only [pair_load_card,row_card,show (4 : ℕ).choose 2 = 6 from by decide,
    sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul]

theorem heavy_card : Nat.card (HeavyPair Inc) = 240 := by
  classical
  have hi (p : Pair (Fin 32)) : (supports Inc p).card =
      if 3 ≤ (supports Inc p).card then 3 else 0 := by
    rcases supports_zero_or_three p with h|h <;> simp [h]
  have hc : Nat.card (HeavyPair Inc) =
      ((univ : Finset (Pair (Fin 32))).filter (fun p => 3 ≤ (supports Inc p).card)).card := by
    simp only [HeavyPair,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hs : (∑ p : Pair (Fin 32), (supports Inc p).card) =
      ∑ p : Pair (Fin 32), if 3 ≤ (supports Inc p).card then 3 else 0 :=
    sum_congr rfl (fun p _ => hi p)
  rw [total_supports] at hs
  rw [← sum_filter] at hs
  simp only [sum_const,Nat.nsmul_eq_mul,← hc] at hs
  omega

theorem zero_or_heavy (x y : Fin 32) : codegree Inc x y = 0 ∨ 3 ≤ codegree Inc x y := by
  rw [codegree_eq,count_data]
  split_ifs <;> norm_num

theorem orderedZero_card :
    Nat.card {p : Fin 32 × Fin 32 // codegree Inc p.1 p.2 = 0} = 512 := by
  classical
  have hc : Nat.card {p : Fin 32 × Fin 32 // codegree Inc p.1 p.2 = 0} =
      ((univ : Finset (Fin 32 × Fin 32)).filter (fun p => count p.1 p.2 = 0)).card := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,codegree_eq]
  rw [hc]
  have he : ((univ : Finset (Fin 32 × Fin 32)).filter (fun p => count p.1 p.2 = 0)) =
      univ.filter (fun p => p.1 ≠ p.2 ∧ ¬ Positive p.1 p.2) := by
    ext p
    simp only [mem_filter,mem_univ,true_and,count_data]
    by_cases hxy : p.1=p.2 <;> by_cases hp : Positive p.1 p.2 <;> simp [hxy,hp]
  rw [he]
  convert orderedZero_data using 1

/-- In particular there is a minimal Hall core in this 32-column relation. -/
theorem exists_hall_core : ∃ S : Finset (HeavyPair Inc), Erdos713ThetaMinimalHallCore.Core Inc S := by
  classical
  have hn := card_le_univ (Erdos713ThetaMinimalHallCore.neighbors Inc univ)
  have hh : (univ : Finset (HeavyPair Inc)).card = 240 := by
    rw [card_univ,← Nat.card_eq_fintype_card,heavy_card]
  have hdef : (Erdos713ThetaMinimalHallCore.neighbors Inc univ).card <
      (univ : Finset (HeavyPair Inc)).card := by
    simp only [Fintype.card_fin] at hn
    omega
  obtain ⟨S,_,hS⟩ := Erdos713ThetaMinimalHallCore.exists_core univ hdef
  exact ⟨S,hS⟩

/-- The unrestricted heavy-pair Hall conclusion fails even with rigidity,
all rows of degree four, and every codegree zero or at least three. -/
theorem counterexample :
    ¬ HasTheta Inc ∧
    (∀ a b, a ≠ b → (row Inc a ∩ row Inc b).card ≤ 2) ∧
    (∀ a, (row Inc a).card = 4) ∧
    (∀ x y, codegree Inc x y = 0 ∨ 3 ≤ codegree Inc x y) ∧
    Nat.card (HeavyPair Inc) = 240 ∧ Nat.card (Fin 120) = 120 ∧
    Nat.card (Fin 120) < Nat.card (HeavyPair Inc) := by
  refine ⟨no_theta,rigid,row_card,zero_or_heavy,heavy_card,by simp,?_⟩
  rw [heavy_card]
  norm_num

theorem no_unrestricted_hall_bound :
    ¬ ∀ m k : ℕ, ∀ R : Fin m → Fin k → Prop,
      ¬ HasTheta R →
      (∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) →
      (∀ x y, codegree R x y = 0 ∨ 3 ≤ codegree R x y) →
      Nat.card (HeavyPair R) ≤ m := by
  intro h
  have hh := h 120 32 Inc no_theta rigid zero_or_heavy
  rw [heavy_card] at hh
  omega

#print axioms row_card
#print axioms rigid
#print axioms no_theta
#print axioms heavy_card
#print axioms zero_or_heavy
#print axioms orderedZero_card
#print axioms exists_hall_core
#print axioms counterexample
#print axioms no_unrestricted_hall_bound

end Erdos713ThetaQuadraticPlanes
