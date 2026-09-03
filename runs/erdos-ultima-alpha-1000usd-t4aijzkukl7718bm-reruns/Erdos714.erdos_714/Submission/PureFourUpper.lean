import Submission.PureFourStructure

/-!
A subcritical upper bound for the special zero-or-three four-point coverage
model. The original K44-free problem permits coverages one and two, and is
not settled by this stronger-hypothesis theorem.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 6000000
namespace Erdos714PureFourUpper
open Erdos714Packing Erdos714PureCommonMoments Erdos714PureFourStructure
variable {B V : Type*} [Fintype B] [Fintype V]

lemma degree_sum (S : B → Finset V) :
    (∑ b, (S b).card) = ∑ v, (dual S v).card := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun b v => v ∈ S b) (s := (univ : Finset B)) (t := (univ : Finset V))
  simpa only [bipartiteAbove, bipartiteBelow, filter_mem_eq_inter, univ_inter] using h

/-- A family with at most three points in each intersection of distinct
blocks has a quadratic edge bound at the 3/2 exponent. -/
theorem pair_intersection_square (S : B → Finset V) (N : ℕ)
    (hB : Fintype.card B ≤ N) (hV : Fintype.card V ≤ N)
    (hpair : ∀ b c, b ≠ c → (S b ∩ S c).card ≤ 3) :
    (∑ b, (S b).card)^2 ≤ 4*N^3 := by
  have hcommon (g : Fin 2 ↪ B) : (common S g).card ≤ 3 := by
    have he : common S g = S (g 0) ∩ S (g 1) := by
      ext v
      simp only [mem_common, mem_inter]
      constructor
      · intro h; exact ⟨h 0,h 1⟩
      · intro h i; fin_cases i; exact h.1; exact h.2
    rw [he]
    exact hpair _ _ (g.injective.ne (by decide))
  have he : (∑ b, (S b).card) ≤ N^2 := by
    calc
      _ ≤ ∑ _b : B, Fintype.card V := sum_le_sum (fun b _ => card_le_univ _)
      _ = Fintype.card B*Fintype.card V := by simp
      _ ≤ N*N := Nat.mul_le_mul hB hV
      _ = N^2 := by ring
  have hs : (∑ v, (dual S v).card.descFactorial 2) ≤ 3*N^2 := by
    rw [star_count S 2]
    calc
      _ ≤ ∑ _g : Fin 2 ↪ B, 3 := sum_le_sum (fun g _ => hcommon g)
      _ = 3*(Fintype.card B).descFactorial 2 := by simp [Nat.mul_comm]
      _ ≤ 3*(Fintype.card B)^2 := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 2)
  have hid (t : ℕ) : t^2 = t+t.descFactorial 2 := by
    by_cases ht : t=0
    · simp [ht]
    · have hh : t-1+1=t := by omega
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one]
      nlinarith
  have hsecond : (∑ v, (dual S v).card^2) ≤ 4*N^2 := by
    calc
      _ = ∑ v, ((dual S v).card+(dual S v).card.descFactorial 2) :=
        sum_congr rfl (fun v _ => hid _)
      _ = (∑ b, (S b).card)+(∑ v, (dual S v).card.descFactorial 2) := by
        rw [sum_add_distrib, ← degree_sum S]
      _ ≤ _ := by omega
  have hh := pow_sum_le_card_mul_sum_pow
    (s := (univ : Finset V)) (f := fun v => (dual S v).card) (by intros; omega) 1
  norm_num only [pow_one, card_univ, Nat.cast_id] at hh
  rw [← degree_sum S] at hh
  calc
    _ ≤ Fintype.card V*(∑ v, (dual S v).card^2) := hh
    _ ≤ N*(4*N^2) := Nat.mul_le_mul hV hsecond
    _ = _ := by ring

/-- Pure zero-or-three systems have only O(N^(3/2)) incidences. All
constants and finite-size conditions are explicit. -/
theorem pure_four_square_bound (S : B → Finset V) (N : ℕ) (hN : 1 ≤ N)
    (hB : Fintype.card B ≤ N) (hV : Fintype.card V ≤ N)
    (hpure : ∀ T : Finset V, T.card=4 →
      (blocksContaining S T).card=0 ∨ (blocksContaining S T).card=3) :
    (∑ b, (S b).card)^2 ≤ 104*N^3 := by
  let X : Finset B := univ.filter (fun b => 4 ≤ (S b).card ∧
    4*Fintype.card B < ((S b).card-2)^2)
  let L : Finset (Finset V) := X.image S
  have hX : X.card ≤ N := (card_le_univ X).trans hB
  have hsmall (b : B) (hb : b ∈ univ \ X) : (S b).card^2 ≤ 16*N := by
    have hn := (mem_sdiff.mp hb).2
    have hn' : ¬ (4 ≤ (S b).card ∧ 4*Fintype.card B < ((S b).card-2)^2) := by
      intro h
      exact hn (mem_filter.mpr ⟨mem_univ _,h⟩)
    by_cases hd : 4 ≤ (S b).card
    · have hbnd : ((S b).card-2)^2 ≤ 4*Fintype.card B := by omega
      have hs : (S b).card-2+2=(S b).card := by omega
      have hs4 : (S b).card-4+4=(S b).card := by omega
      nlinarith [Nat.zero_le (((S b).card-4)^2)]
    · have hs : (S b).card ≤ 3 := by omega
      have hp := Nat.pow_le_pow_left hs 2
      nlinarith
  have hesmall : (∑ b ∈ univ \ X, (S b).card)^2 ≤ 16*N^3 := by
    have hh := pow_sum_le_card_mul_sum_pow (s := univ \ X)
      (f := fun b => (S b).card) (by intros; omega) 1
    norm_num only [pow_one, Nat.cast_id] at hh
    have hcard : (univ \ X).card ≤ N := (card_le_univ _).trans hB
    have hs : (∑ b ∈ univ \ X, (S b).card^2) ≤ N*(16*N) := by
      calc
        _ ≤ ∑ _b ∈ univ \ X, 16*N := sum_le_sum (fun b hb => hsmall b hb)
        _ = (univ \ X).card*(16*N) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hcard
    calc
      _ ≤ (univ \ X).card*(∑ b ∈ univ \ X, (S b).card^2) := hh
      _ ≤ N*(N*(16*N)) := Nat.mul_le_mul hcard hs
      _ = _ := by ring
  have hL : Fintype.card L ≤ N := by
    simpa only [Fintype.card_coe] using (card_image_le (s := X) (f := S)).trans hX
  have hLpair (T U : L) (hTU : T ≠ U) : (T.val ∩ U.val).card ≤ 3 := by
    obtain ⟨b,hb,hbT⟩ := mem_image.mp T.property
    obtain ⟨c,hc,hcU⟩ := mem_image.mp U.property
    have hbb := (mem_filter.mp hb).2
    have hn : ¬ S b ⊆ S c := by
      intro hbc
      have he := large_block_twins S hpure b hbb.1 hbb.2 c hbc
      apply hTU
      apply Subtype.ext
      exact hbT.symm.trans (he.symm.trans hcU)
    have hh := (large_block_isolated S hpure b hbb.1 hbb.2).2 c hn
    simpa only [hbT,hcU] using hh
  have heL : (∑ T ∈ L, T.card)^2 ≤ 4*N^3 := by
    have hh := pair_intersection_square (fun T : L => T.val) N hL hV hLpair
    simpa only [sum_coe_sort] using hh
  have hlarge : (∑ b ∈ X, (S b).card) ≤ 3*(∑ T ∈ L, T.card) := by
    have hfiber (T : Finset V) (hT : T ∈ L) :
        (∑ b ∈ X with S b=T, (S b).card) ≤ 3*T.card := by
      obtain ⟨b,hb,hbT⟩ := mem_image.mp hT
      have hbb := (mem_filter.mp hb).2
      have hthree := (large_block_isolated S hpure b hbb.1 hbb.2).1
      have hsub : X.filter (fun c => S c=T) ⊆ blocksContaining S (S b) := by
        intro c hc
        apply (mem_blocksContaining S (S b) c).mpr
        have he := (mem_filter.mp hc).2
        rw [hbT,he]
      have hc : (X.filter (fun c => S c=T)).card ≤ 3 := by
        have hh := card_le_card hsub
        omega
      calc
        _ = ∑ _c ∈ X with S _c=T, T.card := by
          apply sum_congr rfl
          intro c hc
          rw [(mem_filter.mp hc).2]
        _ = (X.filter (fun c => S c=T)).card*T.card := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hc
    have hsplit := sum_fiberwise_of_maps_to (s := X) (t := L) (g := S)
      (fun b hb => mem_image.mpr ⟨b,hb,rfl⟩) (fun b => (S b).card)
    rw [← hsplit, mul_sum]
    exact sum_le_sum (fun T hT => hfiber T hT)
  have helarge : (∑ b ∈ X, (S b).card)^2 ≤ 36*N^3 := by
    calc
      _ ≤ (3*(∑ T ∈ L, T.card))^2 := Nat.pow_le_pow_left hlarge 2
      _ = 9*(∑ T ∈ L, T.card)^2 := by ring
      _ ≤ 9*(4*N^3) := Nat.mul_le_mul_left _ heL
      _ = _ := by ring
  have hsplit : (∑ b ∈ univ \ X, (S b).card) + (∑ b ∈ X, (S b).card) =
      ∑ b, (S b).card := sum_sdiff (subset_univ X)
  have hh := add_pow_le (Nat.zero_le (∑ b ∈ univ \ X, (S b).card))
    (Nat.zero_le (∑ b ∈ X, (S b).card)) 2
  rw [hsplit] at hh
  norm_num only at hh
  nlinarith

/-- The same bound stated for common neighbors of ordered row quadruples. -/
theorem common_zero_three_square (S : B → Finset V) (N : ℕ) (hN : 1 ≤ N)
    (hB : Fintype.card B ≤ N) (hV : Fintype.card V ≤ N)
    (hpure : ∀ f : Fin 4 ↪ B, (common S f).card=0 ∨ (common S f).card=3) :
    (∑ b, (S b).card)^2 ≤ 104*N^3 := by
  rw [degree_sum S]
  apply pure_four_square_bound (dual S) N hN hV hB
  intro T hT
  obtain ⟨f : Fin 4 ↪ B,hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (α := Fin 4) (s := T)
      (by simpa using hT.symm)
  have he : blocksContaining (dual S) T = common S f := by
    ext v
    rw [← hf]
    simp only [mem_blocksContaining, mem_common, mem_dual, subset_iff]
    constructor
    · intro h i
      exact h (mem_map.mpr ⟨i,mem_univ _,rfl⟩)
    · intro h b hb
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hb
      exact h i
  rw [he]
  exact hpure f

/-- A pure zero-or-three family cannot have unbounded fourth-case critical
parameters, without ANY degree or pair-codegree regularity hypothesis. -/
theorem critical_pure_budget (S : B → Finset V) (q C : ℕ) (hq : 0 < q)
    (hB : Fintype.card B ≤ q^4) (hV : Fintype.card V ≤ q^4)
    (he : q^7 ≤ C*(∑ b, (S b).card))
    (hpure : ∀ f : Fin 4 ↪ B, (common S f).card=0 ∨ (common S f).card=3) :
    q^2 ≤ 104*C^2 := by
  have hb := common_zero_three_square S (q^4) (one_le_pow₀ hq) hB hV hpure
  have hh : q^12*q^2 ≤ q^12*(104*C^2) := by
    calc
      _ = (q^7)^2 := by ring
      _ ≤ (C*(∑ b, (S b).card))^2 := Nat.pow_le_pow_left he 2
      _ = C^2*(∑ b, (S b).card)^2 := by ring
      _ ≤ C^2*(104*(q^4)^3) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

/-- Even without pair-codegree regularity, a critical K44-free system with
q>11C must have a quadruple with one or two common neighbors. This is an
existence result, not a positive-density count or a stability theorem. -/
theorem critical_exists_intermediate (S : B → Finset V) (q C : ℕ)
    (hq : 11*C < q) (hB : Fintype.card B ≤ q^4) (hV : Fintype.card V ≤ q^4)
    (he : q^7 ≤ C*(∑ b, (S b).card))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    ∃ f : Fin 4 ↪ B, (common S f).card=1 ∨ (common S f).card=2 := by
  by_contra! hn
  have hpure (f : Fin 4 ↪ B) : (common S f).card=0 ∨ (common S f).card=3 := by
    have hb := (free_iff_common_card S (by decide : 0 < 4)).mp hfree f
    have h := hn f
    omega
  have h := critical_pure_budget S q C (by omega) hB hV he hpure
  have hpow := Nat.mul_self_lt_mul_self hq
  nlinarith

variable {F : Type*} [Field F] [Fintype F]

/-- The sparse noncube sextic cannot be an exact all-root common-neighbor
model at unbounded critical scale. This removes the regularity assumptions
from the earlier conditional model obstruction. -/
theorem sparse_sextic_critical_budget (S : B → Finset V) (q C : ℕ) (hq : 0 < q)
    (hB : Fintype.card B ≤ q^4) (hV : Fintype.card V ≤ q^4)
    (he : q^7 ≤ C*(∑ b, (S b).card))
    (a b : (Fin 4 ↪ B) → F) (ζ : F) (hζ : IsPrimitiveRoot ζ 3)
    (hb : ∀ f, ¬ ∃ z : F, z^3=b f)
    (hmodel : ∀ f, (common S f).card =
      (Erdos714PowerQuadraticRoots.solutions 3 (a f) (b f)).card) :
    q^2 ≤ 104*C^2 := by
  apply critical_pure_budget S q C hq hB hV he
  intro f
  rw [hmodel f]
  exact Erdos714PowerQuadraticRoots.solution_card_zero_or_k
    3 (by decide) (a f) (b f) ζ (hb f) hζ

/-- Direct version for simple graphs. Here N bounds the number of vertices,
and e denotes the number of undirected edges. -/
theorem graph_pure_square (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ) (hN : 1 ≤ N) (hV : Fintype.card V ≤ N)
    (hpure : ∀ f : Fin 4 ↪ V,
      (common (fun v => G.neighborFinset v) f).card=0 ∨
      (common (fun v => G.neighborFinset v) f).card=3) :
    G.edgeFinset.card^2 ≤ 26*N^3 := by
  have h := common_zero_three_square (fun v => G.neighborFinset v) N hN hV hV hpure
  have hd : (∑ v, (G.neighborFinset v).card)=2*G.edgeFinset.card := by
    simpa only [card_neighborFinset_eq_degree] using G.sum_degrees_eq_twice_card_edges
  rw [hd] at h
  nlinarith

#print axioms common_zero_three_square
#print axioms critical_pure_budget
#print axioms critical_exists_intermediate
#print axioms sparse_sextic_critical_budget
#print axioms graph_pure_square
#print axioms pair_intersection_square
#print axioms pure_four_square_bound
end Erdos714PureFourUpper
