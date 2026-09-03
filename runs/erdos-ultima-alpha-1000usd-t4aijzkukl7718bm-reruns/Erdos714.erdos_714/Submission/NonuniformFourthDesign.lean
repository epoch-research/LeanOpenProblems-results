import Submission.PureCommonMoments

/-!
Local nonuniform design bounds. Unlike the earlier exact-fourth-design
lemma, block sizes may vary. The exact coverage hypotheses remain essential.
-/
noncomputable section
open Classical Finset Matrix SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714NonuniformFourthDesign
open Erdos714Packing Erdos714PureCommonMoments
variable {B V : Type*} [Fintype B] [Fintype V]

/-- Fisher's inequality for a pairwise balanced family of proper blocks.
No uniformity of block sizes or point degrees is required. -/
theorem pair_fisher (S : B → Finset V) (l : ℕ) (hl : 0 < l)
    (hV : 2 ≤ Fintype.card V)
    (hproper : ∀ b, S b ≠ univ)
    (hpair : ∀ v w : V, v ≠ w →
      (univ.filter (fun b => v ∈ S b ∧ w ∈ S b)).card = l) :
    Fintype.card V ≤ Fintype.card B := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let d (v : V) := (univ.filter (fun b => v ∈ S b)).card
  have hdeg (v : V) : l < d v := by
    obtain ⟨w, hw⟩ := exists_ne v
    have hc := hpair v w hw.symm
    have hex : (univ.filter (fun b => v ∈ S b ∧ w ∈ S b)).Nonempty := by
      apply card_pos.mp
      omega
    obtain ⟨b, hb⟩ := hex
    have hv : v ∈ S b := (mem_filter.mp hb).2.1
    obtain ⟨z, hz⟩ : ∃ z, z ∉ S b := by
      by_contra! h
      apply hproper b
      ext z
      simp [h z]
    have hvz : v ≠ z := by rintro rfl; exact hz hv
    have hsub : univ.filter (fun b => v ∈ S b ∧ z ∈ S b) ⊂
        univ.filter (fun b => v ∈ S b) := by
      apply ssubset_iff_subset_ne.mpr
      constructor
      · intro c hc
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hc).2.1⟩
      · intro he
        have hb' : b ∈ univ.filter (fun b => v ∈ S b) := mem_filter.mpr ⟨mem_univ _, hv⟩
        rw [← he] at hb'
        exact hz (mem_filter.mp hb').2.2
    have hh := card_lt_card hsub
    rw [hpair v z hvz] at hh
    exact hh
  let M : Matrix B V ℝ := fun b v => if v ∈ S b then 1 else 0
  let O : Matrix Unit V ℝ := fun _ _ => 1
  have hgram (v w : V) : (Mᵀ*M) v w =
      ((univ.filter (fun b => v ∈ S b ∧ w ∈ S b)).card : ℝ) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, M]
    have hterm (b : B) : (if v ∈ S b then (1 : ℝ) else 0)*
        (if w ∈ S b then 1 else 0) = if v ∈ S b ∧ w ∈ S b then 1 else 0 := by
      split_ifs <;> simp_all
    simp_rw [hterm]
    simp only [sum_boole]
  have heq : Mᵀ*M = diagonal (fun v => (d v : ℝ)-l) + (l : ℝ) • (Oᵀ*O) := by
    ext v w
    rw [hgram]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have ho : (Oᵀ*O) v w=1 := by simp [Matrix.mul_apply, O]
    rw [ho, mul_one]
    by_cases hvw : v=w
    · subst w
      simp only [diagonal_apply_eq, and_self]
      dsimp [d]
      ring
    · rw [diagonal_apply_ne _ hvw, hpair v w hvw]
      simp
  have hdiag : (diagonal (fun v => (d v : ℝ)-l)).PosDef :=
    Matrix.PosDef.diagonal (fun v => sub_pos.mpr (by exact_mod_cast hdeg v))
  have hones : (Oᵀ*O).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self O
  have hpos : (Mᵀ*M).PosDef := by
    rw [heq]
    exact hdiag.add_posSemidef (hones.smul (by positivity))
  have hrank := Matrix.rank_of_isUnit (Mᵀ*M) hpos.isUnit
  rw [Matrix.rank_transpose_mul_self] at hrank
  rw [← hrank]
  exact Matrix.rank_le_card_height M

/-- Fix two points of a nonuniform exact fourth-order design. The blocks
containing them induce a pairwise balanced design on the remaining points. -/
theorem pair_coverage_lower (S : B → Finset V) (l : ℕ) (hl : 0 < l)
    (hV : 4 ≤ Fintype.card V) (hproper : ∀ b, S b ≠ univ)
    (hfour : ∀ T : Finset V, T.card=4 → (blocksContaining S T).card=l)
    (p : Finset V) (hp : p.card=2) :
    Fintype.card V-2 ≤ (blocksContaining S p).card := by
  let I := {b : B // p ⊆ S b}
  let W := {v : V // v ∉ p}
  let R : I → Finset W := fun b => univ.filter (fun v => v.val ∈ S b.val)
  have hW : Fintype.card W = Fintype.card V-2 := by
    dsimp [W]
    rw [Fintype.card_subtype_compl]
    simp [hp]
  have hI : Fintype.card I = (blocksContaining S p).card := by
    simp [I, blocksContaining, Fintype.card_subtype]
  have hproperR (b : I) : R b ≠ univ := by
    intro he
    apply hproper b.val
    apply eq_univ_of_forall
    intro v
    by_cases hv : v ∈ p
    · exact b.property hv
    · have hmem : (⟨v,hv⟩ : W) ∈ R b := by rw [he]; exact mem_univ _
      exact (mem_filter.mp hmem).2
  have hpairs (v w : W) (hvw : v ≠ w) :
      (univ.filter (fun b : I => v ∈ R b ∧ w ∈ R b)).card=l := by
    let T := p ∪ {v.val,w.val}
    have hvw' : v.val ≠ w.val := fun h => hvw (Subtype.ext h)
    have hT : T.card=4 := by
      have hdis : Disjoint p {v.val,w.val} := by
        apply Finset.disjoint_left.mpr
        intro x hx hxp
        rcases (by simpa only [mem_insert, mem_singleton] using hxp : x=v.val ∨ x=w.val) with rfl | rfl
        · exact v.property hx
        · exact w.property hx
      dsimp [T]
      rw [card_union_of_disjoint hdis, hp, card_pair hvw']
    rw [← hfour T hT]
    apply card_bij (fun b _ => b.val)
    · intro b hb
      apply (mem_blocksContaining S T b.val).mpr
      apply union_subset b.property
      simpa only [insert_subset_iff, singleton_subset_iff] using
        And.intro (mem_filter.mp (mem_filter.mp hb).2.1).2
          (mem_filter.mp (mem_filter.mp hb).2.2).2
    · intro b hb c hc he
      exact Subtype.ext he
    · intro b hb
      have hsub := (mem_blocksContaining S T b).mp hb
      have hpb : p ⊆ S b := subset_trans subset_union_left hsub
      refine ⟨⟨b,hpb⟩, ?_, rfl⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      constructor
      · exact mem_filter.mpr ⟨mem_univ _, hsub (by simp [T])⟩
      · exact mem_filter.mpr ⟨mem_univ _, hsub (by simp [T])⟩
  have hh := pair_fisher R l hl (by omega) hproperR (by
    intro v w hvw
    convert hpairs v w hvw using 2
    ext b
    simp)
  rwa [hW,hI] at hh

/-- A first/second-moment union bound for an indexed family of subsets. -/
lemma small_pair_union_bound {I : Type*} [Fintype I] (U : I → Finset B) (l : ℕ)
    (hpair : ∀ g : Fin 2 ↪ I, (common U g).card ≤ l) :
    2*(∑ i, (U i).card) ≤ 2*Fintype.card B + l*(Fintype.card I).descFactorial 2 := by
  have hcnt := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun i b => b ∈ U i) (s := (univ : Finset I)) (t := (univ : Finset B))
  simp only [bipartiteAbove, bipartiteBelow, filter_mem_eq_inter, univ_inter] at hcnt
  change (∑ i, (U i).card) = ∑ b, (dual U b).card at hcnt
  have hn (t : ℕ) : 2*t ≤ 2+t.descFactorial 2 := by
    by_cases ht : t ≤ 1
    · interval_cases t <;> norm_num
    · have hs : t-1+1=t := by omega
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero,
        Nat.sub_zero, mul_one]
      nlinarith
  have hs : (∑ b, (dual U b).card.descFactorial 2) ≤
      l*(Fintype.card I).descFactorial 2 := by
    rw [star_count U 2]
    calc
      _ ≤ ∑ _g : Fin 2 ↪ I, l := sum_le_sum (fun g _ => hpair g)
      _ = _ := by simp [Nat.mul_comm]
  calc
    _ = ∑ b, 2*(dual U b).card := by rw [hcnt, mul_sum]
    _ ≤ ∑ b, (2+(dual U b).card.descFactorial 2) := sum_le_sum (fun b _ => hn _)
    _ = 2*Fintype.card B + ∑ b, (dual U b).card.descFactorial 2 := by
      simp [sum_add_distrib, Nat.mul_comm]
    _ ≤ _ := Nat.add_le_add_left hs _

/-- Apply the pairwise union bound to disjoint point-pairs. -/
theorem matching_budget (S : B → Finset V) (l m : ℕ) (hl : 0 < l) (hl2 : l ≤ 2)
    (hV : 4 ≤ Fintype.card V) (hproper : ∀ b, S b ≠ univ)
    (hfour : ∀ T : Finset V, T.card=4 → (blocksContaining S T).card=l)
    (p : Fin m → Finset V) (hp : ∀ i, (p i).card=2)
    (hdis : ∀ i j, i ≠ j → Disjoint (p i) (p j)) :
    m*(Fintype.card V-2) ≤ Fintype.card B + m*(m-1) := by
  let U := fun i => blocksContaining S (p i)
  have hlo : m*(Fintype.card V-2) ≤ ∑ i, (U i).card := by
    calc
      _ = ∑ _i : Fin m, (Fintype.card V-2) := by simp
      _ ≤ _ := sum_le_sum (fun i _ => pair_coverage_lower S l hl hV hproper hfour (p i) (hp i))
  have hpair (g : Fin 2 ↪ Fin m) : (common U g).card ≤ 2 := by
    have hne : g 0 ≠ g 1 := g.injective.ne (by decide)
    have hc : (p (g 0) ∪ p (g 1)).card=4 := by
      rw [card_union_of_disjoint (hdis _ _ hne), hp, hp]
    have he : common U g = blocksContaining S (p (g 0) ∪ p (g 1)) := by
      ext b
      simp only [mem_common, U, mem_blocksContaining, union_subset_iff]
      constructor
      · intro h
        exact ⟨h 0,h 1⟩
      · intro h i
        fin_cases i
        · exact h.1
        · exact h.2
    rw [he, hfour _ hc]
    exact hl2
  have hhi := small_pair_union_bound U 2 hpair
  simp only [Fintype.card_fin, Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.sub_zero, mul_one] at hhi
  nlinarith

/-- A coarse quadratic bound for a fourth-order design with index 1 or 2.
The blocks need only be proper; their sizes and lower-order coverages may vary. -/
theorem fourth_design_bound (S : B → Finset V) (l : ℕ) (hl : 0 < l) (hl2 : l ≤ 2)
    (hV : 4 ≤ Fintype.card V) (hproper : ∀ b, S b ≠ univ)
    (hfour : ∀ T : Finset V, T.card=4 → (blocksContaining S T).card=l) :
    (Fintype.card V-2)^2 ≤ 4*Fintype.card B := by
  let m := Fintype.card V/2
  have hm : 2*m ≤ Fintype.card V := Nat.mul_div_le _ _
  have hcard : Fintype.card (Fin m × Bool) ≤ Fintype.card V := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using hm
  let f : (Fin m × Bool) ↪ V := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  let p : Fin m → Finset V := fun i => {f (i,false), f (i,true)}
  have hp (i : Fin m) : (p i).card=2 := by
    apply card_pair
    intro he
    have hh := f.injective he
    cases hh
  have hdis (i j : Fin m) (hij : i ≠ j) : Disjoint (p i) (p j) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    simp only [p, mem_insert, mem_singleton] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with h | h
    all_goals exact hij (congrArg Prod.fst (f.injective h))
  have hb := matching_budget S l m hl hl2 hV hproper hfour p hp hdis
  have hr : Fintype.card V=2*m ∨ Fintype.card V=2*m+1 := by
    have hmod := Nat.mod_lt (Fintype.card V) (by decide : 0 < 2)
    have he := Nat.mod_add_div (Fintype.card V) 2
    dsimp [m] at *
    omega
  have hsub : Fintype.card V-2+2=Fintype.card V := by omega
  have hm1 : m-1+1=m := by omega
  rcases hr with hr | hr <;> nlinarith

#print axioms small_pair_union_bound
#print axioms matching_budget
#print axioms fourth_design_bound
#print axioms pair_fisher
#print axioms pair_coverage_lower
end Erdos714NonuniformFourthDesign
