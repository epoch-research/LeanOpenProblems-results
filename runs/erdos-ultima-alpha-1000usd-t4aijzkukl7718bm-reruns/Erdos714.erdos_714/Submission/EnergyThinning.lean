import Submission.SelectedAdditiveCoding

/-!
Additive-energy bounds for K44-free subgraphs of additive-code hosts.
This is an obstruction to a construction family, not a resolution of Erdős 714.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
open Finset SimpleGraph
open scoped Pointwise
open Classical

namespace Erdos714EnergyThinning

variable {V Y I A : Type*} [AddCommGroup V] [Fintype V] [Fintype Y]

/-- Ordered parallelograms, including degenerate ones. -/
def parallelograms (S : Finset V) : Finset (V × (V × V)) :=
  univ.filter (fun p => p.1 ∈ S ∧ p.1+p.2.1 ∈ S ∧ p.1+p.2.2 ∈ S ∧ p.1+p.2.1+p.2.2 ∈ S)

lemma energy_eq_parallelograms (S : Finset V) : S.addEnergy S = (parallelograms S).card := by
  unfold Finset.addEnergy
  apply card_bij
    (fun p _ => (p.1.1, (p.1.2-p.1.1, p.2.2-p.1.1)))
  · rintro ⟨⟨a,b⟩,c,d⟩ hp
    simp only [mem_filter, mem_product] at hp
    obtain ⟨⟨⟨ha,hb⟩,hc,hd⟩,he⟩ := hp
    apply mem_filter.mpr
    refine ⟨mem_univ _, ha, ?_, ?_, ?_⟩
    · simpa using hb
    · simpa using hd
    · have hh : a+(b-a)+(d-a) = c := by
        calc
          _ = b+d-a := by abel
          _ = c := by rw [← he]; abel
      simpa only [hh] using hc
  · rintro ⟨⟨a,b⟩,c,d⟩ hp ⟨⟨a',b'⟩,c',d'⟩ hq hh
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    have ha : a = a' := congrArg Prod.fst hh
    subst a'
    have hb : b = b' := sub_left_injective (congrArg (fun z : V × (V × V) => z.2.1) hh)
    have hd : d = d' := sub_left_injective (congrArg (fun z : V × (V × V) => z.2.2) hh)
    subst b'
    subst d'
    have hc : c = c' := add_left_cancel (hp'.trans hq'.symm)
    subst c'
    rfl
  · rintro ⟨x,u,v⟩ hp
    obtain ⟨hx,hxu,hxv,hxuv⟩ := (mem_filter.mp hp).2
    refine ⟨((x,x+u),x+u+v,x+v), ?_, ?_⟩
    · simp only [mem_filter, mem_product]
      exact ⟨⟨⟨hx,hxu⟩,hxuv,hxv⟩, by abel⟩
    · simp

/-- The number of right vertices adjacent to all four corners. -/
def commonParallelogram (N : Y → Finset V) (x u v : V) : Finset Y :=
  univ.filter (fun y => x ∈ N y ∧ x+u ∈ N y ∧ x+v ∈ N y ∧ x+u+v ∈ N y)

lemma commonParallelogram_le_three (N : Y → Finset V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Packing.incidence N))
    (x u v : V) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (hs : u+v ≠ 0) :
    (commonParallelogram N x u v).card ≤ 3 := by
  let e : Fin 4 ↪ V := ⟨![0,u,v,u+v], by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact False.elim (hu h)
      | exact False.elim (hu h.symm)
      | exact False.elim (hv h)
      | exact False.elim (hv h.symm)
      | exact False.elim (huv h)
      | exact False.elim (huv h.symm)
      | exact False.elim (hs h)
      | exact False.elim (hs h.symm)
      | exact False.elim (hu (by simpa using h))
      | exact False.elim (hu (by simpa using h.symm))
      | exact False.elim (hv (by simpa using h))⟩
  let g : Fin 4 ↪ V := e.trans (Equiv.addLeft x).toEmbedding
  have hg := (Erdos714Packing.common_card_dual_iff N (by decide : 0 < 4)).mp
    ((Erdos714Packing.free_iff_common_card N (by decide)).mp hfree) g
  have he : commonParallelogram N x u v =
      Erdos714Packing.common (Erdos714Packing.dual N) g := by
    ext y
    simp only [commonParallelogram, mem_filter, mem_univ, true_and,
      Erdos714Packing.mem_common, Erdos714Packing.mem_dual]
    constructor
    · intro hy i
      fin_cases i
      · simpa [g, e] using hy.1
      · simpa [g, e] using hy.2.1
      · simpa [g, e] using hy.2.2.1
      · simpa [g, e, add_assoc] using hy.2.2.2
    · intro hy
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [g,e] using hy 0
      · simpa [g,e] using hy 1
      · simpa [g,e] using hy 2
      · simpa [g,e,add_assoc] using hy 3
  rw [he]
  omega

/-- Freeness bounds the total additive energy of arbitrary column neighborhoods. -/
theorem neighborhood_energy_bound (N : Y → Finset V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Packing.incidence N)) :
    ∑ y : Y, (N y).addEnergy (N y) ≤
      3*(Fintype.card V)^3 + 4*Fintype.card V*(∑ y : Y, (N y).card) := by
  let d (x : V) := (univ.filter (fun y => x ∈ N y)).card
  have hc (x u v : V) : (commonParallelogram N x u v).card ≤
      3 + if (u,v) ∈ Erdos714AdditiveCoding.degeneratePairs then d x else 0 := by
    by_cases hb : (u,v) ∈ Erdos714AdditiveCoding.degeneratePairs
    · have hd : (commonParallelogram N x u v).card ≤ d x := by
        apply card_le_card
        intro y hy
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.1⟩
      simp only [if_pos hb]
      omega
    · have hgood : u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ u+v ≠ 0 := by
        simpa only [Erdos714AdditiveCoding.degeneratePairs, mem_filter,
          mem_univ, true_and, not_or] using hb
      simpa only [if_neg hb, add_zero] using commonParallelogram_le_three N hfree x u v
        hgood.1 hgood.2.1 hgood.2.2.1 hgood.2.2.2
  have he : (∑ y : Y, (N y).addEnergy (N y)) =
      ∑ x : V, ∑ p : V × V, (commonParallelogram N x p.1 p.2).card := by
    simp only [energy_eq_parallelograms, parallelograms, card_filter]
    rw [sum_comm]
    simp only [Fintype.sum_prod_type, commonParallelogram, card_filter]
  have hd : ∑ x : V, d x = ∑ y : Y, (N y).card := by
    simp only [d, card_filter]
    rw [sum_comm]
    simp
  have hb (x : V) : (∑ p : V × V, if p ∈ Erdos714AdditiveCoding.degeneratePairs then d x else 0) =
      (Erdos714AdditiveCoding.degeneratePairs : Finset (V × V)).card * d x := by
    rw [← sum_filter]
    simp
  rw [he]
  calc
    _ ≤ ∑ x : V, ∑ p : V × V,
        (3 + if p ∈ Erdos714AdditiveCoding.degeneratePairs then d x else 0) :=
      sum_le_sum (fun x _ => sum_le_sum (fun p _ => hc x p.1 p.2))
    _ = 3*(Fintype.card V)^3 +
        (Erdos714AdditiveCoding.degeneratePairs : Finset (V × V)).card * ∑ x : V, d x := by
      simp_rw [sum_add_distrib, hb]
      rw [← mul_sum]
      simp [Fintype.card_prod, pow_succ, mul_assoc, mul_comm]
    _ ≤ _ := by
      rw [hd]
      have hh := Nat.mul_le_mul_right (∑ y : Y, (N y).card)
        (Erdos714AdditiveCoding.degeneratePairs_card (V := V))
      nlinarith

/-- The fourth-moment inequality, obtained by applying Cauchy-Schwarz twice. -/
lemma fourth_moment {J : Type*} (s : Finset J) (w : J → ℕ) :
    (∑ j ∈ s, w j)^4 ≤ s.card^3 * ∑ j ∈ s, (w j)^4 := by
  have h₁ : (∑ j ∈ s, w j)^2 ≤ s.card * ∑ j ∈ s, (w j)^2 := by
    simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) s (fun _ => 1) w
  have h₂ : (∑ j ∈ s, (w j)^2)^2 ≤ s.card * ∑ j ∈ s, (w j)^4 := by
    have hh := sum_mul_sq_le_sq_mul_sq (R := ℕ) s (fun _ => 1) (fun j => (w j)^2)
    simp only [one_mul, one_pow, sum_const, smul_eq_mul, mul_one] at hh
    have he : (∑ j ∈ s, ((w j)^2)^2) = ∑ j ∈ s, (w j)^4 := by
      apply sum_congr rfl
      intro j _
      ring
    rw [he] at hh
    exact hh
  calc
    _ = ((∑ j ∈ s, w j)^2)^2 := by ring
    _ ≤ (s.card * ∑ j ∈ s, (w j)^2)^2 := Nat.pow_le_pow_left h₁ 2
    _ = s.card^2 * (∑ j ∈ s, (w j)^2)^2 := by ring
    _ ≤ s.card^2 * (s.card * ∑ j ∈ s, (w j)^4) := Nat.mul_le_mul_left _ h₂
    _ = _ := by ring

variable [AddCommGroup A] [Fintype A] [Fintype I]

omit [Fintype A] in
lemma fiber_card_eq_kernel (l : V →+ A) (v : V) :
    (univ.filter (fun x => l x = l v)).card = (univ.filter (fun x => l x = 0)).card := by
  apply card_equiv (Equiv.subRight v)
  intro x
  simp [map_sub, sub_eq_zero]

omit [Fintype A] in
lemma fiber_card_le_kernel (l : V →+ A) (a : A) :
    (univ.filter (fun x => l x = a)).card ≤ (univ.filter (fun x => l x = 0)).card := by
  by_cases ha : ∃ v, l v = a
  · obtain ⟨v,rfl⟩ := ha
    exact (fiber_card_eq_kernel l v).le
  · have he : univ.filter (fun x => l x = a) = ∅ := by
      simp only [filter_eq_empty_iff, mem_univ, true_implies]
      intro x hx
      exact ha ⟨x,hx⟩
    simp [he]

omit [Fintype A] in
/-- Any subset of a homomorphism fiber has large energy relative to the kernel. -/
lemma fiber_energy_bound (l : V →+ A) (S : Finset V) (a : A)
    (hS : ∀ v ∈ S, l v = a) :
    S.card^4 ≤ (univ.filter (fun v => l v = 0)).card * S.addEnergy S := by
  have hs : (S+S).card ≤ (univ.filter (fun v => l v = 0)).card := by
    apply (card_le_card (t := univ.filter (fun v => l v = a+a)) ?_).trans
      (fiber_card_le_kernel l (a+a))
    intro v hv
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hv
    simp [map_add, hS x hx, hS y hy]
  have h := (le_card_add_mul_addEnergy S S).trans
    (Nat.mul_le_mul_right (S.addEnergy S) hs)
  nlinarith

/-- Across one coordinate, the image/kernel identity improves the fourth-moment factor. -/
lemma coordinate_energy_bound (l : V →+ A) (N : A → Finset V)
    (hN : ∀ a v, v ∈ N a → l v = a) :
    (∑ a : A, (N a).card)^4 ≤
      (Fintype.card A)^2 * Fintype.card V * ∑ a : A, (N a).addEnergy (N a) := by
  let R : Finset A := univ.image l
  let k := (univ.filter (fun v => l v = 0)).card
  have hempty (a : A) (ha : a ∉ R) : N a = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact ha (mem_image.mpr ⟨v, mem_univ _, hN a v hv⟩)
  have hsum : (∑ a ∈ R, (N a).card) = ∑ a : A, (N a).card := by
    apply sum_subset (subset_univ _)
    intro a _ ha
    simp [hempty a ha]
  have hkernel : Fintype.card V = R.card*k := by
    have hh := card_eq_sum_card_fiberwise (s := (univ : Finset V)) (t := R)
      (f := l) (fun v _ => mem_image.mpr ⟨v,mem_univ _,rfl⟩)
    simp only [card_univ] at hh
    rw [hh]
    calc
      _ = ∑ _a ∈ R, k := by
        apply sum_congr rfl
        intro a ha
        obtain ⟨v,_,rfl⟩ := mem_image.mp ha
        exact fiber_card_eq_kernel l v
      _ = _ := by simp
  have hm : R.card ≤ Fintype.card A := card_le_univ _
  have he : (∑ a ∈ R, (N a).card^4) ≤ k * ∑ a ∈ R, (N a).addEnergy (N a) := by
    have hh := sum_le_sum (s := R) (fun a _ => fiber_energy_bound l (N a) a (hN a))
    simpa only [← mul_sum] using hh
  have he' : (∑ a ∈ R, (N a).addEnergy (N a)) ≤ ∑ a : A, (N a).addEnergy (N a) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
  calc
    _ = (∑ a ∈ R, (N a).card)^4 := congrArg (fun n : ℕ => n^4) hsum.symm
    _ ≤ R.card^3 * ∑ a ∈ R, (N a).card^4 := fourth_moment R _
    _ ≤ R.card^3 * (k * ∑ a ∈ R, (N a).addEnergy (N a)) := Nat.mul_le_mul_left _ he
    _ = R.card^2 * Fintype.card V * ∑ a ∈ R, (N a).addEnergy (N a) := by
      rw [hkernel]
      ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm 2)) he'

lemma coordinate_edges_le (l : V →+ A) (N : A → Finset V)
    (hN : ∀ a v, v ∈ N a → l v = a) :
    ∑ a : A, (N a).card ≤ Fintype.card V := by
  have he : Fintype.card V = ∑ a : A, (univ.filter (fun v => l v = a)).card := by
    simpa using card_eq_sum_card_fiberwise (s := (univ : Finset V))
      (t := (univ : Finset A)) (f := l) (fun _ _ => mem_univ _)
  rw [he]
  apply sum_le_sum
  intro a _
  apply card_le_card
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _, hN a v hv⟩

/-- Lower energy bound for arbitrary edge deletions in an additive-code incidence graph. -/
theorem thinning_energy_lower (f : V →+ (I → A)) (N : (I × A) → Finset V)
    (hN : ∀ i a v, v ∈ N (i,a) → f v i = a) :
    (∑ p : I × A, (N p).card)^4 ≤
      (Fintype.card I)^3 * (Fintype.card A)^2 * Fintype.card V *
        ∑ p : I × A, (N p).addEnergy (N p) := by
  have hi (i : I) := coordinate_energy_bound
    ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f) (fun a => N (i,a)) (hN i)
  calc
    _ = (∑ i : I, ∑ a : A, (N (i,a)).card)^4 := by rw [Fintype.sum_prod_type]
    _ ≤ (Fintype.card I)^3 * ∑ i : I, (∑ a : A, (N (i,a)).card)^4 := by
      simpa only [card_univ] using fourth_moment (univ : Finset I) (fun i => ∑ a, (N (i,a)).card)
    _ ≤ (Fintype.card I)^3 * ∑ i : I,
        ((Fintype.card A)^2 * Fintype.card V * ∑ a : A, (N (i,a)).addEnergy (N (i,a))) :=
      Nat.mul_le_mul_left _ (sum_le_sum (fun i _ => hi i))
    _ = _ := by rw [← mul_sum, Fintype.sum_prod_type]; ring

/-- Quantitative obstruction for every K44-free thinning of an additive-code host. -/
theorem thinning_fourth_power_bound (f : V →+ (I → A)) (N : (I × A) → Finset V)
    (hN : ∀ i a v, v ∈ N (i,a) → f v i = a)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Packing.incidence N)) :
    (∑ p : I × A, (N p).card)^4 ≤
      (Fintype.card I)^3 * (Fintype.card A)^2 * Fintype.card V *
        (3*(Fintype.card V)^3 + 4*Fintype.card V*(∑ p : I × A, (N p).card)) :=
  (thinning_energy_lower f N hN).trans
    (Nat.mul_le_mul_left _ (neighborhood_energy_bound N hfree))

/-- At the critical q^4/q^3 host sizes, every free thinning has e^4 <= 7q^27. -/
theorem quartic_thinning_bound (f : V →+ (I → A)) (N : (I × A) → Finset V)
    (hN : ∀ i a v, v ∈ N (i,a) → f v i = a)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Packing.incidence N))
    (hV : Fintype.card V = (Fintype.card A)^4)
    (hI : Fintype.card I = (Fintype.card A)^3) :
    (∑ p : I × A, (N p).card)^4 ≤ 7*(Fintype.card A)^27 := by
  have hmax : (∑ p : I × A, (N p).card) ≤ (Fintype.card I)*Fintype.card V := by
    rw [Fintype.sum_prod_type]
    have hh := sum_le_sum (s := (univ : Finset I)) (fun i _ => coordinate_edges_le
      ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f) (fun a => N (i,a)) (hN i))
    simpa only [sum_const, card_univ, smul_eq_mul] using hh
  have ht := thinning_fourth_power_bound f N hN hfree
  have hb : (∑ p : I × A, (N p).card)^4 ≤
      3*(Fintype.card A)^27 + 4*(Fintype.card A)^26 := by
    calc
      _ ≤ (Fintype.card I)^3 * (Fintype.card A)^2 * Fintype.card V *
          (3*(Fintype.card V)^3 + 4*Fintype.card V*(∑ p : I × A, (N p).card)) := ht
      _ ≤ (Fintype.card I)^3 * (Fintype.card A)^2 * Fintype.card V *
          (3*(Fintype.card V)^3 + 4*Fintype.card V*((Fintype.card I)*Fintype.card V)) := by
        gcongr
      _ = _ := by rw [hV,hI]; ring
  have hp : (Fintype.card A)^26 ≤ (Fintype.card A)^27 :=
    pow_le_pow_right' (show 1 ≤ Fintype.card A from Fintype.card_pos) (by decide)
  nlinarith

/-- The actual neighborhoods in an arbitrary spanning subgraph of a code graph. -/
def thinningNeighborhoods (H : SimpleGraph (V ⊕ (I × A))) (p : I × A) : Finset V :=
  univ.filter (fun v => H.Adj (.inl v) (.inr p))

/-- Swapping the two sides identifies a thinning with its neighborhood set system. -/
def thinningIso (f : V →+ (I → A)) (H : SimpleGraph (V ⊕ (I × A)))
    (hHG : H ≤ Erdos714Coding.graph (fun v i => f v i)) :
    Erdos714Packing.incidence (thinningNeighborhoods H) ≃g H where
  toEquiv := Equiv.sumComm (I × A) V
  map_rel_iff' := by
    intro p q
    cases p with
    | inl p =>
      cases q with
      | inl q =>
        change H.Adj (.inr p) (.inr q) ↔ False
        exact ⟨fun h => hHG h, False.elim⟩
      | inr v =>
        change H.Adj (.inr p) (.inl v) ↔ v ∈ thinningNeighborhoods H p
        simp only [thinningNeighborhoods, mem_filter, mem_univ, true_and]
        exact H.adj_comm _ _
    | inr v =>
      cases q with
      | inl p =>
        change H.Adj (.inl v) (.inr p) ↔ v ∈ thinningNeighborhoods H p
        simp [thinningNeighborhoods]
      | inr w =>
        change H.Adj (.inl v) (.inl w) ↔ False
        exact ⟨fun h => hHG h, False.elim⟩

/-- Every actual K44-free edge subgraph of a critical additive-code host satisfies e^4<=7q^27. -/
theorem edge_subgraph_bound (f : V →+ (I → A)) (H : SimpleGraph (V ⊕ (I × A)))
    (hHG : H ≤ Erdos714Coding.graph (fun v i => f v i))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hV : Fintype.card V = (Fintype.card A)^4)
    (hI : Fintype.card I = (Fintype.card A)^3) :
    H.edgeFinset.card^4 ≤ 7*(Fintype.card A)^27 := by
  let N := thinningNeighborhoods H
  have hN (i : I) (a : A) (v : V) (hv : v ∈ N (i,a)) : f v i = a := by
    have hh := hHG (mem_filter.mp hv).2
    change (i,a) ∈ Erdos714Coding.symbols (fun v i => f v i) v at hh
    exact (Erdos714Coding.mem_symbols _ _ _ _).mp hh
  have hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Packing.incidence N) := by
    rintro ⟨c⟩
    exact hfree ⟨(thinningIso f H hHG).toCopy.comp c⟩
  have he : H.edgeFinset.card = ∑ p : I × A, (N p).card :=
    (thinningIso f H hHG).card_edgeFinset_eq.symm.trans (Erdos714Packing.incidence_edges N)
  rw [he]
  exact quartic_thinning_bound f N hN hf hV hI

/-- A fixed positive edge fraction is impossible once q exceeds an explicit threshold. -/
theorem edge_density_obstruction (f : V →+ (I → A)) (H : SimpleGraph (V ⊕ (I × A)))
    (hHG : H ≤ Erdos714Coding.graph (fun v i => f v i))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hV : Fintype.card V = (Fintype.card A)^4)
    (hI : Fintype.card I = (Fintype.card A)^3)
    (C : ℕ) (hdensity : (Fintype.card A)^7 ≤ C*H.edgeFinset.card) :
    Fintype.card A ≤ 7*C^4 := by
  have hu := Nat.mul_le_mul_left (C^4) (edge_subgraph_bound f H hHG hfree hV hI)
  have hl := Nat.pow_le_pow_left hdensity 4
  have h : (Fintype.card A) * (Fintype.card A)^27 ≤ (7*C^4)*(Fintype.card A)^27 := by
    calc
      _ = ((Fintype.card A)^7)^4 := by ring
      _ ≤ (C*H.edgeFinset.card)^4 := hl
      _ = C^4*H.edgeFinset.card^4 := by ring
      _ ≤ C^4*(7*(Fintype.card A)^27) := hu
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h (pow_pos Fintype.card_pos 27)

#print axioms energy_eq_parallelograms
#print axioms neighborhood_energy_bound
#print axioms coordinate_energy_bound
#print axioms thinning_energy_lower
#print axioms quartic_thinning_bound
#print axioms edge_subgraph_bound
#print axioms edge_density_obstruction

end Erdos714EnergyThinning
