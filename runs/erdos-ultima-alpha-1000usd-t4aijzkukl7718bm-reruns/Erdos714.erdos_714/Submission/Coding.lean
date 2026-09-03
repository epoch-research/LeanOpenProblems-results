import Submission.Packing

/-!
Coding formulations and a linear-code obstruction for the balanced Zarankiewicz problem.
These are reductions and obstructions to a class of constructions, not a solution to Erdős 714.
-/

open Finset SimpleGraph
open Classical

namespace Erdos714Coding

variable {C I A : Type*} [Fintype I]

/-- A codeword is incident with its coordinate-symbol pairs. -/
def symbols (f : C → I → A) (c : C) : Finset (I × A) :=
  univ.map ⟨fun i => (i, f c i), fun _ _ h => congrArg Prod.fst h⟩

@[simp] lemma mem_symbols (f : C → I → A) (c : C) (i : I) (a : A) :
    (i,a) ∈ symbols f c ↔ f c i = a := by
  simp [symbols]

/-- The bipartite graph associated with a code. -/
def graph (f : C → I → A) : SimpleGraph (C ⊕ (I × A)) :=
  Erdos714Packing.incidence (symbols f)

/-- Coordinates where all the chosen words agree. -/
noncomputable def agreement (f : C → I → A) {r : ℕ} (hr : 0 < r) (g : Fin r ↪ C) : Finset I :=
  univ.filter (fun i => ∀ j, f (g j) i = f (g ⟨0,hr⟩) i)

variable [Fintype A]

lemma common_card_eq_agreement (f : C → I → A) {r : ℕ} (hr : 0 < r)
    (g : Fin r ↪ C) :
    (Erdos714Packing.common (symbols f) g).card = (agreement f hr g).card := by
  let e : I ↪ I × A :=
    ⟨fun i => (i, f (g ⟨0,hr⟩) i), fun _ _ h => congrArg Prod.fst h⟩
  have he : Erdos714Packing.common (symbols f) g = (agreement f hr g).map e := by
    ext p
    rcases p with ⟨i,a⟩
    simp only [Erdos714Packing.mem_common, mem_symbols, mem_map]
    constructor
    · intro h
      refine ⟨i, ?_, ?_⟩
      · simp only [agreement, mem_filter, mem_univ, true_and]
        intro j
        exact (h j).trans (h ⟨0,hr⟩).symm
      · exact Prod.ext rfl (h ⟨0,hr⟩)
    · rintro ⟨k, hk, heq⟩
      have hki : k = i := congrArg Prod.fst heq
      subst k
      have ha : f (g ⟨0,hr⟩) i = a := congrArg Prod.snd heq
      intro j
      exact ((mem_filter.mp hk).2 j).trans ha
  rw [he, card_map]

/-- Exact code formulation: `r` distinct words may agree in fewer than `r` positions. -/
theorem free_iff_agreement (f : C → I → A) {r : ℕ} (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (graph f) ↔
      ∀ g : Fin r ↪ C, (agreement f hr g).card < r := by
  rw [graph, Erdos714Packing.free_iff_common_card _ hr]
  simp only [common_card_eq_agreement f hr]

variable [Fintype C]

/-- There is exactly one incidence per codeword and coordinate. -/
theorem edge_count (f : C → I → A) :
    (graph f).edgeFinset.card = Fintype.card C * Fintype.card I := by
  rw [graph, Erdos714Packing.incidence_edges]
  simp [symbols]

/-- The total number of vertices includes all coordinate-symbol pairs. -/
theorem vertex_count : Fintype.card (C ⊕ (I × A)) =
    Fintype.card C + Fintype.card I * Fintype.card A := by simp

end Erdos714Coding

namespace Erdos714LinearCode

open Erdos714Coding

variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Fintype F] [Fintype I]

/-- On a scalar line, the words agree at every zero coordinate of its direction. -/
theorem zero_coordinates_lt (f : V →ₗ[F] (I → F)) {r : ℕ}
    (hr : 0 < r) (hq : r ≤ Fintype.card F)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (graph f))
    {v : V} (hv : v ≠ 0) :
    (univ.filter (fun i => f v i = 0)).card < r := by
  obtain ⟨t⟩ := Function.Embedding.nonempty_of_card_le (α := Fin r) (β := F) (by simpa using hq)
  let g : Fin r ↪ V :=
    ⟨fun i => t i • v, fun i j h => t.injective (smul_left_injective F hv h)⟩
  have hg := (free_iff_agreement (f : V → I → F) hr).mp hfree g
  apply lt_of_le_of_lt (card_le_card (t := agreement (f : V → I → F) hr g) ?_) hg
  intro i hi
  have hz := (mem_filter.mp hi).2
  simp [agreement, g, hz]

variable [Fintype V]

/-- A sufficiently large vertex selection contains `r` points on a line in any direction.
The proof counts all translates, so no choice of a quotient basis is needed. -/
lemma many_points_on_line (S : Finset V) (u : V) {r : ℕ}
    (hS : (r-1) * Fintype.card V < Fintype.card F * S.card) :
    ∃ v : V, r ≤ (univ.filter (fun t : F => v + t • u ∈ S)).card := by
  let T (v : V) : Finset F := univ.filter (fun t => v + t • u ∈ S)
  have hsum : ∑ v, (T v).card = Fintype.card F * S.card := by
    have hcard (t : F) : (univ.filter (fun v : V => v + t • u ∈ S)).card = S.card := by
      have he : univ.filter (fun v : V => v + t • u ∈ S) =
          S.map (Equiv.subRight (t • u)).toEmbedding := by
        ext v
        simp
      rw [he, card_map]
    simp only [T, card_filter]
    rw [sum_comm]
    simp_rw [← card_filter, hcard]
    simp
  by_contra! hn
  have hb : ∑ v, (T v).card ≤ (r-1) * Fintype.card V := by
    calc
      ∑ v, (T v).card ≤ ∑ _v : V, (r-1) := by
        apply sum_le_sum
        intro v _
        have h := hn v
        dsimp [T]
        omega
      _ = _ := by simp [mul_comm]
  omega

/-- Even an arbitrary dense selection of a linear code inherits the scalar-line obstruction. -/
theorem selected_zero_coordinates_lt (f : V →ₗ[F] (I → F)) (S : Finset V) {r : ℕ}
    (hr : 0 < r) (hS : (r-1) * Fintype.card V < Fintype.card F * S.card)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free
      (graph (fun v : S => f v.1))) {u : V} (hu : u ≠ 0) :
    (univ.filter (fun i => f u i = 0)).card < r := by
  obtain ⟨v,hv⟩ := many_points_on_line S u hS
  obtain ⟨t,ht⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin r) (s := univ.filter (fun t : F => v + t • u ∈ S)) (by simpa using hv)
  have hmem (i : Fin r) : v + t i • u ∈ S := (mem_filter.mp (ht ⟨i,rfl⟩)).2
  let g : Fin r ↪ S := ⟨fun i => ⟨v+t i • u, hmem i⟩, by
    intro i j h
    apply t.injective
    apply smul_left_injective F hu
    exact add_left_cancel (congrArg Subtype.val h)⟩
  have hg := (free_iff_agreement (fun v : S => f v.1) hr).mp hfree g
  apply lt_of_le_of_lt (card_le_card (t := agreement (fun v : S => f v.1) hr g) ?_) hg
  intro i hi
  have hz := (mem_filter.mp hi).2
  simp [agreement, g, hz]

/-- A linear functional has at least the average fiber size in its zero fiber. -/
lemma card_le_field_mul_zero_fiber (l : V →ₗ[F] F) :
    Fintype.card V ≤ Fintype.card F * (univ.filter (fun v => l v = 0)).card := by
  have hf (a : F) : (univ.filter (fun v => l v = a)).card ≤
      (univ.filter (fun v => l v = 0)).card := by
    by_cases hn : (univ.filter (fun v => l v = a)).Nonempty
    · obtain ⟨v₀,hv₀⟩ := hn
      have hv₀' := (mem_filter.mp hv₀).2
      apply card_le_card_of_injOn (fun v => v-v₀)
      · intro v hv
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hv ⊢
        simp [map_sub, hv, hv₀']
      · exact (sub_left_injective).injOn
    · simp [not_nonempty_iff_eq_empty.mp hn]
  have hsum : Fintype.card V = ∑ a : F, (univ.filter (fun v => l v = a)).card := by
    simpa using (card_eq_sum_card_fiberwise (s := (univ : Finset V))
      (t := (univ : Finset F)) (f := l) (fun _ _ => mem_univ _))
  rw [hsum]
  calc
    ∑ a : F, (univ.filter (fun v => l v = a)).card ≤
        ∑ _a : F, (univ.filter (fun v => l v = 0)).card := sum_le_sum (fun a _ => hf a)
    _ = _ := by simp

/-- A necessary length bound for any finite linear code whose incidence graph is free.
For `|V|=q^r`, it forces length `O_r(q)`, not the desired `q^(r-1)`. -/
theorem length_bound_of_zeros (f : V →ₗ[F] (I → F)) {r : ℕ}
    (hzeros : ∀ v : V, v ≠ 0 → (univ.filter (fun i => f v i = 0)).card < r) :
    Fintype.card I * (Fintype.card V - Fintype.card F) ≤
      Fintype.card F * ((Fintype.card V - 1) * (r-1)) := by
  let Z (i : I) : Finset V := univ.filter (fun v => v ≠ 0 ∧ f v i = 0)
  have hz (i : I) : Fintype.card V - Fintype.card F ≤ Fintype.card F * (Z i).card := by
    have h := card_le_field_mul_zero_fiber ((LinearMap.proj i).comp f)
    have he : univ.filter (fun v => f v i = 0) = insert 0 (Z i) := by
      ext v
      by_cases hv : v = 0 <;> simp [Z, hv]
    have hn : (0 : V) ∉ Z i := by simp [Z]
    change Fintype.card V ≤ Fintype.card F * (univ.filter (fun v => f v i = 0)).card at h
    rw [he, card_insert_of_notMem hn] at h
    rw [Nat.mul_add, Nat.mul_one] at h
    omega
  have hsum : ∑ i, (Z i).card ≤ (Fintype.card V - 1) * (r-1) := by
    have he : ∑ i, (Z i).card =
        ∑ v ∈ (univ : Finset V).erase 0, (univ.filter (fun i => f v i = 0)).card := by
      have hZ (i : I) : Z i = ((univ : Finset V).erase 0).filter (fun v => f v i = 0) := by
        ext v
        simp [Z]
      simp only [hZ, card_filter]
      rw [sum_comm]
    rw [he]
    calc
      ∑ v ∈ (univ : Finset V).erase 0, (univ.filter (fun i => f v i = 0)).card ≤
          ∑ _v ∈ (univ : Finset V).erase 0, (r-1) := by
        apply sum_le_sum
        intro v hv
        have hv0 : v ≠ 0 := (mem_erase.mp hv).1
        have h := hzeros v hv0
        omega
      _ = _ := by simp
  calc
    Fintype.card I * (Fintype.card V - Fintype.card F) =
        ∑ _i : I, (Fintype.card V - Fintype.card F) := by simp
    _ ≤ ∑ i, Fintype.card F * (Z i).card := sum_le_sum (fun i _ => hz i)
    _ = Fintype.card F * ∑ i, (Z i).card := (mul_sum ..).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hsum

/-- Full linear codes satisfy the same length bound. -/
theorem length_bound (f : V →ₗ[F] (I → F)) {r : ℕ}
    (hr : 0 < r) (hq : r ≤ Fintype.card F)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (graph f)) :
    Fintype.card I * (Fintype.card V - Fintype.card F) ≤
      Fintype.card F * ((Fintype.card V - 1) * (r-1)) :=
  length_bound_of_zeros f (fun _ hv => zero_coordinates_lt f hr hq hfree hv)

/-- The length obstruction persists after taking any selection of density greater than `(r-1)/q`. -/
theorem selected_length_bound (f : V →ₗ[F] (I → F)) (S : Finset V) {r : ℕ}
    (hr : 0 < r) (hS : (r-1) * Fintype.card V < Fintype.card F * S.card)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free
      (graph (fun v : S => f v.1))) :
    Fintype.card I * (Fintype.card V - Fintype.card F) ≤
      Fintype.card F * ((Fintype.card V - 1) * (r-1)) :=
  length_bound_of_zeros f (fun _ hv => selected_zero_coordinates_lt f S hr hS hfree hv)

lemma fourth_case_arithmetic {q : ℕ} (hq : 4 ≤ q) :
    q * ((q^4-1)*3) < q^3*(q^4-q) := by
  have hq0 : 0 < q := by omega
  have h13 : q ≤ q^3 := by nlinarith [sq_nonneg (q : ℤ)]
  have h43 : q^3 ≤ q^4-q := by
    have h : 2*q^3 ≤ q*q^3 := Nat.mul_le_mul_right _ (by omega : 2 ≤ q)
    have hp : q*q^3 = q^4 := by ring
    omega
  calc
    q * ((q^4-1)*3) ≤ 3*q^5 := by
      calc
        q * ((q^4-1)*3) ≤ q*(q^4*3) := Nat.mul_le_mul_left q (Nat.mul_le_mul_right 3 (Nat.sub_le _ _))
        _ = _ := by ring
    _ < 4*q^5 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ ≤ q^6 := by
      calc
        4*q^5 ≤ q*q^5 := Nat.mul_le_mul_right _ hq
        _ = _ := by ring
    _ ≤ q^3*(q^4-q) := by
      calc
        q^6 = q^3*q^3 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h43

/-- At the fourth-case parameters, a free vertex selection from ANY linear code
contains at most `3q^3` words, rather than a positive proportion of `q^4` words. -/
theorem fourth_case_selection_bound
    (f : (Fin 4 → F) →ₗ[F] ((Fin 3 → F) → F))
    (S : Finset (Fin 4 → F)) (hq : 4 ≤ Fintype.card F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (fun v : S => f v.1))) :
    S.card ≤ 3 * (Fintype.card F)^3 := by
  by_contra! hS
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hd : (4-1) * Fintype.card (Fin 4 → F) < Fintype.card F * S.card := by
    have h := Nat.mul_lt_mul_of_pos_left hS hpos
    simpa [Fintype.card_fun, Fintype.card_fin, show Fintype.card F * (3 * Fintype.card F^3) =
      3 * Fintype.card F^4 by ring] using h
  have h := selected_length_bound f S (r := 4) (by omega) hd hfree
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.reduceSub] at h
  exact (fourth_case_arithmetic hq).not_ge h

end Erdos714LinearCode

#print axioms Erdos714Coding.free_iff_agreement
#print axioms Erdos714Coding.edge_count
#print axioms Erdos714LinearCode.zero_coordinates_lt
#print axioms Erdos714LinearCode.length_bound

#print axioms Erdos714LinearCode.selected_length_bound
#print axioms Erdos714LinearCode.fourth_case_selection_bound
