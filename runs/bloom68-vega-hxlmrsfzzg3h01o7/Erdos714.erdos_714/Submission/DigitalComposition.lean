import Submission.IncidenceBridge

/-!
# Exact digital-composition and local-profile obstructions

These lemmas are conditional combinatorial statements. They neither construct
an extremal family nor prove/disprove Erdős 714. This file does not import Spec.
-/

namespace DigitalComposition

variable {A B C D X T P R : Type*}

/-- An injectively indexed complete bipartite rectangle in a relation. -/
def HasBiclique (E : A → B → Prop) (s t : ℕ) : Prop :=
  ∃ (a : Fin s → A) (b : Fin t → B),
    Function.Injective a ∧ Function.Injective b ∧ ∀ i j, E (a i) (b j)

/-- The categorical product, with the two bipartitions kept separate. -/
def tensor (E : A → B → Prop) (F : C → D → Prop) : (A × C) → (B × D) → Prop :=
  fun x y => E x.1 y.1 ∧ F x.2 y.2

/-- Exact product criterion. The projected sets need not have s or t elements:
only their products of cardinalities must be large enough. -/
theorem tensor_hasBiclique_iff (E : A → B → Prop) (F : C → D → Prop) (s t : ℕ) :
    HasBiclique (tensor E F) s t ↔
      ∃ (A₀ : Finset A) (B₀ : Finset B) (C₀ : Finset C) (D₀ : Finset D),
        s ≤ A₀.card * C₀.card ∧ t ≤ B₀.card * D₀.card ∧
        (∀ a ∈ A₀, ∀ b ∈ B₀, E a b) ∧ (∀ c ∈ C₀, ∀ d ∈ D₀, F c d) := by
  classical
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    let A₀ : Finset A := Finset.univ.image fun i => (x i).1
    let B₀ : Finset B := Finset.univ.image fun j => (y j).1
    let C₀ : Finset C := Finset.univ.image fun i => (x i).2
    let D₀ : Finset D := Finset.univ.image fun j => (y j).2
    refine ⟨A₀, B₀, C₀, D₀, ?_, ?_, ?_, ?_⟩
    · let ex : Fin s ↪ A₀ × C₀ := {
        toFun := fun i =>
          (⟨(x i).1, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩,
           ⟨(x i).2, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
        inj' := by
          intro i j h
          apply hx
          exact Prod.ext (congrArg (fun z : A₀ × C₀ => z.1.val) h)
            (congrArg (fun z : A₀ × C₀ => z.2.val) h) }
      simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_coe] using
        Fintype.card_le_of_embedding ex
    · let ey : Fin t ↪ B₀ × D₀ := {
        toFun := fun j =>
          (⟨(y j).1, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩,
           ⟨(y j).2, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
        inj' := by
          intro i j h
          apply hy
          exact Prod.ext (congrArg (fun z : B₀ × D₀ => z.1.val) h)
            (congrArg (fun z : B₀ × D₀ => z.2.val) h) }
      simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_coe] using
        Fintype.card_le_of_embedding ey
    · intro a ha b hb
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      exact (hxy i j).1
    · intro c hc d hd
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
      exact (hxy i j).2
  · rintro ⟨A₀, B₀, C₀, D₀, hs, ht, hE, hF⟩
    obtain ⟨ex⟩ : Nonempty (Fin s ↪ A₀ × C₀) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hs)
    obtain ⟨ey⟩ : Nonempty (Fin t ↪ B₀ × D₀) :=
      Function.Embedding.nonempty_of_card_le (by simpa using ht)
    refine ⟨fun i => ((ex i).1.val, (ex i).2.val),
      fun j => ((ey j).1.val, (ey j).2.val), ?_, ?_, ?_⟩
    · intro i j h
      apply ex.injective
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    · intro i j h
      apply ey.injective
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    · intro i j
      exact ⟨hE _ (ex i).1.property _ (ey j).1.property,
        hF _ (ex i).2.property _ (ey j).2.property⟩

/-- Two oppositely oriented stars suffice; distinct projections in both
coordinates are not required. -/
theorem tensor_hasBiclique_of_opposite_stars (E : A → B → Prop) (F : C → D → Prop)
    {r : ℕ} (hE : HasBiclique E r 1) (hF : HasBiclique F 1 r) :
    HasBiclique (tensor E F) r r := by
  obtain ⟨a, b, ha, _, hab⟩ := hE
  obtain ⟨c, d, _, hd, hcd⟩ := hF
  refine ⟨fun i => (a i, c 0), fun j => (b 0, d j), ?_, ?_, ?_⟩
  · intro i j h
    exact ha (congrArg Prod.fst h)
  · intro i j h
    exact hd (congrArg Prod.snd h)
  · intro i j
    exact ⟨hab i 0, hcd 0 j⟩

/-- The finite number of relation edges. -/
noncomputable def edgeCard [Fintype A] [Fintype B] (E : A → B → Prop) : ℕ := by
  classical
  exact Fintype.card { p : A × B // E p.1 p.2 }

/-- Edge counts in a product multiply exactly. -/
theorem edgeCard_tensor [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (E : A → B → Prop) (F : C → D → Prop) :
    edgeCard (tensor E F) = edgeCard E * edgeCard F := by
  classical
  let e : { p : (A × C) × (B × D) // tensor E F p.1 p.2 } ≃
      ({ p : A × B // E p.1 p.2 } × { p : C × D // F p.1 p.2 }) := {
    toFun := fun z =>
      (⟨(z.val.1.1, z.val.2.1), z.property.1⟩,
       ⟨(z.val.1.2, z.val.2.2), z.property.2⟩)
    invFun := fun z =>
      ⟨((z.1.val.1, z.2.val.1), (z.1.val.2, z.2.val.2)),
        ⟨z.1.property, z.2.property⟩⟩
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl }
  simpa [edgeCard] using Fintype.card_congr e

/-- Any encoding of restriction profiles has fibers of size at most r-1
in a family with no agreement rectangle. -/
theorem card_le_of_profile [Fintype X] [Fintype P]
    (f : X → T → C) {r : ℕ} (hr : 0 < r)
    (t : Fin r → T) (ht : Function.Injective t)
    (profile : X → P)
    (hprofile : ∀ x y, profile x = profile y → ∀ i, f x (t i) = f y (t i))
    (hno : ¬ IncidenceBridge.HasAgreementRectangle f r) :
    Fintype.card X ≤ (r - 1) * Fintype.card P := by
  classical
  have hfib (p : P) : (Finset.univ.filter fun x => profile x = p).card ≤ r - 1 := by
    by_contra hn
    have hle : r ≤ (Finset.univ.filter fun x => profile x = p).card := by omega
    let S : Finset X := Finset.univ.filter fun x => profile x = p
    obtain ⟨e⟩ : Nonempty (Fin r ↪ S) :=
      Function.Embedding.nonempty_of_card_le (by
        simpa only [Fintype.card_fin, Fintype.card_coe] using hle)
    apply hno
    refine ⟨fun i => (e i).val, t, Subtype.val_injective.comp e.injective, ht, ?_⟩
    intro i j k
    apply hprofile _ _ ?_ k
    exact (Finset.mem_filter.mp (e i).property).2.trans
      (Finset.mem_filter.mp (e j).property).2.symm
  have heq : Fintype.card X =
      ∑ p : P, (Finset.univ.filter fun x => profile x = p).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (f := profile) (s := Finset.univ) (t := Finset.univ)
      (by intro x _; exact Finset.mem_univ _))
  calc
    Fintype.card X = ∑ p : P, (Finset.univ.filter fun x => profile x = p).card := heq
    _ ≤ ∑ _p : P, (r - 1) := Finset.sum_le_sum fun p _ => hfib p
    _ = (r - 1) * Fintype.card P := by simp [Nat.mul_comm]

/-- Quantitative local-precision obstruction. Here s+1 is the forbidden
agreement size; only s+1 chosen coordinates and their output differences matter. -/
theorem card_le_of_small_coordinate_differences [Fintype X] [Fintype R]
    [AddCommGroup R] (f : X → T → R) (U : AddSubgroup R) [Fintype U] (s : ℕ)
    (t : Fin (s + 1) → T) (ht : Function.Injective t)
    (hdiff : ∀ x (i : Fin s), f x (t i.succ) - f x (t 0) ∈ U)
    (hno : ¬ IncidenceBridge.HasAgreementRectangle f (s + 1)) :
    Fintype.card X ≤ s * Fintype.card R * (Fintype.card U) ^ s := by
  classical
  let profile : X → R × (Fin s → U) := fun x =>
    (f x (t 0), fun i => ⟨f x (t i.succ) - f x (t 0), hdiff x i⟩)
  have hp : ∀ x y, profile x = profile y → ∀ i, f x (t i) = f y (t i) := by
    intro x y h i
    have hzero : f x (t 0) = f y (t 0) := congrArg Prod.fst h
    refine Fin.cases hzero (fun j => ?_) i
    have hv := congrArg (fun z : R × (Fin s → U) => (z.2 j).val) h
    change f x (t j.succ) - f x (t 0) = f y (t j.succ) - f y (t 0) at hv
    rw [hzero] at hv
    exact sub_left_injective hv
  have h := card_le_of_profile f (by omega : 0 < s + 1) t ht profile hp hno
  simpa [Fintype.card_prod, Fintype.card_fun, Nat.mul_assoc] using h

/-- The additive-label function family associated with a two-variable map. -/
def shiftedFamily [Add R] (H : A → T → R) : (A × R) → T → R :=
  fun x t => H x.1 t + x.2

/-- Every additively separable block with r distinct parameters and positions
supplies an actual agreement rectangle, with all labels specified. -/
theorem rectangle_of_separable [AddCommGroup R] (H : A → T → R) {r : ℕ}
    (a : Fin r → A) (t : Fin r → T)
    (ha : Function.Injective a) (ht : Function.Injective t)
    (u v : Fin r → R) (h : ∀ i j, H (a i) (t j) = u i + v j) :
    IncidenceBridge.HasAgreementRectangle (shiftedFamily H) r := by
  refine ⟨fun i => (a i, -u i), t, ?_, ht, ?_⟩
  · intro i j hij
    exact ha (congrArg Prod.fst hij)
  · intro i i' j
    simp only [shiftedFamily, h]
    abel

/-- A zero mixed difference, as supplied by annihilating ideals, is enough.
No genericity assumption on the selected parameters or positions is made. -/
theorem rectangle_of_mixed_difference [AddCommGroup R] (H : A → T → R) {r : ℕ}
    (a : Fin r → A) (t : Fin r → T)
    (ha : Function.Injective a) (ht : Function.Injective t) (a₀ : A) (t₀ : T)
    (h : ∀ i j, H (a i) (t j) + H a₀ t₀ = H (a i) t₀ + H a₀ (t j)) :
    IncidenceBridge.HasAgreementRectangle (shiftedFamily H) r := by
  apply rectangle_of_separable H a t ha ht
    (fun i => H (a i) t₀ - H a₀ t₀) (fun j => H a₀ (t j))
  intro i j
  calc
    H (a i) (t j) = (H (a i) (t j) + H a₀ t₀) - H a₀ t₀ := by abel
    _ = (H (a i) t₀ + H a₀ (t j)) - H a₀ t₀ := by rw [h i j]
    _ = (H (a i) t₀ - H a₀ t₀) + H a₀ (t j) := by abel

end DigitalComposition
