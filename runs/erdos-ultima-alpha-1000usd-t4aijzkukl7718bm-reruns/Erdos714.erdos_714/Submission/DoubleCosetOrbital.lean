import FormalConjecturesUtil

/-!
Exact incidence semantics for ordered double-coset orbitals. These graphs
need not be matching covers when a vertex stabilizer is replaced by a subgroup.
The results below do not prove or disprove Erdős 714.
-/
noncomputable section
open SimpleGraph Classical

namespace Erdos714DoubleCoset

variable {Γ : Type*} [Group Γ]

abbrev Cosets (H : Subgroup Γ) := Quotient (QuotientGroup.rightRel H)

def coset (H : Subgroup Γ) (x : Γ) : Cosets H := Quotient.mk _ x

lemma coset_eq (H : Subgroup Γ) (x y : Γ) :
    coset H x = coset H y ↔ y * x⁻¹ ∈ H := by
  exact Quotient.eq.trans QuotientGroup.rightRel_apply

/-- The orbit of `(H, K*g)` under simultaneous right multiplication. -/
def Rel (H K : Subgroup Γ) (g : Γ) (x : Cosets H) (y : Cosets K) : Prop :=
  ∃ t : Γ, coset H t = x ∧ coset K (g*t) = y

def graph (H K : Subgroup Γ) (g : Γ) : SimpleGraph (Cosets H ⊕ Cosets K) where
  Adj x y := match x,y with
    | .inl u, .inr v => Rel H K g u v
    | .inr v, .inl u => Rel H K g u v
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

/-- This fixes the side and inverse conventions in the actual double-coset test. -/
theorem relation_iff (H K : Subgroup Γ) (g x y : Γ) :
    Rel H K g (coset H x) (coset K y) ↔
      ∃ k ∈ K, ∃ h ∈ H, y*x⁻¹ = k*g*h := by
  constructor
  · rintro ⟨t, ht, hy⟩
    have hh := H.inv_mem ((coset_eq H t x).mp ht)
    simp only [mul_inv_rev, inv_inv] at hh
    refine ⟨y*(g*t)⁻¹, (coset_eq K (g*t) y).mp hy, t*x⁻¹, hh, ?_⟩
    group
  · rintro ⟨k,hk,h,hh,he⟩
    refine ⟨h*x, (coset_eq H _ _).mpr ?_, (coset_eq K _ _).mpr ?_⟩
    · convert H.inv_mem hh using 1; group
    · have hy : y*(g*(h*x))⁻¹ = k := by
        calc
          y*(g*(h*x))⁻¹ = (y*x⁻¹)*(k*g*h)⁻¹*k := by group
          _ = k := by rw [he]; group
      rwa [hy]

/-- A certificate in representatives gives a genuine copy in the quotient graph. -/
def representativesCopy (H K : Subgroup Γ) (g : Γ) {r s : ℕ}
    (L : Fin r → Γ) (R : Fin s → Γ)
    (hL : ∀ i j, L j * (L i)⁻¹ ∈ H → i = j)
    (hR : ∀ i j, R j * (R i)⁻¹ ∈ K → i = j)
    (hedge : ∀ i j, ∃ k ∈ K, ∃ h ∈ H, R j * (L i)⁻¹ = k*g*h) :
    Copy (completeBipartiteGraph (Fin r) (Fin s)) (graph H K g) := by
  let l : Fin r ↪ Cosets H := ⟨fun i => coset H (L i), fun i j he =>
    hL i j ((coset_eq H _ _).mp he)⟩
  let r' : Fin s ↪ Cosets K := ⟨fun i => coset K (R i), fun i j he =>
    hR i j ((coset_eq K _ _).mp he)⟩
  have he (i : Fin r) (j : Fin s) : Rel H K g (l i) (r' j) :=
    (relation_iff H K g _ _).mpr (hedge i j)
  refine ⟨⟨l.sumMap r', ?_⟩, (l.sumMap r').injective⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at h
    | inr j => exact he i j
  | inr j =>
    cases y with
    | inl i => exact he i j
    | inr k => simp at h

/-- If the subgroup centralizes `a`, distinct conjugates certify distinct cosets. -/
theorem distinct_of_conjugates (H : Subgroup Γ) (a : Γ)
    (hc : ∀ h ∈ H, Commute h a) {x y : Γ}
    (hne : x⁻¹*a*x ≠ y⁻¹*a*y) : coset H x ≠ coset H y := by
  intro he
  have hh := (hc _ ((coset_eq H x y).mp he)).eq
  apply hne
  have ht := congrArg (fun z => y⁻¹*z*x) hh
  convert ht using 1 <;> group

/-- Trivial intersection of the two conjugated stabilizers. -/
def FreePair (H K : Subgroup Γ) (g : Γ) : Prop :=
  ∀ h ∈ H, g*h*g⁻¹ ∈ K → h = 1

lemma transporter_unique (H K : Subgroup Γ) (g : Γ) (hf : FreePair H K g)
    {s t : Γ} (hH : coset H s = coset H t)
    (hK : coset K (g*s) = coset K (g*t)) : s = t := by
  have hh : t*s⁻¹ ∈ H := (coset_eq H _ _).mp hH
  have hk : g*(t*s⁻¹)*g⁻¹ ∈ K := by
    have h := (coset_eq K _ _).mp hK
    convert h using 1; group
  have he := hf _ hh hk
  exact (mul_inv_eq_one.mp he).symm

/-- Under the free-pair hypothesis, each group element gives exactly one edge. -/
def edgeEquiv (H K : Subgroup Γ) (g : Γ) (hf : FreePair H K g) :
    Γ ≃ (graph H K g).edgeSet := by
  let f : Γ → (graph H K g).edgeSet := fun t =>
    ⟨s(Sum.inl (coset H t), Sum.inr (coset K (g*t))), ⟨t,rfl,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro s t he
    have h := Sym2.eq_iff.mp (congrArg Subtype.val he)
    rcases h with ⟨hH,hK⟩ | ⟨hH,hK⟩
    · exact transporter_unique H K g hf (Sum.inl.inj hH) (Sum.inr.inj hK)
    · exact False.elim (Sum.inl_ne_inr hH)
  · rintro ⟨e,he⟩
    induction e using Sym2.ind with
    | _ x y =>
      cases x with
      | inl x =>
        cases y with
        | inl y => exact False.elim he
        | inr y =>
          obtain ⟨t,ht,hy⟩ := he
          exact ⟨t, Subtype.ext (by
            change s(Sum.inl (coset H t), Sum.inr (coset K (g*t))) =
              s(Sum.inl x, Sum.inr y)
            rw [ht,hy])⟩
      | inr z =>
        cases y with
        | inr w => exact False.elim he
        | inl x =>
          obtain ⟨t,ht,hy⟩ := he
          exact ⟨t, Subtype.ext (by
            change s(Sum.inl (coset H t), Sum.inr (coset K (g*t))) =
              s(Sum.inr z, Sum.inl x)
            rw [ht,hy,Sym2.eq_swap])⟩


/-- The canonical neighborhood is the left stabilizer, not a family of matching
partners over every old neighbor. -/
def neighborEquiv (H K : Subgroup Γ) (g : Γ) (hf : FreePair H K g) :
    H ≃ (graph H K g).neighborSet (.inl (coset H 1)) := by
  have hbase (h : H) : coset H (h : Γ) = coset H 1 := by
    apply (coset_eq H _ _).mpr
    simp
  let f : H → (graph H K g).neighborSet (.inl (coset H 1)) := fun h =>
    ⟨.inr (coset K (g*h)), ⟨h, hbase h, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro h h' he
    apply Subtype.ext
    apply transporter_unique H K g hf ((hbase h).trans (hbase h').symm)
    exact Sum.inr.inj (congrArg Subtype.val he)
  · rintro ⟨v,hv⟩
    cases v with
    | inl v => exact False.elim hv
    | inr v =>
      obtain ⟨t,ht,hy⟩ := hv
      have hh : t ∈ H := by
        have h := (coset_eq H t 1).mp ht
        simpa using H.inv_mem h
      refine ⟨⟨t,hh⟩, Subtype.ext ?_⟩
      change Sum.inr (coset K (g*t)) = Sum.inr v
      rw [hy]

theorem neighbor_card (H K : Subgroup Γ) (g : Γ) (hf : FreePair H K g) :
    Nat.card ((graph H K g).neighborSet (.inl (coset H 1))) = Nat.card H :=
  Nat.card_congr (neighborEquiv H K g hf).symm

/-- Shrinking either stabilizer preserves the free-pair property. -/
theorem freePair_mono {H K H₀ K₀ : Subgroup Γ} {g : Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hf : FreePair H K g) : FreePair H₀ K₀ g := by
  intro h hh hk
  exact hf h (hH hh) (hK hk)

/-- In particular, a free-pair orbital has `|Γ|` edges even after shrinking
both stabilizers. It is not a matching cover in general. -/
theorem edge_card (H K : Subgroup Γ) (g : Γ) (hf : FreePair H K g) :
    Nat.card (graph H K g).edgeSet = Nat.card Γ :=
  Nat.card_congr (edgeEquiv H K g hf).symm

/-- The two parts have the indices of their respective stabilizers. -/
theorem vertex_card [Finite Γ] (H K : Subgroup Γ) :
    Nat.card (Cosets H ⊕ Cosets K) = H.index + K.index := by
  rw [Nat.card_sum]
  congr 1
  · exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)
  · exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel K)


/-- Index-two refinements double the vertices, whereas `edge_card` says their
edge count is unchanged when the original pair is free. -/
theorem index_two_vertex_card [Finite Γ] {H K H₀ K₀ : Subgroup Γ}
    (hH : H₀ ≤ H) (hK : K₀ ≤ K)
    (hiH : H₀.relIndex H = 2) (hiK : K₀.relIndex K = 2) :
    Nat.card (Cosets H₀ ⊕ Cosets K₀) = 2 * Nat.card (Cosets H ⊕ Cosets K) := by
  rw [vertex_card, vertex_card, ← H₀.relIndex_mul_index hH,
    ← K₀.relIndex_mul_index hK, hiH, hiK]
  omega


/-- Forgetting an orientation means enlarging its stabilizer. -/
def forget {H₀ H : Subgroup Γ} (hH : H₀ ≤ H) : Cosets H₀ → Cosets H :=
  Quotient.map' id (by
    intro x y h
    exact QuotientGroup.rightRel_apply.mpr (hH (QuotientGroup.rightRel_apply.mp h)))

@[simp] lemma forget_coset {H₀ H : Subgroup Γ} (hH : H₀ ≤ H) (t : Γ) :
    forget hH (coset H₀ t) = coset H t := rfl

/-- Each old edge has one lifted edge when the original pair stabilizer is
trivial, rather than a matching joining all of its sheets. -/
theorem unique_edge_lift {H K H₀ K₀ : Subgroup Γ} (g : Γ)
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hf : FreePair H K g) (t : Γ) :
    ∃! p : Cosets H₀ × Cosets K₀,
      Rel H₀ K₀ g p.1 p.2 ∧
      forget hH p.1 = coset H t ∧ forget hK p.2 = coset K (g*t) := by
  refine ⟨(coset H₀ t, coset K₀ (g*t)), ⟨⟨t,rfl,rfl⟩,rfl,rfl⟩, ?_⟩
  rintro ⟨x,y⟩ ⟨⟨s,hs,hy⟩,h₁,h₂⟩
  dsimp only at hs hy h₁ h₂
  rw [← hs] at h₁
  rw [← hy] at h₂
  have hst : s = t := transporter_unique H K g hf h₁ h₂
  subst s
  exact Prod.ext hs.symm hy.symm

/-- The canonical left degree scales by the index of the smaller stabilizer. -/
theorem neighborhood_index {H K H₀ K₀ : Subgroup Γ} (g : Γ)
    (hH : H₀ ≤ H) (hK : K₀ ≤ K) (hf : FreePair H K g) :
    Nat.card ((graph H₀ K₀ g).neighborSet (.inl (coset H₀ 1))) * H₀.relIndex H =
      Nat.card ((graph H K g).neighborSet (.inl (coset H 1))) := by
  rw [neighbor_card _ _ _ (freePair_mono hH hK hf), neighbor_card _ _ _ hf]
  have he := (H₀.subgroupOf H).card_mul_index
  have hc : Nat.card (H₀.subgroupOf H) = Nat.card H₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  rwa [hc] at he

end Erdos714DoubleCoset

#print axioms Erdos714DoubleCoset.relation_iff
#print axioms Erdos714DoubleCoset.representativesCopy
#print axioms Erdos714DoubleCoset.distinct_of_conjugates
#print axioms Erdos714DoubleCoset.edge_card
#print axioms Erdos714DoubleCoset.vertex_card

#print axioms Erdos714DoubleCoset.neighbor_card
#print axioms Erdos714DoubleCoset.index_two_vertex_card

#print axioms Erdos714DoubleCoset.unique_edge_lift
#print axioms Erdos714DoubleCoset.neighborhood_index
