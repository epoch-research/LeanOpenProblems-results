import Submission.BicliquePartition
import Submission.AdditiveCoding

/-! First-order behavior of polynomial graphs on square-zero ideal cosets.
This is an obstruction to congruence-ring constructions, not Erdős 714. -/

set_option maxHeartbeats 3000000
noncomputable section
open Classical SimpleGraph Finset
namespace Erdos714SquareZero
variable {R σ : Type*} [CommRing R]

lemma affine_on_coset (I : Ideal R) (hI : ∀ a b : I, (a : R)*(b : R)=0)
    (P : MvPolynomial σ R) (x : σ → R) :
    ∃ L : (σ → I) →+ I, ∀ u : σ → I,
      MvPolynomial.eval (fun i => x i+(u i : R)) P = MvPolynomial.eval x P+(L u : R) := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0,fun u => by simp⟩
  | add P Q hP hQ =>
    obtain ⟨L,hL⟩ := hP
    obtain ⟨M,hM⟩ := hQ
    refine ⟨L+M,?_⟩
    intro u
    simp only [MvPolynomial.eval_add,hL,hM,AddMonoidHom.add_apply,Submodule.coe_add]
    ring
  | mul_X P i hP =>
    obtain ⟨L,hL⟩ := hP
    let e : (σ → I) →+ I := Pi.evalAddMonoidHom (fun _ : σ => I) i
    refine ⟨MvPolynomial.eval x P • e + x i • L,?_⟩
    intro u
    simp only [MvPolynomial.eval_mul,MvPolynomial.eval_X,hL,
      AddMonoidHom.add_apply,AddMonoidHom.smul_apply,Submodule.coe_add,
      Submodule.coe_smul,smul_eq_mul]
    change (MvPolynomial.eval x P+(L u : R))*(x i+(u i : R)) =
      MvPolynomial.eval x P*x i+(MvPolynomial.eval x P*(u i : R)+x i*(L u : R))
    linear_combination hI (L u) (u i)

variable {τ : Type*}

def includeLeft {I : Ideal R} : (σ → I) →+ (σ ⊕ τ → I) where
  toFun u := Sum.elim u 0
  map_zero' := by ext i; cases i <;> rfl
  map_add' u v := by ext i; cases i <;> simp

def includeRight {I : Ideal R} : (τ → I) →+ (σ ⊕ τ → I) where
  toFun v := Sum.elim 0 v
  map_zero' := by ext i; cases i <;> rfl
  map_add' u v := by ext i; cases i <;> simp

lemma split_affine (I : Ideal R) (hI : ∀ a b : I, (a : R)*(b : R)=0)
    (P : MvPolynomial (σ ⊕ τ) R) (x : σ → R) (y : τ → R) :
    ∃ L : (σ → I) →+ I, ∃ M : (τ → I) →+ I,
      ∀ u v, MvPolynomial.eval (Sum.elim (fun i => x i+(u i : R))
        (fun j => y j+(v j : R))) P = MvPolynomial.eval (Sum.elim x y) P+(L u : R)+(M v : R) := by
  obtain ⟨T,hT⟩ := affine_on_coset I hI P (Sum.elim x y)
  refine ⟨T.comp includeLeft,T.comp includeRight,?_⟩
  intro u v
  let w : σ ⊕ τ → I := includeLeft (τ := τ) u + includeRight (σ := σ) v
  have he : (fun i => Sum.elim x y i+((w i) : R)) =
      Sum.elim (fun i => x i+(u i : R)) (fun j => y j+(v j : R)) := by
    ext i; cases i <;> simp [w, includeLeft,includeRight]
  have hh := hT w
  rw [he] at hh
  dsimp [w] at hh
  rw [map_add] at hh
  simpa [AddMonoidHom.comp_apply,add_assoc] using hh


lemma fiber_card_bound {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] (f : A →+ B) (b : B) (hb : ∃ a, f a = b) :
    Fintype.card A ≤ Fintype.card B * Fintype.card {a : A // f a = b} := by
  obtain ⟨a₀, ha₀⟩ := hb
  have he : Fintype.card {a : A // f a = 0} = Fintype.card {a : A // f a = b} := by
    apply Fintype.card_congr
    refine ⟨(fun a => ⟨a.val+a₀, by simp [map_add, a.property, ha₀]⟩),
      (fun a => ⟨a.val-a₀, by simp [map_sub, a.property, ha₀]⟩), ?_, ?_⟩
    · intro a; apply Subtype.ext; simp
    · intro a; apply Subtype.ext; simp
  have hh := Erdos714AdditiveCoding.card_le_alphabet_mul_kernel f
  simpa only [← Fintype.card_subtype, he] using hh

lemma pi_fiber_card_bound (I : Ideal R) [Fintype I] [Fintype σ]
    (L : (σ → I) →+ I) (a : I) (ha : ∃ u, L u = a) (hd : 1 ≤ Fintype.card σ) :
    Fintype.card I ^ (Fintype.card σ-1) ≤ Fintype.card {u : σ → I // L u = a} := by
  have hh := fiber_card_bound L a ha
  simp only [Fintype.card_fun] at hh
  have he : Fintype.card σ = (Fintype.card σ-1)+1 := by omega
  rw [he, pow_succ, mul_comm] at hh
  have hz := Nat.le_of_mul_le_mul_left hh (Fintype.card_pos (α := I))
  simpa only [Fintype.card_eq_nat_card] using hz

section Separated
variable {S T U V A : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup A]
variable (C : S → T → A) (L : S → T → U →+ A) (M : S → T → V →+ A)

/-- A separately affine bipartite relation, with arbitrary base pairs. -/
def separatedGraph : SimpleGraph ((S × U) ⊕ (T × V)) where
  Adj p q := match p, q with
    | .inl (s,u), .inr (t,v) => C s t+L s t u+M s t v=0
    | .inr (t,v), .inl (s,u) => C s t+L s t u+M s t v=0
    | _, _ => False
  symm := by intro p q; cases p <;> cases q <;> simp
  loopless := by intro p; cases p <;> simp

abbrev Block := {z : (S × T) × (A × A) //
  C z.1.1 z.1.2+z.2.1+z.2.2=0 ∧
  (∃ u, L z.1.1 z.1.2 u=z.2.1) ∧ (∃ v, M z.1.1 z.1.2 v=z.2.2)}

abbrev LeftFiber (z : Block C L M) := {u : U // L z.val.1.1 z.val.1.2 u=z.val.2.1}
abbrev RightFiber (z : Block C L M) := {v : V // M z.val.1.1 z.val.1.2 v=z.val.2.2}

def blockCopy (z : Block C L M) :
    (completeBipartiteGraph (LeftFiber C L M z) (RightFiber C L M z)).Copy
      (separatedGraph C L M) where
  toHom := {
    toFun := Sum.map (fun u => (z.val.1.1,u.val)) (fun v => (z.val.1.2,v.val))
    map_rel' := by
      intro p q hpq
      cases p with
      | inl u =>
        cases q with
        | inl u' => simp at hpq
        | inr v => exact (by dsimp [separatedGraph]; rw [u.property,v.property]; exact z.property.1)
      | inr v =>
        cases q with
        | inl u => exact (by dsimp [separatedGraph]; rw [u.property,v.property]; exact z.property.1)
        | inr v' => simp at hpq
  }
  injective' := by
    intro p q hpq
    change Sum.map _ _ p = Sum.map _ _ q at hpq
    cases p <;> cases q <;> simp only [Sum.map_inl,Sum.map_inr,Sum.inl.injEq,
      Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Prod.mk.injEq] at hpq ⊢
    · exact Subtype.ext hpq.2
    · exact Subtype.ext hpq.2

lemma separated_edge_rep (e : (separatedGraph C L M).edgeSet) :
    ∃ s u t v, e.val=s(Sum.inl (s,u),Sum.inr (t,v)) ∧ C s t+L s t u+M s t v=0 := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | hf p q =>
    cases p with
    | inl su =>
      cases q with
      | inl su' => exact False.elim he
      | inr tv => exact ⟨su.1,su.2,tv.1,tv.2,rfl,he⟩
    | inr tv =>
      cases q with
      | inl su => exact ⟨su.1,su.2,tv.1,tv.2,Sym2.eq_swap,he⟩
      | inr tv' => exact False.elim he

variable [Fintype S] [Fintype T] [Fintype U] [Fintype V] [Fintype A]

omit [Fintype S] [Fintype T] [Fintype U] [Fintype V] [Fintype A] in
lemma block_partition : Function.Bijective
    (Erdos714BicliquePartition.edgeMap (separatedGraph C L M) (blockCopy C L M)) := by
  constructor
  · rintro ⟨z,e⟩ ⟨z',e'⟩ hh
    obtain ⟨u,v,he⟩ := Erdos714BicliquePartition.edge_rep e
    obtain ⟨u',v',he'⟩ := Erdos714BicliquePartition.edge_rep e'
    have hv := congrArg Subtype.val hh
    change Sym2.map (blockCopy C L M z) e.val=Sym2.map (blockCopy C L M z') e'.val at hv
    rw [he,he'] at hv
    change s(Sum.inl (z.val.1.1,u.val),Sum.inr (z.val.1.2,v.val)) =
      s(Sum.inl (z'.val.1.1,u'.val),Sum.inr (z'.val.1.2,v'.val)) at hv
    simp only [Sym2.eq_iff,Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,false_and,or_false] at hv
    have hz : z=z' := by
      apply Subtype.ext
      apply Prod.ext
      · exact Prod.ext hv.1.1 hv.2.1
      · apply Prod.ext
        · exact u.property.symm.trans ((congrArg₂ (fun (st : S × T) (w : U) =>
            L st.1 st.2 w) (Prod.ext hv.1.1 hv.2.1) hv.1.2).trans u'.property)
        · exact v.property.symm.trans ((congrArg₂ (fun (st : S × T) (w : V) =>
            M st.1 st.2 w) (Prod.ext hv.1.1 hv.2.1) hv.2.2).trans v'.property)
    subst z'
    have hu : u=u' := Subtype.ext hv.1.2
    have hvv : v=v' := Subtype.ext hv.2.2
    have hee : e=e' := Subtype.ext (by rw [he,he',hu,hvv])
    subst e'
    rfl
  · intro e
    obtain ⟨s,u,t,v,he,hadj⟩ := separated_edge_rep C L M e
    let z : Block C L M := ⟨((s,t),(L s t u,M s t v)),hadj,⟨u,rfl⟩,⟨v,rfl⟩⟩
    let u' : LeftFiber C L M z := ⟨u,rfl⟩
    let v' : RightFiber C L M z := ⟨v,rfl⟩
    let e' : (completeBipartiteGraph (LeftFiber C L M z) (RightFiber C L M z)).edgeSet :=
      ⟨s(Sum.inl u',Sum.inr v'),by simp⟩
    refine ⟨⟨z,e'⟩,?_⟩
    apply Subtype.ext
    exact he.symm

/-- Arbitrary edge deletions cannot preserve positive density if every nonempty
fiber in both variables grows. -/
theorem separated_thinning (H : SimpleGraph ((S × U) ⊕ (T × V))) (t : ℕ)
    (hL : ∀ s t' a, (∃ u, L s t' u=a) → t ≤ Fintype.card {u : U // L s t' u=a})
    (hM : ∀ s t' a, (∃ v, M s t' v=a) → t ≤ Fintype.card {v : V // M s t' v=a})
    (hHG : H ≤ separatedGraph C L M)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    t*H.edgeFinset.card^4 ≤ 10368*(separatedGraph C L M).edgeFinset.card^4 := by
  apply Erdos714BicliquePartition.fourth_density_bound H (separatedGraph C L M)
    (blockCopy C L M) (block_partition C L M) t
    (fun z => hL _ _ _ z.property.2.1) (fun z => hM _ _ _ z.property.2.2) hHG hfree

end Separated

lemma pi_fiber_card_bound_coe (I : Ideal R) [Fintype I] [Fintype σ]
    (L : (σ → I) →+ I) (a : R) (ha : ∃ u, (L u : R) = a) (hd : 1 ≤ Fintype.card σ) :
    Fintype.card I ^ (Fintype.card σ-1) ≤ Fintype.card {u : σ → I // (L u : R) = a} := by
  obtain ⟨u₀,hu₀⟩ := ha
  have hh := pi_fiber_card_bound I L (L u₀) ⟨u₀,rfl⟩ hd
  have he : Fintype.card {u : σ → I // (L u : R) = a} =
      Fintype.card {u : σ → I // L u = L u₀} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun u => by rw [←hu₀]; exact Subtype.coe_inj))
  rw [he]
  exact hh

variable {S T : Type*}

/-- The actual polynomial relation on families of ideal cosets. -/
def cosetGraph (I : Ideal R) (P : MvPolynomial (σ ⊕ τ) R)
    (X : S → σ → R) (Y : T → τ → R) :
    SimpleGraph ((S × (σ → I)) ⊕ (T × (τ → I))) where
  Adj p q := match p, q with
    | .inl (s,u), .inr (t,v) => MvPolynomial.eval
        (Sum.elim (fun i => X s i+(u i : R)) (fun j => Y t j+(v j : R))) P=0
    | .inr (t,v), .inl (s,u) => MvPolynomial.eval
        (Sum.elim (fun i => X s i+(u i : R)) (fun j => Y t j+(v j : R))) P=0
    | _, _ => False
  symm := by intro p q; cases p <;> cases q <;> simp
  loopless := by intro p; cases p <;> simp

/-- Uniformly in the polynomial, base cosets, and arbitrary retained edge set,
square-zero directions force a vanishing density when their fibers grow. -/
theorem polynomial_thinning [Fintype R] [Fintype σ] [Fintype τ] [Fintype S] [Fintype T]
    (I : Ideal R) (hI : ∀ a b : I, (a : R)*(b : R)=0)
    (P : MvPolynomial (σ ⊕ τ) R) (X : S → σ → R) (Y : T → τ → R)
    (H : SimpleGraph ((S × (σ → I)) ⊕ (T × (τ → I))))
    (d : ℕ) (hσ : d+1 ≤ Fintype.card σ) (hτ : d+1 ≤ Fintype.card τ)
    (hHG : H ≤ cosetGraph I P X Y)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    (Fintype.card I)^d * H.edgeFinset.card^4 ≤ 10368*(cosetGraph I P X Y).edgeFinset.card^4 := by
  choose L M hLM using fun s t => split_affine I hI P (X s) (Y t)
  let C (s : S) (t : T) := MvPolynomial.eval (Sum.elim (X s) (Y t)) P
  let L' (s : S) (t : T) : (σ → I) →+ R := I.subtype.toAddMonoidHom.comp (L s t)
  let M' (s : S) (t : T) : (τ → I) →+ R := I.subtype.toAddMonoidHom.comp (M s t)
  have he : cosetGraph I P X Y = separatedGraph C L' M' := by
    ext p q
    cases p <;> cases q <;> simp only [cosetGraph,separatedGraph]
    · rw [hLM]; rfl
    · rw [hLM]; rfl
  have hL (s : S) (t : T) (a : R) (ha : ∃ u, L' s t u=a) :
      Fintype.card I^d ≤ Fintype.card {u : σ → I // L' s t u=a} := by
    have hb := pi_fiber_card_bound_coe I (L s t) a ha (by omega)
    exact (Nat.pow_le_pow_right Fintype.card_pos (by omega : d ≤ Fintype.card σ-1)).trans hb
  have hM (s : S) (t : T) (a : R) (ha : ∃ u, M' s t u=a) :
      Fintype.card I^d ≤ Fintype.card {u : τ → I // M' s t u=a} := by
    have hb := pi_fiber_card_bound_coe I (M s t) a ha (by omega)
    exact (Nat.pow_le_pow_right Fintype.card_pos (by omega : d ≤ Fintype.card τ-1)).trans hb
  have hh := separated_thinning C L' M' H (Fintype.card I^d) hL hM (he ▸ hHG) hfree
  simpa only [he,edgeFinset_card,Fintype.card_eq_nat_card] using hh


noncomputable def representative (I : Ideal R) (a : R ⧸ I) : R :=
  Classical.choose (Ideal.Quotient.mk_surjective (I := I) a)

@[simp] lemma mk_representative (I : Ideal R) (a : R ⧸ I) :
    Ideal.Quotient.mk I (representative I a)=a :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (I := I) a)

/-- An exact choice of coordinates on ideal cosets; no duplicate vertices. -/
def cosetEquiv (I : Ideal R) : ((R ⧸ I) × I) ≃ R :=
  Equiv.ofBijective (fun p => representative I p.1+(p.2 : R)) (by
    constructor
    · rintro ⟨a,u⟩ ⟨b,v⟩ h
      have hab : a=b := by
        have hh := congrArg (Ideal.Quotient.mk I) h
        simpa only [map_add,mk_representative,
          (Ideal.Quotient.eq_zero_iff_mem.mpr u.property),
          (Ideal.Quotient.eq_zero_iff_mem.mpr v.property),add_zero] using hh
      subst b
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h))
    · intro x
      let a := Ideal.Quotient.mk I x
      have hm : x-representative I a ∈ I := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simp [a]
      exact ⟨(a,⟨x-representative I a,hm⟩),by simp⟩)

def vectorCosetEquiv (I : Ideal R) : ((σ → R ⧸ I) × (σ → I)) ≃ (σ → R) :=
  Equiv.ofBijective (fun p i => cosetEquiv I (p.1 i,p.2 i)) (by
    constructor
    · intro p q h
      have hh (i : σ) := (cosetEquiv I).injective (congrFun h i)
      exact Prod.ext (funext (fun i => (Prod.mk.inj (hh i)).1))
        (funext (fun i => (Prod.mk.inj (hh i)).2))
    · intro f
      exact ⟨((fun i => ((cosetEquiv I).symm (f i)).1),
        (fun i => ((cosetEquiv I).symm (f i)).2)),by ext i; simp⟩)

/-- The polynomial incidence graph on all ring-valued vectors. -/
def polynomialGraph (P : MvPolynomial (σ ⊕ τ) R) : SimpleGraph ((σ → R) ⊕ (τ → R)) where
  Adj p q := match p, q with
    | .inl x, .inr y => MvPolynomial.eval (Sum.elim x y) P=0
    | .inr y, .inl x => MvPolynomial.eval (Sum.elim x y) P=0
    | _, _ => False
  symm := by intro p q; cases p <;> cases q <;> simp
  loopless := by intro p; cases p <;> simp

def polynomialCosetIso (I : Ideal R) (P : MvPolynomial (σ ⊕ τ) R) :
    cosetGraph I P (fun (x : σ → R ⧸ I) i => representative I (x i)) (fun (y : τ → R ⧸ I) j => representative I (y j)) ≃g
      polynomialGraph P where
  toEquiv := (vectorCosetEquiv (σ := σ) I).sumCongr (vectorCosetEquiv (σ := τ) I)
  map_rel_iff' := by intro p q; cases p <;> cases q <;> rfl

/-- The square-zero thinning obstruction on the full polynomial graph, rather
than only its parametrized or residue-restricted version. -/
theorem full_polynomial_thinning [Fintype R] [Fintype σ] [Fintype τ]
    (I : Ideal R) (hI : ∀ a b : I, (a : R)*(b : R)=0)
    (P : MvPolynomial (σ ⊕ τ) R) (H : SimpleGraph ((σ → R) ⊕ (τ → R)))
    (d : ℕ) (hσ : d+1 ≤ Fintype.card σ) (hτ : d+1 ≤ Fintype.card τ)
    (hHG : H ≤ polynomialGraph P)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    (Fintype.card I)^d * H.edgeFinset.card^4 ≤ 10368*(polynomialGraph P).edgeFinset.card^4 := by
  let e := polynomialCosetIso I P
  let H' := H.comap e.toEquiv.toEmbedding
  have hle : H' ≤ cosetGraph I P
      (fun (x : σ → R ⧸ I) i => representative I (x i)) (fun (y : τ → R ⧸ I) j => representative I (y j)) := by
    intro p q hpq
    exact e.map_rel_iff.mp (hHG hpq)
  have hf := Erdos714GraphAveraging.free_comap _ H e.toEquiv.toEmbedding hfree
  have hh := polynomial_thinning I hI P
    (fun (x : σ → R ⧸ I) i => representative I (x i)) (fun (y : τ → R ⧸ I) j => representative I (y j))
    H' d hσ hτ hle hf
  have heH := (SimpleGraph.Iso.comap e.toEquiv H).card_edgeFinset_eq
  have heG := e.card_edgeFinset_eq
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hh heH heG ⊢
  rw [heH,heG] at hh
  exact hh

end Erdos714SquareZero
#print axioms Erdos714SquareZero.affine_on_coset
#print axioms Erdos714SquareZero.block_partition
#print axioms Erdos714SquareZero.polynomial_thinning
#print axioms Erdos714SquareZero.full_polynomial_thinning
