import Submission.Investigation

/-! The locally finite graph reduction for the Gaussian moat question. -/

namespace Erdos952Investigation
namespace RayReduction

universe u
variable {V : Type u} (G : SimpleGraph V) (v : V)

def Prefix (n : ℕ) :=
  {f : Fin (n + 1) → V // f 0 = v ∧ Function.Injective f ∧
    ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ)}

def restrict {i j : ℕ} (hij : i ≤ j) (f : Prefix G v j) : Prefix G v i :=
  ⟨fun k => f.val (Fin.castLE (Nat.succ_le_succ hij) k), f.property.1,
    f.property.2.1.comp (Fin.castLE_injective _),
    fun k => f.property.2.2 ⟨k.val, lt_of_lt_of_le k.isLt hij⟩⟩

lemma restrict_refl {i : ℕ} (f : Prefix G v i) : restrict G v le_rfl f = f := by
  apply Subtype.ext
  funext k
  rfl

lemma restrict_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (f : Prefix G v k) :
    restrict G v hij (restrict G v hjk f) = restrict G v (hij.trans hjk) f := by
  apply Subtype.ext
  funext k
  rfl

instance : Subsingleton (Prefix G v 0) where
  allEq f g := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact f.property.1.trans g.property.1.symm

lemma prefix_ext {n : ℕ} {f g : Prefix G v (n + 1)}
    (hp : restrict G v (Nat.le_succ n) f = restrict G v (Nat.le_succ n) g)
    (hl : f.val (Fin.last (n + 1)) = g.val (Fin.last (n + 1))) : f = g := by
  apply Subtype.ext
  funext i
  refine Fin.lastCases hl (fun j => ?_) i
  exact congrArg (fun a : Prefix G v n => a.val j) hp

lemma finite_extension_fiber [G.LocallyFinite] (n : ℕ) (a : Prefix G v n) :
    {b : Prefix G v (n + 1) | restrict G v (Nat.le_succ n) b = a}.Finite := by
  let T := {b : Prefix G v (n + 1) // restrict G v (Nat.le_succ n) b = a}
  let f : T → G.neighborSet (a.val (Fin.last n)) := fun b =>
    ⟨b.val.val (Fin.last (n + 1)), by
      have heq : (restrict G v (Nat.le_succ n) b.val).val (Fin.last n) =
          a.val (Fin.last n) := congrArg (fun p : Prefix G v n => p.val (Fin.last n)) b.property
      have hadj := b.val.property.2.2 (Fin.last n)
      change G.Adj (a.val (Fin.last n)) (b.val.val (Fin.last (n + 1)))
      rw [← heq]
      exact hadj⟩
  have hinj : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    apply prefix_ext G v (b.property.trans c.property.symm)
    exact congrArg Subtype.val hbc
  have : Finite T := Finite.of_injective f hinj
  exact this

lemma ray_of_prefixes [G.LocallyFinite] (h : ∀ n, Nonempty (Prefix G v n)) :
    ∃ x : ℕ → V, x 0 = v ∧ Function.Injective x ∧ ∀ n, G.Adj (x n) (x (n + 1)) := by
  classical
  letI (n : ℕ) : Nonempty (Prefix G v n) := h n
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite
    (restrict G v) (fun {_} a => restrict_refl G v a)
    (fun {_ _ _} hij hjk a => restrict_trans G v hij hjk a) (finite_extension_fiber G v)
  let x : ℕ → V := fun n => (f n).val (Fin.last n)
  have hx {i j : ℕ} (hij : i ≤ j) :
      x i = (f j).val ⟨i, by omega⟩ :=
    (congrArg (fun p : Prefix G v i => p.val (Fin.last i)) (hf hij)).symm
  refine ⟨x, (f 0).property.1, ?_, ?_⟩
  · intro i j hij
    rw [hx (Nat.le_add_right i j), hx (Nat.le_add_left j i)] at hij
    exact congrArg Fin.val ((f (i + j)).property.2.1 hij)
  · intro n
    rw [hx (Nat.le_succ n), hx (le_refl (n + 1))]
    exact (f (n + 1)).property.2.2 (Fin.last n)

def walkBall (n : ℕ) : Set V := {w | ∃ p : G.Walk v w, p.length ≤ n}

lemma finite_walkBall [G.LocallyFinite] (n : ℕ) : (walkBall G v n).Finite := by
  induction n generalizing v with
  | zero =>
    apply (Set.finite_singleton v).subset
    rintro w ⟨p, hp⟩
    exact (p.eq_of_length_eq_zero (by omega)).symm
  | succ n ih =>
    have hfinite : ({v} ∪ ⋃ w ∈ G.neighborSet v, walkBall G w n).Finite :=
      (Set.finite_singleton v).union
        ((Set.toFinite (G.neighborSet v)).biUnion fun w _ => ih w)
    apply hfinite.subset
    rintro w ⟨p, hp⟩
    cases p with
    | nil => exact Or.inl rfl
    | cons hadj p =>
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨_, Set.mem_iUnion.mpr ⟨hadj, p, ?_⟩⟩
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega

lemma prefixes_of_infinite_component [G.LocallyFinite]
    (hinf : {w | G.Reachable v w}.Infinite) (n : ℕ) : Nonempty (Prefix G v n) := by
  classical
  obtain ⟨w, hw, hwn⟩ := (hinf.diff (finite_walkBall G v n)).nonempty
  obtain ⟨p, hp⟩ := hw.exists_isPath
  have hn : n < p.length := by
    by_contra h
    exact hwn ⟨p, by omega⟩
  refine ⟨⟨fun i => p.getVert i.val, ?_, ?_, ?_⟩⟩
  · simp
  · intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (by change i.val ≤ p.length; omega)
      (by change j.val ≤ p.length; omega) hij
  · intro i
    exact p.adj_getVert_succ (by omega)

lemma ray_iff_infinite_component [G.LocallyFinite] :
    (∃ x : ℕ → V, x 0 = v ∧ Function.Injective x ∧ ∀ n, G.Adj (x n) (x (n + 1))) ↔
      {w | G.Reachable v w}.Infinite := by
  constructor
  · rintro ⟨x, hx0, hx, ha⟩
    have hr (n : ℕ) : G.Reachable v (x n) := by
      induction n with
      | zero => rw [hx0]
      | succ n ih => exact ih.trans (ha n).reachable
    apply (Set.infinite_range_of_injective hx).mono
    rintro w ⟨n, rfl⟩
    exact hr n
  · intro h
    exact ray_of_prefixes G v (prefixes_of_infinite_component G v h)

#print axioms finite_walkBall
#print axioms ray_iff_infinite_component

#print axioms ray_of_prefixes

end RayReduction

lemma norm_sub_comm (z w : GaussianInt) : (z - w).norm = (w - z).norm := by
  rw [← Zsqrtd.norm_neg (w - z), neg_sub]

def primeGraph (C : ℤ) : SimpleGraph GaussianInt where
  Adj z w := Prime z ∧ Prime w ∧ z ≠ w ∧ (w - z).norm < C
  symm := by
    intro z w h
    exact ⟨h.2.1, h.1, h.2.2.1.symm, by rw [norm_sub_comm]; exact h.2.2.2⟩
  loopless := by
    intro z h
    exact h.2.2.1 rfl

lemma primeGraph_finite_neighbors (C : ℤ) (z : GaussianInt) :
    ((primeGraph C).neighborSet z).Finite := by
  have hinj : Function.Injective (fun w : GaussianInt => w - z) := by
    intro w v h
    simpa using h
  apply ((norm_sublevel_finite C).preimage (f := fun w => w - z) hinj.injOn).subset
  intro w hw
  exact le_of_lt hw.2.2.2

noncomputable instance (C : ℤ) : (primeGraph C).LocallyFinite :=
  fun z => (primeGraph_finite_neighbors C z).fintype

lemma gaussian_moat_graph_equivalence :
    (∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) ↔
    ∃ (C : ℤ) (z : GaussianInt), {w | (primeGraph C).Reachable z w}.Infinite := by
  constructor
  · rintro ⟨x, C, hx, h⟩
    refine ⟨C, x 0, (RayReduction.ray_iff_infinite_component (primeGraph C) (x 0)).mp ?_⟩
    refine ⟨x, rfl, hx, ?_⟩
    intro n
    refine ⟨(h n).1, (h (n + 1)).1, ?_, (h n).2⟩
    intro heq
    have := hx heq
    omega
  · rintro ⟨C, z, h⟩
    obtain ⟨x, _, hx, ha⟩ := (RayReduction.ray_iff_infinite_component (primeGraph C) z).mpr h
    exact ⟨x, C, hx, fun n => ⟨(ha n).1, (ha n).2.2.2⟩⟩

lemma gaussian_moat_negation_equivalence :
    (¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) ↔
    ∀ (C : ℤ) (z : GaussianInt), {w | (primeGraph C).Reachable z w}.Finite := by
  rw [gaussian_moat_graph_equivalence]
  simp

#print axioms gaussian_moat_graph_equivalence
#print axioms gaussian_moat_negation_equivalence

end Erdos952Investigation
