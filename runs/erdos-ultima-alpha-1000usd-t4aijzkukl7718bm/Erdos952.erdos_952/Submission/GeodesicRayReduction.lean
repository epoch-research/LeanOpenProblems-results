import Submission.GraphReduction

/-! A hypothetical prime ray can be chosen to be geodesic in its prime graph.
This does not bound its distance from a Euclidean line. -/
namespace Erdos952Investigation
namespace GeodesicRayReduction
set_option maxHeartbeats 0
universe u
variable {V : Type u} (G : SimpleGraph V) (v : V)

def Prefix (n : ℕ) :=
  {f : RayReduction.Prefix G v n // ∀ i, G.dist v (f.val i) = i.val}

def restrict {i j : ℕ} (hij : i ≤ j) (f : Prefix G v j) : Prefix G v i :=
  ⟨RayReduction.restrict G v hij f.val,fun k => f.property (Fin.castLE (Nat.succ_le_succ hij) k)⟩

lemma restrict_refl {i : ℕ} (f : Prefix G v i) : restrict G v le_rfl f = f := by
  apply Subtype.ext
  exact RayReduction.restrict_refl G v f.val

lemma restrict_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (f : Prefix G v k) :
    restrict G v hij (restrict G v hjk f) = restrict G v (hij.trans hjk) f := by
  apply Subtype.ext
  exact RayReduction.restrict_trans G v hij hjk f.val

instance : Subsingleton (Prefix G v 0) := inferInstanceAs (Subsingleton (Subtype _))

lemma finite_extension_fiber [G.LocallyFinite] (n : ℕ) (a : Prefix G v n) :
    {b : Prefix G v (n+1) | restrict G v (Nat.le_succ n) b = a}.Finite := by
  let T := {b : Prefix G v (n+1) // restrict G v (Nat.le_succ n) b = a}
  let U := {b : RayReduction.Prefix G v (n+1) //
    RayReduction.restrict G v (Nat.le_succ n) b = a.val}
  let f : T → U := fun b => ⟨b.val.val,congrArg Subtype.val b.property⟩
  have hfi : Function.Injective f := by
    intro b c h
    exact Subtype.ext (Subtype.ext (congrArg (fun t : U => t.val) h))
  have : Finite U := RayReduction.finite_extension_fiber G v n a.val
  exact Finite.of_injective f hfi

lemma prefixes_of_infinite_component [G.LocallyFinite]
    (hinf : {w | G.Reachable v w}.Infinite) (n : ℕ) : Nonempty (Prefix G v n) := by
  classical
  obtain ⟨w,hw,hwn⟩ := (hinf.diff (RayReduction.finite_walkBall G v n)).nonempty
  obtain ⟨p,hp⟩ := hw.exists_walk_length_eq_dist
  have hn : n < p.length := by
    by_contra! he
    exact hwn ⟨p,he⟩
  have hpath := p.isPath_of_length_eq_dist hp
  refine ⟨⟨⟨fun i => p.getVert i.val,by simp,?_,?_⟩,?_⟩⟩
  · intro i j he
    apply Fin.ext
    exact hpath.getVert_injOn (by change i.val ≤ p.length; omega)
      (by change j.val ≤ p.length; omega) he
  · intro i
    exact p.adj_getVert_succ (by omega)
  · intro i
    have hh := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i.val)
    have hi : i.val ≤ p.length := by omega
    simpa only [SimpleGraph.Walk.take_length,inf_eq_left.mpr hi] using hh.symm

lemma ray_of_prefixes [G.LocallyFinite] (h : ∀ n, Nonempty (Prefix G v n)) :
    ∃ x : ℕ → V, x 0 = v ∧ Function.Injective x ∧
      (∀ n, G.Adj (x n) (x (n+1))) ∧ ∀ n, G.dist v (x n) = n := by
  classical
  letI (n : ℕ) : Nonempty (Prefix G v n) := h n
  obtain ⟨f,hf⟩ := exists_seq_forall_proj_of_forall_finite
    (restrict G v) (fun {_} a => restrict_refl G v a)
    (fun {_ _ _} hij hjk a => restrict_trans G v hij hjk a) (finite_extension_fiber G v)
  let x : ℕ → V := fun n => (f n).val.val (Fin.last n)
  have hx {i j : ℕ} (hij : i ≤ j) : x i = (f j).val.val ⟨i,by omega⟩ :=
    (congrArg (fun p : Prefix G v i => p.val.val (Fin.last i)) (hf hij)).symm
  have hd (n : ℕ) : G.dist v (x n) = n := (f n).property (Fin.last n)
  refine ⟨x,(f 0).val.property.1,?_,?_,hd⟩
  · intro i j he
    simpa only [hd] using congrArg (G.dist v) he
  · intro n
    rw [hx (Nat.le_succ n),hx (le_refl (n+1))]
    exact (f (n+1)).val.property.2.2 (Fin.last n)

lemma segment_walk (x : ℕ → V) (ha : ∀ n, G.Adj (x n) (x (n+1))) (a n : ℕ) :
    ∃ p : G.Walk (x a) (x (a+n)), p.length = n := by
  induction n with
  | zero => exact ⟨SimpleGraph.Walk.nil,rfl⟩
  | succ n ih =>
    obtain ⟨p,hp⟩ := ih
    have hh : (p.concat (ha (a+n))).length = n+1 := by simp [hp]
    simpa only [Nat.add_assoc] using ⟨p.concat (ha (a+n)),hh⟩

lemma geodesic_of_dist_from_start (x : ℕ → V)
    (ha : ∀ n, G.Adj (x n) (x (n+1))) (hd : ∀ n, G.dist (x 0) (x n) = n) :
    ∀ i j, G.dist (x i) (x j) = Nat.dist i j := by
  have hle (i j : ℕ) (hij : i ≤ j) : G.dist (x i) (x j) = j-i := by
    obtain ⟨p,hp⟩ : ∃ p : G.Walk (x i) (x j), p.length = j-i := by
      have he : i+(j-i) = j := by omega
      have hseg := segment_walk G x ha i (j-i)
      rw [he] at hseg
      exact hseg
    have hu := SimpleGraph.dist_le p
    have hr : G.Reachable (x 0) (x i) := by
      obtain ⟨q,_⟩ := segment_walk G x ha 0 i
      simpa only [Nat.zero_add] using q.reachable
    have hl := hr.dist_triangle_left (x j)
    rw [hd i,hd j] at hl
    omega
  intro i j
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij]
    exact hle i j hij
  · rw [G.dist_comm,Nat.dist_eq_sub_of_le_right hji]
    exact hle j i hji

/-- König compactness can retain shortest-path distances, not merely
injectivity of the chosen ray. -/
theorem geodesic_ray_iff_infinite_component [G.LocallyFinite] :
    (∃ x : ℕ → V, x 0 = v ∧ Function.Injective x ∧
      (∀ n, G.Adj (x n) (x (n+1))) ∧
      ∀ i j, G.dist (x i) (x j) = Nat.dist i j) ↔
    {w | G.Reachable v w}.Infinite := by
  constructor
  · rintro ⟨x,hx0,hx,ha,_⟩
    exact (RayReduction.ray_iff_infinite_component G v).mp ⟨x,hx0,hx,ha⟩
  · intro h
    obtain ⟨x,hx0,hx,ha,hd⟩ := ray_of_prefixes G v (prefixes_of_infinite_component G v h)
    refine ⟨x,hx0,hx,ha,geodesic_of_dist_from_start G x ha ?_⟩
    simpa only [hx0] using hd

/-- The original conjecture is equivalent to existence of a prime-graph
geodesic ray. No assertion about Euclidean straightness is made. -/
theorem gaussian_moat_geodesic_equivalence :
    (∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) ↔
    ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      (∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) ∧
      ∀ i j, (primeGraph C).dist (x i) (x j) = Nat.dist i j := by
  constructor
  · intro h
    obtain ⟨C,v,hv⟩ := gaussian_moat_graph_equivalence.mp h
    obtain ⟨x,_,hx,ha,hd⟩ := (geodesic_ray_iff_infinite_component (primeGraph C) v).mpr hv
    exact ⟨x,C,hx,fun n => ⟨(ha n).1,(ha n).2.2.2⟩,hd⟩
  · rintro ⟨x,C,hx,hp,_⟩
    exact ⟨x,C,hx,hp⟩

#print axioms geodesic_ray_iff_infinite_component
#print axioms gaussian_moat_geodesic_equivalence
end GeodesicRayReduction
end Erdos952Investigation
