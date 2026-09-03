import Submission.QuadraticProfileThinning
import Submission.UnbalancedParabolas

/-!
Cubic routing of affine-plane fibers. Four rows in one fiber have at most
one common column, but arbitrary routing data still gives mixed-fiber
bicliques. Every K44-free edge thinning loses the critical density.
This is not a proof or disproof of Erdos714.
-/

noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714CubicRouting
variable {F U : Type*} [Field F]

abbrev Row (U F : Type*) := (U × F) × F
abbrev Coord (F : Type*) := (F × F) × F
abbrev Column (F : Type*) := Coord F × F

def code (H : U → F × F → F) (r : Row U F) (x : Coord F) : F :=
  r.1.2*x.2+r.1.2^2*x.1.1+r.1.2^3*x.1.2+H r.1.1 x.1-r.2

def On (H : U → F × F → F) (r : Row U F) (y : Column F) : Prop :=
  code H r y.1=y.2

/-- For fixed row and column fiber labels, two distinct rows have at most
one common column in that column fiber. -/
theorem local_pair_unique (H : U → F × F → F) (u : U) (v : F × F)
    (r s : F × F) (y z : F × F) (hrs : r ≠ s)
    (hry : On H ((u,r.1),r.2) ((v,y.1),y.2))
    (hrz : On H ((u,r.1),r.2) ((v,z.1),z.2))
    (hsy : On H ((u,s.1),s.2) ((v,y.1),y.2))
    (hsz : On H ((u,s.1),s.2) ((v,z.1),z.2)) : y=z := by
  dsimp [On,code] at hry hrz hsy hsz
  have ha : r.1 ≠ s.1 := by
    intro he
    apply hrs
    apply Prod.ext he
    rw [he] at hry
    linear_combination hsy-hry
  have hp : (r.1-s.1)*(y.1-z.1)=0 := by
    linear_combination hry-hrz-hsy+hsz
  have hy : y.1=z.1 := sub_eq_zero.mp
    ((mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr ha))
  apply Prod.ext hy
  rw [hy] at hry
  linear_combination hrz-hry

/-- Cubic interpolation really does fix the same-row-fiber problem, even
when the gluing data H are arbitrary. -/
theorem same_fiber_four_unique (H : U → F × F → F) (u : U)
    (r : Fin 4 ↪ F × F) (y z : Column F)
    (hy : ∀ i, On H ((u,(r i).1),(r i).2) y)
    (hz : ∀ i, On H ((u,(r i).1),(r i).2) z) : y=z := by
  have ha : Function.Injective (fun i => (r i).1) := by
    intro i j he
    change (r i).1=(r j).1 at he
    apply r.injective
    apply Prod.ext he
    have hi := hy i
    have hj := hy j
    dsimp [On,code] at hi hj
    rw [he] at hi
    linear_combination hj-hi
  let t : Fin 4 ↪ F := ⟨fun i => (r i).1,ha⟩
  have hp (i : Fin 4) :
      (y.1.1.2-z.1.1.2)*t i^3+(y.1.1.1-z.1.1.1)*t i^2+
      (y.1.2-z.1.2)*t i+(H u y.1.1-H u z.1.1-y.2+z.2)=0 := by
    have hi := hy i
    have hj := hz i
    dsimp [On,code] at hi hj
    dsimp [t]
    linear_combination hi-hj
  obtain ⟨ht,hs,hc,hd⟩ := Erdos714Parabolas.cubic_coefficients t _ _ _ _ hp
  have hv : y.1.1=z.1.1 := Prod.ext (sub_eq_zero.mp hs) (sub_eq_zero.mp ht)
  have hx : y.1=z.1 := Prod.ext hv (sub_eq_zero.mp hc)
  apply Prod.ext hx
  rw [hv] at hd
  linear_combination -hd

variable [Fintype F]

def graph (H : U → F × F → F) : SimpleGraph (Row U F ⊕ Column F) :=
  Erdos714Coding.graph (code H)

lemma adj_iff (H : U → F × F → F) (r : Row U F) (y : Column F) :
    (graph H).Adj (.inl r) (.inr y) ↔ On H r y := by
  rcases y with ⟨x,d⟩
  exact Erdos714Coding.mem_symbols (code H) r x d

/-- The mixed-fiber obstruction works at any prescribed slope a and
column-fiber label v, not just at the zero slope. -/
def mixedCopy (H : U → F × F → F) (u : Fin 4 ↪ U) (t : Fin 4 ↪ F)
    (a : F) (v : F × F) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph H) := by
  let L : Fin 4 ↪ Row U F := ⟨fun i =>
    ((u i,a),a^2*v.1+a^3*v.2+H (u i) v),by
      intro i j h
      exact u.injective (congrArg (fun r : Row U F => r.1.1) h)⟩
  let R : Fin 4 ↪ Column F := ⟨fun j => ((v,t j),a*t j),by
      intro i j h
      exact t.injective (congrArg (fun y : Column F => y.1.2) h)⟩
  have he (i j : Fin 4) : (graph H).Adj (.inl (L i)) (.inr (R j)) := by
    rw [adj_iff]
    dsimp [On,code,L,R]
    ring
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at hxy
    | inr j => exact he i j
  | inr j =>
    cases y with
    | inr i => simp at hxy
    | inl i => exact (he i j).symm

variable [Fintype U]

theorem not_free (H : U → F × F → F) (hu : 4 ≤ Fintype.card U)
    (hq : 4 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph H) := by
  obtain ⟨u⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 4) (β := U) (by simpa using hu)
  obtain ⟨t⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 4) (β := F) (by simpa using hq)
  exact fun hf => hf ⟨mixedCopy H u t 1 (0,0)⟩

theorem edge_count (H : U → F × F → F) :
    (graph H).edgeFinset.card=Fintype.card U*Fintype.card F^5 := by
  rw [graph,Erdos714Coding.edge_count]
  simp only [Row,Coord,Fintype.card_prod]
  ring

theorem balanced_edge_count (H : (F × F) → F × F → F) :
    (graph H).edgeFinset.card=Fintype.card F^7 := by
  rw [edge_count]
  simp only [Fintype.card_prod]
  ring

omit [Field F] in
theorem balanced_vertex_count :
    Fintype.card (Row (F × F) F ⊕ Column F)=2*Fintype.card F^4 := by
  simp only [Row,Column,Coord,Fintype.card_sum,Fintype.card_prod]
  ring

/-- Arbitrary H, and arbitrary edge thinning: no algebraic degree bound on
H is assumed. The remaining free c coordinate has an affine profile. -/
theorem thinning_bound (H : U → F × F → F)
    (G : SimpleGraph (Row U F ⊕ Column F)) (hG : G ≤ graph H)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free G)
    (hu : Fintype.card U ≤ Fintype.card F^2) :
    G.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  apply Erdos714QuadraticProfileThinning.fourth_power_bound (code H)
    (fun v r => r.1.2^2*v.1+r.1.2^3*v.2+H r.1.1 v-r.2)
    (fun _ r => r.1.2) (fun _ _ => 0) _ G hG hf _ _
  · intro r v c
    dsimp [code]
    ring
  · simp [pow_two]
  · simp only [Row,Fintype.card_prod]
    calc
      Fintype.card U*Fintype.card F*Fintype.card F ≤
          Fintype.card F^2*Fintype.card F*Fintype.card F := by gcongr
      _ = Fintype.card F^4 := by ring

theorem size_budget (H : U → F × F → F)
    (G : SimpleGraph (Row U F ⊕ Column F)) (hG : G ≤ graph H)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free G)
    (hu : Fintype.card U ≤ Fintype.card F^2)
    (K : ℕ) (hdense : Fintype.card F^7 ≤ K*G.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have he := thinning_bound H G hG hf hu
  have hh : Fintype.card F^27*Fintype.card F ≤
      Fintype.card F^27*(165888*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*G.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*G.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(165888*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos Fintype.card_pos 27)

end Erdos714CubicRouting

#print axioms Erdos714CubicRouting.local_pair_unique
#print axioms Erdos714CubicRouting.same_fiber_four_unique
#print axioms Erdos714CubicRouting.mixedCopy
#print axioms Erdos714CubicRouting.not_free
#print axioms Erdos714CubicRouting.balanced_edge_count
#print axioms Erdos714CubicRouting.balanced_vertex_count
#print axioms Erdos714CubicRouting.thinning_bound
#print axioms Erdos714CubicRouting.size_budget
