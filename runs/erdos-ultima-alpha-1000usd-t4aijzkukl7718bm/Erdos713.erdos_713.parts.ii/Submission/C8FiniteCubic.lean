import FormalConjecturesUtil
import Submission.C8FiniteQuadratic

/-! Cubic-potential octagons in characteristic two. This is an auxiliary
construction obstruction, not a disproof of Erdos 713. -/
open SimpleGraph
namespace Erdos713C8FiniteCubic
open Erdos713C8FiniteQuadratic
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

def moment (u v r t : K) (Q : K → K → K) : K :=
  Q 0 0*((1-v)*r-(1-u)*t) + Q u (u*((1-v)*r-(1-u)*t))*t +
    Q 1 ((1-v)*r)*(v*r-u*t) - Q v 0*r

lemma octagon_of_moment (Q : K → K → K) (u v r t : K)
    (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hr : r ≠ 0) (ht : t ≠ 0)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) (hM : moment u v r t Q = 0) :
    Octagon Q := by
  dsimp [moment] at hM
  let s := (1-v)*r-(1-u)*t
  have hs : s ≠ 0 := by
    intro he
    have hprod : t^2*(1-u)*(v-u) = 0 := by
      dsimp [s] at he
      linear_combination (1-v)*hB-v*((1-v)*r+(1-u)*t)*he
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht) (sub_ne_zero.mpr hu1.symm))
      (sub_ne_zero.mpr huv.symm)) hprod
  have hs2 : v*r-u*t ≠ 0 := by
    intro he
    have hprod : t^2*u*(u-v) = 0 := by
      linear_combination v*hB-(1-v)*(v*r+u*t)*he
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht) hu) (sub_ne_zero.mpr huv)) hprod
  have hut : u*t ≠ 0 := mul_ne_zero hu ht
  have hvr : v*r ≠ 0 := mul_ne_zero hv hr
  let p : Fin 4 → Vertex K :=
    ![(0,![0,0,0]), (s,![0,0,Q 0 0*s]),
      (s+t,![u*t,u*s*t,Q 0 0*s+Q u (u*s)*t]), (r,![v*r,0,Q v 0*r])]
  let l : Fin 4 → Vertex K :=
    ![(0,![0,0,0]), (u,![u*s,u*s^2,Q u (u*s)*s-Q 0 0*s]),
      (1,![(1-v)*r,(1-v)*r*(s+t)-u*s*t,Q 1 ((1-v)*r)*(s+t)-Q 0 0*s-Q u (u*s)*t]),
      (v,![0,0,0])]
  refine ⟨p,l,?_,?_,?_,?_⟩
  · intro i j hij
    have hx := congrArg (fun w : Vertex K => w.1) hij
    have hy := congrArg (fun w : Vertex K => w.2 0) hij
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [p] at hx hy
      first | exact (hs hx).elim | exact (hs hx.symm).elim |
        exact (hr hx).elim | exact (hr hx.symm).elim |
        exact (hut hy).elim | exact (hut hy.symm).elim |
        exact (hvr hy).elim | exact (hvr hy.symm).elim |
        (exfalso; apply ht; linear_combination hx) |
        (exfalso; apply ht; linear_combination -hx) |
        (exfalso; apply hs2; dsimp [s] at hx; linear_combination hx) |
        (exfalso; apply hs2; dsimp [s] at hx; linear_combination -hx))
  · intro i j hij
    have hx := congrArg (fun w : Vertex K => w.1) hij
    fin_cases i <;> fin_cases j <;> dsimp [l] at hx <;> simp_all
  · intro i
    fin_cases i <;> dsimp [Inc,p,l,s]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals ring
  · intro i
    fin_cases i <;> dsimp [Inc,p,l,s]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals solve | ring | linear_combination hB | linear_combination -hB | linear_combination hM | linear_combination -hM

def pointOffset (a b : K) (p : Vertex K) : Vertex K :=
  (p.1,![p.2 0+a*p.1-b,p.2 1+b*p.1,p.2 2])
def lineOffset (a b : K) (p : Vertex K) : Vertex K :=
  (p.1+a,![p.2 0+b,p.2 1,p.2 2])

lemma pointOffset_injective (a b : K) : Function.Injective (pointOffset a b) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have h0 := congrArg (fun p : Vertex K => p.2 0) h
  have h1 := congrArg (fun p : Vertex K => p.2 1) h
  have h2 := congrArg (fun p : Vertex K => p.2 2) h
  dsimp [pointOffset] at hx h0 h1 h2
  refine Prod.ext hx ?_
  funext i
  fin_cases i
  · change p.2 0 = q.2 0
    linear_combination h0-a*hx
  · change p.2 1 = q.2 1
    linear_combination h1-b*hx
  · exact h2

lemma lineOffset_injective (a b : K) : Function.Injective (lineOffset a b) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have h0 := congrArg (fun p : Vertex K => p.2 0) h
  have h1 := congrArg (fun p : Vertex K => p.2 1) h
  have h2 := congrArg (fun p : Vertex K => p.2 2) h
  dsimp [lineOffset] at hx h0 h1 h2
  refine Prod.ext (add_right_cancel hx) ?_
  funext i
  fin_cases i
  · exact add_right_cancel h0
  · exact h1
  · exact h2

lemma offset_inc (Q : K → K → K) (a b : K) {p l : Vertex K}
    (h : Inc (fun x y => Q (x+a) (y+b)) p l) :
    Inc Q (pointOffset a b p) (lineOffset a b l) := by
  obtain ⟨h0,h1,h2⟩ := h
  dsimp [Inc,pointOffset,lineOffset]
  refine ⟨?_,?_,h2⟩
  · linear_combination h0
  · linear_combination h1

lemma offset_octagon (Q : K → K → K) (a b : K)
    (h : Octagon (fun x y => Q (x+a) (y+b))) : Octagon Q := by
  obtain ⟨p,l,hp,hl,h1,h2⟩ := h
  exact ⟨pointOffset a b ∘ p,lineOffset a b ∘ l,
    (pointOffset_injective a b).comp hp,(lineOffset_injective a b).comp hl,
    fun i => offset_inc Q a b (h1 i),fun i => offset_inc Q a b (h2 i)⟩

abbrev cubic (A B C D₀ E₀ F G H I J₀ : K) (a b : K) : K :=
  A*a^3+B*a^2*b+C*a*b^2+D₀*b^3+E₀*a^2+F*a*b+G*b^2+H*a+I*b+J₀

lemma cubic_add_left [CharP K 2] (A B C D₀ E₀ F G H I J₀ a b s : K) :
    cubic A B C D₀ E₀ F G H I J₀ (a+s) b =
      cubic A B C D₀ E₀ F G H I J₀ a b + s*(A*a^2+C*b^2) +
      A*s^2*a+(B*s^2+F*s)*b+(A*s^3+E₀*s^2+H*s) := by
  dsimp [cubic]
  linear_combination (A*s*a^2+A*s^2*a+B*s*a*b+E₀*s*a)*(CharTwo.two_eq_zero (R := K))

lemma cubic_add_right [CharP K 2] (A B C D₀ E₀ F G H I J₀ a b s : K) :
    cubic A B C D₀ E₀ F G H I J₀ a (b+s) =
      cubic A B C D₀ E₀ F G H I J₀ a b + s*(B*a^2+D₀*b^2) +
      (C*s^2+F*s)*a+D₀*s^2*b+(D₀*s^3+G*s^2+I*s) := by
  dsimp [cubic]
  linear_combination (C*a*b*s+D₀*b^2*s+D₀*b*s^2+G*b*s)*(CharTwo.two_eq_zero (R := K))

lemma moment_add_affine (u v r t s L M N : K) (Q R : K → K → K)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) :
    moment u v r t (fun a b => Q a b+s*R a b+L*a+M*b+N) =
      moment u v r t Q+s*moment u v r t R := by
  dsimp [moment]
  linear_combination M*hB

lemma moment_quadratic_shear [CharP K 2] (u v r t U W τ : K) :
    moment u v r t (fun a b => U*a^2+W*(b+τ*a)^2) =
      (U+W*τ^2)*D u v r t+W*J u v r t := by
  have he : moment u v r t (fun a b => U*a^2+W*(b+τ*a)^2) =
      (U+W*τ^2)*D u v r t+(2*W*τ)*E u v r t+W*J u v r t := by
    dsimp [moment,D,E,J]
    ring
  rw [he,CharTwo.two_eq_zero (R := K)]
  ring

lemma moment_cubic_left [CharP K 2] (A B C D₀ E₀ F G H I J₀ u v r t s τ : K)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) :
    moment u v r t (fun a b => cubic A B C D₀ E₀ F G H I J₀ (a+s) (b+τ*a)) =
      moment u v r t (fun a b => cubic A B C D₀ E₀ F G H I J₀ a (b+τ*a)) +
        s*((A+C*τ^2)*D u v r t+C*J u v r t) := by
  have he : (fun a b => cubic A B C D₀ E₀ F G H I J₀ (a+s) (b+τ*a)) =
      (fun a b => cubic A B C D₀ E₀ F G H I J₀ a (b+τ*a) +
        s*(A*a^2+C*(b+τ*a)^2)+(A*s^2+(B*s^2+F*s)*τ)*a+
        (B*s^2+F*s)*b+(A*s^3+E₀*s^2+H*s)) := by
    funext a b
    rw [cubic_add_left]
    ring
  rw [he,moment_add_affine _ _ _ _ _ _ _ _ _ _ hB,moment_quadratic_shear]

lemma moment_cubic_right [CharP K 2] (A B C D₀ E₀ F G H I J₀ u v r t s τ : K)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) :
    moment u v r t (fun a b => cubic A B C D₀ E₀ F G H I J₀ a (b+τ*a+s)) =
      moment u v r t (fun a b => cubic A B C D₀ E₀ F G H I J₀ a (b+τ*a)) +
        s*((B+D₀*τ^2)*D u v r t+D₀*J u v r t) := by
  have he : (fun a b => cubic A B C D₀ E₀ F G H I J₀ a (b+τ*a+s)) =
      (fun a b => cubic A B C D₀ E₀ F G H I J₀ a (b+τ*a) +
        s*(B*a^2+D₀*(b+τ*a)^2)+(C*s^2+F*s+D₀*s^2*τ)*a+
        (D₀*s^2)*b+(D₀*s^3+G*s^2+I*s)) := by
    funext a b
    rw [cubic_add_right]
    ring
  rw [he,moment_add_affine _ _ _ _ _ _ _ _ _ _ hB,moment_quadratic_shear]

lemma exists_nonzero_shift (U W d j : K) (hd : d ≠ 0) (h : U ≠ 0 ∨ W ≠ 0) :
    ∃ τ : K, (U+W*τ^2)*d+W*j ≠ 0 := by
  by_cases h0 : U*d+W*j ≠ 0
  · exact ⟨0,by simpa using h0⟩
  push_neg at h0
  refine ⟨1,?_⟩
  intro h1
  have hw : W*d=0 := by linear_combination h1-h0
  have hw0 : W=0 := (mul_eq_zero.mp hw).resolve_right hd
  have hu0 : U=0 := (mul_eq_zero.mp (by simpa [hw0] using h0)).resolve_right hd
  rcases h with h | h <;> contradiction

/-- Every cubic two-variable potential over a finite field of characteristic
 two with more than four elements has an actual octagon. -/
theorem cubic_octagon_char_two [Fintype K] [CharP K 2]
    (A B C D₀ E₀ F G H I J₀ : K) (hq : 4 < Fintype.card K) :
    Octagon (cubic A B C D₀ E₀ F G H I J₀) := by
  obtain ⟨u,v,r,t,hu,hv,hu1,hv1,huv,hr,ht,hB,hd,_⟩ := parameters_char_two (K := K) hq
  let Q := cubic A B C D₀ E₀ F G H I J₀
  by_cases hAC : A ≠ 0 ∨ C ≠ 0
  · obtain ⟨τ,hk⟩ := exists_nonzero_shift A C (D u v r t) (J u v r t) hd hAC
    let k := (A+C*τ^2)*D u v r t+C*J u v r t
    let M := moment u v r t (fun a b => Q a (b+τ*a))
    let s := -M/k
    have hm : moment u v r t (fun a b => Q (a+s) (b+τ*a)) = 0 := by
      rw [moment_cubic_left A B C D₀ E₀ F G H I J₀ u v r t s τ hB]
      change M+(-M/k)*k=0
      rw [div_mul_cancel₀ _ hk]
      ring
    have ho := octagon_of_moment (fun a b => Q (a+s) (b+τ*a))
      u v r t hu hv hu1 hv1 huv hr ht hB hm
    have hs : Octagon (fun a b => Q (a+s) b) := shift_octagon τ (fun _ _ => rfl) ho
    exact offset_octagon Q s 0 (by simpa only [add_zero] using hs)
  · by_cases hBD : B ≠ 0 ∨ D₀ ≠ 0
    · obtain ⟨τ,hk⟩ := exists_nonzero_shift B D₀ (D u v r t) (J u v r t) hd hBD
      let k := (B+D₀*τ^2)*D u v r t+D₀*J u v r t
      let M := moment u v r t (fun a b => Q a (b+τ*a))
      let s := -M/k
      have hm : moment u v r t (fun a b => Q a (b+τ*a+s)) = 0 := by
        rw [moment_cubic_right A B C D₀ E₀ F G H I J₀ u v r t s τ hB]
        change M+(-M/k)*k=0
        rw [div_mul_cancel₀ _ hk]
        ring
      have ho := octagon_of_moment (fun a b => Q a (b+τ*a+s))
        u v r t hu hv hu1 hv1 huv hr ht hB hm
      have hs : Octagon (fun a b => Q a (b+s)) := shift_octagon τ (fun _ _ => rfl) ho
      exact offset_octagon Q 0 s (by simpa only [add_zero] using hs)
    · push_neg at hAC hBD
      rcases hAC with ⟨rfl,rfl⟩
      rcases hBD with ⟨rfl,rfl⟩
      have he : cubic (0 : K) 0 0 0 E₀ F G H I J₀ =
          (fun a b => E₀*a^2+F*a*b+G*b^2+H*a+I*b+J₀) := by
        funext a b
        simp [cubic]
      rw [he]
      exact linear_octagon H I J₀ (homogeneous_quadratic_char_two E₀ F G hq)

theorem contains_cubic_char_two [Fintype K] [CharP K 2]
    (A B C D₀ E₀ F G H I J₀ : K) (hq : 4 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (cubic A B C D₀ E₀ F G H I J₀) :=
  contains_of_octagon (cubic_octagon_char_two A B C D₀ E₀ F G H I J₀ hq)

#print axioms octagon_of_moment
#print axioms offset_octagon
#print axioms cubic_octagon_char_two
#print axioms contains_cubic_char_two
end Erdos713C8FiniteCubic
