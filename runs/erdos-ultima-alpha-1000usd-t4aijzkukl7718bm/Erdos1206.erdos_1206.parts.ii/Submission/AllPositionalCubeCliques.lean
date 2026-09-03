import Submission.RationalCurveLocal
import Submission.RepeatedCubeDifferences

/-! Every fixed positional-pair graph has unbounded chromatic number. This
stronger coloring obstruction does not exclude ordinary cube-Sidon coloring. -/

namespace Erdos1206.AllPositionalCubeCliques
open scoped Classical
set_option maxHeartbeats 1000000

lemma pair_first_second {a b : ℚ} (ha : 0<a) (hab : a<b) :
    ∃ c d : ℚ, b<c ∧ c<d ∧ a^3+d^3=b^3+c^3 := by
  obtain ⟨d,c,hbc,hc,hd,he⟩ :=
    UnboundedCubeDifferences.unbounded_rational_difference ha hab b
  have hcd : c<d := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by
    have hp := (Odd.strictMono_pow (by decide : Odd 3)) hab
    linarith)
  exact ⟨c,d,hbc,hcd,by linarith⟩

lemma pair_first_third {a c : ℚ} (ha : 0<a) (hac : a<c) :
    ∃ b d : ℚ, a<b ∧ b<c ∧ c<d ∧ a^3+d^3=b^3+c^3 := by
  have hD : 0<c^3-a^3 := sub_pos.mpr ((Odd.strictMono_pow (by decide : Odd 3)) hac)
  have hbase : (-a)^3-(-c)^3=c^3-a^3 := by ring
  obtain ⟨x,y,hyL,hyU,hxL,hxU,he⟩ :=
    RationalCurveLocal.near_below_of_unbounded hD (neg_ne_zero.mpr ha.ne') hbase
      (sub_pos.mpr hac) (UnboundedCubeDifferences.unbounded_rational_difference ha hac)
  exact ⟨-x,-y,by linarith,by linarith,by linarith,by nlinarith⟩

lemma pair_first_fourth {a d : ℚ} (ha : 0<a) (had : a<d) :
    ∃ b c : ℚ, a<b ∧ b<c ∧ c<d ∧ a^3+d^3=b^3+c^3 := by
  have hd : 0<d := ha.trans had
  have hD : 0<d^3+a^3 := by positivity
  have hbase : d^3-(-a)^3=d^3+a^3 := by ring
  have hun (M : ℚ) : ∃ x y : ℚ, M<y ∧ 0<y ∧ 0<x ∧ x^3-y^3=d^3+a^3 := by
    simpa [add_comm] using RationalCurveLocal.sum_unbounded ha had M
  obtain ⟨x,y,hyL,hyU,hxL,hxU,he⟩ :=
    RationalCurveLocal.near_below_of_unbounded hD hd.ne' hbase
      (show 0<(d-a)/3 from div_pos (sub_pos.mpr had) (by norm_num)) hun
  exact ⟨-y,x,by linarith,by linarith,hxU,by nlinarith⟩

lemma pair_second_third {b c : ℚ} (hb : 0<b) (hbc : b<c) :
    ∃ a d : ℚ, 0<a ∧ a<b ∧ c<d ∧ a^3+d^3=b^3+c^3 := by
  have hc : 0<c := hb.trans hbc
  have hD : 0<b^3+c^3 := by positivity
  have hbase : b^3-(-c)^3=b^3+c^3 := by ring
  obtain ⟨x,y,hyL,hyU,hxL,hxU,he⟩ :=
    RationalCurveLocal.near_below_of_unbounded hD hb.ne' hbase
      (half_pos hb) (RationalCurveLocal.sum_unbounded hb hbc)
  exact ⟨x,-y,by linarith,hxU,by linarith,by nlinarith⟩

lemma pair_third_fourth {c d : ℚ} (hc : 0<c) (hcd : c<d) (hclose : d^3<2*c^3) :
    ∃ a b : ℚ, 0<a ∧ a<b ∧ b<c ∧ a^3+d^3=b^3+c^3 := by
  have hd : 0<d := hc.trans hcd
  let T := d^3+c^3
  have hT : 0<T := by dsimp [T]; positivity
  let a := d*(2*c^3-d^3)/T
  let b := c*(2*d^3-c^3)/T
  have hc3 := pow_pos hc 3
  have hd3 := pow_pos hd 3
  have hpow := (Odd.strictMono_pow (by decide : Odd 3)) hcd
  have ha : 0<a := by
    dsimp [a]
    exact div_pos (mul_pos hd (by linarith)) hT
  have hb : 0<b := by
    dsimp [b]
    exact div_pos (mul_pos hc (by linarith)) hT
  have he : b^3-a^3=d^3-c^3 := by
    dsimp [a,b]
    rw [div_pow,div_pow,← sub_div]
    apply (div_eq_iff (pow_ne_zero 3 hT.ne')).mpr
    dsimp [T]
    ring
  have hab : a<b := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by linarith)
  have hbc : b<c := by
    dsimp [b]
    apply (div_lt_iff₀ hT).mpr
    have hp := mul_pos hc (sub_pos.mpr hclose)
    dsimp [T]
    nlinarith
  exact ⟨a,b,ha,hab,hbc,by linarith⟩

/-- The common strict-collision predicate for natural or rational roots. -/
def StrictCollision {R : Type*} [OfNat R 0] [LT R] [Add R] [Pow R ℕ]
    (r : Fin 4 → R) : Prop :=
  0<r 0 ∧ r 0<r 1 ∧ r 1<r 2 ∧ r 2<r 3 ∧ (r 0)^3+(r 3)^3=(r 1)^3+(r 2)^3

/-- Each positional pair can be prescribed, provided the two values are
sufficiently close. Only the third/fourth pair needs the closeness assumption. -/
theorem rational_pair_extension (p q : Fin 4) (hpq : p<q)
    {u v : ℚ} (hu : 0<u) (huv : u<v) (hclose : v^3<2*u^3) :
    ∃ r : Fin 4 → ℚ, StrictCollision r ∧ r p=u ∧ r q=v := by
  fin_cases p <;> fin_cases q <;> try (norm_num at hpq)
  · obtain ⟨c,d,hbc,hcd,he⟩ := pair_first_second hu huv
    exact ⟨![u,v,c,d],⟨hu,huv,hbc,hcd,he⟩,rfl,rfl⟩
  · obtain ⟨b,d,hab,hbc,hcd,he⟩ := pair_first_third hu huv
    exact ⟨![u,b,v,d],⟨hu,hab,hbc,hcd,he⟩,rfl,rfl⟩
  · obtain ⟨b,c,hab,hbc,hcd,he⟩ := pair_first_fourth hu huv
    exact ⟨![u,b,c,v],⟨hu,hab,hbc,hcd,he⟩,rfl,rfl⟩
  · obtain ⟨a,d,ha,hab,hcd,he⟩ := pair_second_third hu huv
    exact ⟨![a,u,v,d],⟨ha,hab,huv,hcd,he⟩,rfl,rfl⟩
  · obtain ⟨a,c,ha,hab,hbc,hcd,he⟩ := LocalCubeDifferences.second_fourth_pair hu huv
    exact ⟨![a,u,c,v],⟨ha,hab,hbc,hcd,he⟩,rfl,rfl⟩
  · obtain ⟨a,b,ha,hab,hbc,he⟩ := pair_third_fourth hu huv hclose
    exact ⟨![a,b,u,v],⟨ha,hab,hbc,huv,he⟩,rfl,rfl⟩

#print axioms rational_pair_extension

/-- Each fixed-positional-pair graph has cliques of arbitrary finite size. -/
theorem positional_cliques (p q : Fin 4) (hpq : p<q) (k : ℕ) :
    ∃ D N : ℕ, 0<D ∧ 0<N ∧ ∀ i j : Fin k, i<j →
      ∃ r : Fin 4 → ℕ, StrictCollision r ∧ r p=D*(N+i.val) ∧ r q=D*(N+j.val) := by
  let N := 10*(k+1)
  have hN : 0<N := by dsimp [N]; omega
  have hsize (i : Fin k) :
      (10 : ℚ)*(k+1)≤(N : ℚ)+i.val ∧ (N : ℚ)+i.val≤11*(k+1) := by
    have hi : (i.val : ℚ)<k := by exact_mod_cast i.isLt
    have hi0 : (0 : ℚ) ≤ i.val := Nat.cast_nonneg _
    dsimp [N]
    push_cast
    constructor <;> linarith
  have hclose (i j : Fin k) : ((N : ℚ)+j.val)^3<2*((N : ℚ)+i.val)^3 := by
    have ht : (0 : ℚ)<(k : ℚ)+1 := by positivity
    have hmid : (11*((k : ℚ)+1))^3<2*(10*((k : ℚ)+1))^3 := by
      nlinarith [pow_pos ht 3]
    have hlo := pow_le_pow_left₀ (show (0 : ℚ)≤10*(k+1) by positivity) (hsize i).1 3
    have hhi := pow_le_pow_left₀ (show (0 : ℚ)≤(N : ℚ)+j.val by positivity) (hsize j).2 3
    linarith
  have hex (i j : Fin k) : ∃ r : Fin 4 → ℚ, (∀ t, 0<r t) ∧
      (i<j → StrictCollision r ∧ r p=(N : ℚ)+i.val ∧ r q=(N : ℚ)+j.val) := by
    by_cases hij : i<j
    · have hu : (0 : ℚ)<(N : ℚ)+i.val := by positivity
      have huv : (N : ℚ)+i.val<(N : ℚ)+j.val := by
        have hh : (i.val : ℚ)<j.val := by exact_mod_cast hij
        linarith
      obtain ⟨r,hr,hp,hq⟩ := rational_pair_extension p q hpq hu huv (hclose i j)
      refine ⟨r,?_,fun _ => ⟨hr,hp,hq⟩⟩
      intro t
      rcases hr with ⟨h₀,h₁,h₂,h₃,_⟩
      fin_cases t
      · exact h₀
      · exact h₀.trans h₁
      · exact (h₀.trans h₁).trans h₂
      · exact ((h₀.trans h₁).trans h₂).trans h₃
    · exact ⟨fun _ => 1,by norm_num,fun h => (hij h).elim⟩
  choose r hr hpair using hex
  let f : Fin k × Fin k × Fin 4 → ℚ := fun z => r z.1 z.2.1 z.2.2
  have hf : ∀ z, 0<f z := fun z => hr z.1 z.2.1 z.2.2
  obtain ⟨D,hD,t,ht,hcast⟩ := RepeatedCubeDifferences.common_positive_denominator f hf
  have hDQ : (0 : ℚ)<D := by exact_mod_cast hD
  refine ⟨D,N,hD,hN,?_⟩
  intro i j hij
  obtain ⟨hcol,hp,hq⟩ := hpair i j hij
  let R : Fin 4 → ℕ := fun s => t (i,j,s)
  have hR (s : Fin 4) : (R s : ℚ)=(D : ℚ)*r i j s := hcast (i,j,s)
  have hlt (s z : Fin 4) (h : r i j s<r i j z) : R s<R z := by
    have hh : (R s : ℚ)<R z := by rw [hR,hR]; exact mul_lt_mul_of_pos_left h hDQ
    exact_mod_cast hh
  have he : (R 0)^3+(R 3)^3=(R 1)^3+(R 2)^3 := by
    have hh : (R 0 : ℚ)^3+(R 3 : ℚ)^3=(R 1 : ℚ)^3+(R 2 : ℚ)^3 := by
      rw [hR,hR,hR,hR]
      linear_combination (D : ℚ)^3*hcol.2.2.2.2
    exact_mod_cast hh
  refine ⟨R,⟨ht _,hlt _ _ hcol.2.1,hlt _ _ hcol.2.2.1,hlt _ _ hcol.2.2.2.1,he⟩,?_,?_⟩
  · have hh : (R p : ℚ)=(D : ℚ)*(N+i.val) := by rw [hR,hp]
    exact_mod_cast hh
  · have hh : (R q : ℚ)=(D : ℚ)*(N+j.val) := by rw [hR,hq]
    exact_mod_cast hh

/-- Whatever pair of positions is fixed in advance, finite coloring cannot
always give different colors to that pair in every strict cubic collision. -/
theorem no_finite_fixed_position_coloring (p q : Fin 4) (hpq : p<q)
    (k : ℕ) (color : ℕ → Fin k) :
    ∃ r : Fin 4 → ℕ, StrictCollision r ∧ color (r p)=color (r q) := by
  obtain ⟨D,N,hD,hN,hpair⟩ := positional_cliques p q hpq (k+1)
  obtain ⟨i,j,hij,hcolor⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (k+1) => color (D*(N+i.val))) (by simp)
  rcases lt_or_gt_of_ne hij with h | h
  · obtain ⟨r,hr,hp,hq⟩ := hpair i j h
    exact ⟨r,hr,by rwa [hp,hq]⟩
  · obtain ⟨r,hr,hp,hq⟩ := hpair j i h
    exact ⟨r,hr,by rw [hp,hq]; exact hcolor.symm⟩

#print axioms positional_cliques
#print axioms no_finite_fixed_position_coloring
end Erdos1206.AllPositionalCubeCliques
