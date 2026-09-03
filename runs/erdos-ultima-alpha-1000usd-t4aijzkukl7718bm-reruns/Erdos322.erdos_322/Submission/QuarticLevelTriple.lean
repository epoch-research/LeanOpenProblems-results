import FormalConjecturesUtil

/-! Three collinear points on a strictly convex fourth-power level cannot all
be distinct. -/
namespace Erdos322Research.QuarticLevelTriple
noncomputable section
open Finset
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

def fourthNorm (x : Fin 4 → ℝ) : ℝ := ∑ i, x i^4

theorem strictConvex : StrictConvexOn ℝ Set.univ fourthNorm := by
  have hp := Even.strictConvexOn_pow (by decide : Even 4) (by decide : 4≠0)
  refine ⟨convex_univ,?_⟩
  intro x _ y _ hxy s t hs ht hsum
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hxy
  have hle (i : Fin 4) := hp.convexOn.2 (Set.mem_univ (x i)) (Set.mem_univ (y i)) hs.le ht.le hsum
  have hlt := hp.2 (Set.mem_univ (x j)) (Set.mem_univ (y j)) hj hs ht hsum
  change ∑ i, (s*x i+t*y i)^4 < s*(∑ i, x i^4)+t*(∑ i, y i^4)
  calc
    _ < ∑ i, (s*x i^4+t*y i^4) := sum_lt_sum (fun i _ ↦ hle i) ⟨j,mem_univ j,hlt⟩
    _ = _ := by rw [sum_add_distrib,← mul_sum,← mul_sum]

private theorem positive_pair (u v w : Fin 4 → ℝ) (C a b c : ℝ)
    (hu : fourthNorm u=C) (hv : fourthNorm v=C) (hw : fourthNorm w=C)
    (ha : 0<a) (hb : 0<b) (hsum : a+b+c=0)
    (hrel : ∀ i, a*u i+b*v i+c*w i=0) : u=v := by
  by_contra hne
  have hab : 0<a+b := add_pos ha hb
  have hweights : a/(a+b)+b/(a+b)=1 := by field_simp
  have heq : (a/(a+b)) • u+(b/(a+b)) • v=w := by
    funext i
    dsimp
    have hh := hrel i
    have hc : c=-(a+b) := by linarith
    rw [hc] at hh
    calc
      a/(a+b)*u i+b/(a+b)*v i = (a*u i+b*v i)/(a+b) := by ring
      _ = w i := (div_eq_iff hab.ne').mpr (by nlinarith only [hh])
  have hh := strictConvex.2 (Set.mem_univ u) (Set.mem_univ v) hne
    (div_pos ha hab) (div_pos hb hab) hweights
  rw [heq,hu,hv,hw] at hh
  simp only [smul_eq_mul] at hh
  rw [← add_mul,hweights,one_mul] at hh
  exact lt_irrefl _ hh

/-- A nontrivial affine dependence among three points of one fourth-power
level forces two points to coincide. -/
theorem equal_pair (u : Fin 3 → Fin 4 → ℝ) (C : ℝ) (a b c : ℝ)
    (hu : ∀ j, fourthNorm (u j)=C) (hn : a≠0 ∨ b≠0 ∨ c≠0)
    (hs : a+b+c=0) (hr : ∀ i, a*u 0 i+b*u 1 i+c*u 2 i=0) :
    u 0=u 1 ∨ u 0=u 2 ∨ u 1=u 2 := by
  by_cases ha : a=0
  · have hb : b≠0 := by rcases hn with hn|hn|hn; contradiction; assumption; intro hz; rw [ha,hz] at hs; norm_num at hs; contradiction
    right; right
    funext i
    have hh := hr i
    rw [ha] at hh hs
    have hc : c=-b := by linarith
    have hm : b*(u 1 i-u 2 i)=0 := by rw [hc] at hh; nlinarith only [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hb)
  by_cases hb : b=0
  · right; left
    funext i
    have hh := hr i
    rw [hb] at hh hs
    have hc : c=-a := by linarith
    have hm : a*(u 0 i-u 2 i)=0 := by rw [hc] at hh; nlinarith only [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left ha)
  by_cases hc : c=0
  · left
    funext i
    have hh := hr i
    rw [hc] at hh hs
    have hb' : b=-a := by linarith
    have hm : a*(u 0 i-u 1 i)=0 := by rw [hb'] at hh; nlinarith only [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left ha)
  rcases lt_or_gt_of_ne ha with ha|ha <;>
    rcases lt_or_gt_of_ne hb with hb|hb <;>
    rcases lt_or_gt_of_ne hc with hc|hc
  · linarith
  · left
    exact positive_pair (u 0) (u 1) (u 2) C (-a) (-b) (-c) (hu 0) (hu 1) (hu 2)
      (by linarith) (by linarith) (by linarith) (fun i ↦ by have := hr i; linarith)
  · right; left
    exact positive_pair (u 0) (u 2) (u 1) C (-a) (-c) (-b) (hu 0) (hu 2) (hu 1)
      (by linarith) (by linarith) (by linarith) (fun i ↦ by have := hr i; linarith)
  · right; right
    exact positive_pair (u 1) (u 2) (u 0) C b c a (hu 1) (hu 2) (hu 0)
      hb hc (by linarith) (fun i ↦ by have := hr i; linarith)
  · right; right
    exact positive_pair (u 1) (u 2) (u 0) C (-b) (-c) (-a) (hu 1) (hu 2) (hu 0)
      (by linarith) (by linarith) (by linarith) (fun i ↦ by have := hr i; linarith)
  · right; left
    exact positive_pair (u 0) (u 2) (u 1) C a c b (hu 0) (hu 2) (hu 1)
      ha hc (by linarith) (fun i ↦ by have := hr i; linarith)
  · left
    exact positive_pair (u 0) (u 1) (u 2) C a b c (hu 0) (hu 1) (hu 2) ha hb hs hr
  · linarith

end
end Erdos322Research.QuarticLevelTriple
