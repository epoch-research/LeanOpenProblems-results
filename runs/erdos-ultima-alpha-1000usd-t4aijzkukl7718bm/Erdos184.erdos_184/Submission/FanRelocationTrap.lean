import Submission.IntersectingTerminalExchange

/-! A concrete nonmaximal packing on six vertices where every two-fan
same-terminal-path relocation of the unused triangle loses two covered edges.
This is an obstruction to a proposed local algorithm, not to Erdős184. -/
open SimpleGraph
namespace Erdos184Work.OddPaths.FanTrap
set_option maxHeartbeats 1000000

def G : SimpleGraph (Fin 6) where
  Adj u v := u ≠ v ∧ (u.val < 3 ∨ v.val < 3)
  symm := by intro u v h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro u h; exact h.1 rfl

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (u.val < 3 ∨ v.val < 3)))

def P0 : G.Walk 0 3 := .cons (show G.Adj 0 4 by decide) (.cons (show G.Adj 4 1 by decide) (.cons (show G.Adj 1 3 by decide) (.nil)))
def p0 : Piece G := ⟨0,3,P0,by rw [Walk.isPath_def]; decide,by decide⟩
def P1 : G.Walk 1 4 := .cons (show G.Adj 1 5 by decide) (.cons (show G.Adj 5 2 by decide) (.cons (show G.Adj 2 4 by decide) (.nil)))
def p1 : Piece G := ⟨1,4,P1,by rw [Walk.isPath_def]; decide,by decide⟩
def P2 : G.Walk 2 5 := .cons (show G.Adj 2 3 by decide) (.cons (show G.Adj 3 0 by decide) (.cons (show G.Adj 0 5 by decide) (.nil)))
def p2 : Piece G := ⟨2,5,P2,by rw [Walk.isPath_def]; decide,by decide⟩

def L : List (Piece G) := [p0,p1,p2]
def C : G.Walk 0 0 := .cons (show G.Adj 0 1 by decide)
  (.cons (show G.Adj 1 2 by decide) (.cons (show G.Adj 2 0 by decide) .nil))

lemma admissible : Admissible L := by
  constructor
  · change ([s(0,4),s(4,1),s(1,3),s(1,5),s(5,2),s(2,4),s(2,3),s(3,0),s(0,5)] : List (Sym2 (Fin 6))).Nodup
    decide
  · constructor
    · change ([0,3,1,4,2,5] : List (Fin 6)).Nodup
      decide
    · change ∀ v : Fin 6, v ∈ [0,3,1,4,2,5]
      decide

lemma cycle : C.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide
lemma unused : (edgeList L).Disjoint C.edges := by
  change ([s(0,4),s(4,1),s(1,3),s(1,5),s(5,2),s(2,4),s(2,3),s(3,0),s(0,5)] : List (Sym2 (Fin 6))).Disjoint
    [s(0,1),s(1,2),s(2,0)]
  change ∀ e : Sym2 (Fin 6), e ∈ _ → e ∉ _
  decide

lemma all_odd : ∀ v, Odd (G.degree v) := by decide

def R0 : G.Walk 0 3 := .cons (show G.Adj 0 4 by decide) (.cons (show G.Adj 4 1 by decide) (.cons (show G.Adj 1 5 by decide) (.cons (show G.Adj 5 2 by decide) (.cons (show G.Adj 2 3 by decide) (.nil)))))
def r0 : Piece G := ⟨0,3,R0,by rw [Walk.isPath_def]; decide,by decide⟩
def R1 : G.Walk 4 1 := .cons (show G.Adj 4 2 by decide) (.cons (show G.Adj 2 0 by decide) (.cons (show G.Adj 0 3 by decide) (.cons (show G.Adj 3 1 by decide) (.nil))))
def r1 : Piece G := ⟨4,1,R1,by rw [Walk.isPath_def]; decide,by decide⟩
def R2 : G.Walk 5 2 := .cons (show G.Adj 5 0 by decide) (.cons (show G.Adj 0 1 by decide) (.cons (show G.Adj 1 2 by decide) (.nil)))
def r2 : Piece G := ⟨5,2,R2,by rw [Walk.isPath_def]; decide,by decide⟩

def full : List (Piece G) := [r0,r1,r2]
lemma full_admissible : Admissible full := by
  constructor
  · change ([s(0,4),s(4,1),s(1,5),s(5,2),s(2,3),s(4,2),s(2,0),s(0,3),s(3,1),s(5,0),s(0,1),s(1,2)] : List (Sym2 (Fin 6))).Nodup
    decide
  · constructor
    · change ([0,3,4,1,5,2] : List (Fin 6)).Nodup
      decide
    · change ∀ v : Fin 6, v ∈ [0,3,4,1,5,2]
      decide

lemma full_covers : ∀ e : Sym2 (Fin 6), e ∈ edgeList full ↔ e ∈ G.edgeSet := by
  decide

lemma not_maximal : ¬ Maximal L := by
  intro h
  have hh := h.2 full full_admissible
  change 12 ≤ 9 at hh
  omega

def a : Fin 3 → Fin 6 := ![0,1,2]
def b : Fin 3 → Fin 6 := ![3,4,5]
def next : Fin 3 → Fin 3 := ![1,2,0]
def prev : Fin 3 → Fin 3 := ![2,0,1]
def path : Fin 3 → Piece G := ![p0,p1,p2]

lemma touching (v : Fin 3) : touchingEndpoints L (a v) =
    {a v,b v,a (prev v),b (prev v)} := by
  fin_cases v <;> ext x <;> fin_cases x <;>
    simp [touchingEndpoints,touchingPaths,endpoints,L,a,b,prev,p0,p1,p2,P0,P1,P2,
      Walk.support]

lemma first_branch (v : Fin 3) : Branch L (a v) (a (prev v)) (b v) := by
  fin_cases v
  · exact ⟨p2,by simp [L],by decide,Or.inl ⟨rfl,by decide⟩⟩
  · exact ⟨p0,by simp [L],by decide,Or.inl ⟨rfl,by decide⟩⟩
  · exact ⟨p1,by simp [L],by decide,Or.inl ⟨rfl,by decide⟩⟩

lemma second_branch (v : Fin 3) : Branch L (a v) (b v) (b (next v)) := by
  fin_cases v
  · exact ⟨p0,by simp [L],by decide,Or.inr ⟨rfl,by decide⟩⟩
  · exact ⟨p1,by simp [L],by decide,Or.inr ⟨rfl,by decide⟩⟩
  · exact ⟨p2,by simp [L],by decide,Or.inr ⟨rfl,by decide⟩⟩

lemma first_step (v : Fin 3) : fanStep L (a v) (a (prev v)) = b v := by
  apply Branch.fanStep_eq admissible _ (first_branch v)
  rw [touching]
  fin_cases v <;> simp [a,b,prev,Finset.mem_erase]

lemma second_step (v : Fin 3) : fanStep L (a v) (b v) = b (next v) := by
  apply Branch.fanStep_eq admissible _ (second_branch v)
  rw [touching]
  fin_cases v <;> simp [a,b,prev,Finset.mem_erase]

lemma terminal_avoids (v : Fin 3) :
    a (next v) ∉ touchingEndpoints L (a v) ∧ b (next v) ∉ touchingEndpoints L (a v) := by
  rw [touching]
  fin_cases v <;> simp [a,b,prev,next]

lemma first_terminal_fixed (v : Fin 3) : fanStep L (a v) (a (next v)) = a (next v) := by
  letI : DecidableEq (Fin 6) := Classical.decEq _
  unfold fanStep
  split
  · rename_i h
    exact ((terminal_avoids v).1 (Finset.mem_erase.mp h).2).elim
  · rfl

lemma second_terminal_fixed (v : Fin 3) : fanStep L (a v) (b (next v)) = b (next v) := by
  letI : DecidableEq (Fin 6) := Classical.decEq _
  unfold fanStep
  split
  · rename_i h
    exact ((terminal_avoids v).2 (Finset.mem_erase.mp h).2).elim
  · rfl

lemma first_fan_iterate (v : Fin 3) (n : ℕ) :
    (fanStep L (a v))^[n] (a (next v)) = a (next v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,first_terminal_fixed]

lemma second_fan_iterate (v : Fin 3) (n : ℕ) :
    (fanStep L (a v))^[n+2] (a (prev v)) = b (next v) := by
  induction n with
  | zero => simp only [Function.iterate_succ_apply',Function.iterate_zero_apply,first_step,second_step]
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega,Function.iterate_succ_apply',ih,second_terminal_fixed]

lemma second_fan_exit (v : Fin 3) (n : ℕ)
    (hexit : (fanStep L (a v))^[n] (a (prev v)) ∉ touchingEndpoints L (a v)) :
    (fanStep L (a v))^[n] (a (prev v)) = b (next v) := by
  cases n with
  | zero =>
    exfalso
    apply hexit
    simp [touching]
  | succ n =>
    cases n with
    | zero =>
      exfalso
      apply hexit
      simp only [Function.iterate_succ_apply',Function.iterate_zero_apply,first_step]
      simp [touching]
    | succ n => exact second_fan_iterate v n

lemma terminal_path_data (v : Fin 3) :
    path (next v) ∈ L ∧ (path (next v)).src = a (next v) ∧
      (path (next v)).dst = b (next v) ∧ (path (next v)).walk.length = 3 ∧
      a v ∉ (path (next v)).walk.support := by
  fin_cases v <;> simp [path,next,a,b,L,p0,p1,p2,P0,P1,P2,Walk.support]

/-- Every pair of exiting fans at a triangle vertex ends at opposite endpoints
of one length-three path, independently of the existential fan length choices. -/
lemma all_fan_exits_same_path (v : Fin 3) (n m : ℕ)
    (hexit : (fanStep L (a v))^[m] (a (prev v)) ∉ touchingEndpoints L (a v)) :
    ∃ p ∈ L,
      (fanStep L (a v))^[n] (a (next v)) = p.src ∧
      (fanStep L (a v))^[m] (a (prev v)) = p.dst ∧
      p.walk.length = 3 ∧ a v ∉ p.walk.support := by
  obtain ⟨hp,hs,ht,hl,hv⟩ := terminal_path_data v
  exact ⟨path (next v),hp,(first_fan_iterate v n).trans hs.symm,
    (second_fan_exit v m hexit).trans ht.symm,hl,hv⟩

/-- Any exact one-cycle relocation onto any of the packed paths loses two
covered edges. This does NOT assert that the initial packing is maximal. -/
lemma every_same_path_relocation_loses_two (p : Piece G) (hp : p ∈ L)
    (N : List (Piece G)) {v : Fin 6} (D : G.Walk v v)
    (he : (edgeList N ++ D.edges).Perm (edgeList L ++ C.edges))
    (hlen : D.length = p.walk.length + 2) :
    (edgeList N).length + 2 = (edgeList L).length := by
  have hpl : p.walk.length = 3 := by
    simp only [L,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rfl
  have hl := he.length_eq
  simp only [List.length_append,Walk.length_edges] at hl
  have hC : C.length = 3 := rfl
  omega

lemma outside_touching (v : Fin 3) (x : Fin 6) :
    x ∉ touchingEndpoints L (a v) ↔ x = a (next v) ∨ x = b (next v) := by
  rw [touching]
  fin_cases v <;> fin_cases x <;> simp [a,b,prev,next]

lemma all_paths_dirty : ∀ p ∈ L, ∃ w ∈ p.walk.support,
    w ∈ C.support ∧ w ≠ p.src ∧ w ≠ p.dst := by
  intro p hp
  simp only [L,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- The losing relocation is not merely a hypothetical edge identity: actual
fan rotation constructs it at each vertex of the unused triangle. -/
lemma losing_relocation_exists (v : Fin 3) :
    ∃ (N : List (Piece G)) (D : G.Walk (a v) (a v)),
      Admissible N ∧ D.IsCycle ∧ (edgeList N ++ D.edges).Nodup ∧
      (edgeList N ++ D.edges).Perm (edgeList L ++ C.edges) ∧
      (endpoints N).Perm (endpoints L) ∧ D.length = 5 ∧ (edgeList N).length = 7 := by
  have hvC : a v ∈ C.support := by fin_cases v <;> decide
  let R := C.rotate hvC
  have hR : R.IsCycle := cycle.rotate hvC
  have hRe : R.edges.Perm C.edges := (C.rotate_edges hvC).perm
  have hdisR : (edgeList L).Disjoint R.edges := by
    intro e he heR
    exact unused he (hRe.mem_iff.mp heR)
  obtain ⟨x,y,Q,hx,hy,heq,hxy⟩ := FanAbsorption.cycle_as_rim R hR
  have hQcy : (Walk.cons hx (Q.concat hy)).IsCycle := heq ▸ hR
  have hdisQ : (edgeList L).Disjoint (Walk.cons hx (Q.concat hy)).edges := heq ▸ hdisR
  have hxu : (G \ coveredGraph L).Adj (a v) x := by
    refine ⟨hx,?_⟩
    intro h
    exact hdisQ ((coveredGraph_adj L (a v) x).mp h) (by simp)
  have hyu : (G \ coveredGraph L).Adj (a v) y := by
    refine ⟨hy.symm,?_⟩
    intro h
    apply hdisQ ((coveredGraph_adj L (a v) y).mp h)
    simp [Walk.edges_concat,Sym2.eq_swap]
  obtain ⟨t,z,M,htz,hvt,hvz,ht,hz,_,hME,hMV,hkeep⟩ := admissible.rotate_two_endpoint_fans hxu hyu hxy
  obtain ⟨hp,hps,hpd,hpl,hpv⟩ := terminal_path_data v
  have hpt : t = (path (next v)).src ∨ t = (path (next v)).dst := by
    rw [hps,hpd]
    exact (outside_touching v t).mp ht
  have hpz : z = (path (next v)).src ∨ z = (path (next v)).dst := by
    rw [hps,hpd]
    exact (outside_touching v z).mp hz
  obtain ⟨N,D,hN,hD,hn,he,hends,hl,_⟩ := FanRelocation.same_terminal_path admissible Q hx hy
    hQcy hdisQ hME hMV htz hvt hvz (path (next v)) (hkeep _ hp hpv) hpt hpz hpv
  have he' : (edgeList N ++ D.edges).Perm (edgeList L ++ C.edges) := by
    have heR : (edgeList N ++ D.edges).Perm (edgeList L ++ R.edges) := by rwa [heq]
    exact heR.trans (hRe.append_left _)
  have hDl : D.length = 5 := by omega
  have hlen := he'.length_eq
  simp only [List.length_append,Walk.length_edges,hDl] at hlen
  have hLl : (edgeList L).length = 9 := rfl
  have hCl : C.length = 3 := rfl
  exact ⟨N,D,hN,hD,hn,he',hends,hDl,by omega⟩

end Erdos184Work.OddPaths.FanTrap
#print axioms Erdos184Work.OddPaths.FanTrap.not_maximal

#print axioms Erdos184Work.OddPaths.FanTrap.all_fan_exits_same_path
#print axioms Erdos184Work.OddPaths.FanTrap.every_same_path_relocation_loses_two

#print axioms Erdos184Work.OddPaths.FanTrap.losing_relocation_exists
