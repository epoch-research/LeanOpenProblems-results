import Submission.Work

/-! A kernel-evaluated finite search certifies nonexistence of a simple path of a specified length. -/
namespace Erdos583FinitePathSearchDevelopment
open SimpleGraph
set_option maxHeartbeats 3000000
set_option Elab.async false

variable {V : Type*} [DecidableEq V]

def search (next : V → List V) : ℕ → Finset V → V → V → Bool
  | 0, _, u, t => decide (u=t)
  | n+1, used, u, t => (next u).any fun v ↦ decide (v ∉ used) &&
      search next n (insert v used) v t

lemma search_of_path (G : SimpleGraph V) (next : V → List V)
    (hall : ∀ u v, G.Adj u v → v ∈ next u)
    {a b : V} (P : G.Walk a b) (hp : P.IsPath) (used : Finset V)
    (hused : ∀ v ∈ P.support, v ∈ used → v=a) : search next P.length used a b=true := by
  induction P generalizing used with
  | nil => simp [search]
  | @cons a v b h P ih =>
    have hP := (Walk.cons_isPath_iff h P).mp hp
    have hvn : v ∉ used := by
      intro hv
      exact h.ne.symm (hused v (List.mem_cons_of_mem _ P.start_mem_support) hv)
    have hused' : ∀ z ∈ P.support, z ∈ insert v used → z=v := by
      intro z hz hzu
      rcases Finset.mem_insert.mp hzu with hzv | hzu
      · exact hzv
      · have hza := hused z (List.mem_cons_of_mem _ hz) hzu
        exact (hP.2 (hza ▸ hz)).elim
    simp only [Walk.length_cons,search,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨v,hall a v h,hvn,ih hP.1 (insert v used) hused'⟩

lemma no_path_of_search_false (G : SimpleGraph V) (next : V → List V)
    (hall : ∀ u v, G.Adj u v → v ∈ next u)
    (n : ℕ) (a b : V) (h : search next n {a} a b=false) :
    ¬∃ P : G.Walk a b, P.IsPath ∧ P.length=n := by
  rintro ⟨P,hP,hlen⟩
  have hh := search_of_path G next hall P hP {a} (by intro z _ hz; exact Finset.mem_singleton.mp hz)
  rw [hlen,h] at hh
  contradiction

end Erdos583FinitePathSearchDevelopment
