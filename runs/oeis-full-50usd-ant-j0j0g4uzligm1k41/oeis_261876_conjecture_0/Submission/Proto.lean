import FormalConjectures.Util.ProblemImports
open Finset BigOperators
set_option maxHeartbeats 0

def key (p : ℕ×ℕ×ℕ) : ℕ := p.1 * 69696 + p.2.1 * 264 + p.2.2

-- three tiny chunks
def c0 : List (ℕ×ℕ×ℕ) := [(0,0,1),(0,0,2)]
def c1 : List (ℕ×ℕ×ℕ) := [(0,1,1),(0,1,2)]
def c2 : List (ℕ×ℕ×ℕ) := [(0,2,1),(0,2,2)]
def LL : List (ℕ×ℕ×ℕ) := c0 ++ (c1 ++ c2)

lemma c0ch : List.IsChain (· < ·) (c0.map key) := by decide
lemma c1ch : List.IsChain (· < ·) (c1.map key) := by decide
lemma c2ch : List.IsChain (· < ·) (c2.map key) := by decide

lemma LLnodup : LL.Nodup := by
  have hch : List.IsChain (· < ·) (LL.map key) := by
    simp only [LL, List.map_append, List.isChain_append]
    refine ⟨c0ch, ⟨c1ch, c2ch, by decide⟩, by decide⟩
  have hp : (LL.map key).Pairwise (· < ·) := List.isChain_iff_pairwise.mp hch
  have hnd : (LL.map key).Nodup := hp.imp (fun h => Nat.ne_of_lt h)
  exact hnd.of_map key

lemma sumeq : (LL.map (fun p => p.2.2)).sum
    = (c0.map (fun p => p.2.2)).sum + ((c1.map (fun p => p.2.2)).sum + (c2.map (fun p => p.2.2)).sum) := by
  simp only [LL, List.map_append, List.sum_append]
