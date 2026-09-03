import FormalConjecturesUtil

/-! A finite integer-capacity obstruction for acyclic splitting flows.
This validates a necessary-condition recurrence for a construction search,
not an obstruction to arbitrary odd covering systems. -/
namespace Erdos7AcyclicIntegerCapacity
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {n : ℕ} {E : Type*} [Fintype E]

def incoming (dst : E → Fin n) (p f : E → ℕ) (i : Fin n) : ℕ :=
  ∑ e, if dst e = i then p e * f e else 0

def outgoing (src : E → Fin n) (f : E → ℕ) (i : Fin n) : ℕ :=
  ∑ e, if src e = i then f e else 0

lemma edge_le_incoming (dst : E → Fin n) (p f : E → ℕ) (e : E) :
    p e*f e ≤ incoming dst p f (dst e) := by
  classical
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun j => if dst j = dst e then p j*f j else 0)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ e)
  simpa only [ite_true, incoming] using h

/-- Every actual integer flow is bounded by a backwards capacity certificate.
The division by each branch size is integer division; omitting that integrality
can turn an impossible construction into a feasible fractional relaxation. -/
theorem capacity_bound (src dst : E → Fin n) (p f : E → ℕ)
    (hp : ∀ e, 0 < p e) (horder : ∀ e, src e < dst e)
    (root leaf L C : Fin n → ℕ) (hleaf : ∀ i, leaf i ≤ L i)
    (hbalance : ∀ i, root i + incoming dst p f i = leaf i + outgoing src f i)
    (hcap : ∀ i, L i + outgoing src (fun e => C (dst e) / p e) i ≤ C i) :
    ∀ i, root i + incoming dst p f i ≤ C i := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨i,hi⟩ := hn
  let Bad := {i : Fin n // C i < root i + incoming dst p f i}
  letI : Nonempty Bad := ⟨⟨i,hi⟩⟩
  obtain ⟨v,hv⟩ := Finite.exists_max (fun v : Bad => v.val.val)
  have hchild (e : E) (he : src e = v.val) :
      root (dst e) + incoming dst p f (dst e) ≤ C (dst e) := by
    by_contra h
    have hh : C (dst e) < root (dst e) + incoming dst p f (dst e) := by omega
    have hm := hv ⟨dst e,hh⟩
    have ho := horder e
    rw [he] at ho
    change v.val.val < (dst e).val at ho
    exact (not_lt_of_ge hm) ho
  have hflow (e : E) (he : src e = v.val) : f e ≤ C (dst e) / p e := by
    apply (Nat.le_div_iff_mul_le (hp e)).mpr
    calc
      f e*p e = p e*f e := Nat.mul_comm _ _
      _ ≤ incoming dst p f (dst e) := edge_le_incoming dst p f e
      _ ≤ root (dst e) + incoming dst p f (dst e) := by omega
      _ ≤ C (dst e) := hchild e he
  have hout : outgoing src f v.val ≤ outgoing src (fun e => C (dst e)/p e) v.val := by
    apply Finset.sum_le_sum
    intro e _
    by_cases he : src e = v.val
    · simpa only [if_pos he] using hflow e he
    · simp only [if_neg he, le_refl]
  have hgood : root v.val + incoming dst p f v.val ≤ C v.val := by
    rw [hbalance]
    exact (Nat.add_le_add (hleaf v.val) hout).trans (hcap v.val)
  exact (not_lt_of_ge hgood) v.property

/-- In particular a node with positive externally supplied mass cannot have
zero certified capacity. -/
theorem root_bound (src dst : E → Fin n) (p f : E → ℕ)
    (hp : ∀ e, 0 < p e) (horder : ∀ e, src e < dst e)
    (root leaf L C : Fin n → ℕ) (hleaf : ∀ i, leaf i ≤ L i)
    (hbalance : ∀ i, root i + incoming dst p f i = leaf i + outgoing src f i)
    (hcap : ∀ i, L i + outgoing src (fun e => C (dst e) / p e) i ≤ C i) :
    ∀ i, root i ≤ C i := by
  intro i
  exact (Nat.le_add_right _ _).trans
    (capacity_bound src dst p f hp horder root leaf L C hleaf hbalance hcap i)

#print axioms capacity_bound
#print axioms root_bound
end Erdos7AcyclicIntegerCapacity
