import FormalConjecturesUtil

/-! Compressing a finite collection of sites for a decreasing nonnegative profile. -/
namespace Erdos66AntitoneFiniteMass
open scoped Classical

lemma finite_sum_le_prefix (p : ℕ → ℝ) (hp : Antitone p) (S : Finset ℕ) :
    ∑ a∈S, p a ≤ ∑ i∈Finset.range S.card, p i := by
  let e : Fin S.card ↪o ℕ := S.orderEmbOfFin rfl
  have lower : ∀ j (hj : j < S.card), j ≤ e ⟨j,hj⟩ := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hj' : j < S.card := by omega
      have h0 := ih hj'
      have h1 := e.strictMono (show (⟨j,hj'⟩ : Fin S.card) < ⟨j+1,hj⟩ from by
        exact Fin.mk_lt_mk.mpr (by omega))
      omega
  have he : Finset.univ.image e=S := Finset.image_orderEmbOfFin_univ S rfl
  calc
    ∑ a∈S, p a = ∑ i : Fin S.card, p (e i) := by
      calc
        _ = ∑ a∈Finset.univ.image e, p a := congrArg (fun U : Finset ℕ ↦ ∑ a∈U, p a) he.symm
        _ = _ := Finset.sum_image (fun i _ j _ h ↦ e.injective h)
    _ ≤ ∑ i : Fin S.card, p i.val := Finset.sum_le_sum (fun i _ ↦ hp (lower i.val i.isLt))
    _ = ∑ i∈Finset.range S.card, p i := Fin.sum_univ_eq_sum_range p S.card

lemma finite_sum_le_prefix_of_card_le (p : ℕ → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 ≤ p i) (S : Finset ℕ) (n : ℕ) (hc : S.card ≤ n) :
    ∑ a∈S, p a ≤ ∑ i∈Finset.range n, p i :=
  (finite_sum_le_prefix p hp S).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hc) (fun i _ _ ↦ hpos i))

end Erdos66AntitoneFiniteMass
