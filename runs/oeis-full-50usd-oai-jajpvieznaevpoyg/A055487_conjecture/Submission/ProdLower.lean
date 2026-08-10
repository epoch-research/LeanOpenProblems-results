import FormalConjectures.Util.ProblemImports
open Nat

lemma two_mul_le_prod_succ_three {a b c : ℕ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    2 * (a * b * c) ≤ (a + 1) * (b + 1) * (c + 1) := by
  nlinarith

lemma two_mul_le_prod_succ_list : ∀ (l : List ℕ), (∀ x ∈ l, 1 < x) → 3 ≤ l.length →
    2 * l.prod ≤ (l.map (fun x => x + 1)).prod
  | [] => by simp
  | [a] => by simp
  | [a,b] => by simp
  | a::b::c::t => by
      intro h hlen
      have ha : 1 < a := h a (by simp)
      have hb : 1 < b := h b (by simp)
      have hc : 1 < c := h c (by simp)
      have htprod_pos : 1 ≤ t.prod := by exact Nat.succ_le_of_lt (List.prod_pos (fun x hx => by have := h x (by simp [hx]); omega))
      -- enough since first three already give factor 2, remaining succ factors >= original factors
      have hfirst : 2 * (a * b * c) ≤ (a + 1) * (b + 1) * (c + 1) := two_mul_le_prod_succ_three ha hb hc
      have htail : t.prod ≤ (t.map (fun x => x + 1)).prod := by
        apply List.prod_le_prod
        intro x hx
        omega
      simp [List.prod_cons, mul_assoc]
      nlinarith
