import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix
open scoped BigOperators

def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

lemma choose_p_add_small (p r s : ℕ) (hp : Nat.Prime p) (hr : r < p) (hs : s < p) :
    ((Nat.choose (p + r) s : ℕ) : ZMod p) = (Nat.choose r s : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div (n := p + r) (k := s) (p := p))
  rw [← ZMod.intCast_eq_intCast_iff] at h
  norm_num at h
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, Nat.div_eq_of_lt hs,
    Nat.add_div_right _ (Nat.pos_of_ne_zero hp.ne_zero)] using h

lemma choose_p_add_big (p r s : ℕ) (hp : Nat.Prime p) (hr : r < p) (hs : s < p) :
    ((Nat.choose (p + r) (p + s) : ℕ) : ZMod p) = (Nat.choose r s : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div (n := p + r) (k := p + s) (p := p))
  rw [← ZMod.intCast_eq_intCast_iff] at h
  norm_num at h
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  have hdivr : (p + r) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp0, Nat.div_eq_of_lt hr, zero_add]
  have hdivs : (p + s) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp0, Nat.div_eq_of_lt hs, zero_add]
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, hdivr, hdivs] using h

lemma a_p_add_eq_zero (p r : ℕ) (hp : Nat.Prime p) (hodd : p ≠ 2) (hr : r < p) :
    (a (p + r) : ZMod p) = 0 := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  have hpoddZ : ((-1 : ZMod p) ^ p) = -1 := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hodd
    rw [hm]
    simp [pow_succ, pow_mul]
  let F : ℕ → ZMod p := fun k => (-1 : ZMod p)^k * ((Nat.choose (p+r) k : ZMod p)^4)
  have hcast : (a (p+r) : ZMod p) = ∑ k ∈ range (p+r+1), F k := by
    simp [a, F]
  rw [hcast]
  have hsplit : ∑ k ∈ range (p+r+1), F k = ∑ k ∈ range p, F k + ∑ s ∈ range (r+1), F (p+s) := by
    have hlen : p + (r+1) = p+r+1 := by omega
    rw [← hlen]
    exact Finset.sum_range_add F p (r+1)
  rw [hsplit]
  have hfirst : ∑ k ∈ range p, F k = ∑ k ∈ range (r+1), F k := by
    have hlen : r + 1 + (p - (r + 1)) = p := by omega
    calc
      ∑ k ∈ range p, F k = ∑ k ∈ range (r+1 + (p-(r+1))), F k := by rw [hlen]
      _ = ∑ k ∈ range (r+1), F k + ∑ x ∈ range (p-(r+1)), F ((r+1)+x) := by
        rw [Finset.sum_range_add]
      _ = ∑ k ∈ range (r+1), F k := by
        suffices (∑ x ∈ range (p - (r + 1)), F (r + 1 + x)) = 0 by simp [this]
        apply Finset.sum_eq_zero
        intro x hx
        simp only [mem_range] at hx
        have hxlt : r + 1 + x < p := by omega
        have hltchoose : r < r + 1 + x := by
          have hpos : 0 < 1 + x := by omega
          have hlt' : r < r + (1 + x) := Nat.lt_add_of_pos_right hpos
          simpa [Nat.add_assoc] using hlt'
        have hchoose : (Nat.choose r (r+1+x) : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt hltchoose]
          simp
        unfold F
        rw [choose_p_add_small p r (r+1+x) hp hr hxlt, hchoose]
        simp
  rw [hfirst]
  have hpair : (∑ k ∈ range (r+1), F k) + (∑ s ∈ range (r+1), F (p+s)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro s hs
    simp only [mem_range] at hs
    have hsltp : s < p := by omega
    have hsle : s ≤ r := by omega
    unfold F
    rw [choose_p_add_small p r s hp hr hsltp, choose_p_add_big p r s hp hr hsltp]
    have hpow : (-1 : ZMod p) ^ (p + s) = - ((-1 : ZMod p) ^ s) := by
      rw [pow_add, hpoddZ]
      ring
    rw [hpow]
    ring
  simpa using hpair
