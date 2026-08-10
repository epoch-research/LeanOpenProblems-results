import FormalConjectures.Util.ProblemImports

open Matrix Nat Finset

-- Q1: does `ring` normalize polynomial denominators with shifted casts?
example (a : ℚ) (j : ℕ) : a / (4*((j:ℚ)+1)-3) = a / (4*(j:ℚ)+1) := by ring

-- Q2: fraction-equality via ring (nested cast j+1)
example (j : ℕ) :
    (((j:ℚ)+1)+1)*(2*((j:ℚ)+1)-3)/((4*((j:ℚ)+1)-3)*(4*((j:ℚ)+1)+1))
    = ((j:ℚ)+2)*(2*(j:ℚ)-1)/((4*(j:ℚ)+1)*(4*(j:ℚ)+5)) := by
  ring

-- Q3: actual ac unfold form with literal ↑(j+1)
noncomputable def acT (k : ℕ) : ℚ :=
  ((k:ℚ)+1)*(2*(k:ℚ)-3)/((4*(k:ℚ)-3)*(4*(k:ℚ)+1))
example (j : ℕ) : acT (j+1) = ((j:ℚ)+2)*(2*(j:ℚ)-1)/((4*(j:ℚ)+1)*(4*(j:ℚ)+5)) := by
  unfold acT; push_cast; ring

-- Q4: 4j-1 ≠ 0
example (j : ℕ) : (4*(j:ℚ)-1) ≠ 0 := by
  rcases Nat.eq_zero_or_pos j with h|h
  · subst h; norm_num
  · have : (1:ℚ) ≤ (j:ℚ) := by exact_mod_cast h
    intro hc; linarith

-- Q5: factorial successor rewrite for Gf-style denominator
example (m k : ℕ) : ((2*m+2*(k+1)).factorial : ℚ)
    = (2*(m:ℚ)+2*k+2) * ((2*(m:ℚ)+2*k+1) * (2*m+2*k).factorial) := by
  rw [show 2*m+2*(k+1) = 2*m+2*k+1+1 from by ring, Nat.factorial_succ, Nat.factorial_succ]
  push_cast; ring

-- Q6: big field_simp/ring rational identity with opaque atoms factored
example (m j : ℕ) (c P G : ℚ)
    (e1 : (2*(m:ℚ)+2*j+1) ≠ 0) (e2 : (2*(m:ℚ)+2*j+2) ≠ 0)
    (e3 : (2*(m:ℚ)+2*j+3) ≠ 0) (e4 : (2*(m:ℚ)+2*j+4) ≠ 0)
    (qm1 : (4*(j:ℚ)-1) ≠ 0) (q1 : (4*(j:ℚ)+1) ≠ 0)
    (q3 : (4*(j:ℚ)+3) ≠ 0) (q5 : (4*(j:ℚ)+5) ≠ 0) :
    (((2*(j:ℚ)-1)*(2*(j:ℚ)+1)/((4*(j:ℚ)+3)*(4*(j:ℚ)+5))) *
       ((2*(j:ℚ)-3)*(2*(j:ℚ)-1)/((4*(j:ℚ)-1)*(4*(j:ℚ)+1)))
       * ((m:ℚ)-j) * ((m:ℚ)-(j+1)) *
       (((m:ℚ)+j+2)*((m:ℚ)+j+1)/(((2*(m:ℚ)+2*j+4)*(2*(m:ℚ)+2*j+3))*((2*(m:ℚ)+2*j+2)*(2*(m:ℚ)+2*j+1))))) * (c*P*G)
    = (((2*(j:ℚ)-3)*(2*(j:ℚ)-1)/((4*(j:ℚ)-1)*(4*(j:ℚ)+1))) * ((m:ℚ)+1) *
        (((m:ℚ)+2)*((m:ℚ)+j+2)*((m:ℚ)+j+1)/(((2*(m:ℚ)+2*j+4)*(2*(m:ℚ)+2*j+3))*((2*(m:ℚ)+2*j+2)*(2*(m:ℚ)+2*j+1))))) * (c*P*G)
      - (((j:ℚ)+2)*(2*(j:ℚ)-1)/((4*(j:ℚ)+1)*(4*(j:ℚ)+5))) *
          ((((2*(j:ℚ)-3)*(2*(j:ℚ)-1)/((4*(j:ℚ)-1)*(4*(j:ℚ)+1))) * ((m:ℚ)-j) *
            (((m:ℚ)+j+1)/((2*(m:ℚ)+2*j+2)*(2*(m:ℚ)+2*j+1)))) * (c*P*G))
      - (((j:ℚ)+1)*((j:ℚ)+2)*(2*(j:ℚ)-1)*(2*(j:ℚ)-3)/(4*(4*(j:ℚ)-1)*(4*(j:ℚ)+1)^2*(4*(j:ℚ)+3))) * (c*P*G) := by
  field_simp
  ring
