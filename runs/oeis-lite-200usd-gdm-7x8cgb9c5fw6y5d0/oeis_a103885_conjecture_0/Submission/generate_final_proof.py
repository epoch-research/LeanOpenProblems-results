import sympy as sp
import math

def choose(n, k):
    if k < 0 or k > n: return 0
    return math.comb(n, k)

def a(n):
    if n == 0: return 1
    r = n - 1
    s = 0
    for k in range(n + 1):
        s += choose(n, k) * choose(2*n + k - 1, r)
    return s

def b(n):
    return a(2*n)

# We solve the 10 weights
c = sp.symbols('c0:5')
d = sp.symbols('d0:5')
vars = c + d

eqs_rec = []
for n in range(1, 9):
    plus = 1
    for k in range(1, 5):
        plus *= (4 * n + k)
    minus = 1
    for k in range(1, 5):
        minus *= (4 * n - k)
    P_pos = sum(c[i] * n**i for i in range(5))
    P_neg = sum(c[i] * (-n)**i for i in range(5))
    Q_val = sum(d[i] * (n**2)**i for i in range(5))
    eq = plus * P_pos * b(n+1) + minus * P_neg * b(n-1) - Q_val * b(n)
    eqs_rec.append(sp.expand(eq))

eqs_symm = []
for k in range(1, 3):
    P_k = sum(c[i] * k**i for i in range(5))
    P_1_k = sum(c[i] * (1 - k)**i for i in range(5))
    eq_symm = P_k - P_1_k
    eqs_symm.append(sp.expand(eq_symm))

w = sp.symbols('w1:9')
u = sp.symbols('u1:3')
weights = w + u

target = -d[4]

equations = []
for v in vars:
    coeff_lhs = sum(w[i-1] * eqs_rec[i-1].coeff(v) for i in range(1, 9)) + sum(u[k-1] * eqs_symm[k-1].coeff(v) for k in range(1, 3))
    equations.append(coeff_lhs - target.coeff(v))

sol = sp.solve(equations, weights)
print("sol:", sol)

# Format rational in Lean
def format_lean_rat(r):
    num = r.p
    den = r.q
    if den == 1:
        return f"({num} : ℝ)"
    else:
        return f"({num} / {den} : ℝ)"

# Generate Lean code
lines = []
lines.append("import FormalConjectures.Util.ProblemImports")
lines.append("set_option maxRecDepth 200000")
lines.append("")
lines.append("open Nat Finset Polynomial")
lines.append("open scoped BigOperators ComplexConjugate")
lines.append("")
lines.append("/--")
lines.append("A103885: $a(n) = [x^{2n}] \\left(\\frac{1 + x}{1 - x}\\right)^n$.")
lines.append("The sequence is given by the combinatorial identity:")
lines.append("$$a(n) = \\sum_{k = 0}^n \\binom{n}{k} \\binom{2n+k-1}{n-1}$$")
lines.append("with $a(0) = 1$.")
lines.append("-/")
lines.append("def A103885 (n : ℕ) : ℕ :=")
lines.append("  if n = 0 then 1")
lines.append("  else")
lines.append("    let r : ℕ := n - 1")
lines.append("    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))")
lines.append("")
lines.append("-- The sequence b(n) = a(m*n) lifted to ℝ")
lines.append("noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=")
lines.append("  (A103885 (m * n) : ℝ)")
lines.append("")
lines.append("open BigOperators")
lines.append("")
lines.append("-- The indices k = 1 to 2m, used in the product")
lines.append("private def product_indices (m : ℕ) : Finset ℕ :=")
lines.append("  Finset.Ioc 0 (2 * m)")
lines.append("")
lines.append("-- The factor Product_{k=1}^{2m} (2mn + k)")
lines.append("noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=")
lines.append("  (product_indices m).prod fun k =>")
lines.append("    ((2 * m * n : ℝ) + (k : ℝ))")
lines.append("")
lines.append("-- The factor Product_{k=1}^{2m} (2mn - k)")
lines.append("noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=")
lines.append("  (product_indices m).prod fun k =>")
lines.append("    ((2 * m * n : ℝ) - (k : ℝ))")
lines.append("")
lines.append("lemma eval_eq_of_natDegree_four (p : ℝ[X]) (hp : p.natDegree = 4) (z : ℝ) :")
lines.append("    p.eval z = p.coeff 0 + p.coeff 1 * z + p.coeff 2 * z ^ 2 + p.coeff 3 * z ^ 3 + p.coeff 4 * z ^ 4 := by")
lines.append("  have h_lt : p.natDegree < 5 := by omega")
lines.append("  have h1 := eval_eq_sum_range' h_lt z")
lines.append("  rw [h1]")
lines.append("  simp [sum_range_succ]")
lines.append("")
lines.append("theorem oeis_a103885_conjecture_0.disproof :")
lines.append("    ¬ (∀ (m : ℕ) (hm : 1 ≤ m),")
lines.append("        ∃ (P Q : Polynomial ℝ),")
lines.append("          P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧")
lines.append("          (∀ (n : ℕ) (hn : 1 ≤ n),")
lines.append("            (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +")
lines.append("            ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =")
lines.append("            (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧")
lines.append("          (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧")
lines.append("          (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧")
lines.append("          (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1))) := by")
lines.append("  intro h")
lines.append("  obtain ⟨P, Q, h_degP, h_degQ, h_rec, h_symm, h_rootP, h_rootQ⟩ := h 2 (by norm_num)")
lines.append("  have h_natdegP : P.natDegree = 4 := natDegree_eq_of_degree_eq_some h_degP")
lines.append("  have h_natdegQ : Q.natDegree = 4 := natDegree_eq_of_degree_eq_some h_degQ")
lines.append("")

# Generate evaluated b(n) proofs
for n in range(10):
    lines.append(f"  have hb_{n} : A103885_subsequence_real 2 {n} = {b(n)} := by")
    lines.append(f"    unfold A103885_subsequence_real")
    lines.append(f"    norm_cast")

# Generate prod_factor_plus and prod_factor_minus proofs
for n in range(1, 9):
    # prod_factor_plus 2 n
    val_plus = math.prod(4 * n + k for k in range(1, 5))
    lines.append(f"  have h_prod_plus_{n} : prod_factor_plus 2 {n} = {val_plus} := by")
    lines.append(f"    unfold prod_factor_plus product_indices")
    lines.append(f"    have h1 : (∏ k ∈ Finset.Ioc (0 : ℕ) (2 * 2 : ℕ), (2 * ↑(2 : ℕ) * ↑({n} : ℕ) + (k : ℝ))) = ∏ k ∈ Finset.Ioc (0 : ℕ) (4 : ℕ), ((k + {4 * n} : ℕ) : ℝ) := by")
    lines.append(f"      have h_dom : Finset.Ioc (0 : ℕ) (2 * 2 : ℕ) = Finset.Ioc (0 : ℕ) (4 : ℕ) := by norm_num")
    lines.append(f"      rw [h_dom]")
    lines.append(f"      refine Finset.prod_congr rfl (fun x hx => ?_)")
    lines.append(f"      push_cast")
    lines.append(f"      ring")
    lines.append(f"    rw [h1, ← Finset.prod_natCast]")
    lines.append(f"    have h2 : (∏ k ∈ Finset.Ioc (0 : ℕ) (4 : ℕ), (k + {4 * n})) = {val_plus} := by decide")
    lines.append(f"    rw [h2]")
    lines.append(f"    rfl")

    # prod_factor_minus 2 n
    val_minus = math.prod(4 * n - k for k in range(1, 5))
    lines.append(f"  have h_prod_minus_{n} : prod_factor_minus 2 {n} = {val_minus} := by")
    lines.append(f"    unfold prod_factor_minus product_indices")
    lines.append(f"    have h1 : (∏ k ∈ Finset.Ioc (0 : ℕ) (2 * 2 : ℕ), (2 * ↑(2 : ℕ) * ↑({n} : ℕ) - (k : ℝ))) = ∏ k ∈ Finset.Ioc (0 : ℕ) (4 : ℕ), ((({4 * n} - k : ℕ) : ℝ)) := by")
    lines.append(f"      have h_dom : Finset.Ioc (0 : ℕ) (2 * 2 : ℕ) = Finset.Ioc (0 : ℕ) (4 : ℕ) := by norm_num")
    lines.append(f"      rw [h_dom]")
    lines.append(f"      refine Finset.prod_congr rfl (fun x hx => ?_)")
    lines.append(f"      have hx_le : x ≤ {4 * n} := by")
    lines.append(f"        have h_mem := Finset.mem_Ioc.mp hx")
    lines.append(f"        omega")
    lines.append(f"      rw [Nat.cast_sub hx_le]")
    lines.append(f"      push_cast")
    lines.append(f"      ring")
    lines.append(f"    rw [h1, ← Finset.prod_natCast]")
    lines.append(f"    have h2 : (∏ k ∈ Finset.Ioc (0 : ℕ) (4 : ℕ), ({4 * n} - k)) = {val_minus} := by decide")
    lines.append(f"    rw [h2]")
    lines.append(f"    push_cast")
    lines.append(f"    rfl")

# Generate expanded recurrence relations
for n in range(1, 9):
    lines.append(f"  have rec{n} := h_rec {n} (by norm_num)")
    lines.append(f"  push_cast at rec{n}")
    lines.append(f"  norm_num at rec{n}")
    lines.append(f"  rw [eval_eq_of_natDegree_four P h_natdegP {n}, eval_eq_of_natDegree_four P h_natdegP (-{n}), eval_eq_of_natDegree_four Q h_natdegQ ({n**2})] at rec{n}")
    lines.append(f"  rw [hb_{n-1}, hb_{n}, hb_{n+1}, h_prod_plus_{n}, h_prod_minus_{n}] at rec{n}")

# Generate expanded symmetry equations
for k in range(1, 3):
    lines.append(f"  have symm{k} := h_symm {k}")
    lines.append(f"  norm_num at symm{k}")
    lines.append(f"  rw [eval_eq_of_natDegree_four P h_natdegP {k}, eval_eq_of_natDegree_four P h_natdegP ({1-k})] at symm{k}")

# Use linear combination to prove Q.coeff 4 = 0
lines.append("  have h_Q_coeff_4 : Q.coeff 4 = 0 := by")
terms = []
for n in range(1, 9):
    w_val = -sol[w[n-1]]  # negate because we want Q.coeff 4 (which was -d[4])
    if w_val != 0:
        terms.append(f"{format_lean_rat(w_val)} * rec{n}")
for k in range(1, 3):
    u_val = -sol[u[k-1]]
    if u_val != 0:
        terms.append(f"{format_lean_rat(u_val)} * symm{k}")
lines.append("    linear_combination " + " + ".join(terms))

# Finish the proof by contradiction
lines.append("  have h_ne : Q ≠ 0 := by")
lines.append("    intro hQ0")
lines.append("    rw [hQ0, degree_zero] at h_degQ")
lines.append("    contradiction")
lines.append("  have h_lc := leadingCoeff_ne_zero.mpr h_ne")
lines.append("  rw [leadingCoeff, h_natdegQ, h_Q_coeff_4] at h_lc")
lines.append("  exact h_lc rfl")
lines.append("")

# Write to file
with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("\n".join(lines))
    f.write("\n")

print("Generated Spec.lean successfully for m=2!")
