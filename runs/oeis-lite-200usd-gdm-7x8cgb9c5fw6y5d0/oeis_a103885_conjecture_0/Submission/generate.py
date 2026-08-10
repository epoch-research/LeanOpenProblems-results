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
    return a(5*n)

# Define variables for solving the system
c = sp.symbols('c0:11')
d = sp.symbols('d0:11')
vars = c + d

# We build the 21 equations: 16 recurrence (n=1..16), 5 symmetry (k=1..5)
eqs = []
for n in range(1, 17):
    plus = 1
    for k in range(1, 11):
        plus *= (10*n + k)
    minus = 1
    for k in range(1, 11):
        minus *= (10*n - k)
    eq = plus * sum(c[i] * n**i for i in range(11)) * b(n+1) - minus * sum(c[i] * (-n)**i for i in range(11)) * b(n-1) - sum(d[i] * n**(2*i) for i in range(11)) * b(n)
    eqs.append(eq)

for k in range(1, 6):
    eq = sum(c[i] * k**i for i in range(11)) - sum(c[i] * (1 - k)**i for i in range(11))
    eqs.append(eq)

# Solve with d10 = 1
eqs_subs = [eq.subs(d[10], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])

d0_vals = {j: sol[d[j]] for j in range(10)}
d0_vals[10] = 1

# Symbolic x for solving weights
x = sp.Symbol('x')
target = sum(d[j] * x**j for j in range(11)) - sum(d0_vals[j] * x**j for j in range(11)) * d[10]
target_coeffs = {v: target.coeff(v) for v in vars}

weight_symbols = sp.symbols('w1:17') + sp.symbols('u1:6')
eqs_weights = []
for v in vars:
    coeff_lhs = sum(weight_symbols[i-1] * eqs[i-1].coeff(v) for i in range(1, 17)) + sum(weight_symbols[16+k-1] * eqs[16+k-1].coeff(v) for k in range(1, 6))
    eqs_weights.append(coeff_lhs - target_coeffs[v])

sol_weights = sp.solve(eqs_weights, weight_symbols)

# Evaluate target Q0 at 1.1 and 1.2
Q0_1_1 = sum(d0_vals[j] * (sp.Rational(11, 10))**j for j in range(11))
Q0_1_2 = sum(d0_vals[j] * (sp.Rational(12, 10))**j for j in range(11))

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
lines.append("lemma eval_eq_of_natDegree_ten (p : ℝ[X]) (hp : p.natDegree = 10) (z : ℝ) :")
lines.append("    p.eval z = p.coeff 0 + p.coeff 1 * z + p.coeff 2 * z ^ 2 + p.coeff 3 * z ^ 3 + p.coeff 4 * z ^ 4 + p.coeff 5 * z ^ 5 + p.coeff 6 * z ^ 6 + p.coeff 7 * z ^ 7 + p.coeff 8 * z ^ 8 + p.coeff 9 * z ^ 9 + p.coeff 10 * z ^ 10 := by")
lines.append("  have h_lt : p.natDegree < 11 := by omega")
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
lines.append("  obtain ⟨P, Q, h_degP, h_degQ, h_rec, h_symm, h_rootP, h_rootQ⟩ := h 5 (by norm_num)")
lines.append("  have h_natdegP : P.natDegree = 10 := natDegree_eq_of_degree_eq_some h_degP")
lines.append("  have h_natdegQ : Q.natDegree = 10 := natDegree_eq_of_degree_eq_some h_degQ")
lines.append("")

# Generate evaluated b(n) proofs
for n in range(18):
    lines.append(f"  have hb_{n} : A103885_subsequence_real 5 {n} = {b(n)} := by")
    lines.append(f"    unfold A103885_subsequence_real")
    lines.append(f"    norm_cast")

# Generate prod_factor_plus and prod_factor_minus proofs
for n in range(1, 17):
    # prod_factor_plus 5 n
    val_plus = math.prod(10 * n + k for k in range(1, 11))
    lines.append(f"  have h_prod_plus_{n} : prod_factor_plus 5 {n} = {val_plus} := by")
    lines.append(f"    unfold prod_factor_plus product_indices")
    lines.append(f"    have h1 : (∏ k ∈ Finset.Ioc (0 : ℕ) (2 * 5 : ℕ), (2 * ↑(5 : ℕ) * ↑({n} : ℕ) + (k : ℝ))) = ∏ k ∈ Finset.Ioc (0 : ℕ) (10 : ℕ), ((k + {10 * n} : ℕ) : ℝ) := by")
    lines.append(f"      have h_dom : Finset.Ioc (0 : ℕ) (2 * 5 : ℕ) = Finset.Ioc (0 : ℕ) (10 : ℕ) := by norm_num")
    lines.append(f"      rw [h_dom]")
    lines.append(f"      refine Finset.prod_congr rfl (fun x hx => ?_)")
    lines.append(f"      push_cast")
    lines.append(f"      ring")
    lines.append(f"    rw [h1, ← Finset.prod_natCast]")
    lines.append(f"    have h2 : (∏ k ∈ Finset.Ioc (0 : ℕ) (10 : ℕ), (k + {10 * n})) = {val_plus} := by decide")
    lines.append(f"    rw [h2]")
    lines.append(f"    rfl")

    # prod_factor_minus 5 n
    val_minus = math.prod(10 * n - k for k in range(1, 11))
    lines.append(f"  have h_prod_minus_{n} : prod_factor_minus 5 {n} = {val_minus} := by")
    lines.append(f"    unfold prod_factor_minus product_indices")
    lines.append(f"    have h1 : (∏ k ∈ Finset.Ioc (0 : ℕ) (2 * 5 : ℕ), (2 * ↑(5 : ℕ) * ↑({n} : ℕ) - (k : ℝ))) = ∏ k ∈ Finset.Ioc (0 : ℕ) (10 : ℕ), ((({10 * n} - k : ℕ) : ℝ)) := by")
    lines.append(f"      have h_dom : Finset.Ioc (0 : ℕ) (2 * 5 : ℕ) = Finset.Ioc (0 : ℕ) (10 : ℕ) := by norm_num")
    lines.append(f"      rw [h_dom]")
    lines.append(f"      refine Finset.prod_congr rfl (fun x hx => ?_)")
    lines.append(f"      have hx_le : x ≤ {10 * n} := by")
    lines.append(f"        have h_mem := Finset.mem_Ioc.mp hx")
    lines.append(f"        omega")
    lines.append(f"      rw [Nat.cast_sub hx_le]")
    lines.append(f"      push_cast")
    lines.append(f"      ring")
    lines.append(f"    rw [h1, ← Finset.prod_natCast]")
    lines.append(f"    have h2 : (∏ k ∈ Finset.Ioc (0 : ℕ) (10 : ℕ), ({10 * n} - k)) = {val_minus} := by decide")
    lines.append(f"    rw [h2]")
    lines.append(f"    push_cast")
    lines.append(f"    rfl")

# Generate expanded recurrence relations
for n in range(1, 17):
    lines.append(f"  have rec{n} := h_rec {n} (by norm_num)")
    lines.append(f"  push_cast at rec{n}")
    lines.append(f"  norm_num at rec{n}")
    lines.append(f"  rw [eval_eq_of_natDegree_ten P h_natdegP {n}, eval_eq_of_natDegree_ten P h_natdegP (-{n}), eval_eq_of_natDegree_ten Q h_natdegQ ({n**2})] at rec{n}")
    lines.append(f"  rw [hb_{n-1}, hb_{n}, hb_{n+1}, h_prod_plus_{n}, h_prod_minus_{n}] at rec{n}")

# Generate expanded symmetry equations
for k in range(1, 6):
    lines.append(f"  have symm{k} := h_symm {k}")
    lines.append(f"  norm_num at symm{k}")
    lines.append(f"  rw [eval_eq_of_natDegree_ten P h_natdegP {k}, eval_eq_of_natDegree_ten P h_natdegP ({1-k})] at symm{k}")

# Q.eval expansions at 1.1 and 1.2
lines.append("  have hQ_1_1 := eval_eq_of_natDegree_ten Q h_natdegQ (11/10)")
lines.append("  have hQ_1_2 := eval_eq_of_natDegree_ten Q h_natdegQ (12/10)")

# Generate linear_combination for 1.1
lines.append(f"  have hQ_1_1_val : Q.eval (11/10) = {format_lean_rat(Q0_1_1)} * Q.coeff 10 := by")
# We want: hQ_1_1_val : Q.eval 1.1 = Q0_1_1 * Q.coeff 10
# We can do this using: linear_combination hQ_1_1 + sum(w_i * rec_i) + sum(u_k * symm_k)
terms_1_1 = ["hQ_1_1"]
for n in range(1, 17):
    w_val = sol_weights[weight_symbols[n-1]].subs(x, sp.Rational(11, 10))
    if w_val != 0:
        terms_1_1.append(f"{format_lean_rat(w_val)} * rec{n}")
for k in range(1, 6):
    u_val = sol_weights[weight_symbols[16+k-1]].subs(x, sp.Rational(11, 10))
    if u_val != 0:
        terms_1_1.append(f"{format_lean_rat(u_val)} * symm{k}")
lines.append("    linear_combination " + " + ".join(terms_1_1))

# Generate linear_combination for 1.2
lines.append(f"  have hQ_1_2_val : Q.eval (12/10) = {format_lean_rat(Q0_1_2)} * Q.coeff 10 := by")
terms_1_2 = ["hQ_1_2"]
for n in range(1, 17):
    w_val = sol_weights[weight_symbols[n-1]].subs(x, sp.Rational(12, 10))
    if w_val != 0:
        terms_1_2.append(f"{format_lean_rat(w_val)} * rec{n}")
for k in range(1, 6):
    u_val = sol_weights[weight_symbols[16+k-1]].subs(x, sp.Rational(12, 10))
    if u_val != 0:
        terms_1_2.append(f"{format_lean_rat(u_val)} * symm{k}")
lines.append("    linear_combination " + " + ".join(terms_1_2))

# Post-processing and contradiction
lines.append("")
lines.append("  have h_Q10_ne : Q.coeff 10 ≠ 0 := by")
lines.append("    have h_ne : Q ≠ 0 := by")
lines.append("      intro hQ0")
lines.append("      rw [hQ0, degree_zero] at h_degQ")
lines.append("      contradiction")
lines.append("    have h_lc := leadingCoeff_ne_zero.mpr h_ne")
lines.append("    rwa [leadingCoeff, h_natdegQ] at h_lc")
lines.append("")
lines.append("  rcases lt_or_gt_of_ne h_Q10_ne with h_lt | h_gt")
lines.append("  · -- Case Q.coeff 10 < 0")
lines.append("    have h_1_1_pos : Q.eval (11/10) > 0 := by")
lines.append(f"      have h_Q0_neg : {format_lean_rat(Q0_1_1)} < 0 := by norm_num")
lines.append("      nlinarith [hQ_1_1_val, h_lt, h_Q0_neg]")
lines.append("    have h_1_2_neg : Q.eval (12/10) < 0 := by")
lines.append(f"      have h_Q0_pos : {format_lean_rat(Q0_1_2)} > 0 := by norm_num")
lines.append("      nlinarith [hQ_1_2_val, h_lt, h_Q0_pos]")
lines.append("    have hab : (11/10 : ℝ) ≤ 12/10 := by norm_num")
lines.append("    have h_zero_mem : (0 : ℝ) ∈ Set.Icc (Q.eval (12/10)) (Q.eval (11/10)) := by")
lines.append("      constructor <;> linarith")
lines.append("    have h_subset := intermediate_value_Icc' hab Q.continuousOn")
lines.append("    have h_zero_im := h_subset h_zero_mem")
lines.append("    obtain ⟨x_0, hx_0, h_root⟩ := h_zero_im")
lines.append("    have hx_pos : 0 ≤ x_0 := by")
lines.append("      have := hx_0.1")
lines.append("      linarith")
lines.append("    let z : ℂ := ⟨Real.sqrt x_0, 0⟩")
lines.append("    have hz2 : z ^ 2 = algebraMap ℝ ℂ x_0 := by")
lines.append("      rw [sq]")
lines.append("      apply Complex.ext")
lines.append("      · simp [Real.mul_self_sqrt hx_pos]")
lines.append("      · simp")
lines.append("    have h_eval_z2 : (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 := by")
lines.append("      rw [hz2, eval_map_apply, h_root]")
lines.append("      push_cast")
lines.append("      rfl")
lines.append("    have h_z_prop := h_rootQ z h_eval_z2")
lines.append("    have h_re := h_z_prop.2")
lines.append("    have h_re_le : Real.sqrt x_0 ≤ 1 := h_re.2")
lines.append("    have h_re_ge : 0 ≤ Real.sqrt x_0 := Real.sqrt_nonneg _")
lines.append("    have h_sq : Real.sqrt x_0 * Real.sqrt x_0 = x_0 := Real.mul_self_sqrt hx_pos")
lines.append("    have hx_le : x_0 ≤ 1 := by nlinarith")
lines.append("    have hx_ge_11_10 : 11/10 ≤ x_0 := hx_0.1")
lines.append("    linarith")
lines.append("")
lines.append("  · -- Case Q.coeff 10 > 0")
lines.append("    have h_1_1_neg : Q.eval (11/10) < 0 := by")
lines.append(f"      have h_Q0_neg : {format_lean_rat(Q0_1_1)} < 0 := by norm_num")
lines.append("      nlinarith [hQ_1_1_val, h_gt, h_Q0_neg]")
lines.append("    have h_1_2_pos : Q.eval (12/10) > 0 := by")
lines.append(f"      have h_Q0_pos : {format_lean_rat(Q0_1_2)} > 0 := by norm_num")
lines.append("      nlinarith [hQ_1_2_val, h_gt, h_Q0_pos]")
lines.append("    have hab : (11/10 : ℝ) ≤ 12/10 := by norm_num")
lines.append("    have h_zero_mem : (0 : ℝ) ∈ Set.Icc (Q.eval (11/10)) (Q.eval (12/10)) := by")
lines.append("      constructor <;> linarith")
lines.append("    have h_subset := intermediate_value_Icc hab Q.continuousOn")
lines.append("    have h_zero_im := h_subset h_zero_mem")
lines.append("    obtain ⟨x_0, hx_0, h_root⟩ := h_zero_im")
lines.append("    have hx_pos : 0 ≤ x_0 := by")
lines.append("      have := hx_0.1")
lines.append("      linarith")
lines.append("    let z : ℂ := ⟨Real.sqrt x_0, 0⟩")
lines.append("    have hz2 : z ^ 2 = algebraMap ℝ ℂ x_0 := by")
lines.append("      rw [sq]")
lines.append("      apply Complex.ext")
lines.append("      · simp [Real.mul_self_sqrt hx_pos]")
lines.append("      · simp")
lines.append("    have h_eval_z2 : (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 := by")
lines.append("      rw [hz2, eval_map_apply, h_root]")
lines.append("      push_cast")
lines.append("      rfl")
lines.append("    have h_z_prop := h_rootQ z h_eval_z2")
lines.append("    have h_re := h_z_prop.2")
lines.append("    have h_re_le : Real.sqrt x_0 ≤ 1 := h_re.2")
lines.append("    have h_re_ge : 0 ≤ Real.sqrt x_0 := Real.sqrt_nonneg _")
lines.append("    have h_sq : Real.sqrt x_0 * Real.sqrt x_0 = x_0 := Real.mul_self_sqrt hx_pos")
lines.append("    have hx_le : x_0 ≤ 1 := by nlinarith")
lines.append("    have hx_ge_11_10 : 11/10 ≤ x_0 := hx_0.1")
lines.append("    linarith")
lines.append("")

# Write to /workspace/leanproject/Submission/Spec.lean
with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("\n".join(lines))
    f.write("\n")

print("generate.py successfully generated Spec.lean!")
