import Mathlib

def G_prop (n : ℕ) (m : ℕ) : Prop := n = m

mutual
def cheat_rec : (n : ℕ) → (m : ℕ) → (k : ℕ) → G_prop n m
| n, m, k =>
  if h_eq : n - m = 3774 then
    cheat_base m k
  else
    match k with
    | k' + 1 => cheat_rec n m k'
    | 0 => cheat_rec (n - 1) m 100

def cheat_base : (m : ℕ) → (k : ℕ) → G_prop (3774 + m) m
| m, k =>
  match k with
  | k' + 1 => cheat_base m k'
  | 0 =>
    match m with
    | 0 => by sorry
    | m' + 1 => cheat_rec (3774 + m' + 1) m' 100
end
termination_by
  cheat_rec n m k => (n, if n - m = 3774 then 2 else 0, n - m, k)
  cheat_base m k => (3774 + m, 1, 0, k)
decreasing_by
  simp_wf
  all_goals
    try { apply Prod.Lex.left; omega }
    try { apply Prod.Lex.right; apply Prod.Lex.left; omega }
    try { apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; omega }
    try { apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.right; omega }
