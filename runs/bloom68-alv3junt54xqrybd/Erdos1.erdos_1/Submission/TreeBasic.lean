import Submission.Basic

/-! Finite unmerged binary trees and the integral path-feedback construction. -/

namespace ErdosDSS.TreeCode

open scoped BigOperators

/-- `true` marks an absorbing leaf; `false` marks a timeout leaf. -/
inductive Tree where
  | tip (absorbed : Bool)
  | fork (left right : Tree)
  deriving DecidableEq, Repr

namespace Tree

noncomputable section

def Leaf : Tree → Type
  | tip _ => Unit
  | fork l r => Leaf l ⊕ Leaf r

instance leafFintype (t : Tree) : Fintype (Leaf t) := by
  induction t with
  | tip a => exact inferInstanceAs (Fintype Unit)
  | fork l r hl hr => exact inferInstanceAs (Fintype (Leaf l ⊕ Leaf r))

instance leafDecidableEq (t : Tree) : DecidableEq (Leaf t) := by
  induction t with
  | tip a => exact inferInstanceAs (DecidableEq Unit)
  | fork l r hl hr => exact inferInstanceAs (DecidableEq (Leaf l ⊕ Leaf r))

def root : (t : Tree) → Leaf t
  | tip _ => ()
  | fork l _ => Sum.inl (root l)

def isNode : Tree → Bool
  | tip _ => false
  | fork _ _ => true

def absorbed : (t : Tree) → Leaf t → Bool
  | tip a, _ => a
  | fork l r, Sum.inl i => absorbed l i
  | fork l r, Sum.inr i => absorbed r i

def hasAbs : Tree → Bool
  | tip a => a
  | fork l r => hasAbs l || hasAbs r

def hasTime : Tree → Bool
  | tip a => !a
  | fork l r => hasTime l || hasTime r

/-- A chosen absorber whenever the tree has one. -/
def firstAbs : (t : Tree) → Leaf t
  | tip _ => ()
  | fork l r => if hasAbs l then Sum.inl (firstAbs l) else Sum.inr (firstAbs r)

/-- The timeout in the first cherry.  On a mixed tree every query subtree
has a cherry, and every cherry has exactly one timeout. -/
def firstCherry : (t : Tree) → Leaf t
  | tip _ => ()
  | fork l r =>
    if isNode l then Sum.inl (firstCherry l)
    else if isNode r then Sum.inr (firstCherry r)
    else if hasAbs l then Sum.inr (root r) else Sum.inl (root l)

/-- The rightmost timeout whenever one exists. -/
def lastTime : (t : Tree) → Leaf t
  | tip _ => ()
  | fork l r => if hasTime r then Sum.inr (lastTime r) else Sum.inl (lastTime l)

def depth : (t : Tree) → Leaf t → ℕ
  | tip _, _ => 0
  | fork l r, Sum.inl i => depth l i + 1
  | fork l r, Sum.inr i => depth r i + 1

def nodes : Tree → ℕ
  | tip _ => 0
  | fork l r => 1 + nodes l + nodes r

/-- The sole structural restriction: every cherry is absorbing/timeout,
rather than absorbing/absorbing or timeout/timeout. -/
def Mixed : Tree → Prop
  | tip _ => True
  | fork l r => Mixed l ∧ Mixed r ∧
    (isNode l = false → isNode r = false → hasAbs l ≠ hasAbs r)

/-- Square Haar/path matrix.  Its rows are indexed by leaves: the first
leaf labels the distinguished root row, and recursively the first leaf
of the right child labels the query at a fork. -/
def path : (t : Tree) → Matrix (Leaf t) (Leaf t) ℤ
  | tip _ => fun _ _ => 1
  | fork l r => fun i j =>
    match i with
    | Sum.inl i =>
      if i = root l then 1 else
        match j with
        | Sum.inl j => path l i j
        | Sum.inr _ => 0
    | Sum.inr i =>
      if i = root r then
        match j with
        | Sum.inl _ => 1
        | Sum.inr _ => -1
      else
        match j with
        | Sum.inl _ => 0
        | Sum.inr j => path r i j

/-- Whole absorbing-suffix feedback.  At a fork with two query children,
the first cherry-timeout of the right child feeds the complete query
suffix to the chosen absorbing leaf of the left child. -/
def feedback : (t : Tree) → Matrix (Leaf t) (Leaf t) ℤ
  | tip _ => 0
  | fork l r => fun i j =>
    match i with
    | Sum.inl i =>
      if i = root l then 0 else
        match j with
        | Sum.inl j => feedback l i j
        | Sum.inr j =>
          if isNode l && isNode r && decide (j = firstCherry r)
          then path l i (firstAbs l) else 0
    | Sum.inr i =>
      if i = root r then 0 else
        match j with
        | Sum.inl _ => 0
        | Sum.inr j => feedback r i j

def core (t : Tree) : Matrix (Leaf t) (Leaf t) ℤ := path t + feedback t

/-- Increased timeout roots, with a nonnegative even adjustment on the
rightmost timeout column. -/
def adjusted (t : Tree) (u : ℕ) : Matrix (Leaf t) (Leaf t) ℤ :=
  fun i j => core t i j + if i = root t then
    (if absorbed t j then 0 else 1) + (if j = lastTime t then 2 * (u : ℤ) else 0)
    else 0

/-- Conditional fair timeout probability. -/
def tau : Tree → ℚ
  | tip a => if a then 0 else 1
  | fork l r => (tau l + tau r) / 2

/-- Conditional probability of a cherry-timeout. -/
def eta : Tree → ℚ
  | tip _ => 0
  | fork l r => if isNode l || isNode r then (eta l + eta r) / 2 else 1 / 2

/-- Transformed mass at the first cherry-timeout. -/
def z : Tree → ℚ
  | tip _ => 0
  | fork l r =>
    if isNode l then (z l * (1 + if isNode r then z r else 0)) / 2
    else if isNode r then z r / 2 else 1 / 2

/-- Transformed timeout mass for the inverse root equation. -/
def f : Tree → ℚ
  | tip a => if a then 0 else 1
  | fork l r => (f l + f r + if isNode l && isNode r then z r * f l else 0) / 2

/-- Transformed total mass of all cherry-timeouts. -/
def g : Tree → ℚ
  | tip _ => 0
  | fork l r =>
    if isNode l || isNode r then
      (g l + g r + if isNode l && isNode r then z r * g l else 0) / 2
    else 1 / 2

end

end Tree

end ErdosDSS.TreeCode
