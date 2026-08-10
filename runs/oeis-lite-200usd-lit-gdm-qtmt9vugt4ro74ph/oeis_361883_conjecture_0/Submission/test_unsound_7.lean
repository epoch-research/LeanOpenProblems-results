inductive MyEmpty : Type 0

inductive Box (α : Type 0) : Type 0
  | mk : α → Box α

inductive Bad : Type 0
  | mk : (Box Bad → MyEmpty) → Bad
