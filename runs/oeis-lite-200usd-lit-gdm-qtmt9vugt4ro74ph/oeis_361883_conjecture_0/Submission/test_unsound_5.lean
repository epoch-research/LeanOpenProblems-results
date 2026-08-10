inductive Box (α : Type) : Type
  | mk : α → Box α

inductive Bad : Type
  | mk : (Box Bad → PEmpty) → Bad
