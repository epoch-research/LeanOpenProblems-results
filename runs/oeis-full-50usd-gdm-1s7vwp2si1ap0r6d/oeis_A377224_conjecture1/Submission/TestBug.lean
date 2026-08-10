inductive LeanBug : Type where
| mk : (LeanBug → False) → LeanBug
