namespace qwhilep

/-- Values stored in memory - integers -/
abbrev Value := Int

/-- ClassicalExpr represents classical (non-quantum) arithmetic expressions.
    These expressions are:
    - Integer constants
    - Variables (referenced by name)
    - Binary arithmetic operations (addition, subtraction, multiplication, division) -/
inductive ClassicalExpr where
| const (i: Value)  -- Don't know if we need to have more types
| var (name: String) -- I guess we can use strings for variable names
| add (e₁ e₂: ClassicalExpr) -- Inductive definition
-- More constructors to be added
deriving Repr, DecidableEq -- Automatically derive pretty-printing and equality checking

/-- Stmt represents program statements in the qwhile+ language.
    Currently supports:
    - skip (no operation)
    - assignment
    - sequential composition
    More constructors will be added for quantum operations -/
inductive Stmt where
| skip
| assign (name: String) (val: ClassicalExpr)
| seq (stmt₁ stmt₂: Stmt)
-- More constructors to be added
deriving Repr, DecidableEq

end qwhilep
