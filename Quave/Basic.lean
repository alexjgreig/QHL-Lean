namespace qwhilep

/-
Value represents the underlying type
-/
abbrev Value := Int

/-
ClassicalExpr represents classical (non-quantum) arithmetic expressions. These expressions are:
    - Constants
    - Variables (referenced by name)
    - Binary arithmetic operations (addition, subtraction, multiplication, division)
-/
inductive ClassicalExpr where
    | const (i: Value): ClassicalExpr
    | var (name: String): ClassicalExpr
    | add (e₁ e₂: ClassicalExpr): ClassicalExpr
    | sub (e₁ e₂: ClassicalExpr): ClassicalExpr
    | mul (e₁ e₂: ClassicalExpr): ClassicalExpr
deriving Repr, DecidableEq

/-
BooleanExpr represents classical (non-quantum) boolean expressions. These expressions are:
    - Boolean constants (True, False)
    - Comparison expressions (equalities, inequalities)
    - Boolean connectives (not, and, or)
-/
inductive BooleanExpr where
    | True: BooleanExpr
    | False: BooleanExpr
    | eq (e₁ e₂: ClassicalExpr): BooleanExpr
    | le (e₁ e₂: ClassicalExprExpr): BooleanExpr
    | leq (e₁ e₂: ClassicalExpr): BooleanExpr
    | ge (e₁ e₂: ClassicalExpr): BooleanExpr
    | geq (e₁ e₂: ClassicalExpr): BooleanExpr
    | not (e: BooleanExpr): BooleanExpr
    | and (e₁ e₂: BooleanExpr): BooleanExpr
    | or (e₁ e₂: BooleanExpr): BooleanExpr
-- deriving Repr, DecidableEq

/-
Stmt represents program statements in the qwhile+ language. Currently supports:
    - skip (no operation)
    - assignment
    - sequential composition
    - if-then-else
    - while
-/
inductive Stmt where
    | skip: Stmt
    | assign (name: String) (val: ClassicalExpr): Stmt
    | seq (s₁ s₂: Stmt): Stmt
    | if (b: BooleanExpr) (s₁ s₂: Stmt): Stmt
    | while (b: BooleanExpr) (s: Stmt): Stmt
-- deriving Repr, DecidableEq

end qwhilep
