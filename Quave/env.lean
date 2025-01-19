import Quave.Basic

open qwhilep

/-- A context in which the program evaluates its variables and expressions-/
def Env := String → Value


namespace Env

/-- Set a value in an environment -/
def set (x : String) (v : Value) (σ : Env) : Env :=
  fun y => if x == y then v else σ y -- If x == y, return v, else return σ y

/-- Look up a value in an environment -/
def get (x : String) (σ : Env) : Value :=
  σ x -- Return the value of x in σ

/-- Initialize an environment, setting all uninitialized memory to `i` -/
def init (i : Value) : Env := fun _ => i -- Return i for all variables

/-- Initialize an environment with all memory set to 0 -/
@[simp]
theorem get_init (v : Value) (x : String) : (Env.init v).get x = v := by rfl

/-- Set a value in an environment, then look it up -/
@[simp]
theorem get_set_same (v : Value) (x : String) {σ : Env} : (σ.set x v).get x = v := by
  simp [get, set]

/-- Set a value in an environment, then look up a different value -/
@[simp]
theorem get_set_different (v : Value) (x y : String) {σ : Env} : x ≠ y → (σ.set x v).get y = σ.get y := by
  intros
  simp [get, set, *]

end Env





namespace ClassicalExpr

/-- Evaluate a classical expression in an environment.
    Returns `none` if the expression contains an undefined variable.
    Otherwise, returns `some v`, where `v` is the value of the expression.
    -/
def eval (σ : Env) : ClassicalExpr → Option Value
  | .const i => some i
  | .var x => σ.get x
  | .add e₁ e₂ =>
      match (eval σ e₁, eval σ e₂) with
      | (some v₁, some v₂) => some (v₁ + v₂)
      | _ => none

end ClassicalExpr
