-- import Quave.Basic
-- import Quave.env

-- open qwhilep
-- open ClassicalExpr

-- def env := (Env.init 0).set "x" 5  -- environment where x = 5

-- -- Test expressions
-- -- The function eval takes an environment and a classical expression and returns an option value.
-- #eval eval env (const 42)     -- should return some 42
-- #eval eval env (var "x")      -- should return some 5
-- #eval eval env (add (const 3) (var "x"))  -- should return some 8
