import Quave.qwhilep

open qwhilep

def env := (Env.init 0).set "x" 5  -- environment where x = 5

-- Test expressions
#eval (ClassicalExpr.const 42).eval env        -- should return some 42
#eval (ClassicalExpr.var "x").eval env         -- should return some 5
#eval (ClassicalExpr.add (ClassicalExpr.const 3) (ClassicalExpr.var "x")).eval env  -- should return some 8
