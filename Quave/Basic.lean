import Lean

open Lean Meta Syntax Macro Elab

namespace qwhilep

inductive ArithUnOpt where
  | neg : ArithUnOpt

inductive ArithBinOpt where
  | add : ArithBinOpt
  | sub : ArithBinOpt
  | mul : ArithBinOpt
  | div : ArithBinOpt
  | mod : ArithBinOpt

inductive ArithExpr where
  | int : Nat → ArithExpr
  | var : String → ArithExpr
  | un : ArithUnOpt → ArithExpr → ArithExpr
  | bin : ArithBinOpt → ArithExpr → ArithExpr → ArithExpr

declare_syntax_cat arith_un_opt
  syntax "-" : arith_un_opt

declare_syntax_cat arith_bin_opt
  syntax "+" : arith_bin_opt
  syntax "-" : arith_bin_opt
  syntax "*" : arith_bin_opt
  syntax "/" : arith_bin_opt
  syntax "%" : arith_bin_opt

declare_syntax_cat arith_expr
  syntax num : arith_expr
  syntax str : arith_expr
  syntax ident : arith_expr
  syntax arith_un_opt arith_expr : arith_expr
  syntax arith_expr arith_bin_opt arith_expr : arith_expr
  syntax arith_expr arith_bin_opt arith_expr : arith_expr
  syntax "(" arith_expr ")" : arith_expr
  syntax "<[" term "]>" : arith_expr

def elab_arith_un_opt : Syntax → MetaM Expr
  | `(arith_un_opt| -) => return .const ``ArithUnOpt.neg []
  | _ => throwUnsupportedSyntax

def elab_arith_bin_opt : Syntax → MetaM Expr
  | `(arith_bin_opt| +) => return .const ``ArithBinOpt.add []
  | `(arith_bin_opt| -) => return .const ``ArithBinOpt.sub []
  | `(arith_bin_opt| *) => return .const ``ArithBinOpt.mul []
  | `(arith_bin_opt| /) => return .const ``ArithBinOpt.div []
  | `(arith_bin_opt| %) => return .const ``ArithBinOpt.mod []
  | _ => throwUnsupportedSyntax

partial def elab_arith_expr : Syntax → MetaM Expr
  | `(arith_expr| $n:num) => mkAppM ``ArithExpr.int #[mkNatLit n.getNat]
  | `(arith_expr| $i:ident) => mkAppM ``ArithExpr.var #[mkStrLit i.getId.toString]
  | `(arith_expr| $o:arith_un_opt $e:arith_expr) => do
    let o ← elab_arith_un_opt o
    let e ← elab_arith_expr e
    mkAppM ``ArithExpr.un #[o, e]
  | `(arith_expr| $e₁:arith_expr $o:arith_bin_opt $e₂:arith_expr) => do
    let o ← elab_arith_bin_opt o
    let e₁ ← elab_arith_expr e₁
    let e₂ ← elab_arith_expr e₂
    mkAppM ``ArithExpr.bin #[o, e₁, e₂]
  | `(arith_expr| ($e:arith_expr)) => elab_arith_expr e
  | _ => throwUnsupportedSyntax

elab "test1 " e:arith_expr : term => elab_arith_expr e

#reduce test1 -((3 * 4) + 5)





inductive BoolUnOpt where
  | not : BoolUnOpt

inductive BoolBinOpt where
  | eq : BoolBinOpt
  | ne : BoolBinOpt
  | le : BoolBinOpt
  | ge : BoolBinOpt
  | lt : BoolBinOpt
  | gt : BoolBinOpt
  | and : BoolBinOpt
  | or : BoolBinOpt

inductive BoolExpr where
  | True : BoolExpr
  | False : BoolExpr
  | var : String → BoolExpr
  | un : BoolUnOpt → BoolExpr → BoolExpr
  | bin : BoolBinOpt → BoolExpr → BoolExpr → BoolExpr

declare_syntax_cat bool_un_opt
  syntax "!" : bool_un_opt

declare_syntax_cat bool_bin_opt
  syntax "==" : bool_bin_opt
  syntax "!=" : bool_bin_opt
  syntax "<" : bool_bin_opt
  syntax ">" : bool_bin_opt
  syntax "<=" : bool_bin_opt
  syntax ">=" : bool_bin_opt
  syntax "&&" : bool_bin_opt
  syntax "||" : bool_bin_opt

declare_syntax_cat bool_expr
  syntax str : bool_expr
  syntax ident : bool_expr
  syntax bool_un_opt bool_expr : bool_expr
  syntax bool_expr bool_bin_opt bool_expr : bool_expr
  syntax bool_expr bool_bin_opt bool_expr : bool_expr
  syntax "(" bool_expr ")" : bool_expr
  syntax "<[" term "]>" : bool_expr

def elab_bool_un_opt : Syntax → MetaM Expr
  | `(bool_un_opt| !) => return .const ``BoolUnOpt.not []
  | _ => throwUnsupportedSyntax

def elab_bool_bin_opt : Syntax → MetaM Expr
  | `(bool_bin_opt| ==) => return .const ``BoolBinOpt.eq []
  | `(bool_bin_opt| !=) => return .const ``BoolBinOpt.ne []
  | `(bool_bin_opt| <) => return .const ``BoolBinOpt.le []
  | `(bool_bin_opt| >) => return .const ``BoolBinOpt.ge []
  | `(bool_bin_opt| <=) => return .const ``BoolBinOpt.lt []
  | `(bool_bin_opt| >=) => return .const ``BoolBinOpt.gt []
  | `(bool_bin_opt| &&) => return .const ``BoolBinOpt.and []
  | `(bool_bin_opt| ||) => return .const ``BoolBinOpt.or []
  | _ => throwUnsupportedSyntax

partial def elab_bool_expr : Syntax → MetaM Expr
  | `(bool_expr| True) => mkAppM ``BoolExpr.True #[]
  | `(bool_expr| False) => mkAppM ``BoolExpr.False #[]
  | `(bool_expr| $i:ident) => mkAppM ``BoolExpr.var #[mkStrLit i.getId.toString]
  | `(bool_expr| $o:bool_un_opt $e:bool_expr) => do
    let o ← elab_bool_un_opt o
    let e ← elab_bool_expr e
    mkAppM ``BoolExpr.un #[o, e]
  | `(bool_expr| $e₁:bool_expr $o:bool_bin_opt $e₂:bool_expr) => do
    let o ← elab_bool_bin_opt o
    let e₁ ← elab_bool_expr e₁
    let e₂ ← elab_bool_expr e₂
    mkAppM ``BoolExpr.bin #[o, e₁, e₂]
  | `(bool_expr| ($e:bool_expr)) => elab_bool_expr e
  | _ => throwUnsupportedSyntax

elab "test2 " e:bool_expr : term => elab_bool_expr e

#reduce test2 a && !True





inductive Program where
  | skip : Program
  | assign : String → ArithExpr → Program
  | seq : Program → Program → Program
  | if : BoolExpr → Program → Program → Program
  | while : BoolExpr → Program → Program

declare_syntax_cat program
  syntax "skip" : program
  syntax ident "=" arith_expr : program
  syntax program ";" program : program
  syntax "if" bool_expr "then" program "else" program "fi" : program
  syntax "while" bool_expr "do" program "od" : program

partial def elab_program : Syntax → MetaM Expr
  | `(program| skip) => return .const ``Program.skip []
  | `(program| $i:ident = $e:arith_expr) => do
    let i : Expr := mkStrLit i.getId.toString
    let e ← elab_arith_expr e
    mkAppM ``Program.assign #[i, e]
  | `(program| $p₁:program ; $p₂:program) => do
    let p₁ ← elab_program p₁
    let p₂ ← elab_program p₂
    mkAppM ``Program.seq #[p₁, p₂]
  | `(program| if $b:bool_expr then $p₁:program else $p₂:program fi) => do
    let b ← elab_bool_expr b
    let p₁ ← elab_program p₁
    let p₂ ← elab_program p₂
    mkAppM ``Program.if #[b, p₁, p₂]
  | `(program| while $b:bool_expr do $p:program od) => do
    let b ← elab_bool_expr b
    let p ← elab_program p
    mkAppM ``Program.while #[b, p]
  | _ => throwUnsupportedSyntax

elab ">>" p:program "<<" : term => elab_program p

#reduce >>
a = 5;
if (True && True) then c = 5 else a = a + 1 fi;
b = 10
<<

-- syntax "`[ArithExpr|" arith_expr "]" : term

-- macro_rules
--   | `(`[ArithExpr| $n:num]) => `(ArithExpr.int $n)
--   | `(`[ArithExpr| $x:ident]) => `(ArithExpr.var $(Lean.quote (toString x.getId)))
--   | `(`[ArithExpr| $s:str]) => `(ArithExpr.var $s)
--   | `(`[ArithExpr| $x + $y]) => `(ArithExpr.bin ArithBinOpt.add `[ArithExpr| $x] `[ArithExpr| $y])
--   | `(`[ArithExpr| $x - $y]) => `(ArithExpr.bin ArithBinOpt.sub `[ArithExpr| $x] `[ArithExpr| $y])
--   | `(`[ArithExpr| $x * $y]) => `(ArithExpr.bin ArithBinOpt.mul `[ArithExpr| $x] `[ArithExpr| $y])
--   | `(`[ArithExpr| $x / $y]) => `(ArithExpr.bin ArithBinOpt.div `[ArithExpr| $x] `[ArithExpr| $y])
--   | `(`[ArithExpr| $x % $y]) => `(ArithExpr.bin ArithBinOpt.mod `[ArithExpr| $x] `[ArithExpr| $y])
--   | `(`[ArithExpr| ($x)]) => `(`[ArithExpr| $x])
--   | `(`[ArithExpr| <[$e:term]>]) => pure e

end qwhilep
