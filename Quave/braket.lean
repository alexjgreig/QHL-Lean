import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open Complex
open scoped Matrix ComplexOrder

noncomputable section

section
variable (d : Type*) [Fintype d]

/-- A ket as a vector of unit norm. We follow the convention in `Matrix` of vectors as simple functions
 from a Fintype. Kets are distinctly not a vector space in our notion, as they represent only normalized
 states and so cannot (in general) be added or scaled. -/
structure Ket where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖^2 = 1

/-- A bra is definitionally identical to a `Ket`, but are separate to avoid complex conjugation confusion.
 They can be interconverted with the adjoint: `Ket.to_bra` and `Bra.to_ket` -/
structure Bra where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖^2 =1

end section


namespace braket

scoped notation:max "〈" ψ:90 "∣" => (ψ : Bra _)

scoped notation:max "∣" ψ:90 "〉" => (ψ : Ket _)

variable {d : Type*} [Fintype d]

instance instFunLikeKet : FunLike (Ket d) d ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [Ket.mk.injEq]

instance instFunLikeBra : FunLike (Bra d) d ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [Bra.mk.injEq]

def dot (φ : Bra d) (ψ : Ket d) : ℂ := ∑ x, (φ x) * (ψ x)

scoped notation "〈" φ:90 "‖" ψ:90 "〉" => dot (φ : Bra _) (ψ : Ket _)

end braket
