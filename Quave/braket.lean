import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Bra-Ket Notation for Quantum States

This module implements the bra-ket notation (Dirac notation) for quantum states.
It provides the fundamental structures and operations for quantum state vectors.

## Main definitions

* `Ket` - A normalized column vector representing a quantum state
* `Bra` - The dual vector of a Ket (conjugate transpose)
* `dot` - Inner product between a Bra and a Ket

## Notation

* `|ψ⟩` - Represents a Ket state
* `⟨φ|` - Represents a Bra state
* `⟨φ‖ψ⟩` - Represents the inner product between Bra φ and Ket ψ

## Implementation notes

States are represented as functions from a finite type to complex numbers,
following the convention in `Matrix` of vectors as simple functions.
Both Bra and Ket vectors are required to be normalized (norm = 1).
-/

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open Complex
open scoped Matrix ComplexOrder

/-! ### Basic definitions -/

noncomputable section

section BraKet
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
  normalized' : ∑ x, ‖vec x‖^2 = 1

end BraKet

/-! ### Conversion between Bra and Ket -/

namespace Ket
variable (d : Type*) [Fintype d]

/-- Convert a Ket to its dual Bra by taking the complex conjugate of each component. -/
def to_bra (ψ : Ket d) : Bra d where
  vec := fun x => conj (ψ.vec x)
  normalized' := by
    rw [← ψ.normalized']
    congr
    funext x
    rw [Complex.norm_eq_abs, Complex.abs_conj]
    rfl
end Ket

namespace Bra
variable (d : Type*) [Fintype d]

/-- Convert a Bra to its dual Ket by taking the complex conjugate of each component. -/
def to_ket (φ : Bra d) : Ket d where
  vec := fun x => conj (φ.vec x)
  normalized' := by
    rw [← φ.normalized']
    congr
    funext x
    rw [Complex.norm_eq_abs, Complex.abs_conj]
    rfl
end Bra

/-! ### Notation and basic operations -/

namespace braket

/-- Notation for Bra vectors using ⟨ψ| -/
scoped notation:max "〈" ψ:90 "∣" => (ψ : Bra _)

/-- Notation for Ket vectors using |ψ⟩ -/
scoped notation:max "∣" ψ:90 "〉" => (ψ : Ket _)

variable {d : Type*} [Fintype d]

/-- Allow using Ket vectors as functions -/
instance instFunLikeKet : FunLike (Ket d) d ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [Ket.mk.injEq]

/-- Allow using Bra vectors as functions -/
instance instFunLikeBra : FunLike (Bra d) d ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [Bra.mk.injEq]

/-- Inner product between a Bra and a Ket vector -/
def dot (φ : Bra d) (ψ : Ket d) : ℂ := ∑ x, (φ x) * (ψ x)

/-- Notation for inner product using ⟨φ‖ψ⟩ -/
scoped notation "〈" φ:90 "‖" ψ:90 "〉" => dot (φ : Bra _) (ψ : Ket _)

end braket