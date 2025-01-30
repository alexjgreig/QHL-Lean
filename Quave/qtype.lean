import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Lean

open BigOperators Complex

namespace qtype

/-- Complex conjugation of a number `z` in ℂ. -/
def conj (z : ℂ) : ℂ := ⟨z.re, -z.im⟩

/-- Inner product for two vectors in a Hilbert space.
- `dim` is the dimension of the Hilbert space.
- `v1` and `v2` are functions from `Fin dim → ℂ`.
- The inner product is the sum of the product of the elements of the two vectors.
- The product of the elements is multiplied by the complex conjugate of the second vector.
-/
def inner_product {dim : Nat} (v1 v2 : Fin dim → ℂ) : ℂ :=
  ∑ k, v1 k * conj (v2 k)

/-- A struct consist of three fields:
- `dim` is the dimension of the Hilbert space.
- `basis` is a function that maps an index (from `Fin dim`) to a vector.
  - Each vector is also a function from `Fin dim → ℂ`.
- `is_orthonormal` is a proof that ensures the basis is orthonormal.
  - The basis is orthonormal if the inner product of two vectors is 1 if the indices are the same, and 0 otherwise.
 -/
structure HilbertSpace where
  dim : Nat
  basis : Fin dim → (Fin dim → ℂ)  -- Maps an index to a basis vector
  is_orthonormal : ∀ (i j : Fin dim),
    inner_product (basis i) (basis j) = if i = j then 1 else 0

/-- A function to create a Hilbert space with canonical basis vectors. -/
def makeHilbertSpace (d : Nat) : HilbertSpace :=
{ dim := d,
  basis := fun i j => if j == i then (1 : ℝ) else 0,
  is_orthonormal := by
    intro i j
    by_cases h : i = j
    case pos =>
      -- Case: i = j
      rw [h] -- Replace i with j
      simp only [inner_product, Finset.sum_ite_eq, Pi.zero_apply, Pi.one_apply]
      simp [if_pos rfl, conj]
      exact rfl
    case neg =>
      -- Case: i ≠ j
      simp only [inner_product, Finset.sum_ite_eq, Pi.zero_apply, Pi.one_apply]
      simp [if_neg h, conj]
      exact rfl
}

/-- A simple Hilbert space for a qubit (dimension 2). -/
def Hq : HilbertSpace := makeHilbertSpace 2

/-- A structure representing a quantum variable. -/
structure QuantumVar where
  name : String
  type : HilbertSpace

/-- Initialize a quantum variable `q` to a specific state. -/
def init_q (state : Fin Hq.dim → ℂ) : QuantumVar × (Fin Hq.dim → ℂ) :=
  let q : QuantumVar := { name := "q", type := Hq }
  (q, state)

/-- Initialize `q` to the state `|0⟩`. -/
def q_zero : QuantumVar × (Fin Hq.dim → ℂ) :=
  init_q (Hq.basis (Fin.mk 0 (show 0 < 2 from Nat.zero_lt_two)))


/-- A quantum register consists of a vector of quantum variables and their associated states. -/
structure QuantumRegister (n : Nat) where
  qubits : Vector (QuantumVar × (Fin Hq.dim → ℂ)) n

/-- Creates a quantum register of size `n`, with all qubits initialized to `|0⟩`. -/
def createQuantumRegisterVec (n : Nat) : QuantumRegister n :=
  let quantumVars := Vector.ofFn (fun i => (⟨s!"q{i}", Hq⟩, q_zero.snd))
  QuantumRegister.mk quantumVars

end qtype
