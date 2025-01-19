import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

open BigOperators Complex

namespace qtype

def conj (z : ℂ) : ℂ := ⟨z.re, -z.im⟩


/-- A struct consist of three fields:
- `dim` is the dimension of the Hilbert space.
- `basis` is a function that maps an index (from `Fin dim`) to a vector.
  - Each vector is also a function from `Fin dim → ℂ`.
- `is_orthonormal` is a proof that ensures the basis is orthonormal.
  - The basis is orthonormal if the inner product of two vectors is 1 if the indices are the same, and 0 otherwise.
 -/
structure HilbertSpace where
  dim : Nat
  basis : Fin dim → (Fin dim → ℂ)
  is_orthonormal : ∀ (i j : Fin dim),
    (∑ k, basis i k * conj (basis j k)) = if i = j then 1 else 0

/-- A general Hilbert space with a given dimension `d`. -/
def makeHilbertSpace (d : Nat) : HilbertSpace :=
  { dim := d,
    basis := λ i j => if j = i then 1 else 0,  -- Canonical basis vectors
    is_orthonormal := by sorry }  -- Proof to be completed later

/-- A simple Hilbert space `Hq` with dimension 2 (e.g., for a qubit). -/
def Hq : HilbertSpace := makeHilbertSpace 2

/-- Define a quantum variable structure. -/
structure QuantumVar where
  name : String
  type : HilbertSpace

/-- Create a quantum variable `q` of type `Hq`. -/
def q : QuantumVar := { name := "q", type := Hq }

/-- Initialize `q` to the state `|0⟩`. -/
def init_q : QuantumVar × (Fin Hq.dim → ℂ) :=
  (q, Hq.basis (Fin.mk 0 (show 0 < 2 from Nat.zero_lt_two))) -- Initialize `q` to the first basis vector, `|0⟩`.

end qtype
