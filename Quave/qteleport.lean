import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Complex.Basic
--import Quave.qtype
--import Quave.env
--import Quave.quantum

/- Apply a single-qubit gate to a quantum state -/
def apply_gate (gate : Fin 2 → Fin 2 → ℂ) (state : Fin 2 → ℂ) : Fin 2 → ℂ := fun i =>
  ∑ j, gate i j * state j

/- CNOT (Controlled-NOT) gate matrix for 2-qubit system -/
def CNOT_gate : Fin 4 → Fin 4 → ℂ := fun i j =>
  -- Convert to control and target bits
  let control := i / 2
  let target := i % 2
  let j_control := j / 2
  let j_target := j % 2
  if control = j_control then
    if control = 0 then
      if target = j_target then 1 else 0
    else -- control = 1
      if target = (1 - j_target) then 1 else 0
  else 0


def hadamard_gate : Fin 2 → Fin 2 → ℂ
| 0 0 := 1 / real.sqrt 2
| 0 1 := 1 / real.sqrt 2
| 1 0 := 1 / real.sqrt 2
| 1 1 := -1 / real.sqrt 2

def apply_hadamard (state : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i => ∑ j, hadamard_gate i j * state j


/-
- generate epr pair using hadamard and cnot
- |q1⟩ - alice, |q2⟩ - bob
- |ψ⟩ qubit to be sent
- cnot with |ψ⟩ as control qubit, |q1⟩ as target qubit
- H on |ψ⟩
- Alice measures |ψ⟩ and sends information classically to bob
- -/
