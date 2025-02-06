/-

This file defines fundamental mathematical objects needed for quantum
information and computation.

  (a) Common States
  (b) Common Gates
    (i) Pauli Gates (I,X,Y,Z)
    (ii) Hadamard Gate
    (iii) Controlled-Not (CNOT)
    (iv) Phase Gates
    (v) Rotation Gates
  (c)

-/

import Mathlib.Data.Complex.Basic
import Quave.qtype

open Complex

namespace quantum

noncomputable section

/-- The Pauli-I (identity) gate matrix -/
def I_gate : Fin 2 → Fin 2 → ℂ := fun i j =>
  if i = j then 1 else 0

/-- The Pauli-X (NOT) gate matrix -/
def X_gate : Fin 2 → Fin 2 → ℂ := fun i j =>
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0

/-- The Pauli-Y gate matrix -/
def Y_gate : Fin 2 → Fin 2 → ℂ := fun i j =>
  if i = 0 ∧ j = 1 then -I else
  if i = 1 ∧ j = 0 then I else
  0

/-- The Pauli-Z gate matrix -/
def Z_gate : Fin 2 → Fin 2 → ℂ := fun i j =>
  if i = j then
    if i = 0 then 1 else -1
  else 0

/-- The Hadamard gate matrix -/
def H_gate : Fin 2 → Fin 2 → ℂ := fun i j =>
  1/Real.sqrt 2 * if (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) then 1 else
                  if (i = 1 ∧ j = 0) then 1 else -1

/-- Phase gate (S gate) matrix -/
def S_gate : Fin 2 → Fin 2 → ℂ := fun i j =>
  if i = j then
    if i = 0 then 1 else I
  else 0

/-- T gate matrix (π/8 gate) -/
def T_gate : Fin 2 → Fin 2 → ℂ := fun i j =>
  if i = j then
    if i = 0 then 1 else exp (I * Real.pi/4)
  else 0

/-- Apply a single-qubit gate to a quantum state -/
def apply_gate (gate : Fin 2 → Fin 2 → ℂ) (state : Fin 2 → ℂ) : Fin 2 → ℂ := fun i =>
  ∑ j, gate i j * state j

/-- CNOT (Controlled-NOT) gate matrix for 2-qubit system -/
def CNOT_gate : Fin 4 → Fin 4 → ℂ := fun i j =>
  -- Convert to control and target bits
  let control := i / 2
  let target := i % 2
  let j_control := j / 2
  let j_target := j % 2
  if control = j_control then
    if control = 0 then
      if target = j_target then 1 else 0
    else  -- control = 1
      if target = (1 - j_target) then 1 else 0
  else 0

end

end quantum
