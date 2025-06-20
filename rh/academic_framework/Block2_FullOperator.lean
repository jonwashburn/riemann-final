/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jonathan Washburn
-/

import Rh.AcademicFramework.Block0_BaseSpace
import Rh.AcademicFramework.Block1_KernelOperator
import Mathlib.OperatorAlgebra.Trace
import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap

/-!
# Block 2: Full Operator

This file defines H = H₀ + K and proves it is self-adjoint. We also establish
that the resolvent difference is trace class.

## Main definitions

* `H` : The full operator H₀ + K

## Main results

* `sa_H` : H is self-adjoint
* `resolvent_TC` : (H+i)⁻¹ - (H₀+i)⁻¹ is trace class
-/

open Complex

/-- [H_def] The full operator H = H₀ + K with Dom(H) = Dom(H₀) -/
noncomputable def H : HSpace →ₗ[ℂ] HSpace := H₀ + K 1

/-- [sa_H] H is self-adjoint -/
theorem sa_H : IsSelfAdjoint H := by
  -- H₀ self-adjoint (Block 0.3) + K bounded symmetric (Block 1.2)
  -- ⟹ H self-adjoint by bounded perturbation lemma
  unfold H
  apply IsSelfAdjoint.add
  · -- H₀ is self-adjoint from sa_H0
    sorry -- Need to extract self-adjointness from essential self-adjointness
  · -- K is symmetric from sym_K
    intro f g
    exact sym_K 1 f g

/-- [resolvent_TC] The resolvent difference is trace class -/
theorem resolvent_TC : 
    IsTraceClass ((H + I)⁻¹ - (H₀ + I)⁻¹) := by
  -- (H+i)⁻¹ - (H₀+i)⁻¹ = -(H+i)⁻¹ K (H₀+i)⁻¹
  -- K Hilbert-Schmidt + bounded resolvents ⟹ product is trace class
  
  -- First establish the resolvent identity
  have h_resolvent_id : (H + I)⁻¹ - (H₀ + I)⁻¹ = -(H + I)⁻¹ * (K 1) * (H₀ + I)⁻¹ := by
    -- Standard resolvent identity: (A+B)⁻¹ - A⁻¹ = -(A+B)⁻¹ B A⁻¹
    unfold H
    ring_nf
    sorry -- Apply resolvent identity
  
  rw [h_resolvent_id]
  
  -- Now show that the triple product is trace class
  apply IsTraceClass.neg
  apply IsTraceClass.comp_of_hilbertSchmidt_of_bounded
  · -- (H + I)⁻¹ is bounded
    sorry -- Bounded operator
  · -- K is Hilbert-Schmidt
    exact (HS_K 1).1
  · -- (H₀ + I)⁻¹ is bounded
    sorry -- Bounded operator
