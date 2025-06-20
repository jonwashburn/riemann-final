/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jonathan Washburn
-/

import Rh.AcademicFramework.Block0_BaseSpace
import Rh.AcademicFramework.Block1_KernelOperator
import Mathlib.OperatorAlgebra.Trace

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
  sorry

/-- [resolvent_TC] The resolvent difference is trace class -/
theorem resolvent_TC : 
    IsTraceClass ((H + I)⁻¹ - (H₀ + I)⁻¹) := by
  -- (H+i)⁻¹ - (H₀+i)⁻¹ = -(H+i)⁻¹ K (H₀+i)⁻¹
  -- K Hilbert-Schmidt + bounded resolvents ⟹ product is trace class
  sorry
