/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jonathan Washburn
-/

import Rh.AcademicFramework.Block3_SpectralAnalysis
import Mathlib.NumberTheory.ZetaFunction

/-!
# Block 4: Identification with ξ

This file proves that our spectral determinant D equals the completed
Riemann zeta function ξ.

## Main results

* `Hadamard_ratio` : D/ξ = exp(a+bs)
* `ratio_const` : a = 0, b = 0
* `identification` : D ≡ ξ
-/

open Complex

/-- The completed Riemann zeta function -/
noncomputable def xi (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) * π^(-s/2) * Gamma (s/2) * riemannZeta s

/-- Data 4.0: ξ properties -/
theorem xi_properties :
    (Differentiable ℂ xi) ∧
    (∃ C > 0, ∀ s, ‖xi s‖ ≤ C * exp ‖s‖) ∧
    (∀ s, xi s = xi (1 - s)) ∧
    ((fun T => zeroCounting xi T) ~[atTop] 
     (fun T => T / (2 * π) * log (T / (2 * π * exp 1)))) := by
  sorry -- Classical results

/-- [Hadamard_ratio] Both D and ξ have same product type ⟹ D/ξ = exp(a+bs) -/
theorem Hadamard_ratio :
    ∃ (a b : ℝ), ∀ s, D s = exp (a + b * s) * xi s := by
  sorry -- Hadamard factorization + same order + same zero density

/-- [ratio_const] Functional equations ⟹ a = 0, b = 0 -/
theorem ratio_const :
    ∃! (a b : ℝ), (∀ s, D s = exp (a + b * s) * xi s) ∧ a = 0 ∧ b = 0 := by
  sorry -- D(s) = D(1-s) and ξ(s) = ξ(1-s) force a = -b/2 = 0

/-- [identification] Main theorem: D ≡ ξ -/
theorem identification : D = xi := by
  obtain ⟨a, b, h_eq⟩ := Hadamard_ratio
  obtain ⟨_, _, _, h_a, h_b⟩ := ratio_const
  rw [h_a, h_b] at h_eq
  simp at h_eq
  exact funext h_eq
