/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Saminul Haque
-/
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Convolution of functions using the Lebesgue Integral

# Design Decisions

# Main Definitions

# Main Results

# Notation

-/

/-
# TODO

1. Define MeasureTheory.MLConvolutionExistsAt f g x μ
2. Define MeasureTheory.ConvolutionExists f g μ
3. Develop some theory to verify the above
4. Prove that we can convert convolution of measures to convolution of densities

-/

namespace MeasureTheory
open scoped ENNReal
--open Measure

variable {G : Type*} [Group G] [MeasureSpace G]

/-- Multiplicative convolution of functions -/
@[to_additive lconvolution "Additive convolution of functions"]
noncomputable def mlconvolution (f : G → ℝ≥0∞) (g : G → ℝ≥0∞) (μ : Measure G := by volume_tac):
    G → ℝ≥0∞ := fun x ↦ ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ

/-- Scoped notation for the multiplicative convolution of functions -/
scoped[MeasureTheory] infix:80 " ∗ " => MeasureTheory.mlconvolution

/-- Scoped notation for the additive convolution of functions -/
scoped[MeasureTheory] infix:80 " ∗ " => MeasureTheory.lconvolution


end MeasureTheory
