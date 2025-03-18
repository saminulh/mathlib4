/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Convolution of functions using the Lebesgue Integral

# Main Definitions

-/

namespace MeasureTheory
open Measure
open scoped ENNReal
--open Measure

variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Multiplicative convolution of functions -/
@[to_additive lconvolution "Additive convolution of functions"]
noncomputable def mlconvolution (f : G → ℝ≥0∞) (g : G → ℝ≥0∞) (μ : Measure G := by volume_tac):
    G → ℝ≥0∞ := fun x ↦ ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ

/-- Scoped notation for the multiplicative convolution of functions with respect to a measure `μ` -/
scoped[MeasureTheory] notation:67 f " ⋆ₗ["μ:67"] " g:66  => MeasureTheory.mlconvolution f g μ

/-- Scoped notation for the additive convolution of functions with respect to a measure `μ` -/
scoped[MeasureTheory] notation:67 f " ⋆ₗ["μ:67"]" g:66  => MeasureTheory.lconvolution f g μ

theorem mlconvolution_def {f : G → ℝ≥0∞} {g : G → ℝ≥0∞} {μ : Measure G} {x : G} :
    (f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ := rfl

end MeasureTheory
