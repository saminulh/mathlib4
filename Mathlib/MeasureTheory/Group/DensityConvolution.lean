/- Imports-/
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Measure Convolution
open scoped ENNReal NNReal

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
  --{π : Measure G} [SFinite π] [IsAddRightInvariant π]

/- Extend the definition of convolution to NNReal Functions -/
noncomputable def NNRealConvolution (f : G → ℝ≥0) (g : G → ℝ≥0) (μ : Measure G := by volume_tac):
    G → ℝ := (fun x ↦ (f x : ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (fun x ↦ (g x : ℝ))

scoped[NNRealConvolution]
  notation:67 f " ⋆[" μ:67 "]" g:66 => NNRealConvolution f g μ

scoped[NNRealConvolution]
  notation:67 f " ⋆ " g:66 => convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureSpace.volume

/- Main -/
noncomputable section


example {h : ℝ → ℝ≥0} : ℝ → ℝ≥0∞ := fun x ↦ h x
example {h : ℝ → ℝ≥0} : ℝ → ℝ := fun x ↦ h x

example {h : G → ℝ} {l : G → ℝ} : G → ℝ := h ⋆[(ContinuousLinearMap.lsmul ℝ ℝ),π] l

/-
theorem conv_measure_eq_conv_density (f : G → ℝ≥0) (g : G → ℝ≥0) :
    (π.withDensity (fun x ↦ f x)) ∗ (π.withDensity (fun x ↦ g x))
    = π.withDensity ((fun x ↦ f x) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ),π] (fun x ↦ g x)) := by
  sorry
-/
