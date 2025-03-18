/- Imports -/
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.Basic
--import Mathlib.MeasureTheory.Group.Prod

open MeasureTheory ProbabilityTheory Measure AEMeasurable
--open scoped ENNReal

section indepFun

example (f g : ℝ → ℝ) (x : ℝ) : f (g x) = 1 := by
  change (_ ∘ _) _ = _
  sorry


@[to_additive]
theorem IndepFun.map_mul_eq_conv_map_map {M : Type*} [Monoid M] [MeasurableSpace M]
    [MeasurableMul₂ M] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → M} {g : Ω → M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfg : IndepFun f g μ):
    μ.map (f * g) = (μ.map f) ∗ (μ.map g) := by
  conv in f * g => change (fun (x,y) ↦ x * y) ∘ (fun ω ↦ (f ω, g ω))
  rw[← map_map_of_aemeasurable measurable_mul.aemeasurable (AEMeasurable.prodMk hf hg),
     (indepFun_iff_map_prod_eq_prod_map_map hf hg).mp hfg]
  rfl

end indepFun
