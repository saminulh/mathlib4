/- Imports -/
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.Basic
--import Mathlib.MeasureTheory.Group.Prod

open MeasureTheory ProbabilityTheory Measure AEMeasurable
--open scoped ENNReal

section indepFun

example {α β γ: Type*} [MeasureSpace α] [MeasureSpace β] [MeasureSpace γ]
    {f : α → β} {g : α → γ} {μ : Measure α} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun ω ↦ (f ω, g ω)) μ := by
  exact AEMeasurable.prodMk hf hg

#check map_map_of_aemeasurable

@[to_additive]
theorem IndepFun.map_mul_eq_conv_map_map {M : Type*} [Monoid M] [MeasurableSpace M]
    [MeasurableMul₂ M] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → M} {g : Ω → M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfg : IndepFun f g μ):
    μ.map (f * g) = (μ.map f) ∗ (μ.map g) := by
  have : f * g = (fun (x,y) ↦ x * y) ∘ (fun ω ↦ (f ω, g ω)) := by rfl
  rw[this, ← map_map_of_aemeasurable measurable_mul.aemeasurable (AEMeasurable.prodMk hf hg),
     (indepFun_iff_map_prod_eq_prod_map_map hf hg).mp hfg]
  rfl

end indepFun
