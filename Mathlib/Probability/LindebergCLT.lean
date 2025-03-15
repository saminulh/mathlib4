/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.IdentDistrib

/-!
The Central Limit Theorem
-/

noncomputable section

open MeasureTheory ProbabilityTheory ProbabilityMeasure Complex Filter
open scoped Real Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → ℝ}

abbrev stdGaussian : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

abbrev invSqrtMulSum {Ω} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (√n)⁻¹ * ∑ i : Fin n, X i ω

lemma map_invSqrtMulSum (μ : Measure Ω) {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    μ.map (invSqrtMulSum X n)
      = ((μ.map (fun ω (i : Fin n) ↦ X i ω)).map (fun x ↦ ∑ i, x i)).map ((√n)⁻¹ * ·) := by
  rw [Measure.map_map, Measure.map_map]
  · rfl
  all_goals { fun_prop }

lemma measurable_invSqrtMulSum (n) (hX : ∀ n, Measurable (X n)) :
    Measurable (invSqrtMulSum X n) :=
  (Finset.measurable_sum _ fun _ _ ↦ (hX _)).const_mul _

lemma aemeasurable_invSqrtMulSum {μ : Measure Ω} (n) (hX : ∀ n, Measurable (X n)) :
    AEMeasurable (invSqrtMulSum X n) μ :=
  (measurable_invSqrtMulSum n hX).aemeasurable


lemma compact_supported_integral_tendsto_iff_tends_to
  (P : ProbabilityMeasure Ω)
  {Y : ℕ → Ω → ℝ}
  (hY : ∀ n, Measurable (Y n)) (μ : ProbabilityMeasure ℝ):
  (∀ {f : ℝ → ℝ}(hfcont: Continuous f) (hfcompact: HasCompactSupport f),
    Tendsto (fun i ↦ ∫ (ω : ℝ), f ω ∂↑(P.map (hY i).aemeasurable)) atTop
    (𝓝 (∫ (ω : ℝ), f ω ∂↑μ)))
  ↔
  Tendsto (fun n : ℕ => P.map (hY n).aemeasurable) atTop (𝓝 μ)
  -- Goal: Tendsto (fun n ↦ P.map ⋯) atTop (𝓝 stdGaussian)

  -- ∀ (f : BoundedContinuousFunction ℝ ℝ),
  --   Tendsto (fun i ↦ ∫ (ω : ℝ), f ω ∂↑(P.map (hY i).aemeasurable)) atTop
  --   (𝓝 (∫ (ω : ℝ), f ω ∂↑(P.map hZ.aemeasurable)))
  := by
  sorry
  -- intro hctsconv
  -- rw [tendsto_iff_forall_integral_tendsto]
  -- intro f
  -- -- have hfbdd := f.map_bounded'
  -- obtain ⟨ C, hfbdd ⟩ := f.map_bounded'
  -- let g (M : ℝ) (x : ℝ) := (f x) * (max 0 (min 1 (M+1-|x|)))

  -- -- have h1 (f1 : ℝ → ℝ → ℝ) (hfcts: Continuous f1) : ∀ x : ℝ, Continuous (f1 x) := by

  -- have : ∀ M : ℝ, M ≥ 0 → Continuous (g M) := by
  --   intro M hM
  --   -- continuity?
  --   simp_all only [toMeasure_map, ge_iff_le, g]
  --   apply Continuous.mul
  --   · apply ContinuousMapClass.map_continuous
  --   · apply Continuous.comp'
  --     · apply Continuous.max
  --       apply continuous_const
  --       apply continuous_id
  --     · apply Continuous.comp'
  --       · apply Continuous.min
  --         apply continuous_const
  --         apply continuous_id
  --       · apply Continuous.add
  --         · apply continuous_const
  --         · apply Continuous.comp'
  --           · apply ContinuousNeg.continuous_neg
  --           · apply Continuous.abs
  --             apply continuous_id
  -- sorry

lemma smooth_compact_integral_tendsto_iff_compact_integral_tendsto
  (P : ProbabilityMeasure Ω)
  {Y : ℕ → Ω → ℝ}
  (hY : ∀ n, Measurable (Y n)) (μ : ProbabilityMeasure ℝ):
  (∀ {f : ℝ → ℝ}(hfsmooth: ContDiff ℝ ⊤ f) (hfcompact: HasCompactSupport f),
    Tendsto (fun i ↦ ∫ (ω : ℝ), f ω ∂↑(P.map (hY i).aemeasurable)) atTop
    (𝓝 (∫ (ω : ℝ), f ω ∂↑μ)))
  ↔
  (∀ {f : ℝ → ℝ}(hfcont: Continuous f) (hfcompact: HasCompactSupport f),
    Tendsto (fun i ↦ ∫ (ω : ℝ), f ω ∂↑(P.map (hY i).aemeasurable)) atTop
    (𝓝 (∫ (ω : ℝ), f ω ∂↑μ)))
  -- ∀ (f : BoundedContinuousFunction ℝ ℝ),
  --   Tendsto (fun i ↦ ∫ (ω : ℝ), f ω ∂↑(P.map (hY i).aemeasurable)) atTop
  --   (𝓝 (∫ (ω : ℝ), f ω ∂↑(P.map hZ.aemeasurable)))
  := sorry

lemma sum_of_indep_gaussians_is_gaussian
    (P : ProbabilityMeasure Ω)
    (hX : ∀ n, Measurable (X n))
    (hgauss: ∀ n, P.map (hX n).aemeasurable = stdGaussian)
    (hindep : iIndepFun X P):
    ∀ n, P.map (aemeasurable_invSqrtMulSum n hX) = stdGaussian
    := sorry

lemma smooth_compact_clt
    (P : ProbabilityMeasure Ω)
    (hX : ∀ n, Measurable (X n))
    (h0 : P[X 0] = 0) (h1 : P[X 0 ^ 2] = 1)
    (hindep : iIndepFun X P) (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P)
    {f : ℝ → ℝ}(hfsmooth: ContDiff ℝ ⊤ f) (hfcompact: HasCompactSupport f):
    Tendsto (fun i ↦ ∫ (ω : ℝ), f ω ∂↑(P.map (aemeasurable_invSqrtMulSum i hX))) atTop
    (𝓝 (∫ (ω : ℝ), f ω ∂↑stdGaussian)) := sorry

theorem central_limit
    (P : ProbabilityMeasure Ω)
    (hX : ∀ n, Measurable (X n))
    (h0 : P[X 0] = 0) (h1 : P[X 0 ^ 2] = 1)
    (hindep : iIndepFun X P) (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    Tendsto (fun n : ℕ => P.map (aemeasurable_invSqrtMulSum n hX)) atTop (𝓝 stdGaussian) := by
  apply (compact_supported_integral_tendsto_iff_tends_to P
    (fun n ↦ measurable_invSqrtMulSum n hX)
    stdGaussian).mp
  apply (smooth_compact_integral_tendsto_iff_compact_integral_tendsto P
    (fun n ↦ measurable_invSqrtMulSum n hX)
    stdGaussian).mp
  intro f hfsmooth hfcompact
  apply smooth_compact_clt P hX h0 h1 hindep hident hfsmooth hfcompact
