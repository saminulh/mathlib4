/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
import Mathlib.MeasureTheory
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.IdentDistrib

/-!
The Central Limit Theorem
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Real Topology

-- #check tendsto_one_plus_div_pow_exp
/-- `(1 + t/n + o(1/n)) ^ n → exp t`. -/
lemma tendsto_one_plus_div_pow_exp' {f : ℕ → ℂ} (t : ℝ)
    (hf : (fun n ↦ f n - (1 + t / n)) =o[atTop] fun n ↦ 1 / (n : ℝ)) :
    Tendsto (fun n ↦ f n ^ n) atTop (𝓝 (exp t)) := by
  sorry

lemma tendsto_sqrt_atTop : Tendsto (√·) atTop atTop := by
  simp_rw [Real.sqrt_eq_rpow]
  exact tendsto_rpow_atTop (by norm_num)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → ℝ}

/-- From PFR -/
theorem iIndepFun_iff_pi_map_eq_map {Ω : Type u_1} {_mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ι : Type*} {β : ι → Type*} [Fintype ι]
    (f : ∀ x : ι, Ω → β x) [m : ∀ x : ι, MeasurableSpace (β x)]
    [IsProbabilityMeasure μ] (hf : ∀ (x : ι), Measurable (f x)) :
    iIndepFun f μ ↔ Measure.pi (fun i ↦ μ.map (f i)) = μ.map (fun ω i ↦ f i ω) := by
  sorry

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

-- using ProbabilityMeasure for the topology
variable {P : ProbabilityMeasure Ω}

theorem central_limit (hX : ∀ n, Measurable (X n))
    (h0 : P[X 0] = 0) (h1 : P[X 0 ^ 2] = 1)
    (hindep : iIndepFun X P) (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    Tendsto (fun n : ℕ => P.map (aemeasurable_invSqrtMulSum n hX)) atTop (𝓝 stdGaussian) := by
  sorry
