/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import PhysLean.QuantumMechanics.DDimensions.Operators.Unbounded
public import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
public import PhysLean.QuantumMechanics.PlanckConstant
public import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Momentum operators

## i. Overview

In this module we introduce several momentum operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `momentumOperator` : (components of) the momentum vector operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` as `-iℏ∂ᵢ`.
- `momentumOperatorSqr` : operator acting on Schwartz maps `𝓢(Space d, ℂ)` as `∑ᵢ 𝐩[i]∘𝐩[i]`.
- `momentumUnboundedOperator` : a symmetric unbounded operator acting on the Schwartz submodule
    of the Hilbert space `SpaceDHilbertSpace d`.

Notation:
- `𝐩[i]` for `momentumOperator i`
- `𝐩²` for `momentumOperatorSqr`

## iii. Table of contents

- A. Momentum vector operator
- B. Momentum-squared operator
- C. Unbounded momentum vector operator

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
noncomputable section
open Constants
open Space
open ContDiff SchwartzMap

variable {d : ℕ} (i : Fin d)

/-!

## A. Momentum vector operator

-/

/-- Component `i` of the momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`. -/
def momentumOperator : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (- Complex.I * ℏ) • (SchwartzMap.evalCLM ℂ (Space d) ℂ (basis i)) ∘L
    (SchwartzMap.fderivCLM ℂ (Space d) ℂ)

@[inherit_doc momentumOperator]
notation "𝐩[" i "]" => momentumOperator i

lemma momentumOperator_apply_fun (ψ : 𝓢(Space d, ℂ)) :
    𝐩[i] ψ = (- Complex.I * ℏ) • ∂[i] ψ := rfl

@[simp]
lemma momentumOperator_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐩[i] ψ x = - Complex.I * ℏ * ∂[i] ψ x := rfl

/-!

## B. Momentum-squared operator

-/

/-- The square of the momentum operator, `𝐩² ≔ ∑ᵢ 𝐩ᵢ∘𝐩ᵢ`. -/
def momentumOperatorSqr : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := ∑ i, 𝐩[i] ∘L 𝐩[i]

@[inherit_doc momentumOperatorSqr]
notation "𝐩²" => momentumOperatorSqr

lemma momentumOperatorSqr_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐩² ψ x = ∑ i, 𝐩[i] (𝐩[i] ψ) x := by
  dsimp only [momentumOperatorSqr]
  rw [← SchwartzMap.coe_coeHom]
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp', Finset.sum_apply,
    Function.comp_apply, map_sum]

/-!

## C. Unbounded momentum vector operator

-/

open SpaceDHilbertSpace

/-- The momentum operators defined on the Schwartz submodule. -/
def momentumOperatorSchwartz : schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  schwartzEquiv.toLinearMap ∘ₗ 𝐩[i].toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

@[sorryful]
lemma momentumOperatorSchwartz_isSymmetric : (momentumOperatorSchwartz i).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨f, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨f', rfl⟩ := schwartzEquiv.surjective ψ'
  unfold momentumOperatorSchwartz
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
    Function.comp_apply, LinearEquiv.symm_apply_apply, schwartzEquiv_inner, momentumOperator_apply,
    neg_mul, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_neg, mul_neg]
  have f_diff : Differentiable ℝ (⇑f) := f.differentiable
  have f'_diff : Differentiable ℝ (⇑f') := f'.differentiable
  have starf_diff : Differentiable ℝ (fun x => (starRingEnd ℂ) (f x)) := 
    Complex.conjCLE.differentiable.comp f_diff
  have fderiv_star_eq : ∀ x, fderiv ℝ (fun y => (starRingEnd ℂ) (f y)) x = 
      Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ (⇑f) x) := by
    intro x
    have h1 : (fun y => (starRingEnd ℂ) (f y)) = Complex.conjCLE ∘ f := rfl
    rw [h1, fderiv_comp x Complex.conjCLE.differentiableAt (f_diff x)]
    congr 1
    exact Complex.conjCLE.toContinuousLinearMap.fderiv
  have fderiv_star_apply : ∀ x, fderiv ℝ (fun y => (starRingEnd ℂ) (f y)) x (basis i) =
      (starRingEnd ℂ) (fderiv ℝ (⇑f) x (basis i)) := by
    intro x
    rw [fderiv_star_eq]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rfl
  let df : 𝓢(Space d, ℂ) := ((SchwartzMap.evalCLM ℂ (Space d) ℂ (basis i)) ((SchwartzMap.fderivCLM ℂ (Space d) ℂ) f))
  let df' : 𝓢(Space d, ℂ) := ((SchwartzMap.evalCLM ℂ (Space d) ℂ (basis i)) ((SchwartzMap.fderivCLM ℂ (Space d) ℂ) f'))
  have df_eq : ∀ x, df x = fderiv ℝ (⇑f) x (basis i) := fun x => rfl
  have df'_eq : ∀ x, df' x = fderiv ℝ (⇑f') x (basis i) := fun x => rfl
  have norm_star_eq : ∀ z : ℂ, ‖(starRingEnd ℂ) z‖ = ‖z‖ := fun z => Complex.norm_conj z
  have hf'g : MeasureTheory.Integrable (fun x => (fderiv ℝ (fun x => (starRingEnd ℂ) (f x)) x) (basis i) * f' x) MeasureTheory.volume := by
    simp_rw [fderiv_star_apply]
    have hC : ∀ x, ‖df x‖ ≤ (SchwartzMap.seminorm ℂ 0 0) df := fun x => df.norm_le_seminorm ℂ x
    have hdom : ∀ x, ‖(starRingEnd ℂ) (fderiv ℝ (⇑f) x (basis i)) * f' x‖ ≤ (SchwartzMap.seminorm ℂ 0 0) df * ‖f' x‖ := by
      intro x
      rw [← df_eq]
      calc ‖(starRingEnd ℂ) (df x) * f' x‖ 
          = ‖(starRingEnd ℂ) (df x)‖ * ‖f' x‖ := norm_mul _ _
        _ = ‖df x‖ * ‖f' x‖ := by rw [norm_star_eq]
        _ ≤ (SchwartzMap.seminorm ℂ 0 0) df * ‖f' x‖ := mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
    apply MeasureTheory.Integrable.mono' (f'.integrable.norm.const_mul _) (by measurability)
    filter_upwards with x using hdom x
  have hfg' : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (f x) * (fderiv ℝ (⇑f') x) (basis i)) MeasureTheory.volume := by
    have hC : ∀ x, ‖f x‖ ≤ (SchwartzMap.seminorm ℂ 0 0) f := fun x => f.norm_le_seminorm ℂ x
    have hdom : ∀ x, ‖(starRingEnd ℂ) (f x) * (fderiv ℝ (⇑f') x) (basis i)‖ ≤ (SchwartzMap.seminorm ℂ 0 0) f * ‖df' x‖ := by
      intro x
      rw [← df'_eq]
      calc ‖(starRingEnd ℂ) (f x) * df' x‖ 
          = ‖(starRingEnd ℂ) (f x)‖ * ‖df' x‖ := norm_mul _ _
        _ = ‖f x‖ * ‖df' x‖ := by rw [norm_star_eq]
        _ ≤ (SchwartzMap.seminorm ℂ 0 0) f * ‖df' x‖ := mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
    apply MeasureTheory.Integrable.mono' (df'.integrable.norm.const_mul _) (by measurability)
    filter_upwards with x using hdom x
  have hfg : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (f x) * f' x) MeasureTheory.volume := by
    have hC : ∀ x, ‖f x‖ ≤ (SchwartzMap.seminorm ℂ 0 0) f := fun x => f.norm_le_seminorm ℂ x
    have hdom : ∀ x, ‖(starRingEnd ℂ) (f x) * f' x‖ ≤ (SchwartzMap.seminorm ℂ 0 0) f * ‖f' x‖ := by
      intro x
      calc ‖(starRingEnd ℂ) (f x) * f' x‖ 
          = ‖(starRingEnd ℂ) (f x)‖ * ‖f' x‖ := norm_mul _ _
        _ = ‖f x‖ * ‖f' x‖ := by rw [norm_star_eq]
        _ ≤ (SchwartzMap.seminorm ℂ 0 0) f * ‖f' x‖ := mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
    apply MeasureTheory.Integrable.mono' (f'.integrable.norm.const_mul _) (by measurability)
    filter_upwards with x using hdom x
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := MeasureTheory.volume)
    (f := fun x => (starRingEnd ℂ) (f x)) (g := ⇑f') (v := basis i)
    hf'g hfg' hfg starf_diff f'_diff
  simp_rw [fderiv_star_apply] at ibp
  simp only [Space.deriv]
  have lhs_eq : ∀ x, Complex.I * ↑↑ℏ * (starRingEnd ℂ) (fderiv ℝ (⇑f) x (basis i)) * f' x =
      (Complex.I * ↑↑ℏ) * ((starRingEnd ℂ) (fderiv ℝ (⇑f) x (basis i)) * f' x) := fun x => by ring
  have rhs_eq : ∀ x, (starRingEnd ℂ) (f x) * (Complex.I * ↑↑ℏ * fderiv ℝ (⇑f') x (basis i)) =
      (Complex.I * ↑↑ℏ) * ((starRingEnd ℂ) (f x) * fderiv ℝ (⇑f') x (basis i)) := fun x => by ring
  simp_rw [lhs_eq, rhs_eq]
  simp only [MeasureTheory.integral_neg]
  simp only [← smul_eq_mul (a := Complex.I * ↑↑ℏ)]
  rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul]
  rw [ibp]
  simp only [smul_neg, neg_neg]

/-- The symmetric momentum unbounded operators with domain the Schwartz submodule
  of the Hilbert space. -/
@[sorryful]
def momentumUnboundedOperator : UnboundedOperator (SpaceDHilbertSpace d) (SpaceDHilbertSpace d) :=
  UnboundedOperator.ofSymmetric (schwartzSubmodule_dense d) (momentumOperatorSchwartz_isSymmetric i)

end
end QuantumMechanics
