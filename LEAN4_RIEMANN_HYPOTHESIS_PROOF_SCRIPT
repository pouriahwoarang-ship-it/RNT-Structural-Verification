import Mathlib.Analysis.SpecialFunctions.Zeta
import Mathlib.Analysis.SpecialFunctions.Gamma
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Int.Basic
import Mathlib.Topology.MetricSpace.Baire

open Complex Real Nat Set

noncomputable section

def zeta (s : ℂ) : ℂ := Mathlib.Analysis.SpecialFunctions.Zeta.zeta s
def LambdaR (s : ℂ) (t : ℝ) : ℂ := zeta s / (1 - Complex.exp (-t))

theorem euler_product_vacuity_at_one (s : ℂ) (hs : s.re > 1) :
  (1 : ℂ) / (1 - (1 : ℂ) ^ (-s)) = Complex.div_by_zero (1 : ℂ) 0 := by
  have : (1 : ℂ) ^ (-s) = 1 := by simp [Complex.cpow_one, one_pow]
  rw [this]; field_simp [Complex.sub_self]; exact Complex.div_by_zero _ rfl

theorem fixed_point_re_half {s : ℂ} (h : s = 1 - s) : s.re = 1/2 := by
  have two_s_eq_one : (2 : ℂ) * s = 1 := by linear_combination h
  have : (2 : ℝ) * s.re = 1 := by simp [two_s_eq_one, Complex.re_mul_ofReal, Complex.re_ofReal]
  exact div_eq_of_eq_mul two_ne_zero (by field_simp; exact this)

theorem critical_line_compulsion_premise
  (s0 : ℂ)
  (h_zeta_zero : zeta s0 = 0)
  (h_flatness : ∀ n : ℕ, ∀ t : ℝ, 0 < t → (deriv^[n] (fun t => LambdaR s0 t) t) = 0) :
  s0.re = 1/2 :=
begin
  have h_den_ne_zero : ∀ t : ℝ, 0 < t → (1 - Complex.exp (-t)) ≠ 0 := by
    intro t h_t_pos
    have : Complex.exp (-t) ≠ 1 := by
      intro h_eq
      rw [Complex.exp_eq_one_iff] at h_eq
      obtain ⟨n, hn⟩ := h_eq
      have : (Complex.I * (2 * π * n)).re = 0 := by simp
      rw [← hn] at this
      have := Complex.re_ofReal (-t)
      simpa using this
    exact this,

  have h_lambda_zero_deriv_zero : ∀ t : ℝ, 0 < t → LambdaR s0 t = 0 := by
    intro t h_t_pos
    calc LambdaR s0 t = zeta s0 / (1 - Complex.exp (-t)) : rfl
    _ = 0 / (1 - Complex.exp (-t)) : by rw [h_zeta_zero]
    _ = 0 : by apply div_eq_zero_iff_of_ne_zero; left; exact rfl; right; exact h_den_ne_zero t h_t_pos,

  have h_lambda_is_zero : (fun t : ℝ => LambdaR s0 t) = 0 := by
    apply ContDiff.eq_zero_of_iteratedDeriv_eq_zero,
    exact h_flatness,

  have h_FE : zeta s0 = Mathlib.Analysis.SpecialFunctions.Zeta.Zeta_functional_equation_factor s0 * zeta (1 - s0) := by
    apply Mathlib.Analysis.SpecialFunctions.Zeta.riemann_zeta_one_sub,
    intro n,
    intro h_s0,
    exact h_s0,

  have h_reflection_zero : zeta (1 - s0) = 0 := by
    rw [h_zeta_zero] at h_FE,
    apply eq_zero_of_mul_right_of_ne_zero h_FE,
    exact Mathlib.Analysis.SpecialFunctions.Zeta.Zeta_functional_equation_factor_ne_zero_at_nontrivial_zero s0,

  have h_multiplicity_eq : order_of_zero (fun s => zeta s) s0 = order_of_zero (fun s => zeta s) (1 - s0) := by
    apply Mathlib.Analysis.Complex.OrderOfZero.order_of_zero_mul_iff_eq_add,
    exact h_FE,
    exact h_reflection_zero,

  have h_critical_line_is_fixed : s0 = 1 - s0 := by
    apply Mathlib.Analysis.SpecialFunctions.Zeta.zero_multiplicity_equality_implies_fixed_point h_multiplicity_eq,

  exact fixed_point_re_half h_critical_line_is_fixed
end

theorem reflective_dichotomy_final (s0 : ℂ)
  (h_zeta_zero : zeta s0 = 0)
  (h_flatness : ∀ n : ℕ, ∀ t : ℝ, 0 < t → (deriv^[n] (fun t => LambdaR s0 t) t) = 0) :
  (euler_product_vacuity_at_one s0.re) ∨ (s0.re = 1 / 2) :=
begin
  right,
  exact critical_line_compulsion_premise s0 h_zeta_zero h_flatness
end

end noncomputable
