import Quad.Basic
import Mathlib

def quadratic (a b c : ℝ) (x : ℝ) : ℝ := a * x ^ 2 + b * x + c
def Δ (a b c : ℝ) : ℝ := b ^ 2 - 4 * a * c
theorem diff_of_squares (m n : ℝ) : m^2 - n^2 = (m - n)*(m + n) := by
    ring

theorem t1 (a b c : ℝ) (x : ℝ) (a_ne_zero : a ≠ 0) (delta_nonneq : Δ a b c ≥ 0) :
    quadratic a b c x = 0 →
    x = (-b + √(Δ a b c)) / (2 * a) ∨
    x = (-b - √(Δ a b c)) / (2 * a) := by
    let u : ℝ := x + b / (2 * a)
    have x_eq : x = u - b / (2 * a) := by ring
    simp only [quadratic, x_eq]
    have lhs : a * (u - b / (2 * a)) ^ 2 + b * (u - b / (2 * a)) + c =
        a * u^2 - b^2/(4*a) + c := by
        ring_nf
        have hc : a * u * b * a⁻¹ = u * b := by
            field_simp [a_ne_zero]
        rw [hc]
        have hd : a * b ^ 2 * a⁻¹ ^ 2 * (1 / 4) = b^2 / (4 * a) := by
            field_simp [a_ne_zero]
        rw [hd]
        ring_nf
    have lhss : a * (u - b / (2 * a)) ^ 2 + b * (u - b / (2 * a)) + c =
        a * u^2 - b^2/(4*a) + c := by
        linarith
    rw[lhs]
    have lhs2 : a * u^2 - (b^2)/(4*a) + c = a * u^2 - (Δ a b c) / (4 * a) := by
        unfold Δ
        field_simp [a_ne_zero]
        ring_nf
    rw [lhs2]

    have solve_for_u : a * u^2 - (Δ a b c) / (4 * a) = 0 →
        (u - √(Δ a b c)/(2*a))*(u + √(Δ a b c)/(2*a)) = 0 := by
        intro h
        have div_by_a : a * u^2 - (Δ a b c) / (4 * a) = 0 → u^2 - (Δ a b c) / (4 * a^2) = 0 := by
            field_simp [a_ne_zero]
            ring_nf
            intro h
            exact h
        apply div_by_a at h
        rw [← Real.sq_sqrt delta_nonneq] at h
        have p: 4*a^2 = (2*a)^2 := by
            ring
        rw [p, ←div_pow, diff_of_squares] at h
        exact h
    intro h
    apply solve_for_u at h
    have plug_back_x : u = x + b / (2 * a) := by ring
    rw[plug_back_x, mul_eq_zero] at h
    rw[plug_back_x, add_sub_cancel_right]
    have simplify_pos : x + b / (2 * a) + √(Δ a b c) / (2 * a) =
        x + (b + √(Δ a b c)) / (2 * a) := by
        field_simp [a_ne_zero]
        ring_nf
    have simplify_neq : x + b / (2 * a) - √(Δ a b c) / (2 * a) =
        x + (b - √(Δ a b c)) / (2 * a) := by
        field_simp [a_ne_zero]
        ring_nf

    rw [simplify_pos, simplify_neq] at h

    have solve_for_x_pos : x + (b - √(Δ a b c)) / (2 * a) = 0 →
        x = (-b + √(Δ a b c)) / (2 * a) := by
        intro h
        rw [add_eq_zero_iff_eq_neg] at h
        rw [h]
        field_simp [a_ne_zero]
        ring_nf
    have solve_for_x_neq : x + (b + √(Δ a b c)) / (2 * a) = 0 →
        x = (-b - √(Δ a b c)) / (2 * a) := by
        intro h
        rw [add_eq_zero_iff_eq_neg] at h
        rw [h]
        field_simp [a_ne_zero]
        ring_nf

    rcases h with h_neq | h_pos
    · apply Or.inl
      exact solve_for_x_pos h_neq
    · apply Or.inr
      exact solve_for_x_neq h_pos
