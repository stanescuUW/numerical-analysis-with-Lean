import data.real.basic
import tactic.basic
import analysis.specific_limits
import .uwyo_sqrt2

noncomputable theory
open_locale classical topological_space 
open filter 

-- For examples, see mathlib/src/analysis/specific_limits.lean
-- Main business:
--noncomputable theory (probably needed if using ℝ instead of ℚ)

-- Working first with a sequence of rationals for the approximations themselves
def x : ℕ → ℚ
| 0     := (2 : ℚ)
| (n+1) := ( x n * x n + 2) / ( 2 * x n)
-- Now pretend otherwise
def s (n : ℕ) : ℝ := real.sqrt 2 - x n


lemma newton_seq_positive : ∀ n : ℕ, 0 < x n :=
begin
  intro n,
  induction n with d hd,
  { -- base case n = 0
    have h1 : x 0 = 2, refl,
    rw h1, linarith,
  },
  { -- induction step
    have h2 : x d.succ = ( x d * x d + 2) / ( 2 * x d), refl,
    set X := x d with hX,
    have h3 : 0 < X * X, nlinarith,
    have h4 : 0 < X * X + 2, linarith,
    have h5 : 0 < 2 * X, linarith,
    have h6 := div_pos_of_pos_of_pos h4 h5, 
    exact h6,
  }, 
  done
end

lemma some_arithmetic (X : ℚ) (hX: 0 < X): ( X * X + 2) / (2 * X) - X = (2 - X * X) / (2 * X) :=
begin
  set Y := X * X with hY,
  have h1 : 2 - Y = 2 + Y - 2 * Y, linarith,
  rw add_comm 2 Y at h1,
  rw h1,
  set V := 2 * X with hV,
  have h31 : V ≠ 0, linarith,
  have h2 := sub_div (Y+2) (2*Y) V,
  rw h2,
  have h32 : (2 * Y) / V = X, 
    apply (div_eq_iff h31).mpr,
    rw [hY, hV], ring,
  rw h32,
  done
end

lemma aux_1 (X Y V : ℚ) (G : X ≠ 0) (hY : Y = X * X) (hV : V = 2 * X) (G1 : Y ≠ 0) : 
  4 * (Y + 2) / V * ((Y + 2) / (V)) = Y + 2 * 2 + (2*2/(X * X)) :=
begin
  -- this is a struggle
      rw hV, rw hY,
      norm_num, field_simp,
      have h211 : 2 * X * ( 2 * X ) = 4 * X * X,
        ring,
      rw h211, rw mul_assoc 4 X X,
      rw ← hY, field_simp,
      rw mul_assoc,
      have h212 : (Y+2) * (Y + 2) = Y * Y + 4 * Y +4, ring,
      rw h212, 
      set T := 4 * (Y * Y + 4 * Y + 4) with hT,
      rw ← hT,
      have h214 : (4: ℚ) ≠ 0, linarith,
      have h213 : 4 * Y ≠ 0, exact mul_ne_zero h214 G1,
      apply (div_eq_iff h213).mpr,
      have h214 : (Y + 4 + (4/Y)) * (4 * Y) = (Y+4) * (4*Y) + (4/Y) * (4 * Y), 
        ring,
      rw h214,
      have h215 : (4/Y) * (4 * Y) = 16, ring, 
        rw mul_assoc,
        have h216 : Y * Y⁻¹ = 1, exact mul_inv_cancel G1,
        rw h216, linarith,
      rw h215,
      rw hT, ring, done
end

lemma aux_2 (X : ℚ) (G : X ≠ 0) : ( 2 / X - X ) * ( 2 / X - X ) = 4 / (X*X) - 4 + X * X :=
begin
  set V := (2/X) with hV,
  have h1 : V * V = 4 / (X * X), 
    rw hV, ring, field_simp,
    have h11 : X ^ 2 = X * X, ring,
    rw h11,
  rw ← h1,
  have h2 : (V - X) * (V - X) = V * V - 2 * V * X + X * X, ring,
  rw h2,
  have h3 : V * X = 2, field_simp, ring, rw mul_assoc, rw mul_comm X⁻¹ _,
    rw mul_inv_cancel G, linarith,
  rw mul_assoc 2 V X, rw h3,
  linarith,
end 

lemma no_rat_sq_eq_two (X : ℚ) (hX1 : X ≠ 0) :  0 ≠ ( 2 / X - X ) :=
begin
  by_contradiction H,
  push_neg at H,
  have h1 := congr_arg (λ (b : ℚ), X * b) H,
  simp only [] at h1,
  rw mul_zero at h1,
  have h2 : X * (2 / X - X) = 2 - X ^ 2, 
    ring, 
    have h21 : ( - X + 2 * X⁻¹) * X = - X * X + 2 * X⁻¹ * X, ring,
    rw h21, rw mul_assoc 2 (X⁻¹) X, rw mul_comm (X⁻¹) _, rw mul_inv_cancel hX1,
    ring,
  rw ← h1 at h2,
  have h2 : X ^ 2 = 2, linarith,
  have h3 : ∃ r : ℚ, r ^ 2 = 2,
    use X, exact h2,
  exact rational_not_sqrt_two h3, -- from uwyo_sqrt2
  done
end

lemma newton_seq_bounded_below : ∀ n : ℕ, 2 < (x n) * (x n) :=
begin
  intro n,
  induction n with d hd,
  { -- base case n= 0
    have h0 : x 0 =2 , refl,
    rw h0, linarith,
  },
  { -- induction step, kind of ugly so far
    have h1 : x d.succ = ( x d * x d + 2) / ( 2 * x d), refl,
    rw h1,
    have H := newton_seq_positive d,
    set X := x d with hX,
    have G : X ≠ 0, linarith,
    set Y := X * X with hY,
    have G1 : Y ≠ 0, nlinarith,
    have g1 : (Y + 2) * (Y + 2) = Y * Y + 4 * Y + 4, ring,
    set V := 2 * X with hV,
    have F : V ≠ 0, linarith,
    have E : V * V ≠ 0, nlinarith,
    have g2 :  (Y + 2) * (Y + 2) / ( V * V) = (Y + 2) / V * ((Y + 2) / V),
      field_simp,
    have h21 := aux_1 X Y V G hY hV G1,
    have h201 : (1/4) * (4 * (Y + 2) / V * ((Y + 2) / (V))) = (1/4) * (Y + 2 * 2 + (2*2/(X * X)) ),
      rw h21,
    have h202 : (1/4) * (4 * (Y + 2) / V * ((Y + 2) / (V))) = (Y + 2) / V * ((Y + 2) / (V)),
      ring,
    have h2 : (Y + 2) / V * ((Y + 2) / (V)) = (1/4) * (Y + 2 * 2 + (2*2/(X * X)) ), 
      rw h202 at h201, exact h201,
    have h3 : 
      2 - (1/4) * ( X * X + 2 * 2 + (2*2/(X*X)) ) = (1/4) * ( - X * X + 2 * 2 - (2*2/(X*X)) ), 
      ring,
    have h4 : (1/4) * ( - X * X + 2 * 2 - (2*2/(X*X)) ) = - (1/4) * ( 2 / X - X ) ^ 2, 
      have h41 : ( 2 / X - X ) ^ 2 = ( 2 / X - X ) * ( 2 / X - X ), ring,
      rw h41,
      have h42 := aux_2 X G,
      rw h42, ring,
    have h51 : 0 ≤ ( 2 / X - X ) ^ 2, exact pow_two_nonneg _,
    have h52 : 0 ≠ ( 2 / X - X ), exact no_rat_sq_eq_two X G,  
    have h53 : 0 ≠ ( 2 / X - X ) ^ 2, exact ne.symm (pow_ne_zero 2 (ne.symm h52)),
    have h54 : 0 < ( 2 / X - X ) ^ 2, exact lt_of_le_of_ne h51 h53,
    have h6 : - (1/4) * ( 2 / X - X ) ^ 2 < 0, linarith,
    rw h2,
    apply sub_lt_zero.mp,
    rw h3, rw h4, exact h6,
  },
  done
end

lemma newton_seq_decreasing : ∀ n : ℕ, x (n+1) < x n :=
begin
  intro n,
  have h1 : x (n+1) = ( x n * x n + 2) / ( 2 * x n), refl,
  have h2 : x (n+1) - x n = ( x n * x n + 2) / ( 2 * x n) - x n, rw h1,
  have h21 := newton_seq_positive n,
  set X := x n with hX,
  have h3 := some_arithmetic X h21,
  have h4 : 2 - X * X < 0, 
    have h41 := newton_seq_bounded_below n,
    rw ← hX at h41,
    linarith,
  have h5 : 0 < 2 * X, linarith,
  have h6 := div_neg_of_neg_of_pos h4 h5,
  rw ← h3 at h6, rw ← h2 at h6, linarith,
  done
end

theorem sqrt_sub_newton_monotone : monotone s :=
begin
  apply monotone_of_monotone_nat,
  intro n,
  unfold s,
  have h1 := newton_seq_decreasing n,
  have h2 : ((x (n + 1)) : ℝ) ≤ ((x n) : ℝ), 
    norm_cast, linarith,
  exact (sub_le_sub_iff_left (real.sqrt 2)).mpr h2,
  done
end

#check tendsto_of_monotone sqrt_sub_newton_monotone

theorem sqrt_sub_newton_bounded_above : ∀ n : ℕ, s n < (0 : ℝ) :=
begin
  sorry, -- this should be easy
end

theorem sqrt_sub_newton_tendsto_zero : tendsto s at_top (𝓝 (0:ℝ)) :=
begin
  have h1 := tendsto_of_monotone sqrt_sub_newton_monotone,
  cases h1 with hf ht,
  unfold tendsto at hf,
  have h2 := sqrt_sub_newton_bounded_above,
  unfold at_top at hf,
  exfalso,  -- this sequence doesn't go to infinity; it is bounded above
  sorry,
  cases ht with L hL,  -- so it must have a limit in ℝ
  sorry, -- still work to do
end

