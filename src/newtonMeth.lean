import tactic.basic
import analysis.specific_limits
import uwyo_aux

noncomputable theory
open_locale classical topological_space 
open filter 

-- For examples, see mathlib/src/analysis/specific_limits.lean
-- Main business: Newton's method sequence of approximations
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
  have h3 := aux_0 X h21,
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

theorem sqrt_sub_newton_below_zero : ∀ n : ℕ, s n < (0 : ℝ) :=
begin
  unfold s,
  intro n,
  rw sub_lt, rw sub_zero,
  have h1 := newton_seq_bounded_below n,
  have h2 := newton_seq_positive n,
  set X := x n with hX,
  have h3 : 0 ≤ (2 : ℝ), linarith,
  have h4 : 0 ≤ X, linarith,
  have h41 : 0 ≤ ((X * X) : ℝ), nlinarith,
  have h42 : 2 < ((X * X) : ℝ), norm_cast, exact h1,
  have h5 := (real.sqrt_lt h3 h41).mpr h42,
  rw ← pow_two at h5,
  rw real.sqrt_sqr at h5, exact h5,
  norm_cast, exact h4,
end

lemma sqrt_sub_newton_range_subset : set.range s ⊆ set.Iic (0:ℝ) :=
begin
  unfold set.range,
  have h := sqrt_sub_newton_below_zero,
  intros x hx,
  cases hx with m hm,
  have h1 := h m,
  rw hm at h1,
  rw set.mem_Iic,
  linarith,
end

theorem sqrt_sub_newton_bounded_above : bdd_above (set.range s) :=
begin
  have h1 := sqrt_sub_newton_range_subset,
  have h2 : ∃ a : ℝ, (set.range s) ⊆ set.Iic a,
    use [0, h1],
  exact bdd_above_iff_subset_Iic.mpr h2,
end

theorem sqrt_sub_newton_tendsto_finite_limit : ∃ L0 : ℝ, tendsto s at_top (𝓝 L0) :=
begin
  have h1 := tendsto_of_monotone sqrt_sub_newton_monotone,
  cases h1 with hf ht,
  have h2 := unbounded_of_tendsto_at_top hf,
  have h3 := sqrt_sub_newton_bounded_above,
  exfalso,  -- this sequence doesn't go to infinity; it is bounded above
  exact h2 h3,
  exact ht, done
end

-- This is the sequence of Newton approximations, viewed as real numbers
def xR (n : ℕ) : ℝ := real.sqrt 2 - s n
-- We can actually prove `xR` and `x` generate the same values
theorem xR_same_as_x (n : ℕ) : ((x n): ℝ) = xR n := 
begin
  have h1 : xR n = real.sqrt 2 - s n, refl,
  have h2 : s n = real.sqrt 2 - x n, refl,
  rw h2 at h1,
  have h3 : real.sqrt 2 - (real.sqrt 2 - ↑(x n)) = ↑(x n),
    linarith,
  rw h3 at h1, 
  exact h1.symm, done
end

-- And this sequence does have a finite limit:
theorem newton_tendsto_finite_limit_v2 : ∃ L : ℝ, tendsto xR at_top (𝓝 L) :=
begin
  have h1 := sqrt_sub_newton_tendsto_finite_limit,
  cases h1 with l0 hl0,
  use real.sqrt 2 - l0,
  apply tendsto.sub,
  exact tendsto_const_nhds,
  exact hl0,
end

-- I can try proving that `(x n) → sqrt 2` or alternately `s n → 0`
-- There might be an advantage in working with `x n` if I can apply limit operations
theorem sqrt_sub_newton_tendsto_zero : tendsto s at_top (𝓝 (0:ℝ)) :=
begin
  have h1 := sqrt_sub_newton_tendsto_finite_limit,
  rw (show (0 : ℝ) = real.sqrt 2 - real.sqrt 2, by simp),
  apply tendsto.sub,
  apply tendsto_const_nhds,
  cases h1 with L hL,
  unfold tendsto,
  sorry,
  --dsimp s at hL,
end
