import tactic.basic
import uwyo_aux
import analysis.calculus.local_extr

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

theorem sqrt_sub_newton_tendsto_finite_limit_v1 : ∃ L0 : ℝ, tendsto s at_top (𝓝 L0) :=
begin
  have h1 := tendsto_of_monotone sqrt_sub_newton_monotone,
  cases h1 with hf ht,
  have h2 := unbounded_of_tendsto_at_top hf,
  have h3 := sqrt_sub_newton_bounded_above,
  exfalso,  -- this sequence doesn't go to infinity; it is bounded above
  exact h2 h3,
  exact ht, done
end

-- This is due to Yuri Kudryashov
example (s : ℕ → ℝ) (L : ℝ) (h : ∀ n : ℕ, s n < L) : ¬ (tendsto s at_top at_top) := 
begin
  intro H,
  --have h0 := H.eventually,
  have h1 : ∃ n, L ≤ s n := (H.eventually (eventually_ge_at_top L)).exists,
  cases h1 with n hn,
  have h2 := h n, 
  linarith, done
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

-- Rewrite the recursive formula as a function application
--def f (x : ℝ) : ℝ := (1/2) * (x + 2 / x)
def f (x : ℝ) : ℝ := ( x * x + 2) / ( 2 * x)
-- This is needed in the limit calculation result
lemma rw_recursion : ∀ n : ℕ, xR (n+1) = f (xR n) := 
begin
  intro n,
  have h1 := xR_same_as_x n,
  have h2 := xR_same_as_x (n+1),
  rw [← h1, ← h2],
  unfold f,
  have h3 : x (n+1) = ( x n * x n + 2) / ( 2 * x n), refl,
  rw h3,
  norm_cast, done
end

lemma f_contin_at_L (L : ℝ) (h : L ≠ 0) : continuous_at f L := 
begin 
  apply continuous_at.div,
  swap 3, { norm_num, exact h, },
  apply continuous_at.add,
  apply continuous_at.mul,
  apply continuous_at_id,
  apply continuous_at_id,
  apply continuous_at_const,
  apply continuous_at.mul,
  apply continuous_at_const,
  exact continuous_at_id, done
end

-- So now the final push
-- The sequence `xR` has a finite limit:
theorem newton_tendsto_finite_limit : ∃ L : ℝ, tendsto xR at_top (𝓝 L) :=
begin
  have h1 := sqrt_sub_newton_tendsto_finite_limit,
  cases h1 with l0 hl0,
  use real.sqrt 2 - l0,
  apply tendsto.sub,
  exact tendsto_const_nhds,
  exact hl0, done
end

-- The limit can't be zero:
theorem newton_tendsto_nonzero_limit (L : ℝ) : tendsto xR at_top (𝓝 L) → L ≠ 0 :=
begin
  have h2 := xR_same_as_x,
  have h0 : ∀ n : ℕ, 0 < xR n, 
    intro n,
    have g0 := newton_seq_positive n,
    have h21 := h2 n,
    rw ← h21, norm_cast, exact g0,
  have h1 := newton_seq_bounded_below,
  have h3 : ∀ n : ℕ, real.sqrt 2 < xR n,
    intro n, 
    have h30 := h1 n,
    have h31 := h2 n,
    have h00 := h0 n,
    have h32 : 0 ≤ (2:ℝ), linarith,
    have h33 : 0 ≤ (xR n) * (xR n), nlinarith,
    have h34 : 2 < (xR n) * (xR n), rw ← h31, norm_cast, exact h30,
    have h35 := (real.sqrt_lt h32 h33).mpr h34,
    have h01 : 0 ≤ xR n, linarith,
    have h36 : real.sqrt ((xR n) * (xR n)) = xR n, exact real.sqrt_mul_self h01,
    rw h36 at h35,
    exact h35,
  intros H hL,
  have G := aux_3 xR h3,
  rw hL at H,
  exact G H, done
end

-- And this limit satisfies a specific equation
theorem newton_limit_satisfies (L : ℝ) (H : tendsto xR at_top ((𝓝 L) )) :
  f L = L :=
begin
  have h1 : tendsto (xR ∘ nat.succ) at_top (𝓝 L) := (tendsto_add_at_top_iff_nat 1).mpr H,
  have h2 := (tendsto_add_at_top_iff_nat 1).mpr H,
  rw show xR ∘ nat.succ = f ∘ xR, from funext rw_recursion at h1,
  have hL : L ≠ 0, exact newton_tendsto_nonzero_limit L H,
  have hf : continuous_at f L, exact f_contin_at_L L hL,
  exact tendsto_nhds_unique (tendsto.comp hf H) h1,
  done
end

-- The equation for the limit `L` can be solved to get `L = real.sqrt 2`
-- Courtesy Patrick Massot 
lemma solve_limit_eqn {L : ℝ} (h : L = (2 + L * L)/(2*L)) (hL : 0 < L) : L = real.sqrt 2 :=
begin
  apply_fun (λ x, 2*L*x) at h,
  simp_rw mul_div_cancel' _ (ne_of_gt (by linarith) : 2*L ≠ 0) at h,
  apply_fun (λ x, x - L*L) at h,
  ring at h,
  symmetry,
  rwa real.sqrt_eq_iff_sqr_eq; linarith,
end

--------- Scratch space below here:
-- This slick proof due to Patrick Massot:
lemma dan_limit {u : ℕ → ℝ} {L : ℝ} {f : ℝ → ℝ} (hu : tendsto u at_top $ 𝓝 L)
(hf : continuous_at f L) (huf : ∀ n, u (n+1) = f (u n)) : f L = L :=
begin
  have lim : tendsto (u ∘ nat.succ) at_top (𝓝 L) :=
    (tendsto_add_at_top_iff_nat 1).mpr hu,
  rw show u ∘ nat.succ = f ∘ u, from funext huf at lim,
  exact tendsto_nhds_unique (tendsto.comp hf hu) lim
end
