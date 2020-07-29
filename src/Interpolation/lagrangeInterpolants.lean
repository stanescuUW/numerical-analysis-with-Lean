import data.polynomial
import data.real.basic
import algebra.big_operators

noncomputable theory
open_locale big_operators
--open classical
--open polynomial
--def test (a:ℝ ):polynomial ℝ := C a * X

-- These will be useful for defining the Lagrange polynomials
def binomial_R (a : ℝ) : polynomial ℝ := polynomial.X - polynomial.C a
-- To work with their values use this technique:
example : polynomial.eval (5 : ℝ) (binomial_R (2:ℝ)) = 3 :=
begin
    unfold binomial_R,  -- otherwise can't rw below
    rw polynomial.eval_sub,
    rw polynomial.eval_C,
    rw polynomial.eval_X,
    norm_num, done
end

-- Either this way (working with ℕ):
def lagrange_interpolant_v2 (n : ℕ) (i : ℕ) (xData : ℕ → ℝ): polynomial ℝ :=
    ∏ j in ( finset.range (n+1) \ {i} ), 
    (binomial_R (xData j)) * polynomial.C (1/(xData i - xData j))

-- Or this way (working with `fin`):
def lagrange_interpolant_v1 (n : ℕ) (i : fin (n+1) ) (xData : fin (n+1) → ℝ): polynomial ℝ :=
    ∏ j in ( finset.fin_range (n+1) \ { i } ), 
    binomial_R (xData j) * polynomial.C (1/(xData i - xData j))

--------- Scratch space below here:
-- Check that I can work with this definition
def myX : ℕ → ℝ 
| 0 := (1 : ℝ)
| 1 := (2 : ℝ)
| (n+1) := 0

-- This is the interpolant evaluated at the first point:
example : polynomial.eval (1 : ℝ) (lagrange_interpolant_v2 1 0 myX) = 1 :=
begin
    unfold lagrange_interpolant_v2,
    unfold finset.prod,
    simp * at *,
    -- rw polynomial.eval_mul, fails
    sorry,
end
-- To remember:
example (j : ℕ) (n : ℕ) (i : fin n) : j = i := 
begin
    sorry,  -- can coerce from `fin n` to `ℕ` but not the other way around. Of course...
end
 
-- Experiment with products of binomial terms
-- If the interpolation points are placed in a `finset`:
variable x : finset ℝ
#check finset.prod x binomial_R --this works
#check  finset.has_sdiff -- this can be used to remove elements
#check  finset.fin_range -- this returns a finset of `fin k`
-- Probably `fin n` would be even better, is there something similar for `fin`?
#check fin
#check fin.prod_univ_succ
#check  fin.sum_univ_eq_sum_range
#check  list.sum_of_fn
#check  list.prod_of_fn
#check polynomial.coeff_mul_X_sub_C
variables a b : ℝ
#check (binomial_R a) * (binomial_R b)
#check finset.range

-- #lint-