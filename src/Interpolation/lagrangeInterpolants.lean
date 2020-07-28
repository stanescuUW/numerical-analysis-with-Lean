import data.polynomial
import data.real.basic
noncomputable theory
--open classical
--open polynomial
--def test (a:ℝ ):polynomial ℝ := C a * X

-- These are useful for defining the Lagrange polynomials
def binomial_R (a : ℝ) : polynomial ℝ := polynomial.X - polynomial.C a
-- To work with their values use this technique:
example : polynomial.eval (5 : ℝ) (binomial_R (2:ℝ)) = 3 :=
begin
    unfold binomial_R,
    rw polynomial.eval_sub,
    rw polynomial.eval_C,
    rw polynomial.eval_X,
    norm_num, done
end