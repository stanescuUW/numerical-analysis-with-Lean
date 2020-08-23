import data.polynomial
import data.real.basic
import algebra.big_operators

noncomputable theory
open_locale big_operators

open polynomial

-- The basic building block in the Lagrange polynomial
-- this is (x - b)/(a - b)
def scaled_binomial (a b : ℝ) : polynomial ℝ :=
((1 : ℝ) / (a - b)) • (X - C b)

@[simp] lemma scaled_binomial.def (a b : ℝ) :
  scaled_binomial a b = ((1 : ℝ) / (a - b)) • (X - C b) := rfl

lemma bin_zero (a b : ℝ) : eval b (scaled_binomial a b) = 0 :=
by rw [scaled_binomial.def, eval_smul, eval_sub, eval_X, eval_C, sub_self, smul_eq_mul, mul_zero]

lemma bin_one (a b : ℝ) (h : a ≠ b) : eval a (scaled_binomial a b) = 1 :=
by rw [scaled_binomial.def, eval_smul, eval_sub, eval_X, eval_C, smul_eq_mul,
      div_mul_cancel 1 (sub_ne_zero_of_ne h)]

-- This version, using scalar multiplication (`smul`) seems simplest.
-- Must add hypothesis that data points are distinct
def lagrange_interpolant (n : ℕ) (i : ℕ) (xData : ℕ → ℝ) : polynomial ℝ :=
∏ j in (finset.range (n+1)).erase i, scaled_binomial (xData i) (xData j)

-- This has been PR'd into mathlib as `eval_prod`
lemma eval_finset.prod {ι : Type*} (s : finset ι) (p : ι → polynomial ℝ) (x : ℝ) :
  eval x (∏ j in s, p j) = ∏ j in s, eval x (p j) :=
(finset.prod_hom _ _).symm


-- The equivalent of the above for sums
lemma eval_finset.sum {ι : Type*} (s : finset ι) (p : ι → polynomial ℝ) (x : ℝ) :
  eval x (∑ j in s, p j) = ∑ j in s, eval x (p j) :=
(finset.sum_hom _ _).symm

-- The Lagrange interpolant `Lᵢ x` is one for `x = xData i`
@[simp]
lemma lagrange_interpolant_one (n : ℕ) (xData : ℕ → ℝ) (i : ℕ)
  (hinj : function.injective xData) :
  eval (xData i) (lagrange_interpolant n i xData) = (1:ℝ) :=
begin
  unfold lagrange_interpolant,
  rw eval_finset.prod,
  --simp only [bin_one], -- simp fails because the simplifier can't derive `a ≠ b`
  exact finset.prod_eq_one (λ j hj, bin_one (xData i) (xData j)
    (mt (@hinj i j) (finset.ne_of_mem_erase hj).symm))
end