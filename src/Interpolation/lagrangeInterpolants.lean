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

-- The basic building block in the Lagrange polynomial
-- this is (x - b)/(a - b)
def scaled_binomial (a b : ℝ) : polynomial ℝ := 
    ((1 : ℝ)/(a - b)) • (polynomial.X - polynomial.C b)

@[simp] lemma bin_zero (a b : ℝ) (h : a ≠ b) : polynomial.eval b (scaled_binomial a b) = 0 :=
begin
    unfold scaled_binomial, -- doesn't work without this
    rw [polynomial.eval_smul, polynomial.eval_sub, polynomial.eval_X, polynomial.eval_C],
    rw [sub_self, algebra.id.smul_eq_mul, mul_zero],
    done
end

@[simp] lemma bin_one (a b : ℝ) (h : a ≠ b) : polynomial.eval a (scaled_binomial a b) = 1 :=
begin
    unfold scaled_binomial, -- doesn't work without this
    rw [polynomial.eval_smul, polynomial.eval_sub, polynomial.eval_X, polynomial.eval_C],
    rw algebra.id.smul_eq_mul,
    have h1 : a - b ≠ 0, exact sub_ne_zero_of_ne h,
    exact div_mul_cancel 1 h1, done
end

-- This version, using scalar multiplication (`smul`) seems simplest.
def lagrange_interpolant (n : ℕ) (i : ℕ) (xData : ℕ → ℝ): polynomial ℝ :=
    ∏ j in ( finset.range (n+1) \ {i} ), scaled_binomial (xData i) (xData j) 

-- Must show that one can commute polynomial.eval with finset.prod
-- So a lemma like this would be useful
lemma eval_comm_prod (n : ℕ) (pj : ℕ → polynomial ℝ) (x : ℝ) :
    polynomial.eval x ( ∏ j in finset.range n, pj j) = 
    ∏ j in finset.range n, polynomial.eval x (pj j) :=
begin
    induction n with d hd,
    { -- base case n = 0
        repeat { rw finset.prod_range_zero _ },
        rw polynomial.eval_one,
    },
    { -- induction step
        rw [finset.prod_range_succ, polynomial.eval_mul, hd, finset.prod_range_succ  ],
    },
    done
end

variables  {ι : Type*} [decidable_eq ι]

lemma polynomial.eval_finset.prod (s : finset ι) (p : ι → polynomial ℝ) (x : ℝ) :
  polynomial.eval x (∏ j in s, p j) = ∏ j in s, polynomial.eval x (p j) :=
begin
    apply finset.induction_on s,
    { repeat {rw finset.prod_empty}, rw polynomial.eval_one, },
    intros j s hj hpj,
    have h0 : ∏ i in insert j s, polynomial.eval x (p i) = 
            (polynomial.eval x (p j)) * ∏ i in s, polynomial.eval x (p i),
    apply finset.prod_insert hj,
    rw [h0, ← hpj], 
    rw finset.prod_insert hj,
    rw polynomial.eval_mul, done
end

-- The Lagrange interpolant `Lᵢ x` is one for `x = xData i` 
@[simp]
lemma lagrange_interpolant_one (n : ℕ) (xData : ℕ → ℝ) (i : ℕ) (hi: i ∈ finset.range (n+1)) : 
    polynomial.eval (xData i) (lagrange_interpolant n i xData)= (1:ℝ) :=
begin
    unfold lagrange_interpolant,
    -- must commute polynomial.eval with finset.prod
    --apply finset.prod_eq_one,
    sorry,
end
#check finset.prod_eq_one
#check finset.prod_induction
#check finset.prod_range_induction
#check finset.prod_eq_zero


-- The Lagrange interpolant `Lᵢ x` is zero for `x = xData j, j ≠ i` 
@[simp]
lemma lagrange_interpolant_zero (n : ℕ) (xData : ℕ → ℝ) (i : ℕ) (hi: i ∈ finset.range (n+1)) 
    (j : ℕ) (hj : j ∈ finset.range (n+1)) (hij : i ≠ j) : 
    polynomial.eval (xData j) (lagrange_interpolant n i xData)= (0:ℝ) :=
begin
    sorry,
end


--------------------- Scratch space below here


-- Maybe even better, working with `smul`? Maybe not!
def lagrange_interpolant_v3 (n : ℕ) (i : ℕ) (xData : ℕ → ℝ): polynomial ℝ :=
    ∏ j in ( finset.range (n+1) \ {i} ), 
    ((1 : ℝ)/(xData i - xData j)) • (binomial_R (xData j))

-- Either this way (working with ℕ):
def lagrange_interpolant_v2 (n : ℕ) (i : ℕ) (xData : ℕ → ℝ): polynomial ℝ :=
    ∏ j in ( finset.range (n+1) \ {i} ), 
    (binomial_R (xData j)) * polynomial.C (1/(xData i - xData j))

-- Or this way (working with `fin`):
def lagrange_interpolant_v1 (n : ℕ) (i : fin (n+1) ) (xData : fin (n+1) → ℝ): polynomial ℝ :=
    ∏ j in ( finset.fin_range (n+1) \ { i } ), 
    binomial_R (xData j) * polynomial.C (1/(xData i - xData j))



-- Check that I can work with this definition
def myX : ℕ → ℝ 
| 0     := (1 : ℝ)
| 1     := (2 : ℝ)
| (n+2) := (5 : ℝ)

@[simp] lemma myX_0 : myX 0 = (1:ℝ) := rfl
@[simp] lemma myX_1 : myX 1 = (2:ℝ) := rfl
@[simp] lemma myX_all (n : ℕ): myX (nat.succ (nat.succ n)) = (5:ℝ) := rfl 
@[simp] lemma myX_n (n : ℕ) (hn : 1 < n) : myX n = (5:ℝ) := 
begin
    -- should I use rec_on or something else instead of induction?
    induction n with d hd,
    { -- base case
        exfalso, linarith, 
    },
    { -- induction step, how to best prove this?
        have h1 : 0 < d, 
            rw nat.succ_eq_add_one at hn,
            linarith,
        have h2 : ∃ m : ℕ, d = m.succ,
        use d - 1, rw nat.succ_eq_add_one, omega, -- a little ℕ subtraction problem, thx `omega`!
        cases h2 with m hm,
        rw hm,
        exact myX_all m,
    },
    done
end

-- Maybe I can use this lemma below:
@[simp] lemma finset_range_2_0 : finset.range 2 \ {0} = {1} := 
begin
    have h1 : 2 = nat.succ 1, refl,
    rw [ h1, finset.range_succ, finset.range_one ],
    refl,
end
@[simp] lemma finset_range_2_1 : finset.range 2 \ {1} = {0} := 
begin
    have h1 : 2 = nat.succ 1, refl,
    rw h1,
    rw finset.range_succ,
    rw finset.range_one,
    refl,
end
@[simp] lemma finset_range_20 : finset.range 2 \ {0} = {1} := dec_trivial -- wow!

example : polynomial.eval (1 : ℝ) (lagrange_interpolant 1 0 myX) = 1 :=
begin
    unfold lagrange_interpolant,
    simp * at *, -- still doesn't use the simp lemmas for scaled_binomial
    have h : (1:ℝ) ≠ 2, linarith,
    exact bin_one 1 2 h,
end


-- The first interpolant (i=0) evaluated at the first point (x 0 = 1.0):
example : polynomial.eval (1 : ℝ) (lagrange_interpolant_v2 1 0 myX) = 1 :=
begin
    unfold lagrange_interpolant_v2,
    unfold finset.prod,
    have h1 : 1 + 1 = 2, refl,
    rw h1,
    simp * at *,
    unfold binomial_R,
    rw [polynomial.eval_sub, polynomial.eval_X, polynomial.eval_C],
    norm_num,
end
-- The first interpolant (i=0) evaluated at the first point (x 0 = 1.0):
example : polynomial.eval (1 : ℝ) (lagrange_interpolant_v3 1 0 myX) = (1 : ℝ) :=
begin
    unfold lagrange_interpolant_v3,
    unfold finset.prod,
    have h1 : 1 + 1 = 2, refl,
    rw h1,
    rw finset_range_2_0, 
    unfold binomial_R, simp only [one_div_eq_inv, myX_0],
    simp * at *,
    norm_num,
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
#check polynomial.eval_mul

-- #lint-