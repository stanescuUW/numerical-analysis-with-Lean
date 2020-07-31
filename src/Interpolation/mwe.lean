import data.polynomial
import data.real.basic

noncomputable theory
open_locale big_operators

def binom_l (a : ℝ) : polynomial ℝ := polynomial.X - polynomial.C a

def lagrange_interpolant_v2 (n : ℕ) (i : ℕ) (xData : ℕ → ℝ): polynomial ℝ :=
    ∏ j in ( finset.range (n+1) \ {i} ), 
    ((1 : ℝ)/(xData i - xData j)) • (binom_l (xData j))

def myX : ℕ → ℝ 
| 0 := (1 : ℝ)
| 1 := (2 : ℝ)
| (n+2) := 5

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
example (n : ℕ) : n - n = 0 := nat.sub_self n


-- The first interpolant (i=0) evaluated at the first point (x 0 = 1.0):
example : polynomial.eval (1 : ℝ) (lagrange_interpolant_v2 1 0 myX) = (1 : ℝ) :=
begin
    unfold lagrange_interpolant_v2,
    unfold finset.prod,
    simp * at *,
    --rw polynomial.eval_smul (binom_l _) (1:ℝ),
    sorry,
end

#check polynomial.eval_smul (binom_l (1:ℝ)) (1:ℝ) 
