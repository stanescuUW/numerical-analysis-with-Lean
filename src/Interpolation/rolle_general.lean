import analysis.calculus.local_extr
import analysis.calculus.times_cont_diff
import analysis.calculus.iterated_deriv
import tactic
open set

namespace rolle_general

lemma one_step (n : ℕ) (a b : ℝ) (f : ℝ → ℝ) (x : fin (n+2) → ℝ) (hx : strict_mono x) :
    ∀ (f : ℝ → ℝ), continuous_on f (Icc a b) → 
    (∀ i, x i ∈ (Icc a b) ∧ f (x i) = 0)  →
    ∃ (xp : fin(n+1) → ℝ), strict_mono xp ∧ ∀ (i : fin (n+1)), xp i ∈ (Icc a b) ∧ deriv f (xp i) = 0 :=
begin
    intros f hf hxi,
    have h1 : ∀ (i : fin (n+1)), ∃ y ∈ (Ioo (x i) (x (i+1))), deriv f y = 0,
        sorry,
    choose xp hxp using h1, 
    use xp,
    split,
    sorry,
    sorry,
end

theorem general_rolle (n : ℕ) (A B : ℝ) (hAB : A < B) (x : fin (n+2) → ℝ) (hx : strict_mono x) :
    ∀ (f : ℝ → ℝ), times_cont_diff_on ℝ n f (Icc A B) → 
    (∀ i, x i ∈ (Icc A B) ∧ f (x i) = 0)  → 
    ∃ c ∈ Ioo A B, iterated_deriv (n+1) f c = 0 :=
begin
    induction n with d hd,
    { -- base case, just plain Rolle `exists_deriv_eq_zero`
        intros f hf hi,
        norm_cast at hf,
        rw times_cont_diff_on_zero at hf,
        --unfold strict_mono at hx,
        have h001 : 0 < 1, linarith,
        have h002 : (0 : fin 2) < (1 : fin 2), exact h001, -- why doesn't linarith work on this one?
        have hx01 := hx h002, clear h001, clear h002,
        have hx0 := hi 0,
        have hx1 := hi 1,
        cases hx0 with h11 h121, cases hx1 with h21 h221, 
        have h3 : 0 < 1, linarith,
        have h41 : continuous_on f (Icc (x 0) (x 1)), 
            have h412 : (Icc (x 0) (x 1)) ⊆ Icc A B, sorry,
            exact continuous_on.mono hf h412,
        have h42 : f (x 0) = f (x 1), rw [h121, h221], 
        have h5 := exists_deriv_eq_zero f hx01 h41 h42, 
        cases h5 with c hc, cases hc with hc1 hc2,
        have h6 : c ∈ Ioo A B, 
            cases hc1 with h61 h62, cases h11 with h111 h112,
            have h71: A < c, linarith,
            cases h21 with h211 h212,
            have h72 : c < B, linarith,
            split, exact h71, exact h72,
        rw iterated_deriv_one,
        use [c, h6], exact hc2,
    },
    { -- induction step
        -- the derivative is in Cᵈ
        intros f hf hi,
        have hfc : continuous_on f (Icc A B), sorry, 
        have H := one_step d.succ A B f x hx f hfc hi,
        cases H with xp hxp, cases hxp with hxpx hxpi,
        set g := deriv f with hg,
        have hder : times_cont_diff_on ℝ d g (Icc A B),
            sorry, 
        have hdg := hd xp hxpx g hder, clear hd,
        -- the function is continuous
        have G := hdg hxpi,
        have K : iterated_deriv (d+1) g = iterated_deriv (d.succ + 1) f,
            sorry,
        rw K at G,
        exact G,
    },
    done
end

end rolle_general

------------------ Scratch space below here ------------------------------