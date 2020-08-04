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
    intros i j hij,
    have hi := (hxp i).1, have hj := (hxp j).1,
    cases hi with hi1 hi2, cases hj with hj1 hj2,
    --set i2 := fin.cast_succ (i+1) with hii2,
    --have checkf : i2.val = i + 1, rw hii2, sorry, 
    --set j2 := fin.cast_succ j with hjj2,
    rcases lt_trichotomy ((i+1) : fin (n+2) ) (j : fin (n+2)) with h1|h2|h3,
    --rcases lt_trichotomy i2 j2 with gj1|gj2|gj3,
    -- case (i+1) < j
    have hii1 := hx h1, linarith, 
    -- case (i+1) = j
    rw h2 at hi2, linarith,
    -- case j < (i+1) is not possible because i < j
    exfalso, 
        have g0 : i.val < j.val, exact hij,
        --have g1 : j2.val < i2.val + 1, exact h3,
        have h3n : (j : ℕ) < ((i + 1) : ℕ), 
            norm_num at h3,
            --have hcj := fin.coe_coe_eq_self j,
            --have hci := fin.coe_coe_eq_self i,
            rw fin.coe_eq_val, rw fin.coe_eq_val,
            rw fin.coe_eq_val at h3, rw fin.coe_eq_val at h3,
            norm_cast at h3, 
            have m1 : i.val + 1 = i.val.succ, rw nat.succ_eq_add_one,
            rw m1, clear m1,--exact h3,
            have m2 := fin.coe_fin_lt.mp h3, -- why does this keep failing?
            --rw fin.coe_eq_val at h3,
            --rw hcj,
            sorry, -- but there's trouble here
        have gf1 := nat.lt_succ_iff.mp h3n,
        have hijn : (i : ℕ) < (j : ℕ), exact hij,
        linarith,
    sorry, --this should be easy
end
#check fin.cast_val
#check fin.coe_fin_lt.mp
#check fin.cast_succ_val
#check fin.coe_coe_eq_self
#check fin.cast_succ
#check fin.coe_eq_val
#check lt_iff_le_and_ne
#check le_iff_lt_or_eq
example (i j : ℕ) (h : j < i + 1 ) : j ≤ i := nat.lt_succ_iff.mp h

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
        -- The above was needed because linarith fails on next one:
        have h002 : (0 : fin 2) < (1 : fin 2), exact h001, -- linarith fails !!!???
        have hx01 := hx h002, clear h001, clear h002,
        have hx0 := hi 0,
        have hx1 := hi 1,
        cases hx0 with h11 h121, cases hx1 with h21 h221, 
        have h3 : 0 < 1, linarith,
        have h41 : continuous_on f (Icc (x 0) (x 1)), 
            have h412 : (Icc (x 0) (x 1)) ⊆ Icc A B, 
            intros z hz, cases hz with hz1 hz2,
            cases h11 with h11z h12z,
            split, linarith,
            cases h21 with h21z h22z,
            linarith,
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
        have hfc := times_cont_diff_on.continuous_on hf,
        have H := one_step d.succ A B f x hx f hfc hi,
        cases H with xp hxp, cases hxp with hxpx hxpi,
        set g := deriv f with hg,
        --have h1 := times_cont_diff_on_succ_iff_has_fderiv_within_at.mp hf (x 0) (hi 0).1, 
        -- above is not immediately useful
        have h0 := unique_diff_on_Icc hAB,
        have h00 : ((d + 1) : with_top ℕ) ≤ d.succ, norm_cast, 
        have h1 := times_cont_diff_on.fderiv_within hf h0 h00, 
        simp only [] at h1,
        have h000 : (1 : with_top ℕ) ≤ d.succ, norm_cast, sorry,
        have h01 := times_cont_diff_on.continuous_on_iterated_deriv_within hf h000 h0,
        have hder : times_cont_diff_on ℝ d g (Icc A B), -- should come from hf
            rw hg,
            sorry, -- this seems much harder to get than it should!!!
        have hdg := hd xp hxpx g hder, clear hd,
        have G := hdg hxpi,
        have K : iterated_deriv (d.succ + 1) f = iterated_deriv d.succ g,
            apply iterated_deriv_succ',
        rw ← K at G,
        exact G,
    },
    done
end

end rolle_general

------------------ Scratch space below here ------------------------------
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
    intros i j hij,
    have hi := (hxp i).1, have hj := (hxp j).1,
    cases hi with hi1 hi2, cases hj with hj1 hj2,
    set i2 := fin.cast_succ (i+1) with hii2,
    set j2 := fin.cast_succ j with hjj2,
    --rcases lt_trichotomy ((i+1) : fin (n+2) ) (j : fin (n+2)) with h1|h2|h3,
    rcases lt_trichotomy i2 j2 with gj1|gj2|gj3,
    -- case (i+1) < j
    have hii1 := hx gj1, rw [hii2, hjj2] at hii1,  linarith, 
    -- case (i+1) = j
    rw h2 at hi2, linarith,
    -- case j < (i+1) is not possible because i < j
    exfalso, 
        have g0 : i.val < j.val, exact hij,
        --have g1 : j2.val < i2.val + 1, exact h3,
        have h3n : (j : ℕ) < ((i + 1) : ℕ), 
            norm_num at h3,
            have hcj := fin.coe_coe_eq_self j,
            have hci := fin.coe_coe_eq_self i,
            rw fin.coe_eq_val, rw fin.coe_eq_val,
            rw fin.coe_eq_val at h3, rw fin.coe_eq_val at h3,
            --rw fin.coe_eq_val at h3,
            --rw hcj,
            sorry, -- but there's trouble here
        have gf1 := nat.lt_succ_iff.mp h3n,
        have hijn : (i : ℕ) < (j : ℕ), exact hij,
        linarith,
    sorry, --this should be easy
end


#check deriv
#check times_cont_diff_on.continuous_on_iterated_deriv_within
#check times_cont_diff_on.differentiable_on_iterated_deriv_within
variables (f : ℝ → ℝ)
example (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (n : ℕ) (hf : times_cont_diff_on ℝ (n+1) f (Ioo a b) ) :
    times_cont_diff_on ℝ n (deriv f) (Ioo a b) :=
begin 
    refine times_cont_diff_on_of_differentiable_on_deriv _,
    have h0 := unique_diff_on_Ioo a b,
    have h := (times_cont_diff_on_iff_continuous_on_differentiable_on_deriv h0).mp hf,
    cases h with h1 h2,
    intros m hm, 
    have g := h2 m,
    have g1 : (m : with_top ℕ) < n + 1, sorry,
    have g2 := g g1,
    sorry,
    --refine times_cont_diff.times_cont_diff_on _
end

#check unique_diff_on_Ioo
#check times_cont_diff_iff_continuous_differentiable.mp  
#check iterated_deriv_within_succ
#check differentiable ℝ f
#check times_cont_diff_on_iff_continuous_on_differentiable_on_deriv
#check times_cont_diff_on ℝ 3 f
#check times_cont_diff_zero
#check  times_cont_diff_on_succ_iff_has_fderiv_within_at
