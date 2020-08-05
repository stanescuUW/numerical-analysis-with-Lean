import analysis.calculus.local_extr
import analysis.calculus.times_cont_diff
import analysis.calculus.iterated_deriv
import tactic data.fin
open set

namespace rolle_general

lemma shing (n : ℕ) (i j : fin (n+1)) (h : (j.val : fin (n+2)) < (i.val.succ : fin (n+2))) : 
    j.val < i.val.succ :=
begin
  change (j.val : fin (n+2)).val < (i.val.succ : fin (n+2)).val at h,
  rwa [fin.coe_val_of_lt (show j.1 < n + 2, by linarith [j.2]),
       fin.coe_val_of_lt (show i.1 + 1 < n + 2, by linarith [i.2])] at h,
end

lemma fin_le_last_val (n : ℕ) : ∀ i : fin (n + 2), i ≤ (n+1) :=
begin
    intro i,
    have j0 : n + 1 < n + 1 + 1, linarith,
    have j0 := @fin.coe_val_of_lt (n+1) (n+1) j0,
    have h2 := i.is_lt,
    have h3 : i.val ≤ n + 1, linarith,
    apply fin.le_iff_val_le_val.mpr,
    rw ← j0 at h3,
    exact h3,
end


lemma one_step (n : ℕ) (x : fin (n+2) → ℝ) (hx : strict_mono x) :
    ∀ (f : ℝ → ℝ), continuous_on f ( Icc (x 0) (x (n+1)) ) → 
    (∀ i, f (x i) = 0)  →
    ∃ (xp : fin(n+1) → ℝ), strict_mono xp ∧ 
        ∀ (i : fin (n+1)), xp i ∈ ( Icc (x 0) (x (n+1)) ) ∧ deriv f (xp i) = 0 :=
begin
    intros f hf hxi,
    have h1 : ∀ (i : fin (n+1)), ∃ y ∈ (Ioo (x i) (x (i+1))), deriv f y = 0,
        sorry,
    choose xp hxp using h1, 
    use xp, split,
    intros i j hij,
    have hi := (hxp i).1, have hj := (hxp j).1,
    cases hi with hi1 hi2, cases hj with hj1 hj2,
    rcases lt_trichotomy ((i+1) : fin (n+2) ) (j : fin (n+2)) with h1|h2|h3,
    --rcases lt_trichotomy (fin.cast_succ (i+1)) (fin.cast_succ j) with h1|h2|h3,
    -- case (i+1) < j
    have hii1 := hx h1, linarith, 
    -- case (i+1) = j
    rw h2 at hi2, linarith,
    -- case j < (i+1) is not possible because i < j
    exfalso, 
        have h3n : (j : ℕ) < ((i + 1) : ℕ), 
            norm_num at h3,
            have m3 := shing n i j h3, exact m3,
        have gf1 := nat.lt_succ_iff.mp h3n,
        --strange as it looks, linarith still needs this
        have hijn : (i : ℕ) < (j : ℕ), exact hij,
        linarith,
    intro i, split,
    swap, exact (hxp i).2,
    have g0 := (hxp i).1,
    split,
    cases g0 with g01 g02,
    have g1 : (0 : fin (n+2))  ≤ (i : fin (n+2) ), 
        apply fin.le_iff_val_le_val.mpr, exact zero_le _,
    have g2 := (strict_mono.le_iff_le hx).mpr g1, 
    linarith,
    cases g0 with g01 g02,
    have g03 := fin_le_last_val n (i+1),
    have g3 := (strict_mono.le_iff_le hx).mpr g03,
    linarith, done
end


theorem general_rolle (n : ℕ) (x : fin (n+2) → ℝ) (hx : strict_mono x) :
    ∀ (f : ℝ → ℝ), times_cont_diff_on ℝ n f ( Icc (x 0) (x (n+1)) ) → 
    (∀ i, f (x i) = 0)  → 
    ∃ c ∈ Ioo (x 0) (x (n+1)), iterated_deriv (n+1) f c = 0 :=
begin
    induction n with d hd,
    { -- base case, just plain Rolle `exists_deriv_eq_zero`
        intros f hf hi,
        norm_cast at hf,
        rw times_cont_diff_on_zero at hf,
        have h1 : 0 < 1, linarith,
        -- The above was needed because linarith fails on next one:
        have h2 : (0 : fin 2) < (1 : fin 2), exact h1, -- linarith fails !!!???
        have hx01 := hx h2, clear h1, clear h2,
        have hx0 := hi 0,
        have hx1 := hi 1,
        have heq : f (x 0) = f (x 1),
            rw [hx0, hx1],
        have h5 := exists_deriv_eq_zero f hx01 hf heq,
        rw iterated_deriv_one,
        have g : (((0 : ℕ) + 1) : fin 2) = 1, norm_cast,
        rw g, 
        exact h5,
    },
    { -- induction step
        -- the derivative is in Cᵈ
        intros f hf hi,
        have hfc := times_cont_diff_on.continuous_on hf,
        have H := one_step d.succ x hx f hfc hi,
        cases H with xp hxp, cases hxp with hxpx hxpi,
        set g := deriv f with hg,
        have hder : times_cont_diff_on ℝ d g (Icc (xp 0) (xp (d+1))), -- should come from hf
        --    rw hg,
            sorry, -- this seems much harder to get than it should!!!
        have hdg := hd xp hxpx g hder, clear hd,
        have H1 : ∀ i, g (xp i) = 0, 
            intro i,
            have H10 := hxpi i, cases H10 with H101 H102, exact H102,  
        have G := hdg H1,
        have K : iterated_deriv (d.succ + 1) f = iterated_deriv d.succ g,
            apply iterated_deriv_succ',
        rw ← K at G,
        sorry,
        --exact G,
    },
    done
end

end rolle_general

