import analysis.calculus.local_extr
import analysis.calculus.times_cont_diff
import analysis.calculus.iterated_deriv
import tactic data.fin
open set

namespace rolle_general

-- This is courtesy Shing Tak Lam
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
    have h3 : i.val ≤ n + 1, linarith [i.is_lt],
    apply fin.le_iff_val_le_val.mpr,
    rw ← j0 at h3,
    exact h3,
end

lemma fin_le_last_val_2 (n : ℕ) : ∀ i : fin (n + 2), i ≤ (n+1) :=
begin
  intro i,
  change i.val ≤ ((_ + _) : fin (n+2)).val,
  norm_cast,
  have := i.2,
  rw fin.coe_val_of_lt; omega
end

lemma fin_zero_le_any_val (n : ℕ) : ∀ i : fin (n + 2), 0 ≤ i :=
begin
    intro i,
    have j0 : 0 < n + 1 + 1, linarith,
    have j0 := @fin.coe_val_of_lt (n+1) 0 j0,
    have h3 : 0 ≤ i.val, linarith,
    apply fin.le_iff_val_le_val.mpr,
    rw ← j0 at h3,
    exact h3,
end

lemma fin_lt_succ_v0 (n : ℕ) (i : fin (n + 1)) : (i : fin (n+2)) < ((i+1) : fin (n+2)) :=
begin
    apply fin.lt_iff_val_lt_val.mpr,
    have h1 : i.val < n+2, linarith [i.2],
    have h2 := @fin.coe_val_of_lt (n+1) i.val h1,
    have h3 := fin.coe_coe_of_lt h1,
    sorry,
end

-- Again thanks to Shing Tak Lam
lemma fin_lt_succ (n : ℕ) (i : fin (n + 1)) : (i : fin (n+2)) < (i+1) :=
begin
  cases i with i hi,
  change (_ : fin (n+2)).val < (_ : fin (n+2)).val,
  simp only [fin.coe_mk, coe_coe],
  norm_cast,
  rw [fin.coe_val_of_lt, fin.coe_val_of_lt]; omega,
end

-- Result below thanks to Sebastien Gouezel
lemma sgouezel 
    (a b : ℝ) (f : ℝ → ℝ) (n : ℕ) (hf : times_cont_diff_on ℝ (n+1) f (Ioo a b) ) :
    times_cont_diff_on ℝ n (deriv f) (Ioo a b) :=
begin
  have : deriv f = (λ u : ℝ →L[ℝ] ℝ, u 1) ∘ (fderiv ℝ f), by { ext x, refl },
  simp only [this],
  have : times_cont_diff_on ℝ n (fderiv ℝ f) (Ioo a b),
  { apply ((times_cont_diff_on_succ_iff_fderiv_within (unique_diff_on_Ioo a b)).1 hf).2.congr,
    assume x hx,
    calc fderiv ℝ f x = fderiv_within ℝ f univ x : by simp
    ... = fderiv_within ℝ f (univ ∩ Ioo a b) x :
      (fderiv_within_inter (Ioo_mem_nhds hx.1 hx.2) unique_diff_within_at_univ).symm
    ... = fderiv_within ℝ f (Ioo a b) x : by simp },
  apply times_cont_diff.comp_times_cont_diff_on _ this,
  exact (is_bounded_bilinear_map_apply.is_bounded_linear_map_left _).times_cont_diff
end

lemma one_step (n : ℕ) (x : fin (n+2) → ℝ) (hx : strict_mono x) :
    ∀ (f : ℝ → ℝ), continuous_on f ( Icc (x 0) (x (n+1)) ) → 
    (∀ i, f (x i) = 0)  →
    ∃ (xp : fin(n+1) → ℝ), strict_mono xp ∧ 
        ∀ (i : fin (n+1)), xp i ∈ ( Ioo (x 0) (x (n+1)) ) ∧ deriv f (xp i) = 0 :=
begin
    intros f hf hxi,
    have h1 : ∀ (i : fin (n+1)), ∃ y ∈ (Ioo (x i) (x (i+1))), deriv f y = 0,
        intro i,
        apply exists_deriv_eq_zero,
        -- show x i < x (i+1)
        exact hx (fin_lt_succ n i),
        -- show f continuous on Icc (x i) (x (i+1))
        have h02 : Icc (x i) (x (i+1)) ⊆ Icc (x 0) (x (n+1)),
            intros z hz,
            cases hz with hz1 hz2,
            split,
            have g3 := (strict_mono.le_iff_le hx).mpr (fin_zero_le_any_val n i),
            linarith, -- use strict_mono x
            have h020 := fin_le_last_val n (i+1), 
            have g3 := (strict_mono.le_iff_le hx).mpr h020,
            linarith,
        exact continuous_on.mono hf h02,
        -- show f (x i) = f (x (i+1))
        rw [hxi i, hxi (i+1)],
        -- this is just normal Rolle, exists_deriv_eq_zero
    choose xp hxp using h1, 
    use xp, split,
    intros i j hij,
    have hi := (hxp i).1, have hj := (hxp j).1,
    cases hi with hi1 hi2, cases hj with hj1 hj2,
    rcases lt_trichotomy ((i+1) : fin (n+2) ) (j : fin (n+2)) with h1|h2|h3,
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
        have heq : f (x 0) = f (x 1), rw [hi 0, hi 1],
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
        have hf1 : times_cont_diff_on ℝ d.succ f (Ioo (x 0) (x (d.succ+1))),
            have hf11 : Ioo (x 0) (x (d.succ + 1)) ⊆ Icc (x 0) (x (d.succ + 1)), 
                exact Ioo_subset_Icc_self,
            exact times_cont_diff_on.mono hf hf11,
        have hder0 := sgouezel (x 0) (x (d.succ +1)) f d hf1,
        have hder : times_cont_diff_on ℝ d g (Icc (xp 0) (xp (d+1))),
            have hdr0 : Icc (xp 0) (xp (d+1)) ⊆ Ioo (x 0) (x (d.succ + 1)), 
                intros z hz,
                cases hz with hz1 hz2,
                split,
                cases (hxpi 0).1 with h0z0 h0z1, linarith,
                cases (hxpi d.succ).1 with hdz0 hdz1,
                norm_cast at hz2, linarith,
            exact times_cont_diff_on.mono hder0 hdr0,
        have hdg := hd xp hxpx g hder, clear hd,
        have H1 : ∀ i, g (xp i) = 0, 
            intro i,
            have H10 := hxpi i, cases H10 with H101 H102, exact H102,  
        have G := hdg H1,
        have K : iterated_deriv (d.succ + 1) f = iterated_deriv d.succ g,
            apply iterated_deriv_succ',
        rw ← K at G,
        cases G with c hc,
        use c,
        cases hc with hc1 hc2,
        split, swap, exact hc2,
        have hxp0 := (hxpi 0).1, cases hxp0 with hxp01 hxp02,
        cases hc1 with hc10 hc11,
        split, linarith,
        have hxp1 := (hxpi d.succ).1, cases hxp1 with hxp11 hxp12,
        have hxpeq0 : d+1 = d.succ, rw nat.succ_eq_add_one,
        have hxpeq1 : ((d+1) :  fin (d.succ + 1) ) = d.succ,
            norm_cast, 
        rw hxpeq1 at hc11,
        linarith,
    },
    done
end

end rolle_general

