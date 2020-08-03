import analysis.calculus.local_extr
import analysis.calculus.times_cont_diff
import analysis.calculus.iterated_deriv
import tactic
open set

namespace rolle_v0

structure pts (n : ℕ) (A B : ℝ) := 
( a   : ℕ → ℝ )
( ha  : ∀ (i j : ℕ), i < j → a i < a j )
( hA  : a 0 = A )
( hB  : a (n+1) = B )
--( hfx : ∀ (i : fin (n+2)), f (a i) = 0 )


theorem general_rolle_v2 (n : ℕ) (A B : ℝ) (hAB : A < B)
    (f : ℝ → ℝ) (hf : times_cont_diff_on ℝ n f (Icc A B)) 
    (H : ∃ (x : pts n A B),  ∀ (i : ℕ), f (x.a i) = 0 ) :
    ∃ c ∈ Ioo A B, iterated_deriv (n+1) f c = 0 :=
begin
    induction n with d hd,
    { -- base case
        cases H with x hfx,
        norm_cast at hf,
        rw times_cont_diff_on_zero at hf,
        have h1 := x.hA,
        have h2 := x.hB, rw zero_add at h2,
        have hx1 := hfx 0, rw h1 at hx1,
        have hx2 := hfx 1, rw h2 at hx2,
        rw zero_add,
        have heq : f A = f B, linarith,
        have H := exists_deriv_eq_zero f hAB hf heq,
        rw ← iterated_deriv_one at H,
        exact H,
    },
    { -- induction step
        -- from hf obtain that f is d-times differentiable
        -- so there are those (d+2) points where f is zero
        set g : ℝ → ℝ := deriv f with hg,
        have h1 : times_cont_diff_on ℝ ↑d g (Icc A B), sorry, --from hf
        have h2 : ∃ (x : pts d A B),  ∀ (i : ℕ), g (x.a i) = 0, 
            sorry, --can get these using H
        -- so now how can I use the induction hypothesis on g???
        sorry, 
    },
    done
end


lemma general_rolle_v1 (n : ℕ) (A B : ℝ) (hAB : A < B) : 
    ∀ (f : ℝ → ℝ), ∀ (a : fin (n+2) → ℝ), ∀ (k : fin (n+2)), f (a k) = 0 →
    ∀ (i j : fin(n+2)), i < j → a i < a j → 
    a 0 = A ∧ a (n+1) = B → 
    times_cont_diff_on ℝ n f (Icc A B) → 
    ∃ c ∈ Ioo A B, iterated_deriv (n+1) f c = 0 :=
begin
   induction n with d hd,
   { -- base case, should revert to Rolle
        intros f a k hak i j hij haij haAB hf,
        norm_cast at hf,
        --have H : 0 + 2 = 2, linarith,
        --rw H at a k,
        rw times_cont_diff_on_zero at hf,
        set i0 : fin (0+2) := 0 with hi0,
        set j0 : fin (0+2) := 1 with hj0,
        --specialize i i0,
        --specialize ha0 : hak 0,
        have heq : f A = f B, sorry,
        have H := exists_deriv_eq_zero f hAB hf heq,
       sorry, 
   },
   {  intro f,
      set g := deriv f with hg,
      have h1 := hd g,
      sorry,
   },
   done
end

end rolle_v0

namespace rolle_v1


structure pts (n : ℕ) (A : ℝ) (B : ℝ) (f : ℝ → ℝ):= 
( a   : fin (n+2) → ℝ )
( hAB : A < B )
( ha  : ∀ (i j : fin (n+2)), i < j → a i < a j )
( hA  : a 0 = A )
( hB  : a (n+1) = B )
( hfx : ∀ (i : fin (n+2)), f (a i) = 0 )

variables (m : ℕ) (C D : ℝ) (h : ℝ → ℝ)


theorem general_rolle_v2 (n : ℕ) (A B : ℝ) :
    ∀ (f : ℝ → ℝ),
    ∀ (x : pts n A B f),  times_cont_diff_on ℝ n f (Icc A B) → 
    ∃ c ∈ Ioo A B, iterated_deriv (n+1) f c = 0 :=
begin
    induction n with d hd,
    { -- base case
        --rintros ⟨f⟩,
        intros f x hf,
        norm_cast at hf,
        rw times_cont_diff_on_zero at hf,
        have h1 := x.hA,
        have h20 := x.hB, 
        have h2 : x.a 1 = B,
            norm_cast at h20, exact h20, clear h20,
        have hx1 := x.hfx 0, rw h1 at hx1,
        have hx2 := x.hfx 1, rw h2 at hx2,
        rw zero_add,
        have heq : f A = f B, linarith,
        have H := exists_deriv_eq_zero f x.hAB hf heq,
        rw ← iterated_deriv_one at H,
        exact H,
    },
    { -- induction step
        intros f xf hf,
        set g : ℝ → ℝ := deriv f with hg,
        have h0 := hd g,
        -- construct the points where g is zero
        let xg : pts d A B g := 
            {   a := sorry,
                hAB := xf.hAB,
                ha := sorry,
                hA := sorry,
                hB := sorry,
                hfx := sorry},
        have h1 := h0 xg, 
        -- show that g is Cᵈ 
        have h2 : times_cont_diff_on ℝ ↑d g (Icc A B), sorry, --from hf
        -- so now the result should follow from 
        have h3 := h1 h2,
        sorry, 
    },
    done
end


end rolle_v1

namespace rolle_v2


structure pts (n : ℕ) (A B : ℝ) := 
( a   : fin (n+2) → ℝ )
( ha  : ∀ (i j : fin (n+2)), i < j → a i < a j )
( hA  : a 0 = A )
( hB  : a (n+1) = B )
--( hfx : ∀ (i : fin (n+2)), f (a i) = 0 )

lemma construct_x (A B : ℝ) : pts 0 A B := sorry 

theorem general_rolle (n : ℕ) (A B : ℝ) (hAB : A < B) :
    ∀ (f : ℝ → ℝ), ∃ (x : pts n A B), ∃ (hi :  ∀ (i : fin (n+2)), f (x.a i) = 0 ),
    times_cont_diff_on ℝ n f (Icc A B) → 
    ∃ c ∈ Ioo A B, iterated_deriv (n+1) f c = 0 :=
begin
    induction n with d hd,
    { -- base case
        intro f,
        have myX := construct_x A B,
        use myX,
        intros hi,
        --cases H with x hfx,
        norm_cast at hf,
        rw times_cont_diff_on_zero at hf,
        have h1 := myX.hA,
        have h20 := myX.hB, 
        have h2 : myX.a 1 = B,
            norm_cast at h20, exact h20, -- now I need f (a 0) = 0, how???
        have hx1 := hfx 0, rw h1 at hx1,
        have hx2 := hfx 1, rw h2 at hx2,
        rw zero_add,
        have heq : f A = f B, linarith,
        have H := exists_deriv_eq_zero f hAB hf heq,
        rw ← iterated_deriv_one at H,
        exact H,
    },
    { -- induction step
        -- so there are those (d+2) points where f is zero
        set g : ℝ → ℝ := deriv f with hg,
        have h1 : times_cont_diff_on ℝ ↑d g (Icc A B), sorry, --from hf
        have h2 : ∃ (x : pts d A B),  ∀ (i : ℕ), g (x.a i) = 0, 
            sorry, --can get these using H
        -- so now how can I use the induction hypothesis on g???
        sorry, 
    },
    done
end


end rolle_v2

namespace rolle_v3

lemma one_step (n : ℕ) (a b : ℝ) (f : ℝ → ℝ) 
    (hf : continuous_on f (Icc a b))
    (hx : ∃ (x : fin(n+2) → ℝ), 
        ∀ (i j : fin (n+2)), x i ∈ (Icc a b) ∧ f (x i) = 0 ∧ (i < j → x i < x j) ) :
    ∃ (xp : fin(n+1) → ℝ), ∀ (i j : fin (n+1)), xp i ∈ (Icc a b) ∧  --can change Ioo
    deriv f (xp i) = 0 ∧ (i < j → xp i < xp j) :=
begin
    cases hx with x hx1,
    have h1 : ∀ (i : fin (n+1)), ∃ y ∈ (Ioo (x i) (x (i+1))), deriv f y = 0,
        sorry,
    choose xp hxp using h1, 
    use xp,
    intros i j,
    split,
    sorry,
    sorry,
end

theorem general_rolle (n : ℕ) (A B : ℝ) (hAB : A < B) :
    ∀ (f : ℝ → ℝ), times_cont_diff_on ℝ n f (Icc A B) → 
    (∃ (x : fin(n+2) → ℝ), 
        ∀ (i j : fin (n+2)), x i ∈ (Icc A B) ∧ f (x i) = 0 ∧ (i < j → x i < x j) ) → 
    ∃ c ∈ Ioo A B, iterated_deriv (n+1) f c = 0 :=
begin
    induction n with d hd,
    { -- base case, just plain Rolle `exists_deriv_eq_zero`
        intros f hf hg,
        norm_cast at hf,
        rw times_cont_diff_on_zero at hf,
        cases hg with x hx,
        have h1 := hx 0 1,
        have h2 := hx 1 1,
        cases h1 with h11 h12, cases h12 with h121 h122,
        cases h2 with h21 h22, cases h22 with h221 h222, clear h222,
        have h3 : 0 < 1, linarith,
        have h4 := h122 h3, clear h122,
        have h41 : continuous_on f (Icc (x 0) (x 1)), 
            have h412 : (Icc (x 0) (x 1)) ⊆ Icc A B, sorry,
            exact continuous_on.mono hf h412,
        have h42 : f (x 0) = f (x 1), rw [h121, h221], 
        have h5 := exists_deriv_eq_zero f h4 h41 h42, 
        cases h5 with c hc, cases hc with hc1 hc2,
        have h6 : c ∈ Ioo A B, 
            cases hc1 with h61 h62,
            cases h11 with h111 h112,
            have h71: A < c, linarith,
            cases h21 with h211 h212,
            have h72 : c < B, linarith,
            split, exact h71, exact h72,
        rw iterated_deriv_one,
        use [c, h6], exact hc2,
    },
    { -- induction step
        -- the derivative is in Cᵈ
        intros f hf hxf,
        set g := deriv f with hg,
        have hder : times_cont_diff_on ℝ d g (Icc A B),
            sorry, 
        have hdg := hd g hder, clear hd,
        -- the function is continuous
        have hfc : continuous_on f (Icc A B), sorry, 
        have H := one_step d.succ A B f hfc hxf,
        have G := hdg H,
        have K : iterated_deriv (d+1) g = iterated_deriv (d.succ + 1) f,
            sorry,
        rw K at G,
        exact G,
    },
    done
end

theorem general_rolle_yury (n : ℕ) (A B : ℝ) (hAB : A < B) :
    ∀ (f : ℝ → ℝ), times_cont_diff_on ℝ n f (Icc A B) → 
    (∃ (x : fin(n+2) → ℝ), strict_mono x ∧ (∀ (i : fin (n+2)), x i ∈ (Icc A B) ∧ f (x i) = 0) ) → 
    ∃ c ∈ Ioo A B, iterated_deriv (n+1) f c = 0 := sorry


end rolle_v3

/-

lemma check_ind (n : ℕ) : ∀ (f : ℝ → ℝ), 
    ∃ (a : fin (n+2) → ℝ), ∀ (k : fin (n+2)), f (a k) = 0 →
    ∀ (i j : fin(n+2)), i < j, a i < a j → 
    times_cont_diff_on ℝ n f (Icc (a 0) (a (n+1))) → 
    ∃ c ∈ Ioo (a 0) (a (n+1) ), iterated_deriv (n+1) f c = 0 :=
begin
    sorry,
end

-/




------------------ Scratch space below here ------------------------------