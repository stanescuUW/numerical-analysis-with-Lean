import data.nat.prime
import data.rat.basic
import data.real.basic
import tactic

-- could use:
-- (univ : set X)
-- to have X be recognized as a subset of X
-- X has Type u for some universe u; it doesn't have type set X

theorem sqrt_two_irrational {a b : ℕ} (co : nat.gcd a b = 1) : a^2 ≠ 2 * b^2 :=
begin
    intro h,
    have h1 : 2 ∣ a^2, simp [h],
    have h2 : 2 ∣ a, from nat.prime.dvd_of_dvd_pow nat.prime_two h1,
    cases h2 with c aeq,
    have h3 : 2 * ( 2 * c^2) = 2 * b^2,
        by simp [eq.symm h, aeq]; 
           simp [nat.pow_succ, mul_comm, mul_assoc, mul_left_comm],
    have h4 : 2 * c^2 = b^2,
        from nat.eq_of_mul_eq_mul_left dec_trivial h3,
    have h5 : 2 ∣ b^2, by simp [eq.symm h4],
    have hb : 2 ∣ b, from nat.prime.dvd_of_dvd_pow nat.prime_two h5,
    have ha : 2 ∣ a, from nat.prime.dvd_of_dvd_pow nat.prime_two h1,
    have h6 : 2 ∣ nat.gcd a b, from nat.dvd_gcd ha hb,
    have habs : 2 ∣ (1 : ℕ), by 
        {rw co at h6, exact h6},
    have h7 : ¬ 2 ∣ 1, exact dec_trivial,
    exact h7 habs, done
end

-- Some simple preliminary results. Not really needed, but they make the proof shorter
lemma rat_times_rat (r : ℚ) : r * r * ↑(r.denom) ^ 2 = ↑(r.num) ^ 2 :=
begin
    have h1 := @rat.mul_denom_eq_num r,
    rw pow_two,
    rw mul_assoc, rw ← mul_assoc r r.denom r.denom,
    rw h1, rw ← mul_assoc, rw mul_comm, rw ← mul_assoc,
    rw mul_comm ↑r.denom r, rw h1, rw pow_two, done
end
#check nat.coprime.pow
#check nat.coprime.pow_left
#check nat.coprime.dvd_of_dvd_mul_left
#check nat.coprime.coprime_dvd_left

theorem rational_not_sqrt_two : ¬ ∃ r : ℚ, r ^ 2 = (2:ℚ)  := 
begin
    intro h,
    cases h with r H,
    let num := r.num, set den := r.denom with hden,
    --explicitly build the hypothetical rational number r
    have hr := @rat.num_denom r,
    rw ← hr at H, -- use it in the main assumption
    -- now we can figure out some properties of r.num and r.denom
    -- first off, the denominator is not zero; this is encoded in r.
    have hdenom := r.pos,  -- the denom is actually positive
    have hdne : r.denom ≠ 0, linarith, -- so it is non zero; linarith can handle that
    set n := int.nat_abs num with hn1,
    have hn : (n ^2 : ℤ) = num ^ 2,
        norm_cast, rw ← int.nat_abs_pow_two num, rw ← int.coe_nat_pow,
    have G : (2:ℚ) * (r.denom ^2) = (r.num ^ 2),
        rw ← H, norm_cast, simp,
        rw pow_two r, simp * at *,
        exact rat_times_rat r,
    norm_cast at G,
    rw ← hn at G,
    have g1 : nat.gcd n den = 1, 
        have g11 := r.cop, 
        unfold nat.coprime at g11,
        have g12 := nat.coprime.pow_left 2 g11,
        have g13 := nat.coprime.coprime_mul_left g12,
        rw ← hn1 at g13, exact g13,
    have E := sqrt_two_irrational g1,
    have g2 := G.symm, 
    norm_cast at g2,
    done
end

example (a b : ℝ) : a = b → a^2 = b^2 := by library_search

-- some extra stuff on rationals from Zulip
--import data.rat.basic tactic

lemma rat_id01 {a b : ℤ} (hb0 : 0 < b) (h : nat.coprime a.nat_abs b.nat_abs) :
  (a / b : ℚ).num = a ∧ ((a / b : ℚ).denom : ℤ) = b :=
begin
  lift b to ℕ using le_of_lt hb0,
  norm_cast at hb0 h,
  rw [← rat.mk_eq_div, ← rat.mk_pnat_eq a b hb0, rat.mk_pnat_num, rat.mk_pnat_denom,
    pnat.mk_coe, h.gcd_eq_one, int.coe_nat_one, int.div_one, nat.div_one],
  split; refl
end

--import data.rat.basic tactic

lemma rat_id02 {a b : ℤ} (hb0 : 0 < b) (h : nat.coprime a.nat_abs b.nat_abs) :
  (a / b : ℚ).num = a ∧ ((a / b : ℚ).denom : ℤ) = b :=
begin
  lift b to ℕ using le_of_lt hb0,
  norm_cast at hb0 h,
  rw [← rat.mk_eq_div, ← rat.mk_pnat_eq a b hb0],
  split; simp [rat.mk_pnat_num, rat.mk_pnat_denom, h.gcd_eq_one]
end