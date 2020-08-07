import data.fin
import tactic

-- This does exist in mathlib
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

lemma fin_zero_le_any_val_v1 (n : ℕ) (i : fin (n + 1)) : 0 ≤ i :=
fin.le_iff_val_le_val.mpr $ nat.zero_le _

-- This exists in mathlib, but in a form that is not immediately useful
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

lemma fin_le_last_val_v1 (n : ℕ) (i : fin (n + 1)) : i ≤ n :=
fin.le_iff_val_le_val.mpr $ (fin.coe_val_of_lt $ nat.lt_succ_self n).symm ▸ nat.le_of_lt_succ i.2

lemma fin_le_last_val_v2 (n : ℕ) : ∀ i : fin (n + 2), i ≤ (n+1) :=
begin
  intro i,
  change i.val ≤ ((_ + _) : fin (n+2)).val,
  norm_cast,
  have := i.2,
  rw fin.coe_val_of_lt; omega
end

-- This is very particular, only needed in my own proof
-- This is courtesy Shing Tak Lam
lemma shing (n : ℕ) (i j : fin (n+1)) (h : (j.val : fin (n+2)) < (i.val.succ : fin (n+2))) : 
    j.val < i.val.succ :=
begin
  change (j.val : fin (n+2)).val < (i.val.succ : fin (n+2)).val at h,
  rwa [fin.coe_val_of_lt (show j.1 < n + 2, by linarith [j.2]),
       fin.coe_val_of_lt (show i.1 + 1 < n + 2, by linarith [i.2])] at h,
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

