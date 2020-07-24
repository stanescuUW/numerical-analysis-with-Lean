import data.real.basic
import uwyo_sqrt2

lemma aux_0 (X : ℚ) (hX: 0 < X): ( X * X + 2) / (2 * X) - X = (2 - X * X) / (2 * X) :=
begin
  set Y := X * X with hY,
  have h1 : 2 - Y = 2 + Y - 2 * Y, linarith,
  rw add_comm 2 Y at h1,
  rw h1,
  set V := 2 * X with hV,
  have h31 : V ≠ 0, linarith,
  have h2 := sub_div (Y+2) (2*Y) V,
  rw h2,
  have h32 : (2 * Y) / V = X, 
    apply (div_eq_iff h31).mpr,
    rw [hY, hV], ring,
  rw h32,
  done
end

lemma aux_1 (X Y V : ℚ) (G : X ≠ 0) (hY : Y = X * X) (hV : V = 2 * X) (G1 : Y ≠ 0) : 
  4 * (Y + 2) / V * ((Y + 2) / (V)) = Y + 2 * 2 + (2*2/(X * X)) :=
begin
  -- this is a struggle
      rw hV, rw hY,
      norm_num, field_simp,
      have h211 : 2 * X * ( 2 * X ) = 4 * X * X,
        ring,
      rw h211, rw mul_assoc 4 X X,
      rw ← hY, field_simp,
      rw mul_assoc,
      have h212 : (Y+2) * (Y + 2) = Y * Y + 4 * Y +4, ring,
      rw h212, 
      set T := 4 * (Y * Y + 4 * Y + 4) with hT,
      rw ← hT,
      have h214 : (4: ℚ) ≠ 0, linarith,
      have h213 : 4 * Y ≠ 0, exact mul_ne_zero h214 G1,
      apply (div_eq_iff h213).mpr,
      have h214 : (Y + 4 + (4/Y)) * (4 * Y) = (Y+4) * (4*Y) + (4/Y) * (4 * Y), 
        ring,
      rw h214,
      have h215 : (4/Y) * (4 * Y) = 16, ring, 
        rw mul_assoc,
        have h216 : Y * Y⁻¹ = 1, exact mul_inv_cancel G1,
        rw h216, linarith,
      rw h215,
      rw hT, ring, done
end

lemma aux_2 (X : ℚ) (G : X ≠ 0) : ( 2 / X - X ) * ( 2 / X - X ) = 4 / (X*X) - 4 + X * X :=
begin
  set V := (2/X) with hV,
  have h1 : V * V = 4 / (X * X), 
    rw hV, ring, field_simp,
    have h11 : X ^ 2 = X * X, ring,
    rw h11,
  rw ← h1,
  have h2 : (V - X) * (V - X) = V * V - 2 * V * X + X * X, ring,
  rw h2,
  have h3 : V * X = 2, field_simp, ring, rw mul_assoc, rw mul_comm X⁻¹ _,
    rw mul_inv_cancel G, linarith,
  rw mul_assoc 2 V X, rw h3,
  linarith,
end 

lemma no_rat_sq_eq_two (X : ℚ) (hX1 : X ≠ 0) :  0 ≠ ( 2 / X - X ) :=
begin
  by_contradiction H,
  push_neg at H,
  have h1 := congr_arg (λ (b : ℚ), X * b) H,
  simp only [] at h1,
  rw mul_zero at h1,
  have h2 : X * (2 / X - X) = 2 - X ^ 2, 
    ring, 
    have h21 : ( - X + 2 * X⁻¹) * X = - X * X + 2 * X⁻¹ * X, ring,
    rw h21, rw mul_assoc 2 (X⁻¹) X, rw mul_comm (X⁻¹) _, rw mul_inv_cancel hX1,
    ring,
  rw ← h1 at h2,
  have h2 : X ^ 2 = 2, linarith,
  have h3 : ∃ r : ℚ, r ^ 2 = 2,
    use X, exact h2,
  exact rational_not_sqrt_two h3, -- from uwyo_sqrt2
  done
end
