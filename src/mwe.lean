import analysis.specific_limits

open_locale topological_space 
open filter 

example (s : ℕ → ℝ) (hs : ∀ n : ℕ, 2 < s n) : ¬ (tendsto s at_top (𝓝 0)) :=
begin
   sorry,
end
