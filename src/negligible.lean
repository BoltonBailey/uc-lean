
import data.polynomial.basic
import data.polynomial.eval

/-- definition of a negligible function -/
def negligible (f : ℕ → ℚ) : Prop := 
  ∃ p : polynomial ℕ, ∀ n : ℕ,
    (f n : ℚ)  ≤ (1 : ℚ) / p.eval n

lemma add_negligible (f g : ℕ → ℚ) (hf : negligible f) (hg : negligible g) : negligible (f + g) :=
begin
  unfold negligible at *,
  rcases hf with ⟨pf, hpf⟩,
  rcases hg with ⟨pg, hpg⟩,
  use (pg * pf),
  intro n,
  replace hpf := hpf n,
  replace hpg := hpg n,
  simp only [pi.add_apply, polynomial.eval_mul, nat.cast_mul],
  apply le_trans (add_le_add hpf hpg),
  simp,
  rw le_inv_iff_mul_le_one_left,
  simp_rw [le_div_iff],
end