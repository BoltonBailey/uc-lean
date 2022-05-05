
import data.polynomial.basic
import data.polynomial.eval
import data.real.basic

/-- definition of a negligible function -/
def negligible (f : ℕ → ℝ) : Prop := 
  ∀ p : polynomial ℕ, ∃ N : ℕ, ∀ n : ℕ, N < n →
    (f n : ℝ) ≤ (1 : ℝ) / p.eval n

lemma negligible_add {f g : ℕ → ℝ} (hf : negligible f) (hg : negligible g) : negligible (f + g) :=
begin
  unfold negligible at *,
  intro p,
  replace hf := hf (2 * p),
  replace hg := hg (2 * p),
  rcases hf with ⟨Nf, hpf⟩,
  rcases hg with ⟨Ng, hpg⟩,
  use (max Nf Ng),
  intro n,
  replace hpf := hpf n,
  replace hpg := hpg n,
  intro hNfg,
  have hNf : Nf < n, -- library_search, -- fails
    apply lt_of_le_of_lt _ hNfg,
    exact le_max_left Nf Ng,
  have hNg : Ng < n, -- library_search, -- fails
    apply lt_of_le_of_lt _ hNfg,
    exact le_max_right Nf Ng,
  replace hpf := hpf hNf,
  replace hpg := hpg hNg,    
  simp only [pi.add_apply, polynomial.eval_mul, nat.cast_mul],
  have hpfg := (add_le_add hpf hpg),
  apply trans hpfg,
  simp,
  simp_rw mul_inv₀,
  rw ←one_div,
  linarith,
end

lemma negligible_of_le_negligible {f g : ℕ → ℝ} (hfg : f ≤ g) (hg : negligible g) : negligible f :=
begin
  unfold negligible at *,
  intro p,
  replace hg := hg (p),
  rcases hg with ⟨Ng, hpg⟩,
  use Ng,
  intro n,
  replace hpg := hpg n,
  intro hNg,
  replace hpg := hpg hNg,    
  exact le_trans (hfg n) hpg,
end