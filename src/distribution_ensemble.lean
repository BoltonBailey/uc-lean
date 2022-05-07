
import measure_theory.probability_mass_function.basic
import topology.algebra.infinite_sum
import data.polynomial.eval
import .negligible

noncomputable theory
open_locale classical big_operators nnreal ennreal 

-- open polynomial

-- We define ℕ-indexed distribution ensembles where the distributions are discrete, i.e. given by pmfs.

def ensemble (α : Type) : Type := ℕ → pmf α


-- lemma tsum_zero {α β : Type} [add_comm_monoid α] [topological_space α] : tsum (0 : β → α) = 0


variables {α : Type}

-- TODO send to mathlib. see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Total.20variation.20distance.20on.20pmf/near/281214430
instance total_variation : metric_space (pmf α) := sorry
-- { dist := λ u v, tsum (abs ((↑(u : α → ℝ≥0) : α → ℝ) - ↑(v : α → ℝ≥0))),
--   dist_self := by {intros x, cases x, simp only [sub_self], rw abs_zero, }, -- diamond
--   dist_comm := by {sorry,},
--   dist_triangle := _,
--   edist := _,
--   edist_dist := _,
--   to_uniform_space := _,
--   uniformity_dist := _,
--   eq_of_dist_eq_zero := _ }


def statistically_indistinguishable (a b : ensemble α) : Prop :=
negligible (λ n, dist (a n) (b n)) 

notation x ` ≈ₛ ` y := statistically_indistinguishable x y

def reflexive_statistically_indistinguishable : reflexive (@statistically_indistinguishable α) :=
begin
  intros x p, 
  simp only [dist_self, one_div, inv_nonneg, nat.cast_nonneg, implies_true_iff, exists_const],
end

def symmetric_statistically_indistinguishable : symmetric (@statistically_indistinguishable α) :=
begin
  intros x y hxy, 
  unfold statistically_indistinguishable at *,
  simp_rw dist_comm,
  exact hxy,
end

def transitive_statistically_indistinguishable : transitive (@statistically_indistinguishable α) :=
begin
  intros x y z hxy hyz, 
  unfold statistically_indistinguishable at *,
  apply negligible_of_le_negligible _ (negligible_add hxy hyz),
  intro n,
  simp only [pi.add_apply],
  exact dist_triangle (x n) (y n) (z n),
end