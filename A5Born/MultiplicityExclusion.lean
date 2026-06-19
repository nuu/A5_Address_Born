import Mathlib

/-!
# Multiplicity-measure exclusion  (companion to `BornFromDiscreteness.lean`)

Decidable arithmetic core of Proposition `prop:multiplicity-excluded`.

The dimension-linear / multiplicity profile `n ρ / 16` cannot be the
maximally-mixed Born statistics of any *projective* measurement on `ℂ[A₅]`,
because such statistics lie in `(1/60)·ℤ` whereas
`60·(n ρ / 16) = 15·n ρ / 4` is non-integral for four of the five labels.

## Scope (firewall)

Verified here: the *decidable arithmetic* obstruction, plus realisability of the
capacity profile by an integer rank vector summing to `60`.

Imported, NOT re-proved here: the representation-theoretic identity
`rank π_ρ = n_ρ²` (so that the capacity profile *is* a projective Born profile)
and the canonicity of the central resolution `{π_ρ}` — these come from the
Plancherel / isotypic development (`BornFromDiscreteness.lean`,
`BornFromA5Opacity.lean`).

## Verification status

Authored WITHOUT a local Lean+Mathlib toolchain and NOT compiled in that
environment. Check with `lake build`. Minor tactic / lemma-name adjustments may
be needed for your exact Mathlib pin. Run the `#print axioms` lines below to
confirm `axiom = 0`. (No `native_decide` is used in this file.)
-/

namespace A5Born.Multiplicity

/-- Irreducible dimensions of `A₅`: `0 ↦ 𝟏, 1 ↦ 𝟑, 2 ↦ 𝟑', 3 ↦ 𝟒, 4 ↦ 𝟓`. -/
def n : Fin 5 → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 3
  | 3 => 4
  | 4 => 5

/-- Capacity (Artin–Wedderburn block dimension) `n ρ ²`. -/
def cap : Fin 5 → ℕ := fun ρ => (n ρ) ^ 2

/-- Plancherel: the capacity profile sums to `|A₅| = 60`. -/
theorem cap_sum : (∑ ρ, cap ρ) = 60 := by decide

/-- Integrality obstruction, clean form: `4 ∤ n ρ` for some `ρ` (witness `𝟏`).
Equivalent to `60·(n ρ / 16) ∉ ℤ`. -/
theorem multiplicity_obstruction : ∃ ρ : Fin 5, ¬ (4 ∣ n ρ) := by decide

/-- Same obstruction in the `16 ∣ 60·n ρ` form. -/
theorem multiplicity_not_div : ∃ ρ : Fin 5, ¬ (16 ∣ 60 * n ρ) := by decide

/-- Sharper count: the obstruction holds for exactly four of the five labels
(only `𝟒` has `4 ∣ n ρ`). -/
theorem multiplicity_count :
    (Finset.univ.filter fun ρ : Fin 5 => ¬ (4 ∣ n ρ)).card = 4 := by decide

/-- A profile `p : Fin 5 → ℚ` is *projectively realisable* in the maximally
mixed state on the 60-dimensional regular module iff it equals `r / 60` for an
integer rank vector `r` summing to `60`. (This is exactly the shape of the
maximally-mixed Born statistics of a projective measurement: `P i = rank Qᵢ/60`.) -/
def Realisable (p : Fin 5 → ℚ) : Prop :=
  ∃ r : Fin 5 → ℕ, (∑ ρ, r ρ) = 60 ∧ ∀ ρ, (60 : ℚ) * p ρ = (r ρ : ℚ)

/-- Capacity profile `n ρ ² / 60`. -/
def capQ : Fin 5 → ℚ := fun ρ => ((n ρ : ℚ)) ^ 2 / 60

/-- Multiplicity profile `n ρ / 16`. -/
def multQ : Fin 5 → ℚ := fun ρ => (n ρ : ℚ) / 16

/-- The capacity profile **is** projectively realisable (witness `r = cap`). -/
theorem capacity_realisable : Realisable capQ := by
  refine ⟨cap, cap_sum, ?_⟩
  intro ρ
  fin_cases ρ <;> norm_num [capQ, cap, n]

/-- The multiplicity profile is **not** projectively realisable: realisability
would force `60·(n 𝟏 / 16) = 15/4` to be a natural number. -/
theorem multiplicity_not_realisable : ¬ Realisable multQ := by
  rintro ⟨r, _, hr⟩
  have h0 := hr 0
  have hn : (n 0 : ℚ) = 1 := by norm_num [n]
  simp only [multQ] at h0
  rw [hn] at h0
  -- h0 : 60 * (1 / 16) = (r 0 : ℚ)
  have h1 : (4 : ℚ) * (r 0 : ℚ) = 15 := by rw [← h0]; norm_num
  have h2 : (4 : ℤ) * (r 0 : ℤ) = 15 := by exact_mod_cast h1
  omega

/-- Sanity check: the two profiles differ already at `𝟏` (`1/60 ≠ 1/16`). -/
theorem capQ_ne_multQ : capQ ≠ multQ := by
  intro h
  have h0 := congrArg (fun f => f 0) h
  norm_num [capQ, multQ, n] at h0

-- Axiom audit (run after `lake build`):
-- #print axioms cap_sum
-- #print axioms multiplicity_obstruction
-- #print axioms capacity_realisable
-- #print axioms multiplicity_not_realisable

end A5Born.Multiplicity
