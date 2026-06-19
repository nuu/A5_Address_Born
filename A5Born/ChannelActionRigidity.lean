import Mathlib

/-!
# Channel-side action rigidity  (companion to `BornFromDiscreteness.lean`)

Decidable / finite core of Lemma `lem:channel-action-rigidity` and the abstract
algebraic core of Corollary `cor:obs-law-invariant`.

## Scope (firewall)

Verified here: the rigidity at the level of *permutations of the five
irreducible labels* (the only dimension-preserving permutations are the identity
and the `𝟑↔𝟑'` swap), invariance of the capacity weight `mu` under such
permutations, and the weighted-composition invariance `P (t a) = P a`.

Imported, NOT re-proved here: the representation-theoretic bridge that
`Aut(A₅)` induces exactly these permutations on `Irr(A₅)` via
`Out(A₅) ≅ ℤ/2` (the outer automorphism swapping `𝟑↔𝟑'` by exchanging the
5-cycle classes `5A,5B`).

## Verification status

Authored WITHOUT a local Lean+Mathlib toolchain and NOT compiled in that
environment. Check with `lake build`; minor tactic / lemma-name adjustments may
be needed for your exact Mathlib pin.

`dim_preserving_perms` quantifies over `Perm (Fin 5)` (120 elements) and is
discharged by `native_decide`, which introduces the `Lean.ofReduceBool`
reduction axiom. For strict `axiom = 0`, use instead the pointwise `decide`
facts `unique_dim_one/four/five` and `dim_three_pair` together with
`swap_preserves_dim`; everything else in this file is axiom-free.
-/

namespace A5Born.Rigidity

/-- Irreducible dimensions of `A₅`: `0 ↦ 𝟏, 1 ↦ 𝟑, 2 ↦ 𝟑', 3 ↦ 𝟒, 4 ↦ 𝟓`. -/
def n : Fin 5 → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 3
  | 3 => 4
  | 4 => 5

/-- The family swap `𝟑 ↔ 𝟑'` as a permutation of the five labels. -/
def swap33 : Equiv.Perm (Fin 5) := Equiv.swap 1 2

/-! ### Pointwise rigidity facts (axiom-free, `decide`) -/

theorem unique_dim_one  (ρ : Fin 5) : n ρ = 1 ↔ ρ = 0 := by fin_cases ρ <;> decide
theorem unique_dim_four (ρ : Fin 5) : n ρ = 4 ↔ ρ = 3 := by fin_cases ρ <;> decide
theorem unique_dim_five (ρ : Fin 5) : n ρ = 5 ↔ ρ = 4 := by fin_cases ρ <;> decide
theorem dim_three_pair  (ρ : Fin 5) : n ρ = 3 ↔ (ρ = 1 ∨ ρ = 2) := by
  fin_cases ρ <;> decide

/-- The swap preserves the dimension vector. -/
theorem swap_preserves_dim (ρ : Fin 5) : n (swap33 ρ) = n ρ := by
  fin_cases ρ <;> decide

/-! ### Complete permutation-level rigidity (`native_decide`; see status note) -/

/-- The only permutations of the five labels preserving `(1,3,3,4,5)` are the
identity and the `𝟑↔𝟑'` swap. -/
theorem dim_preserving_perms :
    ∀ σ : Equiv.Perm (Fin 5), (∀ ρ, n (σ ρ) = n ρ) → σ = 1 ∨ σ = swap33 := by
  native_decide

/-! ### Capacity-weight invariance -/

/-- Role-side capacity weight as a rational measure. -/
def mu : Fin 5 → ℚ := fun ρ => (n ρ : ℚ) ^ 2 / 60

/-- The swap preserves the capacity weight. -/
theorem mu_swap_invariant (ρ : Fin 5) : mu (swap33 ρ) = mu ρ := by
  simp only [mu, swap_preserves_dim ρ]

/-- Any dimension-preserving permutation preserves the capacity weight. -/
theorem mu_dim_preserving (σ : Equiv.Perm (Fin 5)) (h : ∀ ρ, n (σ ρ) = n ρ) :
    ∀ ρ, mu (σ ρ) = mu ρ := fun ρ => by simp only [mu, h ρ]

/-! ### Observation-law invariance (abstract core of the corollary) -/

/-- For the weighted-composition law `P a = ∑ ρ, mu ρ · K ρ a`, if the
channel-side permutation `σ` preserves `mu` and the kernel is covariant with
respect to `σ` and an observation-side permutation `t`
(`K (σ ρ) (t a) = K ρ a`), then `P (t a) = P a`. -/
theorem obs_law_invariant {A : Type*} [Fintype A]
    (σ : Equiv.Perm (Fin 5)) (t : Equiv.Perm A)
    (hμ : ∀ ρ, mu (σ ρ) = mu ρ)
    (K : Fin 5 → A → ℚ)
    (hcov : ∀ ρ a, K (σ ρ) (t a) = K ρ a) (a : A) :
    (∑ ρ, mu ρ * K ρ (t a)) = ∑ ρ, mu ρ * K ρ a := by
  calc (∑ ρ, mu ρ * K ρ (t a))
      = ∑ ρ, mu (σ ρ) * K (σ ρ) (t a) := (Equiv.sum_comp σ _).symm
    _ = ∑ ρ, mu ρ * K ρ a := by
          apply Finset.sum_congr rfl
          intro ρ _
          rw [hcov ρ a, hμ ρ]

/-- Specialisation to the only nontrivial channel action, the `𝟑↔𝟑'` swap. -/
theorem obs_law_invariant_swap {A : Type*} [Fintype A]
    (t : Equiv.Perm A) (K : Fin 5 → A → ℚ)
    (hcov : ∀ ρ a, K (swap33 ρ) (t a) = K ρ a) (a : A) :
    (∑ ρ, mu ρ * K ρ (t a)) = ∑ ρ, mu ρ * K ρ a :=
  obs_law_invariant swap33 t mu_swap_invariant K hcov a

-- Axiom audit (run after `lake build`):
-- #print axioms swap_preserves_dim       -- expect: no extra axioms
-- #print axioms mu_swap_invariant         -- expect: no extra axioms
-- #print axioms obs_law_invariant         -- expect: no extra axioms
-- #print axioms dim_preserving_perms      -- expect: Lean.ofReduceBool (native_decide)

end A5Born.Rigidity
