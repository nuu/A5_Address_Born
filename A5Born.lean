import A5Born.Auxiliary
import A5Born.SolvabilityBelow60
import A5Born.BornFromA5Opacity
import A5Born.BornFromA5Opacity_Bridge
import A5Born.ObservationLimits
import A5Born.BornFromDiscreteness
import A5Born.TranslationLayer
import A5Born.BornQuadratic
import A5Born.DoubleCover
import A5Born.BranchSign
import A5Born.ReadoutTriviality
import A5Born.FourStateCycle
import A5Born.SpectralCoupling
import A5Born.GateArithmetic
import A5Born.AddressPrinciple
import A5Born.WeightedComposition
import A5Born.G1SelCore

import A5Born.MultiplicityExclusion
import A5Born.ChannelActionRigidity



/-!
# A₅ Paper III — Weight Law and Readout Law from the Non-Solvability of A₅

Lean 4 formal verification for:
"Forced Probability and Phase Readout from a Common Algebraic Root:
 The Born Weight P(i)=n_i²/60 and the (ε,s) Structure of the Double Cover of A₅"

## Module structure (matching paper sections)

### Part A — Weight Law (§2–§4)
- `Auxiliary`                : Basic A₅ properties, Sylow toolkit (§2)
- `SolvabilityBelow60`      : All groups below order 60 are solvable (§2)
- `BornFromA5Opacity`       : Solvable-probe opacity, resolution zero (§3, Thm 3.1)
- `ObservationLimits`       : Resolution-zero theorem, observation limits (§3)
- `BornFromDiscreteness`    : Invariant weight is constant, counting measure forced (§3, Thm 3.2, Cor 3.3)
- `BornFromA5Opacity_Bridge`: Quadratic channel measure P(i)=n_i²/60, k=2 uniqueness (§4, Def 4.1, Thm 4.3)
- `BornQuadratic`           : Born quadraticity — continuous extension chain (§4 extended)

### Part B — Readout Law (§5–§6)
- `DoubleCover`             : SL(2,F₅) = 2I, spin-descent bit ε (§5, Def 5.1)
- `BranchSign`              : C₅⁺/C₅⁻ splitting, branch sign s, swap-odd (§5, Def 5.2)
- `ReadoutTriviality`       : ε = 0 readout triviality Φ(0,s) = 0 (§6, Prop 6.1)
- `FourStateCycle`          : McKay Ê₈ bipartiteness, 4-state cycle (§6, Prop 6.1, Thm 6.2)
- `SpectralCoupling`        : McKay spectral face-coupling (e₂ = 20, C = 20φ⁴)

### Composition and Spatial Embedding (§7–§8)
- `WeightedComposition`     : P_{Σ,P}(a) = Σ μ(i)K(a|i), signal profile (§7)
- `AddressPrinciple`        : Coarse address (ε,s) forcing, Lemma 8.1 (§8)
- `GateArithmetic`          : Gate truth tables as M-layer arithmetic (supplementary)
- `TranslationLayer`        : Three observation modes (supplementary)

### G1' Programme — Emergence Path (Appendix G)
- `G1SelCore`               : 2I ↪ E₈ embedding class selection, n₁ ≥ 8 ⟺ SU(3)-class (App. G)

### Reference-only files (present in the source tree, not built from this root)
- `BornQuadratic/InnerBridge`, `BornQuadratic/PythagorasHelpers`
                            : alternative `_v2` / `_refactored` versions of the
                              `sqNorm` geometry lemmas, superseded by the versions
                              in `Core` / `GeometryHelpers`. Kept for reference and
                              intentionally excluded from the default build to avoid
                              duplicate-name overlap.

Note: the section numbers above are indicative of the development's internal
sectioning; consult the current manuscript for the authoritative mapping.
-/
