/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modularity.AKGradingTotal
import VOA.Modularity.EisensteinSerreClosure
import VOA.Modularity.AKSl2Instance

/-!
# The Arakawa–Kawasetsu MLDE theorem with no structural hypotheses

The library's AK theorem `IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite'` takes three
structural inputs. Each is a theorem for every VOA:
* Serre closure: `e46SerreClosed`, already discharged in that `'` statement;
* `AKWeightGrading W`: `akWeightGrading W` (`Modularity/AKGradingTotal.lean`);
* `VacuumGradeZero W`: `vacuumGradeZero_of_vacuum_grade W`, which is VOA4.

* `IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite_uncond`: for an Etingof-finite VOA,
  every `L[0]`-primary insertion `a` satisfies **one** monic modular linear differential equation, shared by
  all analytic blocks. The only hypothesis is `EtingofFinite W`.
* `exists_monicMLDEOn_all_analyticBlocks_simpleSl2QL`: the instance `L₋₄⁄₃(𝔰𝔩₂)` at the vacuum, with
  **no** hypotheses.
-/

namespace VOA

open VOA.QuasiLisseSl2

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The AK MLDE theorem, with Etingof finiteness as its only hypothesis.** -/
theorem IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite_uncond
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (hE : EtingofFinite W) :
    ∃ (s : ℕ) (p : ℕ → E46), 1 ≤ s ∧
      ∀ (F : 𝒱 → ℂ → ℂ), IsAnalyticBlock W F → MonicMLDEOn wt (F a) s p :=
  ha.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite' (akWeightGrading W)
    (VOA.QuasiLisseSl2.vacuumGradeZero_of_vacuum_grade W) hE

/-- **The AK MLDE theorem for `L₋₄⁄₃(𝔰𝔩₂)`**, unconditionally: one monic MLDE satisfied by the vacuum
insertion of every analytic block. -/
theorem exists_monicMLDEOn_all_analyticBlocks_simpleSl2QL :
    ∃ (s : ℕ) (p : ℕ → E46), 1 ≤ s ∧
      ∀ F, IsAnalyticBlock simpleSl2QL F →
        MonicMLDEOn 0 (F simpleSl2QL.vacuum) s p :=
  IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite_uncond
    (wt := 0) (by exact_mod_cast vacuum_isSqPrimary simpleSl2QL) VOA.Sl2Pres.etingofFinite_simpleSl2QL'

end VOA

section AxiomAudit
#print axioms VOA.IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite_uncond
#print axioms VOA.exists_monicMLDEOn_all_analyticBlocks_simpleSl2QL
end AxiomAudit
