/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2Unconditional

/-! The unconditional A2 series headline, checked independently of other types. -/
namespace VOA.DeligneAudit.DeligneSeries
open VOA.DeligneHigherRankConditionalCapstone

/-- **`A₂`**: `L_{-3/2}(sl₃)`, unconditionally. -/
theorem A2_classicallyFree_final :
    CaseClassicallyFree .A2 VOA.DeligneAudit.A2.W VOA.DeligneAudit.A2.explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass VOA.DeligneAudit.A2.W 1 ⟨VOA.DeligneAudit.A2.explicitPresentation.gen i,
          VOA.DeligneAudit.A2.explicitPresentation.gen_weight_one i⟩).toRingHom =
        VOA.DeligneAudit.A2.I2ns :=
  VOA.DeligneAudit.A2.classicallyFree

/-- The older A₂ S2 interface, retained for reuse. -/
theorem A2_classicallyFree_final_S2 (hK : VOA.DeligneAudit.A2.RavinderKernelLower) :
    CaseClassicallyFree .A2 VOA.DeligneAudit.A2.W VOA.DeligneAudit.A2.explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass VOA.DeligneAudit.A2.W 1 ⟨VOA.DeligneAudit.A2.explicitPresentation.gen i,
          VOA.DeligneAudit.A2.explicitPresentation.gen_weight_one i⟩).toRingHom =
        VOA.DeligneAudit.A2.I2ns :=
  VOA.DeligneAudit.A2.classicallyFree_of_kernelLower' hK

end VOA.DeligneAudit.DeligneSeries

#print axioms VOA.DeligneAudit.DeligneSeries.A2_classicallyFree_final
#print axioms VOA.DeligneAudit.DeligneSeries.A2_classicallyFree_final_S2
