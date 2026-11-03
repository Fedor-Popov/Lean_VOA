import VOA.Classification.COne.OrbOctaRRanges
import VOA.Classification.COne.OrbSpanMain

/-! Charged probes from the lattice Hermitian form. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet OrbSpan OrbOcta OrbOctaR OrbC2b OrbC2c

/-- Pairing against a lattice state, restricted to the octahedral fixed space. -/
def chargedProbe (q : LatModuleGen (latP 1)) : (orbifold octa).carrier →ₗ[ℂ] ℂ :=
  ((v2mVirUnitary 1 le_rfl).form.flip q).comp (orbifold octa).carrier.subtype

theorem chargedProbe_L (q : LatModuleGen (latP 1)) (n : ℤ)
    (v : (orbifold octa).carrier) :
    chargedProbe q (W.L n v) =
      (v2mVirUnitary 1 le_rfl).form (v : LatModuleGen (latP 1))
        ((V2m 1 le_rfl).L (-n) q) :=
  (v2mVirUnitary 1 le_rfl).adjoint n v q

/-- The two positive-mode checks imply all the discarded-word checks. -/
theorem chargedProbe_errors (q : LatModuleGen (latP 1))
    (h1 : (V2m 1 le_rfl).L 1 q = 0) (h3 : (V2m 1 le_rfl).L 3 q = 0) :
    virError W W.vacuum ⊔ virError W X ≤ (chargedProbe q).ker := by
  have kill1 (v : (orbifold octa).carrier) : chargedProbe q (W.L (-1) v) = 0 := by
    rw [chargedProbe_L, neg_neg, h1, map_zero]
  have kill3 (v : (orbifold octa).carrier) : chargedProbe q (W.L (-3) v) = 0 := by
    rw [chargedProbe_L, neg_neg, h3, map_zero]
  exact sup_le (virError_le_ker_of_two_modes W _ kill1 kill3 _)
    (virError_le_ker_of_two_modes W _ kill1 kill3 _)

end VOA.Classification.COne.OrbOctaRC
