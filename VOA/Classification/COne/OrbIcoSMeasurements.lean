import VOA.Classification.COne.OrbIcoSDecomposition
import VOA.Classification.COne.OrbOctaRCWard

/-! Measurement interfaces for the icosahedral symbol problem.
All functionals act on the actual fixed-point VOA. Concrete measurements remain required. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoS
open VOA VertexOperatorAlgebra OrbSpan OrbC2b OrbC2c OrbIco OrbXu
  VOA.LatGen VOA.LatGen.Triplet

/-- Pairing against an ambient lattice state, restricted to the icosahedral orbifold. -/
def chargedProbe (q : LatModuleGen (latP 1)) : (orbifold ico).carrier →ₗ[ℂ] ℂ :=
  ((v2mVirUnitary 1 le_rfl).form.flip q).comp (orbifold ico).carrier.subtype

theorem chargedProbe_L (q : LatModuleGen (latP 1)) (n : ℤ)
    (v : (orbifold ico).carrier) :
    chargedProbe q (Wi.L n v) =
      (v2mVirUnitary 1 le_rfl).form (v : LatModuleGen (latP 1))
        ((V2m 1 le_rfl).L (-n) q) :=
  (v2mVirUnitary 1 le_rfl).adjoint n v q

theorem chargedProbe_errors (q : LatModuleGen (latP 1))
    (h1 : (V2m 1 le_rfl).L 1 q = 0) (h3 : (V2m 1 le_rfl).L 3 q = 0) :
    virError Wi Wi.vacuum ⊔ virError Wi Xico ≤ (chargedProbe q).ker := by
  have kill1 (v : (orbifold ico).carrier) : chargedProbe q (Wi.L (-1) v) = 0 := by
    rw [chargedProbe_L, neg_neg, h1, map_zero]
  have kill3 (v : (orbifold ico).carrier) : chargedProbe q (Wi.L (-3) v) = 0 := by
    rw [chargedProbe_L, neg_neg, h3, map_zero]
  exact sup_le (OrbOctaR.virError_le_ker_of_two_modes Wi _ kill1 kill3 _)
    (OrbOctaR.virError_le_ker_of_two_modes Wi _ kill1 kill3 _)

def neutralProbe : (orbifold ico).carrier →ₗ[ℂ] ℂ :=
  OrbOctaR.neutralProbe.comp (orbifold ico).carrier.subtype

theorem neutralProbe_L (k : ℕ) (p : (orbifold ico).carrier) :
    neutralProbe (Wi.L (-(k : ℤ) - 1) p) =
      (if k = 1 then (1/2 : ℂ) else 0) * neutralProbe p :=
  OrbOctaR.neutralProbe_L k p

theorem neutralProbe_vacuum : neutralProbe Wi.vacuum = 1 :=
  OrbOctaR.octaProbe_vacuum

theorem neutralProbe_L_pow (n : ℕ) (p : (orbifold ico).carrier) :
    neutralProbe (((Wi.L (-2)) ^ n) p) = (1/2 : ℂ)^n * neutralProbe p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, show (-2 : ℤ) = -(1 : ℕ)-1 by norm_num,
      neutralProbe_L, if_pos rfl]
    rw [show (-(1 : ℕ)-1 : ℤ) = -2 by norm_num, ih, pow_succ']
    ring

theorem neutralProbe_errors :
    virError Wi Wi.vacuum ⊔ virError Wi Xico ≤ neutralProbe.ker := by
  have h1 (v : (orbifold ico).carrier) : neutralProbe (Wi.L (-1) v) = 0 := by
    simpa using neutralProbe_L 0 v
  have h3 (v : (orbifold ico).carrier) : neutralProbe (Wi.L (-3) v) = 0 := by
    simpa using neutralProbe_L 2 v
  exact sup_le (OrbOctaR.virError_le_ker_of_two_modes Wi _ h1 h3 _)
    (OrbOctaR.virError_le_ker_of_two_modes Wi _ h1 h3 _)

theorem Xico_ambient_primary :
    (Xico : LatModuleGen (latP 1)) ∈ prim (V2m 1 le_rfl) 36 := by
  change (TavI J6).val ∈ _
  rw [TavI_coe icoInv_J6]
  convert OrbPrim.T2_prim J6_hom using 1

/-- Ward evaluation at any shared descendant level; the residual mode is explicit. -/
theorem charged_mode_combo (q : LatModuleGen (latP 1)) (n : ℤ) (N : ℕ)
    (cs : List (ℚ × List ℕ))
    (hcs : ∀ t ∈ cs, t.2.sum = N ∧ ∀ k ∈ t.2, 0 < k) :
    chargedProbe (OrbOctaRC.virCombo (V2m 1 le_rfl) q cs) (Wi.smul Xico n Xico) =
      (OrbOctaRC.wardSum 36 n cs : ℂ) * chargedProbe q (Wi.smul Xico (n + N) Xico) :=
  OrbOctaRC.form_self_combo _ (v2mVirUnitary 1 le_rfl) Xico_ambient_primary q n N cs hcs

/-- Two independent measurements identify the two intrinsic coefficients. -/
theorem mode_remainder_of_measurements (r : ℕ) (hr : 18 ≤ r) (hmax : r < 50)
    (a b : ℂ) (f g : (orbifold ico).carrier →ₗ[ℂ] ℂ)
    (hf : virError Wi Wi.vacuum ⊔ virError Wi Xico ≤ f.ker)
    (hg : virError Wi Wi.vacuum ⊔ virError Wi Xico ≤ g.ker)
    (hdet : f (((Wi.L (-2)) ^ r) Wi.vacuum) * g (((Wi.L (-2)) ^ (r - 18)) Xico) -
      g (((Wi.L (-2)) ^ r) Wi.vacuum) * f (((Wi.L (-2)) ^ (r - 18)) Xico) ≠ 0)
    (hyf : f (Wi.smul Xico (71 - 2 * r) Xico) =
      a * f (((Wi.L (-2)) ^ r) Wi.vacuum) + b * f (((Wi.L (-2)) ^ (r - 18)) Xico))
    (hyg : g (Wi.smul Xico (71 - 2 * r) Xico) =
      a * g (((Wi.L (-2)) ^ r) Wi.vacuum) + b * g (((Wi.L (-2)) ^ (r - 18)) Xico)) :
    modeSymbol Wi Xico (71 - 2 * r) r (r - 18) a b ∈
      virError Wi Wi.vacuum ⊔ virError Wi Xico := by
  simpa only [modeSymbol, sub_sub] using
    OrbOctaR.remainder_of_measurements _ _ _ _ a b f g hf hg hdet
      (mode_remainder_exists r hr hmax) hyf hyg

end VOA.Classification.COne.OrbIcoS
