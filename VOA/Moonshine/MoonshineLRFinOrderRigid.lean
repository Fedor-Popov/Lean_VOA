import VOA.Moonshine.MoonshineLRFinOrderIsing
import VOA.Moonshine.TopPairsCore
import VOA.Moonshine.AutFaithfulAssembly
import VOA.Moonshine.AutSigma
import VOA.Moonshine.MoonshineLRFinOrderPeriodic

/-!
# Ising rigidity and finite order of Moonshine automorphisms

Blueprint: the finite-order argument in `MOON_MONSTER`. Explicit spectral identities give rigidity
on the Griess algebra. Abstract periodicity, untwisted generation, and triality then prove
`autVnat_isOfFinOrder` without additional hypotheses.

The zero modes act on the ambient untwisted and twisted spaces; their annihilation
statements restrict them to weight two. The cocycle normalisation remains explicit.
The twisted charge coefficient is `2 * 2⁻⁴`, before multiplication by `s/4`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop
open VOA.Moonshine.TrialityTw VOA.LatGen VOA.IntegralLattice HeisenbergN
open VOA.Moonshine.SigmaExist VOA.Moonshine.Extraspecial
open scoped TensorProduct

/-- The untwisted block of the Ising zero mode. -/
noncomputable def isingPlusMode (α : leech.carrier) (s : ℂ) : Module.End ℂ VPlus :=
  mode (leechVOAPlus.Y (isingVec α s).1) 1

/-- The twisted block of the Ising zero mode. -/
noncomputable def isingTwistedMode (α : leech.carrier) (s : ℂ) : Module.End ℂ TP :=
  mode (plusModule.YM (isingVec α s).1) 1

/-- The polynomial `t(t-2)(t-1/2)(t-1/16)` evaluated on an endomorphism. -/
noncomputable def isingSpectralPolynomial {B : Type*} [AddCommGroup B] [Module ℂ B]
    (X : Module.End ℂ B) : Module.End ℂ B :=
  X * (X - (2 : ℂ) • 1) * (X - (1 / 2 : ℂ) • 1) * (X - (1 / 16 : ℂ) • 1)

private theorem isingSpectralPolynomial_apply {B : Type*} [AddCommGroup B] [Module ℂ B]
    (X : Module.End ℂ B) (y : B) :
    isingSpectralPolynomial X y = X (X (X (X y))) - (41 / 16 : ℂ) • X (X (X y)) +
      (37 / 32 : ℂ) • X (X y) - (1 / 16 : ℂ) • X y := by
  simp only [isingSpectralPolynomial, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
  module

private theorem isingSpectralPolynomial_of_cubic {B : Type*}
    [AddCommGroup B] [Module ℂ B] (X : Module.End ℂ B) (y : B)
    (h : X (X (X y)) = (5 / 2 : ℂ) • X (X y) - X y) :
    isingSpectralPolynomial X y = 0 := by
  have h4 := congrArg X h
  simp only [map_sub, map_smul] at h4
  rw [isingSpectralPolynomial_apply, h4, h]
  module

private theorem isingSpectralPolynomial_of_quadratic {B : Type*}
    [AddCommGroup B] [Module ℂ B] (X : Module.End ℂ B) (y : B) (c : ℂ)
    (hc : c = 2 ∨ c = 1 / 2 ∨ c = 1 / 16)
    (h : X (X y) = c • X y) : isingSpectralPolynomial X y = 0 := by
  rw [isingSpectralPolynomial_apply]
  simp only [h, map_smul]
  rcases hc with rfl | rfl | rfl <;> module

private theorem isingPlusMode_apply (α : leech.carrier) (s : ℂ) (y : VPlus) :
    isingPlusMode α s y = (1 / 16 : ℂ) • leechVOAPlus.smul (dV α α : VPlus) 1 y +
      (s / 4) • leechVOAPlus.smul (frameX0P α) 1 y := by
  change leechVOAPlus.smul _ 1 y = _
  simp only [isingVec, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_smul_left]

private theorem isingPlusMode_quad {α : leech.carrier} (hα : leech.form α α = 4)
    (s : ℂ) (u v : Fin (rank leech) → ℂ) :
    isingPlusMode α s (isingQuad u v) =
      ((∑ a, u a * chargeCoord leech α a) / 8) •
        isingQuad (chargeCoord leech α) v +
      ((∑ a, v a * chargeCoord leech α a) / 8) •
        isingQuad u (chargeCoord leech α) +
      (s * (∑ a, u a * chargeCoord leech α a) *
        (∑ a, v a * chargeCoord leech α a) / 4) • frameX0P α := by
  rw [isingPlusMode_apply, quadH_one_isingQuad, frameX0P_one_isingQuad hα]
  module

private theorem isingPlusMode_charge_self {α : leech.carrier}
    (hα : leech.form α α = 4) (s : ℂ) :
    isingPlusMode α s (frameX0P α) = frameX0P α +
      (s * latticeCocycle leech α (-α) / 4) •
        isingQuad (chargeCoord leech α) (chargeCoord leech α) := by
  rw [isingPlusMode_apply, quadH_one_frameX0P, frameX0P_one_frameX0P_self hα,
    isingQuad_chargeCoord, hα]
  norm_num
  module

private theorem isingPlusMode_quad_cubic {α : leech.carrier}
    (hα : leech.form α α = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1)
    (u v : Fin (rank leech) → ℂ) :
    isingPlusMode α s (isingPlusMode α s (isingPlusMode α s (isingQuad u v))) =
      (5 / 2 : ℂ) • isingPlusMode α s (isingPlusMode α s (isingQuad u v)) -
        isingPlusMode α s (isingQuad u v) := by
  simp only [isingPlusMode_quad hα, map_add, map_smul, isingPlusMode_charge_self hα,
    sum_chargeCoord leech leech_posDef, hα]
  match_scalars <;> ring_nf
  · linear_combination
      (∑ a, u a * chargeCoord leech α a) * (∑ a, v a * chargeCoord leech α a) * hs / 32
  · linear_combination
      (∑ a, u a * chargeCoord leech α a) * (∑ a, v a * chargeCoord leech α a) * s * hs / 4

private theorem isingSpectralPolynomial_of_eigen {B : Type*}
    [AddCommGroup B] [Module ℂ B] (X : Module.End ℂ B) (y : B) (c : ℂ)
    (hc : c = 0 ∨ c = 2 ∨ c = 1 / 2 ∨ c = 1 / 16)
    (h : X y = c • y) : isingSpectralPolynomial X y = 0 := by
  rw [isingSpectralPolynomial_apply]
  simp only [h, map_smul]
  rcases hc with rfl | rfl | rfl | rfl <;> module

private theorem isingRigid_frameX0P_neg (β : leech.carrier) :
    frameX0P (-β) = frameX0P β := by
  apply Subtype.ext
  change latChargeGen leech (-β) + latChargeGen leech (- -β) = _
  rw [neg_neg, add_comm]
  rfl

private theorem isingPlusMode_charge_self_quadratic {α : leech.carrier}
    (hα : leech.form α α = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1) :
    isingPlusMode α s (isingPlusMode α s (frameX0P α)) =
      (2 : ℂ) • isingPlusMode α s (frameX0P α) := by
  simp only [isingPlusMode_charge_self hα, map_add, map_smul, isingPlusMode_quad hα,
    sum_chargeCoord leech leech_posDef, hα]
  match_scalars <;> ring_nf
  linear_combination hs

private theorem isingPlusMode_charge_two_quadratic {α β : leech.carrier}
    (hα : leech.form α α = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1) (hab : leech.form α β = 2) :
    isingPlusMode α s (isingPlusMode α s (frameX0P β)) =
      (1 / 2 : ℂ) • isingPlusMode α s (frameX0P β) := by
  have hab' : leech.form α (β - α) = -2 := by rw [map_sub, hab, hα]; norm_num
  have hstep : isingPlusMode α s (frameX0P β) =
      (1 / 4 : ℂ) • frameX0P β +
        (s * latticeCocycle leech α (-β) / 4) • frameX0P (β - α) := by
    rw [isingPlusMode_apply, quadH_one_frameX0P,
      frameX0P_one_frameX0P_of_form_two hab, hab]
    norm_num
    module
  have hstep' : isingPlusMode α s (frameX0P (β - α)) =
      (1 / 4 : ℂ) • frameX0P (β - α) +
        (s * latticeCocycle leech α (β - α) / 4) • frameX0P β := by
    rw [isingPlusMode_apply, quadH_one_frameX0P,
      frameX0P_one_frameX0P_of_form_neg_two hab', hab',
      show α + (β - α) = β by abel]
    norm_num
    module
  have hc : latticeCocycle leech α (-β) * latticeCocycle leech α (β - α) =
      latticeCocycle leech α (-α) := by
    rw [← latticeCocycle_add_right, show -β + (β - α) = -α by abel]
  have hsc : s ^ 2 * (latticeCocycle leech α (-β) *
      latticeCocycle leech α (β - α)) = 1 := by rw [hc]; exact hs
  rw [hstep, map_add, map_smul, map_smul, hstep, hstep']
  match_scalars <;> ring_nf
  linear_combination hsc / 16

private theorem isingPlusMode_charge_annihilated {α β : leech.carrier}
    (hα : leech.form α α = 4) (hβ : leech.form β β = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1) :
    isingSpectralPolynomial (isingPlusMode α s) (frameX0P β) = 0 := by
  have hsmall (hlo : -1 ≤ leech.form α β) (hhi : leech.form α β ≤ 1)
      (hc : ((leech.form α β : ℂ) * (leech.form α β : ℂ) / 16) = 0 ∨
        ((leech.form α β : ℂ) * (leech.form α β : ℂ) / 16) = 1 / 16) :
      isingSpectralPolynomial (isingPlusMode α s) (frameX0P β) = 0 := by
    apply isingSpectralPolynomial_of_eigen _ _ _
      (hc.imp_right fun h => Or.inr (Or.inr h))
    rw [isingPlusMode_apply, quadH_one_frameX0P,
      frameX0P_one_frameX0P_of_form_small hlo hhi]
    module
  rcases leech_form_cases_of_normFour hα hβ with h | h | h | h | h | h | h
  · have hb := (leech_form_neg_four_iff_of_normFour hα hβ).mp h
    rw [hb, isingRigid_frameX0P_neg]
    exact isingSpectralPolynomial_of_quadratic _ _ 2 (Or.inl rfl)
      (isingPlusMode_charge_self_quadratic hα s hs)
  · have hp := isingPlusMode_charge_two_quadratic hα s hs
      (β := -β) (by rw [map_neg, h]; norm_num)
    rw [isingRigid_frameX0P_neg] at hp
    exact isingSpectralPolynomial_of_quadratic _ _ (1 / 2) (Or.inr (Or.inl rfl)) hp
  · exact hsmall (by omega) (by omega) (by rw [h]; norm_num)
  · exact hsmall (by omega) (by omega) (by rw [h]; norm_num)
  · exact hsmall (by omega) (by omega) (by rw [h]; norm_num)
  · exact isingSpectralPolynomial_of_quadratic _ _ (1 / 2) (Or.inr (Or.inl rfl))
      (isingPlusMode_charge_two_quadratic hα s hs h)
  · rw [(leech_form_four_iff_of_normFour hα hβ).mp h]
    exact isingSpectralPolynomial_of_quadratic _ _ 2 (Or.inl rfl)
      (isingPlusMode_charge_self_quadratic hα s hs)

/-- `t(t-2)(t-1/2)(t-1/16)` annihilates the untwisted weight-two block. -/
theorem isingVec_zeroMode_plus_annihilated {α : leech.carrier}
    (hα : leech.form α α = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1)
    (y : VPlus) (hy : y ∈ leechVOAPlus.grading 2) :
    isingSpectralPolynomial (isingPlusMode α s) y = 0 := by
  have hle : leechVOAPlus.grading 2 ≤
      LinearMap.ker (isingSpectralPolynomial (isingPlusMode α s)) := by
    rw [leechVOAPlus_grading_two_eq_span, Submodule.span_le]
    rintro x (⟨⟨a, b⟩, rfl⟩ | ⟨β, hβ, rfl⟩)
    · have hq : isingQuad (Pi.single a 1) (Pi.single b 1) = qP a b := by
        classical
        simp [isingQuad, isingQuadRow, Pi.single_apply]
      change isingSpectralPolynomial (isingPlusMode α s) (qP a b) = 0
      rw [← hq]
      exact isingSpectralPolynomial_of_cubic _ _
        (isingPlusMode_quad_cubic hα s hs _ _)
    · exact isingPlusMode_charge_annihilated hα hβ s hs
  exact hle hy

/-- The cocycle-normalised charge operator on the finite twisted ground space. -/
noncomputable def isingChargeInvolution (α : leech.carrier) (s : ℂ) :
    Module.End ℂ TLeechT := s • eT leech leech_even leech_isUnit_det_gramMat α

/-- The condition on `s` makes the charge operator an involution. -/
theorem isingChargeInvolution_apply_twice (α : leech.carrier) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1) (t : TLeechT) :
    isingChargeInvolution α s (isingChargeInvolution α s t) = t := by
  simp only [isingChargeInvolution, LinearMap.smul_apply, map_smul,
    ← Module.End.mul_apply, eT_mul_self', Module.End.one_apply]
  simp only [smul_smul]
  have hc : s * (s * latticeCocycle leech α α) = 1 := by
    rw [latticeCocycle_neg_right] at hs
    linear_combination hs
  rw [hc, one_smul]

/-- The twisted zero-mode action formula. The two `2⁻⁴` charge terms give `s/32` after Ising
scaling. -/
theorem isingTwistedMode_hP {α : leech.carrier} (hα : leech.form α α = 4)
    (s : ℂ) (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    isingTwistedMode α s (hP v t) = (1 / 32 : ℂ) •
      (hP (v + (2 * ∑ a, chargeCoord leech α a * v a) • chargeCoord leech α) t +
        hP (v - (2 * ∑ a, chargeCoord leech α a * v a) • chargeCoord leech α)
          (isingChargeInvolution α s t)) := by
  have hq : mode (plusModule.YM (dV α α : VPlus)) 1 (hP v t) =
      hP (dL α α v) t := actT_dV_hP α α v t
  simp only [isingTwistedMode, isingVec, map_add, map_smul, mode_add, mode_smul,
    LinearMap.add_apply, LinearMap.smul_apply, hq, TopPairs.oX_hP hα]
  simp only [dL, latL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.smulRight_apply, LinearMap.sum_apply,
    LinearMap.proj_apply, smul_eq_mul, hα]
  simp only [hP_add_left, hP_sub_left, hP_smul_left, isingChargeInvolution,
    LinearMap.smul_apply, hP_smul_right]
  norm_num
  module

private theorem isingTwistedMode_hP_expanded {α : leech.carrier}
    (hα : leech.form α α = 4) (s : ℂ) (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    isingTwistedMode α s (hP v t) =
      (1 / 32 : ℂ) • hP v t +
      ((∑ a, chargeCoord leech α a * v a) / 16) • hP (chargeCoord leech α) t +
      (1 / 32 : ℂ) • hP v (isingChargeInvolution α s t) -
      ((∑ a, chargeCoord leech α a * v a) / 16) •
        hP (chargeCoord leech α) (isingChargeInvolution α s t) := by
  rw [isingTwistedMode_hP hα]
  simp only [hP_add_left, hP_sub_left, hP_smul_left]
  module

private theorem isingTwistedMode_hP_cubic {α : leech.carrier}
    (hα : leech.form α α = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1)
    (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    isingTwistedMode α s (isingTwistedMode α s (isingTwistedMode α s (hP v t))) =
      (9 / 16 : ℂ) • isingTwistedMode α s (isingTwistedMode α s (hP v t)) -
        (1 / 32 : ℂ) • isingTwistedMode α s (hP v t) := by
  simp only [isingTwistedMode_hP_expanded hα, map_add, map_sub, map_smul,
    isingChargeInvolution_apply_twice α s hs, sum_chargeCoord leech leech_posDef, hα]
  module

/-- The smaller polynomial `t(t-1/16)(t-1/2)` kills the twisted weight-two block. -/
theorem isingVec_zeroMode_twisted_annihilated {α : leech.carrier}
    (hα : leech.form α α = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1)
    (y : TP) (hy : y ∈ plusModule.weight (2 : ℂ)) :
    (isingTwistedMode α s * (isingTwistedMode α s - (1 / 16 : ℂ) • 1) *
      (isingTwistedMode α s - (1 / 2 : ℂ) • 1)) y = 0 := by
  have hle : plusModule.weight (2 : ℂ) ≤
      LinearMap.ker (isingTwistedMode α s *
        (isingTwistedMode α s - (1 / 16 : ℂ) • 1) *
        (isingTwistedMode α s - (1 / 2 : ℂ) • 1)) := by
    rw [twistedPlus_grading_two_eq_span, Submodule.span_le]
    rintro _ ⟨v, t, rfl⟩
    change (isingTwistedMode α s * (isingTwistedMode α s - (1 / 16 : ℂ) • 1) *
      (isingTwistedMode α s - (1 / 2 : ℂ) • 1)) (hP v t) = 0
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul]
    rw [isingTwistedMode_hP_cubic hα s hs]
    module
  exact hle hy

/-- Ising rigidity on the weight-two Griess algebra, as used by abstract periodicity. -/
theorem isingVec_rigid {α : leech.carrier} (hα : leech.form α α = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1) :
    ∀ y : VnatVOA.grading 2,
      VnatVOA.griessMul ⟨isingVec α s, isingVec_mem_grading_two hα s⟩ y = y → y = 0 := by
  intro y hy
  have heq := congrArg (fun z : VnatVOA.grading 2 => (z : Vnat)) hy
  simp only [VertexOperatorAlgebra.griessMul_coe] at heq
  change VnatVOA.smul ((isingVec α s).1, 0) 1 (y : Vnat) = (y : Vnat) at heq
  rw [VnatVOA_smul_inl] at heq
  have hp : isingPlusMode α s (y : Vnat).1 = (y : Vnat).1 := congrArg Prod.fst heq
  have ht : isingTwistedMode α s (y : Vnat).2 = (y : Vnat).2 := congrArg Prod.snd heq
  have hyg := y.property
  simp only [VnatVOA_grading, mem_gradingNat] at hyg
  have hpa := isingVec_zeroMode_plus_annihilated hα s hs (y : Vnat).1 hyg.1
  rw [isingSpectralPolynomial_apply] at hpa
  simp only [hp] at hpa
  have hta := isingVec_zeroMode_twisted_annihilated hα s hs (y : Vnat).2 hyg.2
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul, ht] at hta
  have hp0 : (y : Vnat).1 = 0 := by
    have hz : (-15 / 32 : ℂ) • (y : Vnat).1 = 0 := by
      linear_combination (norm := module) hpa
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have ht0 : (y : Vnat).2 = 0 := by
    have hz : (15 / 32 : ℂ) • (y : Vnat).2 = 0 := by
      linear_combination (norm := module) hta
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  apply Subtype.ext
  exact Prod.ext hp0 ht0

private theorem isingRigid_Bq_charge (α β : leech.carrier) :
    Bq (chargeCoord leech α) (chargeCoord leech β) = dV α β := by
  rw [Bq_apply, dV_eq_sum]

private theorem isingRigid_Bq_symm (u v : Fin (rank leech) → ℂ) : Bq u v = Bq v u := by
  have h (w z : Fin (rank leech) → ℂ) : (Bq w z : VPlus) = isingQuad w z := by
    simp only [Bq_apply, Submodule.coe_sum, Submodule.coe_smul, isingQuad, isingQuadRow,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [mul_comm]
      rfl
  apply Subtype.ext
  rw [h, h, isingQuad_symm]

private theorem isingRigid_dV_offdiag (j k : Fin 24) :
    dV (fw j) (fw k) = dV (gP j k) (gP j k) - dV (gM j k) (gM j k) := by
  rw [← isingRigid_Bq_charge (gP j k), ← isingRigid_Bq_charge (gM j k),
    chargeCoord_gP, chargeCoord_gM]
  simp only [map_smul, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply]
  rw [isingRigid_Bq_symm (cw k) (cw j)]
  simp only [Bq_cw]
  module

private theorem isingRigid_dV_diagonal_pair (j k : Fin 24) :
    dV (fw j) (fw j) + dV (fw k) (fw k) =
      (2 : ℂ) • (dV (gP j k) (gP j k) + dV (gM j k) (gM j k)) := by
  rw [← isingRigid_Bq_charge (gP j k), ← isingRigid_Bq_charge (gM j k),
    chargeCoord_gP, chargeCoord_gM]
  simp only [map_smul, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Bq_cw]
  module

private theorem isingRigid_qV_mem (S : Submodule ℂ V0Sub.carrier)
    (hS : ∀ α : leech.carrier, leech.form α α = 4 → dV α α ∈ S)
    (a b : Fin (rank leech)) : qV a b ∈ S := by
  have hpair (j k : Fin 24) (hjk : j ≠ k) :
      dV (fw j) (fw j) + dV (fw k) (fw k) ∈ S := by
    rw [isingRigid_dV_diagonal_pair]
    exact S.smul_mem _ (S.add_mem (hS _ (form_gP_self hjk)) (hS _ (form_gM_self hjk)))
  have hdiag (j : Fin 24) : dV (fw j) (fw j) ∈ S := by
    obtain ⟨k, hk⟩ := exists_ne j
    obtain ⟨l, hlj, hlk⟩ := Fin.exists_ne_and_ne_of_two_lt j k (by norm_num)
    have hid : dV (fw j) (fw j) = (1 / 2 : ℂ) •
        ((dV (fw j) (fw j) + dV (fw k) (fw k)) +
          (dV (fw j) (fw j) + dV (fw l) (fw l)) -
          (dV (fw k) (fw k) + dV (fw l) (fw l))) := by module
    rw [hid]
    exact S.smul_mem _ (S.sub_mem (S.add_mem (hpair j k hk.symm)
      (hpair j l hlj.symm)) (hpair k l hlk.symm))
  rw [qV_eq_sum_dV]
  refine S.sum_mem fun j _ => S.sum_mem fun k _ => S.smul_mem _ ?_
  by_cases hjk : j = k
  · subst k
    exact hdiag j
  · rw [isingRigid_dV_offdiag]
    exact S.sub_mem (hS _ (form_gP_self hjk)) (hS _ (form_gM_self hjk))

/-- Fixing a normalised pair of Ising vectors for every minimal charge fixes
all quadratic letters and all minimal charged letters. -/
theorem aut_fix_quad_minimal_of_fix_ising (g : AutVnat)
    (hg : ∀ α : leech.carrier, leech.form α α = 4 →
      ∃ s : ℂ, s ^ 2 * latticeCocycle leech α (-α) = 1 ∧
        g (isingVec α s) = isingVec α s ∧ g (isingVec α (-s)) = isingVec α (-s)) :
    (∀ a b : Fin (rank leech), g ((qP a b, 0) : Vnat) = ((qP a b, 0) : Vnat)) ∧
      (∀ α : leech.carrier, leech.form α α = 4 →
        g ((frameX0P α, 0) : Vnat) = ((frameX0P α, 0) : Vnat)) := by
  have hletters (α : leech.carrier) (hα : leech.form α α = 4) :
      g (((dV α α : VPlus), 0) : Vnat) = (((dV α α : VPlus), 0) : Vnat) ∧
        g ((frameX0P α, 0) : Vnat) = ((frameX0P α, 0) : Vnat) := by
    obtain ⟨s, hs, hp, hm⟩ := hg α hα
    have hs0 : s ≠ 0 := by intro h; simp [h] at hs
    have hq : (((dV α α : VPlus), 0) : Vnat) =
        (8 : ℂ) • (isingVec α s + isingVec α (-s)) := by
      apply Prod.ext <;> simp only [isingVec, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_add, Prod.snd_add] <;> module
    have hx : ((frameX0P α, 0) : Vnat) =
        (2 / s) • (isingVec α s - isingVec α (-s)) := by
      apply Prod.ext <;> simp only [isingVec, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub]
      · match_scalars <;> field_simp <;> ring
      · module
    constructor
    · rw [hq, Aut.map_smul_c, map_add, hp, hm]
    · rw [hx, Aut.map_smul_c, map_sub, hp, hm]
  refine ⟨?_, fun α hα => (hletters α hα).2⟩
  intro a b
  let S : Submodule ℂ V0Sub.carrier := (GriessAut.fixedSpace g).comap
    ((LinearMap.inl ℂ VPlus TP).comp V0Sub.carrier.subtype)
  have hS : ∀ v : V0Sub.carrier, v ∈ S ↔
      g (((v : VPlus), 0) : Vnat) = (((v : VPlus), 0) : Vnat) := by
    intro v
    exact GriessAut.mem_fixedSpace
  exact (hS (qV a b)).mp (isingRigid_qV_mem S
    (fun α hα => (hS _).mpr (hletters α hα).1) a b)

private theorem isingRigid_frame_eigen (g : AutVnat) (hg : ∀ a b : Fin (rank leech),
      g ((qP a b, 0) : Vnat) = ((qP a b, 0) : Vnat))
    (β : leech.carrier) :
    ∃ c : ℂ, g ((frameX0P β, 0) : Vnat) = c • ((frameX0P β, 0) : Vnat) := by
  set w := g ((frameX0P β, 0) : Vnat) with hw
  have heq : ∀ a b, VnatVOA.smul ((qP a b, 0) : Vnat) 1 w
      = (chargeCoord leech β a * chargeCoord leech β b) • w := by
    intro a b
    rw [hw, ← hg a b, ← Aut.map_smul, VnatVOA_smul_qN_frameX0P,
      Aut.coe_toLinearEquiv, ← Aut.coe_toLinearEquiv, map_smul]
  have hsplit : ∀ a b, VnatVOA.smul ((qP a b, 0) : Vnat) 1 w
      = (leechVOAPlus.smul (qP a b) 1 w.1, mode (plusModule.YM (qP a b)) 1 w.2) := by
    intro a b
    conv_lhs => rw [show w = (w.1, w.2) from rfl]
    exact VnatVOA_smul_inl _ _ _ _
  have hw1 : ∀ a b, leechVOAPlus.smul (qP a b) 1 w.1
      = (chargeCoord leech β a * chargeCoord leech β b) • w.1 := fun a b => by
    have := congrArg Prod.fst ((hsplit a b).symm.trans (heq a b))
    simpa using this
  have hw2 : w.2 = 0 := by
    refine AutZeroTw.VnatVOA_twisted_outer_eigen_eq_zero (fun a => chargeCoord leech β a) w.2
      fun a b u hu => ?_
    have hu' : u = qP a b := Subtype.ext (hu.trans (qP_coe a b).symm)
    subst hu'
    rw [VnatVOA_smul_inl, PreVertexAlgebra.smul_zero_right]
    have := congrArg Prod.snd ((hsplit a b).symm.trans (heq a b))
    simp only [Prod.smul_snd] at this
    rw [this, Prod.smul_mk, smul_zero]
  obtain ⟨c, hc⟩ := eigen_plus β w.1 hw1
  refine ⟨c, ?_⟩
  change (w.1, w.2) = _
  rw [hc, hw2, Prod.smul_mk, smul_zero]

private theorem isingRigid_scalar_step_of_neg (g : AutVnat)
    (hg : ∀ α : leech.carrier, leech.form α α = 4 →
      g ((frameX0P α, 0) : Vnat) = ((frameX0P α, 0) : Vnat))
    {α γ : leech.carrier} (hα : leech.form α α = 4) (h : leech.form α γ < 0) {c c' : ℂ}
    (hc : g ((frameX0P γ, 0) : Vnat) = c • ((frameX0P γ, 0) : Vnat))
    (hc' : g ((frameX0P (α + γ), 0) : Vnat) = c' • ((frameX0P (α + γ), 0) : Vnat)) : c = c' := by
  have hε : latticeCocycle leech α γ ≠ 0 := latticeCocycle_ne_zero leech α γ
  have key := congrArg (fun v => g v) (VnatVOA_smul_xN_of_neg α γ h)
  simp only at key
  rw [Aut.map_smul, hg α hα, hc, PreVertexAlgebra.smul_smul_right,
    VnatVOA_smul_xN_of_neg α γ h, map_smul, hc', smul_comm c] at key
  have key2 := smul_right_injective Vnat hε key
  exact scalar_unique key2

/-- ⭐ **The scalars agree along every minimal vector**: `c_γ = c_{γ+α}` for `α` minimal. -/
private theorem isingRigid_scalar_step (g : AutVnat) (hg : ∀ α : leech.carrier, leech.form α α = 4 →
      g ((frameX0P α, 0) : Vnat) = ((frameX0P α, 0) : Vnat))
    {α γ : leech.carrier} (hα : leech.form α α = 4) {c c' : ℂ}
    (hc : g ((frameX0P γ, 0) : Vnat) = c • ((frameX0P γ, 0) : Vnat))
    (hc' : g ((frameX0P (α + γ), 0) : Vnat) = c' • ((frameX0P (α + γ), 0) : Vnat)) : c = c' := by
  by_cases h : leech.form α γ < 0
  · exact isingRigid_scalar_step_of_neg g hg hα h hc hc'
  · -- use `−α` against `γ + α`
    have hα' : leech.form (-α) (-α) = 4 := by
      rw [LinearMap.map_neg₂, map_neg, neg_neg, hα]
    have h' : leech.form (-α) (α + γ) < 0 := by
      have e : leech.form (-α) (α + γ) = -(leech.form α α + leech.form α γ) := by
        rw [LinearMap.map_neg₂, map_add]
      rw [e, hα]
      omega
    have hsum : -α + (α + γ) = γ := by abel
    have hc2 : g ((frameX0P (-α + (α + γ)), 0) : Vnat) =
        c • ((frameX0P (-α + (α + γ)), 0) : Vnat) := by
      rw [hsum]; exact hc
    exact (isingRigid_scalar_step_of_neg g hg hα' h' hc' hc2).symm

/-- Fixing the quadratic letters and minimal charges fixes the untwisted VOA. -/
theorem aut_fix_untwisted_of_fix_quad_minimal (g : AutVnat)
    (hq : ∀ a b : Fin (rank leech), g ((qP a b, 0) : Vnat) = ((qP a b, 0) : Vnat))
    (hx : ∀ α : leech.carrier, leech.form α α = 4 →
      g ((frameX0P α, 0) : Vnat) = ((frameX0P α, 0) : Vnat)) :
    ∀ x : VPlus, g ((x, 0) : Vnat) = ((x, 0) : Vnat) := by
  have hX : ∀ β : leech.carrier,
      g ((frameX0P β, 0) : Vnat) = ((frameX0P β, 0) : Vnat) := by
    intro β
    refine LeechSpan.leech_induction
      (fun β => g ((frameX0P β, 0) : Vnat) = ((frameX0P β, 0) : Vnat)) ?_ ?_ ?_ β
    · -- `β = 0`: `(x_0, 0) = 2·𝟙♮`
      have hvac : ((frameX0P (0 : leech.carrier), 0) : Vnat) = (2 : ℂ) • VnatVOA.vacuum := by
        rw [VnatVOA_vacuum, frameX0P_zero]
        change _ = (2 : ℂ) • ((leechVOAPlus.vacuum, 0) : Vnat)
        rw [Prod.smul_mk, smul_zero]
      change g.toLinearEquiv _ = _
      rw [hvac, map_smul]
      change (2 : ℂ) • g VnatVOA.vacuum = _
      rw [g.map_vacuum]
    · intro γ α hα hP
      obtain ⟨c, hc⟩ := isingRigid_frame_eigen g hq (γ + α)
      have hc' : g ((frameX0P (α + γ), 0) : Vnat) = c • ((frameX0P (α + γ), 0) : Vnat) := by
        rw [add_comm]; exact hc
      have h1 : g ((frameX0P γ, 0) : Vnat) = (1 : ℂ) • ((frameX0P γ, 0) : Vnat) := by
        rw [one_smul]; exact hP
      have := isingRigid_scalar_step g hx hα h1 hc'
      change g ((frameX0P (γ + α), 0) : Vnat) = _
      rw [hc, ← this, one_smul]
    · intro γ α hα hP
      have hα' : leech.form (-α) (-α) = 4 := by
        rw [LinearMap.map_neg₂, map_neg, neg_neg, hα]
      obtain ⟨c, hc⟩ := isingRigid_frame_eigen g hq (γ - α)
      have hc' : g ((frameX0P (-α + γ), 0) : Vnat) = c • ((frameX0P (-α + γ), 0) : Vnat) := by
        rw [show -α + γ = γ - α by abel]; exact hc
      have h1 : g ((frameX0P γ, 0) : Vnat) = (1 : ℂ) • ((frameX0P γ, 0) : Vnat) := by
        rw [one_smul]; exact hP
      have := isingRigid_scalar_step g hx hα' h1 hc'
      change g ((frameX0P (γ - α), 0) : Vnat) = _
      rw [hc, ← this, one_smul]
  set S : Submodule ℂ VPlus := (GriessAut.fixedSpace g).comap (LinearMap.inl ℂ SkewVP TP) with hS
  have hmemS : ∀ x : VPlus, x ∈ S ↔ g ((x, 0) : Vnat) = ((x, 0) : Vnat) := fun x => by
    rw [hS, Submodule.mem_comap, LinearMap.inl_apply, GriessAut.mem_fixedSpace]
  have hStop : S = ⊤ := by
    refine leechPlus_generated S ?_ ?_ (fun β => (hmemS _).2 (hX β))
    · rw [hmemS]
      have := g.map_vacuum
      rw [VnatVOA_vacuum] at this
      exact this
    · intro u hu x hx' n
      rw [hmemS] at hu hx' ⊢
      have h1 : VnatVOA.smul ((u, 0) : Vnat) n ((x, 0) : Vnat) =
          ((leechVOAPlus.smul u n x, 0) : Vnat) := by
        rw [VnatVOA_smul_inl, map_zero]
      rw [← h1, Aut.map_smul, hu, hx']
  have hU : ∀ x : VPlus, g ((x, 0) : Vnat) = ((x, 0) : Vnat) := fun x =>
    (hmemS x).1 (hStop ▸ Submodule.mem_top)
  exact hU

/-- The untwisted VOA and its cyclic twisted generator determine an automorphism. -/
theorem aut_eq_one_of_fix_untwisted_twistedGen (g : AutVnat)
    (hU : ∀ x : VPlus, g ((x, 0) : Vnat) = ((x, 0) : Vnat))
    (hx : g ((0, xGen) : Vnat) = ((0, xGen) : Vnat)) : g = 1 := by
  let R : Submodule ℂ TP := (GriessAut.fixedSpace g).comap (LinearMap.inr ℂ VPlus TP)
  have hmem (t : TP) : t ∈ R ↔ g ((0, t) : Vnat) = ((0, t) : Vnat) :=
    GriessAut.mem_fixedSpace
  have htop : R = ⊤ := by
    apply top_unique
    rw [← M8hKey.modeSpan_x0T (SigmaAssemble.tF_ne Dnat.s), Submodule.span_le]
    rintro _ ⟨u, n, i, rfl⟩
    rw [SetLike.mem_coe, hmem]
    have hmode : VnatVOA.smul ((u, 0) : Vnat) n ((0, xGen) : Vnat) =
        ((0, mode (plusModule.YM u) n xGen) : Vnat) := by
      rw [VnatVOA_smul_inl, PreVertexAlgebra.smul_zero_right]
    change g ((0, mode (plusModule.YM u) n xGen) : Vnat) = _
    rw [← hmode, Aut.map_smul, hU, hx]
  have hT (t : TP) : g ((0, t) : Vnat) = ((0, t) : Vnat) :=
    (hmem t).mp (htop ▸ Submodule.mem_top)
  refine Aut.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, t⟩ := v
  have hsplit : ((x, t) : Vnat) = ((x, 0) : Vnat) + ((0, t) : Vnat) := by simp
  change g (x, t) = (x, t)
  rw [hsplit, map_add, hU, hT]

private noncomputable def isingRigid_griessMul :
    VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2 :=
  LinearMap.mk₂ ℂ VnatVOA.griessMul VnatVOA.griessMul_add_left
    (fun c x y => Subtype.ext (VnatVOA.smul_smul_left c x 1 y))
    VnatVOA.griessMul_add_right
    (fun c x y => Subtype.ext (VnatVOA.smul_smul_right x c 1 y))

private theorem isingRigid_restrict_pow (g : AutVnat) (n : ℕ) (y : VnatVOA.grading 2) :
    (((GriessAut.autRestrict g 2 ^ n) y : VnatVOA.grading 2) : Vnat) =
      (g ^ n) (y : Vnat) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', LinearEquiv.mul_apply, GriessAut.autRestrict_coe, Aut.mul_apply, ih]

/-- Every explicit normalised Ising vector is periodic under every Moonshine automorphism. -/
theorem aut_isingVec_periodic (g : AutVnat) {α : leech.carrier}
    (hα : leech.form α α = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1) :
    ∃ K : ℕ, 1 ≤ K ∧ (g ^ K) (isingVec α s) = isingVec α s := by
  letI : FiniteDimensional ℂ (VnatVOA.grading 2) := by
    change FiniteDimensional ℂ (gradingNat 2)
    infer_instance
  let e : VnatVOA.grading 2 := ⟨isingVec α s, isingVec_mem_grading_two hα s⟩
  have he : isingRigid_griessMul e e = (2 : ℂ) • e :=
    Subtype.ext (isingVec_one_self hα s hs)
  obtain ⟨K, hK, hfix⟩ := pow_apply_eq_self_of_rigid isingRigid_griessMul
    vnat_griessMul_comm (GriessAut.autRestrict g 2) (GriessAut.griessMul_aut g)
    e he (isingVec_rigid hα s hs)
  refine ⟨K, hK, ?_⟩
  have h := congrArg (fun z : VnatVOA.grading 2 => (z : Vnat)) hfix
  dsimp only at h
  rwa [isingRigid_restrict_pow] at h

private theorem isingRigid_pow_fix (g : AutVnat) (x : Vnat) (hx : g x = x) (n : ℕ) :
    (g ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Aut.mul_apply, ih, hx]

private theorem isingRigid_pow_fix_of_dvd (g : AutVnat) (x : Vnat) {n N : ℕ}
    (hn : (g ^ n) x = x) (hdiv : n ∣ N) : (g ^ N) x = x := by
  obtain ⟨d, rfl⟩ := hdiv
  rw [pow_mul]
  exact isingRigid_pow_fix (g ^ n) x hn d

/-- A positive power of every automorphism fixes the whole untwisted block. -/
theorem aut_pow_fix_untwisted (g : AutVnat) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ x : VPlus, (g ^ K) ((x, 0) : Vnat) = ((x, 0) : Vnat) := by
  classical
  let I := {α : leech.carrier // leech.form α α = 4}
  letI : Fintype I := (normFour_finite leech leech_posDef).fintype
  let c (α : I) : ℂ := FrameT.sqrtEps leech α
  have hc (α : I) : c α ^ 2 * latticeCocycle leech α (-α) = 1 := by
    dsimp only [c]
    rw [pow_two, FrameT.sqrtEps_mul_self, latticeCocycle_neg_right, latticeCocycle_sq]
  have hper (α : I) : ∃ n : ℕ, 1 ≤ n ∧
      (g ^ n) (isingVec α (c α)) = isingVec α (c α) ∧
      (g ^ n) (isingVec α (-c α)) = isingVec α (-c α) := by
    obtain ⟨n, hn, hp⟩ := aut_isingVec_periodic g α.property (c α) (hc α)
    obtain ⟨m, hm, hq⟩ := aut_isingVec_periodic g α.property (-c α)
      (by rw [neg_sq]; exact hc α)
    refine ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
    · rw [pow_mul]
      exact isingRigid_pow_fix (g ^ n) _ hp m
    · rw [Nat.mul_comm, pow_mul]
      exact isingRigid_pow_fix (g ^ m) _ hq n
  choose k hkpos hkp hkm using hper
  let K := ∏ α : I, k α
  have hK : 1 ≤ K := by
    change 0 < ∏ α : I, k α
    exact Finset.prod_pos fun α _ => hkpos α
  refine ⟨K, hK, ?_⟩
  obtain ⟨hq, hx⟩ := aut_fix_quad_minimal_of_fix_ising (g ^ K) (by
    intro α hα
    let i : I := ⟨α, hα⟩
    have hd : k i ∣ K := Finset.dvd_prod_of_mem k (Finset.mem_univ i)
    exact ⟨c i, hc i, isingRigid_pow_fix_of_dvd g _ (hkp i) hd,
      isingRigid_pow_fix_of_dvd g _ (hkm i) hd⟩)
  exact aut_fix_untwisted_of_fix_quad_minimal (g ^ K) hq hx

/-- Every automorphism of the Moonshine VOA has finite order. -/
theorem autVnat_isOfFinOrder : ∀ g : AutVnat, IsOfFinOrder g := by
  intro g
  obtain ⟨n, hn, hU⟩ := aut_pow_fix_untwisted g
  obtain ⟨m, hm, hσ⟩ := aut_pow_fix_untwisted (sigmaAut * g * sigmaAut⁻¹)
  have hsx : sigmaAut ((0, xGen) : Vnat) = ((Dnat.Ψ xGen, 0) : Vnat) := by
    rw [sigmaAut_apply, M8hKey.sigNat_Ts Dnat xGen_mem]
  have hT : (g ^ m) ((0, xGen) : Vnat) = ((0, xGen) : Vnat) := by
    apply sigmaAut.toLinearEquiv.injective
    have h := hσ (Dnat.Ψ xGen)
    rw [← hsx, conj_pow, Aut.mul_apply, Aut.mul_apply, Aut.inv_apply,
      ← Aut.coe_toLinearEquiv, LinearEquiv.symm_apply_apply] at h
    exact h
  have hpow : g ^ (n * m) = 1 := by
    apply aut_eq_one_of_fix_untwisted_twistedGen
    · intro x
      rw [pow_mul]
      exact isingRigid_pow_fix (g ^ n) _ (hU x) m
    · rw [Nat.mul_comm, pow_mul]
      exact isingRigid_pow_fix (g ^ m) _ hT n
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n * m, Nat.mul_pos hn hm, hpow⟩

end VOA.Moonshine.ConwayNorton.M8
