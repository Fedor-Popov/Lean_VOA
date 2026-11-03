import VOA.Classification.COne.OrbOctaRCPair
import VOA.Classification.COne.OrbOctaRCBottom

/-! Scalar bottom coefficients and skew symmetry for translation-annihilating probes. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e OrbC2g
  VertexOperatorAlgebra

def bottomTerm (b : ℚ) (t : ℚ × List ℕ) : ℚ × ℚ :=
  let q := t.1 * (-b) ^ t.2.length * 2 ^ (t.2.length / 2)
  if t.2.length % 2 = 0 then (q, 0) else (0, q)

def bottomRaw (b : ℚ) (P : RawPoly ℕ) : ℚ × ℚ :=
  (P.map (bottomTerm b)).sum

theorem bottomRaw_sound (b : ℚ) (c : ℂ) (hc : c * c = ((2 : ℚ) : ℂ))
    (P : RawPoly ℕ) : bottomValue ((b : ℂ) * c) P = pairValue c (bottomRaw b P) := by
  induction P with
  | nil => simp [bottomValue, bottomRaw]
  | cons t P ih =>
    simp only [bottomValue, bottomRaw, List.map_cons, List.sum_cons, map_add] at *
    rw [ih]
    congr 1
    rw [show -((b : ℂ) * c) = (-(b : ℂ)) * c by ring, mul_pow,
      power_two_reduce c hc]
    simp only [bottomTerm, pairValue, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    split_ifs <;> push_cast <;> ring

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (A : VertexOperatorAlgebra V)

theorem probe_skew (f : V →ₗ[ℂ] ℂ) (hf : ∀ v, f (A.toPreVertexAlgebra.T v) = 0)
    (u v : V) (n : ℤ) : f (A.smul u n v) = sgn (-n - 1) * f (A.smul v n u) := by
  rw [skew_mode, map_finsum f (skew_support_finite A u v (-n - 1))]
  rw [finsum_eq_single _ 0]
  · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, Nat.cast_zero, sub_zero,
      pow_zero, Module.End.one_apply, one_smul, map_smul, smul_eq_mul]
    rfl
  · intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [map_smul, map_smul, pow_succ', Module.End.mul_apply, hf]
    simp

end General

open VOA.LatGen VOA.LatGen.Triplet LatMod OrbSpan PlusC2

noncomputable def ambientProbe (q : FockN (VOA.IntegralLattice.rank (latP 1))) :
    LatModuleGen (latP 1) →ₗ[ℂ] ℂ :=
  (v2mVirUnitary 1 le_rfl).form.flip (sector 4 q)

theorem ambientProbe_sector (q p : FockN (VOA.IntegralLattice.rank (latP 1))) (d : ℤ) :
    ambientProbe q (sector d p) = if 4 = d then fockForm p q else 0 := by
  exact sector_form d 4 p q

theorem ambientProbe_EE (q : FockN (VOA.IntegralLattice.rank (latP 1)))
    (b d n : ℤ) (hd : 4 ≠ b + d) :
    ambientProbe q ((V2m 1 le_rfl).smul (latChargeGen (latP 1) b) n
      (latChargeGen (latP 1) d)) = 0 := by
  rw [V2m_charge_smul_charge, PlusCharacterTable.rankOne_cocycle, one_smul]
  change ambientProbe q (sector (b + d) _) = 0
  rw [ambientProbe_sector, if_neg hd]

theorem ambientProbe_EN (q : FockN (VOA.IntegralLattice.rank (latP 1)))
    (b n : ℤ) (P : RawPoly ℕ) (hb : 4 ≠ b) :
    ambientProbe q ((V2m 1 le_rfl).smul (latChargeGen (latP 1) b) n (ls 1 P)) = 0 := by
  have h := V2m_charge_smul_evRc 1 le_rfl b 0 n (liftR P)
  rw [evRc_liftR, PlusCharacterTable.rankOne_cocycle, one_smul, add_zero] at h
  rw [show ls 1 P = latStateGen (latP 1) (evR (a0 1) P) 0 from rfl, h]
  change ambientProbe q (sector b _) = 0
  rw [ambientProbe_sector, if_neg hb]

theorem ambientProbe_NN (q : FockN (VOA.IntegralLattice.rank (latP 1)))
    (P Q : RawPoly ℕ) (n : ℤ) :
    ambientProbe q ((V2m 1 le_rfl).smul (ls 1 P) n (ls 1 Q)) = 0 := by
  change ambientProbe q ((V2m 1 le_rfl).smul (latStateGen _ _ 0) n
    (latStateGen _ _ 0)) = 0
  rw [V2m_smul_sec0]
  change ambientProbe q (sector 0 _) = 0
  rw [ambientProbe_sector, if_neg (by norm_num)]

theorem ambientProbe_one_T (v : LatModuleGen (latP 1)) :
    ambientProbe 1 ((V2m 1 le_rfl).toPreVertexAlgebra.T v) = 0 := by
  rw [T_eq_Lneg1]
  change (v2mVirUnitary 1 le_rfl).form ((V2m 1 le_rfl).L (-1) v)
    (latChargeGen (latP 1) (4 : ℤ)) = 0
  rw [(v2mVirUnitary 1 le_rfl).adjoint, neg_neg,
    show (V2m 1 le_rfl).L 1 (latChargeGen (latP 1) (4 : ℤ)) = 0 from
      OrbPrim.chargeGen_primary 4 0, map_zero]

theorem ambientProbe_self (q : FockN (VOA.IntegralLattice.rank (latP 1)))
    (P : RawPoly ℕ) (n : ℤ)
    (hT : ∀ v, ambientProbe q ((V2m 1 le_rfl).toPreVertexAlgebra.T v) = 0)
    (hs : sgn (-n - 1) = 1) :
    let x := (2 : ℂ) • latChargeGen (latP 1) (4 : ℤ) + ls 1 P +
      (2 : ℂ) • latChargeGen (latP 1) (-4 : ℤ)
    ambientProbe q ((V2m 1 le_rfl).smul x n x) =
      4 * ambientProbe q ((V2m 1 le_rfl).smul (latChargeGen (latP 1) (4 : ℤ)) n
        (ls 1 P)) := by
  dsimp only
  have hp (b : ℤ) := probe_skew (V2m 1 le_rfl) (ambientProbe q) hT
    (ls 1 P) (latChargeGen (latP 1) b) n
  simp only [hs, one_mul] at hp
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    map_add, map_smul, smul_eq_mul]
  rw [ambientProbe_EE _ 4 4 _ (by norm_num),
    ambientProbe_EE _ 4 (-4) _ (by norm_num),
    ambientProbe_EE _ (-4) 4 _ (by norm_num),
    ambientProbe_EE _ (-4) (-4) _ (by norm_num),
    ambientProbe_NN, hp 4, hp (-4), ambientProbe_EN _ (-4) _ _ (by norm_num)]
  ring

end VOA.Classification.COne.OrbOctaRC
