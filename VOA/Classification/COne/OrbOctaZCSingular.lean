import VOA.Classification.COne.OrbOddChain
import VOA.Classification.COne.OrbOctaRSpan

/-! The level-nine singular vector of the weight-sixteen octahedral primary.

This is a genuine state identity, certified by L(1), L(2), and positivity of
Virasoro's form. Its direct Zhu projection is the zero polynomial; applying
it directly to the primary gives no conformal annihilator. Mixed mode
relations, rather than this direct projection, are needed for that purpose.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000

namespace VOA.Classification.COne.OrbOctaZC
open VOA VertexOperatorAlgebra OrbOdd OrbSpan OrbPrim OrbC2b OrbC2c OrbOcta

/-- The normalized singular vector, with coefficient one on L(-1)^9. -/
def s9v : VVec := ofRaw [
  (328218880, 1, [9]),
  (-103474128, 1, [8, 1]),
  (-74050560, 1, [7, 2]),
  (16494720, 1, [7, 1, 1]),
  (-64944640, 1, [6, 3]),
  (26630720, 1, [6, 2, 1]),
  (-2076960, 1, [6, 1, 1, 1]),
  (-64838400, 1, [5, 4]),
  (22565096, 1, [5, 3, 1]),
  (10481664, 1, [5, 2, 2]),
  (-4976048, 1, [5, 2, 1, 1]),
  (204000, 1, [5, 1, 1, 1, 1]),
  (12157200, 1, [4, 4, 1]),
  (19148800, 1, [4, 3, 2]),
  (-4565640, 1, [4, 3, 1, 1]),
  (-4358912, 1, [4, 2, 2, 1]),
  (728160, 1, [4, 2, 1, 1, 1]),
  (-18936, 1, [4, 1, 1, 1, 1, 1]),
  (2696192, 1, [3, 3, 3]),
  (-3671296, 1, [3, 3, 2, 1]),
  (305436, 1, [3, 3, 1, 1, 1]),
  (-1179648, 1, [3, 2, 2, 2]),
  (895872, 1, [3, 2, 2, 1, 1]),
  (-78480, 1, [3, 2, 1, 1, 1, 1]),
  (1428, 1, [3, 1, 1, 1, 1, 1, 1]),
  (147456, 1, [2, 2, 2, 2, 1]),
  (-52480, 1, [2, 2, 2, 1, 1, 1]),
  (4368, 1, [2, 2, 1, 1, 1, 1, 1]),
  (-120, 1, [2, 1, 1, 1, 1, 1, 1, 1]),
  (1, 1, [1, 1, 1, 1, 1, 1, 1, 1, 1])]

def s9chk (m : ℕ) : Bool :=
  match bindV (lowerF 16 1 64 m) s9v with
  | some r => isZeroK (normK r)
  | none => false

set_option maxHeartbeats 2000000 in
-- The kernel normal-orders all thirty level-nine words.
theorem s9chk_one : s9chk 1 = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel normal-orders all thirty level-nine words.
theorem s9chk_two : s9chk 2 = true := by decide +kernel

theorem s9v_spec : ∀ p ∈ s9v, p.2.sum = 9 ∧ p.2 ≠ [] ∧ posW p.2 = true := by
  decide +kernel

/-- The direct Zhu image of this singular vector vanishes identically. -/
theorem s9_zhu_polynomial_zero : zp (zhuV 16 s9v) = 0 := by
  have h : ptrim (zhuV 16 s9v) = [] := by decide +kernel
  rw [← zp_ptrim, h]; rfl

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V} {x : V}

theorem s9chk_sound (hc : W.centralCharge = ((1 : ℚ) : ℂ))
    (hx : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) x = 0)
    (hx0 : W.L 0 x = ((16 : ℚ) : ℂ) • x)
    {m : ℕ} (hk : s9chk m = true) : W.L (m : ℤ) (evV W x s9v) = 0 := by
  unfold s9chk at hk
  split at hk
  · rename_i r hr
    rw [← bindV_sound (fun w r h => lowerF_sound hc hx hx0 _ _ w r h) s9v r hr]
    exact evV_eq_zero_of_isZeroK hk
  · exact absurd hk (by simp)
end General

noncomputable section
noncomputable local instance : Fintype octa :=
  @Fintype.ofFinite _ (Finite.of_equiv (Equiv.Perm (Fin 4)) octa_group.some.symm.toEquiv)

theorem X_primary : OrbOctaR.X ∈ prim OrbOctaR.W 16 := by
  rw [mem_prim]
  refine ⟨OrbOctaR.X_grading, fun m => ?_⟩
  apply Subtype.ext
  change (V2m 1 le_rfl).L ((m : ℤ) + 1)
    ((Tav I4 : (orbifold octa).carrier) : VOA.LatGen.LatModuleGen
      (VOA.LatGen.Triplet.latP 1)) = 0
  rw [Tav_coe ⟨isA4Inv_I4, s3_I4⟩]
  exact ((mem_prim _).mp (T2_prim I4_hom)).2 m

/-- The level-nine singular vector vanishes on the actual S4 primary. -/
theorem s9_zero : evV OrbOctaR.W OrbOctaR.X s9v = 0 := by
  have hx : ∀ m : ℕ, 1 ≤ m → OrbOctaR.W.L (m : ℤ) OrbOctaR.X = 0 := by
    intro m hm
    have h := ((mem_prim _).mp X_primary).2 (m - 1)
    rwa [show ((m - 1 : ℕ) : ℤ) + 1 = m by omega] at h
  have hx0 : OrbOctaR.W.L 0 OrbOctaR.X = ((16 : ℚ) : ℂ) • OrbOctaR.X := by
    rw [OrbOctaR.W.L_zero_grading _ OrbOctaR.X_grading]; norm_num
  have hc : OrbOctaR.W.centralCharge = ((1 : ℚ) : ℂ) := by
    change (V2m 1 le_rfl).centralCharge = _
    simpa using V2m_centralCharge 1 le_rfl
  have hp : evV OrbOctaR.W OrbOctaR.X s9v ∈ prim OrbOctaR.W (16 + (9 : ℕ)) := by
    rw [mem_prim]
    refine ⟨evV_mem_grading OrbOctaR.X_grading (fun p hp => (s9v_spec p hp).1), fun m => ?_⟩
    have h := L_pos_of_L1_L2 (s9chk_sound hc hx hx0 s9chk_one)
      (s9chk_sound hc hx hx0 s9chk_two) (m + 1) (by omega)
    simpa using h
  have hl := evV_mem_lowerDesc OrbOctaR.X_grading (N := 9) (v := s9v) s9v_spec
  have hz := prim_inf_lowerDesc (W := OrbOctaR.W)
    ((v2VirUnitary_holds.some).restrict (orbifold octa)) (16 + (9 : ℕ))
  have hmem : evV OrbOctaR.W OrbOctaR.X s9v ∈
      prim OrbOctaR.W (16 + (9 : ℕ)) ⊓ lowerDesc OrbOctaR.W (16 + (9 : ℕ)) := ⟨hp, hl⟩
  rw [hz] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

end
end VOA.Classification.COne.OrbOctaZC
