import VOA.Examples.AffineSl2ParabolicEvaluation

/-! # Degree shifts for actual affine highest-module maps

A singular vector at relative degree N induces a genuine map from the
corresponding highest module after shifting the affine derivation. This
works in every actual representation, including the parabolic modules.
-/
namespace VOA.AffineVOA.HighestModule
noncomputable section
open AffineLie UniversalEnvelopingAlgebra
open Module (End)
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Shift an actual affine representation's degree origin by N, retaining
all its original currents and central action. -/
def highestEnergyShiftData (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (k : ℂ)
    (hC : R (AffineLie.C kappaForm kappaForm_isInvariant)=k • (1:End ℂ E))
    (N : ℤ) : AffineCurrentData k E where
  loopMode n := R.toLinearMap.comp (ofLoopₗ kappaForm kappaForm_isInvariant n)
  degree := R (ell0 kappaForm kappaForm_isInvariant) + (N:ℂ) • 1
  vacuum := 0
  loop_comm x y m n := by
    change ⁅R (ofLoop _ _ x m),R (ofLoop _ _ y n)⁆ = _
    rw [← R.map_lie,affine_bracket,map_add]
    congr 1
    split_ifs <;> simp only [map_smul,hC,map_zero] <;> rfl
  degree_comm x n := by
    change ⁅R (ell0 _ _) + (N:ℂ) • 1,R (ofLoop _ _ x n)⁆ = _
    have hz : ⁅(N:ℂ) • (1:End ℂ E),R (ofLoop _ _ x n)⁆=0 := by simp [Ring.lie_def]
    rw [add_lie,hz,add_zero,← R.map_lie,ell0_lie_ofLoop,map_smul]
    rfl
  pos_annihilate x n hn := map_zero _
  degree_vacuum := map_zero _

@[simp] theorem highestEnergyShiftData_mode (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (k : ℂ)
    (hC : R (AffineLie.C kappaForm kappaForm_isInvariant)=k • (1:End ℂ E))
    (N : ℤ) (a : Fin 3) (n : ℤ) :
    (highestEnergyShiftData R k hC N).rho (modeElement a n)=R (modeElement a n) := by
  rw [modeElement,AffineCurrentData.rho_ofLoop]
  rfl

/-- Genuine primitive equations in an actual representation give all
highest relations after the proved degree shift. -/
theorem highestEnergyShift_isHighest (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (k h : ℂ)
    (hC : R (AffineLie.C kappaForm kappaForm_isInvariant)=k • (1:End ℂ E))
    (N : ℤ) (v : E) (hN : R (ell0 kappaForm kappaForm_isInvariant) v=-(N:ℂ) • v)
    (hp : ∀ a n, 0<n → R (modeElement a n) v=0)
    (he : R (modeElement 0 0) v=0) (hh : R (modeElement 2 0) v=h • v) :
    IsHighest (highestEnergyShiftData R k hC N).rho v k h where
  central := (highestEnergyShiftData R k hC N).rho_C
  degree := by
    rw [AffineCurrentData.rho_ell0]
    change R (ell0 _ _) v + (N:ℂ) • v=0
    rw [hN]
    module
  modes a n hnot := by
    rw [highestEnergyShiftData_mode]
    have hn0 : 0 ≤ n := by
      simp only [HighestNormalOrdering.IsLower,not_or] at hnot
      omega
    by_cases hpos : 0<n
    · rw [hp a n hpos,if_neg (by omega)]
    · have hnz : n=0 := by omega
      subst n
      fin_cases a
      · simpa using he
      · exact False.elim (hnot (by simp [HighestNormalOrdering.IsLower]))
      · simpa using hh

/-- The actual map from a parabolic term determined by a singular state
in any affine representation. Its image, kernel and exactness are separate
mathematical questions, not fields assumed by this construction. -/
def shiftedParabolicMap (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (k : ℂ) (d : ℕ)
    (hC : R (AffineLie.C kappaForm kappaForm_isInvariant)=k • (1:End ℂ E))
    (N : ℤ) (v : E) (hN : R (ell0 kappaForm kappaForm_isInvariant) v=-(N:ℂ) • v)
    (hp : ∀ a n, 0<n → R (modeElement a n) v=0)
    (he : R (modeElement 0 0) v=0) (hh : R (modeElement 2 0) v=(d:ℂ) • v)
    (hf : (R (modeElement 1 0) ^ (d+1)) v=0) : Parabolic k d →ₗ[ℂ] E :=
  parabolicUniversalMap (highestEnergyShiftData R k hC N).rho v
    (highestEnergyShift_isHighest R k d hC N v hN hp he hh)
    (by simpa only [highestEnergyShiftData_mode] using hf)

@[simp] theorem shiftedParabolicMap_highest
    (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (k : ℂ) (d : ℕ)
    (hC : R (AffineLie.C kappaForm kappaForm_isInvariant)=k • (1:End ℂ E))
    (N : ℤ) (v : E) (hN : R (ell0 kappaForm kappaForm_isInvariant) v=-(N:ℂ) • v)
    (hp : ∀ a n, 0<n → R (modeElement a n) v=0)
    (he : R (modeElement 0 0) v=0) (hh : R (modeElement 2 0) v=(d:ℂ) • v)
    (hf : (R (modeElement 1 0) ^ (d+1)) v=0) :
    shiftedParabolicMap R k d hC N v hN hp he hh hf (parabolicHighest k d)=v :=
  parabolicUniversalMap_highest _ _ _ _

/-- Every current intertwines with the actual shifted parabolic map. -/
theorem shiftedParabolicMap_mode
    (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (k : ℂ) (d : ℕ)
    (hC : R (AffineLie.C kappaForm kappaForm_isInvariant)=k • (1:End ℂ E))
    (N : ℤ) (v : E) (hN : R (ell0 kappaForm kappaForm_isInvariant) v=-(N:ℂ) • v)
    (hp : ∀ a n, 0<n → R (modeElement a n) v=0)
    (he : R (modeElement 0 0) v=0) (hh : R (modeElement 2 0) v=(d:ℂ) • v)
    (hf : (R (modeElement 1 0) ^ (d+1)) v=0)
    (a : Fin 3) (n : ℤ) (u : Parabolic k d) :
    shiftedParabolicMap R k d hC N v hN hp he hh hf (parabolicMode k d a n u)=
      R (modeElement a n) (shiftedParabolicMap R k d hC N v hN hp he hh hf u) := by
  exact (parabolicUniversalMap_intertwines _ _ _ _ _ u).trans
    (congrArg (fun T : End ℂ E => T (shiftedParabolicMap R k d hC N v hN hp he hh hf u))
      (highestEnergyShiftData_mode R k hC N a n))

end
end VOA.AffineVOA.HighestModule
