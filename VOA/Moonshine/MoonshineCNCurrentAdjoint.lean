import VOA.Moonshine.MoonshineCNChargedAdjoint

/-! Skew-adjointness of the complex-frame Heisenberg generators, including momentum zero modes. -/

namespace VOA.Moonshine.ConwayNorton

open IntegralLattice LatGen HeisenbergN Nondeg
open Module (End)

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem latForm_frameCurrent_state (a : Fin (rank L)) (n : ℤ)
    (p q : FockN (rank L)) (α β : L.carrier) :
    latForm L (mode (frameCurrent F a) n (latStateGen L p α)) (latStateGen L q β) =
      -latForm L (latStateGen L p α)
        (mode (frameCurrent F a) (-n) (latStateGen L q β)) := by
  classical
  simp only [mode_apply, frameCurrent_tmul, currentN_apply,
    show -(-n - 1) - 1 = n by ring,
    show -(- -n - 1) - 1 = -n by ring]
  by_cases hαβ : α + β = 0
  · have hβ : β = -α := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hαβ
    subst β
    have hc : frameCoordinate F (-α) a = -frameCoordinate F α a := by
      exact congrFun (F.coordinate.map_neg α) a
    by_cases hn : n = 0
    · subst n
      simp [latForm_state, hc]
    · simp only [if_neg (show -n - 1 ≠ -1 by omega),
        if_neg (show - -n - 1 ≠ -1 by omega), add_zero,
        latForm_state, add_neg_cancel, if_true, uForm_oscN, mul_neg]
  · split_ifs <;>
      simp [map_add, LinearMap.add_apply, latForm_state, hαβ]

/-- Every mode of a complex-frame current is skew-adjoint to its opposite mode. -/
theorem latForm_frameCurrent_adjoint (a : Fin (rank L)) (n : ℤ)
    (x y : LatModuleGen L) :
    latForm L (mode (frameCurrent F a) n x) y =
      -latForm L x (mode (frameCurrent F a) (-n) y) := by
  induction x using induction_latState L with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', neg_add_rev]; ring
  | hsmul c x hx => simp only [map_smul, LinearMap.smul_apply, hx, smul_neg]
  | hst p α =>
      induction y using induction_latState L with
      | h0 => simp
      | hadd y y' hy hy' => simp only [map_add, hy, hy', neg_add_rev]; ring
      | hsmul c y hy => simp only [map_smul, hy, smul_neg]
      | hst q β => exact latForm_frameCurrent_state F a n p q α β

/-- Reconstruction identifies the one-oscillator state with the complex-frame current. -/
theorem frameStateField_currentState (hEven : L.Even) (a : Fin (rank L)) :
    frameStateField F hEven (frameWordState L [(0, a)] 0) = frameCurrent F a := by
  rw [frameStateField_word, frameWordField_cons]
  funext s
  apply LinearMap.ext
  intro x
  rw [nprod_apply]
  have hterm (m : ℤ) :
      normalOrdered (frameDerivativeCurrent F a 0) (frameWordField F [] 0) m (s - m) x =
        if m = s then frameCurrent F a s x else 0 := by
    rw [frameDerivativeCurrent_zero, frameWordField_nil, canonicalChargedField_zero_eq_one,
      normalOrdered_apply, FormalDist.one_apply]
    by_cases hm : m = s
    · subst m; simp
    · simp [show s - m ≠ 0 by omega, hm]
  simp_rw [hterm]
  rw [finsum_eq_single _ s (fun m hm => if_neg hm), if_pos rfl]

theorem latForm_frameStateField_current_adjoint (hEven : L.Even) (a : Fin (rank L))
    (n : ℤ) (x y : LatModuleGen L) :
    latForm L (mode (frameStateField F hEven (frameWordState L [(0, a)] 0)) n x) y =
      -latForm L x
        (mode (frameStateField F hEven (frameWordState L [(0, a)] 0)) (-n) y) := by
  rw [frameStateField_currentState]
  exact latForm_frameCurrent_adjoint F a n x y

/-- The tested generators generate the full reconstructed lattice vertex algebra. -/
theorem frameStateField_generated_by_charges_currents (hEven : L.Even)
    (S : Submodule ℂ (LatModuleGen L))
    (hCharge : ∀ α, latChargeGen L α ∈ S)
    (hCurrent : ∀ a, frameWordState L [(0, a)] 0 ∈ S)
    (hClosed : ∀ u ∈ S, ∀ v ∈ S, ∀ n : ℤ,
      mode (frameStateField F hEven u) n v ∈ S) : S = ⊤ := by
  apply top_unique
  rw [← frameWordState_span L]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨l, α⟩, rfl⟩
  induction l with
  | nil => exact hCharge α
  | cons ia rest ih =>
      have h := hClosed _ (hCurrent ia.2) _ ih (-(ia.1 : ℤ) - 1)
      rw [frameStateField_currentState, mode_apply,
        show -(-(ia.1 : ℤ) - 1) - 1 = (ia.1 : ℤ) by ring,
        frameCurrent_apply, if_neg (by omega : (ia.1 : ℤ) ≠ -1), add_zero] at h
      exact h

end VOA.Moonshine.ConwayNorton
