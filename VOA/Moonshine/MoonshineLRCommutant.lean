import VOA.Moonshine.MonsterGriess.TrialityFourGroup
import VOA.Moonshine.MonsterGriess.ParityTraceSplitting

/-!
# Parity blocks and short-line characters of the rational Griess commutant
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA.Moonshine.MonsterGriess
open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.SpinLattice VOA.Moonshine.MonsterGriess.Visible
open scoped BigOperators

theorem commutXlift_zQ_mul (t : Q) : Xlift (zQ * t) = -Xlift t := by
  have h := Xlift_zQ_pow_mul (1 : ZMod 2) t
  change Xlift (zQ ^ 1 * t) = (-1 : ℚ) • Xlift t at h
  rw [pow_one, neg_one_smul] at h
  exact h

theorem commutRho_mem_Gmat (r : Q) : rhoEquiv r ∈ Generated.Gmat :=
  Generated.Hmat_le_Gmat (rhoEquiv_mem_Gvis r)

theorem commutXB_mem_Gmat : xB ∈ Generated.Gmat := by
  rw [← rhoEquiv_zQ]
  exact commutRho_mem_Gmat zQ

theorem commutTau_mem_Gmat : tauB ∈ Generated.Gmat := Generated.tauB_mem_Gmat

/-- Commutation with parity preserves the sum of the matrix and short-line blocks. -/
theorem commutPreservesAX (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ u, T (xB u) = xB (T u)) (A : symMat) (X : SpaceX) :
    (T (A, X, 0)).2.2 = 0 := by
  have e := congrArg (fun u : SpaceB => u.2.2) (h (A, X, 0))
  simp only [xB_apply, neg_zero] at e
  ext i j
  have e' := congrArg (fun w : SpaceW => w i j) e
  change _ = -_ at e'
  have : (T (A, X, 0)).2.2 i j = 0 := by linarith
  exact this

/-- Commutation with parity preserves the spin-tensor block. -/
theorem commutPreservesW (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ u, T (xB u) = xB (T u)) (W : SpaceW) :
    (T (0, 0, W)).1 = 0 ∧ (T (0, 0, W)).2.1 = 0 := by
  have hn : xB (0, 0, W) = -((0, 0, W) : SpaceB) := by simp [xB_apply]
  have e := h (0, 0, W)
  rw [hn, map_neg] at e
  constructor
  · apply Subtype.ext
    ext i j
    have e' := congrArg (fun u : SpaceB => (u.1 : Matrix _ _ ℚ) i j) e
    change -(T (0, 0, W)).1.val i j = (T (0, 0, W)).1.val i j at e'
    change (T (0, 0, W)).1.val i j = 0
    linarith
  · ext c
    have e' := congrArg (fun u : SpaceB => u.2.1 c) e
    change -(T (0, 0, W)).2.1 c = (T (0, 0, W)).2.1 c at e'
    change (T (0, 0, W)).2.1 c = 0
    linarith

/-- The sign of conjugation on the line indexed by a code-cocode pair. -/
def commutChar (p : C × Cocode) (r : Q) : ℚ :=
  sgn (pair p.1 (coordOf r).2 + pair (coordOf r).1 p.2)

theorem commutSpin_conj (x y : SpinCoord) :
    x⁻¹ * y * x =
      ⟨pair y.a x.δ + pair x.a y.δ + y.s, y.a, y.δ⟩ := by
  ext
  · simp only [SpinCoord.mul_s, SpinCoord.inv_s, SpinCoord.mul_δ,
      SpinCoord.inv_δ, pair_add_right]
    have htwo : (2 : ZMod 2) = 0 := rfl
    linear_combination (x.s + pair x.a x.δ) * htwo
  · simp only [SpinCoord.mul_a, SpinCoord.inv_a]
    rw [add_right_comm, add_self_C, zero_add]
  · simp only [SpinCoord.mul_δ, SpinCoord.inv_δ]
    rw [add_right_comm, add_self_cocode, zero_add]

theorem commutXlift_conj (r t : Q) :
    Xlift (r⁻¹ * t * r) = commutChar (coordOf t) r • Xlift t := by
  have he : spinEquiv.symm (r⁻¹ * t * r) =
      (spinEquiv.symm r)⁻¹ * spinEquiv.symm t * spinEquiv.symm r := by
    simp only [map_mul, map_inv]
  rw [commutSpin_conj] at he
  apply Xlift_eq_sgn_smul
  · unfold coordOf
    rw [he]
  · unfold centralCoord
    rw [he]
    rfl

theorem commutRho_Xlift (r t : Q) :
    rhoEquiv r (0, Xlift t, 0) = commutChar (coordOf t) r • (0, Xlift t, 0) := by
  rw [rhoEquiv_Xlift, commutXlift_conj]
  simp

theorem commutSgn_injective : Function.Injective MonsterGriess.sgn := by decide

theorem commutChar_injective {p q : C × Cocode}
    (h : ∀ r, commutChar p r = commutChar q r) : p = q := by
  have hp (a : C) (δ : Cocode) :
      pair p.1 δ + pair a p.2 = pair q.1 δ + pair a q.2 := by
    apply commutSgn_injective
    simpa only [commutChar, coordOf_rep] using h (rep (a, δ))
  apply Prod.ext
  · apply Subtype.ext
    funext i
    have e := hp 0 (Submodule.Quotient.mk (Pi.single i 1))
    simpa only [pair_zero_left, add_zero, pair_mk, dotProduct_single, mul_one] using e
  · exact ext_pair fun a => by simpa using hp a 0

theorem commutChar_nontrivial (p : ShortIdx) : ∃ r, commutChar p.1 r ≠ 1 := by
  by_contra! h
  apply Parity.ne_zero_of_isShortCoord p.2
  apply commutChar_injective
  intro r
  simpa [commutChar] using h r

theorem commutRho_Acomponent (r : Q) (u : SpaceB) : (rhoEquiv r u).1 = u.1 :=
  thetaA_one u.1

theorem commutThetaX_apply (r : Q) (X : SpaceX) (c : ShortIdx) :
    thetaX (rhoPair r) X c = commutChar c.1 r * X c := by
  have he : (LinearMap.proj c).comp (thetaX (rhoPair r)) =
      commutChar c.1 r • (LinearMap.proj c : SpaceX →ₗ[ℚ] ℚ) := by
    apply (Pi.basisFun ℚ ShortIdx).ext
    intro d
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, LinearMap.proj_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [thetaX_single, conjQ_rhoPair, commutXlift_conj, coordOf_rep, Xlift_rep]
    by_cases h : d = c
    · subst d
      simp
    · simp [h]
  exact LinearMap.congr_fun he X

theorem commutRho_Xcomponent (r : Q) (u : SpaceB) (c : ShortIdx) :
    (rhoEquiv r u).2.1 c = commutChar c.1 r * u.2.1 c :=
  commutThetaX_apply r u.2.1 c

/-- The joint fixed vectors of the extraspecial group form the symmetric-matrix block. -/
theorem commutFixed_eq_A (u : SpaceB) (h : ∀ r, rhoEquiv r u = u) :
    u = (u.1, 0, 0) := by
  have hw : u.2.2 = 0 := by
    have e := congrArg (fun v : SpaceB => v.2.2) (h zQ)
    rw [rhoEquiv_zQ] at e
    ext i j
    have e' := congrArg (fun w : SpaceW => w i j) e
    change -u.2.2 i j = u.2.2 i j at e'
    change u.2.2 i j = 0
    linarith
  have hx : u.2.1 = 0 := by
    ext c
    obtain ⟨r, hr⟩ := commutChar_nontrivial c
    have e := congrArg (fun v : SpaceB => v.2.1 c) (h r)
    dsimp only at e
    rw [commutRho_Xcomponent] at e
    change u.2.1 c = 0
    exact (mul_eq_zero.mp (by nlinarith : (commutChar c.1 r - 1) * u.2.1 c = 0)).resolve_left
      (sub_ne_zero.mpr hr)
  exact Prod.ext rfl (Prod.ext hx hw)

/-- An endomorphism commuting with the extraspecial action preserves symmetric matrices. -/
theorem commutPreservesA (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u)) (A : symMat) :
    T (A, 0, 0) = ((T (A, 0, 0)).1, 0, 0) := by
  apply commutFixed_eq_A
  intro r
  rw [← h, rhoEquiv_symMat]

/-- A short-line character has exactly its prescribed one-dimensional eigenspace. -/
theorem commutCharacter_eigenspace (c : ShortIdx) (u : SpaceB)
    (hw : u.2.2 = 0)
    (h : ∀ r, rhoEquiv r u = commutChar c.1 r • u) :
    u = u.2.1 c • ((0, Pi.single c 1, 0) : SpaceB) := by
  have ha : u.1 = 0 := by
    obtain ⟨r, hr⟩ := commutChar_nontrivial c
    have e := congrArg (fun v : SpaceB => v.1) (h r)
    dsimp only at e
    rw [commutRho_Acomponent] at e
    apply Subtype.ext
    ext i j
    have e' := congrArg (fun A : symMat => A.val i j) e
    change u.1.val i j = commutChar c.1 r * u.1.val i j at e'
    change u.1.val i j = 0
    exact (mul_eq_zero.mp (by nlinarith : (commutChar c.1 r - 1) * u.1.val i j = 0)).resolve_left
      (sub_ne_zero.mpr hr)
  have hx : u.2.1 = u.2.1 c • Pi.single c 1 := by
    ext d
    by_cases hd : d = c
    · subst d
      simp
    · have he : ∃ r, commutChar d.1 r ≠ commutChar c.1 r := by
        by_contra! he
        exact hd (Subtype.ext (commutChar_injective he))
      obtain ⟨r, hr⟩ := he
      have e := congrArg (fun v : SpaceB => v.2.1 d) (h r)
      dsimp only at e
      rw [commutRho_Xcomponent] at e
      change commutChar d.1 r * u.2.1 d = commutChar c.1 r * u.2.1 d at e
      have hz : u.2.1 d = 0 :=
        (mul_eq_zero.mp (by nlinarith :
          (commutChar d.1 r - commutChar c.1 r) * u.2.1 d = 0)).resolve_left
            (sub_ne_zero.mpr hr)
      simp [hd, hz]
  exact Prod.ext (by simpa using ha) (Prod.ext hx (by simpa using hw))

/-- Every short line is preserved by an endomorphism commuting with the extraspecial action. -/
theorem commutXlift_eigen (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (t : Q) (ht : IsShortCoord (coordOf t)) :
    ∃ a : ℚ, T (0, Xlift t, 0) = a • ((0, Xlift t, 0) : SpaceB) := by
  let c : ShortIdx := ⟨coordOf t, ht⟩
  have hx : T (0, Pi.single c 1, 0) =
      (T (0, Pi.single c 1, 0)).2.1 c • ((0, Pi.single c 1, 0) : SpaceB) := by
    apply commutCharacter_eigenspace
    · apply commutPreservesAX
      intro u
      simpa only [rhoEquiv_zQ] using h zQ u
    · intro r
      rw [← h]
      have e := commutRho_Xlift r (rep c.1)
      rw [coordOf_rep, Xlift_rep] at e
      rw [e, map_smul]
  refine ⟨(T (0, Pi.single c 1, 0)).2.1 c, ?_⟩
  have he : ((0, Xlift t, 0) : SpaceB) =
      sgn (centralCoord t) • ((0, Pi.single c 1, 0) : SpaceB) := by
    rw [Xlift_eq ht]
    simp [c]
  rw [he, map_smul, hx, smul_comm]
  simp

/-- The coefficient of an endomorphism on the odd short line in the triality basis. -/
def commutOddScalar (T : SpaceB →ₗ[ℚ] SpaceB) (c : C₀) (i : Fin 24) : ℚ :=
  tbasis.repr (T (tbasis (.inr (.inr (.inl (c, i, 0)))))) (.inr (.inr (.inl (c, i, 0))))

/-- Triality transports an odd-line eigenvalue around its three basis vectors. -/
theorem commutOdd_eigen_of_Xlift (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ u, T (tauB u) = tauB (T u)) (c : C₀) (i : Fin 24) (a : ℚ)
    (h0 : T (0, Xlift (rOdd c i), 0) = a • ((0, Xlift (rOdd c i), 0) : SpaceB))
    (k : Fin 3) :
    T (tbasis (.inr (.inr (.inl (c, i, k))))) =
      a • tbasis (.inr (.inr (.inl (c, i, k)))) := by
  have hz : T (tbasis (.inr (.inr (.inl (c, i, 0))))) =
      a • tbasis (.inr (.inr (.inl (c, i, 0)))) := by
    simpa only [tbasis_odd_zero] using h0
  have hs (j : Fin 3)
      (hj : T (tbasis (.inr (.inr (.inl (c, i, j))))) =
        a • tbasis (.inr (.inr (.inl (c, i, j))))) :
      T (tbasis (.inr (.inr (.inl (c, i, j + 1))))) =
        a • tbasis (.inr (.inr (.inl (c, i, j + 1)))) := by
    rw [← tauB_odd, h, hj, map_smul, tauB_odd]
  fin_cases k
  · exact hz
  · exact hs 0 hz
  · exact hs 1 (hs 0 hz)

/-- Extraspecial and triality commutation diagonalize every odd triality block. -/
theorem commutOdd_eigen (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (hτ : ∀ u, T (tauB u) = tauB (T u)) (c : C₀) (i : Fin 24) (k : Fin 3) :
    T (tbasis (.inr (.inr (.inl (c, i, k))))) =
      commutOddScalar T c i • tbasis (.inr (.inr (.inl (c, i, k)))) := by
  obtain ⟨a, ha⟩ := commutXlift_eigen T hQ (rOdd c i)
    (isShortCoord_labelElt (.inr (.inr (.inl (c, i)))))
  have he := commutOdd_eigen_of_Xlift T hτ c i a ha
  have hc : commutOddScalar T c i = a := by
    unfold commutOddScalar
    rw [he 0]
    simp
  rw [hc]
  exact he k

theorem commutCancel_sign_eigen (T : SpaceB →ₗ[ℚ] SpaceB) (s : ZMod 2)
    (a : ℚ) (u : SpaceB) (h : T (sgn s • u) = a • (sgn s • u)) :
    T u = a • u := by
  have hs : sgn s ≠ 0 := by
    intro hz
    have he := sgn_mul_self s
    rw [hz, zero_mul] at he
    exact zero_ne_one he
  apply smul_right_injective _ hs
  dsimp only
  rw [← map_smul, h, smul_comm]

/-- The two spin signs share the coefficient of their associated odd short line. -/
theorem commutSpin_eigen (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (hτ : ∀ u, T (tauB u) = tauB (T u)) (c : C₀) (i : Fin 24) (η : ZMod 2) :
    T (0, 0, tensor (Spin.E η c) (Pi.single i 1)) =
      commutOddScalar T c i • ((0, 0, tensor (Spin.E η c) (Pi.single i 1)) : SpaceB) := by
  have hc : η = 0 ∨ η = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) η
  rcases hc with rfl | rfl
  · have he := commutOdd_eigen T hQ hτ c i 2
    rw [tbasis_odd_two] at he
    apply commutCancel_sign_eigen T (P ((c : C) : Fin 24 → ZMod 2))
    simpa using he
  · have he := commutOdd_eigen T hQ hτ c i 1
    rw [tbasis_odd_one] at he
    apply commutCancel_sign_eigen T (((c : C) : Fin 24 → ZMod 2) i)
    simpa using he

/-- The spin-tensor eigenvalue is also the eigenvalue on the associated odd short line. -/
theorem commutOdd_Xlift (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (hτ : ∀ u, T (tauB u) = tauB (T u)) (c : C₀) (i : Fin 24) :
    T (0, Xlift (rOdd c i), 0) =
      commutOddScalar T c i • ((0, Xlift (rOdd c i), 0) : SpaceB) := by
  simpa only [tbasis_odd_zero] using commutOdd_eigen T hQ hτ c i 0

/-- Commutation with the generated group supplies the spin-tensor diagonalization. -/
theorem commutGmat_spin_eigen (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (c : C₀) (i : Fin 24) (η : ZMod 2) :
    T (0, 0, tensor (Spin.E η c) (Pi.single i 1)) =
      commutOddScalar T c i • ((0, 0, tensor (Spin.E η c) (Pi.single i 1)) : SpaceB) :=
  commutSpin_eigen T (fun r => h _ (commutRho_mem_Gmat r))
    (h _ commutTau_mem_Gmat) c i η

end VOA.Moonshine.ConwayNorton.M8
