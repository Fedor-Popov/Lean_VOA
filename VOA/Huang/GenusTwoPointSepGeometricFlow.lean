import VOA.Huang.GenusTwoPointSepIntertwinerFlow

/-!
# Formal integration of the geometric intertwiner action

The geometric generator acts on the insertion and on complex mode indices.
It is distinct from the source/target commutator generator. Jacobi identifies
them on an intertwiner, and commutation identifies their entire formal flows.
All generator sums are finite jets. This does not yet identify this flow with
the explicit logarithmic coordinate substitution and its local state operator.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P Q N : LWModule W}

/-- A finite jet of the positive Virasoro generator. -/
def coordinateJet (a : ℕ → ℂ) (K : ℕ) (k : ℕ) : ℂ := if k < K then a k else 0

theorem moduleCoordGen_jet (P : LWModule W) (a : ℕ → ℂ) (K : ℕ) :
    moduleCoordGen P (coordinateJet a K) =
      ∑ k ∈ Finset.range K, a k • mode (P.isMod.YM W.conformalVector) ((k : ℤ) + 2) := by
  ext x
  change (∑ᶠ k, coordinateJet a K k • _) = _
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range K)]
  · simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [coordinateJet, if_pos (Finset.mem_range.mp hk)]
  · intro k hk
    by_contra h
    have hkK : ¬k < K := by simpa only [Finset.mem_coe, Finset.mem_range] using h
    exact hk (by simp [coordinateJet, hkK])

/-- Complex-indexed formal fields; no integral-mode restriction is imposed. -/
abbrev CoordinateField (P Q N : LWModule W) :=
  ℂ → P.carrier → Q.carrier →ₗ[ℂ] N.carrier

/-- The source/target infinitesimal sandwich, acting on every field. -/
def fieldConjugation (D : Module.End ℂ N.carrier) (E : Module.End ℂ Q.carrier) :
    Module.End ℂ (CoordinateField P Q N) where
  toFun f n w := conjugationGenerator D E (f n w)
  map_add' f g := by funext n w; exact (conjugationGenerator D E).map_add _ _
  map_smul' c f := by funext n w; exact (conjugationGenerator D E).map_smul c _

/-- The geometric action on the insertion and coordinate. The `j = 0` term
is formal differentiation, by the intertwiner translation property. -/
def geometricJet (a : ℕ → ℂ) (K : ℕ) : Module.End ℂ (CoordinateField P Q N) where
  toFun f n w := ∑ k ∈ Finset.range K, a k •
    ∑ j ∈ Finset.range (k + 3), ((k + 2).choose j : ℂ) •
      f ((k : ℂ) + 2 + n - j) (mode (P.isMod.YM W.conformalVector) j w)
  map_add' f g := by
    funext n w
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext n w
    simp only [Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    simp only [RingHom.id_apply, smul_smul]
    congr 1
    ring

/-- Output conjugation commutes with the independent insertion/coordinate action. -/
theorem fieldConjugation_commute_geometricJet
    (D : Module.End ℂ N.carrier) (E : Module.End ℂ Q.carrier)
    (a : ℕ → ℂ) (K : ℕ) :
    Commute (fieldConjugation (P := P) D E) (geometricJet a K) := by
  ext f n w x
  change conjugationGenerator D E ((geometricJet a K) f n w) x = _
  simp only [geometricJet, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    fieldConjugation]
  rfl

/-- Jacobi identifies the two generators on the actual intertwiner. -/
theorem geometricJet_intertwiner
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) (a : ℕ → ℂ) (K : ℕ) :
    fieldConjugation (moduleCoordGen N (coordinateJet a K))
      (moduleCoordGen Q (coordinateJet a K)) (fun n w => Y.val n w) =
        geometricJet a K (fun n w => Y.val n w) := by
  funext n w
  ext x
  change moduleCoordGen N _ (Y.val n w x) - Y.val n w (moduleCoordGen Q _ x) = _
  rw [moduleCoordGen_jet, moduleCoordGen_jet]
  simp only [geometricJet, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    ← Finset.sum_sub_distrib, ← smul_sub]
  change (∑ k ∈ Finset.range K, a k • _) = _
  apply Finset.sum_congr rfl
  intro k _
  have h := intertwiner_virasoro_comm Y (k + 1) n w x
  simpa only [SquareModule.roundL, Nat.cast_add, Nat.cast_one,
    show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega,
    show (k : ℤ) + 1 + 1 = k + 2 by ring,
    show (k : ℂ) + 1 + 1 = k + 2 by ring] using congrArg (a k • ·) h

/-- Commuting generators agreeing at the initial vector have identical formal flows. -/
theorem linearFlowCoeff_eq_of_commute {M : Type*} [AddCommGroup M] [Module ℂ M]
    (D E : Module.End ℂ M) (hDE : Commute D E) (x : M) (hx : D x = E x) (r : ℕ) :
    linearFlowCoeff D x r = linearFlowCoeff E x r := by
  have hp : ∀ r : ℕ, (D ^ r) x = (E ^ r) x := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [VOA.pow_succ'_apply, ih]
      change (D * E ^ r) x = _
      rw [(hDE.pow_right r).eq]
      change (E ^ r) (D x) = _
      rw [hx, pow_succ, Module.End.mul_apply]
  simp only [linearFlowCoeff, hp]

theorem fieldConjugation_flow (D : Module.End ℂ N.carrier)
    (E : Module.End ℂ Q.carrier) (f : CoordinateField P Q N) (r : ℕ) (n : ℂ)
    (w : P.carrier) :
    linearFlowCoeff (fieldConjugation D E) f r n w = conjugationCoeff D E (f n w) r := by
  have hp : ∀ r : ℕ, (fieldConjugation D E ^ r) f n w =
      (conjugationGenerator D E ^ r) (f n w) := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [VOA.pow_succ'_apply, VOA.pow_succ'_apply]
      change conjugationGenerator D E ((fieldConjugation D E ^ r) f n w) = _
      rw [ih]
  simp only [linearFlowCoeff, Pi.smul_apply, conjugationCoeff, hp]

/-- Equality of formal series in the flow parameter, at every complex mode.
The right side is computed entirely by the geometric insertion/coordinate generator. -/
theorem intertwiner_geometricJet_flow
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) (a : ℕ → ℂ) (K r : ℕ)
    (n : ℂ) (w : P.carrier) :
    conjugationCoeff (moduleCoordGen N (coordinateJet a K))
      (moduleCoordGen Q (coordinateJet a K)) (Y.val n w) r =
        linearFlowCoeff (geometricJet a K) (fun m v => Y.val m v) r n w := by
  rw [← fieldConjugation_flow _ _ (fun m v => Y.val m v) r n w]
  exact congrArg (fun f : CoordinateField P Q N => f n w)
    (linearFlowCoeff_eq_of_commute _ _ (fieldConjugation_commute_geometricJet _ _ a K)
      _ (geometricJet_intertwiner Y a K) r)

/-- The geometric formal initial-value problem has no other solution. This
is the coefficientwise first-order flow ODE, including every descendant. -/
theorem intertwiner_geometricJet_flow_unique
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) (a : ℕ → ℂ) (K : ℕ)
    (g : ℕ → CoordinateField P Q N) (h₀ : g 0 = fun n w => Y.val n w)
    (hg : ∀ r, ((r + 1 : ℕ) : ℂ) • g (r + 1) = geometricJet a K (g r))
    (r : ℕ) (n : ℂ) (w : P.carrier) :
    g r n w = conjugationCoeff (moduleCoordGen N (coordinateJet a K))
      (moduleCoordGen Q (coordinateJet a K)) (Y.val n w) r := by
  rw [linearFlowCoeff_unique (geometricJet a K) _ g h₀ hg]
  exact (intertwiner_geometricJet_flow Y a K r n w).symm

/-- Every evaluated mode of the geometric flow is polynomial in the flow parameter. -/
theorem intertwiner_geometricJet_flow_finite
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) (a : ℕ → ℂ) (K : ℕ)
    (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    (Function.support (fun r =>
      linearFlowCoeff (geometricJet a K) (fun m v => Y.val m v) r n w x)).Finite := by
  simpa only [← intertwiner_geometricJet_flow] using
    conjugationCoeff_support_finite (moduleCoordGen_isLocNilp N _)
      (moduleCoordGen_isLocNilp Q _) (Y.val n w) x

/-- Evaluating the geometric jet flow is an algebraic finite computation. -/
theorem intertwiner_geometricJet_evaluate
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) (a : ℕ → ℂ) (K : ℕ)
    (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    expFun (moduleCoordGen_isLocNilp N (coordinateJet a K))
      (Y.val n w (expFun (moduleCoordGen_isLocNilp Q (coordinateJet a K)).neg x)) =
      ∑ᶠ r, linearFlowCoeff (geometricJet a K) (fun m v => Y.val m v) r n w x := by
  rw [expFun_conjugation_eq_finsum (moduleCoordGen_isLocNilp N _)
    (moduleCoordGen_isLocNilp Q _)]
  exact finsum_congr fun r => congrArg (fun f : Q.carrier →ₗ[ℂ] N.carrier => f x)
    (intertwiner_geometricJet_flow Y a K r n w)

end VOA.Huang.GenusTwoPoint.Separate
