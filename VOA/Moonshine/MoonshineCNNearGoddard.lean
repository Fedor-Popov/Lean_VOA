import VOA.Core.SuperTranslationCovariance

/-! Goddard uniqueness and Dong locality for a near-VOA, without finiteness assumptions.
The difference-field proof is the sign-independent argument of `SuperGoddard`. -/

namespace VOA
open Module (End)
universe u
namespace NearVOA
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

noncomputable def smul (V : NearVOA 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) : 𝒱 := mode (V.Y u) n v

theorem smul_def (V : NearVOA 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul u n v = mode (V.Y u) n v := rfl

noncomputable def L (V : NearVOA 𝒱) (n : ℤ) : End ℂ 𝒱 :=
  mode (V.Y V.conformalVector) (n + 1)

theorem L_def (V : NearVOA 𝒱) (n : ℤ) :
    V.L n = mode (V.Y V.conformalVector) (n + 1) := rfl

noncomputable def T (V : NearVOA 𝒱) : End ℂ 𝒱 := V.L (-1)

@[simp] theorem smul_neg_one_vacuum (V : NearVOA 𝒱) (u : 𝒱) :
    V.smul u (-1) V.vacuum = u := (V.creation u).1

theorem smul_vacuum_eq_zero (V : NearVOA 𝒱) (u : 𝒱) {n : ℤ} (hn : 0 ≤ n) :
    V.smul u n V.vacuum = 0 := (V.creation u).2 n hn

theorem localε_one (V : NearVOA 𝒱) (u v : 𝒱) : Localε 1 (V.Y u) (V.Y v) :=
  (localε_one_iff _ _).mpr (V.locality u v)

theorem Y_apply_vacuum_eq_zero (V : NearVOA 𝒱) (b : 𝒱) {n : ℤ} (hn : n < 0) :
    (V.Y b) n V.vacuum = 0 := by
  have h : (V.Y b) n V.vacuum = V.smul b (-n - 1) V.vacuum := by
    rw [smul_def, mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring]
  rw [h]
  exact V.smul_vacuum_eq_zero b (by omega)

theorem Y_apply_vacuum_zero (V : NearVOA 𝒱) (b : 𝒱) : (V.Y b) 0 V.vacuum = b := by
  have h : (V.Y b) 0 V.vacuum = V.smul b (-1) V.vacuum := by
    rw [smul_def, mode_apply]; norm_num
  rw [h, smul_neg_one_vacuum]

def goddardDifference (V : NearVOA 𝒱) (A : FormalDist (End ℂ 𝒱)) (a b : 𝒱) :
    FormalDist₂ 𝒱 := fun p q => A p ((V.Y b) q V.vacuum) - (V.Y a) p ((V.Y b) q V.vacuum)

@[simp] theorem goddardDifference_apply (V : NearVOA 𝒱) (A : FormalDist (End ℂ 𝒱))
    (a b : 𝒱) (p q : ℤ) :
    goddardDifference V A a b p q = A p ((V.Y b) q V.vacuum) - (V.Y a) p ((V.Y b) q V.vacuum) := rfl

theorem goddard_pointwiseε (V : NearVOA 𝒱) (A : FormalDist (End ℂ 𝒱)) (a : 𝒱)
    (ε : ℂ) (b : 𝒱) (hAloc : Localε ε A (V.Y b)) (hVloc : Localε ε (V.Y a) (V.Y b))
    (hAvac : ∀ m : ℤ, A m V.vacuum = (V.Y a) m V.vacuum) (m : ℤ) :
    A m b = (V.Y a) m b := by
  obtain ⟨N₁, hN₁⟩ := hAloc
  obtain ⟨N₂, hN₂⟩ := hVloc

  have hDeq : goddardDifference V A a b = applyVec V.vacuum (bracketDistε ε A (V.Y b))
      - applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b)) := by
    ext p q
    have hsub : (applyVec V.vacuum (bracketDistε ε A (V.Y b))
        - applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b))) p q
        = applyVec V.vacuum (bracketDistε ε A (V.Y b)) p q
          - applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b)) p q := rfl
    rw [hsub]
    simp only [goddardDifference_apply, applyVec_apply, bracketDistε_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.mul_apply]
    rw [hAvac p]
    abel

  have hkill : mulBySubPow (N₁ + N₂) (goddardDifference V A a b) = 0 := by
    rw [hDeq, map_sub]
    have e1 : mulBySubPow (N₁ + N₂) (applyVec V.vacuum (bracketDistε ε A (V.Y b))) = 0 :=
      mulBySubPow_eq_zero_mono (Nat.le_add_right N₁ N₂)
        (by rw [← applyVec_mulBySubPow, hN₁, applyVec_zero])
    have e2 : mulBySubPow (N₁ + N₂)
        (applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b))) = 0 :=
      mulBySubPow_eq_zero_mono (Nat.le_add_left N₂ N₁)
        (by rw [← applyVec_mulBySubPow, hN₂, applyVec_zero])
    rw [e1, e2, sub_zero]

  have hbb : IsBddBelow₂ (goddardDifference V A a b) := by
    refine ⟨0, fun p q hq => ?_⟩
    rw [goddardDifference_apply, V.Y_apply_vacuum_eq_zero b hq, map_zero, map_zero, sub_zero]
  have hD0 : goddardDifference V A a b = 0 :=
    eq_zero_of_mulBySubPow_of_bddBelow (N₁ + N₂) _ hkill hbb
  have hfin : goddardDifference V A a b m 0 = 0 := congrFun (congrFun hD0 m) 0
  rw [goddardDifference_apply, V.Y_apply_vacuum_zero b, sub_eq_zero] at hfin
  exact hfin


/-- Ordinary locality and the vacuum tower determine a vertex operator. -/
theorem goddard_uniqueness (V : NearVOA 𝒱) (A : FormalDist (End ℂ 𝒱)) (a : 𝒱)
    (hAloc : ∀ b : 𝒱, Local A (V.Y b))
    (hAvac : ∀ m : ℤ, A m V.vacuum = (V.Y a) m V.vacuum) : A = V.Y a := by
  funext m
  apply LinearMap.ext
  intro b
  exact V.goddard_pointwiseε A a 1 b ((localε_one_iff _ _).mpr (hAloc b))
    (V.localε_one a b) hAvac m

theorem dong_fields (V : NearVOA 𝒱) (u v w : 𝒱) (k : ℕ) :
    Local (cCoeff k (bracketDist (V.Y u) (V.Y v))) (V.Y w) := by
  have h := dong_nonnegε (by norm_num : (1 : ℂ) * 1 = 1)
    (V.localε_one u v) (V.localε_one u w) (V.localε_one v w) k
  simpa only [one_mul, bracketDistε_one, localε_one_iff] using h

end NearVOA
end VOA
