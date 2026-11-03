import VOA.Huang.GenusOneWardInstance
import VOA.Huang.GenusOneWardTranslation
import VOA.Huang.GenusOneModeLinear
import VOA.Huang.PzTensorY4
import VOA.Modules.Translation
import VOA.Core.InvariantFormPStep

/-!
# Square-bracket form of the two-point Ward identities

`Phi Y₁ Y₂ x y ∈ ℂ⟦u⟧⟦t⟧` is the bilinear two-point trace series, defined on
weight components and extended bilinearly. Zhu's square modes on the
insertions expand into finitely many ordinary modes, so the minus-one identity
of `GenusOneWardInstance` becomes an identity between square-mode insertions.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.QEquation (TailBound)
open VOA.Huang.GenusOne (sqAct)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

section Bilinear
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

theorem tauZ_add_left (x x' : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℤ) :
    tauZ Y₁ Y₂ (x + x') y α₁ α₂ n k = tauZ Y₁ Y₂ x y α₁ α₂ n k + tauZ Y₁ Y₂ x' y α₁ α₂ n k := by
  simp only [tauZ, map_add, LinearMap.add_comp, lvl_add]

theorem tauZ_smul_left (a : ℂ) (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℤ) :
    tauZ Y₁ Y₂ (a • x) y α₁ α₂ n k = a * tauZ Y₁ Y₂ x y α₁ α₂ n k := by
  simp only [tauZ, map_smul, LinearMap.smul_comp, lvl_smul]

theorem tauZ_add_right (x : P₁.carrier) (y y' : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℤ) :
    tauZ Y₁ Y₂ x (y + y') α₁ α₂ n k = tauZ Y₁ Y₂ x y α₁ α₂ n k + tauZ Y₁ Y₂ x y' α₁ α₂ n k := by
  simp only [tauZ, map_add, LinearMap.comp_add, lvl_add]

theorem tauZ_smul_right (a : ℂ) (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℤ) :
    tauZ Y₁ Y₂ x (a • y) α₁ α₂ n k = a * tauZ Y₁ Y₂ x y α₁ α₂ n k := by
  simp only [tauZ, map_smul, LinearMap.comp_smul, lvl_smul]

/-- The two-point series on a pair of weight spaces. -/
def phiPair (α₁ α₂ : ℂ) : P₁.isMod.weight α₁ →ₗ[ℂ] P₂.isMod.weight α₂ →ₗ[ℂ] R2 :=
  LinearMap.mk₂ ℂ (fun x y => phiH Y₁ Y₂ x.val y.val α₁ α₂)
    (fun x x' y => ext2 fun n k => by
      simp only [phiH, c2_mk2, c2_add, Submodule.coe_add, tauZ_add_left])
    (fun a x y => ext2 fun n k => by
      simp only [phiH, c2_mk2, c2_smul, Submodule.coe_smul, tauZ_smul_left])
    (fun x y y' => ext2 fun n k => by
      simp only [phiH, c2_mk2, c2_add, Submodule.coe_add, tauZ_add_right])
    (fun a x y => ext2 fun n k => by
      simp only [phiH, c2_mk2, c2_smul, Submodule.coe_smul, tauZ_smul_right])

/-- The bilinear two-point trace series. -/
def Phi : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2 :=
  PzTensorY4.biHat fun α₁ α₂ => phiPair Y₁ Y₂ α₁ α₂

theorem Phi_homog {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) :
    Phi Y₁ Y₂ x y = phiH Y₁ Y₂ x y α₁ α₂ := by
  rw [Phi, PzTensorY4.biHat_homog _ hx hy]
  rfl

/-- The zero-mode insertion series on weight spaces. -/
def omZ (c : V) (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℤ) : ℂ :=
  lvl N (oMod N.isMod c * ((Y₁.val (sMode N Q α₁ n k) x).comp (Y₂.val (rMode N Q α₂ n k) y))) n

def omPair (c : V) (α₁ α₂ : ℂ) : P₁.isMod.weight α₁ →ₗ[ℂ] P₂.isMod.weight α₂ →ₗ[ℂ] R2 :=
  LinearMap.mk₂ ℂ (fun x y => ofZ (omZ Y₁ Y₂ c x.val y.val α₁ α₂))
    (fun x x' y => ext2 fun n k => by
      simp only [ofZ, omZ, c2_mk2, c2_add, Submodule.coe_add, map_add, LinearMap.add_comp,
        mul_add, lvl_add])
    (fun a x y => ext2 fun n k => by
      simp only [ofZ, omZ, c2_mk2, c2_smul, Submodule.coe_smul, map_smul, LinearMap.smul_comp,
        mul_smul_comm, lvl_smul])
    (fun x y y' => ext2 fun n k => by
      simp only [ofZ, omZ, c2_mk2, c2_add, Submodule.coe_add, map_add, LinearMap.comp_add,
        mul_add, lvl_add])
    (fun a x y => ext2 fun n k => by
      simp only [ofZ, omZ, c2_mk2, c2_smul, Submodule.coe_smul, map_smul, LinearMap.comp_smul,
        mul_smul_comm, lvl_smul])

/-- The zero-mode insertion `Tr o(c) Y₁(x) Y₂(y) q^{L₀}` as a bilinear series. -/
def Om (c : V) : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2 :=
  PzTensorY4.biHat fun α₁ α₂ => omPair Y₁ Y₂ c α₁ α₂

theorem Om_homog (c : V) {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) :
    Om Y₁ Y₂ c x y = ofZ (omZ Y₁ Y₂ c x y α₁ α₂) := by
  rw [Om, PzTensorY4.biHat_homog _ hx hy]
  rfl

theorem Om_add (c c' : V) (x : P₁.carrier) (y : P₂.carrier) :
    Om Y₁ Y₂ (c + c') x y = Om Y₁ Y₂ c x y + Om Y₁ Y₂ c' x y := by
  refine FusionTop.induction_weight P₁.isMod x (by simp) (fun a b ha hb => ?_) ?_
  · simp only [map_add, LinearMap.add_apply, ha, hb]; abel
  · intro α₁ x hx
    refine FusionTop.induction_weight P₂.isMod y (by simp) (fun a b ha hb => ?_) ?_
    · simp only [map_add, ha, hb]; abel
    · intro α₂ y hy
      rw [Om_homog Y₁ Y₂ _ hx hy, Om_homog Y₁ Y₂ _ hx hy, Om_homog Y₁ Y₂ _ hx hy]
      apply ext2
      intro n k
      simp only [ofZ, omZ, c2_mk2, c2_add, map_add, add_mul, lvl_add]

theorem Om_smul (a : ℂ) (c : V) (x : P₁.carrier) (y : P₂.carrier) :
    Om Y₁ Y₂ (a • c) x y = a • Om Y₁ Y₂ c x y := by
  refine FusionTop.induction_weight P₁.isMod x (by simp) (fun a b ha hb => ?_) ?_
  · simp only [map_add, LinearMap.add_apply, ha, hb, smul_add]
  · intro α₁ x hx
    refine FusionTop.induction_weight P₂.isMod y (by simp) (fun a b ha hb => ?_) ?_
    · simp only [map_add, ha, hb, smul_add]
    · intro α₂ y hy
      rw [Om_homog Y₁ Y₂ _ hx hy, Om_homog Y₁ Y₂ _ hx hy]
      apply ext2
      intro n k
      simp only [ofZ, omZ, c2_mk2, c2_smul, map_smul, smul_mul_assoc, lvl_smul]

/-- The zero-mode trace is the boundary trace at `p = kc − 1`. -/
theorem famA_zero_mode {c : V} {kc : ℤ} (hc : c ∈ W.grading kc) {α₁ α₂ : ℂ}
    {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) :
    famA Y₁ Y₂ c kc x y α₁ α₂ (kc - 1) = Om Y₁ Y₂ c x y := by
  rw [Om_homog Y₁ Y₂ c hx hy]
  apply ext2
  intro n k
  simp only [famA, ofZ, c2_mk2, AZ, omZ, oMod_of_mem_grading N.isMod hc]
  congr 4
  push_cast
  ring

end Bilinear

/-! ## Square modes as finite sums -/

theorem sqAct_eq_sum {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)
    (c : V) (k : ℕ) (m : ℤ) (w : M) (K : ℕ) (hK : ∀ j : ℤ, (K : ℤ) ≤ j → mode (A.YM c) j w = 0)
    (lo : ℤ) (hlo : lo ≤ m) :
    sqAct A c k m w = ∑ j ∈ Finset.Ico lo (K : ℤ), sqBracketCoeffZ k m j • mode (A.YM c) j w := by
  rw [GenusOne.sqAct_apply]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj
  simp only [Finset.coe_Ico, Set.mem_Ico]
  constructor
  · by_contra h
    exact hj (by rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul])
  · by_contra h
    exact hj (by rw [hK j (by omega), smul_zero])

/-- Nonnegative square modes use only nonnegative ordinary modes. -/
theorem sqAct_nonneg_eq {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)
    (c : V) (k m : ℕ) (w : M) (K : ℕ) (hK : ∀ j : ℤ, (K : ℤ) ≤ j → mode (A.YM c) j w = 0) :
    sqAct A c k m w = ∑ j ∈ Finset.range K, sqBracketCoeff k m j • mode (A.YM c) j w := by
  rw [sqAct_eq_sum A c k m w K hK 0 (by omega)]
  rw [show Finset.range K = Finset.image (fun j : ℤ => j.toNat) (Finset.Ico 0 (K : ℤ)) by
    ext j; simp only [Finset.mem_range, Finset.mem_image, Finset.mem_Ico]
    constructor
    · intro h; exact ⟨j, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega]
  rw [Finset.sum_image (fun a ha b hb h => by
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb; omega)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [← sqBracketCoeffZ_of_nonneg, show ((j.toNat : ℕ) : ℤ) = j by omega]

/-- The minus-one square mode: the diagonal term plus nonnegative modes. -/
theorem sqAct_neg_one_eq {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)
    (c : V) (k : ℕ) (w : M) (K : ℕ) (hK : ∀ j : ℤ, (K : ℤ) ≤ j → mode (A.YM c) j w = 0) :
    sqAct A c k (-1) w = mode (A.YM c) (-1) w +
      ∑ j ∈ Finset.range K, sqBracketCoeffZ k (-1) j • mode (A.YM c) j w := by
  rw [sqAct_eq_sum A c k (-1) w K hK (-1) le_rfl]
  rw [show Finset.Ico (-1 : ℤ) K = insert (-1) (Finset.Ico 0 (K : ℤ)) by
    ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega]
  rw [Finset.sum_insert (by simp), sqBracketCoeffZ_neg_one_diag, one_smul]
  congr 1
  rw [show Finset.range K = Finset.image (fun j : ℤ => j.toNat) (Finset.Ico 0 (K : ℤ)) by
    ext j; simp only [Finset.mem_range, Finset.mem_image, Finset.mem_Ico]
    constructor
    · intro h; exact ⟨j, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega]
  rw [Finset.sum_image (fun a ha b hb h => by
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb; omega)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [show ((j.toNat : ℕ) : ℤ) = j by omega]

end VOA.Huang.GenusOneWard
