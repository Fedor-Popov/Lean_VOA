import VOA.Huang.TensorCatSkewUnit

/-! # The braiding isomorphisms of the fusion product

For an admissible phase `c` (`c (n+1) = -c n`, `c n ≠ 0`), skew-symmetry
`Ω_c(𝒴)(w₂, x) w₁ = e^{x L(-1)} 𝒴(w₁, e^{πi} x) w₂` (FHL Prop. 5.4.7, `BraidingSkew`) carries
the universal intertwiner of `Y ⊠ X` to a universal intertwiner of type `(Y ⊠ X / X Y)`.
The universal property of `X ⊠ Y` then gives a module isomorphism

`c_{X,Y} : X ⊠ Y ≅ Y ⊠ X`,   `c_{X,Y} (𝒴_{X,Y}(x, z) y) = Ω_c(𝒴_{Y,X})(x, z) y`.

Proved here, for any choice of fusion products `F` (no rationality):
* `braidingP_intertwiner` (defining equation), `braidingP_naturality` (naturality in both
  variables);
* `braidingP_inv`: the braiding for the inverse phase, with arguments exchanged, is the inverse
  (`Ω_{1/c} ∘ Ω_c = id`);
* `skewModes_skewModes_mul` and `braidingP_monodromy`: the double braiding acts on the
  coefficient `𝒴_{X,Y}(n)` by the scalar `c(n)²` — for FHL's `c(n) = e^{-πi(n+1)}` this is
  `e^{-2πi(n+1)}`, the monodromy behind the balancing axiom;
* `braiding_leftUnitor`: `c_{X,𝟙} ≫ λ_X = ρ_X` for the library's actual unitors.

The hexagon identities are not asserted here (see `BraidRibbonHexagon`).
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.BraidingSkew
open Module (End)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace BraidRibbon

/-! ## Double skew-symmetry with arbitrary phases -/

section DoubleSkew

variable {M₁ M₂ M₃ : Type*}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {L : End ℂ M₃}

/-- **`Ω_{c'} ∘ Ω_c` multiplies the `n`-th mode by `c'(n) c(n)`** (generalizes
`skewModes_skewModes`, which is the case `c' c = 1`). -/
theorem skewModes_skewModes_mul {c c' : ℂ → ℂ} (hc : ∀ n, c (n + 1) = -c n)
    {Y : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) :
    skewModes L c' (skewModes L c Y) = fun n => (c' n * c n) • Y n := by
  funext n
  refine LinearMap.ext fun w₁ => LinearMap.ext fun w₂ => ?_
  rw [skewModes_apply (trunc_skewModes c Y)]
  obtain ⟨K, hK⟩ := hY.bound w₁ w₂ n
  have hout : ∀ k : ℕ, K + 1 ≤ k → skewModes L c Y (n + k) w₂ w₁ = 0 := by
    intro k hk
    rw [skewModes_apply hY, sSum]
    rw [finsum_eq_zero_of_forall_eq_zero fun j => ?_, smul_zero]
    rw [sTerm, show n + (k : ℂ) + (j : ℂ) = n + ((k + j : ℕ) : ℂ) by push_cast; ring,
      hK _ (by omega), map_zero, smul_zero]
  rw [sSum_eq_sum (K + 1) hout]
  have hin : ∀ k : ℕ, sTerm L (skewModes L c Y) n w₂ w₁ k
      = ∑ j ∈ Finset.range (K + 1), (c n * ((k.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ j
          * (j.factorial : ℂ)⁻¹))) • (L ^ (j + k)) (Y (n + ((j + k : ℕ) : ℂ)) w₁ w₂) := by
    intro k
    rw [sTerm, skewModes_apply hY, sSum_eq_sum (K + 1) (fun j hj => by
      rw [show n + (k : ℂ) + (j : ℂ) = n + ((k + j : ℕ) : ℂ) by push_cast; ring]
      exact hK _ (by omega)), Finset.smul_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sTerm, map_smul, map_smul, smul_smul, smul_smul, ← Module.End.mul_apply, ← pow_add,
      phase_nat hc, show n + (k : ℂ) + (j : ℂ) = n + ((j + k : ℕ) : ℂ) by push_cast; ring,
      add_comm k j]
    congr 1
    simp only [sc]
    have h1 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination (c n * (k.factorial : ℂ)⁻¹ * (-1) ^ j * (j.factorial : ℂ)⁻¹) * h1
  rw [Finset.sum_congr rfl fun k _ => hin k, Finset.sum_comm]
  have htri : ∀ j ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (K + 1),
      (c n * ((k.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ j * (j.factorial : ℂ)⁻¹))) •
        (L ^ (j + k)) (Y (n + ((j + k : ℕ) : ℂ)) w₁ w₂)
      = c n • ∑ k ∈ Finset.range (K - j + 1),
          ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * (k.factorial : ℂ)⁻¹)) •
            (fun N : ℕ => (L ^ N) (Y (n + (N : ℂ)) w₁ w₂)) (k + j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.smul_sum]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : K - j + 1 ≤ K + 1))
      (fun k _ hk => by
        rw [Finset.mem_range] at hk
        rw [hK _ (by omega), map_zero, smul_zero])]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, add_comm k j]
    congr 1
    ring
  rw [Finset.sum_congr rfl htri, ← Finset.smul_sum,
    triangle_sum K (fun N : ℕ => (L ^ N) (Y (n + (N : ℂ)) w₁ w₂)), smul_smul]
  simp

end DoubleSkew

/-! ## Admissible phases -/

/-- An **admissible phase** for skew-symmetry: `c (n+1) = -c n` and `c n ≠ 0`. -/
structure Phase where
  c : ℂ → ℂ
  succ : ∀ n, c (n + 1) = -c n
  ne_zero : ∀ n, c n ≠ 0

/-- FHL's `Ω₀` phase `c n = e^{-πi(n+1)}` (`𝒴(w, e^{πi} x)`), the one used by the library's
right unitor. -/
def Phase.upper : Phase := ⟨omegaPhase, omegaPhase_succ, omegaPhase_ne_zero⟩

/-- The inverse phase `1/c` (FHL's `Ω₋₁` for `c = Ω₀`). -/
def Phase.inv (p : Phase) : Phase :=
  ⟨fun n => (p.c n)⁻¹, fun n => by simp only [p.succ n, inv_neg],
    fun n => inv_ne_zero (p.ne_zero n)⟩

theorem Phase.inv_inv (p : Phase) : p.inv.inv = p := by
  cases p; simp [Phase.inv]

/-! ## Skew-symmetry on intertwiners of ordinary objects -/

variable (p : Phase)

/-- Skew-symmetry with phase `p`, as a linear equivalence of intertwiner spaces. -/
def skewP (X Y Z : Ordinary W) :
    IntertwiningOperator X.isMod Y.isMod Z.isMod ≃ₗ[ℂ]
      IntertwiningOperator Y.isMod X.isMod Z.isMod :=
  skewEquiv X.isMod Y.isMod Z.isMod p.succ p.ne_zero

theorem skewP_val (X Y Z : Ordinary W) (I : IntertwiningOperator X.isMod Y.isMod Z.isMod) :
    (skewP p X Y Z I).val = skewModes Z.isMod.Lm1 p.c I.val := rfl

theorem skewP_upper (X Y Z : Ordinary W) : skewP Phase.upper X Y Z = skew X Y Z := rfl

theorem hom_Lm1_pow' {X Y : Ordinary W} (f : X ⟶ Y) (j : ℕ) (x : X.carrier) :
    f.val ((X.isMod.Lm1 ^ j) x) = (Y.isMod.Lm1 ^ j) (f.val x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [show f.val (X.isMod.Lm1 ((X.isMod.Lm1 ^ j) x)) =
      Y.isMod.Lm1 (f.val ((X.isMod.Lm1 ^ j) x)) from
        f.property W.conformalVector 0 _, ih]

/-- Skew-symmetry is natural in the output module. -/
theorem skewP_postcompose {X Y Z T : Ordinary W}
    (I : IntertwiningOperator X.isMod Y.isMod Z.isMod) (f : Z ⟶ T) :
    skewP p X Y T (postcompose I T.isMod f) =
      postcompose (skewP p X Y Z I) T.isMod f := by
  apply Subtype.ext
  funext n
  ext y x
  change skewModes T.isMod.Lm1 p.c (postcompose I T.isMod f).val n y x =
    f.val (skewModes Z.isMod.Lm1 p.c I.val n y x)
  rw [skewModes_apply (trunc_of_isIntertwining (postcompose I T.isMod f).property),
    skewModes_apply (trunc_of_isIntertwining I.property), map_smul]
  obtain ⟨K, hK⟩ := (trunc_of_isIntertwining I.property).bound x y n
  have hK' : ∀ j : ℕ, K ≤ j → (postcompose I T.isMod f).val (n + j) x y = 0 := by
    intro j hj
    simp only [postcompose_apply, hK j hj, map_zero]
  rw [sSum_eq_sum K hK', sSum_eq_sum K hK, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [sTerm, postcompose_apply, map_smul, hom_Lm1_pow']

/-- Skew-symmetry exchanges the two input maps. -/
theorem skewP_restrictInputs {X X' Y Y' Z : Ordinary W}
    (I : IntertwiningOperator X'.isMod Y'.isMod Z.isMod)
    (f : X ⟶ X') (g : Y ⟶ Y') :
    skewP p X Y Z (restrictInputs f g I) = restrictInputs g f (skewP p X' Y' Z I) := by
  apply Subtype.ext
  funext n
  ext y x
  change skewModes Z.isMod.Lm1 p.c (restrictInputs f g I).val n y x =
    skewModes Z.isMod.Lm1 p.c I.val n (g.val y) (f.val x)
  rw [skewModes_apply (trunc_of_isIntertwining (restrictInputs f g I).property),
    skewModes_apply (trunc_of_isIntertwining I.property)]
  rfl

/-- Skew-symmetry with inverse phases is involutive. -/
theorem skewP_inv_skewP (X Y Z : Ordinary W) (I : IntertwiningOperator X.isMod Y.isMod Z.isMod) :
    skewP p.inv Y X Z (skewP p X Y Z I) = I := by
  apply Subtype.ext
  change skewModes Z.isMod.Lm1 p.inv.c (skewModes Z.isMod.Lm1 p.c I.val) = I.val
  exact skewModes_skewModes p.succ (fun n => inv_mul_cancel₀ (p.ne_zero n))
    (trunc_of_isIntertwining I.property)

/-- Skew-symmetry with inverse phases is involutive (other order). -/
theorem skewP_skewP_inv (X Y Z : Ordinary W) (I : IntertwiningOperator X.isMod Y.isMod Z.isMod) :
    skewP p Y X Z (skewP p.inv X Y Z I) = I := by
  apply Subtype.ext
  change skewModes Z.isMod.Lm1 p.c (skewModes Z.isMod.Lm1 p.inv.c I.val) = I.val
  exact skewModes_skewModes p.inv.succ (fun n => mul_inv_cancel₀ (p.ne_zero n))
    (trunc_of_isIntertwining I.property)

/-- Double skew-symmetry with the same phase multiplies the `n`-th mode by `c(n)²`. -/
theorem skewP_skewP_val (X Y Z : Ordinary W) (I : IntertwiningOperator X.isMod Y.isMod Z.isMod)
    (n : ℂ) (x : X.carrier) (y : Y.carrier) :
    (skewP p Y X Z (skewP p X Y Z I)).val n x y = (p.c n * p.c n) • I.val n x y := by
  change skewModes Z.isMod.Lm1 p.c (skewModes Z.isMod.Lm1 p.c I.val) n x y = _
  rw [skewModes_skewModes_mul p.succ (trunc_of_isIntertwining I.property)]
  rfl

/-- Swapping the inputs of a universal intertwiner preserves universality. -/
theorem skewP_isUniversal {X Y Z : Ordinary W}
    (I : IntertwiningOperator X.isMod Y.isMod Z.isMod) (hI : IsUniversal I) :
    IsUniversal (skewP p X Y Z I) := by
  intro N _ _ AN
  have he : postcompose (skewP p X Y Z I) AN =
      (skewP p X Y (Ordinary.of AN)).toLinearMap.comp (postcompose I AN) := by
    ext f n x y
    exact congrArg (fun J : IntertwiningOperator Y.isMod X.isMod AN => J.val n x y)
      (skewP_postcompose p (X := X) (Y := Y) (Z := Z) (T := Ordinary.of AN) I f).symm
  unfold UniversalFor
  rw [he]
  exact (skewP p X Y (Ordinary.of AN)).bijective.comp (hI N AN)

/-- A representing product with the inputs swapped by skew-symmetry with phase `p`. -/
def swappedProductP {X Y : Ordinary W} (P : Product X.isMod Y.isMod) :
    Product Y.isMod X.isMod where
  carrier := P.carrier
  isMod := P.isMod
  intertwiner := skewP p X Y (Ordinary.ofProduct P) P.intertwiner
  universal := skewP_isUniversal p (X := X) (Y := Y) (Z := Ordinary.ofProduct P)
    P.intertwiner P.universal

/-! ## The braiding -/

variable (F : FusionChoice W)

/-- **The braiding** `c_{X,Y} : X ⊠ Y ≅ Y ⊠ X` with phase `p`:
`c_{X,Y}(𝒴_{X,Y}(x, z) y) = Ω_p(𝒴_{Y,X})(x, z) y`. -/
def braidingP (X Y : Ordinary W) : tensorObj F X Y ≅ tensorObj F Y X :=
  Ordinary.isoOfModuleEquiv (productIso (F X Y) (swappedProductP p (F Y X)))

/-- The defining equation of the braiding on universal coefficients. -/
@[simp] theorem braidingP_intertwiner (X Y : Ordinary W) (n : ℂ) (x : X.carrier)
    (y : Y.carrier) :
    (braidingP p F X Y).hom.val ((F X Y).intertwiner.val n x y) =
      (skewP p Y X (tensorObj F Y X) (F Y X).intertwiner).val n x y :=
  productIso_intertwiner (F X Y) (swappedProductP p (F Y X)) n x y

/-- The defining equation as an identity of intertwining operators. -/
theorem postcompose_braidingP (X Y : Ordinary W) :
    postcompose (F X Y).intertwiner (tensorObj F Y X).isMod (braidingP p F X Y).hom =
      skewP p Y X (tensorObj F Y X) (F Y X).intertwiner := by
  apply Subtype.ext
  funext n
  ext x y
  exact braidingP_intertwiner p F X Y n x y

/-- Composition with the braiding, on universal coefficients. -/
theorem postcompose_braidingP_comp {X Y T : Ordinary W} (g : tensorObj F Y X ⟶ T) :
    postcompose (F X Y).intertwiner T.isMod ((braidingP p F X Y).hom ≫ g) =
      skewP p Y X T (postcompose (F Y X).intertwiner T.isMod g) := by
  erw [skewP_postcompose, ← postcompose_braidingP]
  rfl

theorem postcompose_tensorHom {X X' Y Y' : Ordinary W} (f : X ⟶ X') (g : Y ⟶ Y') :
    postcompose (F X Y).intertwiner (tensorObj F X' Y').isMod (tensorHom F f g) =
      restrictInputs f g (F X' Y').intertwiner := by
  apply Subtype.ext
  funext n
  ext x y
  exact tensorHom_intertwiner F f g n x y

/-- **Naturality of the braiding** in both variables. -/
theorem braidingP_naturality {X X' Y Y' : Ordinary W} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom F f g ≫ (braidingP p F X' Y').hom =
      (braidingP p F X Y).hom ≫ tensorHom F g f := by
  apply tensor_hom_ext F
  intro n x y
  simp only [Ordinary.comp_apply, tensorHom_intertwiner, braidingP_intertwiner]
  have h1 := skewP_postcompose p (X := Y) (Y := X) (Z := tensorObj F Y X)
    (T := tensorObj F Y' X') (F Y X).intertwiner (tensorHom F g f)
  erw [postcompose_tensorHom, skewP_restrictInputs] at h1
  exact (congrArg (fun J : IntertwiningOperator X.isMod Y.isMod (tensorObj F Y' X').isMod =>
    J.val n x y) h1)

/-- The braiding for the inverse phase, with the arguments exchanged, is the inverse. -/
theorem braidingP_hom_inv_hom (X Y : Ordinary W) :
    (braidingP p F X Y).hom ≫ (braidingP p.inv F Y X).hom = 𝟙 _ := by
  apply tensor_hom_ext F
  intro n x y
  simp only [Ordinary.comp_apply, braidingP_intertwiner, Ordinary.id_apply]
  have h := skewP_postcompose p (X := Y) (Y := X) (Z := tensorObj F Y X)
    (T := tensorObj F X Y) (F Y X).intertwiner (braidingP p.inv F Y X).hom
  erw [postcompose_braidingP, skewP_skewP_inv] at h
  have h' := congrArg (fun J : IntertwiningOperator X.isMod Y.isMod (tensorObj F X Y).isMod =>
    J.val n x y) h
  exact h'.symm

/-- `c^{1/p}_{Y,X} = (c^p_{X,Y})⁻¹`. -/
theorem braidingP_inv (X Y : Ordinary W) :
    (braidingP p.inv F Y X).hom = (braidingP p F X Y).inv :=
  (Iso.inv_ext (braidingP_hom_inv_hom p F X Y)).symm

/-- **Monodromy**: the double braiding multiplies the coefficient `𝒴_{X,Y}(n)` by `c(n)²`. -/
theorem braidingP_monodromy (X Y : Ordinary W) (n : ℂ) (x : X.carrier) (y : Y.carrier) :
    ((braidingP p F X Y).hom ≫ (braidingP p F Y X).hom).val ((F X Y).intertwiner.val n x y) =
      (p.c n * p.c n) • (F X Y).intertwiner.val n x y := by
  simp only [Ordinary.comp_apply, braidingP_intertwiner]
  have h := skewP_postcompose p (X := Y) (Y := X) (Z := tensorObj F Y X)
    (T := tensorObj F X Y) (F Y X).intertwiner (braidingP p F Y X).hom
  erw [postcompose_braidingP] at h
  have h' := congrArg (fun J : IntertwiningOperator X.isMod Y.isMod (tensorObj F X Y).isMod =>
    J.val n x y) h
  simp only [postcompose_apply] at h'
  rw [← h', skewP_skewP_val]
  rfl

/-- The braiding with FHL's phase `Ω₀`. -/
abbrev braiding (X Y : Ordinary W) : tensorObj F X Y ≅ tensorObj F Y X :=
  braidingP Phase.upper F X Y

/-- **Unit compatibility**: `c_{X,𝟙} ≫ λ_X = ρ_X` for the library's actual unitors. -/
theorem braiding_leftUnitor (X : Ordinary W) :
    (braiding F X vacuumObject).hom ≫ (leftUnitor F X).hom = (rightUnitor F X).hom := by
  apply tensor_hom_ext F
  intro n x v
  simp only [Ordinary.comp_apply, braidingP_intertwiner, rightUnitor_intertwiner]
  have h := skewP_postcompose Phase.upper (X := vacuumObject) (Y := X)
    (Z := tensorObj F vacuumObject X) (T := X) (F vacuumObject X).intertwiner
    (leftUnitor F X).hom
  have hl : postcompose (F vacuumObject X).intertwiner X.isMod (leftUnitor F X).hom =
      moduleIntertwiner X.isMod := by
    apply Subtype.ext
    funext m
    ext v' x'
    exact leftUnitor_intertwiner F X m v' x'
  erw [hl] at h
  exact (congrArg (fun J : IntertwiningOperator X.isMod (adjointModule W) X.isMod =>
    J.val n x v) h).symm

end BraidRibbon
end VOA.Huang.TensorCat
