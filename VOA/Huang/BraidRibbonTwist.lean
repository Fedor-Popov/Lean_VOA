import VOA.Huang.BraidRibbonBraiding
import VOA.Huang.FusionTop

/-! # The twist `θ = e^{2πi L(0)}` and the balancing identity

For an ordinary module the weight decomposition is internal (`OrdVModule.isInternal`), so any
function `s : ℂ → ℂ` defines the diagonal operator `x ↦ s(α) x` on `M_α` (`twistLin`).  When `s`
is `1`-periodic it commutes with every vertex-algebra mode (a homogeneous mode shifts weights by
an integer), hence is a module endomorphism.  With `s α = e^{2πiα}` this is the twist
`θ_X = e^{2πi L(0)}`.

Proved here (no rationality, any choice of fusion products):
* `twistIso X : X ≅ X`, natural (`twist_naturality`);
* `twist_balance`: `θ_{X ⊠ Y} = (θ_X ⊠ θ_Y) ≫ c_{X,Y} ≫ c_{Y,X}` for the braiding with FHL's
  phase — exactly the `balance` field of `RibbonStructure` once the braiding is installed as a
  `BraidedCategory` (the monodromy `c(n)² = e^{-2πi(n+1)}` of `braidingP_monodromy` against the
  weight `α + β - n - 1` of `𝒴(n) x y`);
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.BraidingSkew
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace BraidRibbon

/-! ## The scalar `e^{2πiα}` -/

/-- `e^{2πiα}`. -/
def tw (α : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * α)

theorem tw_ne_zero (α : ℂ) : tw α ≠ 0 := Complex.exp_ne_zero _

theorem tw_add (α β : ℂ) : tw (α + β) = tw α * tw β := by
  rw [tw, tw, tw, ← Complex.exp_add]; ring_nf

theorem tw_int (k : ℤ) : tw (k : ℂ) = 1 := by
  rw [tw, Complex.exp_eq_one_iff]
  exact ⟨k, by ring⟩

theorem tw_add_int (α : ℂ) (k : ℤ) : tw (α + k) = tw α := by
  rw [tw_add, tw_int, mul_one]

/-! ## Diagonal operators on ordinary modules -/

section Diagonal

variable {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)

/-- The weight decomposition as a linear equivalence. -/
def weightEquiv : (DirectSum ℂ fun α => A.weight α) ≃ₗ[ℂ] M :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap A.weight) A.isInternal

/-- The diagonal operator `x ↦ s(α) x` on `M_α`. -/
def twistLin (s : ℂ → ℂ) : M →ₗ[ℂ] M :=
  (DirectSum.toModule ℂ ℂ M fun α => s α • (A.weight α).subtype) ∘ₗ
    (weightEquiv A).symm.toLinearMap

theorem twistLin_of_mem (s : ℂ → ℂ) {α : ℂ} {x : M} (hx : x ∈ A.weight α) :
    twistLin A s x = s α • x := by
  have he : (weightEquiv A).symm x = DirectSum.lof ℂ ℂ (fun α => A.weight α) α ⟨x, hx⟩ := by
    apply (weightEquiv A).injective
    rw [LinearEquiv.apply_symm_apply]
    change x = DirectSum.coeLinearMap A.weight (DirectSum.of (fun i => A.weight i) α ⟨x, hx⟩)
    rw [DirectSum.coeLinearMap_of]
  simp only [twistLin, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
    DirectSum.toModule_lof, LinearMap.smul_apply, Submodule.subtype_apply]

/-- Linear maps out of an ordinary module agreeing on homogeneous vectors agree. -/
theorem linearMap_ext_homog {N : Type*} [AddCommGroup N] [Module ℂ N] (f g : M →ₗ[ℂ] N)
    (h : ∀ α x, x ∈ A.weight α → f x = g x) : f = g := by
  ext x
  have hx : x ∈ ⨆ α, A.weight α := by
    rw [A.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction A.weight (motive := fun x => f x = g x) hx
    (fun α x hx => h α x hx) (by simp) (fun a b ha hb => by simp [ha, hb])

/-- A property additive in the vector holds everywhere if it holds on homogeneous vectors. -/
theorem induction_homog {P : M → Prop} (x : M) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (h : ∀ α x, x ∈ A.weight α → P x) : P x := by
  have hx : x ∈ ⨆ α, A.weight α := by
    rw [A.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  exact Submodule.iSup_induction A.weight (motive := P) hx (fun α x hx => h α x hx) h0 hadd

theorem twistLin_comp (s t : ℂ → ℂ) :
    twistLin A s ∘ₗ twistLin A t = twistLin A (fun α => s α * t α) := by
  refine linearMap_ext_homog A _ _ fun α x hx => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, twistLin_of_mem A _ hx,
    map_smul, smul_smul]
  rw [mul_comm]

theorem twistLin_one : twistLin A (fun _ => 1) = LinearMap.id := by
  refine linearMap_ext_homog A _ _ fun α x hx => ?_
  rw [twistLin_of_mem A _ hx, one_smul, LinearMap.id_apply]

/-- A `1`-periodic diagonal operator commutes with every vertex-algebra mode. -/
theorem twistLin_mode (s : ℂ → ℂ) (hs : ∀ α (k : ℤ), s (α + k) = s α) (u : V) (n : ℤ)
    (x : M) : twistLin A s (mode (A.YM u) n x) = mode (A.YM u) n (twistLin A s x) := by
  refine induction_homog A x
    (P := fun x => twistLin A s (mode (A.YM u) n x) = mode (A.YM u) n (twistLin A s x))
    (by beta_reduce; rw [map_zero, map_zero, map_zero])
    (fun a b ha hb => by beta_reduce at ha hb ⊢; rw [map_add, map_add, map_add, map_add, ha, hb])
    fun α x hx => ?_
  have hu : u ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => twistLin A s (mode (A.YM u) n x) = mode (A.YM u) n (twistLin A s x)) hu
    (fun k u hu' => ?_) (by simp) (fun a b ha hb => by
      beta_reduce at ha hb ⊢
      simp only [map_add, mode_add, LinearMap.add_apply]
      rw [ha, hb])
  beta_reduce
  rw [twistLin_of_mem A s (mode_mem_weight A hu' hx n), twistLin_of_mem A s hx, map_smul,
    show α + (k : ℂ) - (n : ℂ) - 1 = α + ((k - n - 1 : ℤ) : ℂ) by push_cast; ring, hs]

end Diagonal

/-! ## The twist on `Ordinary W` -/

/-- The diagonal module endomorphism for a `1`-periodic `s`. -/
def diagHom (X : Ordinary W) (s : ℂ → ℂ) (hs : ∀ α (k : ℤ), s (α + k) = s α) : X ⟶ X :=
  ⟨twistLin X.isMod s, fun u n x => twistLin_mode X.isMod s hs u n x⟩

@[simp] theorem diagHom_val (X : Ordinary W) (s : ℂ → ℂ) (hs) (x : X.carrier) :
    (diagHom X s hs).val x = twistLin X.isMod s x := rfl

theorem twInv_add_int (α : ℂ) (k : ℤ) : (tw (α + k))⁻¹ = (tw α)⁻¹ := by rw [tw_add_int]

/-- **The twist** `θ_X = e^{2πi L(0)}` as an automorphism in `Ordinary W`. -/
def twistIso (X : Ordinary W) : X ≅ X where
  hom := diagHom X tw tw_add_int
  inv := diagHom X (fun α => (tw α)⁻¹) twInv_add_int
  hom_inv_id := by
    apply Subtype.ext
    change twistLin X.isMod _ ∘ₗ twistLin X.isMod tw = LinearMap.id
    rw [twistLin_comp, ← twistLin_one X.isMod]
    congr 1
    funext α
    exact inv_mul_cancel₀ (tw_ne_zero α)
  inv_hom_id := by
    apply Subtype.ext
    change twistLin X.isMod tw ∘ₗ twistLin X.isMod _ = LinearMap.id
    rw [twistLin_comp, ← twistLin_one X.isMod]
    congr 1
    funext α
    exact mul_inv_cancel₀ (tw_ne_zero α)

theorem twistIso_hom_of_mem (X : Ordinary W) {α : ℂ} {x : X.carrier} (hx : x ∈ X.isMod.weight α) :
    (twistIso X).hom.val x = tw α • x :=
  twistLin_of_mem X.isMod tw hx

/-- **Naturality of the twist.** -/
theorem twist_naturality {X Y : Ordinary W} (f : X ⟶ Y) :
    f ≫ (twistIso Y).hom = (twistIso X).hom ≫ f := by
  apply Subtype.ext
  refine linearMap_ext_homog X.isMod _ _ fun α x hx => ?_
  change (twistIso Y).hom.val (f.val x) = f.val ((twistIso X).hom.val x)
  rw [twistIso_hom_of_mem Y (hom_mem_weight f.property hx), twistIso_hom_of_mem X hx, map_smul]

variable (F : FusionChoice W)

theorem omegaPhase_sq (n : ℂ) :
    omegaPhase n * omegaPhase n = Complex.exp (-(2 * Real.pi * Complex.I) * (n + 1)) := by
  rw [omegaPhase, ← Complex.exp_add]; ring_nf

/-- Morphisms out of `X ⊠ Y` agreeing on homogeneous universal coefficients agree. -/
theorem tensor_hom_ext_homog {X Y Z : Ordinary W} (Φ Ψ : tensorObj F X Y ⟶ Z)
    (h : ∀ n α β x y, x ∈ X.isMod.weight α → y ∈ Y.isMod.weight β →
      Φ.val ((F X Y).intertwiner.val n x y) = Ψ.val ((F X Y).intertwiner.val n x y)) :
    Φ = Ψ := by
  apply tensor_hom_ext F
  intro n x y
  have hA : ∀ (x : X.carrier) β (y : Y.carrier), y ∈ Y.isMod.weight β →
      Φ.val ((F X Y).intertwiner.val n x y) = Ψ.val ((F X Y).intertwiner.val n x y) := by
    intro x β y hy
    have e := linearMap_ext_homog X.isMod
      ((Φ.val : (F X Y).carrier →ₗ[ℂ] Z.carrier) ∘ₗ ((F X Y).intertwiner.val n).flip y)
      ((Ψ.val : (F X Y).carrier →ₗ[ℂ] Z.carrier) ∘ₗ ((F X Y).intertwiner.val n).flip y)
      (fun α x hx => h n α β x y hx hy)
    exact congrArg (fun k => k x) e
  have e := linearMap_ext_homog Y.isMod
    ((Φ.val : (F X Y).carrier →ₗ[ℂ] Z.carrier) ∘ₗ ((F X Y).intertwiner.val n x))
    ((Ψ.val : (F X Y).carrier →ₗ[ℂ] Z.carrier) ∘ₗ ((F X Y).intertwiner.val n x))
    (fun β y hy => hA x β y hy)
  exact congrArg (fun k => k y) e

/-- **The balancing identity** `θ_{X⊠Y} = (θ_X ⊠ θ_Y) ≫ c_{X,Y} ≫ c_{Y,X}` for the braiding
with FHL's phase. -/
theorem twist_balance (X Y : Ordinary W) :
    (twistIso (tensorObj F X Y)).hom =
      tensorHom F (twistIso X).hom (twistIso Y).hom ≫
        (braiding F X Y).hom ≫ (braiding F Y X).hom := by
  refine tensor_hom_ext_homog F _ _ fun n α β x y hx hy => ?_
  have hmem := FusionTop.mem_weight (F X Y).intertwiner.property hx hy n
  rw [twistIso_hom_of_mem (tensorObj F X Y) hmem]
  rw [← Category.assoc, Ordinary.comp_apply, Ordinary.comp_apply, tensorHom_intertwiner,
    twistIso_hom_of_mem X hx, twistIso_hom_of_mem Y hy]
  have hm := braidingP_monodromy Phase.upper F X Y n (tw α • x) (tw β • y)
  rw [Ordinary.comp_apply] at hm
  rw [hm]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  congr 1
  change tw (α + β - n - 1) = omegaPhase n * omegaPhase n * (tw β * tw α)
  rw [omegaPhase_sq, show α + β - n - 1 = (α + β) + (-(n + 1)) by ring, tw_add, tw_add]
  rw [show tw (-(n + 1)) = Complex.exp (-(2 * Real.pi * Complex.I) * (n + 1)) by
    rw [tw]; ring_nf]
  ring

end BraidRibbon
end VOA.Huang.TensorCat
