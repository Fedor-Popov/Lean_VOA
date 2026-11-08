import VOA.Moonshine.MoonshineCNLatticeForm
import VOA.Moonshine.MoonshineCNTensorRealization
import VOA.Moonshine.SimpleForm

/-! Symmetric, normalized bilinear forms and their tensor Virasoro adjointness. -/

namespace VOA.Moonshine.ConwayNorton

open scoped TensorProduct
open Module (End)
open TensorFieldLift AutMonster SimpleNat

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

theorem nearTensorForm_virasoro_adjoint {V : NearVOA A} {W : NearVOA B}
    (F : NearInvariantForm V) (G : NearInvariantForm W) (n : ℤ) (x y : A ⊗[ℂ] B) :
    (F.form.tmul G.form) (nearVirasoroMode (nearTensorVOA V W) n x) y =
      (F.form.tmul G.form) x (nearVirasoroMode (nearTensorVOA V W) (-n) y) := by
  have he (m : ℤ) : nearVirasoroMode (nearTensorVOA V W) m =
      tensorTranslation (nearVirasoroMode V m) (nearVirasoroMode W m) :=
    nearTensorField_conformal_mode V W m
  rw [he, he]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | tmul a' b' =>
          simp only [tensorTranslation, LinearMap.add_apply, LinearMap.rTensor_tmul,
            LinearMap.lTensor_tmul, map_add, LinearMap.add_apply,
            LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, F.virasoro_adj, G.virasoro_adj]

/-- Tensoring Virasoro-adjoint forms preserves every adjointness relation. -/
noncomputable def nearTensorInvariantForm {V : NearVOA A} {W : NearVOA B}
    (F : NearInvariantForm V) (G : NearInvariantForm W) : NearInvariantForm (nearTensorVOA V W) where
  form := F.form.tmul G.form
  virasoro_adj := nearTensorForm_virasoro_adjoint F G

/-- The product of the established moonshine form with the explicit Lorentzian form. -/
noncomputable def moonshineMatterForm : LinearMap.BilinForm ℂ moonshineMatterSpace :=
  natForm.tmul lorentzianBilinearForm

theorem moonshineMatterForm_symmetric (x y : moonshineMatterSpace) :
    moonshineMatterForm x y = moonshineMatterForm y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | tmul a' b' =>
          change lorentzianBilinearForm b b' * natForm a a' =
            lorentzianBilinearForm b' b * natForm a' a
          rw [lorentzianBilinearForm_symmetric, natForm_symm]

theorem moonshineMatterForm_normalized :
    moonshineMatterForm moonshineMatterNearVOA.vacuum moonshineMatterNearVOA.vacuum = 1 := by
  change lorentzianBilinearForm lorentzianNearVOA.vacuum lorentzianNearVOA.vacuum *
    natForm VnatVOA.vacuum VnatVOA.vacuum = 1
  rw [lorentzianBilinearForm_normalized, one_mul]
  exact natInvForm_normalized vnat_twistedLocality

theorem moonshineMatterForm_virasoro_adjoint (n : ℤ) (x y : moonshineMatterSpace) :
    moonshineMatterForm (nearVirasoroMode moonshineMatterNearVOA n x) y =
      moonshineMatterForm x (nearVirasoroMode moonshineMatterNearVOA (-n) y) :=
  nearTensorForm_virasoro_adjoint
    (show NearInvariantForm VnatVOA.toNearVOA from
      ⟨natForm, natForm_virasoro_adj vnat_twistedLocality⟩)
    lorentzianInvariantForm n x y

noncomputable def moonshineMatterInvariantForm : NearInvariantForm moonshineMatterNearVOA where
  form := moonshineMatterForm
  virasoro_adj := moonshineMatterForm_virasoro_adjoint

end VOA.Moonshine.ConwayNorton
