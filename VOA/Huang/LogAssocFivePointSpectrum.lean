import VOA.Huang.LogAssocFivePointEvaluation
import VOA.Huang.LogAssocLowerSpectrum

/-! The two weights in every genuine logarithmic pentagon expansion lie in
finite actual lower spectral progressions. True point blocks force this
support statement without any ordinary-module or convergence assumption. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 2000000
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogModuleCat
open VOA.Huang.LogAssocExpansion VOA.Huang.LogHuangODEProduct
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- Actual first internal tensor object for each genuine pentagon shape. -/
def fivePointFirstObject (N P Q R : LogModuleCat W) : FiveTree → LogModuleCat W
  | .left | .pair => tensorObject hC2 N P
  | .inner | .middle => tensorObject hC2 P Q
  | .right => tensorObject hC2 Q R

/-- Actual second internal tensor object for each genuine pentagon shape. -/
def fivePointSecondObject (N P Q R : LogModuleCat W) : FiveTree → LogModuleCat W
  | .left => tensorObject hC2 (tensorObject hC2 N P) Q
  | .inner => tensorObject hC2 N (tensorObject hC2 P Q)
  | .middle => tensorObject hC2 (tensorObject hC2 P Q) R
  | .right => tensorObject hC2 P (tensorObject hC2 Q R)
  | .pair => tensorObject hC2 Q R

private theorem weight_subtype_zero_of_bot {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) {γ : ℂ} (h : N.weight γ=⊥) (x : N.weight γ) : x=0 := by
  apply Subtype.ext
  have hx : (x : M)∈(⊥ : Submodule ℂ M) := h ▸ x.2
  exact (Submodule.mem_bot ℂ).mp hx

private theorem pointTensorBlock_zero_first (N P : LogModuleCat W) (ell a b c : ℂ)
    (y : P.act.weight b) : pointTensorBlock hC2 N P ell a b c 0 y=0 :=
  LinearMap.map_zero₂ _ y

private theorem pointTensorBlock_zero_second (N P : LogModuleCat W) (ell a b c : ℂ)
    (x : N.act.weight a) : pointTensorBlock hC2 N P ell a b c x 0=0 :=
  map_zero _

/-- A zero first internal weight space kills the literal all-log point term. -/
theorem fivePointTerm_zero_first_of_weight_bot (N P Q R : LogModuleCat W) (tree : FiveTree)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R tree →ₗ[ℂ] ℂ) (γ δ : ℂ)
    (hbot : (fivePointFirstObject hC2 N P Q R tree).act.weight γ=⊥) :
    fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f γ δ=0 := by
  have h0 := weight_subtype_zero_of_bot (fivePointFirstObject hC2 N P Q R tree).act hbot
  cases tree with
  | left =>
      let T := tensorObject hC2 N P
      let L := tensorObject hC2 T Q
      let u := pointTensor hC2 N P (Complex.log r) x y γ
      let B := pointTensorBlock hC2 T Q (Complex.log s) γ c δ
      let A := pointTensorBlock hC2 L R 0 δ d β
      change f ((A (B u z) w : (tensorObject hC2 L R).carrier))=0
      have hu : u=0 := h0 u
      have hv : B u z=0 := (congrArg (fun q => B q z) hu).trans (LinearMap.map_zero₂ B z)
      have ho : A (B u z) w=0 := (congrArg (fun q => A q w) hv).trans (LinearMap.map_zero₂ A w)
      have hh := congrArg (fun q : (tensorObject hC2 L R).act.weight β => f (q : (tensorObject hC2 L R).carrier)) ho
      have hh' := hh.trans (f.map_zero)
      simpa only [Submodule.coe_zero] using hh'
  | inner =>
      let T := tensorObject hC2 P Q
      let L := tensorObject hC2 N T
      let u := pointTensor hC2 P Q (Complex.log s) y z γ
      let B := pointTensorBlock hC2 N T (Complex.log (s+r)) a γ δ
      let A := pointTensorBlock hC2 L R 0 δ d β
      change f ((A (B x u) w : (tensorObject hC2 L R).carrier))=0
      have hu : u=0 := h0 u
      have hv : B x u=0 := (congrArg (B x) hu).trans (map_zero _)
      have ho : A (B x u) w=0 := (congrArg (fun q => A q w) hv).trans (LinearMap.map_zero₂ A w)
      have hh := congrArg (fun q : (tensorObject hC2 L R).act.weight β => f (q : (tensorObject hC2 L R).carrier)) ho
      have hh' := hh.trans (f.map_zero)
      simpa only [Submodule.coe_zero] using hh'
  | middle =>
      let T := tensorObject hC2 P Q
      let L := tensorObject hC2 T R
      let u := pointTensor hC2 P Q (Complex.log s) y z γ
      let B := pointTensorBlock hC2 T R 0 γ d δ
      let A := pointTensorBlock hC2 N L (Complex.log (1+s+r)) a δ β
      change f ((A x (B u w) : (tensorObject hC2 N L).carrier))=0
      have hu : u=0 := h0 u
      have hv : B u w=0 := (congrArg (fun q => B q w) hu).trans (LinearMap.map_zero₂ B w)
      have ho : A x (B u w)=0 := (congrArg (A x) hv).trans (map_zero _)
      have hh := congrArg (fun q : (tensorObject hC2 N L).act.weight β => f (q : (tensorObject hC2 N L).carrier)) ho
      have hh' := hh.trans (f.map_zero)
      simpa only [Submodule.coe_zero] using hh'
  | right =>
      let T := tensorObject hC2 Q R
      let L := tensorObject hC2 P T
      let u := pointTensor hC2 Q R 0 z w γ
      let B := pointTensorBlock hC2 P T (Complex.log (1+s)) b γ δ
      let A := pointTensorBlock hC2 N L (Complex.log (1+s+r)) a δ β
      change f ((A x (B y u) : (tensorObject hC2 N L).carrier))=0
      have hu : u=0 := h0 u
      have hv : B y u=0 := (congrArg (B y) hu).trans (map_zero _)
      have ho : A x (B y u)=0 := (congrArg (A x) hv).trans (map_zero _)
      have hh := congrArg (fun q : (tensorObject hC2 N L).act.weight β => f (q : (tensorObject hC2 N L).carrier)) ho
      have hh' := hh.trans (f.map_zero)
      simpa only [Submodule.coe_zero] using hh'
  | pair =>
      let T := tensorObject hC2 N P
      let L := tensorObject hC2 Q R
      let u := pointTensor hC2 N P (Complex.log r) x y γ
      let v := pointTensor hC2 Q R 0 z w δ
      let A := pointTensorBlock hC2 T L (Complex.log (1+s)) γ δ β
      change f ((A u v : (tensorObject hC2 T L).carrier))=0
      have hu : u=0 := h0 u
      have ho : A u v=0 := (congrArg (fun q => A q v) hu).trans (LinearMap.map_zero₂ A v)
      have hh := congrArg (fun q : (tensorObject hC2 T L).act.weight β => f (q : (tensorObject hC2 T L).carrier)) ho
      have hh' := hh.trans (f.map_zero)
      simpa only [Submodule.coe_zero] using hh'

/-- A zero second internal weight space kills the literal all-log point term. -/
theorem fivePointTerm_zero_second_of_weight_bot (N P Q R : LogModuleCat W) (tree : FiveTree)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R tree →ₗ[ℂ] ℂ) (γ δ : ℂ)
    (hbot : (fivePointSecondObject hC2 N P Q R tree).act.weight δ=⊥) :
    fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f γ δ=0 := by
  have h0 := weight_subtype_zero_of_bot (fivePointSecondObject hC2 N P Q R tree).act hbot
  cases tree with
  | left =>
      let T := tensorObject hC2 N P
      let L := tensorObject hC2 T Q
      let u := pointTensor hC2 N P (Complex.log r) x y γ
      let B := pointTensorBlock hC2 T Q (Complex.log s) γ c δ
      let A := pointTensorBlock hC2 L R 0 δ d β
      change f ((A (B u z) w : (tensorObject hC2 L R).carrier))=0
      have hv : B u z=0 := h0 (B u z)
      have ho : A (B u z) w=0 := (congrArg (fun q => A q w) hv).trans (LinearMap.map_zero₂ A w)
      have hh := congrArg (fun q : (tensorObject hC2 L R).act.weight β => f (q : (tensorObject hC2 L R).carrier)) ho
      have hh' := hh.trans (f.map_zero)
      simpa only [Submodule.coe_zero] using hh'
  | inner =>
      let T := tensorObject hC2 P Q
      let L := tensorObject hC2 N T
      let u := pointTensor hC2 P Q (Complex.log s) y z γ
      let B := pointTensorBlock hC2 N T (Complex.log (s+r)) a γ δ
      let A := pointTensorBlock hC2 L R 0 δ d β
      change f ((A (B x u) w : (tensorObject hC2 L R).carrier))=0
      have hv : B x u=0 := h0 (B x u)
      have ho : A (B x u) w=0 := (congrArg (fun q => A q w) hv).trans (LinearMap.map_zero₂ A w)
      have hh := congrArg (fun q : (tensorObject hC2 L R).act.weight β => f (q : (tensorObject hC2 L R).carrier)) ho
      have hh' := hh.trans (f.map_zero)
      simpa only [Submodule.coe_zero] using hh'
  | middle =>
      let T := tensorObject hC2 P Q
      let L := tensorObject hC2 T R
      let u := pointTensor hC2 P Q (Complex.log s) y z γ
      let B := pointTensorBlock hC2 T R 0 γ d δ
      let A := pointTensorBlock hC2 N L (Complex.log (1+s+r)) a δ β
      change f ((A x (B u w) : (tensorObject hC2 N L).carrier))=0
      have hv : B u w=0 := h0 (B u w)
      have ho : A x (B u w)=0 := (congrArg (A x) hv).trans (map_zero _)
      have hh := congrArg (fun q : (tensorObject hC2 N L).act.weight β => f (q : (tensorObject hC2 N L).carrier)) ho
      have hh' := hh.trans (f.map_zero)
      simpa only [Submodule.coe_zero] using hh'
  | right =>
      let T := tensorObject hC2 Q R
      let L := tensorObject hC2 P T
      let u := pointTensor hC2 Q R 0 z w γ
      let B := pointTensorBlock hC2 P T (Complex.log (1+s)) b γ δ
      let A := pointTensorBlock hC2 N L (Complex.log (1+s+r)) a δ β
      change f ((A x (B y u) : (tensorObject hC2 N L).carrier))=0
      have hv : B y u=0 := h0 (B y u)
      have ho : A x (B y u)=0 := (congrArg (A x) hv).trans (map_zero _)
      have hh := congrArg (fun q : (tensorObject hC2 N L).act.weight β => f (q : (tensorObject hC2 N L).carrier)) ho
      have hh' := hh.trans (f.map_zero)
      simpa only [Submodule.coe_zero] using hh'
  | pair =>
      let T := tensorObject hC2 N P
      let L := tensorObject hC2 Q R
      let u := pointTensor hC2 N P (Complex.log r) x y γ
      let v := pointTensor hC2 Q R 0 z w δ
      let A := pointTensorBlock hC2 T L (Complex.log (1+s)) γ δ β
      change f ((A u v : (tensorObject hC2 T L).carrier))=0
      have hv : v=0 := h0 (v)
      have ho : A u v=0 := (congrArg (A u) hv).trans (map_zero _)
      have hh := congrArg (fun q : (tensorObject hC2 T L).act.weight β => f (q : (tensorObject hC2 T L).carrier)) ho
      have hh' := hh.trans (f.map_zero)
      simpa only [Submodule.coe_zero] using hh'

/-- Every nonzero true term requires both genuine internal weight spaces. -/
theorem fivePointTerm_weight_support (N P Q R : LogModuleCat W) (tree : FiveTree)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R tree →ₗ[ℂ] ℂ) (γ δ : ℂ)
    (hne : fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f γ δ≠0) :
    (fivePointFirstObject hC2 N P Q R tree).act.weight γ≠⊥ ∧
      (fivePointSecondObject hC2 N P Q R tree).act.weight δ≠⊥ := by
  constructor
  · intro hbot
    exact hne (fivePointTerm_zero_first_of_weight_bot hC2 N P Q R tree a b c d β x y z w r s f γ δ hbot)
  · intro hbot
    exact hne (fivePointTerm_zero_second_of_weight_bot hC2 N P Q R tree a b c d β x y z w r s f γ δ hbot)

/-- Every true generalized weight in a finitely generated C2 module has
one actual nonnegative natural level above a proved spectral lower base. -/
theorem exists_lowerSpectrum_weight {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) (hfg : FinGen N.toWeakModule) (γ : ℂ) (hne : N.weight γ≠⊥) :
    ∃ mu∈spectrumCosets hC2 N hfg,∃ n : ℕ,γ=lowerSpectrumRep hC2 N hfg mu+n := by
  obtain ⟨mu,hmu,d,hd⟩ := exists_spectrumCoset_weight hC2 N hfg γ hne
  obtain ⟨⟨K,hK⟩,hL⟩ := lowerSpectrumRep_spec hC2 N hfg mu
  have he : γ=lowerSpectrumRep hC2 N hfg mu+((K : ℤ)+d : ℤ) := by
    rw [hd,hK]
    push_cast
    ring
  have hn : 0≤(K : ℤ)+d := by
    by_contra hn
    have hh := hL ((K : ℤ)+d) (by omega)
    rw [← he] at hh
    exact hne hh
  refine ⟨mu,hmu,((K : ℤ)+d).toNat,?_⟩
  rw [he]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hn).symm

/-- The actual generalized spectrum has a finite honest natural-progression cover. -/
theorem finite_lower_weight_spectrum (hC2 : C2Cofinite W) (N : LogModuleCat W) :
    ∃ S : Finset ℂ,∀ γ,N.act.weight γ≠⊥ → ∃ h∈S,∃ n : ℕ,γ=h+n := by
  classical
  let S := (spectrumCosets hC2 N.act N.finiteGeneration).image
    (lowerSpectrumRep hC2 N.act N.finiteGeneration)
  refine ⟨S,fun γ hγ => ?_⟩
  obtain ⟨mu,hmu,n,hn⟩ := exists_lowerSpectrum_weight hC2 N.act N.finiteGeneration γ hγ
  exact ⟨_,Finset.mem_image_of_mem _ hmu,n,hn⟩

/-- Every actual logarithmic five-point array has a finite rectangular
spectral cover, with every live weight accounted for by its actual module. -/
theorem fivePoint_finite_spectral_cover (N P Q R : LogModuleCat W) (tree : FiveTree)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R tree →ₗ[ℂ] ℂ) :
    ∃ S T : Finset ℂ,∀ γ δ,
      fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f γ δ≠0 →
      ∃ h∈S,∃ h'∈T,∃ m n : ℕ,γ=h+m ∧ δ=h'+n := by
  obtain ⟨S,hS⟩ := finite_lower_weight_spectrum hC2 (fivePointFirstObject hC2 N P Q R tree)
  obtain ⟨T,hT⟩ := finite_lower_weight_spectrum hC2 (fivePointSecondObject hC2 N P Q R tree)
  refine ⟨S,T,fun γ δ hγδ => ?_⟩
  obtain ⟨hγ,hδ⟩ := fivePointTerm_weight_support hC2 N P Q R tree a b c d β x y z w r s f γ δ hγδ
  obtain ⟨h,hh,m,hm⟩ := hS γ hγ
  obtain ⟨h',hh',n,hn⟩ := hT δ hδ
  exact ⟨h,hh,h',hh',m,n,hm,hn⟩

end VOA.Huang.LogAssocFivePoint
