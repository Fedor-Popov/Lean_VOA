import VOA.Classification.COne.McRaeM2LogPentagonFaithful

/-! The fixed-log arrays of the left pentagon vertex: support in finitely
many natural progressions, and absolute convergence on the common chart by
root reflection of the outer coefficient and the proved iterate-in-product
bounds. Two-scale uniqueness then shows that vanishing completed left
evaluations kill every literal nested canonical coefficient. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogModuleCat VOA.LogSkew
open VOA.C2Rigid.LocalInjective VOA.Huang.LogAssocFivePointGraded VOA.Huang.HuangODEThree
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- A bilinear map at a zero first argument, followed by a functional. -/
theorem app_zero_zero {A B C : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] (Φ : A →ₗ[ℂ] B →ₗ[ℂ] C) (g : C →ₗ[ℂ] ℂ)
    (w : B) : g (Φ 0 w)=0 := by simp

-- Actual fourfold tensor signatures require a larger elaboration budget.
set_option maxHeartbeats 4000000 in
/-- A nonzero left coefficient forces both internal weights to be live. -/
theorem leftCoeff_support (N P Q R : LogModuleCat W)
    (g : fivePointObject hC2 N P Q R .left →ₗ[ℂ] ℂ) (a b c d β : ℂ)
    {x : N} {y : P} {z : Q} (w : R) (hx : x∈N.act.weight a) (hy : y∈P.act.weight b)
    (hz : z∈Q.act.weight c) (γ δ : ℂ) (k l : ℕ)
    (hne : leftCoeff hC2 N P Q R g a b c d β x y z w γ δ k l≠0) :
    (tensorObject hC2 N P).act.weight γ≠⊥ ∧
      (tensorObject hC2 (tensorObject hC2 N P) Q).act.weight δ≠⊥ := by
  have hu : (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration).1
      (a+b-γ-1) k x y∈(tensorObject hC2 N P).act.weight γ :=
    LogFin.mem_weight_eval (tensorIntertwiner hC2 N.act P.act
      N.finiteGeneration P.finiteGeneration).2 γ k hx hy
  have hv : (tensorIntertwiner hC2 (tensorObject hC2 N P).act Q.act
      (tensorObject hC2 N P).finiteGeneration Q.finiteGeneration).1 (γ+c-δ-1) l
      ((tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration).1
        (a+b-γ-1) k x y) z∈(tensorObject hC2 (tensorObject hC2 N P) Q).act.weight δ :=
    LogFin.mem_weight_eval (tensorIntertwiner hC2 (tensorObject hC2 N P).act Q.act
      (tensorObject hC2 N P).finiteGeneration Q.finiteGeneration).2 δ l hu hz
  constructor
  · intro hbot
    apply hne
    rw [hbot] at hu
    unfold leftCoeff
    rw [(Submodule.mem_bot (M := (tensorObject hC2 N P).carrier) ℂ).mp hu]
    rw [map_zero, LinearMap.zero_apply]
    exact app_zero_zero _ g w
  · intro hbot
    apply hne
    rw [hbot] at hv
    unfold leftCoeff
    rw [(Submodule.mem_bot (M := (tensorObject hC2 (tensorObject hC2 N P) Q).carrier) ℂ).mp hv]
    rw [map_zero, LinearMap.zero_apply]
    exact g.map_zero

/-- Power algebra of the left chart along a natural progression row. -/
theorem left_chart_powers {r s : ℝ} (hr : 0<r) (hs : 0<s) (h h' A c : ℂ) (m n : ℕ) :
    (r : ℂ)^((h+(m : ℂ))-A)*((s : ℂ)^((h'+(n : ℂ))-(h+(m : ℂ))-c))=
      ((r : ℂ)^(h-A)*(s : ℂ)^(h'-h-c))*((s : ℂ)^n*((r : ℂ)/(s : ℂ))^m) := by
  have hr0 : (r : ℂ)≠0 := by exact_mod_cast hr.ne'
  have hs0 : (s : ℂ)≠0 := by exact_mod_cast hs.ne'
  rw [show (h+(m : ℂ))-A=(h-A)+(m : ℂ) by ring,
    show (h'+(n : ℂ))-(h+(m : ℂ))-c=((h'-h-c)+(n : ℂ))-(m : ℂ) by ring,
    Complex.cpow_add _ _ hr0, Complex.cpow_sub _ _ hs0, Complex.cpow_add _ _ hs0,
    Complex.cpow_natCast, Complex.cpow_natCast, Complex.cpow_natCast, div_pow]
  have hsm : (s : ℂ)^m≠0 := pow_ne_zero _ hs0
  field_simp

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 8000000 in
/-- Every fixed-log array of the left vertex converges absolutely on the
common chart. -/
theorem leftCoeff_summable (N P Q R : LogModuleCat W)
    (g : fivePointObject hC2 N P Q R .left →ₗ[ℂ] ℂ) (a b c d β : ℂ)
    (x : N.act.weight a) (y : P.act.weight b) (z : Q.act.weight c) (w : R.act.weight d)
    (r s : ℝ) (hD : FivePointDomain r s) (k l : ℕ) :
    Summable (fun p : ℂ × ℂ => (r : ℂ)^(p.1-(a+b))*((s : ℂ)^(p.2-p.1-c)*
      leftCoeff hC2 N P Q R g a b c d β x y z w p.1 p.2 k l)) := by
  classical
  let T := tensorObject hC2 N P
  let L' := tensorObject hC2 T Q
  let O := fivePointObject hC2 N P Q R .left
  let YNP := tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration
  let YTQ := tensorIntertwiner hC2 T.act Q.act T.finiteGeneration Q.finiteGeneration
  let YLR := tensorIntertwiner hC2 L'.act R.act L'.finiteGeneration R.finiteGeneration
  have hr : 0<r := hD.1
  have hs : 0<s := hD.1.trans hD.2.1
  have hs0 : (s : ℂ)≠0 := by exact_mod_cast hs.ne'
  have hnt : ‖(s : ℂ)‖=s := by simp [abs_of_pos hs]
  have hnu : ‖(r : ℂ)/(s : ℂ)‖=r/s := by
    rw [norm_div]; simp [abs_of_pos hs, abs_of_pos hr]
  have ht : ‖(s : ℂ)‖+‖(s : ℂ)‖*‖(r : ℂ)/(s : ℂ)‖<1 := by
    rw [hnt,hnu,mul_div_cancel₀ _ hs.ne']
    linarith [hD.2.2]
  have hu : ‖(r : ℂ)/(s : ℂ)‖<1 := by
    rw [hnu, div_lt_one hs]
    exact hD.2.1
  obtain ⟨J,hJ⟩ := exists_rootSkew_scalar_profiles L'.act R.act O.act YLR β
  obtain ⟨S,hS⟩ := finite_lower_weight_spectrum hC2 T
  obtain ⟨S',hS'⟩ := finite_lower_weight_spectrum hC2 L'
  let F : ℂ × ℂ → ℂ := fun p => (r : ℂ)^(p.1-(a+b))*((s : ℂ)^(p.2-p.1-c)*
      leftCoeff hC2 N P Q R g a b c d β x y z w p.1 p.2 k l)
  apply Summable.of_norm
  apply summable_norm_of_finite_cover F (S ×ˢ S') (fun i (q : ℕ × ℕ) => (i.1+q.1,i.2+q.2))
  · intro i _ p q he
    apply Prod.ext
    · have hc : (p.1 : ℂ)=(q.1 : ℂ) := add_left_cancel (congrArg Prod.fst he)
      exact_mod_cast hc
    · have hc : (p.2 : ℂ)=(q.2 : ℂ) := add_left_cancel (congrArg Prod.snd he)
      exact_mod_cast hc
  · intro p hp
    have hne : leftCoeff hC2 N P Q R g a b c d β x y z w p.1 p.2 k l≠0 :=
      right_ne_zero_of_mul (right_ne_zero_of_mul hp)
    obtain ⟨hγ,hδ⟩ := leftCoeff_support hC2 N P Q R g a b c d β w x.2 y.2 z.2 p.1 p.2 k l hne
    obtain ⟨h,hh,m,hm⟩ := hS p.1 hγ
    obtain ⟨h',hh',n,hn⟩ := hS' p.2 hδ
    exact ⟨(h,h'),Finset.mem_product.mpr ⟨hh,hh'⟩,(m,n),Prod.ext hm.symm hn.symm⟩
  · intro i _
    obtain ⟨h,h'⟩ := i
    let K₀ : ℂ := (r : ℂ)^(h-(a+b))*(s : ℂ)^(h'-h-c)
    let pc : ℕ → ℂ → ℂ → ℂ → ℂ := fun j A B C =>
      productCoeff (rootSkewIntertwiner L'.act R.act O.act YLR).1 (flipLogModes YTQ.1) YNP.1
        (g ∘ₗ Lm1 O.act.toWeakModule^j) (w : R) (z : Q) (x : N) (y : P) A B C 0 l k
    refine summable_norm_finite_sum_rows
      (F := fun q : ℕ × ℕ => F (h+q.1,h'+q.2)) J
      (fun j q => (omegaPhase 0 ((h'+q.2)+d-β-1))⁻¹*sc j)
      (fun j q => K₀*(pc j (h'+d-β-1+j+q.2) (h+c-h'-1-q.2+q.1) (a+b-h-1-q.1)*
        (s : ℂ)^q.2*((r : ℂ)/(s : ℂ))^q.1))
      (fun j => ‖(omegaPhase 0 (h'+d-β-1))⁻¹‖*‖sc j‖) ?_ ?_ ?_
    · intro j q
      simp only []
      rw [norm_mul]
      have he : h'+(q.2 : ℂ)+d-β-1=(h'+d-β-1)+(q.2 : ℂ) := by ring
      rw [he, rootSkew_phase_norm_add_nat]
    · intro j
      have hmid := summable_mid_double O.act R.act Q.act N.act P.act T.act L'.act hC2
        O.finiteGeneration R.finiteGeneration Q.finiteGeneration N.finiteGeneration
        P.finiteGeneration T.finiteGeneration L'.finiteGeneration
        (rootSkewIntertwiner L'.act R.act O.act YLR) YTQ YNP w.2 z.2 x.2 y.2
        (g ∘ₗ Lm1 O.act.toWeakModule^j) (h'+d-β-1+j) (h+c-h'-1) (a+b-h-1) 0 l k ht hu
      have hh := (hmid.comp_injective Prod.swap_injective).mul_left ‖K₀‖
      refine hh.congr fun q => ?_
      simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, norm_mul, pc]
    · intro q
      simp only [F]
      have hV : YTQ.1 ((h+(q.1 : ℂ))+c-(h'+(q.2 : ℂ))-1) l
          (YNP.1 (a+b-(h+(q.1 : ℂ))-1) k (x : N) (y : P)) (z : Q)∈L'.act.weight (h'+q.2) :=
        LogFin.mem_weight_eval YTQ.2 _ l (LogFin.mem_weight_eval YNP.2 _ k x.2 y.2) z.2
      have hcoef : leftCoeff hC2 N P Q R g a b c d β x y z w (h+q.1) (h'+q.2) k l=
          ∑ j∈Finset.range J,(omegaPhase 0 ((h'+q.2)+d-β-1))⁻¹*sc j*
            pc j (h'+d-β-1+j+q.2) (h+c-h'-1-q.2+q.1) (a+b-h-1-q.1) :=
        (hJ (h'+q.2) d _ (w : R) hV w.2 g 0).trans (Finset.sum_congr rfl fun j _ => by
          simp only [pc, productCoeff, flipLogModes, LinearMap.flip_apply]
          have e1 : h'+(q.2 : ℂ)+d-β-1+(j : ℂ)=h'+d-β-1+(j : ℂ)+(q.2 : ℂ) := by ring
          have e2 : h+(q.1 : ℂ)+c-(h'+(q.2 : ℂ))-1=h+c-h'-1-(q.2 : ℂ)+(q.1 : ℂ) := by ring
          have e3 : a+b-(h+(q.1 : ℂ))-1=a+b-h-1-(q.1 : ℂ) := by ring
          rw [e1, e2, e3]; rfl)
      rw [hcoef, ← mul_assoc, left_chart_powers hr hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

end VOA.Huang.LogAssocFivePoint
