import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.PathDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.MeasureSpace

open scoped Classical Manifold RealInnerProductSpace Uniformity

universe u_1 u_2 uE uM

noncomputable section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (I : ModelWithCorners ℝ E E) [I.Boundaryless]
  (M : Type uM) [TopologicalSpace M] [ChartedSpace E M] [SmoothManifoldWithCorners I M]

class PseudoMetric extends SmoothManifoldWithCorners I M where
  metric: SmoothSection I (E →L[ℝ] (E →L[ℝ] ℝ)) (Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentSpace I : M → Type uE) (Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentSpace I : M → Type uE) (Bundle.Trivial M ℝ)))

class PseudoRiemannianManifold extends PseudoMetric I M where
  metric_symm : ∀ p : M, ∀ v w : (TangentSpace I p), metric p v w = metric p w v
  metric_nondegenerate : ∀ p : M, ∀ v : (TangentSpace I p), (v ≠ 0) → metric p v ≠ 0

class Metric extends PseudoRiemannianManifold I M where
  metric_posdef : ∀ p : M, ∀ v : (TangentSpace I p), (v ≠ 0) → (0 < metric p v v)

theorem metric_nonneg [m: Metric I M] {p : M} (v : TangentSpace I p) : 0 ≤ m.metric p v v := by
  by_cases h : v=0
  simp [h]
  exact le_of_lt (m.metric_posdef p v h)

instance [iM: Metric I M] (p : M) : Inner ℝ (TangentSpace I p) :=
  ⟨fun v w => iM.metric p v w⟩

theorem tangent_inner_def [iM: Metric I M] {p : M} (v w : TangentSpace I p) :
  ⟪v,w⟫ = iM.metric p v w := rfl


instance [iM: Metric I M] (p : M) : NormedAddCommGroup (TangentSpace I p) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I p) _ _ _
    {
      toInner := inferInstance
      conj_symm := fun v w => by simp [tangent_inner_def,iM.metric_symm p w v]
      nonneg_re := fun v => metric_nonneg I M v
      definite := fun v h => by
        have h2 := mt (iM.metric_posdef p v)
        simp [h,←tangent_inner_def] at h2
        exact h2
      add_left := fun v w z => by simp [tangent_inner_def]
      smul_left := fun v w r => by simp [tangent_inner_def]
    }

instance innerProductSpace [Metric I M] (p : M) : InnerProductSpace ℝ (TangentSpace I p) :=
  InnerProductSpace.ofCore _

section Length

/-! ### Length of paths. -/

variable [Metric I M]

def length {p q : M} (γ : Path p q) :=
  ∫ t, ‖pathderiv I γ t‖

lemma length_eq_intervalIntegral {p q : M} (γ : Path p q) : length I M γ =
    ∫ t in (0:ℝ)..1, ‖pathderiv I γ (unitInterval.proj t)‖ := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one,←MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.set_integral_eq_subtype measurableSet_Icc,length]
  congr; ext t; rw [unitInterval.proj_val t]

lemma length_nonneg {p q : M} (γ : Path p q) : 0 ≤ length I M γ :=
  MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)

@[simp]
lemma length_of_const {p : M} : length I M (Path.refl p) = 0 := by
  simp [length,pathderiv,Path.refl]

@[simp]
lemma length_of_symm {p q : M} {γ : Path p q} : length I M (Path.symm γ) = length I M γ := by
  simp_rw [length_eq_intervalIntegral,Path.pathderiv_of_symm,norm_neg]
  have h' := sub_zero (1 : ℝ) ▸ sub_self (1 : ℝ) ▸ intervalIntegral.integral_comp_sub_left
    (a := 0) (b := 1) (fun x => ‖pathderiv I γ (unitInterval.proj x)‖) 1
  convert h' using 2; ext x
  rw [Path.coe_symm,Function.comp_apply,fun t => unitInterval.symm_proj t]

lemma length_of_trans [Metric I M] {p p' p'' : M} (γ : Path p p') (γ' : Path p' p'')
    (h₁ : IntervalIntegrable (fun t => ‖pathderiv I (γ.trans γ') (unitInterval.proj t)‖)
      MeasureTheory.volume 0 (1 / 2))
    (h₂ : IntervalIntegrable (fun t => ‖pathderiv I (γ.trans γ') (unitInterval.proj t)‖)
      MeasureTheory.volume (1 / 2) 1) :
    length I M (γ.trans γ') = length I M γ + length I M γ' := by
  rw [length_eq_intervalIntegral,←intervalIntegral.integral_add_adjacent_intervals h₁ h₂]
  congr
  rw [←zero_div 2]
  rw [←intervalIntegral.inv_smul_integral_comp_div,smul_eq_mul,←intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_of_le zero_le_one,MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.set_integral_congr measurableSet_Ioo (g := fun t => ‖pathderiv I γ
    (unitInterval.proj t)‖) _]
  rw [←MeasureTheory.integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le zero_le_one,
    length_eq_intervalIntegral]
  intro t ⟨ht,ht'⟩; simp only
  rw [Path.trans_pathderiv_left I γ γ' _,←unitInterval.half_proj ⟨ht.le,ht'.le⟩,
    unitInterval.double_half _,←Function.comp_apply (f := γ.trans γ'),Path.trans_comp_half]
  simp [norm_smul]
  simp [-one_div,unitInterval.proj,Set.projIcc,one_half_pos,div_lt_div_of_lt two_pos ht']
  rw [←zero_add (1 / 2),←zero_div 2]
  nth_rewrite 2 [←add_halves' 1]
  rw [←intervalIntegral.inv_smul_integral_comp_div_add,smul_eq_mul,
    ←intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.set_integral_congr measurableSet_Ioc (g := fun t => ‖pathderiv I γ'
      (unitInterval.proj t)‖) _,
    ←intervalIntegral.integral_of_le zero_le_one,length_eq_intervalIntegral]
  intro t ⟨ht,ht'⟩; simp only
  rw [Path.trans_pathderiv_right I γ γ' _,div_add_div_same,←unitInterval.half'_proj ⟨ht.le,ht'⟩,
    unitInterval.double'_half',←Function.comp_apply (f := γ.trans γ'),Path.trans_comp_half']
  simp [norm_smul]
  simp [-one_div,unitInterval.proj,Set.projIcc,half_pos ht]

end Length

class RiemannianManifold extends Metric I M where
  edist : M → M → ENNReal-- := fun p q => ⨅ (γ : Path p q) (hγ : Smooth (𝓡∂ 1) I γ), ENNReal.some ⟨length I M γ,length_nonneg I M γ⟩
  edist_metric : ∀ p q, edist p q = ⨅ (γ : Path p q) (hγ : Smooth (𝓡∂ 1) I γ), ENNReal.some ⟨length I M γ,length_nonneg I M γ⟩
  toUniformSpace : UniformSpace M
  uniformity_edist : 𝓤 M = ⨅ ε > 0, Filter.principal { p : M × M | edist p.1 p.2 < ε }

def RiemannianManifold.toEMetricSpace [iM : RiemannianManifold I M] : EMetricSpace M where
  edist p q := iM.edist p q
  edist_self p := by
    change iM.edist p p = 0
    rw [iM.edist_metric p p,←le_zero_iff]
    apply sInf_le_of_le; use Path.refl p
    apply sInf_le_of_le; use smooth_const
    have h : ⟨0,Eq.ge rfl⟩=(0:NNReal) := by rfl
    simp [h]
  edist_comm p q := by
    simp
    rw [iM.edist_metric p q,iM.edist_metric q p]
    sorry
  edist_triangle := by sorry
  eq_of_edist_eq_zero := by sorry

#check Equiv.iInf_congr
