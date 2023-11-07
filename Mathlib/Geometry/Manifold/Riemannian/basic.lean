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

def length [Metric I M] {p q : M} (γ : Path p q) :=
  ∫ t, ‖pathderiv I γ t‖

lemma length_eq_intervalIntegral [Metric I M] {p q : M} (γ : Path p q) : length I M γ =
    ∫ t in (0:ℝ)..1, if ht : t ∈ unitInterval then ‖pathderiv I γ ⟨t,ht⟩‖ else 0 := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one,←MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.set_integral_eq_subtype measurableSet_Icc,
    fun t => eq_true (Subtype.mem t),dite_true,length]

lemma length_nonneg [Metric I M] {p q : M} (γ : Path p q) : 0 ≤ length I M γ :=
  MeasureTheory.integral_nonneg (fun t => by simp)

@[simp]
lemma length_of_const [Metric I M] {p : M} : length I M (Path.refl p) = 0 := by
  simp [length,pathderiv,Path.refl]

@[simp]
lemma length_of_symm [Metric I M] {p q : M} {γ : Path p q} : length I M (Path.symm γ) = length I M γ := by
  have h : ∀ t, (if ht : t ∈ unitInterval then ‖pathderiv I γ (unitInterval.symm ⟨t,ht⟩)‖ else 0) =
      (fun t => if ht : t ∈ unitInterval then ‖pathderiv I γ ⟨t,ht⟩‖ else 0) (1-t) := fun t => by
    simp [and_comm,unitInterval.symm]
  simp_rw [length_eq_intervalIntegral,Path.pathderiv_of_symm,norm_neg,h,
    intervalIntegral.integral_comp_sub_left (fun t => if ht : t ∈ unitInterval then ‖pathderiv I γ ⟨t,ht⟩‖ else 0) 1,
    sub_self,sub_zero]

lemma length_of_trans [Metric I M] {p p' p'' : M} (γ : Path p p') (γ' : Path p' p'') :
    length I M (γ.trans γ') = length I M γ + length I M γ' := by
  sorry

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
