import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open scoped Manifold

open scoped RealInnerProductSpace

universe uE uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (I : ModelWithCorners ℝ E E) [I.Boundaryless]
  (M : Type uM) [TopologicalSpace M] [ChartedSpace E M] [SmoothManifoldWithCorners I M]

class PseudoMetric extends SmoothManifoldWithCorners I M where
  metric: SmoothSection I (E →L[ℝ] (E →L[ℝ] ℝ)) (Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentSpace I : M → Type uE) (Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentSpace I : M → Type uE) (Bundle.Trivial M ℝ)))

class PseudoRiemannianManifold extends PseudoMetric I M where
  metric_symm : ∀ p : M, ∀ v w : (TangentSpace I p), metric p v w = metric p w v
  metric_nondegenerate : ∀ p : M, ∀ v : (TangentSpace I p), (v ≠ 0) → metric p v ≠ 0

class Metric extends PseudoRiemannianManifold I M where
  metric_posdef : ∀ p : M, ∀ v : (TangentSpace I p), (v ≠ 0) → (metric p v v > 0)

theorem metric_nonneg [m: Metric I M] {p : M} (v : TangentSpace I p) : 0 ≤ m.metric p v v := by
  by_cases h : v=0
  simp [h]
  linarith [m.metric_posdef p v h]

instance [m: Metric I M] (p : M) : Inner ℝ (TangentSpace I p) :=
  ⟨fun v w => m.metric p v w⟩

theorem tangent_inner_def [m: Metric I M] {p : M} (v w : TangentSpace I p) :
  ⟪v,w⟫ = m.metric p v w := rfl

noncomputable instance [m: Metric I M] (p : M) : NormedAddCommGroup (TangentSpace I p) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I p) _ _ _
    {
      toInner := inferInstance
      conj_symm := fun v w => by simp [tangent_inner_def,m.metric_symm p w v]
      nonneg_re := fun v => metric_nonneg I M v
      definite := fun v h => by
        have h2 := mt (m.metric_posdef p v)
        simp [h,←tangent_inner_def] at h2
        exact h2
      add_left := fun v w z => by simp [tangent_inner_def]
      smul_left := fun v w r => by simp [tangent_inner_def]
    }

noncomputable instance innerProductSpace [Metric I M] (p : M) : InnerProductSpace ℝ (TangentSpace I p) :=
  InnerProductSpace.ofCore _
