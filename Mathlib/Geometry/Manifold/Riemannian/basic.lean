import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom

open scoped Manifold

universe uE uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (I : ModelWithCorners ℝ E E) [I.Boundaryless]
  (M : Type uM) [TopologicalSpace M] [ChartedSpace E M] [SmoothManifoldWithCorners I M]

class Metric extends SmoothManifoldWithCorners I M where
  metric: SmoothSection I (E →L[ℝ] (E →L[ℝ] ℝ)) (Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentSpace I : M → Type uE) (Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentSpace I : M → Type uE) (Bundle.Trivial M ℝ)))

class PseudoRiemannianManifold extends Metric I M where
  metric_symm : ∀ x : M, ∀ v w : (TangentSpace I x), metric x v w = metric x w v
  metric_nondegenerate : ∀ x : M, ∀ v : (TangentSpace I x), (v ≠ 0) → metric x v ≠ 0

class RiemannianManifold extends PseudoRiemannianManifold I M where
  metric_pos : ∀ x : M, ∀ v : (TangentSpace I x), (v ≠ 0) → (metric x v v > 0)
