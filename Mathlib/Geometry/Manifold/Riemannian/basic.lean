import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.MeasureSpace

open scoped Manifold RealInnerProductSpace Uniformity

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

def pathderiv {p q : M} (γ : Path p q) (t : unitInterval) : TangentSpace I (γ t) :=
  if t.val < 1 then ((mfderiv (𝓡∂ 1) I γ t) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
    else -((mfderiv (𝓡∂ 1) I γ t) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))

@[simp]
lemma unitInterval.symm_comp_symm : unitInterval.symm ∘ unitInterval.symm = @id unitInterval := by
  simp [Function.funext_iff]

lemma unitInterval.smooth_symm : Smooth (𝓡∂ 1) (𝓡∂ 1) unitInterval.symm := fun t => by
  refine' ⟨unitInterval.continuous_symm.continuousWithinAt,_⟩
  have hS : ∀ s:ℝ, s<1 → {x:EuclideanSpace ℝ (Fin 1) | x 0 ≤ 1} ∈ nhds (fun i => s:EuclideanSpace ℝ (Fin 1)) := fun s hs => by
    have  hS'' : ({x | x 0 ≤ 1} : Set (Fin 1 → ℝ)) = Set.pi Set.univ (fun i => Set.Iic 1) := by
      simp [Set.pi,Unique.forall_iff]
    simp_rw [EuclideanSpace,PiLp,hS'']
    exact set_pi_mem_nhds Set.finite_univ (Unique.forall_iff.mpr (fun i => Iic_mem_nhds hs))
  have hid : @id (EuclideanSpace ℝ (Fin 1)) = fun x i => x 0 :=
    funext fun x => funext fun i => (Fin.eq_zero i) ▸ rfl
  simp_rw [ContDiffWithinAtProp,Function.comp,chartAt,ChartedSpace.chartAt,coe_symm_eq,sub_lt_self_iff,Set.preimage_univ,Set.univ_inter]
  by_cases ht : (t:ℝ)<1
  all_goals (by_cases ht' : 0<(t:ℝ))
  all_goals (simp_rw [ht,ht',ite_true,ite_false,modelWithCornersEuclideanHalfSpace,
      ModelWithCorners.mk_coe,ModelWithCorners.mk_symm,LocalEquiv.coe_symm_mk,
      IccLeftChart,IccRightChart,LocalHomeomorph.mk_coe,LocalHomeomorph.mk_coe_symm,
      LocalEquiv.coe_symm_mk,coe_symm_eq,Function.update_same,add_zero,sub_zero,max_le_iff,
      sub_sub_cancel,Set.range,EuclideanHalfSpace,Subtype.exists,exists_prop,exists_eq_right])
  apply (contDiffWithinAt_inter (hS t ht)).mp
  have hf : @ContDiffWithinAt ℝ _ (EuclideanSpace ℝ (Fin 1)) _ _ (EuclideanSpace ℝ (Fin 1))
      _ _ ⊤ (fun x i ↦ 1 - x 0) ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1}) (fun i => t) :=
    contDiffWithinAt_const.sub (hid ▸ contDiffWithinAt_id)
  exact ContDiffWithinAt.congr' hf (fun x ⟨(hx1:0≤x 0),(hx2:x 0≤1)⟩ => by simp [hx1,hx2]) t.prop
  apply (contDiffWithinAt_inter (hS t ht)).mp
  exact ContDiffWithinAt.congr' (hid ▸ contDiffWithinAt_id) (fun x ⟨(hx1:0≤x 0),(hx2:x 0≤1)⟩ => by simp [hx1,hx2]) t.prop
  apply (contDiffWithinAt_inter (hS (1-t) ((sub_lt_self_iff 1).mpr ht'))).mp
  exact ContDiffWithinAt.congr' (hid ▸ contDiffWithinAt_id) (fun x ⟨(hx1:0≤x 0),(hx2:x 0≤1)⟩ => by simp [hx1,hx2]) (unitInterval.symm t).prop
  linarith

def unitInterval.symm_toDiffeomorph : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) unitInterval unitInterval ⊤ where
  toFun := unitInterval.symm
  invFun := unitInterval.symm
  left_inv := unitInterval.symm_symm
  right_inv := unitInterval.symm_symm
  contMDiff_toFun := unitInterval.smooth_symm
  contMDiff_invFun := unitInterval.smooth_symm

lemma unitInterval.mfderiv_symm {t : unitInterval} {x : EuclideanSpace ℝ (Fin 1)} :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) unitInterval.symm t x = if 0 < t.val ∧ t.val < 1 then -x else x := by
  have hS : ∀ s:ℝ, s<1 → {x:EuclideanSpace ℝ (Fin 1) | x 0 ≤ 1} ∈ nhds (fun i => s:EuclideanSpace ℝ (Fin 1)) := fun s hs => by
    have  hS'' : ({x | x 0 ≤ 1} : Set (Fin 1 → ℝ)) = Set.pi Set.univ (fun i => Set.Iic 1) := by
      simp [Set.pi,Unique.forall_iff]
    simp_rw [EuclideanSpace,PiLp,hS'']
    exact set_pi_mem_nhds Set.finite_univ (Unique.forall_iff.mpr (fun i => Iic_mem_nhds hs))
  have hS' : ∀ s:unitInterval, UniqueDiffWithinAt ℝ
      ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1} : Set (EuclideanSpace ℝ (Fin 1))) (fun i => s) := fun s => by
    have  hS'' : ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1} : Set (Fin 1 → ℝ)) = Set.pi Set.univ (fun i => Set.Icc 0 1) := by
      simp [Set.pi,Unique.forall_iff,Inter.inter,Set.inter]
    simp_rw [EuclideanSpace,PiLp,hS'']
    refine' UniqueDiffWithinAt.univ_pi (Fin 1) (fun i => ℝ) (fun i => Set.Icc 0 1) (fun i => s) _
    simp [Unique.forall_iff,(uniqueDiffOn_Icc_zero_one).uniqueDiffWithinAt s.prop]
  have hid : @id (EuclideanSpace ℝ (Fin 1)) = fun x i => x 0 :=
    funext fun x => funext fun i => (Fin.eq_zero i) ▸ rfl
  have h : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1) unitInterval.symm t := unitInterval.smooth_symm.mdifferentiableAt
  by_cases ht : (t:ℝ)<1
  all_goals by_cases ht' : 0<(t:ℝ)
  all_goals simp [mfderiv,h,Function.comp,chartAt,ChartedSpace.chartAt,ht,ht',IccLeftChart,IccRightChart]
  all_goals simp [modelWithCornersEuclideanHalfSpace,Set.range,EuclideanHalfSpace]
  have hf :  @Set.EqOn (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))
      (fun x i => 1 - min (max (x 0) 0) 1) (fun x => (fun (i:Fin 1) => 1) - fun (i:Fin 1) => x 0) ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1}) :=
    fun x ⟨(hx1:0≤x 0),(hx2:x 0≤1)⟩ => funext fun i => by simp [hx1,hx2,HSub.hSub,Sub.sub]
  rw [←fderivWithin_inter (hS t ht),fderivWithin_congr' hf t.prop,fderivWithin_const_sub (hS' t),←hid,fderivWithin_id (hS' t)]
  simp [ContinuousLinearMap.id]
  have hf :  @Set.EqOn (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))
      (fun x i => min (max (x 0) 0) 1) (fun x => fun (i:Fin 1) => x 0) ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1}) :=
    fun x ⟨(hx1:0≤x 0),(hx2:x 0≤1)⟩ => funext fun i => by simp [hx1,hx2]
  rw [←fderivWithin_inter (hS t ht),fderivWithin_congr' hf t.prop,←hid,fderivWithin_id (hS' t)]
  simp [ContinuousLinearMap.id]
  have hf :  @Set.EqOn (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))
      (fun x i => 1 - max (1 - max (x 0) 0) 0) (fun x => fun (i:Fin 1) => x 0) ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1}) :=
    fun x ⟨(hx1:0≤x 0),(hx2:x 0≤1)⟩ => funext fun i => by simp [hx1,hx2]
  rw [←fderivWithin_inter (hS (1-t) ((sub_lt_self_iff 1).mpr ht')),fderivWithin_congr' hf (unitInterval.symm t).prop,←hid,fderivWithin_id (hS' ⟨1-t,(unitInterval.symm t).prop⟩)]
  simp [ContinuousLinearMap.id]
  exact False.rec (ht' (lt_of_lt_of_le zero_lt_one (le_of_not_lt ht)))

lemma symm_mdifferentiableAt_iff {p q : M} {γ : Path p q} {t : unitInterval} :
    MDifferentiableAt (𝓡∂ 1) I γ.symm t ↔ MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.symm t) := by
  have h {p q : M} (γ : Path p q) (t : unitInterval) :
      MDifferentiableAt (𝓡∂ 1) I γ.symm t → MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.symm t) := fun h' => by
    rw [←Function.comp.right_id γ,←unitInterval.symm_comp_symm,←Function.comp.assoc _ _ _]
    exact MDifferentiableAt.comp (unitInterval.symm t) ((unitInterval.symm_symm t).symm ▸ h') unitInterval.smooth_symm.mdifferentiableAt
  have h' := unitInterval.symm_symm t ▸ (@Path.symm_symm _ _ _ _ γ) ▸ (h γ.symm (unitInterval.symm t))
  exact ⟨h γ t,h'⟩

lemma pathderiv_of_symm {p q : M} {γ : Path p q} {t : unitInterval} : pathderiv I M γ.symm t =
    -pathderiv I M γ (unitInterval.symm t) := by
  rw [pathderiv,pathderiv]
  by_cases hγ : MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.symm t)
  rw [Path.symm,Path.coe_mk_mk,mfderiv_comp t hγ unitInterval.smooth_symm.mdifferentiableAt]
  by_cases ht : 0 < t.val ∧ t.val < 1
  simp [unitInterval.mfderiv_symm,ht]
  obtain ht' | ht' := not_and_or.mp ht
  simp [unitInterval.mfderiv_symm,ht',lt_of_le_of_lt (le_of_not_lt ht') zero_lt_one]
  simp [unitInterval.mfderiv_symm,ht',lt_of_lt_of_le zero_lt_one (le_of_not_lt ht')]
  have hγ' := (not_iff_not.mpr (symm_mdifferentiableAt_iff I M)).mpr hγ
  simp [mfderiv_zero_of_not_mdifferentiableAt hγ,mfderiv_zero_of_not_mdifferentiableAt hγ']

def length [Metric I M] {p q : M} (γ : Path p q) :=
  ∫ t, ‖pathderiv I M γ t‖

theorem length_nonneg [Metric I M] {p q : M} (γ : Path p q) : 0 ≤ length I M γ :=
  MeasureTheory.integral_nonneg (fun t => by simp)

@[simp]
theorem length_of_const [Metric I M] {p : M} : length I M (Path.refl p) = 0 := by
  simp [length,pathderiv,Path.refl]

def unitInterval.symm_toMeasurableEquiv : MeasurableEquiv unitInterval unitInterval where
  toFun := symm
  invFun := symm
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse,Function.LeftInverse]
  measurable_toFun := continuous_symm.measurable
  measurable_invFun := continuous_symm.measurable

lemma MeasurePreserving.subtype_map_preimage {α : Type u_1} {β : Type u_2} [MeasurableSpace α]
    [MeasurableSpace β] {μα : MeasureTheory.Measure α} {μβ : MeasureTheory.Measure β} {f : α → β}
    (hf : MeasureTheory.MeasurePreserving f μα μβ) {s : Set β} (hs : MeasurableSet s)
    : MeasureTheory.MeasurePreserving (Subtype.map f (fun x => (id : x ∈ f ⁻¹' s → f x ∈ s)))
    (MeasureTheory.Measure.comap Subtype.val μα) (MeasureTheory.Measure.comap Subtype.val μβ) := by
  have hf' := Measurable.subtype_map hf.measurable (fun x => (id : x ∈ f ⁻¹' s → f x ∈ s))
  refine' ⟨hf',_⟩
  apply MeasureTheory.Measure.ext; intro t ht
  simp_rw [MeasureTheory.Measure.map_apply hf' ht]
  have hs': (MeasureTheory.Measure.comap Subtype.val μβ) t = μβ (Subtype.val '' t)
    := comap_subtype_coe_apply hs μβ t
  have h : (MeasureTheory.Measure.map f μα) (Subtype.val '' t) = μα (f ⁻¹' (Subtype.val '' t))
    := MeasureTheory.Measure.map_apply hf.measurable (MeasurableSet.subtype_image hs ht)
  rw [comap_subtype_coe_apply (hf.measurable hs) μα,hs',←hf.map_eq,h]
  apply congrArg μα
  apply Set.ext; intro x
  simp only [Set.mem_image,Set.mem_preimage,Subtype.exists,exists_and_right,exists_eq_right]
  rfl

def unitInterval.measurePreserving_symm : MeasureTheory.MeasurePreserving unitInterval.symm := by
  have hsymm := unitInterval.continuous_symm.measurable
  refine' ⟨hsymm,_⟩
  apply MeasureTheory.Measure.ext; intro s hs
  simp_rw [volume_set_coe_def,MeasureTheory.Measure.map_apply hsymm hs]
  simp_rw [comap_subtype_coe_apply measurableSet_Icc]
  have h : Set.image symm = Set.preimage symm :=
    Set.image_eq_preimage_of_inverse symm_toMeasurableEquiv.left_inv symm_toMeasurableEquiv.right_inv
  have h' : Subtype.val ∘ symm = (fun t => 1-t : ℝ → ℝ) ∘ Subtype.val := funext fun t => by simp
  have h'' : Set.image (fun t => 1-t : ℝ → ℝ) = Set.preimage (fun t => 1-t : ℝ → ℝ) :=
    Set.image_eq_preimage_of_inverse (by simp [Function.LeftInverse]) (by simp [Function.RightInverse,Function.LeftInverse])
  have h''' : MeasureTheory.MeasurePreserving (fun t => 1-t : ℝ → ℝ) := MeasureTheory.Measure.measurePreserving_sub_left _ 1
  rw [←h,←Set.image_comp,h',Set.image_comp,h'']
  rw [←MeasureTheory.Measure.map_apply h'''.measurable (MeasurableSet.subtype_image measurableSet_Icc hs)]
  rw [h'''.map_eq]

@[simp]
theorem length_of_symm [Metric I M] {p q : M} {γ : Path p q} : length I M (Path.symm γ) = length I M γ := by
  simp_rw [length,pathderiv_of_symm,norm_neg]
  refine' MeasureTheory.MeasurePreserving.integral_comp _ _ (fun t => ‖pathderiv I M γ t‖)
  exact unitInterval.measurePreserving_symm
  exact unitInterval.symm_toMeasurableEquiv.measurableEmbedding

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
