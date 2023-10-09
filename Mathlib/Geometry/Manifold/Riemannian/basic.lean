import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Diffeomorph
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

def pathderiv {p q : M} (γ : Path p q) (t : unitInterval) : TangentSpace I (γ t) :=
  if t.val < 1 then ((mfderiv (𝓡∂ 1) I γ t) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
    else -((mfderiv (𝓡∂ 1) I γ t) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))

@[simp]
lemma unitInterval.symm_comp_symm : unitInterval.symm ∘ unitInterval.symm = @id unitInterval := by
  simp [Function.funext_iff]

lemma unitInterval.smooth_symm : Smooth (𝓡∂ 1) (𝓡∂ 1) unitInterval.symm := fun t => by
  refine' ⟨continuous_symm.continuousWithinAt,_⟩
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

lemma Path.symm_mdifferentiableAt_iff {p q : M} {γ : Path p q} {t : unitInterval} :
    MDifferentiableAt (𝓡∂ 1) I γ.symm t ↔ MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.symm t) := by
  have h {p q : M} (γ : Path p q) (t : unitInterval) :
      MDifferentiableAt (𝓡∂ 1) I γ.symm t → MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.symm t) := fun h' => by
    rw [←Function.comp.right_id γ,←unitInterval.symm_comp_symm,←Function.comp.assoc _ _ _]
    exact MDifferentiableAt.comp (unitInterval.symm t) ((unitInterval.symm_symm t).symm ▸ h') unitInterval.smooth_symm.mdifferentiableAt
  have h' := unitInterval.symm_symm t ▸ (@Path.symm_symm _ _ _ _ γ) ▸ (h γ.symm (unitInterval.symm t))
  exact ⟨h γ t,h'⟩

lemma Path.pathderiv_of_symm {p q : M} {γ : Path p q} {t : unitInterval} : pathderiv I M γ.symm t =
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

def unitInterval.double : unitInterval → unitInterval := fun t => Set.projIcc 0 1 zero_le_one (2*t)

def unitInterval.double' : unitInterval → unitInterval := fun t => Set.projIcc 0 1 zero_le_one (2*t-1)

lemma unitInterval.continuous_double : Continuous unitInterval.double :=
  continuous_projIcc.comp ((continuous_mul_left 2).comp continuous_subtype_val)

lemma unitInterval.continuous_double' : Continuous unitInterval.double' :=
  continuous_projIcc.comp (((continuous_mul_left 2).comp continuous_subtype_val).sub continuous_const)

lemma unitInterval.coe_double_eq (t : unitInterval) : (unitInterval.double t) = min 1 (2*(t:ℝ)) := by
  simp [double,Set.coe_projIcc,t.2.1]

lemma unitInterval.smoothAt_double {t : unitInterval} (ht : (t : ℝ) < 1 / 2) :
    SmoothAt (𝓡∂ 1) (𝓡∂ 1) unitInterval.double t := by
  have hS : ∀ s:ℝ, s<1/2 → {x:EuclideanSpace ℝ (Fin 1) | x 0 ≤ 1/2} ∈ nhds (fun i => s:EuclideanSpace ℝ (Fin 1)) := fun s hs => by
    have  hS'' : ({x | x 0 ≤ 1/2} : Set (Fin 1 → ℝ)) = Set.pi Set.univ (fun i => Set.Iic (1/2)) := by
      simp [Set.pi,Unique.forall_iff]
    simp_rw [EuclideanSpace,PiLp,hS'']
    exact set_pi_mem_nhds Set.finite_univ (Unique.forall_iff.mpr (fun i => Iic_mem_nhds hs))
  refine' ⟨continuous_double.continuousWithinAt,_⟩
  have ht' := (lt_div_iff' zero_lt_two).mp ht
  have ht'' : (double t).val < 1 := by simp [coe_double_eq,ht']
  simp_rw [ContDiffWithinAtProp,Function.comp,chartAt,ChartedSpace.chartAt,Set.preimage_univ,
      Set.univ_inter,ht'',ht.trans one_half_lt_one,ite_true,modelWithCornersEuclideanHalfSpace,
      ModelWithCorners.mk_coe,ModelWithCorners.mk_symm,LocalEquiv.coe_symm_mk,IccLeftChart,
      LocalHomeomorph.mk_coe,LocalHomeomorph.mk_coe_symm,LocalEquiv.coe_symm_mk,coe_double_eq,
      Function.update_same,add_zero,sub_zero,Set.range,EuclideanHalfSpace,Subtype.exists,
      exists_prop,exists_eq_right]
  apply (contDiffWithinAt_inter (hS t ht)).mp
  have hf : (fun x i ↦ 2 * (x 0) : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) = fun x => (2:ℝ)•x :=
    funext fun x => funext fun i => Fin.eq_zero i ▸ rfl
  have hf' : @ContDiffWithinAt ℝ _ (EuclideanSpace ℝ (Fin 1)) _ _ (EuclideanSpace ℝ (Fin 1))
      _ _ ⊤ (fun x i ↦ 2 * (x 0)) ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1 / 2}) (fun i => t) := by
    rw [hf]
    exact (contDiff_const_smul 2).contDiffWithinAt
  refine' ContDiffWithinAt.congr' hf' _ ⟨t.2.1,ht.le⟩
  exact (fun x ⟨(hx1:0≤x 0),(hx2:x 0≤1/2)⟩ => by
    simp [hx1,hx2.trans one_half_lt_one.le,min_eq_right ((le_div_iff' zero_lt_two).mp hx2)])

lemma unitInterval.double'_eq_symm_double_symm : unitInterval.double' =
    unitInterval.symm ∘ unitInterval.double ∘ unitInterval.symm := funext fun t => by
  have h : (2 : ℝ) - 1 = 1 := by ring
  have h' : (1 : ℝ) - (2 - 2 * t) = 2 * t - 1 := by ring
  simp_rw [Function.comp_apply,double,double',symm,Set.projIcc,Subtype.mk_eq_mk,mul_sub]
  by_cases ht : 2 * (t : ℝ) ≤ 1
  simp [ht,h ▸ (sub_le_sub_left ht 2)]
  have  ht' := le_of_not_le ht
  have ht'' := h ▸ (sub_le_sub_right ((mul_le_iff_le_one_right zero_lt_two).mpr t.2.2) 1)
  simp [t.2.2,ht',min_eq_right ht'',min_eq_right (h ▸ (sub_le_sub_left ht' 2)),h']

lemma unitInterval.smoothAt_double' {t : unitInterval} (ht : (t : ℝ) > 1 / 2) :
    SmoothAt (𝓡∂ 1) (𝓡∂ 1) unitInterval.double' t := by
  rw [unitInterval.double'_eq_symm_double_symm]
  have ht' : (symm t : ℝ) < 1 / 2 := by rw [coe_symm_eq]; linarith
  exact ((smooth_symm.smoothAt)).comp t ((smoothAt_double ht').comp t (smooth_symm.smoothAt))

lemma Path.trans_mdifferentiableAt_left {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    {t : unitInterval} (ht : (t : ℝ) < 1 / 2)
    (hγ : MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.double t)) :
      MDifferentiableAt (𝓡∂ 1) I (γ.trans γ') t := by
  rw [trans,coe_mk_mk]
  have h : MDifferentiableAt (𝓡∂ 1) I (γ ∘ unitInterval.double) t := by
    refine' MDifferentiableAt.comp t hγ _
    exact (unitInterval.smoothAt_double ht).mdifferentiableAt
  refine' MDifferentiableAt.congr_of_eventuallyEq h _
  sorry

#check fun (t : unitInterval) (ht : (t : ℝ) < 1 / 2) => (⟨2*t,(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1,le_of_lt ht⟩⟩:unitInterval)

lemma pathderiv_of_trans {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} {t : unitInterval} :
    pathderiv I M (γ.trans γ') t =
      if ht : (t : ℝ) < 1 / 2 then
        2 • (pathderiv I M γ ⟨2 * t,(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1,le_of_lt ht⟩⟩)
      else if ht : (t : ℝ) > 1 / 2 then
        2 • (pathderiv I M γ ⟨2 * t - 1,unitInterval.two_mul_sub_one_mem_iff.2 ⟨le_of_lt ht, t.2.2⟩⟩)
      else if hp' : pathderiv I M γ 1 = pathderiv I M γ' 0 then pathderiv I M γ 1 else 0 := by
  by_cases ht : (t : ℝ) < 1 / 2
  simp_rw [eq_true ht,dite_true]
  simp_rw [pathderiv,eq_true (ht.trans one_half_lt_one),eq_true ((lt_div_iff' zero_lt_two).mp ht),
      ite_true,Path.trans,Path.coe_mk_mk]
  sorry
  sorry

def length [Metric I M] {p q : M} (γ : Path p q) :=
  ∫ t, ‖pathderiv I M γ t‖

lemma length_eq_intervalIntegral [Metric I M] {p q : M} (γ : Path p q) : length I M γ =
    ∫ t in (0:ℝ)..1, if ht : t ∈ unitInterval then ‖pathderiv I M γ ⟨t,ht⟩‖ else 0 := by
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
  have h : ∀ t, (if ht : t ∈ unitInterval then ‖pathderiv I M γ (unitInterval.symm ⟨t,ht⟩)‖ else 0) =
      (fun t => if ht : t ∈ unitInterval then ‖pathderiv I M γ ⟨t,ht⟩‖ else 0) (1-t) := fun t => by
    simp [and_comm,unitInterval.symm]
  simp_rw [length_eq_intervalIntegral,Path.pathderiv_of_symm,norm_neg,h,
    intervalIntegral.integral_comp_sub_left (fun t => if ht : t ∈ unitInterval then ‖pathderiv I M γ ⟨t,ht⟩‖ else 0) 1,
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
