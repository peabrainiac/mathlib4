import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Diffeomorph

open scoped Classical Manifold

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

universe uE uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (I : ModelWithCorners ℝ E E) [I.Boundaryless]
  (M : Type uM) [TopologicalSpace M] [ChartedSpace E M] [SmoothManifoldWithCorners I M]

noncomputable section

def pathderiv {p q : M} (γ : Path p q) (t : unitInterval) : TangentSpace I (γ t) :=
  if t.val < 1 then ((mfderiv (𝓡∂ 1) I γ t) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
    else -((mfderiv (𝓡∂ 1) I γ t) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))

@[simp]
lemma unitInterval.symm_comp_symm : unitInterval.symm ∘ unitInterval.symm = id := by
  simp [Function.funext_iff]

lemma unitInterval.smooth_symm : Smooth (𝓡∂ 1) (𝓡∂ 1) unitInterval.symm := fun t => by
  refine' ⟨continuous_symm.continuousWithinAt,_⟩
  have hS : ∀ s:ℝ, s<1 → {x : ℝ¹ | x 0 ≤ 1} ∈ nhds (fun _i => s : ℝ¹) := fun s hs => by
    have  hS'' : ({x | x 0 ≤ 1} : Set (Fin 1 → ℝ)) = Set.pi Set.univ (fun i => Set.Iic 1) := by
      simp [Set.pi,Unique.forall_iff]
    simp_rw [EuclideanSpace,PiLp,hS'']
    exact set_pi_mem_nhds Set.finite_univ (Unique.forall_iff.mpr (fun _i => Iic_mem_nhds hs))
  have hid : @id (ℝ¹) = fun x i => x 0 :=
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
  have hf : @ContDiffWithinAt ℝ _ ℝ¹ _ _ ℝ¹
      _ _ ⊤ (fun x i ↦ 1 - x 0) ({x | 0 ≤ x 0 ∧ x 0 ≤ 1}) (fun _i => t) :=
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

lemma unitInterval.mfderiv_symm {t : unitInterval} {x : ℝ¹} :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) unitInterval.symm t x = if 0 < t.val ∧ t.val < 1 then -x else x := by
  have hS : ∀ s:ℝ, s<1 → {x : ℝ¹ | x 0 ≤ 1} ∈ nhds (fun _i => s:ℝ¹) := fun s hs => by
    have  hS'' : ({x | x 0 ≤ 1} : Set (Fin 1 → ℝ)) = Set.pi Set.univ (fun i => Set.Iic 1) := by
      simp [Set.pi,Unique.forall_iff]
    simp_rw [EuclideanSpace,PiLp,hS'']
    exact set_pi_mem_nhds Set.finite_univ (Unique.forall_iff.mpr (fun _i => Iic_mem_nhds hs))
  have hS' : ∀ s:unitInterval, UniqueDiffWithinAt ℝ
      ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1} : Set (ℝ¹)) (fun _i => s) := fun s => by
    have  hS'' : ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1} : Set (Fin 1 → ℝ)) = Set.pi Set.univ (fun i => Set.Icc 0 1) := by
      simp [Set.pi,Unique.forall_iff,Inter.inter,Set.inter]
    simp_rw [EuclideanSpace,PiLp,hS'']
    refine' UniqueDiffWithinAt.univ_pi (Fin 1) (fun _i => ℝ) (fun i => Set.Icc 0 1) (fun _i => s) _
    simp [Unique.forall_iff,(uniqueDiffOn_Icc_zero_one).uniqueDiffWithinAt s.prop]
  have hid : @id (ℝ¹) = fun x i => x 0 :=
    funext fun x => funext fun i => (Fin.eq_zero i) ▸ rfl
  have h : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1) unitInterval.symm t := unitInterval.smooth_symm.mdifferentiableAt
  by_cases ht : (t:ℝ)<1
  all_goals by_cases ht' : 0<(t:ℝ)
  all_goals simp [mfderiv,h,Function.comp,chartAt,ChartedSpace.chartAt,ht,ht',IccLeftChart,IccRightChart]
  all_goals simp [modelWithCornersEuclideanHalfSpace,Set.range,EuclideanHalfSpace]
  have hf :  @Set.EqOn (ℝ¹) (ℝ¹)
      (fun x i => 1 - min (max (x 0) 0) 1) (fun x => (fun (i:Fin 1) => 1) - fun (_i:Fin 1) => x 0) ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1}) :=
    fun x ⟨(hx1:0≤x 0),(hx2:x 0≤1)⟩ => funext fun i => by simp [hx1,hx2,HSub.hSub,Sub.sub]
  rw [←fderivWithin_inter (hS t ht),fderivWithin_congr' hf t.prop,fderivWithin_const_sub (hS' t),←hid,fderivWithin_id (hS' t)]
  simp [ContinuousLinearMap.id]
  have hf :  @Set.EqOn (ℝ¹) (ℝ¹)
      (fun x i => min (max (x 0) 0) 1) (fun x => fun (_i:Fin 1) => x 0) ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1}) :=
    fun x ⟨(hx1:0≤x 0),(hx2:x 0≤1)⟩ => funext fun i => by simp [hx1,hx2]
  rw [←fderivWithin_inter (hS t ht),fderivWithin_congr' hf t.prop,←hid,fderivWithin_id (hS' t)]
  simp [ContinuousLinearMap.id]
  have hf :  @Set.EqOn (ℝ¹) (ℝ¹)
      (fun x i => 1 - max (1 - max (x 0) 0) 0) (fun x => fun (_i:Fin 1) => x 0) ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1}) :=
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

lemma unitInterval.coe_double_eq (t : unitInterval) : (unitInterval.double t) = min 1 (2*t.val) := by
  simp [double,Set.coe_projIcc,t.2.1]

lemma unitInterval.coe_double'_eq (t : unitInterval) : (unitInterval.double' t) = max 0 (2*t.val-1) := by
  have h : (2:ℝ)-1 = 1 := (eq_sub_of_add_eq one_add_one_eq_two).symm
  have h' := h ▸ (sub_le_sub_right ((mul_le_iff_le_one_right zero_lt_two).mpr t.2.2) 1)
  simp [double',Set.coe_projIcc,t.2.2,min_eq_right h']

lemma unitInterval.smoothAt_double {t : unitInterval} (ht : t.val < 1 / 2) :
    SmoothAt (𝓡∂ 1) (𝓡∂ 1) unitInterval.double t := by
  have hS : ∀ s:ℝ, s<1/2 → {x:ℝ¹ | x 0 ≤ 1/2} ∈ nhds (fun _i => s:ℝ¹) := fun s hs => by
    have  hS'' : ({x | x 0 ≤ 1/2} : Set (Fin 1 → ℝ)) = Set.pi Set.univ (fun i => Set.Iic (1/2)) := by
      simp [Set.pi,Unique.forall_iff]
    simp_rw [EuclideanSpace,PiLp,hS'']
    exact set_pi_mem_nhds Set.finite_univ (Unique.forall_iff.mpr (fun _i => Iic_mem_nhds hs))
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
  have hf : (fun x i ↦ 2 * (x 0) : ℝ¹ → ℝ¹) = fun x => (2:ℝ)•x :=
    funext fun x => funext fun i => Fin.eq_zero i ▸ rfl
  have hf' : @ContDiffWithinAt ℝ _ (ℝ¹) _ _ (ℝ¹)
      _ _ ⊤ (fun x i ↦ 2 * (x 0)) ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1 / 2}) (fun _i => t) := by
    rw [hf]
    exact (contDiff_const_smul 2).contDiffWithinAt
  refine' ContDiffWithinAt.congr' hf' _ ⟨t.2.1,ht.le⟩
  exact (fun x ⟨(hx1:0≤x 0),(hx2:x 0≤1/2)⟩ => by
    simp [hx1,hx2.trans one_half_lt_one.le,min_eq_right ((le_div_iff' zero_lt_two).mp hx2)])

lemma unitInterval.double_symm (t : unitInterval) : unitInterval.double (unitInterval.symm t) =
    unitInterval.symm (unitInterval.double' t) := by
  ext; simp_rw [coe_double_eq,coe_symm_eq,coe_double'_eq,mul_sub]
  have h : (2 : ℝ) - 1 = 1 := by ring
  have h' : (2 - 2 * t.val) = 1 - (2 * t.val - 1) := by ring
  by_cases ht : 2 * t.val ≤ 1
  simp [ht,h ▸ (sub_le_sub_left ht 2)]
  have  ht' := le_of_not_le ht
  have ht'' := h ▸ (sub_le_sub_right ((mul_le_iff_le_one_right zero_lt_two).mpr t.2.2) 1)
  simp [ht',t.2.2,min_eq_right ht'',h']

lemma unitInterval.double'_eq_symm_double_symm : unitInterval.double' =
    unitInterval.symm ∘ unitInterval.double ∘ unitInterval.symm := funext fun t => by
  simp_rw [Function.comp_apply,unitInterval.double_symm,unitInterval.symm_symm]

lemma unitInterval.smoothAt_double' {t : unitInterval} (ht : (t : ℝ) > 1 / 2) :
    SmoothAt (𝓡∂ 1) (𝓡∂ 1) unitInterval.double' t := by
  rw [unitInterval.double'_eq_symm_double_symm]
  have ht' : (symm t : ℝ) < 1 / 2 := by rw [coe_symm_eq]; linarith
  exact ((smooth_symm.smoothAt)).comp t ((smoothAt_double ht').comp t (smooth_symm.smoothAt))

lemma Path.trans_eqOn_left {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} :
    Set.EqOn (γ.trans γ') (γ ∘ unitInterval.double) {t | t.val ≤ 1 / 2} := fun t ht => by
  have ht' : 2 * t.val ∈ unitInterval := ⟨mul_nonneg zero_lt_two.le t.2.1,(le_div_iff' zero_lt_two).mp ht⟩
  simp [trans,(inv_eq_one_div (2 : ℝ)).symm ▸ ht.out,γ.extend_extends ht',
    Subtype.coe_eq_of_eq_mk (unitInterval.coe_double_eq t),ht'.out]

lemma Path.trans_eqOn_right {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} :
    Set.EqOn (γ.trans γ') (γ' ∘ unitInterval.double') {t | 1 / 2 ≤ t.val} := fun t ht => by
  by_cases ht' : t.val = 1 / 2
  simp [trans,(inv_eq_one_div (2 : ℝ)).symm ▸ ht',unitInterval.double']
  have ht'' := Ne.lt_of_le (Ne.symm ht') ht.out
  have ht''' : 2 * t.val - 1 ∈ unitInterval := ⟨by linarith,by linarith [t.2.2]⟩
  simp [trans,(inv_eq_one_div (2 : ℝ)).symm ▸ ht''.not_le,γ'.extend_extends ht''',
    Subtype.coe_eq_of_eq_mk (unitInterval.coe_double'_eq t),max_eq_right ht'''.out.1]

lemma Path.trans_mdifferentiableAt_left {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    {t : unitInterval} (ht : (t : ℝ) < 1 / 2)
    (hγ : MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.double t)) :
      MDifferentiableAt (𝓡∂ 1) I (γ.trans γ') t := by
  have h := MDifferentiableAt.comp t hγ (unitInterval.smoothAt_double ht).mdifferentiableAt
  refine' MDifferentiableAt.congr_of_eventuallyEq h ((trans_eqOn_left M).eventuallyEq_of_mem _)
  apply (mem_nhds_subtype unitInterval t {s | s.val ≤ 1 / 2}).mpr
  exact ⟨Set.Iic (1 / 2),⟨Iic_mem_nhds ht,subset_of_eq rfl⟩⟩

lemma Path.trans_mdifferentiableAt_right {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    {t : unitInterval} (ht : (t : ℝ) > 1 / 2)
    (hγ : MDifferentiableAt (𝓡∂ 1) I γ' (unitInterval.double' t)) :
      MDifferentiableAt (𝓡∂ 1) I (γ.trans γ') t := by
  rw [←(γ.trans γ').symm_symm,Path.trans_symm]
  have ht' : (unitInterval.symm t).val < 1 / 2 := by rw [unitInterval.coe_symm_eq]; linarith
  apply (Path.symm_mdifferentiableAt_iff I M).mpr
  apply Path.trans_mdifferentiableAt_left I M ht'
  apply (Path.symm_mdifferentiableAt_iff I M).mpr
  rw [unitInterval.double_symm,unitInterval.symm_symm]
  exact hγ

def unitInterval.one_half : unitInterval := ⟨1/2,div_mem zero_lt_one.le zero_lt_two.le one_lt_two.le⟩

lemma Path.trans_mdifferentiableAt_mid {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    (hγ : MDifferentiableAt (𝓡∂ 1) I γ 1) (hγ' : MDifferentiableAt (𝓡∂ 1) I γ' 0)
    (h : pathderiv I M γ 1 = pathderiv I M γ' 0) :
      MDifferentiableAt (𝓡∂ 1) I (γ.trans γ') unitInterval.one_half := by
  sorry

#check HasMFDerivWithinAt.union

lemma pathderiv_of_trans {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} {t : unitInterval} :
    pathderiv I M (γ.trans γ') t =
      if ht : (t : ℝ) < 1 / 2 then
        2 • (pathderiv I M γ ⟨2 * t,(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1,le_of_lt ht⟩⟩)
      else if ht : (t : ℝ) > 1 / 2 then
        2 • (pathderiv I M γ ⟨2 * t - 1,unitInterval.two_mul_sub_one_mem_iff.2 ⟨le_of_lt ht, t.2.2⟩⟩)
      else if hp' : pathderiv I M γ 1 = pathderiv I M γ' 0 then pathderiv I M γ 1 else 0 := by
  by_cases ht : (t : ℝ) < 1 / 2
  simp_rw [eq_true ht,dite_true]
  --simp_rw [pathderiv,eq_true (ht.trans one_half_lt_one),eq_true ((lt_div_iff' zero_lt_two).mp ht),
      --ite_true,Path.trans,Path.coe_mk_mk]
  sorry
  sorry
