import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Diffeomorph

open scoped Classical Manifold

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

universe uE uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (I : ModelWithCorners ℝ E E) [I.Boundaryless]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace E M] [SmoothManifoldWithCorners I M]

noncomputable section

def pathderiv {p q : M} (γ : Path p q) (t : unitInterval) : TangentSpace I (γ t) :=
  if t.val < 1 then ((mfderiv (𝓡∂ 1) I γ t) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
    else -((mfderiv (𝓡∂ 1) I γ t) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))

def pathderivWithin {p q : M} (γ : Path p q) (s : Set unitInterval) (t : unitInterval) :
    TangentSpace I (γ t) :=
  if t.val < 1 then ((mfderivWithin (𝓡∂ 1) I γ s t) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
    else -((mfderivWithin (𝓡∂ 1) I γ s t) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))

@[simp]
lemma pathderivWithin_univ {p q : M} (γ : Path p q) : pathderivWithin I γ Set.univ = pathderiv I γ := by
  simp [pathderiv,pathderivWithin]

lemma pathderivWithin_congr {p q p' q' : M} {γ : Path p q} {γ' : Path p' q'} {s : Set unitInterval}
    {t : unitInterval} (hs : UniqueMDiffWithinAt (𝓡∂ 1) s t) (h : ∀ t' ∈ s, γ t' = γ' t')
    (ht : γ t = γ' t) : pathderivWithin I γ s t = pathderivWithin I γ' s t := by
  rw [pathderivWithin,pathderivWithin,mfderivWithin_congr hs h ht]

lemma pathderivWithin_congr' {p q p' q' : M} {γ : Path p q} {γ' : Path p' q'} {s : Set unitInterval}
    {t : unitInterval} (hs : UniqueMDiffWithinAt (𝓡∂ 1) s t) (h : ∀ t' ∈ s, γ t' = γ' t')
    (ht : t ∈ s) : pathderivWithin I γ s t = pathderivWithin I γ' s t :=
  pathderivWithin_congr I hs h (h t ht)

lemma pathderivWithin_reparam {p q : M} {γ : Path p q} {f : unitInterval → unitInterval}
    {hf : Continuous f} {hf₀ : f 0 = 0} {hf₁ : f 1 = 1} {s u : Set unitInterval}
    (t : unitInterval) (hγ : MDifferentiableWithinAt (𝓡∂ 1) I γ u (f t))
    (hf' : MDifferentiableWithinAt (𝓡∂ 1) (𝓡∂ 1) f s t) (hsu : s ⊆ f ⁻¹' u)
    (hst : UniqueMDiffWithinAt (𝓡∂ 1) s t) :
      pathderivWithin I (γ.reparam f hf hf₀ hf₁) s t =
      (if t.val < 1 ∧ (f t).val < 1 ∨ ¬t.val < 1 ∧ ¬(f t).val < 1
        then mfderivWithin (𝓡∂ 1) (𝓡∂ 1) f s t (EuclideanSpace.single 0 1) 0
        else -mfderivWithin (𝓡∂ 1) (𝓡∂ 1) f s t (EuclideanSpace.single 0 1) 0 : ℝ)
       • (pathderivWithin I γ u (f t))
        := by
  have h : ↑(mfderivWithin (𝓡∂ 1) (𝓡∂ 1) f s t) =
      fun x => (mfderivWithin (𝓡∂ 1) (𝓡∂ 1) f s t (EuclideanSpace.single 0 1) 0) • x := by
    refine' funext fun x => (PiLp.ext (Unique.forall_iff.mpr _) : @Eq ℝ¹ _ _)
    have hx : x = (x 0) • (EuclideanSpace.single 0 1 : ℝ¹) := PiLp.ext fun i => by
      simp [((Fin.eq_zero i) ▸ rfl : x 0 = x i)]
    rw [PiLp.smul_apply,smul_eq_mul,mul_comm,hx,map_smul,PiLp.smul_apply _ _ (_ : ℝ¹)]
    simp
  rw [pathderivWithin,pathderivWithin,Path.coe_reparam,mfderivWithin_comp t hγ hf' hsu hst]
  by_cases ht : t.val < 1
  all_goals by_cases ht' : (f t).val < 1
  all_goals simp only [ht,ht',ite_true,ite_false,ContinuousLinearMap.comp_apply]
  all_goals nth_rewrite 1 [h]
  all_goals simp

@[simp]
lemma unitInterval.symm_comp_symm : symm ∘ symm = id := by
  simp [Function.funext_iff]

@[simp]
lemma unitInterval.symm_symm_image (s : Set unitInterval) : symm '' (symm '' s) = s := by
  simp [s.image_image symm]

def unitInterval.val' (t : unitInterval) : ℝ¹ := EuclideanSpace.single 0 t

def unitInterval.proj (t : ℝ) : unitInterval := Set.projIcc 0 1 zero_le_one t

def unitInterval.proj' (x : ℝ¹) : unitInterval := Set.projIcc 0 1 zero_le_one (x 0)

lemma unitInterval.proj_val (t : unitInterval) : proj t.val = t := by simp [proj]

lemma unitInterval.val_proj (ht : t ∈ unitInterval) : (proj t).val = t := by
  simp [proj,Set.projIcc,ht.out]

lemma unitInterval.proj_comp_val : proj ∘ Subtype.val = id := funext fun t => by simp [proj]

lemma unitInterval.proj'_val' (t : unitInterval) : proj' (val' t) = t := by
  simp [proj',val']

lemma unitInterval.proj'_comp_val' : proj' ∘ val' = id := funext fun t => by
  simp [proj',val']

lemma EuclideanSpace.single_eq_self {x : ℝ¹} : single 0 (x 0) = x := by
  apply PiLp.ext; intro i
  simp only [single_apply,eq_iff_true_of_subsingleton,ite_true]
  rw [Subsingleton.elim 0 i]

lemma unitInterval.image_val' {s : Set unitInterval} : val' '' s = {x | proj' x ∈ s ∧ x 0 ∈ unitInterval} := by
  ext x
  rw [Set.mem_setOf_eq,Set.mem_image]
  refine' ⟨fun ⟨t,ht⟩ => _,fun hx => ⟨proj' x,⟨hx.1,_⟩⟩⟩
  simp [ht.2.symm,val',proj',ht.1,t.2.1,t.2.2]
  simp [val',proj',Set.projIcc,hx.2.1,hx.2.2,EuclideanSpace.single_eq_self]

lemma unitInterval.range_val' : Set.range val' = {x | x 0 ∈ unitInterval} := by
  simp_rw [←Set.image_univ,image_val',Set.mem_univ,true_and]

lemma EuclideanSpace.single_sub {ι : Type u_1} {𝕜 : Type u_2} [IsROrC 𝕜] [Fintype ι] [DecidableEq ι]
    (i : ι) (a : 𝕜) (b : 𝕜) : single i (a - b) = single i a - single i b:= by
  apply PiLp.ext; intro j
  by_cases h : j = i
  all_goals simp [h]

lemma EuclideanSpace.cont_single {ι : Type u_1} {𝕜 : Type u_2} [IsROrC 𝕜] [Fintype ι] [DecidableEq ι]
    (i : ι) : Continuous (fun (a : 𝕜) => EuclideanSpace.single i a) := by
  have h : (fun (a : 𝕜) => single i a) = (equiv ι 𝕜).symm ∘ Pi.single i := funext fun a => by simp
  rw [h]
  refine' (equiv ι 𝕜).continuous_invFun.comp (@continuous_single ι (fun _i => 𝕜) _ _ _ i)

lemma unitInterval.smooth_val : Smooth (𝓡∂ 1) 𝓘(ℝ, ℝ) ((↑) : unitInterval → ℝ) := fun t => by
  have hS : ∀ s:ℝ, s<1 → {x : ℝ¹ | x 0 ≤ 1} ∈ nhds (fun _i => s : ℝ¹) := fun s hs => by
    have  hS'' : ({x | x 0 ≤ 1} : Set (Fin 1 → ℝ)) = Set.pi Set.univ (fun i => Set.Iic 1) := by
      simp [Set.pi,Unique.forall_iff]
    simp_rw [EuclideanSpace,PiLp,hS'']
    exact set_pi_mem_nhds Set.finite_univ (Unique.forall_iff.mpr (fun _i => Iic_mem_nhds hs))
  refine' ⟨continuous_subtype_val.continuousWithinAt,_⟩
  by_cases ht : t.val < 1
  all_goals simp only [ContDiffWithinAtProp,mfld_simps,chartAt,ChartedSpace.chartAt,ht,ite_true,
    ite_false,IccLeftChart,IccRightChart,Function.comp,modelWithCornersEuclideanHalfSpace,
    Function.update_same,add_zero,sub_zero,Set.range,EuclideanHalfSpace,Subtype.exists,exists_prop,
    exists_eq_right]
  apply (contDiffWithinAt_inter (hS t ht)).mp
  refine' (EuclideanSpace.proj 0).contDiff.contDiffWithinAt.congr' (fun x hx => _) t.prop
  simp [hx.1.out,hx.2.out]
  apply (contDiffWithinAt_inter (hS (1-t) (by linarith))).mp
  exact ((contDiff_const (c := 1)).sub (EuclideanSpace.proj 0).contDiff).contDiffWithinAt.congr'
    (fun x hx => by simp [hx.1.out,hx.2.out]) (by simp [t.2.1,t.2.2])

lemma unitInterval.smoothOn_proj : SmoothOn 𝓘(ℝ, ℝ) (𝓡∂ 1) proj unitInterval := fun x hx => by
  refine' ⟨(continuous_projIcc (h := zero_le_one)).continuousWithinAt,_⟩
  by_cases hx' : x < 1
  all_goals simp only [ContDiffWithinAtProp,mfld_simps,chartAt,ChartedSpace.chartAt,val_proj hx,hx',
    ite_true,ite_false,IccLeftChart,IccRightChart,modelWithCornersEuclideanHalfSpace,Function.comp]
  --refine' (contDiffWithinAt_pi (ι := Fin 1) (F' := fun i => ℝ))).mpr _
  --refine' (contDiffWithinAt_id).congr' _ _
  all_goals sorry

-- TODO: abolish
lemma unitInterval.smooth_val' : Smooth (𝓡∂ 1) (𝓡 1) val' := fun t => by
  have hS : ∀ s:ℝ, s<1 → {x : ℝ¹ | x 0 ≤ 1} ∈ nhds (fun _i => s : ℝ¹) := fun s hs => by
    have  hS'' : ({x | x 0 ≤ 1} : Set (Fin 1 → ℝ)) = Set.pi Set.univ (fun i => Set.Iic 1) := by
      simp [Set.pi,Unique.forall_iff]
    simp_rw [EuclideanSpace,PiLp,hS'']
    exact set_pi_mem_nhds Set.finite_univ (Unique.forall_iff.mpr (fun _i => Iic_mem_nhds hs))
  refine' ⟨_,_⟩
  have h : val' = (EuclideanSpace.single (0 : Fin 1)) ∘ Subtype.val := funext fun t => by simp [val']
  rw [h]
  exact ((EuclideanSpace.cont_single 0).comp continuous_subtype_val).continuousWithinAt
  simp_rw [ContDiffWithinAtProp,Function.comp,chartAt,ChartedSpace.chartAt,coe_symm_eq,sub_lt_self_iff,Set.preimage_univ,Set.univ_inter]
  by_cases ht : t.val < 1
  all_goals simp_rw [ht,ite_true,ite_false,val',modelWithCornersSelf_coe,LocalHomeomorph.refl_apply,
    id_eq,modelWithCornersEuclideanHalfSpace,ModelWithCorners.mk_coe,ModelWithCorners.mk_symm,
    IccLeftChart,IccRightChart,LocalHomeomorph.mk_coe_symm,LocalEquiv.coe_symm_mk,
    LocalHomeomorph.mk_coe,add_zero,sub_zero,Function.update_same,Set.range,EuclideanHalfSpace,
    Subtype.exists,exists_prop,exists_eq_right]
  apply (contDiffWithinAt_inter (hS t ht)).mp
  refine' contDiffWithinAt_id.congr' (fun x hx => _) t.prop
  simp [hx.1.out,hx.2.out,EuclideanSpace.single_eq_self]
  apply (contDiffWithinAt_inter (hS (1-t) (by linarith))).mp
  refine' ((contDiffWithinAt_const).sub contDiffWithinAt_id).congr' (fun x hx => _) _
  use EuclideanSpace.single 0 1
  simp [hx.1.out,hx.2.out,EuclideanSpace.single_sub,EuclideanSpace.single_eq_self]
  simp [t.2.1,t.2.2]

lemma unitInterval.smoothOn_proj' : SmoothOn (𝓡 1) (𝓡∂ 1) proj' {x | x 0 ∈ unitInterval} := fun x hx => by
  refine' ⟨_,_⟩
  have h : proj' = Set.projIcc 0 1 zero_le_one ∘ EuclideanSpace.proj 0 := funext fun t => by simp [proj']
  rw [h]
  refine' (continuous_projIcc.comp (EuclideanSpace.proj (0:Fin 1)).cont).continuousWithinAt
  simp_rw [ContDiffWithinAtProp,Function.comp,chartAt,ChartedSpace.chartAt,coe_symm_eq,sub_lt_self_iff,Set.preimage_univ,Set.univ_inter]
  by_cases ht' : (proj' x).val < 1
  all_goals simp_rw [ht',ite_true,ite_false,proj',modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,LocalHomeomorph.refl_symm,LocalHomeomorph.refl_apply,
    id_eq,Set.preimage_id,modelWithCornersEuclideanHalfSpace,ModelWithCorners.mk_coe,ModelWithCorners.mk_symm,
    IccLeftChart,IccRightChart,LocalHomeomorph.mk_coe_symm,LocalEquiv.coe_symm_mk,
    LocalHomeomorph.mk_coe,add_zero,sub_zero,Function.update_same,Set.range,id_eq,exists_eq,
    Set.setOf_true,Set.inter_univ,Set.mem_Icc]
  refine' contDiffWithinAt_id.congr' (fun y hy => PiLp.ext fun i => _) hx
  simp only [Set.coe_projIcc,ge_iff_le,hy.out.2,min_eq_right,hy.out.1,max_eq_right,id_eq]
  rw [Subsingleton.elim 0 i]
  refine' (contDiffWithinAt_const.sub contDiffWithinAt_id).congr' (fun y hy => PiLp.ext fun i => _) hx
  use EuclideanSpace.single 0 1
  have hyi : y i = y 0 := by rw [Subsingleton.elim 0 i]
  simp [Set.coe_projIcc,hy.out.1,hy.out.2,hyi]

lemma unitInterval.mfderiv_val {t : unitInterval} : mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) Subtype.val t =
    if t.val < 1 then EuclideanSpace.proj 0 else -EuclideanSpace.proj 0 := by
  have hS : ∀ s:ℝ, s<1 → {x : ℝ¹ | x 0 ≤ 1} ∈ nhds (fun _i => s : ℝ¹) := fun s hs => by
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
  simp_rw [mfderiv,smooth_val.mdifferentiableAt,ite_true]
  by_cases ht : t.val < 1
  all_goals simp only [chartAt,ChartedSpace.chartAt,ht,ite_true,ite_false,mfld_simps,Function.comp,
    IccLeftChart,IccRightChart,modelWithCornersEuclideanHalfSpace,Function.update_same,add_zero,
    sub_zero,Set.range,EuclideanHalfSpace,Subtype.exists,exists_prop,exists_eq_right]
  rw [←fderivWithin_inter (hS t ht),fderivWithin_congr' (f := (EuclideanSpace.proj (0 : Fin 1)))
    (fun x hx => by simp [hx.1.out,hx.2.out]) (by simp [t.2.1,t.2.2]),
    ContinuousLinearMap.fderivWithin _ (hS' t)]
  rw [←fderivWithin_inter (hS (1-t) (by linarith)),
    fderivWithin_congr' (f := fun x => 1 - (EuclideanSpace.proj 0 : ℝ¹ → ℝ) x)
    (fun x hx => by simp [hx.1.out,hx.2.out]) (by simp [t.2.1,t.2.2]),
    fderivWithin_const_sub ((by simp : (1 - t.val) = (symm t).val) ▸ (hS' (symm t))),
    ContinuousLinearMap.fderivWithin _ ((by simp : (1 - t.val) = (symm t).val) ▸ (hS' (symm t)))]

-- TODO : remove coercion once `EuclideanSpace.single 0` is registered as a continuous linear map
lemma unitInterval.coe_mfderivWithin_proj {t : unitInterval} :
    ↑(mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1) proj unitInterval t.val : ℝ → ℝ¹) =
      (if t.val < 1 then EuclideanSpace.single 0 else - EuclideanSpace.single 0 : ℝ → ℝ¹) := by
  have h : mfderivWithin (𝓡∂ 1) (𝓡∂ 1) id Set.univ t = ContinuousLinearMap.id ℝ ℝ¹ :=
    mfderivWithin_id (𝓡∂ 1) (uniqueMDiffWithinAt_univ (𝓡∂ 1))
  rw [←proj_comp_val,mfderivWithin_comp t
      (smoothOn_proj.mdifferentiableOn t.val (by simp [t.2.1,t.2.2]))
      smooth_val.mdifferentiableWithinAt
      (by convert Set.univ.subset_preimage_image _; rw [Set.image_univ,Subtype.range_val])
      (uniqueMDiffWithinAt_univ _),
    mfderivWithin_univ,mfderiv_val] at h
  rw [←Function.comp.left_id (EuclideanSpace.single 0),←@ContinuousLinearMap.coe_id' ℝ _ ℝ¹,←h]
  ext
  by_cases ht : t.val < 1
  all_goals simp [ht,TangentSpace]

lemma unitInterval.mdifferentiableWithinAt_iff_differentiableWithinAt {f : unitInterval → unitInterval}
    {s : Set unitInterval} {t : unitInterval} : MDifferentiableWithinAt (𝓡∂ 1) (𝓡∂ 1) f s t ↔
      DifferentiableWithinAt ℝ (val' ∘ f ∘ proj') (val' '' s) (val' t) := by
  refine' ⟨fun hf => _,fun hf => _⟩
  have h : MDifferentiableWithinAt (𝓡 1) (𝓡 1) (val' ∘ f ∘ proj') (val' '' s) (val' t) := by
    refine' smooth_val'.mdifferentiableWithinAt.comp _ _ Set.subset_preimage_univ
    refine' MDifferentiableWithinAt.comp _ ((unitInterval.proj'_val' t).symm ▸ hf) _ _
    exact (smoothOn_proj'.mdifferentiableOn _ (by simp [val',t.2.1,t.2.2])).mono (by simp [image_val'])
    simp [Set.preimage_comp.symm,proj'_comp_val',subset_refl]
  replace h := h.2
  simp_rw [ContDiffWithinAtProp,modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,chartAt,
    ChartedSpace.chartAt,LocalHomeomorph.refl_symm,LocalHomeomorph.refl_apply,Set.preimage_id,
    Function.comp.right_id,Function.comp.left_id,id_eq,Set.range_id,Set.inter_univ] at h
  exact h
  have hf' : f = proj' ∘ (val' ∘ f ∘ proj') ∘ val' := funext fun t => by simp [val',proj']
  rw [hf']
  refine' (smoothOn_proj'.mdifferentiableOn _ (by simp [val',proj',(f t).2.1,(f t).2.2])).comp t _ _
  refine' MDifferentiableWithinAt.comp t _ smooth_val'.mdifferentiableWithinAt (s.subset_preimage_image _)
  exact ⟨hf.continuousWithinAt,by simp [hf]⟩
  exact (fun t _ht => by simp [val',proj',(f t).2.1,(f t).2.2])

lemma unitInterval.contMDiffWithinAt_iff_contDiffWithinAt {n : ℕ∞} {f : unitInterval → unitInterval}
    {s : Set unitInterval} {t : unitInterval} : ContMDiffWithinAt (𝓡∂ 1) (𝓡∂ 1) n f s t ↔
      ContDiffWithinAt ℝ n (val' ∘ f ∘ proj') (val' '' s) (val' t) := by
  refine' ⟨fun hf => _,fun hf => _⟩
  have h : ContMDiffWithinAt (𝓡 1) (𝓡 1) n (val' ∘ f ∘ proj') (val' '' s) (val' t) := by
    refine' smooth_val'.smoothAt.smoothWithinAt.contMDiffWithinAt.comp _ _ (Set.mapsTo_univ _ _)
    refine' ContMDiffWithinAt.comp _ ((unitInterval.proj'_val' t).symm ▸ hf) _ _
    exact (smoothOn_proj'.contMDiffOn _ (by simp [val',t.2.1,t.2.2])).mono (by simp [image_val'])
    simp [proj'_comp_val',Set.mapsTo_id]
  replace h := h.2
  simp_rw [ContDiffWithinAtProp,modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,chartAt,
    ChartedSpace.chartAt,LocalHomeomorph.refl_symm,LocalHomeomorph.refl_apply,Set.preimage_id,
    Function.comp.right_id,Function.comp.left_id,id_eq,Set.range_id,Set.inter_univ] at h
  exact h
  have hf' : f = proj' ∘ (val' ∘ f ∘ proj') ∘ val' := funext fun t => by simp [val',proj']
  rw [hf']
  refine' (smoothOn_proj'.contMDiffOn _ (by simp [val',proj',(f t).2.1,(f t).2.2])).comp t _ _
  refine' ContMDiffWithinAt.comp t _ smooth_val'.smoothAt.smoothWithinAt.contMDiffWithinAt (s.mapsTo_image _)
  exact ⟨hf.continuousWithinAt,by simp [ContDiffWithinAtProp,hf]⟩
  exact (fun t _ht => by simp [val',proj',(f t).2.1,(f t).2.2])

lemma unitInterval.smoothWithinAt_iff_contDiffWithinAt {f : unitInterval → unitInterval} {s : Set unitInterval}
    {t : unitInterval} : SmoothWithinAt (𝓡∂ 1) (𝓡∂ 1) f s t ↔
      ContDiffWithinAt ℝ ⊤ (val' ∘ f ∘ proj') (val' '' s) (val' t) := by
  rw [SmoothWithinAt]
  exact contMDiffWithinAt_iff_contDiffWithinAt

lemma unitInterval.smooth_symm : Smooth (𝓡∂ 1) (𝓡∂ 1) unitInterval.symm := fun t => by
  apply smoothWithinAt_iff_contDiffWithinAt.mpr
  have h : ∀ x ∈ val' '' Set.univ, (val' ∘ unitInterval.symm ∘ proj') x =
      (Function.const ℝ¹ (EuclideanSpace.single 0 1 : ℝ¹) - @id ℝ¹) x := fun x hx => by
    have hx' := (range_val' ▸ (Set.image_univ ▸ hx)).out
    simp [val',proj',Set.coe_projIcc,hx'.1,hx'.2,EuclideanSpace.single_sub,EuclideanSpace.single_eq_self]
  refine' ContDiffWithinAt.congr' _ h (Set.image_univ ▸ (Set.mem_range_self t))
  refine' contDiffWithinAt_const.sub contDiffWithinAt_id

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

lemma Path.symm_mdifferentiableWithinAt_iff {p q : M} {γ : Path p q} {s : Set unitInterval}
    {t : unitInterval} : MDifferentiableWithinAt (𝓡∂ 1) I γ.symm s t ↔
      MDifferentiableWithinAt (𝓡∂ 1) I γ (unitInterval.symm '' s) (unitInterval.symm t) := by
  have h {p q : M} (γ : Path p q) (s : Set unitInterval) (t : unitInterval) : MDifferentiableWithinAt (𝓡∂ 1) I γ.symm s t →
      MDifferentiableWithinAt (𝓡∂ 1) I γ (unitInterval.symm '' s) (unitInterval.symm t) := fun h' => by
    rw [←Function.comp.right_id γ,←unitInterval.symm_comp_symm,←Function.comp.assoc _ _ _]
    rw [←unitInterval.symm_symm_image s,←unitInterval.symm_symm t] at h'
    exact h'.comp _ unitInterval.smooth_symm.mdifferentiableWithinAt (Set.subset_preimage_image _ _)
  have h' := h γ.symm (unitInterval.symm '' s) (unitInterval.symm t)
  rw [unitInterval.symm_symm_image s,unitInterval.symm_symm t,Path.symm_symm] at h'
  exact ⟨h γ s t,h'⟩

lemma Path.symm_mdifferentiableAt_iff {p q : M} {γ : Path p q} {t : unitInterval} :
    MDifferentiableAt (𝓡∂ 1) I γ.symm t ↔ MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.symm t) := by
  have h {p q : M} (γ : Path p q) (t : unitInterval) :
      MDifferentiableAt (𝓡∂ 1) I γ.symm t → MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.symm t) := fun h' => by
    rw [←Function.comp.right_id γ,←unitInterval.symm_comp_symm,←Function.comp.assoc _ _ _]
    exact MDifferentiableAt.comp (unitInterval.symm t) ((unitInterval.symm_symm t).symm ▸ h') unitInterval.smooth_symm.mdifferentiableAt
  have h' := unitInterval.symm_symm t ▸ (@Path.symm_symm _ _ _ _ γ) ▸ (h γ.symm (unitInterval.symm t))
  exact ⟨h γ t,h'⟩

lemma Path.pathderivWithin_of_symm {p q : M} {γ : Path p q} {s : Set unitInterval}
    {t : unitInterval} (hst : UniqueMDiffWithinAt (𝓡∂ 1) s t) : pathderivWithin I γ.symm s t =
      -pathderivWithin I γ (unitInterval.symm '' s) (unitInterval.symm t) := by
  rw [pathderivWithin,pathderivWithin]
  by_cases hγ : MDifferentiableWithinAt (𝓡∂ 1) I γ (unitInterval.symm '' s) (unitInterval.symm t)
  rw [Path.symm,Path.coe_mk_mk,mfderivWithin_comp t hγ unitInterval.smooth_symm.mdifferentiableWithinAt
    (s.subset_preimage_image unitInterval.symm) hst,
    mfderivWithin_subset s.subset_univ hst unitInterval.smooth_symm.mdifferentiableWithinAt,
    mfderivWithin_univ]
  by_cases ht : 0 < t.val ∧ t.val < 1
  simp [unitInterval.mfderiv_symm,ht]
  obtain ht' | ht' := not_and_or.mp ht
  simp [unitInterval.mfderiv_symm,ht',lt_of_le_of_lt (le_of_not_lt ht') zero_lt_one]
  simp [unitInterval.mfderiv_symm,ht',lt_of_lt_of_le zero_lt_one (le_of_not_lt ht')]
  have hγ' := (not_iff_not.mpr (symm_mdifferentiableWithinAt_iff I)).mpr hγ
  simp [mfderivWithin_zero_of_not_mdifferentiableWithinAt hγ,
    mfderivWithin_zero_of_not_mdifferentiableWithinAt hγ']

lemma Path.pathderiv_of_symm {p q : M} {γ : Path p q} {t : unitInterval} : pathderiv I γ.symm t =
    -pathderiv I γ (unitInterval.symm t) := by
  have h : Set.range unitInterval.symm = Set.univ := unitInterval.symm_toDiffeomorph.toEquiv.range_eq_univ
  rw [←pathderivWithin_univ,pathderivWithin_of_symm I (uniqueMDiffWithinAt_univ (𝓡∂ 1))]
  simp [h]

lemma unitInterval.one_half_mem : 1 / 2 ∈ unitInterval := div_mem zero_le_one zero_le_two one_le_two

def unitInterval.one_half : unitInterval := ⟨1 / 2,one_half_mem⟩

@[simp]
lemma unitInterval.coe_one_half : one_half.val = 1 / 2 := rfl

@[simp]
lemma unitInterval.symm_one_half : symm one_half = one_half := by
  ext; rw [coe_symm_eq, coe_one_half]; ring

def unitInterval.double : unitInterval → unitInterval := fun t => Set.projIcc 0 1 zero_le_one (2*t)

def unitInterval.double' : unitInterval → unitInterval := fun t => Set.projIcc 0 1 zero_le_one (2*t-1)

lemma unitInterval.continuous_double : Continuous unitInterval.double :=
  continuous_projIcc.comp ((continuous_mul_left 2).comp continuous_subtype_val)

lemma unitInterval.continuous_double' : Continuous unitInterval.double' :=
  continuous_projIcc.comp (((continuous_mul_left 2).comp continuous_subtype_val).sub continuous_const)

@[simp]
lemma unitInterval.coe_double_eq (t : unitInterval) : (unitInterval.double t) = min 1 (2*t.val) := by
  simp [double,Set.coe_projIcc,t.2.1]

@[simp]
lemma unitInterval.coe_double'_eq (t : unitInterval) : (unitInterval.double' t) = max 0 (2*t.val-1) := by
  have h : (2:ℝ)-1 = 1 := (eq_sub_of_add_eq one_add_one_eq_two).symm
  have h' := h ▸ (sub_le_sub_right ((mul_le_iff_le_one_right zero_lt_two).mpr t.2.2) 1)
  simp [double',Set.coe_projIcc,t.2.2,min_eq_right h']

lemma unitInterval.double_zero : double 0 = 0 := by ext; simp

lemma unitInterval.double'_zero : double' 0 = 0 := by ext; simp

lemma unitInterval.double_one_half : double one_half = 1 := by ext; simp

lemma unitInterval.double'_one_half : double' one_half = 0 := by ext; simp

lemma unitInterval.double_one : double 1 = 1 := by ext; simp [one_le_two]

lemma unitInterval.double'_one : double' 1 = 1 := by ext; simp [(by ring : (2 : ℝ) - 1 = 1)]

lemma unitInterval.smoothOn_double :
    SmoothOn (𝓡∂ 1) (𝓡∂ 1) unitInterval.double {s | s.val ≤ 1 / 2} := fun t ht => by
  refine' (smoothWithinAt_iff_contDiffWithinAt.mpr _).contMDiffWithinAt
  have hs : val' '' {s | s.val ≤ 1 / 2} = {x | 0 ≤ x 0 ∧ x 0 ≤ 1 / 2} := Set.ext fun x => by
    simp_rw [Set.image,val',Set.mem_setOf_eq]
    refine' ⟨fun ⟨a,ha⟩ => _,fun hx => _⟩
    have ha' := (congr ha.2 (rfl : (0 : Fin 1) = 0))
    simp_rw [EuclideanSpace.single_apply,ite_true] at ha'
    exact And.intro (ha' ▸ a.2.1) (ha' ▸ ha.1)
    exact ⟨⟨x 0,⟨hx.1,hx.2.trans one_half_lt_one.le⟩⟩,⟨hx.2,EuclideanSpace.single_eq_self⟩⟩
  rw [hs]
  refine' (contDiffWithinAt_id.const_smul (2:ℝ)).congr' (fun y hy => PiLp.ext fun i => _) _
  rw [Subsingleton.elim i 0]
  simp [val',double,proj',Set.coe_projIcc,hy.out.1,hy.out.2.trans one_half_lt_one.le,
    (le_div_iff' zero_lt_two).mp hy.out.2]
  simp [val',t.2.1,(one_div (2 : ℝ)) ▸ ht.out]

lemma unitInterval.smoothAt_double {t : unitInterval} (ht : t.val < 1 / 2) :
    SmoothAt (𝓡∂ 1) (𝓡∂ 1) unitInterval.double t := by
  refine' smoothOn_double.smoothAt ((mem_nhds_subtype unitInterval t _).mpr _)
  exact  ⟨Set.Iic (1/2),⟨Iic_mem_nhds ht,by simp [Set.preimage]⟩⟩

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

lemma unitInterval.smoothOn_double' :
    SmoothOn (𝓡∂ 1) (𝓡∂ 1) unitInterval.double' {s | 1 / 2 ≤ s.val} := by
  rw [unitInterval.double'_eq_symm_double_symm]
  refine' smooth_symm.comp_smoothOn (smoothOn_double.comp smooth_symm.smoothOn _)
  refine' Set.MapsTo.subset_preimage (fun t ht => _)
  rw [Set.mem_setOf_eq,coe_symm_eq]; linarith [ht.out]

lemma unitInterval.smoothAt_double' {t : unitInterval} (ht : (t : ℝ) > 1 / 2) :
    SmoothAt (𝓡∂ 1) (𝓡∂ 1) unitInterval.double' t := by
  rw [unitInterval.double'_eq_symm_double_symm]
  have ht' : (symm t : ℝ) < 1 / 2 := by rw [coe_symm_eq]; linarith
  exact ((smooth_symm.smoothAt)).comp t ((smoothAt_double ht').comp t (smooth_symm.smoothAt))

lemma unitInterval.mfderivWithin_double {t : unitInterval} (ht : t.val ≤ 1 / 2) :
    mfderivWithin (𝓡∂ 1) (𝓡∂ 1) double {t | t.val ≤ 1 / 2} t = if t.val < 1 / 2
      then (2 : ℝ) • (ContinuousLinearMap.id ℝ ℝ¹) else (-2 : ℝ) • (ContinuousLinearMap.id ℝ ℝ¹) := by
  have hs : UniqueDiffWithinAt ℝ ({x | 0 ≤ x 0} ∩ {x | x 0 ≤ 1 / 2} : Set ℝ¹) (fun _i => t) := by
    have h := UniqueDiffOn.univ_pi (Fin 1) _ _ (fun _i => uniqueDiffOn_Icc one_half_pos)
    simp_rw [Set.pi,Unique.forall_iff] at h
    exact h _ ⟨t.2.1,ht⟩
  by_cases ht' : t.val < 1 / 2
  all_goals simp only [mfderivWithin,smoothOn_double.mdifferentiableOn t ht,ite_true,ite_false,
    mfld_simps,chartAt,ChartedSpace.chartAt,lt_of_le_of_lt ht one_half_lt_one,coe_double_eq,
    min_lt_iff,lt_irrefl,false_or,(lt_div_iff' zero_lt_two : t.val < 1 / 2 ↔ _).symm,ht']
  all_goals simp only [Function.comp,mfld_simps,IccLeftChart,IccRightChart,double,Set.projIcc,
    modelWithCornersEuclideanHalfSpace,Function.update_same,add_zero,sub_zero,Set.preimage_setOf_eq,
    min_le_iff,one_half_lt_one.not_le,or_false,max_le_iff,one_half_pos.le]
  all_goals rw [Subtype.range_coe_subtype,Set.inter_comm]
  rw [fderivWithin_congr' (_ : Set.EqOn _ (fun x => (2 : ℝ) • id x) _) _,
    fderivWithin_const_smul hs differentiableWithinAt_id,fderivWithin_id hs]
  exact fun x hx => PiLp.ext (Unique.forall_iff.mpr (by
    simp [hx.1.out,hx.2.out.trans one_half_lt_one.le,(le_div_iff' zero_lt_two).mp hx.2.out]))
  exact ⟨t.2.1,ht⟩
  rw [fderivWithin_congr' (_ : Set.EqOn _ (fun x => (EuclideanSpace.single 0 1 : ℝ¹) - (2 : ℝ) • id x) _) _,
    fderivWithin_const_sub hs _,fderivWithin_const_smul hs differentiableWithinAt_id,
    fderivWithin_id hs,neg_smul]
  exact fun x hx => PiLp.ext (Unique.forall_iff.mpr (by
    simp [hx.1.out,hx.2.out.trans one_half_lt_one.le,(le_div_iff' zero_lt_two).mp hx.2.out]))
  exact ⟨t.2.1,ht⟩

lemma unitInterval.mfderivWithin_double' {t : unitInterval} (ht : 1 / 2 ≤ t.val) :
    mfderivWithin (𝓡∂ 1) (𝓡∂ 1) double' {t | 1 / 2 ≤ t.val} t =
      (2 : ℝ) • (ContinuousLinearMap.id ℝ ℝ¹) := by
  have hs {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ ({x | a ≤ x 0} ∩ {x | x 0 ≤ b} : Set ℝ¹) := by
    have h := UniqueDiffOn.univ_pi (Fin 1) _ _ (fun _i => uniqueDiffOn_Icc hab)
    simp_rw [Set.pi,Unique.forall_iff] at h
    exact h
  have hs' := hs one_half_pos (fun _i => 1 - t) ⟨(symm t).2.1,(by linarith [ht] : 1 - t.val ≤ 1 / 2)⟩
  have hs'' := hs one_half_lt_one (fun _i => t) ⟨ht,t.2.2⟩
  by_cases ht' : t.val < 1
  all_goals simp only [mfderivWithin,smoothOn_double'.mdifferentiableOn t ht,ite_true,ite_false,ht',
    mfld_simps,chartAt,ChartedSpace.chartAt,coe_double'_eq,max_lt_iff,zero_lt_one,sub_lt_iff_lt_add,
    one_add_one_eq_two,(@lt_div_iff' ℝ _ _ _ _ two_pos).symm,@div_self ℝ _ _ two_ne_zero]
  all_goals simp only [Function.comp,mfld_simps,IccLeftChart,IccRightChart,double',Set.projIcc,
    modelWithCornersEuclideanHalfSpace,Function.update_same,add_zero,sub_zero,Set.preimage_setOf_eq,
    le_min_iff,le_max_iff,one_half_lt_one.le,one_half_pos.not_le,or_false,one_half_pos.le,
    (le_sub_comm : (1 / 2 : ℝ) ≤ _ ↔ _),max_le_iff,(by ring : (1 : ℝ) - 1 / 2 = 1 / 2)]
  all_goals rw [Subtype.range_coe_subtype,Set.inter_comm]
  rw [Set.inter_eq_self_of_subset_right (fun x hx => by exact one_half_pos.le.trans hx.out),
    ←fderivWithin_inter (_ : {x | x 0 ≤ (1 : ℝ)} ∈ _),
    fderivWithin_congr' (_ : Set.EqOn _ (fun x => (2 : ℝ) • id x - (EuclideanSpace.single 0 1 : ℝ¹)) _) _,
    fderivWithin_sub_const hs'' _,fderivWithin_const_smul hs'' differentiableWithinAt_id _,
    fderivWithin_id hs'']
  exact fun x hx => PiLp.ext (Unique.forall_iff.mpr (by
    simp [one_half_pos.le.trans hx.1.out,hx.2.out,(div_le_iff' two_pos).mp hx.1.out,
      min_eq_right (by linarith [hx.2.out] : (2 : ℝ) * x 0 - 1 ≤ 1)]))
  exact ⟨ht,t.2.2⟩
  convert set_pi_mem_nhds Set.finite_univ (fun _i _hi => Iic_mem_nhds ht')
  exact Set.ext fun x => by rw [Set.mem_univ_pi,Unique.forall_iff]; rfl
  infer_instance
  rw [fderivWithin_congr' (_ : Set.EqOn _ (fun x => (2 : ℝ) • id x) _) _,
    fderivWithin_const_smul hs' differentiableWithinAt_id _,fderivWithin_id hs']
  exact fun x hx => PiLp.ext (Unique.forall_iff.mpr (by
    simp_rw [id_eq,PiLp.smul_apply,smul_eq_mul,Fin.default_eq_zero,max_eq_left hx.1.out]
    rw [@max_eq_left _ _ _ 0,min_eq_right,max_eq_right]; ring
    all_goals linarith [hx.1.out,hx.2.out]))
  exact ⟨(symm t).2.1,(by linarith [ht] : 1 - t.val ≤ 1 / 2)⟩

lemma unitInterval.uniqueMDiffWithinAt_iff {s : Set unitInterval} {t : unitInterval} :
    UniqueMDiffWithinAt (𝓡∂ 1) s t ↔ UniqueDiffWithinAt ℝ (Subtype.val '' s) t := by
  rw [←uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
  refine' ⟨fun h => _,fun h => _⟩
  refine' h.image_denseRange smooth_val.mdifferentiableWithinAt.hasMFDerivWithinAt _
  rw [mfderivWithin_subset s.subset_univ h smooth_val.mdifferentiableWithinAt,mfderivWithin_univ,
    mfderiv_val]
  refine' ((Function.rightInverse_iff_comp (f := (if t.val < 1 then EuclideanSpace.single 0
      else -EuclideanSpace.single 0 : ℝ → ℝ¹))).mpr _).surjective.denseRange
  exact funext fun s => if ht : t.val < 1 then by simp [ht] else by simp [ht]
  rw [←proj_val t,←Set.image_id s,←proj_comp_val,Set.image_comp]
  refine' h.image_denseRange ((smoothOn_proj.mdifferentiableOn t.1 t.2).mono _).hasMFDerivWithinAt _
  simp
  rw [mfderivWithin_subset (Subtype.coe_image_subset _ s) h (smoothOn_proj.mdifferentiableOn _ t.2),
    coe_mfderivWithin_proj]
  refine' ((Function.rightInverse_iff_comp (f := (if t.val < 1 then EuclideanSpace.proj 0
      else -EuclideanSpace.proj 0 : ℝ¹ →L[ℝ] ℝ))).mpr _).surjective.denseRange
  ext x i; by_cases ht : t.val < 1
  all_goals simp [ht,((Fin.eq_zero i) ▸ rfl : x 0 = x i)]

lemma Path.trans_eqOn_left {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} :
    Set.EqOn (γ.trans γ') (γ ∘ unitInterval.double) {t | t.val ≤ 1 / 2} := fun t ht => by
  have ht' : 2 * t.val ∈ unitInterval := ⟨mul_nonneg zero_lt_two.le t.2.1,(le_div_iff' zero_lt_two).mp ht⟩
  simp [trans,(one_div (2 : ℝ)) ▸ ht.out,γ.extend_extends ht',
    Subtype.coe_eq_of_eq_mk (unitInterval.coe_double_eq t),ht'.out]

lemma Path.trans_eqOn_right {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} :
    Set.EqOn (γ.trans γ') (γ' ∘ unitInterval.double') {t | 1 / 2 ≤ t.val} := fun t ht => by
  by_cases ht' : t.val = 1 / 2
  simp [trans,(one_div (2 : ℝ)) ▸ ht',unitInterval.double']
  have ht'' := Ne.lt_of_le (Ne.symm ht') ht.out
  have ht''' : 2 * t.val - 1 ∈ unitInterval := ⟨by linarith,by linarith [t.2.2]⟩
  simp [trans,(one_div (2 : ℝ)) ▸ ht''.not_le,γ'.extend_extends ht''',
    Subtype.coe_eq_of_eq_mk (unitInterval.coe_double'_eq t),max_eq_right ht'''.out.1]

lemma Path.trans_eqOn_left' {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} :
    Set.EqOn (γ.trans γ') (γ.reparam unitInterval.double unitInterval.continuous_double
      unitInterval.double_zero unitInterval.double_one) {t | t.val ≤ 1 / 2} := Path.trans_eqOn_left

lemma Path.trans_eqOn_right' {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} :
    Set.EqOn (γ.trans γ') (γ'.reparam unitInterval.double' unitInterval.continuous_double'
      unitInterval.double'_zero unitInterval.double'_one) {t | 1 / 2 ≤ t.val} := Path.trans_eqOn_right

lemma Path.trans_mdifferentiableWithinAt_left {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    {t : unitInterval} (ht : t.val ≤ 1 / 2) {u : Set unitInterval}
    (hγ : MDifferentiableWithinAt (𝓡∂ 1) I γ u (unitInterval.double t)) :
      MDifferentiableWithinAt (𝓡∂ 1) I (γ.trans γ') (unitInterval.double ⁻¹' u ∩ {s | s.val ≤ 1 / 2}) t := by
  have hs := (unitInterval.double ⁻¹' u).inter_subset_right {s | s.val ≤ 1 / 2}
  have h := ((unitInterval.smoothOn_double t ht).mono hs).mdifferentiableWithinAt le_top
  exact (hγ.comp t h (Set.inter_subset_left _ _)).congr (fun t ht => trans_eqOn_left ht.2) (trans_eqOn_left ht)

lemma Path.trans_mdifferentiableAt_left {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    {t : unitInterval} (ht : (t : ℝ) < 1 / 2)
    (hγ : MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.double t)) :
      MDifferentiableAt (𝓡∂ 1) I (γ.trans γ') t := by
  have h := MDifferentiableAt.comp t hγ (unitInterval.smoothAt_double ht).mdifferentiableAt
  refine' h.congr_of_eventuallyEq (trans_eqOn_left.eventuallyEq_of_mem _)
  apply (mem_nhds_subtype unitInterval t {s | s.val ≤ 1 / 2}).mpr
  exact ⟨Set.Iic (1 / 2),⟨Iic_mem_nhds ht,subset_of_eq rfl⟩⟩

lemma Path.trans_mdifferentiableWithinAt_right {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    {t : unitInterval} (ht : 1 / 2 ≤ t.val) {u : Set unitInterval}
    (hγ' : MDifferentiableWithinAt (𝓡∂ 1) I γ' u (unitInterval.double' t)) :
      MDifferentiableWithinAt (𝓡∂ 1) I (γ.trans γ') (unitInterval.double' ⁻¹' u ∩ {s | 1 / 2 ≤ s.val}) t := by
  have hs := (unitInterval.double' ⁻¹' u).inter_subset_right {s | 1 / 2 ≤ s.val}
  have h := ((unitInterval.smoothOn_double' t ht).mono hs).mdifferentiableWithinAt le_top
  exact (hγ'.comp t h (Set.inter_subset_left _ _)).congr (fun t ht => trans_eqOn_right ht.2) (trans_eqOn_right ht)

lemma Path.trans_mdifferentiableAt_right {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    {t : unitInterval} (ht : (t : ℝ) > 1 / 2)
    (hγ : MDifferentiableAt (𝓡∂ 1) I γ' (unitInterval.double' t)) :
      MDifferentiableAt (𝓡∂ 1) I (γ.trans γ') t := by
  rw [←(γ.trans γ').symm_symm,Path.trans_symm]
  have ht' : (unitInterval.symm t).val < 1 / 2 := by rw [unitInterval.coe_symm_eq]; linarith
  apply (Path.symm_mdifferentiableAt_iff I).mpr
  apply Path.trans_mdifferentiableAt_left I ht'
  apply (Path.symm_mdifferentiableAt_iff I).mpr
  rw [unitInterval.double_symm,unitInterval.symm_symm]
  exact hγ

-- TODO: remove unnecessary differentiability hypothesis
lemma Path.trans_pathderivWithin_left {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    {t : unitInterval} (ht : t.val ≤ 1 / 2) {u : Set unitInterval}
    (hγ : MDifferentiableWithinAt (𝓡∂ 1) I γ u (unitInterval.double t))
    (hu : UniqueMDiffWithinAt (𝓡∂ 1) (unitInterval.double ⁻¹' u ∩ {s | s.val ≤ 1 / 2}) t) :
      pathderivWithin I (γ.trans γ') (unitInterval.double ⁻¹' u ∩ {s | s.val ≤ 1 / 2}) t =
        (2 : ℝ) • pathderivWithin I γ u (unitInterval.double t) := by
  rw [pathderivWithin_congr I hu (Path.trans_eqOn_left'.mono (Set.inter_subset_right _ _))
    (Path.trans_eqOn_left ht),pathderivWithin_reparam I _ hγ _ (Set.inter_subset_left _ _) hu,
    mfderivWithin_subset (Set.inter_subset_right _ _) hu _,unitInterval.mfderivWithin_double ht]
  by_cases ht' : t.val < 1 / 2
  simp only [ht',ite_true,ContinuousLinearMap.coe_smul',Pi.smul_apply,ContinuousLinearMap.id]
  simp [-one_div,lt_of_le_of_lt ht one_half_lt_one,(lt_div_iff' zero_lt_two).mp ht']
  simp only [ht',ite_false,ContinuousLinearMap.coe_smul',Pi.smul_apply,ContinuousLinearMap.id]
  simp [-one_div,lt_of_le_of_lt ht one_half_lt_one,ht',(lt_div_iff' zero_lt_two).not.mp ht']
  exact unitInterval.smoothOn_double.mdifferentiableOn t ht
  exact (unitInterval.smoothOn_double.mdifferentiableOn t ht).mono (Set.inter_subset_right _ _)

lemma Path.trans_pathderiv_left {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} {t : unitInterval}
    (ht : t.val ≤ 1 / 2) (hγ : MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.double t)) :
      pathderivWithin I (γ.trans γ') {s | s.val ≤ 1 / 2} t =
        (2 : ℝ) • pathderiv I γ (unitInterval.double t) := by
  rw [←pathderivWithin_univ,←Set.univ_inter {s : unitInterval | s.val ≤ 1 / 2}]
  convert Path.trans_pathderivWithin_left I ht (mdifferentiableWithinAt_univ.mpr hγ) _
  rw [Set.preimage_univ,Set.univ_inter]
  apply unitInterval.uniqueMDiffWithinAt_iff.mpr
  convert (uniqueDiffOn_Icc one_half_pos) t ⟨t.2.1,ht⟩
  convert Subtype.image_preimage_val unitInterval {s | s ≤ 1 / 2}
  ext s
  exact ⟨fun h => ⟨h.2,⟨h.1,h.2.trans one_half_lt_one.le⟩⟩,fun h => ⟨h.2.1,h.1⟩⟩

-- TODO: remove unnecessary differentiability hypothesis
lemma Path.trans_pathderivWithin_right {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    {t : unitInterval} (ht : 1 / 2 ≤ t.val) {u : Set unitInterval}
    (hγ' : MDifferentiableWithinAt (𝓡∂ 1) I γ' u (unitInterval.double' t))
    (hu : UniqueMDiffWithinAt (𝓡∂ 1) (unitInterval.double' ⁻¹' u ∩ {s | 1 / 2 ≤ s.val}) t) :
      pathderivWithin I (γ.trans γ') (unitInterval.double' ⁻¹' u ∩ {s | 1 / 2 ≤ s.val}) t =
        (2 : ℝ) • pathderivWithin I γ' u (unitInterval.double' t) := by
  sorry

lemma Path.trans_pathderiv_right {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} {t : unitInterval}
    (ht : 1 / 2 ≤ t.val) (hγ' : MDifferentiableAt (𝓡∂ 1) I γ' (unitInterval.double' t)) :
      pathderivWithin I (γ.trans γ') {s | 1 / 2 ≤ s.val} t =
        (2 : ℝ) • pathderiv I γ' (unitInterval.double' t) := by
  rw [←pathderivWithin_univ,←Set.univ_inter {s : unitInterval | 1 / 2 ≤ s.val}]
  convert Path.trans_pathderivWithin_right I ht (mdifferentiableWithinAt_univ.mpr hγ') _
  rw [Set.preimage_univ,Set.univ_inter]
  apply unitInterval.uniqueMDiffWithinAt_iff.mpr
  convert (uniqueDiffOn_Icc one_half_lt_one) t ⟨ht,t.2.2⟩
  convert Subtype.image_preimage_val unitInterval {s | 1 / 2 ≤ s}
  ext s
  exact ⟨fun h => ⟨h.1,⟨one_half_pos.le.trans h.1,h.2⟩⟩,fun h => ⟨h.1,h.2.2⟩⟩

lemma Path.trans_mdifferentiableAt_mid {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}
    (hγ : MDifferentiableAt (𝓡∂ 1) I γ 1) (hγ' : MDifferentiableAt (𝓡∂ 1) I γ' 0)
    (h : pathderiv I γ 1 = pathderiv I γ' 0) :
      MDifferentiableAt (𝓡∂ 1) I (γ.trans γ') unitInterval.one_half := by
  have hl : MDifferentiableWithinAt (𝓡∂ 1) I (γ.trans γ') {s | s.val ≤ 1 / 2} unitInterval.one_half := by
    rw [←{s : unitInterval | s.val ≤ 1 / 2}.univ_inter,←@Set.preimage_univ _ _ unitInterval.double]
    apply trans_mdifferentiableWithinAt_left I (by simp)
    exact unitInterval.double_one_half ▸ (mdifferentiableWithinAt_univ.mpr hγ)
  have hr : MDifferentiableWithinAt (𝓡∂ 1) I (γ.trans γ') {s | 1 / 2 ≤ s.val} unitInterval.one_half := by
    rw [←{s : unitInterval | 1 / 2 ≤ s.val}.univ_inter,←@Set.preimage_univ _ _ unitInterval.double']
    apply trans_mdifferentiableWithinAt_right I (by simp)
    exact unitInterval.double'_one_half ▸ (mdifferentiableWithinAt_univ.mpr hγ')
  have h' : pathderivWithin I (γ.trans γ') {s | s.val ≤ 1 / 2} unitInterval.one_half =
      pathderivWithin I (γ.trans γ') {s | 1 / 2 ≤ s.val} unitInterval.one_half := by
    rw [Path.trans_pathderiv_left I (by simp) (unitInterval.double_one_half ▸ hγ),
      Path.trans_pathderiv_right I (by simp) (unitInterval.double'_one_half ▸ hγ'),
      unitInterval.double_one_half,unitInterval.double'_one_half,h]
  have h'' : mfderivWithin (𝓡∂ 1) I (γ.trans γ') {s | s.val ≤ 1 / 2} unitInterval.one_half =
      mfderivWithin (𝓡∂ 1) I (γ.trans γ') {s | 1 / 2 ≤ s.val} unitInterval.one_half := by
    simp_rw [pathderivWithin,unitInterval.coe_one_half,one_half_lt_one,ite_true] at h'
    refine' ContinuousLinearMap.ext fun x => _
    have hx : x = (x 0) • (EuclideanSpace.single 0 1 : ℝ¹) := PiLp.ext fun i => by
      simp [((Fin.eq_zero i) ▸ rfl : x 0 = x i)]
    rw [hx,map_smul,map_smul,h']
  have hs : {s | s.val ≤ 1 / 2} ∪ {s | 1 / 2 ≤ s.val} = @Set.univ unitInterval := by
    ext; simp [le_total]
  have h''' := hs ▸ (hl.hasMFDerivWithinAt.union (h''.symm ▸ hr.hasMFDerivWithinAt))
  exact (h'''.hasMFDerivAt Filter.univ_mem).mdifferentiableAt

lemma pathderiv_of_trans {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''} {t : unitInterval} :
    pathderiv I (γ.trans γ') t =
      if ht : (t : ℝ) < 1 / 2 then
        2 • (pathderiv I γ ⟨2 * t,(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1,le_of_lt ht⟩⟩)
      else if ht : (t : ℝ) > 1 / 2 then
        2 • (pathderiv I γ ⟨2 * t - 1,unitInterval.two_mul_sub_one_mem_iff.2 ⟨le_of_lt ht, t.2.2⟩⟩)
      else if hp' : pathderiv I γ 1 = pathderiv I γ' 0 then pathderiv I γ 1 else 0 := by
  by_cases ht : (t : ℝ) < 1 / 2
  simp_rw [eq_true ht,dite_true]
  --simp_rw [pathderiv,eq_true (ht.trans one_half_lt_one),eq_true ((lt_div_iff' zero_lt_two).mp ht),
      --ite_true,Path.trans,Path.coe_mk_mk]
  sorry
  sorry
