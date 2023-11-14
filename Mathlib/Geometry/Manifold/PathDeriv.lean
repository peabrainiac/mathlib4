import Mathlib.Geometry.Manifold.Instances.UnitInterval
import Mathlib.Geometry.Manifold.Diffeomorph

open scoped Classical Manifold

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

universe uE uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : ModelWithCorners ℝ E E)
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

lemma pathderivWithin_subset {p q : M} {γ : Path p q} {s u : Set unitInterval} {t : unitInterval}
    (hsu : s ⊆ u) (hs : UniqueMDiffWithinAt (𝓡∂ 1) s t)
    (h : MDifferentiableWithinAt (𝓡∂ 1) I γ u t) :
      pathderivWithin I γ s t = pathderivWithin I γ u t := by
  rw [pathderivWithin,pathderivWithin,mfderivWithin_subset hsu hs h]

lemma pathderivWithin_eq_pathderiv {p q : M} {γ : Path p q} {s : Set unitInterval}
    {t : unitInterval} (hs : UniqueMDiffWithinAt (𝓡∂ 1) s t) (h : MDifferentiableAt (𝓡∂ 1) I γ t) :
      pathderivWithin I γ s t = pathderiv I γ t := by
  rw [pathderivWithin_subset I s.subset_univ hs h.mdifferentiableWithinAt,pathderivWithin_univ]

-- TODO : replace proof with `rw [pathderivWithin,pathderiv,mfderivWithin_of_mem_nhds h]`
lemma pathderivWithin_of_mem_nhds {p q : M} {γ : Path p q} {s : Set unitInterval} {t : unitInterval}
    (h : s ∈ nhds t) : pathderivWithin I γ s t = pathderiv I γ t := by
  rw [pathderivWithin,pathderiv,←mfderivWithin_univ,←s.univ_inter,mfderivWithin_inter h]

lemma pathderiv_zero_of_not_mdifferentiableAt {p q : M} {γ : Path p q} {t : unitInterval}
    (h : ¬MDifferentiableAt (𝓡∂ 1) I γ t) : pathderiv I γ t = 0 := by
  simp [pathderiv,mfderiv_zero_of_not_mdifferentiableAt h]

lemma pathderivWithin_zero_of_not_mdifferentiableWithinAt {p q : M} {γ : Path p q}
    {s : Set unitInterval} {t : unitInterval} (h : ¬MDifferentiableWithinAt (𝓡∂ 1) I γ s t) :
      pathderivWithin I γ s t = 0 := by
  simp [pathderivWithin,mfderivWithin_zero_of_not_mdifferentiableWithinAt h]

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

namespace Path

section Symm

/-! ### Differentiability and derivatives of reverses of paths. -/

variable  {p q : M} {γ : Path p q}

lemma symm_mdifferentiableWithinAt_iff {s : Set unitInterval} {t : unitInterval} :
    MDifferentiableWithinAt (𝓡∂ 1) I γ.symm s t ↔
      MDifferentiableWithinAt (𝓡∂ 1) I γ (unitInterval.symm '' s) (unitInterval.symm t) := by
  refine' ⟨fun h => symm_symm (γ := γ) ▸ _,fun h => _⟩
  rw [←unitInterval.symm_symm t] at h
  refine' h.comp _ unitInterval.smooth_symm.mdifferentiableWithinAt _
  simp [←Set.preimage_comp,subset_rfl]
  refine' h.comp _ unitInterval.smooth_symm.mdifferentiableWithinAt _
  exact s.subset_preimage_image _

lemma symm_mdifferentiableAt_iff {t : unitInterval} :
    MDifferentiableAt (𝓡∂ 1) I γ.symm t ↔ MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.symm t) := by
  have h {p q : M} (γ : Path p q) (t : unitInterval) :
      MDifferentiableAt (𝓡∂ 1) I γ.symm t → MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.symm t) := fun h' => by
    rw [←Function.comp.right_id γ,←unitInterval.symm_comp_symm,←Function.comp.assoc _ _ _]
    exact ((unitInterval.symm_symm t).symm ▸ h').comp _ unitInterval.smooth_symm.mdifferentiableAt
  have h' := unitInterval.symm_symm t ▸ (@symm_symm _ _ _ _ γ) ▸ (h γ.symm (unitInterval.symm t))
  exact ⟨h γ t,h'⟩

lemma symm_mdifferentiableOn_iff {s : Set unitInterval} :
    MDifferentiableOn (𝓡∂ 1) I γ.symm s ↔ MDifferentiableOn (𝓡∂ 1) I γ (unitInterval.symm '' s) := by
  refine' ⟨fun h t ht => _,fun h t ht => _⟩
  refine' unitInterval.symm_symm t ▸ (symm_mdifferentiableWithinAt_iff I).mp (h _ _)
  exact (unitInterval.symm_symm_image s) ▸ (Set.mem_image_of_mem _ ht)
  exact (symm_mdifferentiableWithinAt_iff I).mpr (h _ (s.mem_image_of_mem _ ht))

lemma symm_mdifferentiable_iff : MDifferentiable (𝓡∂ 1) I γ.symm ↔ MDifferentiable (𝓡∂ 1) I γ := by
  refine' ⟨fun h t => _,fun h t => _⟩
  exact unitInterval.symm_symm t ▸ (symm_mdifferentiableAt_iff I).mp (h _)
  exact (symm_mdifferentiableAt_iff I).mpr (h _)

lemma symm_contMDiffWithinAt_iff {n : ℕ∞} {s : Set unitInterval} {t : unitInterval} :
    ContMDiffWithinAt (𝓡∂ 1) I n γ.symm s t ↔
      ContMDiffWithinAt (𝓡∂ 1) I n γ (unitInterval.symm '' s) (unitInterval.symm t) := by
  refine' ⟨fun h => symm_symm (γ := γ) ▸ _,fun h => _⟩
  rw [←unitInterval.symm_symm t] at h
  refine' h.comp _ unitInterval.smooth_symm.contMDiff.contMDiffAt.contMDiffWithinAt _
  simp [Set.mapsTo_id]
  refine' h.comp _ unitInterval.smooth_symm.contMDiff.contMDiffAt.contMDiffWithinAt _
  exact s.subset_preimage_image _

lemma symm_contMDiffAt_iff {n : ℕ∞} {t : unitInterval} :
    ContMDiffAt (𝓡∂ 1) I n γ.symm t ↔ ContMDiffAt (𝓡∂ 1) I n γ (unitInterval.symm t) := by
  have h {p q : M} (γ : Path p q) (t : unitInterval) :
      ContMDiffAt (𝓡∂ 1) I n γ.symm t → ContMDiffAt (𝓡∂ 1) I n γ (unitInterval.symm t) := fun h' => by
    rw [←Function.comp.right_id γ,←unitInterval.symm_comp_symm,←Function.comp.assoc _ _ _]
    exact ((unitInterval.symm_symm t).symm ▸ h').comp _ unitInterval.smooth_symm.contMDiff.contMDiffAt
  have h' := unitInterval.symm_symm t ▸ (@symm_symm _ _ _ _ γ) ▸ (h γ.symm (unitInterval.symm t))
  exact ⟨h γ t,h'⟩

lemma symm_contMDiffOn_iff {n : ℕ∞} {s : Set unitInterval} :
    ContMDiffOn (𝓡∂ 1) I n γ.symm s ↔ ContMDiffOn (𝓡∂ 1) I n γ (unitInterval.symm '' s) := by
  refine' ⟨fun h t ht => _,fun h t ht => _⟩
  refine' unitInterval.symm_symm t ▸ (symm_contMDiffWithinAt_iff I).mp (h _ _)
  exact (unitInterval.symm_symm_image s) ▸ (Set.mem_image_of_mem _ ht)
  exact (symm_contMDiffWithinAt_iff I).mpr (h _ (s.mem_image_of_mem _ ht))

lemma symm_contMDiff_iff {n : ℕ∞} : ContMDiff (𝓡∂ 1) I n γ.symm ↔ ContMDiff (𝓡∂ 1) I n γ := by
  refine' ⟨fun h t => _,fun h t => _⟩
  exact unitInterval.symm_symm t ▸ (symm_contMDiffAt_iff I).mp (h _)
  exact (symm_contMDiffAt_iff I).mpr (h _)

lemma symm_smoothWithinAt_iff {s : Set unitInterval} {t : unitInterval} :
    SmoothWithinAt (𝓡∂ 1) I γ.symm s t ↔
      SmoothWithinAt (𝓡∂ 1) I γ (unitInterval.symm '' s) (unitInterval.symm t) :=
  symm_contMDiffWithinAt_iff I

lemma symm_smoothAt_iff {t : unitInterval} :
    SmoothAt (𝓡∂ 1) I γ.symm t ↔ SmoothAt (𝓡∂ 1) I γ (unitInterval.symm t) :=
  symm_contMDiffAt_iff I

lemma symm_smoothOn_iff {s : Set unitInterval} :
    SmoothOn (𝓡∂ 1) I γ.symm s ↔ SmoothOn (𝓡∂ 1) I γ (unitInterval.symm '' s) :=
  symm_contMDiffOn_iff I

lemma symm_smooth_iff : Smooth (𝓡∂ 1) I γ.symm ↔ Smooth (𝓡∂ 1) I γ := symm_contMDiff_iff I

lemma pathderivWithin_of_symm {s : Set unitInterval} {t : unitInterval}
    (hst : UniqueMDiffWithinAt (𝓡∂ 1) s t) : pathderivWithin I γ.symm s t =
      -pathderivWithin I γ (unitInterval.symm '' s) (unitInterval.symm t) := by
  rw [pathderivWithin,pathderivWithin]
  by_cases hγ : MDifferentiableWithinAt (𝓡∂ 1) I γ (unitInterval.symm '' s) (unitInterval.symm t)
  rw [symm,coe_mk_mk,mfderivWithin_comp t hγ unitInterval.smooth_symm.mdifferentiableWithinAt
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

lemma pathderiv_of_symm {t : unitInterval} :
    pathderiv I γ.symm t = -pathderiv I γ (unitInterval.symm t) := by
  have h : Set.range unitInterval.symm = Set.univ := unitInterval.symm_toDiffeo.toEquiv.range_eq_univ
  rw [←pathderivWithin_univ,pathderivWithin_of_symm I (uniqueMDiffWithinAt_univ (𝓡∂ 1))]
  simp [h]

end Symm

-- TODO : move to Mathlib.Topology.Connected.PathConnected
lemma coe_symm {p q : M} (γ : Path p q) : ↑γ.symm = ↑γ ∘ unitInterval.symm := rfl

section Trans

/-! ### Differentiability and derivatives of concatenations of paths. -/

variable {p p' p'' : M} {γ : Path p p'} {γ' : Path p' p''}

lemma trans_eqOn_left :
    Set.EqOn (γ.trans γ') (γ ∘ unitInterval.double) {t | t.val ≤ 1 / 2} := fun t ht => by
  have ht' : 2 * t.val ∈ unitInterval := ⟨mul_nonneg zero_lt_two.le t.2.1,(le_div_iff' zero_lt_two).mp ht⟩
  simp [trans,(one_div (2 : ℝ)) ▸ ht.out,γ.extend_extends ht',
    Subtype.coe_eq_of_eq_mk (unitInterval.coe_double_eq t),ht'.out]

lemma trans_eqOn_right :
    Set.EqOn (γ.trans γ') (γ' ∘ unitInterval.double') {t | 1 / 2 ≤ t.val} := fun t ht => by
  by_cases ht' : t.val = 1 / 2
  simp [trans,(one_div (2 : ℝ)) ▸ ht',unitInterval.double']
  have ht'' := Ne.lt_of_le (Ne.symm ht') ht.out
  have ht''' : 2 * t.val - 1 ∈ unitInterval := ⟨by linarith,by linarith [t.2.2]⟩
  simp [trans,(one_div (2 : ℝ)) ▸ ht''.not_le,γ'.extend_extends ht''',
    Subtype.coe_eq_of_eq_mk (unitInterval.coe_double'_eq t),max_eq_right ht'''.out.1]

lemma trans_eqOn_left' :
    Set.EqOn (γ.trans γ') (γ.reparam unitInterval.double unitInterval.continuous_double
      unitInterval.double_zero unitInterval.double_one) {t | t.val ≤ 1 / 2} := trans_eqOn_left

lemma trans_eqOn_right' :
    Set.EqOn (γ.trans γ') (γ'.reparam unitInterval.double' unitInterval.continuous_double'
      unitInterval.double'_zero unitInterval.double'_one) {t | 1 / 2 ≤ t.val} := trans_eqOn_right

lemma trans_comp_half :
    γ.trans γ' ∘ unitInterval.half = γ := funext fun t => by
  simp [-one_div,trans,div_le_div_of_le two_pos.le t.2.2,mul_div_cancel']

lemma trans_comp_half' :
    γ.trans γ' ∘ unitInterval.half' = γ' := funext fun t => by
  simp only [unitInterval.half'_eq_symm_half_symm,←Function.comp.assoc,←coe_symm,trans_symm,
    trans_comp_half,symm_symm]

variable (γ) (γ')

lemma trans_mdifferentiableWithinAt_left_iff {t : unitInterval} (ht : t.val ≤ 1 / 2)
    {u : Set unitInterval} :
    MDifferentiableWithinAt (𝓡∂ 1) I (γ.trans γ') (unitInterval.double ⁻¹' u ∩ {s | s.val ≤ 1 / 2}) t ↔
      MDifferentiableWithinAt (𝓡∂ 1) I γ u (unitInterval.double t) := by
  refine' ⟨fun hγ => _,fun hγ => _⟩
  rw [←trans_comp_half (γ' := γ')]
  refine' ((unitInterval.half_double ht).symm ▸ hγ).comp _ _ _
  exact unitInterval.smooth_half.mdifferentiableWithinAt
  simp [-one_div,←Set.preimage_comp,unitInterval.double_comp_half,subset_rfl,
    (show u ⊆ {s | s.val / 2 ≤ 1 / 2} by exact fun s _ => div_le_div_of_le two_pos.le s.2.2)]
  have hs := (unitInterval.double ⁻¹' u).inter_subset_right {s | s.val ≤ 1 / 2}
  have h := ((unitInterval.smoothOn_double t ht).mono hs).mdifferentiableWithinAt le_top
  exact (hγ.comp t h (Set.inter_subset_left _ _)).congr (fun t ht => trans_eqOn_left ht.2) (trans_eqOn_left ht)

lemma trans_mdifferentiableWithinAt_left_iff' {t : unitInterval} (ht : t.val ≤ 1 / 2) :
    MDifferentiableWithinAt (𝓡∂ 1) I (γ.trans γ') {s | s.val ≤ 1 / 2} t ↔
      MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.double t) := by
  rw [←mdifferentiableWithinAt_univ,←Set.univ_inter {s : unitInterval | s.val ≤ 1 / 2}]
  exact Set.preimage_univ ▸ trans_mdifferentiableWithinAt_left_iff I γ γ' ht

lemma trans_mdifferentiableAt_left_iff {t : unitInterval} (ht : t.val < 1 / 2) :
    MDifferentiableAt (𝓡∂ 1) I (γ.trans γ') t ↔
      MDifferentiableAt (𝓡∂ 1) I γ (unitInterval.double t) := by
  simp_rw [←mdifferentiableWithinAt_univ]
  rw [←mdifferentiableWithinAt_inter (t := {s | s.val ≤ 1 / 2})]
  exact Set.preimage_univ ▸ trans_mdifferentiableWithinAt_left_iff I γ γ' ht.le
  exact (mem_nhds_subtype _ t _).mpr ⟨Set.Iic (1 / 2),⟨Iic_mem_nhds ht,subset_of_eq rfl⟩⟩

lemma trans_mdifferentiableWithinAt_right_iff {t : unitInterval} (ht : 1 / 2 ≤ t.val)
    {u : Set unitInterval} :
    MDifferentiableWithinAt (𝓡∂ 1) I (γ.trans γ') (unitInterval.double' ⁻¹' u ∩ {s | 1 / 2 ≤ s.val}) t ↔
      MDifferentiableWithinAt (𝓡∂ 1) I γ' u (unitInterval.double' t) := by
  refine' ⟨fun hγ' => _, fun hγ' => _⟩
  rw [←trans_comp_half' (γ := γ)]
  refine' ((unitInterval.half'_double' ht).symm ▸ hγ').comp _ _ _
  exact unitInterval.smooth_half'.mdifferentiableWithinAt
  simp [-one_div,←Set.preimage_comp,unitInterval.double'_comp_half',subset_rfl,
    (show u ⊆ {s | 1 / 2 ≤ (s.val + 1) / 2} by exact fun s _ => Set.mem_setOf.mpr (by linarith [s.2.1]))]
  have hs := (unitInterval.double' ⁻¹' u).inter_subset_right {s | 1 / 2 ≤ s.val}
  have h := ((unitInterval.smoothOn_double' t ht).mono hs).mdifferentiableWithinAt le_top
  exact (hγ'.comp t h (Set.inter_subset_left _ _)).congr (fun t ht => trans_eqOn_right ht.2) (trans_eqOn_right ht)

lemma trans_mdifferentiableWithinAt_right_iff' {t : unitInterval} (ht : 1 / 2 ≤ t.val) :
    MDifferentiableWithinAt (𝓡∂ 1) I (γ.trans γ') {s | 1 / 2 ≤ s.val} t ↔
      MDifferentiableAt (𝓡∂ 1) I γ' (unitInterval.double' t) := by
  rw [←mdifferentiableWithinAt_univ,←Set.univ_inter {s : unitInterval | 1 / 2 ≤ s.val}]
  exact Set.preimage_univ ▸ trans_mdifferentiableWithinAt_right_iff I γ γ' ht

lemma trans_mdifferentiableAt_right_iff {t : unitInterval} (ht : t.val > 1 / 2) :
    MDifferentiableAt (𝓡∂ 1) I (γ.trans γ') t ↔
      MDifferentiableAt (𝓡∂ 1) I γ' (unitInterval.double' t) := by
  rw [←(γ.trans γ').symm_symm,trans_symm,symm_mdifferentiableAt_iff,
    trans_mdifferentiableAt_left_iff I _ _ (by rw [unitInterval.coe_symm_eq]; linarith),
    symm_mdifferentiableAt_iff,unitInterval.double_symm,unitInterval.symm_symm]

lemma trans_mdifferentiableOn_left {s : Set unitInterval} :
    MDifferentiableOn (𝓡∂ 1) I (γ.trans γ') (unitInterval.double ⁻¹' s ∩ {s | s.val ≤ 1 / 2}) ↔
      MDifferentiableOn (𝓡∂ 1) I γ s := by
  refine' ⟨fun h t ht => _,fun h t ht => _⟩
  rw [←unitInterval.double_half t,←trans_mdifferentiableWithinAt_left_iff I γ γ' _]
  exact h _ (by simp [-one_div,ht,div_le_div_of_le two_pos.le t.2.2])
  simp [-one_div,div_le_div_of_le two_pos.le t.2.2]
  refine' (trans_mdifferentiableWithinAt_left_iff I γ γ' ht.2.out).mpr (h _ _)
  exact Set.mem_preimage.mp ht.1

lemma trans_mdifferentiableOn_right {s : Set unitInterval} :
    MDifferentiableOn (𝓡∂ 1) I (γ.trans γ') (unitInterval.double' ⁻¹' s ∩ {s | 1 / 2 ≤ s.val}) ↔
      MDifferentiableOn (𝓡∂ 1) I γ' s := by
  refine' ⟨fun h t ht => _,fun h t ht => _⟩
  rw [←unitInterval.double'_half' t,←trans_mdifferentiableWithinAt_right_iff I γ γ' _]
  exact h _ (by simp [-one_div,ht,show 1 / 2 ≤ (t.val +1 ) / 2 by linarith [t.2.1]])
  simp [-one_div,show 1 / 2 ≤ (t.val +1 ) / 2 by linarith [t.2.1]]
  refine' (trans_mdifferentiableWithinAt_right_iff I γ γ' ht.2.out).mpr (h _ _)
  exact Set.mem_preimage.mp ht.1

lemma trans_contMDiffWithinAt_left_iff {n : ℕ∞} {t : unitInterval} (ht : t.val ≤ 1 / 2)
    {u : Set unitInterval} :
    ContMDiffWithinAt (𝓡∂ 1) I n (γ.trans γ') (unitInterval.double ⁻¹' u ∩ {s | s.val ≤ 1 / 2}) t ↔
      ContMDiffWithinAt (𝓡∂ 1) I n γ u (unitInterval.double t) := by
  refine' ⟨fun hγ => _,fun hγ => _⟩
  rw [←trans_comp_half (γ' := γ')]
  refine' ((unitInterval.half_double ht).symm ▸ hγ).comp _ _ _
  exact unitInterval.smooth_half.contMDiff.contMDiffAt.contMDiffWithinAt
  simp [-one_div,←Set.preimage_comp,unitInterval.double_comp_half,subset_rfl,Set.mapsTo',
    (show u ⊆ {s | s.val / 2 ≤ 1 / 2} by exact fun s _ => div_le_div_of_le two_pos.le s.2.2)]
  have hs := (unitInterval.double ⁻¹' u).inter_subset_right {s | s.val ≤ 1 / 2}
  have h := ((unitInterval.smoothOn_double t ht).mono hs).of_le (m := n) le_top
  exact (hγ.comp t h (Set.inter_subset_left _ _)).congr (fun t ht => trans_eqOn_left ht.2) (trans_eqOn_left ht)

lemma trans_contMDiffWithinAt_left_iff' {n : ℕ∞} {t : unitInterval} (ht : t.val ≤ 1 / 2) :
    ContMDiffWithinAt (𝓡∂ 1) I n (γ.trans γ') {s | s.val ≤ 1 / 2} t ↔
      ContMDiffAt (𝓡∂ 1) I n γ (unitInterval.double t) := by
  rw [←contMDiffWithinAt_univ,←Set.univ_inter {s : unitInterval | s.val ≤ 1 / 2}]
  exact Set.preimage_univ ▸ trans_contMDiffWithinAt_left_iff I γ γ' ht

lemma trans_contMDiffAt_left_iff {n : ℕ∞} {t : unitInterval} (ht : t.val < 1 / 2) :
    ContMDiffAt (𝓡∂ 1) I n (γ.trans γ') t ↔
      ContMDiffAt (𝓡∂ 1) I n γ (unitInterval.double t) := by
  simp_rw [←contMDiffWithinAt_univ]
  rw [←contMDiffWithinAt_inter (t := {s | s.val ≤ 1 / 2})]
  exact Set.preimage_univ ▸ trans_contMDiffWithinAt_left_iff I γ γ' ht.le
  exact (mem_nhds_subtype _ t _).mpr ⟨Set.Iic (1 / 2),⟨Iic_mem_nhds ht,subset_of_eq rfl⟩⟩

lemma trans_contMDiffWithinAt_right_iff {n : ℕ∞} {t : unitInterval} (ht : 1 / 2 ≤ t.val)
    {u : Set unitInterval} :
    ContMDiffWithinAt (𝓡∂ 1) I n (γ.trans γ') (unitInterval.double' ⁻¹' u ∩ {s | 1 / 2 ≤ s.val}) t ↔
      ContMDiffWithinAt (𝓡∂ 1) I n γ' u (unitInterval.double' t) := by
  refine' ⟨fun hγ' => _, fun hγ' => _⟩
  rw [←trans_comp_half' (γ := γ)]
  refine' ((unitInterval.half'_double' ht).symm ▸ hγ').comp _ _ _
  exact unitInterval.smooth_half'.contMDiff.contMDiffAt.contMDiffWithinAt
  simp [-one_div,←Set.preimage_comp,unitInterval.double'_comp_half',subset_rfl,Set.mapsTo',
    (show u ⊆ {s | 1 / 2 ≤ (s.val + 1) / 2} by exact fun s _ => Set.mem_setOf.mpr (by linarith [s.2.1]))]
  have hs := (unitInterval.double' ⁻¹' u).inter_subset_right {s | 1 / 2 ≤ s.val}
  have h := ((unitInterval.smoothOn_double' t ht).mono hs).of_le (m := n) le_top
  exact (hγ'.comp t h (Set.inter_subset_left _ _)).congr (fun t ht => trans_eqOn_right ht.2) (trans_eqOn_right ht)

lemma trans_contMDiffWithinAt_right_iff' {n : ℕ∞} {t : unitInterval} (ht : 1 / 2 ≤ t.val) :
    ContMDiffWithinAt (𝓡∂ 1) I n (γ.trans γ') {s | 1 / 2 ≤ s.val} t ↔
      ContMDiffAt (𝓡∂ 1) I n γ' (unitInterval.double' t) := by
  rw [←contMDiffWithinAt_univ,←Set.univ_inter {s : unitInterval | 1 / 2 ≤ s.val}]
  exact Set.preimage_univ ▸ trans_contMDiffWithinAt_right_iff I γ γ' ht

lemma trans_contMDiffAt_right_iff {n : ℕ∞} {t : unitInterval} (ht : t.val > 1 / 2) :
    ContMDiffAt (𝓡∂ 1) I n (γ.trans γ') t ↔
      ContMDiffAt (𝓡∂ 1) I n γ' (unitInterval.double' t) := by
  rw [←(γ.trans γ').symm_symm,trans_symm,symm_contMDiffAt_iff,
    trans_contMDiffAt_left_iff I _ _ (by rw [unitInterval.coe_symm_eq]; linarith),
    symm_contMDiffAt_iff,unitInterval.double_symm,unitInterval.symm_symm]

lemma trans_contMDiffOn_left {n : ℕ∞} {s : Set unitInterval} :
    ContMDiffOn (𝓡∂ 1) I n (γ.trans γ') (unitInterval.double ⁻¹' s ∩ {s | s.val ≤ 1 / 2}) ↔
      ContMDiffOn (𝓡∂ 1) I n γ s := by
  refine' ⟨fun h t ht => _,fun h t ht => _⟩
  rw [←unitInterval.double_half t,←trans_contMDiffWithinAt_left_iff I γ γ' _]
  exact h _ (by simp [-one_div,ht,div_le_div_of_le two_pos.le t.2.2])
  simp [-one_div,div_le_div_of_le two_pos.le t.2.2]
  refine' (trans_contMDiffWithinAt_left_iff I γ γ' ht.2.out).mpr (h _ _)
  exact Set.mem_preimage.mp ht.1

lemma trans_contMDiffOn_right {n : ℕ∞} {s : Set unitInterval} :
    ContMDiffOn (𝓡∂ 1) I n (γ.trans γ') (unitInterval.double' ⁻¹' s ∩ {s | 1 / 2 ≤ s.val}) ↔
      ContMDiffOn (𝓡∂ 1) I n γ' s := by
  refine' ⟨fun h t ht => _,fun h t ht => _⟩
  rw [←unitInterval.double'_half' t,←trans_contMDiffWithinAt_right_iff I γ γ' _]
  exact h _ (by simp [-one_div,ht,show 1 / 2 ≤ (t.val +1 ) / 2 by linarith [t.2.1]])
  simp [-one_div,show 1 / 2 ≤ (t.val +1 ) / 2 by linarith [t.2.1]]
  refine' (trans_contMDiffWithinAt_right_iff I γ γ' ht.2.out).mpr (h _ _)
  exact Set.mem_preimage.mp ht.1

lemma trans_smoothWithinAt_left_iff {t : unitInterval} (ht : t.val ≤ 1 / 2)
    {u : Set unitInterval} :
    SmoothWithinAt (𝓡∂ 1) I (γ.trans γ') (unitInterval.double ⁻¹' u ∩ {s | s.val ≤ 1 / 2}) t ↔
      SmoothWithinAt (𝓡∂ 1) I γ u (unitInterval.double t) :=
  trans_contMDiffWithinAt_left_iff I γ γ' ht

lemma trans_smoothWithinAt_left_iff' {t : unitInterval} (ht : t.val ≤ 1 / 2) :
    SmoothWithinAt (𝓡∂ 1) I (γ.trans γ') {s | s.val ≤ 1 / 2} t ↔
      SmoothAt (𝓡∂ 1) I γ (unitInterval.double t) :=
  trans_contMDiffWithinAt_left_iff' I γ γ' ht

lemma trans_smoothAt_left_iff {t : unitInterval} (ht : t.val < 1 / 2) :
    SmoothAt (𝓡∂ 1) I (γ.trans γ') t ↔
      SmoothAt (𝓡∂ 1) I γ (unitInterval.double t) :=
  trans_contMDiffAt_left_iff I γ γ' ht

lemma trans_smoothWithinAt_right_iff {t : unitInterval} (ht : 1 / 2 ≤ t.val)
    {u : Set unitInterval} :
    SmoothWithinAt (𝓡∂ 1) I (γ.trans γ') (unitInterval.double' ⁻¹' u ∩ {s | 1 / 2 ≤ s.val}) t ↔
      SmoothWithinAt (𝓡∂ 1) I γ' u (unitInterval.double' t) :=
  trans_contMDiffWithinAt_right_iff I γ γ' ht

lemma trans_smoothWithinAt_right_iff' {t : unitInterval} (ht : 1 / 2 ≤ t.val) :
    SmoothWithinAt (𝓡∂ 1) I (γ.trans γ') {s | 1 / 2 ≤ s.val} t ↔
      SmoothAt (𝓡∂ 1) I γ' (unitInterval.double' t) :=
  trans_contMDiffWithinAt_right_iff' I γ γ' ht

lemma trans_smoothAt_right_iff {t : unitInterval} (ht : t.val > 1 / 2) :
    SmoothAt (𝓡∂ 1) I (γ.trans γ') t ↔
      SmoothAt (𝓡∂ 1) I γ' (unitInterval.double' t) :=
  trans_contMDiffAt_right_iff I γ γ' ht

lemma trans_smoothOn_left {s : Set unitInterval} :
    SmoothOn (𝓡∂ 1) I (γ.trans γ') (unitInterval.double ⁻¹' s ∩ {s | s.val ≤ 1 / 2}) ↔
      SmoothOn (𝓡∂ 1) I γ s :=
  trans_contMDiffOn_left I γ γ'

lemma trans_smoothOn_right {s : Set unitInterval} :
    SmoothOn (𝓡∂ 1) I (γ.trans γ') (unitInterval.double' ⁻¹' s ∩ {s | 1 / 2 ≤ s.val}) ↔
      SmoothOn (𝓡∂ 1) I γ' s :=
  trans_contMDiffOn_right I γ γ'

example : True := by tauto

lemma trans_pathderivWithin_left {t : unitInterval} (ht : t.val ≤ 1 / 2) {u : Set unitInterval}
    (hu : UniqueMDiffWithinAt (𝓡∂ 1) (unitInterval.double ⁻¹' u ∩ {s | s.val ≤ 1 / 2}) t) :
      pathderivWithin I (γ.trans γ') (unitInterval.double ⁻¹' u ∩ {s | s.val ≤ 1 / 2}) t =
        (2 : ℝ) • pathderivWithin I γ u (unitInterval.double t) := by
  by_cases hγ : MDifferentiableWithinAt (𝓡∂ 1) I γ u (unitInterval.double t)
  rw [pathderivWithin_congr I hu (trans_eqOn_left'.mono (Set.inter_subset_right _ _))
    (trans_eqOn_left ht),pathderivWithin_reparam I _ hγ _ (Set.inter_subset_left _ _) hu,
    mfderivWithin_subset (Set.inter_subset_right _ _) hu _,unitInterval.mfderivWithin_double ht]
  by_cases ht' : t.val < 1 / 2
  simp only [ht',ite_true,ContinuousLinearMap.coe_smul',Pi.smul_apply,ContinuousLinearMap.id]
  simp [-one_div,lt_of_le_of_lt ht one_half_lt_one,(lt_div_iff' zero_lt_two).mp ht']
  simp only [ht',ite_false,ContinuousLinearMap.coe_smul',Pi.smul_apply,ContinuousLinearMap.id]
  simp [-one_div,lt_of_le_of_lt ht one_half_lt_one,ht',(lt_div_iff' zero_lt_two).not.mp ht']
  exact unitInterval.smoothOn_double.mdifferentiableOn t ht
  exact (unitInterval.smoothOn_double.mdifferentiableOn t ht).mono (Set.inter_subset_right _ _)
  rw [pathderivWithin_zero_of_not_mdifferentiableWithinAt I hγ,
    pathderivWithin_zero_of_not_mdifferentiableWithinAt I _,smul_zero]
  exact (trans_mdifferentiableWithinAt_left_iff I γ γ' ht).not.mpr hγ

lemma trans_pathderivWithin_left' {t : unitInterval} (ht : t.val ≤ 1 / 2) :
    pathderivWithin I (γ.trans γ') {s | s.val ≤ 1 / 2} t =
      (2 : ℝ) • pathderiv I γ (unitInterval.double t) := by
  rw [←pathderivWithin_univ,←Set.univ_inter {s : unitInterval | s.val ≤ 1 / 2}]
  convert Set.preimage_univ ▸ trans_pathderivWithin_left I γ γ' ht _
  rw [Set.preimage_univ,Set.univ_inter]
  exact unitInterval.uniqueMDiffOn_left t ht

lemma trans_pathderiv_left {t : unitInterval} (ht : t.val < 1 / 2) :
    pathderiv I (γ.trans γ') t = (2 : ℝ) • pathderiv I γ (unitInterval.double t) := by
  rw [←trans_pathderivWithin_left' I γ γ' ht.le,pathderivWithin_of_mem_nhds I _]
  exact (mem_nhds_subtype _ t _).mpr ⟨Set.Iic (1 / 2),⟨Iic_mem_nhds ht,subset_of_eq rfl⟩⟩

lemma trans_pathderivWithin_right {t : unitInterval} (ht : 1 / 2 ≤ t.val) {u : Set unitInterval}
    (hu : UniqueMDiffWithinAt (𝓡∂ 1) (unitInterval.double' ⁻¹' u ∩ {s | 1 / 2 ≤ s.val}) t) :
      pathderivWithin I (γ.trans γ') (unitInterval.double' ⁻¹' u ∩ {s | 1 / 2 ≤ s.val}) t =
        (2 : ℝ) • pathderivWithin I γ' u (unitInterval.double' t) := by
  by_cases hγ' : MDifferentiableWithinAt (𝓡∂ 1) I γ' u (unitInterval.double' t)
  rw [pathderivWithin_congr I hu (trans_eqOn_right'.mono (Set.inter_subset_right _ _))
    (trans_eqOn_right ht),pathderivWithin_reparam I _ hγ' _ (Set.inter_subset_left _ _) hu,
    mfderivWithin_subset (Set.inter_subset_right _ _) hu _,unitInterval.mfderivWithin_double' ht]
  by_cases ht' : t.val < 1
  simp only [ht',ite_true,ContinuousLinearMap.coe_smul',Pi.smul_apply,ContinuousLinearMap.id]
  simp [-one_div,(by linarith : 2 * t.val - 1 < 1)]
  simp only [ht',ite_true,ContinuousLinearMap.coe_smul',Pi.smul_apply,ContinuousLinearMap.id]
  simp [-one_div,(by linarith : ¬ 2 * t.val - 1 < 1)]
  exact unitInterval.smoothOn_double'.mdifferentiableOn t ht
  exact (unitInterval.smoothOn_double'.mdifferentiableOn t ht).mono (Set.inter_subset_right _ _)
  rw [pathderivWithin_zero_of_not_mdifferentiableWithinAt I hγ',
    pathderivWithin_zero_of_not_mdifferentiableWithinAt I _,smul_zero]
  exact (trans_mdifferentiableWithinAt_right_iff I γ γ' ht).not.mpr hγ'

lemma trans_pathderivWithin_right' {t : unitInterval} (ht : 1 / 2 ≤ t.val) :
    pathderivWithin I (γ.trans γ') {s | 1 / 2 ≤ s.val} t =
      (2 : ℝ) • pathderiv I γ' (unitInterval.double' t) := by
  rw [←pathderivWithin_univ,←Set.univ_inter {s : unitInterval | 1 / 2 ≤ s.val}]
  convert Set.preimage_univ ▸ trans_pathderivWithin_right I γ γ' ht _
  rw [Set.preimage_univ,Set.univ_inter]
  exact unitInterval.uniqueMDiffOn_right t ht

lemma trans_pathderiv_right {t : unitInterval} (ht : 1 / 2 < t.val) :
    pathderiv I (γ.trans γ') t = (2 : ℝ) • pathderiv I γ' (unitInterval.double' t) := by
  rw [←trans_pathderivWithin_right' I γ γ' ht.le,pathderivWithin_of_mem_nhds I _]
  exact (mem_nhds_subtype _ t _).mpr ⟨Set.Ici (1 / 2),⟨Ici_mem_nhds ht,subset_of_eq rfl⟩⟩

lemma trans_mdifferentiableAt_mid_iff :
    MDifferentiableAt (𝓡∂ 1) I (γ.trans γ') unitInterval.one_half ↔
      MDifferentiableAt (𝓡∂ 1) I γ 1 ∧ MDifferentiableAt (𝓡∂ 1) I γ' 0 ∧
        pathderiv I γ 1 = pathderiv I γ' 0 := by
  rw [←unitInterval.double_one_half,←unitInterval.double'_one_half]
  refine' ⟨fun h => ⟨_,_,_⟩,fun ⟨hγ,hγ',h⟩ => _⟩
  exact (trans_mdifferentiableWithinAt_left_iff' I γ γ' (by simp)).mp h.mdifferentiableWithinAt
  exact (trans_mdifferentiableWithinAt_right_iff' I γ γ' (by simp)).mp h.mdifferentiableWithinAt
  rw [←smul_right_inj (R := ℝ) two_ne_zero,←trans_pathderivWithin_left' I γ γ' (by simp),
    ←trans_pathderivWithin_right' I γ γ' (by simp),
    pathderivWithin_eq_pathderiv I (unitInterval.uniqueMDiffOn_left _ (by simp)) h,
    pathderivWithin_eq_pathderiv I (unitInterval.uniqueMDiffOn_right _ (by simp)) h]
  refine' (HasMFDerivWithinAt.hasMFDerivAt _ Filter.univ_mem).mdifferentiableAt
  convert (MDifferentiableWithinAt.hasMFDerivWithinAt _).union (s := {s | s.val ≤ 1 / 2})
    (t := {s : unitInterval | 1 / 2 ≤ s.val}) _
  ext; simp [le_total]
  exact (trans_mdifferentiableWithinAt_left_iff' I γ γ' (by simp)).mpr hγ
  convert ((trans_mdifferentiableWithinAt_right_iff' I γ γ' (by simp)).mpr hγ').hasMFDerivWithinAt
    using 1
  rw [←(smul_right_inj (R := ℝ) two_ne_zero),←trans_pathderivWithin_left' I γ γ' (by simp),
    ←trans_pathderivWithin_right' I γ γ' (by simp)] at h
  simp_rw [pathderivWithin,unitInterval.coe_one_half,one_half_lt_one,ite_true] at h
  ext x
  have hx : x = (x 0) • (EuclideanSpace.single 0 1 : ℝ¹) := PiLp.ext fun i => by
    simp [((Fin.eq_zero i) ▸ rfl : x 0 = x i)]
  rw [hx,map_smul,map_smul,h]

lemma trans_mdifferentiable_iff :
    MDifferentiable (𝓡∂ 1) I (γ.trans γ') ↔ MDifferentiable (𝓡∂ 1) I γ ∧
      MDifferentiable (𝓡∂ 1) I γ' ∧ pathderiv I γ 1 = pathderiv I γ' 0 := by
  refine' ⟨fun h => ⟨fun t => _,fun t => _,_⟩,fun ⟨hγ,hγ',h⟩ t => _⟩
  rw [←unitInterval.double_half t,←trans_mdifferentiableWithinAt_left_iff' I γ γ' _]
  exact (h _).mdifferentiableWithinAt
  rw [unitInterval.coe_half_eq]; linarith [t.2.2]
  rw [←unitInterval.double'_half' t,←trans_mdifferentiableWithinAt_right_iff' I γ γ' _]
  exact (h _).mdifferentiableWithinAt
  rw [unitInterval.coe_half'_eq]; linarith [t.2.1]
  refine' ((trans_mdifferentiableAt_mid_iff I γ γ').mp (h _)).2.2
  by_cases ht : t.val < 1 / 2
  exact (trans_mdifferentiableAt_left_iff I γ γ' ht).mpr (hγ _)
  by_cases ht' : 1 / 2 < t.val
  exact (trans_mdifferentiableAt_right_iff I γ γ' ht').mpr (hγ' _)
  convert (trans_mdifferentiableAt_mid_iff I γ γ').mpr ⟨hγ _,hγ' _,h⟩
  exact Subtype.ext (eq_of_le_of_not_lt (le_of_not_lt ht') ht)

lemma trans_pathderiv {t : unitInterval} :
    pathderiv I (γ.trans γ') t =
      if t.val < 1 / 2 then (2 : ℝ) • pathderiv I γ (unitInterval.double t)
      else if t.val > 1 / 2 then (2 : ℝ) • pathderiv I γ' (unitInterval.double' t)
      else if pathderiv I γ 1 = pathderiv I γ' 0 then (2 : ℝ) • pathderiv I γ 1 else 0 := by
  by_cases ht : t.val < 1 / 2
  all_goals simp only [ht,ite_true,ite_false]
  exact trans_pathderiv_left I γ γ' ht
  by_cases ht' : 1 / 2 < t.val
  all_goals simp only [ht',ite_true,ite_false]
  exact trans_pathderiv_right I γ γ' ht'
  rw [(Subtype.ext (eq_of_le_of_not_lt (le_of_not_lt ht') ht) : t = unitInterval.one_half)]
  by_cases h : pathderiv I γ 1 = pathderiv I γ' 0
  simp_rw [eq_true h,ite_true]
  by_cases hγ : MDifferentiableAt (𝓡∂ 1) I γ 1
  by_cases hγ' : MDifferentiableAt (𝓡∂ 1) I γ' 0
  have h' := (trans_mdifferentiableAt_mid_iff I γ γ').mpr ⟨hγ,hγ',h⟩
  rw [←pathderivWithin_eq_pathderiv I (unitInterval.uniqueMDiffOn_left _ (by simp)) h',
    ←unitInterval.double_one_half,trans_pathderivWithin_left' I γ γ' (by simp)]
  rw [h,pathderiv_zero_of_not_mdifferentiableAt I hγ',smul_zero,
    pathderiv_zero_of_not_mdifferentiableAt I ((trans_mdifferentiableAt_mid_iff I γ γ').not.mpr _)]
  tauto
  rw [pathderiv_zero_of_not_mdifferentiableAt I hγ,smul_zero,
    pathderiv_zero_of_not_mdifferentiableAt I ((trans_mdifferentiableAt_mid_iff I γ γ').not.mpr _)]
  tauto
  simp only [h,ite_false]
  apply pathderiv_zero_of_not_mdifferentiableAt I
  refine' (trans_mdifferentiableAt_mid_iff I γ γ').not.mpr (by tauto)

end Trans
