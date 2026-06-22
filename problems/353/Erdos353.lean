import Mathlib

namespace Erdos353

open scoped BigOperators Real Classical RealInnerProductSpace
open MeasureTheory Filter Topology

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option grind.warning false

-- ============================================================
-- Koizumi
-- ============================================================

/-!
# Isosceles trapezoids of unit area with vertices in sets of infinite planar measure
This file formalizes Theorems 1 and 2 of J. Koizumi, *Isosceles trapezoids of unit area with
vertices in sets of infinite planar measure*.
The plane is modelled as `EuclideanSpace ℝ (Fin 2)`, so that `dist` is the Euclidean distance
and `volume` is the two–dimensional Lebesgue measure.
-/
namespace Koizumi

open scoped Pointwise

/-- (Twice-halved) signed-area magnitude of the triangle `A B C`, i.e. its area, computed via the
cross product of the edge vectors. -/
noncomputable def area2 (A B C : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |(B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)| / 2
/-- The area of the quadrilateral `A B C D` (vertices in order), via the shoelace formula. -/
noncomputable def quadArea (A B C D : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |(A 0 * B 1 - B 0 * A 1) + (B 0 * C 1 - C 0 * B 1)
    + (C 0 * D 1 - D 0 * C 1) + (D 0 * A 1 - A 0 * D 1)| / 2
/-- `A B C` are the vertices of an isosceles triangle of area `1`: the area is `1` and (at least)
two of the three sides have equal length. -/
def IsoscelesTriangleArea1 (A B C : EuclideanSpace ℝ (Fin 2)) : Prop :=
  area2 A B C = 1 ∧ (dist A B = dist A C ∨ dist B A = dist B C ∨ dist C A = dist C B)
/-- `A B C` are the vertices of a right-angled triangle of area `1`: the area is `1` and the angle
at one of the three vertices is a right angle. -/
def RightTriangleArea1 (A B C : EuclideanSpace ℝ (Fin 2)) : Prop :=
  area2 A B C = 1 ∧ (⟪B - A, C - A⟫ = 0 ∨ ⟪A - B, C - B⟫ = 0 ∨ ⟪A - C, B - C⟫ = 0)
/-- `A B C D` (in order) are the vertices of an isosceles trapezoid of area `1`.
The conditions are: the area is `1`; the sides `AB` and `DC` are parallel (the two bases);
the legs `AD` and `BC` are equal; the diagonals `AC` and `BD` are equal; and the four vertices are
pairwise distinct.  Equal diagonals together with a pair of parallel sides is the classical
characterization of an isosceles trapezoid (in particular it rules out non-rectangular
parallelograms). -/
def IsoTrapArea1 (A B C D : EuclideanSpace ℝ (Fin 2)) : Prop :=
  quadArea A B C D = 1 ∧
  ((B 0 - A 0) * (C 1 - D 1) = (B 1 - A 1) * (C 0 - D 0)) ∧
  dist A D = dist B C ∧ dist A C = dist B D ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D
/-- Rotation of a planar vector `v` by angle `a` (counter-clockwise). -/
noncomputable def rot (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos a * v 0 - Real.sin a * v 1, Real.sin a * v 0 + Real.cos a * v 1]
@[simp] lemma rot_apply0 (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    (rot a v) 0 = Real.cos a * v 0 - Real.sin a * v 1 := by simp [rot]
@[simp] lemma rot_apply1 (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    (rot a v) 1 = Real.sin a * v 0 + Real.cos a * v 1 := by simp [rot]
/-- The radius-dependent rotation (twist) about a center `O` by angle `ang ‖p - O‖`. -/
noncomputable def twistAt (O : EuclideanSpace ℝ (Fin 2)) (ang : ℝ → ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  O + rot (ang ‖p - O‖) (p - O)
/-- The midpoint map `g(p) = (p + twist p)/2` about center `O` with angle `ang ‖p - O‖`. -/
noncomputable def avgAt (O : EuclideanSpace ℝ (Fin 2)) (ang : ℝ → ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  O + (1 / 2 : ℝ) • ((p - O) + rot (ang ‖p - O‖) (p - O))
/-- Contraction toward `O` by factor `R⁻¹`. -/
noncomputable def conAt (O : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) := O + R⁻¹ • (p - O)
/-- Trapezoid angle function `ψ_R(t) = arcsin((R²/(R²-1))·(2/t²))`. -/
noncomputable def psi (R : ℝ) : ℝ → ℝ := fun t => Real.arcsin (R ^ 2 / (R ^ 2 - 1) * (2 / t ^ 2))
/-- Rotation preserves the norm. -/
lemma norm_rot (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : ‖rot a v‖ = ‖v‖ := by
  rw [ EuclideanSpace.norm_eq, EuclideanSpace.norm_eq ];
  simp +zetaDelta at *;
  exact congrArg Real.sqrt ( by nlinarith [ Real.sin_sq_add_cos_sq a ] )
/-- **Geometry of the twist.**  With the angle function `φ(t) = arcsin(2/t²)`, for any point `p` with
`‖p - O‖ > √2` the three points `O`, `p`, `twistAt O φ p` form an isosceles triangle of area `1`. -/
lemma twistAt_isosceles (O p : EuclideanSpace ℝ (Fin 2))
    (hp : Real.sqrt 2 < ‖p - O‖) :
    IsoscelesTriangleArea1 O p (twistAt O (fun t => Real.arcsin (2 / t ^ 2)) p) := by
  constructor;
  · unfold area2; unfold twistAt; norm_num [ EuclideanSpace.norm_eq ] at *;
    rw [ Real.sq_sqrt <| by positivity, Real.sin_arcsin, Real.cos_arcsin ];
    · grind;
    · rw [ le_div_iff₀ ] <;> linarith;
    · rw [ div_le_iff₀ ] <;> linarith;
  · unfold twistAt; norm_num [ dist_eq_norm' ] ;
    exact Or.inl ( by rw [ norm_rot ] )
/-
The fiberwise rotation `w ↦ rot (ang ‖w‖) w` is injective.
-/
lemma rotTwist_inj (ang : ℝ → ℝ) :
    Function.Injective (fun w : EuclideanSpace ℝ (Fin 2) => rot (ang ‖w‖) w) := by
  intro w w' h_eq
  have h_norm : ‖w‖ = ‖w'‖ := by
    simpa [ norm_rot ] using congr_arg Norm.norm h_eq
  have h_angle : ang ‖w‖ = ang ‖w'‖ := by
    rw [ h_norm ]
  have h_rot_eq : rot (ang ‖w‖) w = rot (ang ‖w‖) w' := by
    aesop
  have h_w_eq_w' : w = w' := by
    simp +decide [ rot, ← List.ofFn_inj ] at h_rot_eq ⊢;
    ext i; fin_cases i <;> simp_all +decide [ Prod.ext_iff ] ;
    · cases le_or_gt 0 ( Real.cos ( ang ‖w'‖ ) ) <;> cases le_or_gt 0 ( Real.sin ( ang ‖w'‖ ) ) <;> nlinarith [ Real.sin_sq_add_cos_sq ( ang ‖w'‖ ) ];
    · cases le_or_gt 0 ( Real.cos ( ang ‖w'‖ ) ) <;> cases le_or_gt 0 ( Real.sin ( ang ‖w'‖ ) ) <;> nlinarith [ Real.sin_sq_add_cos_sq ( ang ‖w'‖ ) ]
  exact h_w_eq_w'
/-- A directional derivative equals the Fréchet derivative applied to the direction. -/
lemma fderiv_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (w v : E) (h : DifferentiableAt ℝ f w) :
    (fderiv ℝ f w) v = deriv (fun t : ℝ => f (w + t • v)) 0 := by
  have hline : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const v |>.const_add w
  have hf : HasFDerivAt f (fderiv ℝ f w) ((fun t : ℝ => w + t • v) 0) := by
    simpa using h.hasFDerivAt
  have hc := hf.comp_hasDerivAt (0:ℝ) hline
  have : HasDerivAt (fun t : ℝ => f (w + t • v)) ((fderiv ℝ f w) v) 0 := hc
  rw [this.deriv]
/-
The fiberwise rotation `w ↦ rot (ang ‖w‖) w` is differentiable at `w ≠ 0`, provided `ang` is
differentiable at `‖w‖`.
-/
lemma twist_differentiableAt (ang : ℝ → ℝ) {w : EuclideanSpace ℝ (Fin 2)} (hw : w ≠ 0)
    (hang : DifferentiableAt ℝ ang ‖w‖) :
    DifferentiableAt ℝ (fun w : EuclideanSpace ℝ (Fin 2) => rot (ang ‖w‖) w) w := by
  -- Apply the differentiability of the norm and the composition rule.
  have h_norm_diff : DifferentiableAt ℝ (fun w => ‖w‖) w := by
    exact differentiableAt_id.norm ℝ hw;
  refine' DifferentiableAt.congr_of_eventuallyEq _ _;
  exact fun w => ( Real.cos ( ang ‖w‖ ) * w 0 - Real.sin ( ang ‖w‖ ) * w 1 ) • EuclideanSpace.single 0 1 + ( Real.sin ( ang ‖w‖ ) * w 0 + Real.cos ( ang ‖w‖ ) * w 1 ) • EuclideanSpace.single 1 1;
  · fun_prop;
  · filter_upwards [ ] with w using by ext i; fin_cases i <;> simp +decide [ EuclideanSpace.single_apply ] ;
/-- Derivative of `t ↦ ‖x + t • v‖` at `0` for `x ≠ 0`. -/
lemma norm_line_hasDerivAt {x v : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖x + t • v‖) (inner ℝ x v / ‖x‖) 0 := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h2 : HasDerivAt (fun t : ℝ => ‖x + t • v‖ ^ 2) (2 * inner ℝ x v) 0 := by
    have heq : (fun t : ℝ => ‖x + t • v‖ ^ 2)
        = (fun t : ℝ => ‖x‖^2 + 2 * inner ℝ x v * t + ‖v‖^2 * t^2) := by
      funext t
      rw [norm_add_sq_real, norm_smul]
      simp [inner_smul_right, mul_pow]
      ring
    rw [heq]
    have := ((hasDerivAt_const (0:ℝ) (‖x‖^2)).add
      ((hasDerivAt_id (0:ℝ)).const_mul (2 * inner ℝ x v))).add
      ((hasDerivAt_pow 2 (0:ℝ)).const_mul (‖v‖^2))
    convert this using 1
    norm_num
  have hne : ‖x + (0:ℝ) • v‖ ^ 2 ≠ 0 := by
    simp only [zero_smul, add_zero]; exact pow_ne_zero 2 (ne_of_gt hxpos)
  have hsqrt := h2.sqrt hne
  have heq : (fun t : ℝ => Real.sqrt (‖x + t • v‖ ^ 2)) = (fun t : ℝ => ‖x + t • v‖) := by
    funext t; rw [Real.sqrt_sq (norm_nonneg _)]
  rw [heq] at hsqrt
  convert hsqrt using 1
  simp only [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg x)]
  field_simp
/-
Directional (line) derivative of the fiberwise rotation at `x ≠ 0`, provided `ang` is
differentiable at `‖x‖`.
-/
lemma twist_line_hasDerivAt (ang : ℝ → ℝ)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) (hang : DifferentiableAt ℝ ang ‖x‖)
    (v : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun t : ℝ => rot (ang ‖x + t • v‖) (x + t • v))
      (!₂[ Real.cos (ang ‖x‖) * v 0 - Real.sin (ang ‖x‖) * v 1
            - (deriv ang ‖x‖) * (inner ℝ x v / ‖x‖) * (Real.sin (ang ‖x‖) * x 0 + Real.cos (ang ‖x‖) * x 1),
          Real.sin (ang ‖x‖) * v 0 + Real.cos (ang ‖x‖) * v 1
            + (deriv ang ‖x‖) * (inner ℝ x v / ‖x‖) * (Real.cos (ang ‖x‖) * x 0 - Real.sin (ang ‖x‖) * x 1)]) 0 := by
  have h_deriv : HasDerivAt (fun t : ℝ => ang ‖x + t • v‖) (deriv ang ‖x‖ * (⟪x, v⟫ / ‖x‖)) 0 := by
    convert HasDerivAt.comp _ _ _ using 1;
    · simpa using hang.hasDerivAt;
    · convert norm_line_hasDerivAt hx using 1;
  convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
  use fun t => ( Real.cos ( ang ‖x + t • v‖ ) * ( x 0 + t * v 0 ) - Real.sin ( ang ‖x + t • v‖ ) * ( x 1 + t * v 1 ) ) • EuclideanSpace.single 0 1 + ( Real.sin ( ang ‖x + t • v‖ ) * ( x 0 + t * v 0 ) + Real.cos ( ang ‖x + t • v‖ ) * ( x 1 + t * v 1 ) ) • EuclideanSpace.single 1 1;
  · convert HasDerivAt.add ( HasDerivAt.smul ( HasDerivAt.sub ( HasDerivAt.mul ( HasDerivAt.cos h_deriv ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( hasDerivAt_mul_const _ ) ) ) ( HasDerivAt.mul ( HasDerivAt.sin h_deriv ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( hasDerivAt_mul_const _ ) ) ) ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.smul ( HasDerivAt.add ( HasDerivAt.mul ( HasDerivAt.sin h_deriv ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( hasDerivAt_mul_const _ ) ) ) ( HasDerivAt.mul ( HasDerivAt.cos h_deriv ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( hasDerivAt_mul_const _ ) ) ) ) ( hasDerivAt_const _ _ ) ) using 1 ; norm_num;
    congr! 1;
    · ext i; fin_cases i <;> norm_num <;> ring;
    · infer_instance;
    · infer_instance;
    · infer_instance;
    · infer_instance;
  · filter_upwards [ ] with t ; ext i ; fin_cases i <;> simp +decide [ rot ]
/-- Determinant of a continuous linear endomorphism of the plane via its action on the unit axes. -/
lemma det_two (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    L.det = (L (EuclideanSpace.single 0 1)) 0 * (L (EuclideanSpace.single 1 1)) 1
          - (L (EuclideanSpace.single 0 1)) 1 * (L (EuclideanSpace.single 1 1)) 0 := by
  rw [ContinuousLinearMap.det]
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis L.toLinearMap]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr]
  ring
/-
**Measure preservation of the twist.**  The twist about `O` preserves Lebesgue measure of any
measurable set `T` avoiding `O`, provided the angle function is differentiable at each radius
`‖x - O‖` for `x ∈ T` (where the Jacobian determinant is `1`).
-/
lemma twistAt_volume (O : EuclideanSpace ℝ (Fin 2)) (ang : ℝ → ℝ)
    (T : Set (EuclideanSpace ℝ (Fin 2))) (hT : MeasurableSet T) (hO : O ∉ closure T)
    (hang : ∀ x ∈ T, DifferentiableAt ℝ ang ‖x - O‖) :
    volume (twistAt O ang '' T) = volume T := by
  -- Set T' := T - {O} (i.e. {x - O : x ∈ T}), which is measurable.
  set T' : Set (EuclideanSpace ℝ (Fin 2)) := T - {O} with hT';
  -- For every y ∈ T', y = x - O for some x ∈ T, hence y ≠ 0 (as O ∉ closure T ⊇ T) and DifferentiableAt ℝ ang ‖y‖ (since ‖y‖ = ‖x - O‖ and hang x).
  have hT'_meas : MeasurableSet T' := by
    convert hT.preimage ( show Measurable ( fun x => x + O ) from measurable_id.add_const O ) using 1 ; aesop
  have hT'_nonzero : ∀ y ∈ T', y ≠ 0 := by
    simp_all +decide [ sub_eq_zero, mem_closure_iff ];
    exact fun x hx hx' => hO.choose_spec.2.2 ⟨ x, hO.choose_spec.2.1 |> fun h => by aesop ⟩
  have hT'_diff : ∀ y ∈ T', DifferentiableAt ℝ (fun w => rot (ang ‖w‖) w) y := by
    intro y hy
    obtain ⟨x, hxT, rfl⟩ : ∃ x ∈ T, y = x - O := by
      rw [ Set.mem_sub ] at hy ; aesop;
    convert twist_differentiableAt ang ( hT'_nonzero _ hy ) ( hang _ hxT ) using 1
  have hT'_det : ∀ y ∈ T', (fderiv ℝ (fun w => rot (ang ‖w‖) w) y).det = 1 := by
    intro y hy
    have h_det : (fderiv ℝ (fun w => rot (ang ‖w‖) w) y) (EuclideanSpace.single 0 1) = !₂[Real.cos (ang ‖y‖) - (deriv ang ‖y‖) * (inner ℝ y (EuclideanSpace.single 0 1) / ‖y‖) * (Real.sin (ang ‖y‖) * y 0 + Real.cos (ang ‖y‖) * y 1), Real.sin (ang ‖y‖) + (deriv ang ‖y‖) * (inner ℝ y (EuclideanSpace.single 0 1) / ‖y‖) * (Real.cos (ang ‖y‖) * y 0 - Real.sin (ang ‖y‖) * y 1)] := by
      convert HasDerivAt.deriv ( twist_line_hasDerivAt ang ( hT'_nonzero y hy ) ( show DifferentiableAt ℝ ang ‖y‖ from ?_ ) ( EuclideanSpace.single 0 1 ) ) using 1;
      · convert fderiv_dir _ _ _ ( hT'_diff y hy ) using 1;
      · ext i; fin_cases i <;> norm_num;
      · rw [ Set.mem_sub ] at hy ; aesop;
    have h_det' : (fderiv ℝ (fun w => rot (ang ‖w‖) w) y) (EuclideanSpace.single 1 1) = !₂[-Real.sin (ang ‖y‖) - (deriv ang ‖y‖) * (inner ℝ y (EuclideanSpace.single 1 1) / ‖y‖) * (Real.sin (ang ‖y‖) * y 0 + Real.cos (ang ‖y‖) * y 1), Real.cos (ang ‖y‖) + (deriv ang ‖y‖) * (inner ℝ y (EuclideanSpace.single 1 1) / ‖y‖) * (Real.cos (ang ‖y‖) * y 0 - Real.sin (ang ‖y‖) * y 1)] := by
      convert HasDerivAt.deriv ( twist_line_hasDerivAt ang ( hT'_nonzero y hy ) ( show DifferentiableAt ℝ ang ‖y‖ from ?_ ) ( EuclideanSpace.single 1 1 ) ) using 1;
      · rw [ fderiv_dir ];
        exact hT'_diff y hy;
      · ext i; fin_cases i <;> norm_num;
      · rw [ Set.mem_sub ] at hy ; aesop;
    convert det_two _ using 1;
    simp_all +decide [ EuclideanSpace.norm_eq ];
    norm_num [ EuclideanSpace.inner_single_right ] ; ring;
    rw [ Real.cos_sq_add_sin_sq ];
  -- Apply lintegral_abs_det_fderiv_eq_addHaar_image to h := (fun w => rot (ang ‖w‖) w) on T'.
  have h_volume_eq : volume ((fun w => rot (ang ‖w‖) w) '' T') = volume T' := by
    have h_volume_eq : ∫⁻ y in T', ENNReal.ofReal |(fderiv ℝ (fun w => rot (ang ‖w‖) w) y).det| = volume T' := by
      rw [ MeasureTheory.lintegral_congr_ae ];
      rw [ MeasureTheory.lintegral_one ];
      · norm_num;
      · filter_upwards [ MeasureTheory.ae_restrict_mem hT'_meas ] with y hy using by rw [ hT'_det y hy ] ; norm_num;
    rw [ ← h_volume_eq, lintegral_abs_det_fderiv_eq_addHaar_image ];
    · exact hT'_meas;
    · exact fun x hx => DifferentiableAt.hasFDerivAt ( hT'_diff x hx ) |> HasFDerivAt.hasFDerivWithinAt;
    · exact fun x hx y hy hxy => rotTwist_inj _ hxy;
  convert h_volume_eq using 1;
  · rw [ show twistAt O ang '' T = ( fun w => O + w ) '' ( ( fun w => rot ( ang ‖w‖ ) w ) '' ( T - { O } ) ) from ?_ ];
    · simp +zetaDelta at *;
    · ext; simp [twistAt];
      grind +qlia;
  · simp +decide [ T', sub_eq_add_neg ]
/-- Volume of the half-radius ball is a quarter of the full ball (in the plane). -/
lemma volume_ball_half (A : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 ≤ ε) :
    volume (Metric.ball A (ε / 2)) * 4 = volume (Metric.ball A ε) := by
  convert congr_arg ( fun x : ENNReal => x * 4 ) ( MeasureTheory.Measure.addHaar_ball ( μ := MeasureTheory.MeasureSpace.volume ) ( x := A ) ( show 0 ≤ ε / 2 by positivity ) ) using 1 ; ring;
  convert MeasureTheory.Measure.addHaar_ball ( μ := MeasureTheory.MeasureSpace.volume ) ( x := A ) ( show 0 ≤ ε by positivity ) using 1 ; norm_num ; ring;
  rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num ; ring;
  · rw [ ENNReal.toReal_ofReal ( by positivity ), ENNReal.toReal_ofReal ( by positivity ), ENNReal.toReal_ofReal ( by positivity ) ] ; ring;
  · exact ENNReal.mul_ne_top ( ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top ) ) ( by norm_num );
  · exact ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top )
/-- **Abstract matching lemma.**  If `S` has high density in the ball `B = B(A, ε)` (its
complement occupies less than `1/10` of `B`), and `f` is a volume-preserving map sending the
half-ball `B' = B(A, ε/2)` into `B`, then there is a point `p ∈ B' ∩ S` whose image `f p` also lies
in `S`. -/
lemma matching (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : MeasurableSet S)
    (A : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 < ε)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hmap : ∀ T : Set (EuclideanSpace ℝ (Fin 2)), T ⊆ Metric.ball A (ε / 2) → MeasurableSet T →
      volume (f '' T) = volume T)
    (hfB : Set.MapsTo f (Metric.ball A (ε / 2)) (Metric.ball A ε))
    (hdens : volume (Metric.ball A ε \ S) < (1 / 10 : ENNReal) * volume (Metric.ball A ε)) :
    ∃ p, p ∈ Metric.ball A (ε / 2) ∧ p ∈ S ∧ f p ∈ S := by
  by_contra! h_contra;
  -- Set T := B' ∩ S, which is measurable (B' is open, S measurable). Claim f '' T ⊆ B \ S: if x = f p with p ∈ B'∩S then f p ∈ B by hfB (MapsTo), and f p ∉ S by the contradiction hypothesis applied to p. Hence by measure_mono, volume (B \ S) ≥ volume (f '' T) = volume T (using hmap T with T measurable).
  set T := Metric.ball A (ε / 2) ∩ S with hT_def
  have hT_meas : MeasurableSet T := by
    exact measurableSet_ball.inter hS
  have hT_image : f '' T ⊆ Metric.ball A ε \ S := by
    exact Set.image_subset_iff.mpr fun x hx => ⟨ hfB hx.1, h_contra x hx.1 hx.2 ⟩
  have hT_volume : volume (Metric.ball A ε \ S) ≥ volume T := by
    exact hmap T Set.inter_subset_left hT_meas ▸ MeasureTheory.measure_mono hT_image
  have hT_eq : volume (f '' T) = volume T := by
    exact hmap T Set.inter_subset_left hT_meas;
  -- So (1) volume (B \ S) ≥ volume B' - volume (B \ S), i.e. (using volume(B\S) finite) volume (B \ S) + volume (B \ S) ≥ volume B'. So 2 * volume (B \ S) ≥ volume B'.
  have h_half : 2 * volume (Metric.ball A ε \ S) ≥ volume (Metric.ball A (ε / 2)) := by
    have h_half : volume (Metric.ball A (ε / 2)) = volume T + volume (Metric.ball A (ε / 2) \ S) := by
      rw [ ← MeasureTheory.measure_inter_add_diff _ hS ];
    have h_half : volume (Metric.ball A (ε / 2) \ S) ≤ volume (Metric.ball A ε \ S) := by
      exact MeasureTheory.measure_mono ( Set.diff_subset_diff ( Metric.ball_subset_ball ( by linarith ) ) le_rfl );
    rw [ two_mul ] ; exact le_trans ( by aesop ) ( add_le_add hT_volume h_half ) ;
  -- By volume_ball_half, volume B' * 4 = volume B, so volume B' = volume B / 4. Hence 2 * volume (B\S) ≥ volume B / 4, giving volume (B \ S) ≥ volume B / 8.
  have h_quarter : volume (Metric.ball A (ε / 2)) = volume (Metric.ball A ε) / 4 := by
    convert congr_arg ( fun x : ENNReal => x / 4 ) ( volume_ball_half A hε.le ) using 1;
    rw [ ENNReal.mul_div_cancel_right ] <;> norm_num
  have h_eighth : volume (Metric.ball A ε \ S) ≥ volume (Metric.ball A ε) / 8 := by
    simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    convert ( mul_le_mul_right' h_half ( 1 / 2 : ENNReal ) ) using 1 <;> ring;
    · rw [ show ( 8⁻¹ : ENNReal ) = 4⁻¹ * ( 1 / 2 ) by
            rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num;
            norm_num [ ENNReal.mul_eq_top ] ] ; ring;
    · rw [ mul_assoc, ENNReal.div_mul_cancel ] <;> norm_num;
  refine' hdens.not_ge _;
  refine' le_trans _ h_eighth;
  rw [ ENNReal.div_eq_inv_mul ];
  rw [ ENNReal.div_eq_inv_mul ] ; gcongr ; norm_num
/-- An unbounded set contains points arbitrarily far from any fixed point. -/
lemma farPoint {S : Set (EuclideanSpace ℝ (Fin 2))} (hunb : ¬ Bornology.IsBounded S)
    (A : EuclideanSpace ℝ (Fin 2)) (M : ℝ) : ∃ O ∈ S, dist O A > M := by
  by_contra! h;
  exact hunb <| isBounded_iff_forall_norm_le.mpr ⟨ M + ‖A‖, by rintro x ( hx : x ∈ S ) ; exact le_trans ( norm_le_of_mem_closedBall <| by simpa using h x hx ) ( by linarith ) ⟩
/-- **Density point extraction.**  A measurable set of positive measure has a point `A ∈ S` around
which `S` is dense: for some radius `ε ∈ (0,1)`, the complement of `S` occupies less than `1/10` of
the ball `B(A, ε)`. -/
lemma densityPoint {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S)
    (hpos : 0 < volume S) :
    ∃ A ∈ S, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      volume (Metric.ball A ε \ S) < (1 / 10 : ENNReal) * volume (Metric.ball A ε) := by
  -- By Besicovitch's theorem, there exists a point $A \in S$ such that $\lim_{r \to 0} \frac{\lambda(S \cap B(A, r))}{\lambda(B(A, r))} = 1$.
  obtain ⟨A, hA⟩ : ∃ A ∈ S, Filter.Tendsto (fun r => volume (S ∩ Metric.ball A r) / volume (Metric.ball A r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h_besicovitch : ∀ᵐ x ∂(volume.restrict S), Filter.Tendsto (fun r => volume (S ∩ Metric.ball x r) / volume (Metric.ball x r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have := @Besicovitch.ae_tendsto_measure_inter_div;
      specialize this volume S;
      filter_upwards [ this ] with x hx;
      have h_eq : ∀ r > 0, volume (S ∩ Metric.closedBall x r) = volume (S ∩ Metric.ball x r) := by
        intro r hr; rw [ MeasureTheory.measure_congr ] ; filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( show volume ( Metric.sphere x r ) = 0 from by simp +decide [ MeasureTheory.Measure.addHaar_sphere ] ) ] with y hy; simp_all +decide [ Metric.mem_ball, Metric.mem_closedBall ] ;
        exact ⟨ fun h => ⟨ h.1, lt_of_le_of_ne ( by simpa using h.2 ) hy ⟩, fun h => ⟨ h.1, le_of_lt ( by simpa using h.2 ) ⟩ ⟩;
      refine' hx.congr' _;
      filter_upwards [ self_mem_nhdsWithin ] with r hr using by rw [ h_eq r hr, MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball ] ;
    contrapose! h_besicovitch;
    refine' fun h => _;
    simp_all +decide [ Filter.eventually_inf_principal ];
    exact hpos.ne' ( MeasureTheory.measure_mono_null ( fun x hx => by aesop ) h );
  -- By the definition of limit, there exists a δ > 0 such that for all 0 < r < δ, we have volume (S ∩ Metric.ball A r) / volume (Metric.ball A r) > 9 / 10.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ r, 0 < r ∧ r < δ → volume (S ∩ Metric.ball A r) / volume (Metric.ball A r) > 9 / 10 := by
    have := Metric.mem_nhdsWithin_iff.mp ( hA.2.eventually ( lt_mem_nhds ( show 1 > 9 / 10 by norm_num [ ENNReal.div_lt_iff ] ) ) );
    exact ⟨ this.choose, this.choose_spec.1, fun r hr => this.choose_spec.2 ⟨ mem_ball_zero_iff.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩, hr.1 ⟩ ⟩;
  refine' ⟨ A, hA.1, Min.min δ 1 / 2, _, _, _ ⟩ <;> norm_num [ hδ_pos ];
  · linarith [ min_le_left δ 1, min_le_right δ 1 ];
  · have h_complement : volume (Metric.ball A (min δ 1 / 2) \ S) = volume (Metric.ball A (min δ 1 / 2)) - volume (S ∩ Metric.ball A (min δ 1 / 2)) := by
      rw [ ← MeasureTheory.measure_diff ] <;> norm_num [ hS, Set.inter_comm ];
      · exact hS.nullMeasurableSet.inter ( measurableSet_ball.nullMeasurableSet );
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by exact ( Metric.isBounded_ball.measure_lt_top ) ) );
    have := hδ ( Min.min δ 1 / 2 ) ⟨ by positivity, by linarith [ min_le_left δ 1, min_le_right δ 1 ] ⟩ ; rw [ gt_iff_lt, ENNReal.lt_div_iff_mul_lt ] at this <;> norm_num at *;
    · rw [ h_complement, ENNReal.sub_lt_iff_lt_right ];
      · refine' lt_of_le_of_lt _ ( ENNReal.add_lt_add_left _ this );
        · rw [ ENNReal.div_eq_inv_mul ] ; ring_nf ; norm_num;
          rw [ mul_assoc, ENNReal.inv_mul_cancel ] <;> norm_num;
        · norm_num [ ENNReal.mul_eq_top ];
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by exact ( Metric.isBounded_ball.measure_lt_top ) ) );
      · refine' le_trans ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) _;
        rw [ ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul ] <;> norm_num;
        · rw [ ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_pow ( by positivity ) ];
        · positivity;
        · positivity;
    · exact Or.inl ⟨ hδ_pos, Real.pi_pos ⟩
/-
`arcsin (2/t²)` is differentiable at any `r` with `√2 < r` (so the argument lies in `(-1,1)`).
-/
lemma phi_differentiableAt {r : ℝ} (hr : Real.sqrt 2 < r) :
    DifferentiableAt ℝ (fun t => Real.arcsin (2 / t ^ 2)) r := by
  refine' ( Real.differentiableAt_arcsin.2 _ ) |> DifferentiableAt.comp _ <| DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.pow 2 ) <| _;
  · exact ⟨ by linarith [ show 0 < 2 / r ^ 2 by exact div_pos zero_lt_two ( sq_pos_of_pos ( lt_trans ( Real.sqrt_pos.mpr zero_lt_two ) hr ) ) ], by rw [ Ne.eq_def, div_eq_iff ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ⟩;
  · nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]
/-
Distance moved by the isosceles twist is at most `2√2 / ‖p - O‖`.
-/
lemma dist_twistAt_phi_le (O p : EuclideanSpace ℝ (Fin 2)) (hp : Real.sqrt 2 < ‖p - O‖) :
    dist (twistAt O (fun t => Real.arcsin (2 / t ^ 2)) p) p ≤ 2 * Real.sqrt 2 / ‖p - O‖ := by
  -- Use the fact that `dist (twistAt O φ p) p = ‖rot a v - v‖` and `‖rot a v - v‖^2 = 2*(1 - cos a)*r^2`.
  set v := p - O
  set r := ‖v‖
  set a := Real.arcsin (2 / r^2)
  have hdist : dist (twistAt O (fun t => Real.arcsin (2 / t^2)) p) p = ‖rot a v - v‖ := by
    unfold twistAt; simp +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
    simp +zetaDelta at *;
    norm_num [ EuclideanSpace.norm_eq ] ; ring
  have hnorm : ‖rot a v - v‖^2 = 2 * (1 - Real.cos a) * r^2 := by
    -- By definition of `rot`, we have `rot a v = !₂[Real.cos a * v 0 - Real.sin a * v 1, Real.sin a * v 0 + Real.cos a * v 1]`.
    have hrot : rot a v = !₂[Real.cos a * v 0 - Real.sin a * v 1, Real.sin a * v 0 + Real.cos a * v 1] := by
      rfl;
    rw [ hrot, EuclideanSpace.norm_eq ];
    simp +zetaDelta at *;
    rw [ Real.sq_sqrt <| by positivity ] ; rw [ EuclideanSpace.norm_eq ] ; norm_num ; ring;
    rw [ Real.sq_sqrt ] <;> try nlinarith [ sq_nonneg ( p.ofLp 0 - O.ofLp 0 ), sq_nonneg ( p.ofLp 1 - O.ofLp 1 ) ];
    rw [ Real.sin_sq, Real.cos_arcsin ] ; ring;
  -- Since $r > \sqrt{2}$, we have $0 < 2 / r^2 < 1$, so $\sin a = 2 / r^2$ and $\cos a \in [0, 1]$.
  have h_sin_cos : Real.sin a = 2 / r^2 ∧ 0 ≤ Real.cos a ∧ Real.cos a ≤ 1 := by
    rw [ Real.sin_arcsin, Real.cos_arcsin ];
    · exact ⟨ rfl, Real.sqrt_nonneg _, Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩ ⟩;
    · exact le_trans ( by norm_num ) ( div_nonneg zero_le_two ( sq_nonneg _ ) );
    · rw [ div_le_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
  -- Therefore, $1 - \cos a \leq (1 - \cos a)(1 + \cos a) = 1 - \cos^2 a = \sin^2 a = (2 / r^2)^2 = 4 / r^4$.
  have h_cos_sin : 1 - Real.cos a ≤ 4 / r^4 := by
    have := Real.sin_sq_add_cos_sq a; rw [ h_sin_cos.1 ] at this; ring_nf at this ⊢; nlinarith;
  rw [ le_div_iff₀ ] at * <;> try nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
  · rw [ ← Real.sqrt_sq ( show 0 ≤ 2 * Real.sqrt 2 by positivity ) ];
    exact Real.le_sqrt_of_sq_le ( by rw [ mul_pow, hdist ] ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ] );
  · exact pow_pos ( lt_trans ( Real.sqrt_pos.mpr zero_lt_two ) hp ) _
/-
**Core existence step.**  Given a density point `A` (radius `ε ∈ (0,1)`) and a far center `O`,
and a measure-preserving twist with small displacement, there is `p ∈ B(A, ε/2) ∩ S` whose twist
image also lies in `S`.
-/
lemma exists_twist_point (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : MeasurableSet S)
    (A O : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (ang : ℝ → ℝ)
    (hdens : volume (Metric.ball A ε \ S) < (1 / 10 : ENNReal) * volume (Metric.ball A ε))
    (hfar : 100 / ε + ε < dist O A)
    (hdiff : ∀ r : ℝ, 100 < r → DifferentiableAt ℝ ang r)
    (hbound : ∀ p : EuclideanSpace ℝ (Fin 2), dist p A < ε / 2 → dist (twistAt O ang p) p < ε / 2) :
    ∃ p, p ∈ Metric.ball A (ε / 2) ∧ p ∈ S ∧ twistAt O ang p ∈ S := by
  apply_rules [ @matching ];
  · intro T hT_sub hT_meas
    apply twistAt_volume O ang T hT_meas;
    · intro hO_in_closure_T
      have hO_in_closedBall : O ∈ Metric.closedBall A (ε / 2) := by
        exact closure_minimal ( hT_sub.trans ( Metric.ball_subset_closedBall ) ) ( Metric.isClosed_closedBall ) hO_in_closure_T;
      simp +zetaDelta at *;
      rw [ div_add', div_lt_iff₀ ] at hfar <;> nlinarith;
    · intro x hx
      have h_dist : dist x O ≥ dist O A - dist x A := by
        linarith [ dist_triangle_left O A x ]
      have h_dist_gt : dist x O > 100 := by
        nlinarith [ div_mul_cancel₀ 100 hε.ne', show dist x A < ε / 2 from hT_sub hx ]
      have h_norm_gt : ‖x - O‖ > 100 := by
        simpa only [ dist_eq_norm ] using h_dist_gt
      exact hdiff _ h_norm_gt;
  · intro p hp;
    simp_all +decide [ dist_eq_norm ];
    have := hbound p hp; rw [ show twistAt O ang p - A = ( twistAt O ang p - p ) + ( p - A ) by abel1 ] ; exact lt_of_le_of_lt ( norm_add_le _ _ ) ( by linarith ) ;
/-
**Geometry of the midpoint map.**  With angle `χ(t) = arcsin(4/t²)`, for `‖p - O‖ > 2` the points
`O`, `p`, `avgAt O χ p` form a right-angled triangle of area `1` (right angle at `avgAt O χ p`).
-/
lemma avgAt_right (O p : EuclideanSpace ℝ (Fin 2)) (hp : 2 < ‖p - O‖) :
    RightTriangleArea1 O p (avgAt O (fun t => Real.arcsin (4 / t ^ 2)) p) := by
  constructor;
  · unfold area2; norm_num [ EuclideanSpace.norm_eq ] at *;
    unfold avgAt; norm_num [ rot ] ; ring_nf ;
    rw [ Real.sin_arcsin ];
    · norm_num [ EuclideanSpace.norm_eq ] at *;
      rw [ Real.sq_sqrt ( by positivity ) ] ; ring_nf at *;
      grind;
    · exact le_trans ( by norm_num ) ( mul_nonneg ( sq_nonneg _ ) zero_le_four );
    · norm_num [ EuclideanSpace.norm_eq ] at *;
      rw [ inv_mul_eq_div, div_le_iff₀ ] <;> nlinarith [ Real.mul_self_sqrt ( add_nonneg ( sq_nonneg ( p.ofLp 0 - O.ofLp 0 ) ) ( sq_nonneg ( p.ofLp 1 - O.ofLp 1 ) ) ) ];
  · refine Or.inr <| Or.inr ?_;
    unfold avgAt; norm_num [ EuclideanSpace.norm_eq ] at *;
    norm_num [ rot, inner ] ; ring;
    rw [ Real.sin_sq, Real.cos_sq ] ; ring
/-
`arcsin (4/t²)` is differentiable at any `r` with `2 < r`.
-/
lemma chi_differentiableAt {r : ℝ} (hr : 2 < r) :
    DifferentiableAt ℝ (fun t => Real.arcsin (4 / t ^ 2)) r := by
  exact ( Real.differentiableAt_arcsin.2 ⟨ by rw [ Ne, div_eq_iff ] <;> nlinarith, by rw [ Ne, div_eq_iff ] <;> nlinarith ⟩ ) |> DifferentiableAt.comp r <| DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.pow 2 ) <| by positivity;
/-
Distance moved by the midpoint map is at most `2√2 / ‖p - O‖`.
-/
lemma dist_avgAt_chi_le (O p : EuclideanSpace ℝ (Fin 2)) (hp : 2 < ‖p - O‖) :
    dist (avgAt O (fun t => Real.arcsin (4 / t ^ 2)) p) p ≤ 2 * Real.sqrt 2 / ‖p - O‖ := by
  -- Let $v = p - O$, $r = ‖v‖$, and $a = \arcsin(4/r^2)$. Then $avgAt O \chi p - p = (1/2)(rot a v - v)$.
  set v : EuclideanSpace ℝ (Fin 2) := p - O
  set r := ‖v‖
  set a := Real.arcsin (4 / r ^ 2)
  have h_avg : avgAt O (fun t => Real.arcsin (4 / t ^ 2)) p - p = (1 / 2 : ℝ) • (rot a v - v) := by
    unfold avgAt;
    ext i ; norm_num ; ring!;
    norm_num [ div_eq_inv_mul ] ; ring!;
  -- Then ‖rot a v - v‖² = 2(1 - cos a)r². Since r² > 4, 0 < 4/r² ≤ 1, sin a = 4/r², cos a ∈ [0,1], 1 - cos a ≤ 1 - cos²a = sin²a = 16/r⁴.
  have h_norm_sq : ‖rot a v - v‖ ^ 2 ≤ 2 * (1 - Real.cos a) * r ^ 2 := by
    norm_num [ EuclideanSpace.norm_eq, rot ];
    rw [ Real.sq_sqrt <| by positivity ];
    rw [ show r ^ 2 = ‖v‖ ^ 2 by rfl, EuclideanSpace.norm_eq ] ; norm_num ; ring_nf;
    rw [ Real.sq_sqrt <| by positivity ] ; rw [ Real.sin_sq ] ; ring_nf ; norm_num
  have h_cos_sq : 1 - Real.cos a ≤ 16 / r ^ 4 := by
    rw [ Real.cos_arcsin ];
    ring_nf;
    nlinarith only [ show 0 ≤ r⁻¹ ^ 4 * 16 by positivity, Real.sqrt_nonneg ( 1 - r⁻¹ ^ 4 * 16 ), Real.mul_self_sqrt ( show 0 ≤ 1 - r⁻¹ ^ 4 * 16 by nlinarith [ show r⁻¹ ^ 4 ≤ 1 / 16 by exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( inv_anti₀ ( by positivity ) hp.le ) 4 ) ( by norm_num ) ] ) ];
  -- Hence ‖rot a v - v‖² ≤ 2·(16/r⁴)·r² = 32/r², so ‖rot a v - v‖ ≤ 4√2/r.
  have h_norm_le : ‖rot a v - v‖ ≤ 4 * Real.sqrt 2 / r := by
    rw [ le_div_iff₀ ( by positivity ) ] at *;
    nlinarith [ show 0 < r ^ 2 by positivity, show 0 < r ^ 4 by positivity, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
  rw [ dist_eq_norm, h_avg ];
  rw [ norm_smul, Real.norm_of_nonneg ] <;> ring_nf at * <;> linarith
/-
`arcsin (4/t²)` has non-positive derivative for `t > 2` (it is decreasing).
-/
lemma chi_deriv_nonpos {r : ℝ} (hr : 2 < r) :
    deriv (fun t => Real.arcsin (4 / t ^ 2)) r ≤ 0 := by
  erw [ deriv_comp _ ( Real.hasDerivAt_arcsin .. |> HasDerivAt.differentiableAt ) ] <;> norm_num;
  · norm_num [ show r ≠ 0 by linarith ];
    exact mul_nonpos_of_nonneg_of_nonpos ( inv_nonneg.2 ( Real.sqrt_nonneg _ ) ) ( div_nonpos_of_nonpos_of_nonneg ( by linarith ) ( sq_nonneg _ ) );
  · exact DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.pow 2 ) ( by positivity );
  · rw [ div_eq_iff ] <;> nlinarith;
  · rw [ div_eq_iff ] <;> nlinarith
/-
For `r > 100`, `cos (arcsin (4/r²)) ≥ 3/5`.
-/
lemma cos_chi_ge {r : ℝ} (hr : 100 < r) :
    (3 / 5 : ℝ) ≤ Real.cos (Real.arcsin (4 / r ^ 2)) := by
  rw [ Real.cos_arcsin ] ; exact Real.le_sqrt_of_sq_le ( by nlinarith [ show 0 ≤ 4 / r ^ 2 by positivity, show 4 / r ^ 2 ≤ 1 / 25 by rw [ div_le_iff₀ <| by positivity ] ; nlinarith ] ) ;
/-
Directional (line) derivative of the origin midpoint map at `x ≠ 0`.
-/
lemma avg_line_hasDerivAt (ang : ℝ → ℝ)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) (hang : DifferentiableAt ℝ ang ‖x‖)
    (v : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) • ((x + t • v) + rot (ang ‖x + t • v‖) (x + t • v)))
      ((1 / 2 : ℝ) • (v +
        (!₂[ Real.cos (ang ‖x‖) * v 0 - Real.sin (ang ‖x‖) * v 1
              - (deriv ang ‖x‖) * (inner ℝ x v / ‖x‖) * (Real.sin (ang ‖x‖) * x 0 + Real.cos (ang ‖x‖) * x 1),
            Real.sin (ang ‖x‖) * v 0 + Real.cos (ang ‖x‖) * v 1
              + (deriv ang ‖x‖) * (inner ℝ x v / ‖x‖) * (Real.cos (ang ‖x‖) * x 0 - Real.sin (ang ‖x‖) * x 1)]))) 0 := by
  convert HasDerivAt.const_smul ( 1 / 2 : ℝ ) ( HasDerivAt.add ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.smul ( hasDerivAt_id 0 ) ( hasDerivAt_const _ _ ) ) ) ( twist_line_hasDerivAt ang hx hang v ) ) using 2 ; norm_num
/-
The Jacobian determinant of the origin midpoint map at `x` with `100 < ‖x‖` is `≥ 4/5`.
-/
lemma avg_chi_det_ge {x : EuclideanSpace ℝ (Fin 2)} (hx : 100 < ‖x‖) :
    (4 / 5 : ℝ) ≤ (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 2) =>
      (1 / 2 : ℝ) • (w + rot ((fun t => Real.arcsin (4 / t ^ 2)) ‖w‖) w)) x).det := by
  have h_deriv : ∀ j : Fin 2, (fderiv ℝ (fun w => (1 / 2 : ℝ) • (w + rot ((fun t => Real.arcsin (4 / t ^ 2)) ‖w‖) w)) x) (EuclideanSpace.single j 1) =
    (1 / 2 : ℝ) • (EuclideanSpace.single j 1 +
      (!₂[ Real.cos (Real.arcsin (4 / ‖x‖ ^ 2)) * (EuclideanSpace.single j 1 0) - Real.sin (Real.arcsin (4 / ‖x‖ ^ 2)) * (EuclideanSpace.single j 1 1)
            - (deriv (fun t => Real.arcsin (4 / t ^ 2)) ‖x‖) * (inner ℝ x (EuclideanSpace.single j 1) / ‖x‖) * (Real.sin (Real.arcsin (4 / ‖x‖ ^ 2)) * x 0 + Real.cos (Real.arcsin (4 / ‖x‖ ^ 2)) * x 1),
          Real.sin (Real.arcsin (4 / ‖x‖ ^ 2)) * (EuclideanSpace.single j 1 0) + Real.cos (Real.arcsin (4 / ‖x‖ ^ 2)) * (EuclideanSpace.single j 1 1)
            + (deriv (fun t => Real.arcsin (4 / t ^ 2)) ‖x‖) * (inner ℝ x (EuclideanSpace.single j 1) / ‖x‖) * (Real.cos (Real.arcsin (4 / ‖x‖ ^ 2)) * x 0 - Real.sin (Real.arcsin (4 / ‖x‖ ^ 2)) * x 1)])) := by
              intro j;
              convert HasDerivAt.deriv ( avg_line_hasDerivAt ( fun t => Real.arcsin ( 4 / t ^ 2 ) ) ( show x ≠ 0 from by rintro rfl; norm_num at hx ) ( chi_differentiableAt ( show 2 < ‖x‖ from by linarith ) ) ( EuclideanSpace.single j 1 ) ) using 1;
              convert fderiv_dir _ _ _ _ using 1;
              convert DifferentiableAt.const_smul ( DifferentiableAt.add ( differentiableAt_id ) ( twist_differentiableAt _ _ _ ) ) _ using 1;
              rotate_left;
              exact ℝ;
              all_goals try infer_instance;
              exacts [ fun t => Real.arcsin ( 4 / t ^ 2 ), by rintro rfl; norm_num at hx, chi_differentiableAt ( show 2 < ‖x‖ from by linarith ), 1 / 2, by ext; norm_num ];
  convert ( show ( 4 : ℝ ) / 5 ≤ ( 1 / 2 ) * ( 1 + Real.cos ( Real.arcsin ( 4 / ‖x‖ ^ 2 ) ) ) - ( 1 / 4 ) * ( deriv ( fun t => Real.arcsin ( 4 / t ^ 2 ) ) ‖x‖ ) * ‖x‖ * Real.sin ( Real.arcsin ( 4 / ‖x‖ ^ 2 ) ) from ?_ ) using 1;
  · rw [ det_two ];
    simp_all +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_two ];
    norm_num [ EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right ] ; ring;
    rw [ Real.sin_sq, Real.cos_arcsin ] ; ring;
    grind;
  · refine' le_trans _ ( sub_le_sub_left ( mul_nonpos_of_nonpos_of_nonneg _ _ ) _ );
    · linarith [ cos_chi_ge hx ];
    · exact mul_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos ( by norm_num ) ( chi_deriv_nonpos ( by linarith ) ) ) ( by positivity );
    · exact Real.sin_nonneg_of_nonneg_of_le_pi ( Real.arcsin_nonneg.2 <| by positivity ) ( Real.arcsin_le_pi_div_two _ |> le_trans <| by linarith [ Real.pi_pos ] )
/-
The origin midpoint map (angle `χ`) is injective on the annulus `{w | 2 < ‖w‖}`.
-/
lemma avg_chi_inj :
    Set.InjOn (fun w : EuclideanSpace ℝ (Fin 2) =>
      (1 / 2 : ℝ) • (w + rot ((fun t => Real.arcsin (4 / t ^ 2)) ‖w‖) w))
      {w : EuclideanSpace ℝ (Fin 2) | 2 < ‖w‖} := by
  intros w₁ hw₁ w₂ hw₂ h_eq
  have h_norm : ‖w₁‖ = ‖w₂‖ := by
    have h_norm_eq : ‖w₁‖^2 / 2 + Real.sqrt (‖w₁‖^4 - 16) / 2 = ‖w₂‖^2 / 2 + Real.sqrt (‖w₂‖^4 - 16) / 2 := by
      have h_norm_sq : ∀ w : EuclideanSpace ℝ (Fin 2), 2 < ‖w‖ → ‖(1 / 2 : ℝ) • (w + rot (Real.arcsin (4 / ‖w‖ ^ 2)) w)‖ ^ 2 = ‖w‖ ^ 2 / 2 + Real.sqrt (‖w‖ ^ 4 - 16) / 2 := by
        intros w hw
        have h_norm_sq : ‖w + rot (Real.arcsin (4 / ‖w‖ ^ 2)) w‖ ^ 2 = 2 * ‖w‖ ^ 2 * (1 + Real.cos (Real.arcsin (4 / ‖w‖ ^ 2))) := by
          norm_num [ EuclideanSpace.norm_eq, rot ];
          rw [ Real.sq_sqrt <| by positivity ] ; ring;
          rw [ Real.sin_sq, Real.sq_sqrt <| by positivity ] ; ring;
        rw [ norm_smul, Real.norm_of_nonneg ] <;> norm_num [ h_norm_sq ] ; ring;
        rw [ show ( -16 + ‖w‖ ^ 4 : ℝ ) = ( ‖w‖ ^ 2 ) ^ 2 * ( 1 - 16 / ‖w‖ ^ 4 ) by nlinarith [ show 0 < ‖w‖ ^ 4 by positivity, div_mul_cancel₀ 16 ( show ( ‖w‖ ^ 4 : ℝ ) ≠ 0 by positivity ) ], Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ) ] ; ring_nf at * ; norm_num at *;
        rw [ h_norm_sq, Real.cos_arcsin ] ; ring;
      grind;
    have h_sqrt_eq : Real.sqrt (‖w₁‖^4 - 16) = Real.sqrt (‖w₂‖^4 - 16) := by
      by_contra h_contra;
      cases lt_or_gt_of_ne h_contra <;> nlinarith [ Real.mul_self_sqrt ( show 0 ≤ ‖w₁‖ ^ 4 - 16 by nlinarith [ show ‖w₁‖ ^ 2 > 4 by nlinarith [ hw₁.out ] ] ), Real.mul_self_sqrt ( show 0 ≤ ‖w₂‖ ^ 4 - 16 by nlinarith [ show ‖w₂‖ ^ 2 > 4 by nlinarith [ hw₂.out ] ] ), Real.sqrt_nonneg ( ‖w₁‖ ^ 4 - 16 ), Real.sqrt_nonneg ( ‖w₂‖ ^ 4 - 16 ) ];
    nlinarith [ show 0 < ‖w₁‖ by linarith [ hw₁.out ], show 0 < ‖w₂‖ by linarith [ hw₂.out ] ];
  have h_det : (1 + Real.cos (Real.arcsin (4 / ‖w₁‖ ^ 2))) ^ 2 + (Real.sin (Real.arcsin (4 / ‖w₁‖ ^ 2))) ^ 2 ≠ 0 := by
    exact ne_of_gt ( add_pos_of_pos_of_nonneg ( sq_pos_of_pos ( by nlinarith only [ Real.cos_sq' ( Real.arcsin ( 4 / ‖w₁‖ ^ 2 ) ), Real.sin_pos_of_pos_of_lt_pi ( show 0 < Real.arcsin ( 4 / ‖w₁‖ ^ 2 ) from Real.arcsin_pos.mpr ( by exact div_pos zero_lt_four ( sq_pos_of_pos ( by linarith [ hw₁.out ] ) ) ) ) ( by linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( 4 / ‖w₁‖ ^ 2 ) ] ) ] ) ) ( sq_nonneg _ ) );
  ext i; fin_cases i <;> simp_all +decide [ rot ];
  · have := congr_arg ( fun x => x 0 ) h_eq; norm_num at this; ( have := congr_arg ( fun x => x 1 ) h_eq; norm_num at this; );
    grind;
  · have := congr_arg ( fun x : EuclideanSpace ℝ ( Fin 2 ) => x 0 ) h_eq; have := congr_arg ( fun x : EuclideanSpace ℝ ( Fin 2 ) => x 1 ) h_eq; norm_num at * ;
    grobner
/-
**Measure lower bound for the midpoint map.**  For `ang = χ` and `T` avoiding `O` with all radii
`> 100`, the midpoint map expands measure by at least the factor `4/5`.
-/
lemma avgAt_volume_ge (O : EuclideanSpace ℝ (Fin 2))
    (T : Set (EuclideanSpace ℝ (Fin 2))) (hT : MeasurableSet T)
    (hbig : ∀ x ∈ T, 100 < ‖x - O‖) :
    (4 / 5 : ENNReal) * volume T ≤ volume (avgAt O (fun t => Real.arcsin (4 / t ^ 2)) '' T) := by
  -- Let χ t = arcsin(4/t²), M w = (1/2)•(w + rot(χ‖w‖)w), T' = T - {O}.
  set χ : ℝ → ℝ := fun t => Real.arcsin (4 / t ^ 2)
  set M : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun w => (1 / 2 : ℝ) • (w + rot (χ ‖w‖) w)
  set T' : Set (EuclideanSpace ℝ (Fin 2)) := (fun p => p - O) '' T;
  -- By the change-of-variables area formula, we have $\int_{T'} |(fderiv ℝ M y).det| \, dy = \text{volume}(M(T'))$.
  have h_change : ∫⁻ y in T', ENNReal.ofReal |(fderiv ℝ M y).det| = volume (M '' T') := by
    apply_rules [ MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image ];
    · convert hT.preimage ( show Measurable ( fun p : EuclideanSpace ℝ ( Fin 2 ) => p + O ) from measurable_id.add_const O ) using 1 ; aesop;
    · intro x hx
      have hx' : x ≠ 0 := by
        obtain ⟨ p, hp, rfl ⟩ := hx; specialize hbig p hp; contrapose! hbig; aesop;
      have h_diff : DifferentiableAt ℝ M x := by
        have h_diff : DifferentiableAt ℝ (fun w => rot (χ ‖w‖) w) x := by
          apply_rules [ twist_differentiableAt ];
          obtain ⟨ p, hp, rfl ⟩ := hx; exact chi_differentiableAt ( by linarith [ hbig p hp ] ) ;
        fun_prop
      exact h_diff.hasFDerivAt.hasFDerivWithinAt;
    · intro x hx y hy; obtain ⟨ p, hp, rfl ⟩ := hx; obtain ⟨ q, hq, rfl ⟩ := hy; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have := avg_chi_inj ( show 2 < ‖p - O‖ from by linarith [ hbig p hp ] ) ( show 2 < ‖q - O‖ from by linarith [ hbig q hq ] ) ; aesop;
  -- Since $|(fderiv ℝ M y).det| \geq 4/5$ for all $y \in T'$, we have $\int_{T'} |(fderiv ℝ M y).det| \, dy \geq \int_{T'} (4/5) \, dy$.
  have h_integral : ∫⁻ y in T', ENNReal.ofReal |(fderiv ℝ M y).det| ≥ ∫⁻ y in T', ENNReal.ofReal (4 / 5) := by
    have h_integral : ∀ y ∈ T', |(fderiv ℝ M y).det| ≥ 4 / 5 := by
      have h_det : ∀ y ∈ T', (fderiv ℝ M y).det ≥ 4 / 5 := by
        rintro _ ⟨ x, hx, rfl ⟩ ; exact avg_chi_det_ge ( by simpa using hbig x hx ) ;
      exact fun y hy => le_trans ( h_det y hy ) ( le_abs_self _ );
    refine' MeasureTheory.setLIntegral_mono' _ _;
    · convert hT.preimage ( show Measurable ( fun p : EuclideanSpace ℝ ( Fin 2 ) => p + O ) from measurable_id.add_const O ) using 1 ; aesop;
    · exact fun x hx => ENNReal.ofReal_le_ofReal <| h_integral x hx;
  convert h_integral.trans_eq h_change using 1;
  · norm_num [ ENNReal.ofReal_div_of_pos ];
    rw [ show T' = ( fun p => p + ( -O ) ) '' T by ext; aesop ];
    rw [ Set.image_add_right ];
    rw [ MeasureTheory.measure_preimage_add_right ];
  · rw [ show avgAt O χ '' T = ( fun p => p + O ) '' ( M '' T' ) from ?_ ];
    · rw [ Set.image_add_right ];
      rw [ MeasureTheory.measure_preimage_add_right ];
    · ext; simp [avgAt, M, T'];
      grind
/-
**Matching lemma, expanding version.**  If `f` expands measure by a factor `≥ 4/5` on subsets of
`B' = B(A, ε/2)` and maps `B'` into `B = B(A, ε)`, with `S` dense in `B`, then some `p ∈ B' ∩ S` has
`f p ∈ S`.
-/
lemma matching_ge (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : MeasurableSet S)
    (A : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 < ε)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hmap : ∀ T : Set (EuclideanSpace ℝ (Fin 2)), T ⊆ Metric.ball A (ε / 2) → MeasurableSet T →
      (4 / 5 : ENNReal) * volume T ≤ volume (f '' T))
    (hfB : Set.MapsTo f (Metric.ball A (ε / 2)) (Metric.ball A ε))
    (hdens : volume (Metric.ball A ε \ S) < (1 / 10 : ENNReal) * volume (Metric.ball A ε)) :
    ∃ p, p ∈ Metric.ball A (ε / 2) ∧ p ∈ S ∧ f p ∈ S := by
  by_contra! h_contra;
  -- Set T := ball A (ε/2) ∩ S (measurable, ⊆ ball A (ε/2)).
  set T := Metric.ball A (ε / 2) ∩ S
  have hT_meas : MeasurableSet T := by
    exact measurableSet_ball.inter hS
  have hT_subset : T ⊆ Metric.ball A (ε / 2) := by
    exact Set.inter_subset_left
  have hT_image_subset : f '' T ⊆ Metric.ball A ε \ S := by
    exact Set.image_subset_iff.mpr fun x hx => ⟨ hfB hx.1, h_contra x hx.1 hx.2 ⟩
  have hT_image_measure : volume (f '' T) ≥ (4 / 5) * volume T := by
    exact hmap T hT_subset hT_meas
  have hT_measure : volume T = volume (Metric.ball A (ε / 2)) - volume (Metric.ball A (ε / 2) \ S) := by
    rw [ ← MeasureTheory.measure_diff ] <;> norm_num [ hS ];
    · rfl;
    · grind;
    · exact MeasurableSet.nullMeasurableSet ( MeasurableSet.diff ( measurableSet_ball ) hS );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show Metric.ball A ( ε / 2 ) \ S ⊆ Metric.ball A ( ε / 2 ) from fun x hx => hx.1 ) ) ( by exact ( Metric.isBounded_ball.measure_lt_top ) ) )
  have hT_measure_le : volume (Metric.ball A (ε / 2) \ S) ≤ volume (Metric.ball A ε \ S) := by
    exact MeasureTheory.measure_mono ( Set.diff_subset_diff ( Metric.ball_subset_ball ( by linarith ) ) le_rfl )
  have hT_measure_le' : volume (Metric.ball A (ε / 2)) = volume (Metric.ball A ε) / 4 := by
    rw [ ← volume_ball_half A hε.le ] ; ring; norm_num;
    rw [ ENNReal.mul_div_cancel_right ] <;> norm_num
  have h_contradiction : volume (Metric.ball A ε \ S) ≥ (4 / 5) * (volume (Metric.ball A ε) / 4 - volume (Metric.ball A ε \ S)) := by
    refine' le_trans _ ( hT_image_measure.trans ( MeasureTheory.measure_mono hT_image_subset ) );
    gcongr;
    exact hT_measure ▸ hT_measure_le'.symm ▸ tsub_le_tsub_left hT_measure_le _
  have h_final : volume (Metric.ball A ε \ S) ≥ volume (Metric.ball A ε) / 10 := by
    contrapose! h_contradiction;
    refine' lt_of_lt_of_le h_contradiction _;
    rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num [ ENNReal.toReal_mul, ENNReal.toReal_ofReal, hε.le, Real.pi_pos.le ] ; ring_nf ; norm_num [ hε.le, Real.pi_pos.le ] ;
      · rw [ ← ENNReal.toReal_lt_toReal ] at * <;> norm_num at *;
        · rw [ ENNReal.toReal_ofReal ( by positivity ), ENNReal.toReal_ofReal ( by positivity ) ] at * ; nlinarith [ Real.pi_pos ] ;
        · exact ne_of_lt ( lt_of_lt_of_le hdens ( by exact le_top ) );
        · exact ENNReal.mul_ne_top ( by norm_num ) ( ENNReal.mul_ne_top ( by norm_num ) ( by norm_num ) );
        · exact ne_of_lt ( lt_of_lt_of_le h_contradiction ( by exact le_top ) );
        · norm_num [ ENNReal.div_eq_top ];
          exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
      · refine' le_trans h_contradiction.le _;
        rw [ show ( Metric.ball A ε : Set ( EuclideanSpace ℝ ( Fin 2 ) ) ) = ( Metric.ball A ε : Set ( EuclideanSpace ℝ ( Fin 2 ) ) ) from rfl, MeasureTheory.Measure.addHaar_ball ] <;> norm_num [ hε.le ] ; ring_nf ;
        gcongr ; norm_num;
      · norm_num [ ENNReal.mul_eq_top, ENNReal.div_eq_top ];
    · norm_num [ ENNReal.div_eq_top ];
      exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
    · simp +decide [ ENNReal.mul_eq_top ];
      norm_num [ ENNReal.div_eq_top ];
      exact fun h => absurd h ( by exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num ) )
  exact absurd h_final (by
  convert hdens using 1;
  rw [ ENNReal.div_eq_inv_mul ] ; norm_num)
/-
`S` (unbounded, positive measure, measurable) contains the vertices of a right-angled triangle of
area `1`.
-/
lemma exists_right (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : MeasurableSet S) (hpos : 0 < volume S) (hunb : ¬ Bornology.IsBounded S) :
    ∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ RightTriangleArea1 A B C := by
  -- Apply densityPoint to get A ∈ S, ε ∈ (0,1), and l.2.2.2.
  obtain ⟨A, hAS, ε, hε, hε1, hdens⟩ : ∃ A ∈ S, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ volume (Metric.ball A ε \ S) < (1/10 : ENNReal) * volume (Metric.ball A ε) := densityPoint hS hpos;
  obtain ⟨O, hOS, hOfar⟩ : ∃ O ∈ S, 100 / ε + ε < dist O A := by
    contrapose! hunb;
    exact isBounded_iff_forall_norm_le.mpr ⟨ 100 / ε + ε + ‖A‖, fun x hx => by simpa using le_trans ( norm_le_of_mem_closedBall <| show x ∈ Metric.closedBall A ( 100 / ε + ε ) from hunb x hx ) ( by linarith ) ⟩;
  -- Apply `matching_ge` to get `⟨p, hpB, hpS, hfpS⟩`.
  obtain ⟨p, hpB, hpS, hfpS⟩ : ∃ p, p ∈ Metric.ball A (ε / 2) ∧ p ∈ S ∧ avgAt O (fun t => Real.arcsin (4 / t ^ 2)) p ∈ S := by
    apply_rules [ matching_ge ];
    · intro T hT hmeasT
      apply avgAt_volume_ge O T hmeasT (by
      intro x hx
      have h_dist : dist x O ≥ dist O A - dist x A := by
        linarith [ dist_triangle_left O A x ]
      have h_dist_xA : dist x A < ε / 2 := by
        exact hT hx
      have h_dist_OA : dist O A > 100 / ε + ε := by
        exact hOfar
      have h_dist_xO : dist x O > 100 := by
        nlinarith [ mul_div_cancel₀ 100 hε.ne' ]
      exact (by
      simpa only [ dist_eq_norm ] using h_dist_xO));
    · intro p hp
      have h_dist : dist (avgAt O (fun t => Real.arcsin (4 / t ^ 2)) p) p ≤ 2 * Real.sqrt 2 / ‖p - O‖ := by
        apply dist_avgAt_chi_le;
        have := norm_sub_le ( p - O ) ( p - A ) ; simp_all +decide [ dist_eq_norm' ];
        rw [ norm_sub_rev p A ] at this ; nlinarith [ mul_div_cancel₀ 100 hε.ne' ];
      -- Since ‖p - O‖ > 100 / ε, we have 2 * Real.sqrt 2 / ‖p - O‖ < ε / 2.
      have h_bound : 2 * Real.sqrt 2 / ‖p - O‖ < ε / 2 := by
        have h_bound : ‖p - O‖ > 100 / ε := by
          have := dist_triangle_left O A p;
          linarith [ show dist p A < ε / 2 from hp, show dist p O = ‖p - O‖ from dist_eq_norm p O ];
        rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_div_cancel₀ 100 hε.ne', mul_pos hε ( Real.sqrt_pos.mpr zero_lt_two ) ];
      have := dist_triangle ( avgAt O ( fun t => Real.arcsin ( 4 / t ^ 2 ) ) p ) p A; norm_num at *; linarith;
  refine' ⟨ O, p, avgAt O ( fun t => Real.arcsin ( 4 / t ^ 2 ) ) p, hOS, hpS, hfpS, avgAt_right O p _ ⟩;
  rw [ dist_eq_norm' ] at hOfar;
  rw [ Metric.mem_ball, dist_eq_norm ] at hpB;
  have := norm_sub_le ( p - O ) ( p - A ) ; norm_num at * ; nlinarith [ mul_div_cancel₀ 100 hε.ne' ]
/-- `S` (unbounded, positive measure, measurable) contains the vertices of an isosceles triangle of
area `1`. -/
lemma exists_isosceles (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : MeasurableSet S) (hpos : 0 < volume S) (hunb : ¬ Bornology.IsBounded S) :
    ∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ IsoscelesTriangleArea1 A B C := by
  -- By density point, get A ∈ S, ε ∈ (0,1), hdens.
  obtain ⟨A, hAS, ε, hε, hε1, hdens⟩ := densityPoint hS hpos;
  obtain ⟨O, hOS, hOfar⟩ : ∃ O ∈ S, 100 / ε + ε < dist O A := farPoint hunb A (100 / ε + ε);
  obtain ⟨p, hpB, hpS, hfpS⟩ : ∃ p, p ∈ Metric.ball A (ε / 2) ∧ p ∈ S ∧ twistAt O (fun t => Real.arcsin (2 / t ^ 2)) p ∈ S := by
    apply exists_twist_point S hS A O hε hε1 (fun t => Real.arcsin (2 / t ^ 2)) hdens hOfar;
    · exact fun r hr => phi_differentiableAt <| by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
    · intro p hp
      have h_dist : dist (twistAt O (fun t => Real.arcsin (2 / t ^ 2)) p) p ≤ 2 * Real.sqrt 2 / ‖p - O‖ := by
        apply dist_twistAt_phi_le;
        have h_dist : ‖p - O‖ ≥ dist O A - dist p A := by
          have := dist_triangle_left O A p; simp_all +decide [ dist_eq_norm' ] ;
          simpa only [ norm_sub_rev ] using this;
        rw [ Real.sqrt_lt ] <;> nlinarith [ show ( 0 : ℝ ) ≤ 100 / ε by positivity, mul_div_cancel₀ 100 ( ne_of_gt hε ) ];
      -- Since ‖p - O‖ > 100 / ε, we have 2 * Real.sqrt 2 / ‖p - O‖ < ε / 2.
      have h_norm : ‖p - O‖ > 100 / ε := by
        have := dist_triangle_left O A p;
        linarith! [ dist_eq_norm' p O ];
      refine lt_of_le_of_lt h_dist ?_;
      rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_div_cancel₀ 100 hε.ne', mul_pos hε ( Real.sqrt_pos.mpr zero_lt_two ) ];
  refine' ⟨ O, p, twistAt O ( fun t => Real.arcsin ( 2 / t ^ 2 ) ) p, hOS, hpS, hfpS, _ ⟩;
  apply twistAt_isosceles;
  -- By the triangle inequality, we have ‖p - O‖ ≥ dist O A - dist p A.
  have h_triangle : ‖p - O‖ ≥ dist O A - dist p A := by
    simpa [ dist_eq_norm', norm_sub_rev ] using dist_triangle_left O A p;
  nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( 100 : ℝ ) / ε ≥ 100 by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;> linarith, show ( dist p A : ℝ ) < ε / 2 by simpa using hpB ]
/-- **Theorem 1.**  Let `S ⊆ ℝ²` be an unbounded measurable set of positive Lebesgue measure.
Then `S` contains the vertices of an isosceles triangle of area `1`, and also the vertices of a
right-angled triangle of area `1`. -/
theorem thm_iso_right (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : MeasurableSet S) (hpos : 0 < volume S) (hunb : ¬ Bornology.IsBounded S) :
    (∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ IsoscelesTriangleArea1 A B C) ∧
    (∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ RightTriangleArea1 A B C) :=
  ⟨exists_isosceles S hS hpos hunb, exists_right S hS hpos hunb⟩
/-
`psi R` is differentiable at `r` when `2 ≤ R` and `2 < r` (argument in `(-1,1)`).
-/
lemma psi_differentiableAt {R r : ℝ} (hR : 2 ≤ R) (hr : 2 < r) :
    DifferentiableAt ℝ (psi R) r := by
  -- Use the fact that `psi` differs from `chi` only by the factor `R^2/(R^2-1)` and establish:
  -- `0 < R^2/(R^2-1) ≤ 4/3` and `0 < 2/r^2 < 1/2` (so `0 < psi R r < 1`), hence `psi` is differentiable.
  have hr0 : 0 < r := by linarith;
  have hpos : 0 < R^2 / (R^2 - 1) ∧ R^2 / (R^2 - 1) ≤ 4 / 3 := by
    exact ⟨ div_pos ( by positivity ) ( by nlinarith ), by rw [ div_le_iff₀ ] <;> nlinarith ⟩;
  have harg : 0 < 2 / r^2 ∧ 2 / r^2 < 1 / 2 := by
    exact ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> nlinarith ⟩;
  have hlt : R^2 / (R^2 - 1) * (2 / r^2) < 1 := by
    nlinarith;
  exact DifferentiableAt.comp r ( Real.differentiableAt_arcsin.2 ⟨ by nlinarith, by nlinarith ⟩ ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.pow 2 ) ( by positivity ) ) )
/-
Distance moved by the trapezoid twist is at most `4 / ‖p - O‖` (for `2 ≤ R`, `‖p - O‖ > 2`).
-/
lemma dist_twistAt_psi_le {R : ℝ} (hR : 2 ≤ R) (O p : EuclideanSpace ℝ (Fin 2))
    (hp : 2 < ‖p - O‖) :
    dist (twistAt O (psi R) p) p ≤ 4 / ‖p - O‖ := by
  have h_dist : ‖rot (psi R ‖p - O‖) (p - O) - (p - O)‖^2 ≤ 16 / ‖p - O‖^2 := by
    -- Using the fact that `rot a v - v` has norm squared `2 * (1 - cos a) * r^2`
    have h_norm_sq : ‖rot (psi R ‖p - O‖) (p - O) - (p - O)‖^2 = 2 * (1 - Real.cos (psi R ‖p - O‖)) * ‖p - O‖^2 := by
      norm_num [ EuclideanSpace.norm_eq, rot ];
      rw [ Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity ] ; ring;
      rw [ Real.sin_sq ] ; ring;
    -- Using the fact that `sin a ≤ (4/3)*(2/r^2) = 8/(3r^2)` and `1 - cos a ≤ 1 - cos²a = sin²a`.
    have h_sin_a : Real.sin (psi R ‖p - O‖) ≤ 8 / (3 * ‖p - O‖^2) := by
      unfold psi;
      rw [ Real.sin_arcsin ];
      · field_simp;
        rw [ div_le_iff₀ ] <;> nlinarith only [ hR ];
      · exact le_trans ( by norm_num ) ( mul_nonneg ( div_nonneg ( sq_nonneg _ ) ( by nlinarith ) ) ( div_nonneg zero_le_two ( sq_nonneg _ ) ) );
      · rw [ div_mul_div_comm, div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( R - 2 ), mul_pos ( sub_pos.mpr hp ) ( sub_pos.mpr hp ) ];
    -- Using the fact that `1 - cos a ≤ 1 - cos²a = sin²a`.
    have h_cos_a : 1 - Real.cos (psi R ‖p - O‖) ≤ Real.sin (psi R ‖p - O‖)^2 := by
      nlinarith only [ Real.sin_sq_add_cos_sq ( psi R ‖p - O‖ ), show 0 ≤ Real.cos ( psi R ‖p - O‖ ) from Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, show psi R ‖p - O‖ ≥ 0 from Real.arcsin_nonneg.2 <| by exact mul_nonneg ( div_nonneg ( sq_nonneg _ ) <| by nlinarith ) <| by positivity ], by linarith [ Real.pi_pos, show psi R ‖p - O‖ ≤ Real.pi / 2 from Real.arcsin_le_pi_div_two _ ] ⟩ ];
    refine le_trans ( h_norm_sq.le.trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( h_cos_a.trans <| pow_le_pow_left₀ ( Real.sin_nonneg_of_nonneg_of_le_pi ( ?_ ) <| ?_ ) h_sin_a 2 ) zero_le_two ) <| sq_nonneg _ ) ) ?_;
    · exact Real.arcsin_nonneg.2 ( mul_nonneg ( div_nonneg ( sq_nonneg _ ) ( by nlinarith ) ) ( div_nonneg zero_le_two ( sq_nonneg _ ) ) );
    · exact le_trans ( Real.arcsin_le_pi_div_two _ ) ( by linarith [ Real.pi_pos ] );
    · field_simp;
      norm_num;
  convert Real.le_sqrt_of_sq_le h_dist using 1 <;> norm_num [ dist_eq_norm, twistAt ];
  exact congr_arg Norm.norm ( by abel1 )
/-
**Geometry of the trapezoid.**  For `2 ≤ R` and `‖p - O‖ > 2`, the four points `p`,
`twistAt O ψ_R p`, `conAt O R (twistAt O ψ_R p)`, `conAt O R p` form an isosceles trapezoid of
area `1`.
-/
lemma trapezoid_geom {R : ℝ} (hR : 2 ≤ R) (O p : EuclideanSpace ℝ (Fin 2)) (hr : 2 < ‖p - O‖) :
    IsoTrapArea1 p (twistAt O (psi R) p)
      (conAt O R (twistAt O (psi R) p)) (conAt O R p) := by
  constructor;
  · unfold quadArea twistAt conAt psi;
    unfold rot;
    rw [ Real.sin_arcsin, Real.cos_arcsin ];
    · simp +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_two ] at *;
      rw [ Real.sq_sqrt ( by positivity ) ] ; ring_nf ; norm_num [ show R ≠ 0 by linarith, show R ^ 2 - 1 ≠ 0 by nlinarith ] ;
      field_simp;
      rw [ abs_eq ] <;> norm_num;
      exact Or.inl <| by rw [ div_eq_iff <| mul_ne_zero ( by nlinarith ) <| by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ ( p.ofLp 0 - O.ofLp 0 ) ^ 2 + ( p.ofLp 1 - O.ofLp 1 ) ^ 2 by positivity ) ] ] ; ring;
    · exact le_trans ( by norm_num ) ( mul_nonneg ( div_nonneg ( sq_nonneg _ ) ( by nlinarith ) ) ( div_nonneg zero_le_two ( sq_nonneg _ ) ) );
    · rw [ div_mul_div_comm, div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( R - 2 ), mul_lt_mul_of_pos_left hr ( show 0 < R by linarith ) ];
  · refine' ⟨ _, _, _, _, _ ⟩;
    · unfold twistAt conAt;
      unfold rot; norm_num; ring;
    · unfold conAt twistAt;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
      exact congrArg Real.sqrt ( by nlinarith [ Real.sin_sq_add_cos_sq ( psi R ( Real.sqrt ( ( p.ofLp 0 - O.ofLp 0 ) ^ 2 + ( p.ofLp 1 - O.ofLp 1 ) ^ 2 ) ) ) ] );
    · unfold conAt; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
      unfold twistAt; norm_num [ rot_apply0, rot_apply1 ] ; ring;
      rw [ Real.sin_sq, Real.cos_sq ] ; ring;
    · unfold twistAt;
      unfold rot; intro h; have := congr_arg ( fun x => x 0 ) h; have := congr_arg ( fun x => x 1 ) h; norm_num at *;
      -- Since $\sin(\psi_R(\|p - O\|)) \neq 0$, we can divide both sides of the equation by $\sin(\psi_R(\|p - O\|))$.
      have h_sin_ne_zero : Real.sin (psi R ‖p - O‖) ≠ 0 := by
        unfold psi;
        rw [ Real.sin_arcsin ];
        · exact mul_ne_zero ( div_ne_zero ( by positivity ) ( by nlinarith ) ) ( div_ne_zero ( by positivity ) ( by positivity ) );
        · exact le_trans ( by norm_num ) ( mul_nonneg ( div_nonneg ( sq_nonneg _ ) ( by nlinarith ) ) ( div_nonneg zero_le_two ( sq_nonneg _ ) ) );
        · rw [ div_mul_div_comm, div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( R - 2 ), mul_pos ( sub_pos.mpr hr ) ( sub_pos.mpr hr ) ];
      -- Since $\sin(\psi_R(\|p - O\|)) \neq 0$, we can divide both sides of the equation by $\sin(\psi_R(\|p - O\|))$ to get a contradiction.
      have h_contra : (p.ofLp 0 - O.ofLp 0)^2 + (p.ofLp 1 - O.ofLp 1)^2 = 0 := by
        grind;
      norm_num [ show p = O by ext i; fin_cases i <;> nlinarith! only [ h_contra ] ] at *;
    · refine' ⟨ _, _, _, _, _ ⟩;
      · unfold twistAt conAt; norm_num;
        intro h; have := congr_arg ( fun x => ‖x‖ ) h; norm_num [ norm_rot ] at this;
        rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ] at this;
        rw [ norm_rot ] at this ; nlinarith [ inv_mul_cancel₀ ( by linarith : R ≠ 0 ) ];
      · unfold conAt twistAt;
        intro h; have := congr_arg ( fun x => x - O ) h; norm_num [ norm_smul, ne_of_gt ( zero_lt_two.trans_le hR ) ] at this;
        -- Since $rot (psi R ‖p - O‖) (p - O) = p - O$, we have $‖rot (psi R ‖p - O‖) (p - O) - (p - O)‖ = 0$.
        have h_norm_zero : ‖rot (psi R ‖p - O‖) (p - O) - (p - O)‖ = 0 := by
          rw [ this, sub_self, norm_zero ];
        -- Since $‖rot (psi R ‖p - O‖) (p - O) - (p - O)‖ = 0$, we have $2(1 - cos(psi R ‖p - O‖))‖p - O‖^2 = 0$.
        have h_cos_zero : 2 * (1 - Real.cos (psi R ‖p - O‖)) * ‖p - O‖^2 = 0 := by
          convert congr_arg ( · ^ 2 ) h_norm_zero using 1 ; norm_num [ EuclideanSpace.norm_eq ] ; ring;
          · rw [ Real.sq_sqrt, Real.sq_sqrt ] <;> try nlinarith [ sq_nonneg ( p.ofLp 0 - O.ofLp 0 ), sq_nonneg ( p.ofLp 1 - O.ofLp 1 ) ];
            · rw [ Real.sin_sq ] ; ring;
            · rw [ Real.sin_sq, Real.cos_sq ] ; ring;
              nlinarith [ sq_nonneg ( p.ofLp 0 - O.ofLp 0 ), sq_nonneg ( p.ofLp 1 - O.ofLp 1 ), Real.cos_le_one ( psi R ( Real.sqrt ( - ( p.ofLp 0 * O.ofLp 0 * 2 ) + p.ofLp 0 ^ 2 + ( O.ofLp 0 ^ 2 - p.ofLp 1 * O.ofLp 1 * 2 ) + p.ofLp 1 ^ 2 + O.ofLp 1 ^ 2 ) ) ) ];
          · norm_num;
        norm_num [ show ‖p - O‖ ≠ 0 by linarith ] at h_cos_zero;
        rw [ sub_eq_zero, eq_comm, Real.cos_eq_one_iff ] at h_cos_zero;
        obtain ⟨ n, hn ⟩ := h_cos_zero; rcases n with ⟨ _ | n ⟩ <;> norm_num at hn;
        · exact absurd hn ( ne_of_lt ( Real.arcsin_pos.mpr ( mul_pos ( div_pos ( by positivity ) ( by nlinarith ) ) ( div_pos ( by positivity ) ( by positivity ) ) ) ) );
        · unfold psi at hn;
          nlinarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( R ^ 2 / ( R ^ 2 - 1 ) * ( 2 / ‖p - O‖ ^ 2 ) ) ];
        · nlinarith [ Real.pi_pos, show 0 ≤ psi R ‖p - O‖ from Real.arcsin_nonneg.2 <| mul_nonneg ( div_nonneg ( sq_nonneg _ ) <| by nlinarith ) <| div_nonneg zero_le_two <| sq_nonneg _ ];
      · unfold conAt; intro H; have := congr_arg ( fun x => x - O ) H; norm_num at this;
        replace this := congr_arg ( fun x => ‖x‖ ) this ; norm_num at this;
        rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ] at this ; nlinarith [ inv_mul_cancel₀ ( by positivity : ( R : ℝ ) ≠ 0 ), norm_nonneg ( p - O ) ];
      · intro h_eq
        have h_norm : ‖p - O‖ = ‖conAt O R (twistAt O (psi R) p) - O‖ := by
          rw [ ← h_eq ];
        unfold conAt at h_norm;
        norm_num [ norm_smul, abs_of_nonneg ( by positivity : 0 ≤ R ) ] at h_norm;
        rw [ show twistAt O ( psi R ) p - O = rot ( psi R ‖p - O‖ ) ( p - O ) by rw [ twistAt ] ; norm_num ] at h_norm ; rw [ norm_rot ] at h_norm ; nlinarith [ inv_mul_cancel₀ ( by linarith : R ≠ 0 ) ];
      · unfold twistAt conAt;
        intro h; have := congr_arg ( fun x => x - O ) h; norm_num at this;
        replace this := congr_arg ( fun x => ‖x‖ ) this ; norm_num [ norm_rot ] at this;
        rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ] at this ; nlinarith [ inv_mul_cancel₀ ( by positivity : ( R : ℝ ) ≠ 0 ), norm_nonneg ( p - O ) ]
/-
**Density-one far point.**  A measurable set of infinite measure has a point `O ∈ S`, arbitrarily
far from `A`, at which `S` has density `1` (its complement has density `0`).
-/
lemma densityOnePoint {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S)
    (hinf : volume S = ⊤) (A : EuclideanSpace ℝ (Fin 2)) (M : ℝ) :
    ∃ O ∈ S, M < dist O A ∧
      Filter.Tendsto (fun δ => volume (Metric.ball O δ \ S) / volume (Metric.ball O δ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  contrapose! hinf; simp_all +decide [ MeasureTheory.Measure.restrict_apply ] ;
  -- By Besicovitch's density theorem, for volume.restrict S-a.e. x the ratio volume(S ∩ closedBall x r)/volume(closedBall x r) → 1.
  have h_density : ∀ᵐ x ∂(volume.restrict S), Filter.Tendsto (fun r => volume (S ∩ Metric.closedBall x r) / volume (Metric.closedBall x r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    convert Besicovitch.ae_tendsto_measure_inter_div volume S using 1;
  -- Converting closedBall to ball (spheres null) and to the complement, the set G of points where volume(ball x δ \ S)/volume(ball x δ) → 0 is co-null in S, i.e. volume(S \ G) = 0.
  have h_complement : ∀ᵐ x ∂(volume.restrict S), Filter.Tendsto (fun r => volume (Metric.ball x r \ S) / volume (Metric.ball x r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [ h_density ] with x hx;
    have h_complement : ∀ r > 0, volume (Metric.ball x r \ S) = volume (Metric.ball x r) - volume (S ∩ Metric.ball x r) := by
      intro r hr; rw [ ← MeasureTheory.measure_diff ] <;> norm_num [ hS, hr ] ;
      · exact hS.nullMeasurableSet.inter ( measurableSet_ball.nullMeasurableSet );
      · finiteness;
    have h_complement : ∀ r > 0, volume (Metric.ball x r \ S) / volume (Metric.ball x r) = 1 - volume (S ∩ Metric.ball x r) / volume (Metric.ball x r) := by
      intro r hr; rw [ h_complement r hr, ENNReal.sub_div ] ;
      · rw [ ENNReal.div_self ] <;> norm_num [ hr ];
        · positivity;
        · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
      · grind;
    have h_complement : Filter.Tendsto (fun r => volume (S ∩ Metric.ball x r) / volume (Metric.ball x r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have h_complement : ∀ r > 0, volume (S ∩ Metric.ball x r) = volume (S ∩ Metric.closedBall x r) := by
        intro r hr; rw [ MeasureTheory.measure_congr ] ; filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( show MeasureTheory.MeasureSpace.volume ( Metric.sphere x r ) = 0 from by
                                                                                                                            rw [ MeasureTheory.Measure.addHaar_sphere ] ) ] with y hy; simp_all +decide [ Metric.mem_ball, Metric.mem_closedBall ] ;
        exact ⟨ fun h => ⟨ h.1, Metric.mem_closedBall.mpr <| le_of_lt h.2 ⟩, fun h => ⟨ h.1, lt_of_le_of_ne ( Metric.mem_closedBall.mp h.2 ) hy ⟩ ⟩;
      have h_complement : ∀ r > 0, volume (Metric.ball x r) = volume (Metric.closedBall x r) := by
        intro r hr; rw [ MeasureTheory.Measure.addHaar_closedBall ] ; norm_num [ hr.le ] ;
        positivity;
      exact Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun r hr => by rw [ ‹∀ r > 0, volume ( S ∩ Metric.ball x r ) = volume ( S ∩ Metric.closedBall x r ) › r hr, h_complement r hr ] ) hx;
    rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun r hr => by rw [ ‹∀ r > 0, volume ( Metric.ball x r \ S ) / volume ( Metric.ball x r ) = 1 - volume ( S ∩ Metric.ball x r ) / volume ( Metric.ball x r ) › r hr ] ) ] ; convert ENNReal.Tendsto.sub tendsto_const_nhds h_complement _ using 1 <;> norm_num;
  rw [ MeasureTheory.ae_iff ] at h_complement;
  rw [ MeasureTheory.Measure.restrict_apply' ] at h_complement;
  · -- Since $S$ is contained in the union of the set where the complement density does not tend to 0 and the closed ball of radius $M$ centered at $A$, and the volume of the closed ball is finite, the volume of $S$ must also be finite.
    have h_finite : volume S ≤ volume ({a | ¬Filter.Tendsto (fun r => volume (Metric.ball a r \ S) / volume (Metric.ball a r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)} ∩ S) + volume (Metric.closedBall A M) := by
      refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
      intro x hx; by_cases hx' : M < dist x A <;> simp_all +decide [ dist_comm ] ;
    exact ne_of_lt ( lt_of_le_of_lt h_finite ( by rw [ h_complement ] ; exact ENNReal.add_lt_top.mpr ⟨ by norm_num, by exact ( Metric.isBounded_closedBall.measure_lt_top ) ⟩ ) );
  · exact hS
/-
**The `S_R` density step.**  Given a density point `A` and a density-one far center `O`, for some
`R ≥ 2` the refined set `S_R = {x | x ∈ S ∧ conAt O R x ∈ S}` is still dense in `B(A, ε)`.
-/
lemma exists_SR {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S)
    (A O : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hdens : volume (Metric.ball A ε \ S) < (1 / 10 : ENNReal) * volume (Metric.ball A ε))
    (hfar : 100 / ε + ε < dist O A)
    (hdens1 : Filter.Tendsto (fun δ => volume (Metric.ball O δ \ S) / volume (Metric.ball O δ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∃ R : ℝ, 2 ≤ R ∧
      volume (Metric.ball A ε \ {x | x ∈ S ∧ conAt O R x ∈ S}) <
        (1 / 10 : ENNReal) * volume (Metric.ball A ε) := by
  -- Let $d = \text{dist}(O, A)$ and $B = \text{Metric.ball}(A, \epsilon)$.
  set d := dist O A with hd
  set B := Metric.ball A ε with hB;
  -- For $x \in B$, $conAt O R x \in ball O (2d/R)$ (since $‖conAt O R x - O‖ = R⁻¹‖x-O‖ < R⁻¹(ε+d) ≤ 2d/R$ as $ε < d$).
  have h_conAt_ball : ∀ R : ℝ, 2 ≤ R → ∀ x ∈ B, conAt O R x ∈ Metric.ball O (2 * d / R) := by
    intros R hR x hx
    have h_conAt_ball : ‖conAt O R x - O‖ < 2 * d / R := by
      have h_conAt_ball : ‖x - O‖ < 2 * d := by
        have h_conAt_ball : ‖x - O‖ ≤ ‖x - A‖ + ‖A - O‖ := by
          simpa using norm_add_le ( x - A ) ( A - O );
        simp_all +decide [ dist_eq_norm' ];
        linarith [ norm_sub_rev x A, show ‖A - O‖ > 100 by nlinarith [ div_mul_cancel₀ 100 hε.ne' ] ];
      unfold conAt; norm_num [ norm_smul, abs_of_nonneg ( by positivity : 0 ≤ R ) ] ; ring_nf at *; nlinarith [ inv_mul_cancel₀ ( by positivity : ( R : ℝ ) ≠ 0 ) ] ;
    exact h_conAt_ball;
  -- Set `bad R := B ∩ {x | conAt O R x ∉ S}`. Then `bad R ⊆ conAt O R ⁻¹'(ball O (2d/R) \ S)`, and since the homothety `conAt O R` scales volume of preimages by `R²`, `volume (bad R) ≤ R²·volume(ball O (2d/R) \ S)`.
  have h_bad_R : ∀ R : ℝ, 2 ≤ R → volume (B ∩ {x | conAt O R x ∉ S}) ≤ ENNReal.ofReal (R^2) * volume (Metric.ball O (2 * d / R) \ S) := by
    intro R hR;
    have h_bad_R_subset : B ∩ {x | conAt O R x ∉ S} ⊆ (fun x => O + R • (x - O)) '' (Metric.ball O (2 * d / R) \ S) := by
      intro x hx;
      use conAt O R x; simp_all +decide [ conAt ] ;
      simp +decide [ show R ≠ 0 by linarith ];
    refine' le_trans ( MeasureTheory.measure_mono h_bad_R_subset ) _;
    have h_volume_image : ∀ (T : Set (EuclideanSpace ℝ (Fin 2))), MeasurableSet T → volume ((fun x => O + R • (x - O)) '' T) = ENNReal.ofReal (R^2) * volume T := by
      intro T hT
      have h_volume_image : volume ((fun x => R • x) '' (T - {O})) = ENNReal.ofReal (R^2) * volume (T - {O}) := by
        norm_num [ abs_of_nonneg ( by positivity : 0 ≤ R ) ];
      convert h_volume_image using 1;
      · rw [ show ( fun x => O + R • ( x - O ) ) '' T = ( fun x => R • x ) '' ( T - { O } ) + { O } from ?_ ];
        · simp +decide [ Set.add_singleton ];
        · ext; simp [Set.mem_image];
          simp +decide [ Set.mem_smul_set, eq_comm ];
          grind +qlia;
      · simp +decide [ sub_eq_add_neg ];
    rw [ h_volume_image _ ( measurableSet_ball.diff hS ) ];
  -- Writing `g δ = volume(ball O δ \ S)/volume(ball O δ)` and using `volume(ball O δ) = ofReal(δ²)·volume(ball 0 1)`, we get `R²·volume(ball O (2d/R)\S) = volume(ball O (2d))·g(2d/R)`.
  have h_volume_bad_R : ∀ R : ℝ, 2 ≤ R → volume (B ∩ {x | conAt O R x ∉ S}) ≤ volume (Metric.ball O (2 * d)) * (volume (Metric.ball O (2 * d / R) \ S) / volume (Metric.ball O (2 * d / R))) := by
    intro R hR
    have h_volume_ball : volume (Metric.ball O (2 * d)) = ENNReal.ofReal ((2 * d)^2) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      convert MeasureTheory.Measure.addHaar_ball ( MeasureTheory.MeasureSpace.volume ) O ( show 0 ≤ 2 * d by exact mul_nonneg zero_le_two ( dist_nonneg ) ) using 1;
      norm_num
    have h_volume_ball_R : volume (Metric.ball O (2 * d / R)) = ENNReal.ofReal ((2 * d / R)^2) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      have := @MeasureTheory.Measure.addHaar_ball ( EuclideanSpace ℝ ( Fin 2 ) );
      convert this volume O ( show 0 ≤ 2 * d / R by exact div_nonneg ( mul_nonneg zero_le_two ( dist_nonneg ) ) ( by positivity ) ) using 1 ; norm_num;
    refine le_trans ( h_bad_R R hR ) ?_;
    rw [ h_volume_ball, h_volume_ball_R, mul_div ];
    rw [ ENNReal.le_div_iff_mul_le ];
    · rw [ show ( 2 * d ) ^ 2 = ( 2 * d / R ) ^ 2 * R ^ 2 by rw [ div_pow, div_mul_cancel₀ _ ( by positivity ) ] ] ; rw [ ENNReal.ofReal_mul ( by positivity ) ] ; ring_nf ; norm_num;
    · simp +zetaDelta at *;
      exact Or.inl ⟨ ⟨ by rintro rfl; norm_num at hfar; linarith [ div_pos ( by norm_num : ( 0 : ℝ ) < 100 ) hε ], by linarith ⟩, Real.pi_pos ⟩;
    · exact Or.inl <| ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) <| by exact ne_of_lt <| by exact ( Metric.isBounded_ball.measure_lt_top ) ;
  -- As $R \to \infty$, $2d/R \to 0⁺$ so $g(2d/R) \to 0$ (hdens1), hence $volume(bad R) \to 0$.
  have h_volume_bad_R_zero : Filter.Tendsto (fun R : ℝ => volume (B ∩ {x | conAt O R x ∉ S})) Filter.atTop (nhds 0) := by
    have h_volume_bad_R_zero : Filter.Tendsto (fun R : ℝ => volume (Metric.ball O (2 * d)) * (volume (Metric.ball O (2 * d / R) \ S) / volume (Metric.ball O (2 * d / R)))) Filter.atTop (nhds 0) := by
      convert ENNReal.Tendsto.const_mul ( hdens1.comp _ ) _ using 2;
      · norm_num;
      · rw [ tendsto_nhdsWithin_iff ];
        exact ⟨ tendsto_const_nhds.div_atTop Filter.tendsto_id, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => div_pos ( mul_pos zero_lt_two ( lt_of_le_of_lt ( by positivity ) hfar ) ) ( by positivity ) ⟩ ⟩;
      · exact Or.inr ( ne_of_lt ( IsCompact.measure_lt_top ( ProperSpace.isCompact_closedBall _ _ ) |> lt_of_le_of_lt ( MeasureTheory.measure_mono ( Metric.ball_subset_closedBall ) ) ) );
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_volume_bad_R_zero ( Filter.eventually_atTop.mpr ⟨ 2, fun R hR => zero_le _ ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 2, fun R hR => h_volume_bad_R R hR ⟩ );
  -- Now $B \ S_R \subseteq (B \ S) \cup bad R$, so $volume(B \ S_R) \le volume(B \ S) + volume(bad R)$.
  have h_volume_B_S_R : ∀ R : ℝ, 2 ≤ R → volume (B \ {x | x ∈ S ∧ conAt O R x ∈ S}) ≤ volume (B \ S) + volume (B ∩ {x | conAt O R x ∉ S}) := by
    intro R hR; refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ ) ; intro x ; by_cases hx : x ∈ S <;> by_cases hx' : conAt O R x ∈ S <;> aesop;
  have := h_volume_bad_R_zero.eventually ( gt_mem_nhds <| show 0 < 1 / 10 * volume B - volume ( B \ S ) from tsub_pos_of_lt hdens ) ; have := this.and ( Filter.eventually_ge_atTop 2 ) ; obtain ⟨ R, hR₁, hR₂ ⟩ := this.exists; use R;
  rw [ lt_tsub_iff_left ] at hR₁;
  exact ⟨ hR₂, lt_of_le_of_lt ( h_volume_B_S_R R hR₂ ) hR₁ ⟩
/-- **Theorem 2.**  Let `S ⊆ ℝ²` be a measurable set of infinite Lebesgue measure.  Then `S`
contains the four vertices of an isosceles trapezoid of area `1`. -/
theorem thm_trapezoid (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : MeasurableSet S) (hinf : volume S = ⊤) :
    ∃ A B C D, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ IsoTrapArea1 A B C D := by
  have hpos : 0 < volume S := by rw [hinf]; exact ENNReal.zero_lt_top
  obtain ⟨A, hAS, ε, hε, hε1, hdens⟩ := densityPoint hS hpos
  obtain ⟨O, hOS, hOfar', hdens1⟩ := densityOnePoint hS hinf A (100 / ε + ε)
  have hOfar : 100 / ε + ε < dist O A := hOfar'
  obtain ⟨R, hR, hdensSR⟩ := exists_SR hS A O hε hε1 hdens hOfar hdens1
  set SR : Set (EuclideanSpace ℝ (Fin 2)) := {x | x ∈ S ∧ conAt O R x ∈ S} with hSR_def
  have hcon : Measurable (conAt O R) := by
    unfold conAt; fun_prop
  have hSR : MeasurableSet SR := hS.inter (hcon hS)
  obtain ⟨p, hpB, hpSR, hfpSR⟩ :=
    exists_twist_point SR hSR A O hε hε1 (psi R) hdensSR hOfar
      (fun r hr => psi_differentiableAt hR (by linarith))
      (by
        intro q hq
        have hqO : 100 / ε < ‖q - O‖ := by
          have h1 : dist O A ≤ dist O q + dist q A := dist_triangle O q A
          have h2 : dist O q = ‖q - O‖ := by rw [dist_eq_norm']
          have : (0:ℝ) < 100 / ε := by positivity
          nlinarith [dist_nonneg (x := q) (y := A)]
        have hb := dist_twistAt_psi_le hR O q (by
          have : (100:ℝ) / ε ≥ 100 := by rw [ge_iff_le, le_div_iff₀ hε]; nlinarith
          linarith)
        have hpos' : (0:ℝ) < ‖q - O‖ := by linarith [show (100:ℝ)/ε > 0 by positivity]
        have : 4 / ‖q - O‖ < ε / 2 := by
          rw [div_lt_iff₀ hpos']
          have : (100:ℝ) / ε * ε = 100 := by field_simp
          nlinarith [mul_pos hε hpos']
        linarith)
  have hr2 : 2 < ‖p - O‖ := by
    have h1 : dist O A ≤ dist O p + dist p A := dist_triangle O p A
    have h2 : dist O p = ‖p - O‖ := by rw [dist_eq_norm']
    have h3 : dist p A < ε / 2 := by simpa [Metric.mem_ball] using hpB
    have : (100:ℝ) / ε ≥ 100 := by rw [ge_iff_le, le_div_iff₀ hε]; nlinarith
    nlinarith
  exact ⟨p, twistAt O (psi R) p, conAt O R (twistAt O (psi R) p), conAt O R p,
    hpSR.1, hfpSR.1, hfpSR.2, hpSR.2, trapezoid_geom hR O p hr2⟩

end Koizumi

-- ============================================================
-- KovacPredojevicT1
-- ============================================================

namespace CyclicQuad
/- ===================== Defs ===================== -/
/-- A point of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)
/-- Signed orientation (twice the signed area) of the triangle `X Y Z`. -/
noncomputable def orient (X Y Z : Pt) : ℝ :=
  (Y 0 - X 0) * (Z 1 - X 1) - (Z 0 - X 0) * (Y 1 - X 1)
/-- Signed area of the quadrilateral with vertices `P Q R S` in this order (shoelace formula). -/
noncomputable def quadArea (P Q R S : Pt) : ℝ :=
  ((P 0 * Q 1 - Q 0 * P 1) + (Q 0 * R 1 - R 0 * Q 1) +
   (R 0 * S 1 - S 0 * R 1) + (S 0 * P 1 - P 0 * S 1)) / 2
/-- Four points are concyclic: they lie on a common circle of positive radius. -/
def Concyclic4 (P Q R S : Pt) : Prop :=
  ∃ (O : Pt) (r : ℝ), 0 < r ∧ dist P O = r ∧ dist Q O = r ∧ dist R O = r ∧ dist S O = r
/-- `P Q R S` form a strictly convex counterclockwise quadrilateral (all turns are left turns). -/
def ConvexQuadCCW (P Q R S : Pt) : Prop :=
  0 < orient P Q R ∧ 0 < orient Q R S ∧ 0 < orient R S P ∧ 0 < orient S P Q
/-- `P Q R S` are the vertices of a (non-degenerate) cyclic quadrilateral of area `1`,
listed in their convex counterclockwise cyclic order. -/
def UnitCyclicQuad (P Q R S : Pt) : Prop :=
  Concyclic4 P Q R S ∧ ConvexQuadCCW P Q R S ∧ quadArea P Q R S = 1
/-- An orientation-preserving rigid motion of the plane (rotation by `(a,b)` with `a²+b²=1`
followed by the translation `(v₁,v₂)`). -/
noncomputable def rigid (a b v1 v2 : ℝ) (p : Pt) : Pt :=
  !₂[a * p 0 - b * p 1 + v1, b * p 0 + a * p 1 + v2]
/-- `C` is a Lebesgue density point of `S` (using closed balls, as in Besicovitch's theorem). -/
def IsDensityPt (S : Set Pt) (C : Pt) : Prop :=
  Tendsto (fun r : ℝ => volume (S ∩ Metric.closedBall C r) / volume (Metric.closedBall C r))
    (𝓝[>] 0) (𝓝 1)
/-- The geometric configuration produced by the first half of the proof:
a non-degenerate triangle `A=(0,0)`, `B=(c,0)`, `C=(xC,yC)` of area `1` with vertices in `S`,
and with `C` a density point of `S`. -/
structure Config (S : Set Pt) (c xC yC : ℝ) : Prop where
  c_pos : 0 < c
  yC_pos : 0 < yC
  /-- `area △ABC = 1`, i.e. `c·yC = 2`. -/
  area : c * yC = 2
  memA : (!₂[(0 : ℝ), (0 : ℝ)] : Pt) ∈ S
  memB : (!₂[c, (0 : ℝ)] : Pt) ∈ S
  memC : (!₂[xC, yC] : Pt) ∈ S
  meas : MeasurableSet S
  dens : IsDensityPt S (!₂[xC, yC] : Pt)
/-- The signed orientation is invariant under orientation-preserving rigid motions. -/
lemma orient_rigid {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (X Y Z : Pt) :
    orient (rigid a b v1 v2 X) (rigid a b v1 v2 Y) (rigid a b v1 v2 Z) = orient X Y Z := by
  unfold orient rigid; norm_num
  linear_combination ((Y 0 - X 0) * (Z 1 - X 1) - (Z 0 - X 0) * (Y 1 - X 1)) * hab
/-- The shoelace area is invariant under orientation-preserving rigid motions. -/
lemma quadArea_rigid {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (P Q R S : Pt) :
    quadArea (rigid a b v1 v2 P) (rigid a b v1 v2 Q) (rigid a b v1 v2 R) (rigid a b v1 v2 S)
      = quadArea P Q R S := by
  unfold quadArea
  unfold rigid; norm_num [Fin.sum_univ_succ]; ring_nf
  rw [show b ^ 2 = 1 - a ^ 2 by linarith]; ring
/-- A rigid motion is an isometry. -/
lemma dist_rigid {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (P Q : Pt) :
    dist (rigid a b v1 v2 P) (rigid a b v1 v2 Q) = dist P Q := by
  norm_num [dist_eq_norm, EuclideanSpace.norm_eq, rigid]
  congr 1
  linear_combination ((P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2) * hab
/-- Being the vertices of a unit cyclic quadrilateral is invariant under orientation-preserving
rigid motions. -/
lemma unitCyclicQuad_rigid_iff {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (P Q R S : Pt) :
    UnitCyclicQuad (rigid a b v1 v2 P) (rigid a b v1 v2 Q) (rigid a b v1 v2 R)
        (rigid a b v1 v2 S)
      ↔ UnitCyclicQuad P Q R S := by
  constructor <;> intro h
  · refine ⟨?_, ?_, ?_⟩
    · obtain ⟨O, r, hr, hO⟩ := h.1
      have h_surjective : ∀ O' : Pt, ∃ O : Pt, rigid a b v1 v2 O = O' := by
        intro O'
        use !₂[a * (O' 0 - v1) + b * (O' 1 - v2), -b * (O' 0 - v1) + a * (O' 1 - v2)]
        ext i; fin_cases i <;> norm_num [rigid] <;> ring_nf
        · linear_combination' hab * O'.ofLp 0 - hab * v1
        · linear_combination' hab * O'.ofLp 1 - hab * v2
      obtain ⟨O', rfl⟩ := h_surjective O
      exact ⟨O', r, hr, by simpa [dist_rigid hab] using hO⟩
    · exact ⟨by simpa [orient_rigid hab] using h.2.1.1,
        by simpa [orient_rigid hab] using h.2.1.2.1,
        by simpa [orient_rigid hab] using h.2.1.2.2.1,
        by simpa [orient_rigid hab] using h.2.1.2.2.2⟩
    · exact h.2.2 ▸ quadArea_rigid hab P Q R S ▸ rfl
  · constructor
    · obtain ⟨O, r, hr, hO⟩ := h.1
      exact ⟨rigid a b v1 v2 O, r, hr, by simpa [dist_rigid hab] using hO⟩
    · exact ⟨by simpa [ConvexQuadCCW, orient_rigid hab] using h.2.1,
        by rw [quadArea_rigid hab]; exact h.2.2⟩
/- ===================== Config ===================== -/
/-- The closed "upper" right-angled sector `{ p : |p₀| ≤ p₁ }`.  The part of this sector below any
horizontal line is a bounded triangle, hence of finite area. -/
def sectorUp : Set Pt := {p : Pt | |p 0| ≤ p 1}
/-
`rigid` is continuous.
-/
lemma continuous_rigid (a b v1 v2 : ℝ) : Continuous (rigid a b v1 v2) := by
  refine' Continuous.comp _ _;
  · fun_prop (disch := norm_num);
  · refine' continuous_pi_iff.mpr _;
    intro i; fin_cases i <;> apply_rules [ Continuous.sub, Continuous.add, Continuous.mul, continuous_const, continuous_apply ] ;
    · exact continuous_apply _ |> Continuous.comp <| continuous_induced_dom;
    · exact continuous_apply _ |> Continuous.comp <| continuous_induced_dom;
    · fun_prop;
    · fun_prop
/-- Composition of a rotation `rigid a b 0 0` with a translation `rigid 1 0 v1 v2`. -/
lemma rigid_one_zero_comp (a b v1 v2 : ℝ) (p : Pt) :
    rigid 1 0 v1 v2 (rigid a b 0 0 p) = rigid a b v1 v2 p := by
  simp [rigid]
/-- Image form of the previous composition lemma. -/
lemma image_rigid_one_zero_comp (a b v1 v2 : ℝ) (A : Set Pt) :
    rigid 1 0 v1 v2 '' (rigid a b 0 0 '' A) = rigid a b v1 v2 '' A := by
  rw [Set.image_image]
  exact Set.image_congr' (rigid_one_zero_comp a b v1 v2)
/-
The image of a measurable set under a rigid motion is measurable.
-/
lemma measurableSet_rigid_image {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    {A : Set Pt} (hA : MeasurableSet A) :
    MeasurableSet (rigid a b v1 v2 '' A) := by
  have h_measurable : Measurable (rigid a b v1 v2) ∧ Measurable (fun p : Pt => rigid (a) (-b) (-(a * v1 - b * v2)) (-(b * v1 + a * v2)) p) := by
    exact ⟨ continuous_rigid a b v1 v2 |> Continuous.measurable, continuous_rigid a ( -b ) ( - ( a * v1 - b * v2 ) ) ( - ( b * v1 + a * v2 ) ) |> Continuous.measurable ⟩;
  have h_measurable : MeasurableEmbedding (rigid a b v1 v2) := by
    refine' h_measurable.1.measurableEmbedding _;
    intro p q h_eq;
    ext i; fin_cases i <;> simp_all +decide [ rigid ]; all_goals grind;
  exact h_measurable.measurableSet_image.mpr hA
/-
A rigid motion preserves Lebesgue measure of sets.
-/
lemma volume_rigid_image {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (A : Set Pt) :
    volume (rigid a b v1 v2 '' A) = volume A := by
  unfold rigid;
  -- The translation part does not affect the volume, so we can focus on the linear part.
  have h_volume_linear : volume ((fun p : Pt => !₂[a * p 0 - b * p 1, b * p 0 + a * p 1]) '' A) = volume A := by
    have h_volume_linear : volume (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => Matrix.toLin (PiLp.basisFun 2 ℝ (Fin 2)) (PiLp.basisFun 2 ℝ (Fin 2)) (Matrix.of ![![a, -b], ![b, a]]) p) A) = volume A := by
      norm_num [ ← sq, hab ];
    convert h_volume_linear using 4 ; ring_nf!;
    erw [ Matrix.toLin_apply ] ; ext i ; fin_cases i <;> norm_num <;> ring!;
  rw [ ← h_volume_linear ];
  rw [ show ( fun p : Pt => !₂[a * p.ofLp 0 - b * p.ofLp 1 + v1, b * p.ofLp 0 + a * p.ofLp 1 + v2] ) '' A = ( fun p : Pt => p + !₂[v1, v2] ) '' ( ( fun p : Pt => !₂[a * p.ofLp 0 - b * p.ofLp 1, b * p.ofLp 0 + a * p.ofLp 1] ) '' A ) from ?_ ];
  · rw [ Set.image_add_right ];
    rw [ MeasureTheory.measure_preimage_add_right ];
  · ext; simp [Set.mem_image];
    constructor <;> rintro ⟨ x, hx, hx' ⟩ <;> use x, hx <;> simp_all +decide;
    · ext i; fin_cases i <;> norm_num [ ← hx' ] ;
    · convert congr_arg ( fun y => y + !₂[v1, v2] ) hx' using 1 <;> ext i <;> fin_cases i <;> norm_num
/-
**Pigeonhole + rotation.**  Some `90°·k` rotation of `A` has infinite measure inside the upper
sector.
-/
lemma sector_reduction (A : Set Pt) (hA_inf : volume A = ⊤) :
    ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧ volume (rigid a b 0 0 '' A ∩ sectorUp) = ⊤ := by
  by_contra h_contra;
  -- Define the four closed quadrant sectors of the plane.
  set sectorUp : Set Pt := {p : Pt | |p 0| ≤ p 1}
  set sectorDown : Set Pt := {p : Pt | |p 0| ≤ -p 1}
  set sectorRight : Set Pt := {p : Pt | |p 1| ≤ p 0}
  set sectorLeft : Set Pt := {p : Pt | |p 1| ≤ -p 0};
  -- By countable subadditivity, we have $volume A \leq volume (A \cap sectorUp) + volume (A \cap sectorDown) + volume (A \cap sectorRight) + volume (A \cap sectorLeft)$.
  have h_subadd : volume A ≤ volume (A ∩ sectorUp) + volume (A ∩ sectorDown) + volume (A ∩ sectorRight) + volume (A ∩ sectorLeft) := by
    have h_subadd : volume A ≤ volume (A ∩ sectorUp ∪ A ∩ sectorDown ∪ A ∩ sectorRight ∪ A ∩ sectorLeft) := by
      refine' MeasureTheory.measure_mono _;
      grind;
    exact h_subadd.trans ( le_trans ( MeasureTheory.measure_union_le _ _ ) ( add_le_add ( le_trans ( MeasureTheory.measure_union_le _ _ ) ( add_le_add ( MeasureTheory.measure_union_le _ _ ) le_rfl ) ) le_rfl ) );
  -- Since $volume A = ⊤$, at least one of the four summands must be $⊤$.
  obtain ⟨Sec, hSec⟩ : ∃ Sec ∈ [sectorUp, sectorDown, sectorRight, sectorLeft], volume (A ∩ Sec) = ⊤ := by
    contrapose! h_subadd; simp_all +decide ;
    exact ⟨ ⟨ ⟨ lt_top_iff_ne_top.mpr h_subadd.1, lt_top_iff_ne_top.mpr h_subadd.2.1 ⟩, lt_top_iff_ne_top.mpr h_subadd.2.2.1 ⟩, lt_top_iff_ne_top.mpr h_subadd.2.2.2 ⟩;
  -- Each sector is carried INTO `Up` by a `90°·k` rotation `rigid a b 0 0`.
  obtain ⟨a, b, hab, hSecUp⟩ : ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧ rigid a b 0 0 '' Sec ⊆ sectorUp := by
    simp +zetaDelta at *;
    rcases hSec.1 with ( rfl | rfl | rfl | rfl ) <;> norm_num [ rigid ];
    · exact ⟨ 1, 0, by norm_num, fun p hp => by simpa using hp ⟩;
    · use -1, 0 ; norm_num;
    · use 0, 1 ; norm_num;
    · use 0, -1 ; norm_num;
  -- Therefore, $volume (rigid a b 0 0 '' A ∩ sectorUp) ≥ volume (rigid a b 0 0 '' (A ∩ Sec)) = volume (A ∩ Sec) = ⊤$.
  have h_volume_ge : volume (rigid a b 0 0 '' A ∩ sectorUp) ≥ volume (rigid a b 0 0 '' (A ∩ Sec)) := by
    refine' MeasureTheory.measure_mono _;
    exact Set.image_subset_iff.mpr fun x hx => ⟨ Set.mem_image_of_mem _ hx.1, hSecUp <| Set.mem_image_of_mem _ hx.2 ⟩;
  exact h_contra ⟨ a, b, hab, le_antisymm ( le_top ) ( h_volume_ge.trans' ( by rw [ volume_rigid_image hab ] ; aesop ) ) ⟩
/-- The upper sector is measurable. -/
lemma measurableSet_sectorUp : MeasurableSet sectorUp := by
  apply measurableSet_le
  · exact (Measurable.abs (by fun_prop))
  · fun_prop
/-- The map `(x,y) ↦ !₂[x,y]` from `ℝ × ℝ` to the Euclidean plane preserves Lebesgue measure. -/
lemma measurePreserving_pair :
    MeasurePreserving (fun p : ℝ × ℝ => (!₂[p.1, p.2] : Pt)) volume volume := by
  have h1 : MeasurePreserving (⇑(MeasurableEquiv.finTwoArrow (α := ℝ)).symm) volume volume :=
    (MeasureTheory.volume_preserving_finTwoArrow ℝ).symm
  have h2 : MeasurePreserving (WithLp.toLp 2 : (Fin 2 → ℝ) → Pt) volume volume :=
    PiLp.volume_preserving_toLp (Fin 2)
  have := h2.comp h1
  convert this using 2 with p
/-
**Fubini.**  A measurable set with infinite measure inside the upper sector has, at some
positive height `t₀`, a horizontal slice of positive one-dimensional measure.
-/
lemma exists_pos_slice (A' : Set Pt) (hA' : MeasurableSet A')
    (hsec : volume (A' ∩ sectorUp) = ⊤) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ 0 < (volume : Measure ℝ) {x : ℝ | (!₂[x, t₀] : Pt) ∈ A'} := by
  -- By Fubini's theorem, we can consider the integral of the measure of the slices over t.
  have h_fubini : ∫⁻ t in Set.Ioi 0, volume {x : ℝ | !₂[x, t] ∈ A' ∧ |x| ≤ t} = ⊤ := by
    have h_fubini : volume (Set.preimage (fun p : ℝ × ℝ => !₂[p.1, p.2]) (A' ∩ sectorUp)) = ∫⁻ t in Set.Ioi 0, volume {x : ℝ | !₂[x, t] ∈ A' ∧ |x| ≤ t} := by
      have h_fubini : volume (Set.preimage (fun p : ℝ × ℝ => !₂[p.1, p.2]) (A' ∩ sectorUp)) = ∫⁻ t, volume {x : ℝ | !₂[x, t] ∈ A' ∧ |x| ≤ t} := by
        convert MeasureTheory.Measure.prod_apply_symm _ using 1;
        · infer_instance;
        · infer_instance;
        · convert hA'.inter measurableSet_sectorUp |> MeasurableSet.preimage <| continuous_rigid 1 0 0 0 |> Continuous.measurable using 1;
          convert Iff.rfl;
          unfold rigid; norm_num [ Set.preimage ] ;
          constructor <;> intro h;
          · convert h.comp ( show Measurable fun x : ℝ × ℝ => ( x.1 • EuclideanSpace.single 0 1 + x.2 • EuclideanSpace.single 1 1 ) from ?_ ) using 1;
            · ext; simp [Function.comp];
            · fun_prop;
          · convert h.comp ( show Measurable fun x : EuclideanSpace ℝ ( Fin 2 ) => ( x 0, x 1 ) from ?_ ) using 1;
            fun_prop;
      rw [ h_fubini, ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
      congr with t ; split_ifs <;> simp_all +decide [ abs_le ];
      exact MeasureTheory.measure_mono_null ( fun x hx => by cases hx; exact Set.mem_singleton_iff.mpr <| by linarith ) ( MeasureTheory.measure_singleton t );
    convert hsec using 1;
    rw [ ← h_fubini, ← MeasureTheory.MeasurePreserving.measure_preimage ( measurePreserving_pair ) ];
    exact MeasurableSet.nullMeasurableSet ( hA'.inter measurableSet_sectorUp );
  contrapose! h_fubini;
  refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.setLIntegral_mono' measurableSet_Ioi fun t ht => _ ) _ );
  use fun t => 0;
  · exact le_trans ( MeasureTheory.measure_mono ( fun x hx => hx.1 ) ) ( h_fubini t ht );
  · norm_num
/-
The part of the upper sector below a horizontal line is a bounded triangle, so removing it from
a set of infinite measure leaves infinite measure above any height `H`.
-/
lemma volume_sector_above (A' : Set Pt) (hsec : volume (A' ∩ sectorUp) = ⊤) (H : ℝ) :
    volume (A' ∩ sectorUp ∩ {p : Pt | H < p 1}) = ⊤ := by
  -- By subadditivity, we have `volume (A' ∩ sectorUp) ≤ volume (A' ∩ sectorUp ∩ {p | p 1 ≤ H}) + volume (A' ∩ sectorUp ∩ {p | H < p 1})`.
  have h_subadd : volume (A' ∩ sectorUp) ≤ volume (A' ∩ sectorUp ∩ {p | p.ofLp 1 ≤ H}) + volume (A' ∩ sectorUp ∩ {p | H < p.ofLp 1}) := by
    refine' le_trans _ ( MeasureTheory.measure_union_le _ _ );
    exact MeasureTheory.measure_mono fun x hx => by by_cases h : x.ofLp 1 ≤ H <;> aesop;
  contrapose! h_subadd;
  refine' lt_of_le_of_lt ( add_le_add ( MeasureTheory.measure_mono _ ) le_rfl ) _;
  exact { p : Pt | |p 0| ≤ p 1 ∧ p 1 ≤ H };
  · exact fun x hx => ⟨ hx.1.2, hx.2 ⟩;
  · -- The set {p : Pt | |p 0| ≤ p 1 ∧ p 1 ≤ H} is bounded.
    have h_bounded : Bornology.IsBounded {p : Pt | |p 0| ≤ p 1 ∧ p 1 ≤ H} := by
      refine' isBounded_iff_forall_norm_le.mpr ⟨ H ^ 2 + 1, fun p hp => _ ⟩;
      norm_num [ EuclideanSpace.norm_eq ] at *;
      rw [ Real.sqrt_le_left ] <;> nlinarith [ abs_le.mp hp.1, sq_nonneg ( p.ofLp 0 - p.ofLp 1 ), sq_nonneg ( p.ofLp 0 + p.ofLp 1 ) ];
    exact lt_of_lt_of_le ( ENNReal.add_lt_top.mpr ⟨ h_bounded.measure_lt_top, lt_top_iff_ne_top.mpr h_subadd ⟩ ) ( by aesop )
/-
Being a Lebesgue density point is preserved by orientation-preserving rigid motions.
-/
lemma isDensityPt_rigid_image {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (A' : Set Pt) (C : Pt)
    (h : IsDensityPt A' C) :
    IsDensityPt (rigid a b v1 v2 '' A') (rigid a b v1 v2 C) := by
  convert h.congr' _;
  filter_upwards [ self_mem_nhdsWithin ] with r hr;
  have h_image : rigid a b v1 v2 '' (A' ∩ Metric.closedBall C r) = (rigid a b v1 v2 '' A') ∩ Metric.closedBall (rigid a b v1 v2 C) r := by
    ext x;
    constructor;
    · rintro ⟨ y, ⟨ hyA', hyC ⟩, rfl ⟩;
      exact ⟨ ⟨ y, hyA', rfl ⟩, by simpa [ dist_rigid hab ] using hyC ⟩;
    · rintro ⟨ ⟨ y, hy, rfl ⟩, hy' ⟩;
      exact ⟨ y, ⟨ hy, by simpa [ dist_rigid hab ] using hy' ⟩, rfl ⟩;
  rw [ ← h_image, volume_rigid_image hab ];
  norm_num [ EuclideanSpace.volume_closedBall ]
/-
**Density.**  There is a Lebesgue density point of `A'` of arbitrarily large height.
-/
lemma exists_densityPt_high (A' : Set Pt) (hA' : MeasurableSet A')
    (hsec : volume (A' ∩ sectorUp) = ⊤) (H : ℝ) :
    ∃ C : Pt, C ∈ A' ∧ IsDensityPt A' C ∧ H < C 1 := by
  obtain ⟨C, hC⟩ : ∃ C ∈ A' ∩ {p : Pt | H < p 1}, IsDensityPt A' C := by
    have := @Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet;
    specialize this volume hA';
    -- By `volume_sector_above`, `volume (A' ∩ sectorUp ∩ {p | H < p 1}) = ⊤ ≠ 0`.
    have h_volume_pos : volume (A' ∩ {p : Pt | H < p 1} ∩ sectorUp) ≠ 0 := by
      have h_volume_pos : volume (A' ∩ sectorUp ∩ {p : Pt | H < p 1}) = ⊤ := by
        convert volume_sector_above A' hsec H using 1;
      simp_all +decide [ Set.inter_comm, Set.inter_left_comm, Set.inter_assoc ];
    contrapose! h_volume_pos;
    refine' MeasureTheory.measure_mono_null _ this;
    intro x hx; specialize h_volume_pos x; simp_all +decide [ IsDensityPt ] ;
  exact ⟨ C, hC.1.1, hC.2, hC.1.2 ⟩
/-
**Fubini + Steinhaus + density.**  Given a measurable set with infinite measure inside the
upper sector, a translation of it admits a `Config`.
-/
lemma config_from_sector (A' : Set Pt) (hA' : MeasurableSet A')
    (hsec : volume (A' ∩ sectorUp) = ⊤) :
    ∃ v1 v2 c xC yC : ℝ, Config (rigid 1 0 v1 v2 '' A') c xC yC := by
  obtain ⟨t₀, ht₀_pos, ht₀_slice⟩ := exists_pos_slice A' hA' hsec;
  -- By Steinhaus, `I - I ∈ 𝓝 0`, so there is `θ > 0` with `Metric.ball (0:ℝ) θ ⊆ I - I`.
  obtain ⟨θ, hθ_pos, hθ_subset⟩ : ∃ θ > 0, Metric.ball 0 θ ⊆ {x - y | (x : ℝ) (hx : x ∈ {x : ℝ | (!₂[x, t₀] : Pt) ∈ A'}) (y : ℝ) (hy : y ∈ {x : ℝ | (!₂[x, t₀] : Pt) ∈ A'})} := by
    have h_steinhaus : ∀ {S : Set ℝ}, MeasurableSet S → 0 < volume S → {x - y | (x : ℝ) (hx : x ∈ S) (y : ℝ) (hy : y ∈ S)} ∈ 𝓝 0 := by
      intro S hS hS_pos;
      convert MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume S hS hS_pos using 1;
      exact Set.ext fun x => ⟨ fun ⟨ a, ha, b, hb, hx ⟩ => ⟨ a, ha, b, hb, hx ⟩, fun ⟨ a, ha, b, hb, hx ⟩ => ⟨ a, ha, b, hb, hx ⟩ ⟩;
    have := h_steinhaus ( show MeasurableSet { x : ℝ | !₂[x, t₀] ∈ A' } from ?_ ) ht₀_slice; rw [ Metric.mem_nhds_iff ] at this; aesop;
    exact hA'.preimage ( by exact Continuous.measurable ( by exact by rw [ show ( fun x : ℝ => !₂[x, t₀] : ℝ → Pt ) = fun x => x • ( EuclideanSpace.single 0 1 ) + t₀ • ( EuclideanSpace.single 1 1 ) by ext x i; fin_cases i <;> simp +decide ] ; exact Continuous.add ( continuous_id.smul continuous_const ) ( continuous_const.smul continuous_const ) ) );
  obtain ⟨C, hC_mem, hC_density, hC_height⟩ : ∃ C : Pt, C ∈ A' ∧ IsDensityPt A' C ∧ t₀ + 2 / θ < C 1 := exists_densityPt_high A' hA' hsec (t₀ + 2 / θ);
  -- Set `yC := C 1 - t₀`; then `yC > 2/θ > 0`. Set `c := 2 / yC`; then `0 < c < θ` (since `yC > 2/θ`).
  set yC := C 1 - t₀
  have hyC_pos : 0 < yC := by
    exact sub_pos_of_lt ( lt_of_le_of_lt ( le_add_of_nonneg_right <| by positivity ) hC_height )
  set c := 2 / yC
  have hc_pos : 0 < c := by
    exact div_pos zero_lt_two hyC_pos
  have hc_lt_θ : c < θ := by
    rw [ div_lt_iff₀ ] <;> nlinarith [ mul_div_cancel₀ 2 hθ_pos.ne' ];
  -- Hence `c ∈ Metric.ball 0 θ ⊆ I - I` (because `|c| = c < θ`), so `∃ x₁ ∈ I, ∃ x₂ ∈ I, x₁ - x₂ = c`.
  obtain ⟨x₁, hx₁_mem, x₂, hx₂_mem, hx₁x₂⟩ : ∃ x₁ x₂ : ℝ, x₁ ∈ {x : ℝ | (!₂[x, t₀] : Pt) ∈ A'} ∧ x₂ ∈ {x : ℝ | (!₂[x, t₀] : Pt) ∈ A'} ∧ x₁ - x₂ = c := by
    exact hθ_subset ( mem_ball_zero_iff.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) |> fun ⟨ x₁, hx₁, x₂, hx₂, h ⟩ => ⟨ x₁, x₂, hx₁, hx₂, h ⟩;
  use -hx₁_mem, -t₀, c, C 0 - hx₁_mem, yC;
  constructor;
  any_goals assumption;
  exact div_mul_cancel₀ _ hyC_pos.ne';
  · use !₂[hx₁_mem, t₀];
    exact ⟨ hx₂_mem, by ext i; fin_cases i <;> norm_num [ rigid ] ⟩;
  · use !₂[x₁, t₀];
    exact ⟨ x₂, by ext i; fin_cases i <;> norm_num [ rigid ] ; linarith ⟩;
  · use C; simp [rigid];
    exact ⟨ hC_mem, by ring, by ring ⟩;
  · exact measurableSet_rigid_image ( by norm_num ) hA';
  · convert isDensityPt_rigid_image _ _ _ hC_density using 1;
    · ext i; fin_cases i <;> simp +decide [ rigid ] ;
      · ring;
      · ring;
    · norm_num
/-- **First half of the proof.** Locating the triangle.  After applying a suitable
orientation-preserving rigid motion `g` (rotation `(a,b)` plus translation `(v₁,v₂)`), the image
`g '' A` contains a configuration as in `Config`. -/
lemma exists_config (A : Set Pt) (hA : MeasurableSet A) (hA_inf : volume A = ⊤) :
    ∃ (a b v1 v2 c xC yC : ℝ), a ^ 2 + b ^ 2 = 1 ∧
      Config (rigid a b v1 v2 '' A) c xC yC := by
  obtain ⟨a, b, hab, hsec⟩ := sector_reduction A hA_inf
  have hA' : MeasurableSet (rigid a b 0 0 '' A) := measurableSet_rigid_image hab hA
  obtain ⟨v1, v2, c, xC, yC, hcfg⟩ := config_from_sector _ hA' hsec
  refine ⟨a, b, v1, v2, c, xC, yC, hab, ?_⟩
  rwa [image_rigid_one_zero_comp] at hcfg
/- ===================== Core ===================== -/
/-!
## The perturbation map
Fix the base `A = (0,0)`, `B = (c,0)` and a triangle apex `C = (xC, yC)` with `c·yC = 2`
(so `area △ABC = 1`).  Given a point `D = (xD, yD)` (thought of as close to `C`, below the
horizontal line through `C`), there is a unique point `E = f(D)` close to `C` such that `A B E D`
is a cyclic quadrilateral of area `1`.  Geometrically, `E` is the second intersection of:
* the line `l`:  `yD·x + (c - xD)·y = 2`  (area `ABED = 1`), and
* the circumcircle `k` of `A B D`:  `x² + y² - c·x + ((c·xD - xD² - yD²)/yD)·y = 0`.
Eliminating `x` via the line equation yields a quadratic `P·y² + Q·y + R = 0` for `yE`, and
`E = f(D)` corresponds to the `+` root.
-/
/-- Coefficient `P = |BD|²` of the quadratic for `yE`. -/
noncomputable def Pcoef (c xD yD : ℝ) : ℝ := (xD - c) ^ 2 + yD ^ 2
/-- Coefficient `Q` of the quadratic for `yE`. -/
noncomputable def Qcoef (c xD yD : ℝ) : ℝ :=
  -4 * (c - xD) + c * yD * (c - xD) + yD * (c * xD - xD ^ 2 - yD ^ 2)
/-- Coefficient `R` of the quadratic for `yE`. -/
noncomputable def Rcoef (c yD : ℝ) : ℝ := 4 - 2 * c * yD
/-- Discriminant of the quadratic for `yE`. -/
noncomputable def discr (c xD yD : ℝ) : ℝ :=
  Qcoef c xD yD ^ 2 - 4 * Pcoef c xD yD * Rcoef c yD
/-- The `y`-coordinate of `E = f(D)`. -/
noncomputable def yEval (c xD yD : ℝ) : ℝ :=
  (-(Qcoef c xD yD) + Real.sqrt (discr c xD yD)) / (2 * Pcoef c xD yD)
/-- The `x`-coordinate of `E = f(D)`. -/
noncomputable def xEval (c xD yD : ℝ) : ℝ :=
  (2 - (c - xD) * yEval c xD yD) / yD
/-- The perturbation map `D ↦ E`. -/
noncomputable def fmap (c : ℝ) (D : Pt) : Pt := !₂[xEval c (D 0) (D 1), yEval c (D 0) (D 1)]
/-
`yEval` is a root of the quadratic `P·y² + Q·y + R = 0` (when the discriminant is nonneg
and `P > 0`).
-/
lemma quad_root (c xD yD : ℝ) (hP : 0 < Pcoef c xD yD) (hdisc : 0 ≤ discr c xD yD) :
    Pcoef c xD yD * yEval c xD yD ^ 2 + Qcoef c xD yD * yEval c xD yD + Rcoef c yD = 0 := by
  unfold yEval;
  field_simp;
  linarith [ Real.mul_self_sqrt hdisc, show discr c xD yD = Qcoef c xD yD ^ 2 - 4 * Pcoef c xD yD * Rcoef c yD from rfl ]
/-
The line equation (`area ABED = 1`).
-/
lemma eqI (c xD yD : ℝ) (hyD : yD ≠ 0) :
    yD * xEval c xD yD + (c - xD) * yEval c xD yD = 2 := by
  grind +locals
/-
The circle equation (`E` lies on the circumcircle of `A B D`).
-/
lemma eqII (c xD yD : ℝ) (hyD : yD ≠ 0) (hP : 0 < Pcoef c xD yD) (hdisc : 0 ≤ discr c xD yD) :
    xEval c xD yD ^ 2 + yEval c xD yD ^ 2 - c * xEval c xD yD
      + (c * xD - xD ^ 2 - yD ^ 2) / yD * yEval c xD yD = 0 := by
  unfold xEval yEval;
  field_simp;
  unfold Pcoef Qcoef discr; ring_nf;
  rw [ Real.sq_sqrt ];
  · unfold Qcoef Pcoef Rcoef; ring;
  · unfold discr at hdisc; linarith;
/-
The fixed point: `f(C) = C` when `c·yC = 2`.
-/
lemma fmap_fixed (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    xEval c xC yC = xC ∧ yEval c xC yC = yC := by
  have h_yC : yEval c xC yC = yC := by
    unfold yEval;
    rw [ div_eq_iff ];
    · rw [ show discr c xC yC = ( Qcoef c xC yC ) ^ 2 by
            unfold discr Rcoef Pcoef Qcoef; ring_nf;
            grind ];
      rw [ Real.sqrt_sq_eq_abs, abs_of_nonpos ];
      · unfold Qcoef Pcoef; ring_nf;
        grind;
      · unfold Qcoef;
        nlinarith [ sq_nonneg ( xC - c ), sq_nonneg ( xC - yC ), sq_nonneg ( yC - c ) ];
    · exact mul_ne_zero two_ne_zero ( by unfold Pcoef; nlinarith );
  unfold xEval; simp +decide [ * ] ; ring_nf;
  grind
/-
The shoelace area of `A B E D` equals `1`.
-/
lemma quadArea_ABED (c xD yD : ℝ) (hyD : yD ≠ 0) :
    quadArea (!₂[(0 : ℝ), (0 : ℝ)] : Pt) (!₂[c, (0 : ℝ)] : Pt)
        (!₂[xEval c xD yD, yEval c xD yD] : Pt) (!₂[xD, yD] : Pt) = 1 := by
  unfold quadArea; norm_num; ring_nf;
  linarith [ eqI c xD yD hyD ]
/-
`A B E D` are concyclic (all four lie on the circumcircle of `A B D`).
-/
lemma concyclic_ABED (c xD yD : ℝ) (hyD : 0 < yD) (hc : 0 < c)
    (hP : 0 < Pcoef c xD yD) (hdisc : 0 ≤ discr c xD yD) :
    Concyclic4 (!₂[(0 : ℝ), (0 : ℝ)] : Pt) (!₂[c, (0 : ℝ)] : Pt)
        (!₂[xEval c xD yD, yEval c xD yD] : Pt) (!₂[xD, yD] : Pt) := by
  refine' ⟨ !₂[c / 2, ( xD ^ 2 + yD ^ 2 - c * xD ) / ( 2 * yD ) ], Real.sqrt ( ( c / 2 ) ^ 2 + ( ( xD ^ 2 + yD ^ 2 - c * xD ) / ( 2 * yD ) ) ^ 2 ), _, _, _, _, _ ⟩;
  · positivity;
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
    ring_nf;
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
    have := eqII c xD yD hyD.ne' hP hdisc;
    grind;
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
    grind +locals
/-
Evaluating the quadratic `P·y² + Q·y + R` at `y = yC` factors as `yC·(yC - yD)·(xD² + yD²)`
(using `c·yC = 2`).
-/
lemma Pq_at_yC (c xD yD yC : ℝ) (harea : c * yC = 2) :
    Pcoef c xD yD * yC ^ 2 + Qcoef c xD yD * yC + Rcoef c yD
      = yC * (yC - yD) * (xD ^ 2 + yD ^ 2) := by
  unfold Pcoef Qcoef Rcoef;
  grind
/-
In the lower half (`c·yD < 2`, i.e. `yD < yC`), with the discriminant positive and the
sign conditions that hold near `C`, the image height satisfies `yEval < yC`.
-/
lemma yEval_lt_yC (c xD yD yC : ℝ) (hyC : 0 < yC) (harea : c * yC = 2)
    (hyD : 0 < yD) (hlt : yD < yC) (hP : 0 < Pcoef c xD yD) (hdisc : 0 ≤ discr c xD yD)
    (hpos : 0 < 2 * Pcoef c xD yD * yC + Qcoef c xD yD) :
    yEval c xD yD < yC := by
  -- By `Real.sqrt_lt' hpos`, this is `discr < (2 * Pcoef c xD yD * yC + Qcoef c xD yD)^2`.
  have h_sqrt_lt : discr c xD yD < (2 * Pcoef c xD yD * yC + Qcoef c xD yD)^2 := by
    have h_discr_lt_K2 : discr c xD yD < (2 * Pcoef c xD yD * yC + Qcoef c xD yD) ^ 2 := by
      have h_K2_minus_discr : (2 * Pcoef c xD yD * yC + Qcoef c xD yD) ^ 2 - discr c xD yD = 4 * Pcoef c xD yD * yC * (yC - yD) * (xD ^ 2 + yD ^ 2) := by
        convert congr_arg ( fun x : ℝ => 4 * Pcoef c xD yD * x ) ( Pq_at_yC c xD yD yC harea ) using 1 ; ring_nf;
        · unfold discr Rcoef; ring;
        · ring
      exact lt_of_sub_pos ( h_K2_minus_discr.symm ▸ mul_pos ( mul_pos ( mul_pos ( mul_pos zero_lt_four hP ) hyC ) ( sub_pos.mpr hlt ) ) ( by positivity ) );
    exact h_discr_lt_K2;
  unfold yEval; rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg ( discr c xD yD ), Real.mul_self_sqrt hdisc ] ;
/-
Near `C`, `yEval > 0` (it follows from `Qcoef < 0`, which holds near `C`).
-/
lemma yEval_pos (c xD yD : ℝ) (hP : 0 < Pcoef c xD yD)
    (hQ : Qcoef c xD yD < 0) :
    0 < yEval c xD yD := by
  exact div_pos ( by linarith [ Real.sqrt_nonneg ( discr c xD yD ) ] ) ( by positivity )
/-
Convexity of `A B E D` from the height bounds (using the orientation identities
`orient D A B = c·yD`, `orient A B E = c·yEval`, `orient E D A = 2 - c·yEval`,
`orient B E D = 2 - c·yD`).
-/
lemma convex_ABED (c xD yD : ℝ) (hc : 0 < c) (hyD : 0 < yD) (hyD' : c * yD < 2)
    (hyE : 0 < yEval c xD yD) (hyE' : c * yEval c xD yD < 2) :
    ConvexQuadCCW (!₂[(0 : ℝ), (0 : ℝ)] : Pt) (!₂[c, (0 : ℝ)] : Pt)
        (!₂[xEval c xD yD, yEval c xD yD] : Pt) (!₂[xD, yD] : Pt) := by
  refine' ⟨ _, _, _, _ ⟩ <;> norm_num [ ConvexQuadCCW, orient ];
  · positivity;
  · unfold xEval yEval at *;
    rw [ div_sub', div_mul_cancel₀ ] <;> linarith;
  · nlinarith [ eqI c xD yD hyD.ne' ];
  · nlinarith
/-- Measurability of `{D ∈ ball C δ | g D ∈ S}` when `g` is continuous on the ball. -/
lemma measurableSet_ball_preimage {S : Set Pt} (C : Pt) (g : Pt → Pt) (δ : ℝ)
    (hcont : ContinuousOn g (Metric.ball C δ)) (hS : MeasurableSet S) :
    MeasurableSet {D : Pt | D ∈ Metric.ball C δ ∧ g D ∈ S} := by
  have hmg : Measurable (fun x : Metric.ball C δ => g x.1) :=
    (continuousOn_iff_continuous_restrict.mp hcont).measurable
  obtain ⟨t, ht⟩ := hmg hS
  refine (ht.1.inter (measurableSet_ball (x := C) (ε := δ))).congr ?_
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxt, hxb⟩
    refine ⟨hxb, ?_⟩
    have : (⟨x, hxb⟩ : Metric.ball C δ) ∈ Subtype.val ⁻¹' t := hxt
    rw [ht.2] at this; exact this
  · rintro ⟨hxb, hxS⟩
    refine ⟨?_, hxb⟩
    have : (⟨x, hxb⟩ : Metric.ball C δ) ∈ Subtype.val ⁻¹' t := by rw [ht.2]; exact hxS
    exact this
/-
**Abstract measure overlap.**  If `g` is, on a ball around `C`, an injective `C¹` map fixing
`C` with Jacobian determinant bounded below by `m > 0` and `M`-Lipschitz, and `S` has Lebesgue
density `1` at `C`, then arbitrarily close to `C` (and strictly below it) there is a point `D ∈ S`
with `g D ∈ S`.
-/
lemma overlap_of_diffeo
    (S : Set Pt) (C : Pt) (g : Pt → Pt) (g' : Pt → (Pt →L[ℝ] Pt))
    (m M r0 : ℝ) (hm : 0 < m) (hM : 0 < M) (hr0 : 0 < r0)
    (hSmeas : MeasurableSet S)
    (hderiv : ∀ x ∈ Metric.ball C r0, HasFDerivWithinAt g (g' x) (Metric.ball C r0) x)
    (hdet : ∀ x ∈ Metric.ball C r0, m ≤ |(g' x).det|)
    (hinj : Set.InjOn g (Metric.ball C r0))
    (hLip : ∀ x ∈ Metric.ball C r0, dist (g x) C ≤ M * dist x C)
    (hdens : IsDensityPt S C) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Pt, dist D C < ε ∧ D 1 < C 1 ∧ D ∈ S ∧ g D ∈ S := by
  contrapose! hdens; simp_all +decide [ dist_eq_norm ] ; (
  contrapose! hdens with hdens';
  -- Choose $\delta \in (0, \min(\epsilon, \min(r_0/M, r_0)))$ such that $\text{volume}(\text{closedBall } C \delta \setminus S) + \text{ENNReal.ofReal}(1/m) \cdot \text{volume}(\text{closedBall } C (M\delta) \setminus S) < \text{ENNReal.ofReal}(\pi \delta^2 / 16)$.
  obtain ⟨δ, hδ_pos, hδ_lt, hδ⟩ : ∃ δ > 0, δ < min ε (min (r0 / M) r0) ∧
    (MeasureTheory.volume (Metric.closedBall C δ \ S)) + (ENNReal.ofReal (1 / m)) * (MeasureTheory.volume (Metric.closedBall C (M * δ) \ S)) <
    ENNReal.ofReal (Real.pi * (δ / 4) ^ 2) := by
      -- By the properties of the density function, we know that
      have h_density : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S)) / ENNReal.ofReal (δ ^ 2)) (𝓝[>] 0) (𝓝 0) ∧ Filter.Tendsto (fun δ => (volume (Metric.closedBall C (M * δ) \ S)) / ENNReal.ofReal (δ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
        have h_density : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S)) / ENNReal.ofReal (δ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
          have h_volume_closedBall : ∀ δ > 0, volume (Metric.closedBall C δ) = ENNReal.ofReal (Real.pi * δ ^ 2) := by
            intro δ hδ_pos; erw [ MeasureTheory.Measure.addHaar_closedBall ] ; norm_num [ hδ_pos.le ] ; ring_nf;
            · rw [ mul_comm, ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_pow ( by positivity ) ];
            · positivity;
          have h_volume_closedBall : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S)) / volume (Metric.closedBall C δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            have := hdens';
            have h_volume_closedBall : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ ∩ S)) / volume (Metric.closedBall C δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
              convert this using 1;
              unfold IsDensityPt; simp +decide [ Set.inter_comm ] ;
            have h_volume_closedBall : ∀ δ > 0, volume (Metric.closedBall C δ \ S) = volume (Metric.closedBall C δ) - volume (Metric.closedBall C δ ∩ S) := by
              intro δ hδ_pos; rw [ ← MeasureTheory.measure_diff ] <;> norm_num [ hSmeas ] ;
              · exact MeasurableSet.nullMeasurableSet ( measurableSet_closedBall.inter hSmeas );
              · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( by aesop ) );
            rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_volume_closedBall x hx ] ) ];
            have h_volume_closedBall : Filter.Tendsto (fun δ => 1 - (volume (Metric.closedBall C δ ∩ S)) / volume (Metric.closedBall C δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
              convert ENNReal.Tendsto.sub tendsto_const_nhds ‹Tendsto ( fun δ => volume ( Metric.closedBall C δ ∩ S ) / volume ( Metric.closedBall C δ ) ) ( 𝓝[>] 0 ) ( 𝓝 1 ) › _ using 1 <;> norm_num;
            refine' h_volume_closedBall.congr' _;
            filter_upwards [ self_mem_nhdsWithin ] with δ hδ;
            rw [ ENNReal.sub_div ] <;> norm_num [ hδ.out.ne' ];
            · rw [ ENNReal.div_self ] <;> norm_num [ hδ.out.ne' ];
              · exact ⟨ hδ, Real.pi_pos ⟩;
              · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
            · exact fun _ _ => ⟨ hδ, Real.pi_pos ⟩;
          have h_volume_closedBall : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S)) / ENNReal.ofReal (Real.pi * δ ^ 2) * ENNReal.ofReal Real.pi) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            have h_volume_closedBall : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S)) / ENNReal.ofReal (Real.pi * δ ^ 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
              exact h_volume_closedBall.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by aesop );
            convert ENNReal.Tendsto.mul_const h_volume_closedBall _ using 1 ; norm_num [ Real.pi_pos.le ];
            norm_num [ ENNReal.ofReal_ne_top ];
          refine' h_volume_closedBall.congr' _;
          filter_upwards [ self_mem_nhdsWithin ] with δ hδ ; simp +decide [ div_eq_mul_inv, mul_comm, Real.pi_pos.le ] ; ring_nf;
          simp +decide [ mul_assoc, mul_comm, ENNReal.mul_inv ];
          rw [ ← mul_assoc, ENNReal.mul_inv_cancel ( by positivity ) ( by norm_num ), one_mul ];
        have h_density_M : Filter.Tendsto (fun δ => (volume (Metric.closedBall C (M * δ) \ S)) / ENNReal.ofReal ((M * δ) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
          exact h_density.comp <| Filter.Tendsto.inf ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) <| Filter.tendsto_principal_principal.mpr <| by aesop;
        refine' ⟨ h_density, _ ⟩;
        have h_density_M : Filter.Tendsto (fun δ => (volume (Metric.closedBall C (M * δ) \ S)) / ENNReal.ofReal ((M * δ) ^ 2) * ENNReal.ofReal (M ^ 2)) (𝓝[>] 0) (𝓝 0) := by
          convert ENNReal.Tendsto.mul_const h_density_M _ using 1 ; norm_num [ hM.ne' ];
          norm_num [ ENNReal.ofReal_ne_top ];
        refine' h_density_M.congr' _;
        filter_upwards [ self_mem_nhdsWithin ] with δ hδ ; rw [ ENNReal.div_mul ] ; ring_nf ;
        · rw [ ← ENNReal.ofReal_div_of_pos ( by positivity ), mul_div_cancel_left₀ _ ( by positivity ) ];
        · exact Or.inr ( ne_of_gt ( ENNReal.ofReal_pos.mpr ( sq_pos_of_pos hM ) ) );
        · exact Or.inl ENNReal.ofReal_ne_top;
      -- By the properties of the density function, we know that the limit of the ratio is 0.
      have h_limit : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S) + ENNReal.ofReal (1 / m) * volume (Metric.closedBall C (M * δ) \ S)) / ENNReal.ofReal (δ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
        simp_all +decide [ ENNReal.add_div ];
        convert h_density.1.add ( ENNReal.Tendsto.const_mul h_density.2 _ ) using 2 <;> norm_num [ mul_div_assoc ];
        congr! 1;
        exact ENNReal.inv_ne_top.mpr ( by aesop );
      have := h_limit.eventually ( gt_mem_nhds <| show 0 < ENNReal.ofReal ( Real.pi / 16 ) from by positivity ) ; have := this.and ( Ioo_mem_nhdsGT <| show 0 < Min.min ε ( Min.min ( r0 / M ) r0 ) from lt_min hε <| lt_min ( div_pos hr0 hM ) hr0 ) ; obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this.exists ; use δ ; simp_all +decide ;
      rw [ ENNReal.div_lt_iff ] at hδ₁ <;> norm_num at *;
      · exact hδ₁.trans_le ( by rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; ring_nf; norm_num );
      · exact Or.inl hδ₂.1.ne';
  -- Let $L := \text{Metric.ball } C \delta \cap \{D | D.ofLp 1 < C.ofLp 1\}$.
  set L := Metric.ball C δ ∩ {D : Pt | D 1 < C 1} with hL_def
  have hL_meas : MeasurableSet L := by
    refine' MeasurableSet.inter ( measurableSet_ball ) _;
    refine' measurableSet_lt _ _ <;> norm_num [ Pi.single_apply ];
    fun_prop (disch := norm_num)
  have hL_pos : MeasureTheory.volume L ≥ ENNReal.ofReal (Real.pi * (δ / 4) ^ 2) := by
    -- Contain a smaller ball in $L$.
    have h_ball_subset_L : Metric.ball (C - (δ / 2 : ℝ) • EuclideanSpace.single 1 1) (δ / 4) ⊆ L := by
      intro x hx; simp_all +decide [ EuclideanSpace.norm_eq ] ; (
      constructor <;> norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
      · rw [ Real.sqrt_lt' ] at * <;> nlinarith [ sq_nonneg ( x.ofLp 1 - C.ofLp 1 + δ / 2 ) ] ;
      · rw [ Real.sqrt_lt' ] at hx <;> nlinarith [ sq_nonneg ( x.ofLp 0 - C.ofLp 0 ), sq_nonneg ( x.ofLp 1 + δ / 2 - C.ofLp 1 ) ] ;)
    generalize_proofs at *; (
    refine' le_trans _ ( MeasureTheory.measure_mono h_ball_subset_L ) ; ring_nf ; norm_num [ Real.pi_pos.le ] ;
    rw [ ← ENNReal.ofReal_pow ( by positivity ) ] ; ring_nf ;
    rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; ring_nf; norm_num;)
  generalize_proofs at *; (
  -- Let $T := \{D \in L | g D \notin S\}$.
  set T := {D ∈ L | g D ∉ S} with hT_def
  have hT_meas : MeasurableSet T := by
    have hT_meas : MeasurableSet {D ∈ Metric.ball C δ | g D ∉ S} := by
      apply measurableSet_ball_preimage C g δ (by
      exact fun x hx => ( hderiv x ( by exact lt_of_lt_of_le ( by simpa using hx ) ( by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] ) ) |> HasFDerivWithinAt.continuousWithinAt ) |> ContinuousWithinAt.mono <| Metric.ball_subset_ball <| by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] ;) (hSmeas.compl)
    generalize_proofs at *; (
    convert hT_meas.inter hL_meas using 1 ; ext ; aesop ( simp_config := { singlePass := true } ) ;)
  have hT_bound : MeasureTheory.volume T ≤ (ENNReal.ofReal (1 / m)) * (MeasureTheory.volume (Metric.closedBall C (M * δ) \ S)) := by
    have hT_bound : ENNReal.ofReal m * MeasureTheory.volume T ≤ MeasureTheory.volume (g '' T) := by
      have hT_bound : ∫⁻ x in T, ENNReal.ofReal (|(g' x).det|) ∂MeasureTheory.volume ≤ MeasureTheory.volume (g '' T) := by
        apply_rules [ MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image ];
        · intro x hx; exact HasFDerivWithinAt.mono ( hderiv x <| by
            exact lt_of_lt_of_le ( mem_ball_iff_norm.mp hx.1.1 ) ( by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] ) ) <| by
            exact fun x hx => Metric.ball_subset_ball ( by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] ) hx.1.1;
        · exact hinj.mono ( fun x hx => by exact Metric.mem_ball.mpr ( lt_of_lt_of_le ( Metric.mem_ball.mp hx.1.1 ) ( by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] ) ) )
      generalize_proofs at *; (
      refine' le_trans _ hT_bound
      generalize_proofs at *; (
      refine' le_trans _ ( MeasureTheory.setLIntegral_mono' hT_meas fun x hx => ENNReal.ofReal_le_ofReal <| hdet x _ ) <;> norm_num [ hδ_pos, hδ_lt ];
      exact lt_of_lt_of_le ( mem_ball_iff_norm.mp hx.1.1 ) ( by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] )))
    generalize_proofs at *; (
    have hT_subset : g '' T ⊆ Metric.closedBall C (M * δ) \ S := by
      simp_all +decide [ Set.subset_def ];
      rintro x y hy₁ hy₂ hy₃ rfl; exact ⟨ by simpa [ dist_eq_norm ] using le_trans ( hLip y <| by simpa [ dist_eq_norm ] using hy₁.trans_le <| by nlinarith [ mul_div_cancel₀ r0 hM.ne' ] ) <| mul_le_mul_of_nonneg_left hy₁.le hM.le, hy₃ ⟩ ;
    generalize_proofs at *; (
    refine' le_trans _ ( mul_le_mul_right ( MeasureTheory.measure_mono hT_subset ) _ );
    convert mul_le_mul_right hT_bound ( ENNReal.ofReal ( 1 / m ) ) using 1 ; ring_nf ;
    rw [ ← ENNReal.ofReal_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), ENNReal.ofReal_one, one_mul ]))
  generalize_proofs at *; (
  -- Since $L \subseteq (L \setminus S) \cup T \cup \{D \in \text{ball } C \delta | D.ofLp 1 < C.ofLp 1 \land D \in S \land g D \in S\}$, we have $\text{volume } L \leq \text{volume } (L \setminus S) + \text{volume } T + \text{volume } \{D \in \text{ball } C \delta | D.ofLp 1 < C.ofLp 1 \land D \in S \land g D \in S\}$.
  have hL_subset : MeasureTheory.volume L ≤ MeasureTheory.volume (Metric.closedBall C δ \ S) + MeasureTheory.volume T + MeasureTheory.volume {D ∈ Metric.ball C δ | D 1 < C 1 ∧ D ∈ S ∧ g D ∈ S} := by
    have hL_subset : L ⊆ (Metric.closedBall C δ \ S) ∪ T ∪ {D ∈ Metric.ball C δ | D 1 < C 1 ∧ D ∈ S ∧ g D ∈ S} := by
      intro D hD; by_cases hD' : D ∈ S <;> by_cases hD'' : g D ∈ S <;> simp_all +decide ;
      linarith [ hD.1 ]
    generalize_proofs at *; (
    refine' le_trans ( MeasureTheory.measure_mono hL_subset ) _;
    exact le_trans ( MeasureTheory.measure_union_le _ _ ) ( add_le_add ( MeasureTheory.measure_union_le _ _ ) le_rfl ))
  generalize_proofs at *; (
  contrapose! hL_subset; simp_all +decide [ Set.setOf_and ] ; (
  refine' lt_of_le_of_lt _ ( lt_of_lt_of_le hδ hL_pos ) |> lt_of_lt_of_le <| le_rfl; simp_all +decide [ ← Set.inter_assoc ] ;
  rw [ show { a : Pt | dist a C < δ } ∩ { a : Pt | a.ofLp 1 < C.ofLp 1 } ∩ S ∩ { a : Pt | g a ∈ S } = ∅ from Set.eq_empty_of_forall_notMem fun x hx => hL_subset x ( by simpa using hx.1.1.1.trans_le hδ_lt.1.le ) hx.1.1.2 hx.1.2 hx.2 ] ; norm_num [ add_assoc ] ; gcongr;)))));
/-
`fmap c` is `C¹` near `C = (xC,yC)` (where `c·yC = 2`): the discriminant and `Pcoef` are
positive there, so the explicit formula is smooth.
-/
lemma fmap_contDiffAt (c xC yC : ℝ) (hyC : 0 < yC) (harea : c * yC = 2) :
    ContDiffAt ℝ 1 (fmap c) (!₂[xC, yC] : Pt) := by
  refine' ContDiffAt.comp _ _ _;
  · fun_prop (disch := norm_num);
  · -- By definition of $fmap$, we know that it is a composition of smooth functions.
    have h_smooth : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (xEval c p.1 p.2, yEval c p.1 p.2)) (xC, yC) := by
      apply_rules [ ContDiffAt.prodMk, ContDiffAt.div, ContDiffAt.sqrt ];
      any_goals positivity;
      · apply_rules [ ContDiffAt.sub, ContDiffAt.mul, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
        · apply_rules [ ContDiffAt.add, ContDiffAt.neg, ContDiffAt.sqrt ];
          any_goals apply_rules [ ContDiffAt.mul, ContDiffAt.sub, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
          · apply_rules [ ContDiffAt.add, ContDiffAt.neg, ContDiffAt.mul, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
          · apply_rules [ ContDiffAt.add, ContDiffAt.neg, ContDiffAt.mul, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
          · exact ContDiffAt.add ( ContDiffAt.pow ( contDiffAt_fst.sub contDiffAt_const ) 2 ) ( ContDiffAt.pow ( contDiffAt_snd ) 2 );
          · unfold discr;
            unfold Qcoef Pcoef Rcoef; norm_num [ show c = 2 / yC by rw [ eq_div_iff hyC.ne' ] ; linarith ] ; ring_nf; norm_num [ hyC.ne' ] ;
            field_simp;
            nlinarith [ sq_nonneg ( xC * yC - 2 ), sq_nonneg ( xC * yC + 2 ), pow_pos hyC 3, pow_pos hyC 4, pow_pos hyC 5, pow_pos hyC 6, pow_pos hyC 7, pow_pos hyC 8 ];
        · apply_rules [ ContDiffAt.inv, ContDiffAt.mul, contDiffAt_const ];
          · exact ContDiffAt.add ( ContDiffAt.pow ( contDiffAt_fst.sub contDiffAt_const ) 2 ) ( ContDiffAt.pow ( contDiffAt_snd ) 2 );
          · exact mul_ne_zero two_ne_zero ( by unfold Pcoef; nlinarith );
      · exact contDiffAt_snd;
      · apply_rules [ ContDiffAt.add, ContDiffAt.neg, ContDiffAt.sqrt ];
        any_goals apply_rules [ ContDiffAt.pow, ContDiffAt.mul, ContDiffAt.sub, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
        · apply_rules [ ContDiffAt.sub, ContDiffAt.add, ContDiffAt.mul, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
        · exact ContDiffAt.add ( ContDiffAt.pow ( contDiffAt_fst.sub contDiffAt_const ) 2 ) ( ContDiffAt.pow ( contDiffAt_snd ) 2 );
        · unfold discr;
          unfold Qcoef Pcoef Rcoef; norm_num [ show c = 2 / yC by rw [ eq_div_iff hyC.ne' ] ; linarith ] ; ring_nf; norm_num [ hyC.ne' ] ;
          field_simp;
          nlinarith [ sq_nonneg ( xC * yC - 2 ), sq_nonneg ( xC * yC + 2 ), pow_pos hyC 3, pow_pos hyC 4, pow_pos hyC 5, pow_pos hyC 6, pow_pos hyC 7, pow_pos hyC 8 ];
      · exact ContDiffAt.mul contDiffAt_const ( ContDiffAt.add ( ContDiffAt.pow ( contDiffAt_fst.sub contDiffAt_const ) 2 ) ( ContDiffAt.pow ( contDiffAt_snd ) 2 ) );
      · exact mul_ne_zero two_ne_zero ( by unfold Pcoef; nlinarith );
    have h_smooth : ContDiffAt ℝ 1 (fun D : EuclideanSpace ℝ (Fin 2) => (xEval c (D 0) (D 1), yEval c (D 0) (D 1))) !₂[xC, yC] := by
      have h_smooth : ContDiffAt ℝ 1 (fun D : EuclideanSpace ℝ (Fin 2) => (D 0, D 1)) !₂[xC, yC] := by
        fun_prop;
      exact ContDiffAt.comp _ ( by assumption ) h_smooth;
    exact contDiffAt_pi.mpr fun i => by fin_cases i <;> [ exact h_smooth.fst; exact h_smooth.snd ] ;
/-- The partial derivative `∂(yEval)/∂yD` at `C = (xC,yC)` equals `(xC²+yC²)/((xC-c)²+yC²) > 0`.
This is the single non-trivial entry of the Jacobian (the first column is `[1,0]` by
`fmap_fixed`, so the determinant equals this value). -/
lemma yEval_hasDerivAt_y (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    HasDerivAt (fun y => yEval c xC y)
      ((xC ^ 2 + yC ^ 2) / ((xC - c) ^ 2 + yC ^ 2)) yC := by
  have hPpos : 0 < Pcoef c xC yC := by unfold Pcoef; positivity
  have hQval : Qcoef c xC yC = -yC * ((xC - c) ^ 2 + yC ^ 2) := by
    unfold Qcoef; linear_combination (2*c - 2*xC) * harea
  have hQneg : Qcoef c xC yC < 0 := by
    rw [hQval]
    have h : (0:ℝ) < (xC - c) ^ 2 + yC ^ 2 := by positivity
    nlinarith [h, hyC]
  have hRz : Rcoef c yC = 0 := by unfold Rcoef; linarith [harea]
  have hdC : discr c xC yC = (Qcoef c xC yC) ^ 2 := by unfold discr; rw [hRz]; ring
  have hdpos : 0 < discr c xC yC := by
    rw [hdC]; nlinarith [mul_pos (neg_pos.mpr hQneg) (neg_pos.mpr hQneg)]
  have hdiff : DifferentiableAt ℝ (fun y => yEval c xC y) yC := by
    unfold yEval discr Qcoef Pcoef Rcoef
    fun_prop (disch := first | positivity | nlinarith [hdpos, hPpos] | assumption)
  set v := deriv (fun y => yEval c xC y) yC with hvdef
  have hf : HasDerivAt (fun y => yEval c xC y) v yC := hdiff.hasDerivAt
  have hyEvalC : yEval c xC yC = yC := (fmap_fixed c xC yC hc hyC harea).2
  have hP' : HasDerivAt (fun y => Pcoef c xC y) (2*yC) yC := by
    unfold Pcoef
    have h := (hasDerivAt_const (𝕜:=ℝ) yC ((xC-c)^2)).add (hasDerivAt_pow 2 yC)
    convert h using 1; push_cast; ring
  have hQ' : HasDerivAt (fun y => Qcoef c xC y) (c*(c-xC)+(c*xC-xC^2)-3*yC^2) yC := by
    unfold Qcoef
    have hid : HasDerivAt (fun y : ℝ => y) 1 yC := hasDerivAt_id' yC
    have h1 := (hasDerivAt_const (𝕜:=ℝ) yC (-4*(c-xC))).add ((hid.const_mul c).mul_const (c-xC))
    have hsub := (hasDerivAt_const (𝕜:=ℝ) yC (c*xC-xC^2)).sub (hasDerivAt_pow 2 yC)
    have h := h1.add (hid.mul hsub)
    convert h using 1; simp only [Pi.sub_apply]; push_cast; ring
  have hR' : HasDerivAt (fun y => Rcoef c y) (-2*c) yC := by
    unfold Rcoef
    have hid : HasDerivAt (fun y : ℝ => y) 1 yC := hasDerivAt_id' yC
    have h := (hasDerivAt_const (𝕜:=ℝ) yC (4:ℝ)).sub ((hid.const_mul 2).const_mul c)
    convert h using 1 <;> (try ext y) <;> (try simp only [Pi.sub_apply]) <;> ring
  have hPnhds : ∀ᶠ y in 𝓝 yC, 0 < Pcoef c xC y :=
    (continuousAt_const).eventually_lt hP'.continuousAt hPpos
  have hdnhds : ∀ᶠ y in 𝓝 yC, 0 ≤ discr c xC y := by
    have hcont : ContinuousAt (fun y => discr c xC y) yC := by
      unfold discr Qcoef Pcoef Rcoef; fun_prop
    exact ((continuousAt_const).eventually_lt hcont hdpos).mono (fun y h => le_of_lt h)
  have hH0 : (fun y => Pcoef c xC y * yEval c xC y^2 + Qcoef c xC y * yEval c xC y + Rcoef c y)
      =ᶠ[𝓝 yC] (fun _ => 0) := by
    filter_upwards [hPnhds, hdnhds] with y hPy hdy using quad_root c xC y hPy hdy
  have hHd0 : HasDerivAt (fun y => Pcoef c xC y * yEval c xC y^2 + Qcoef c xC y * yEval c xC y
      + Rcoef c y) 0 yC :=
    (hasDerivAt_const yC (0:ℝ)).congr_of_eventuallyEq hH0
  have hsq : HasDerivAt (fun y => yEval c xC y ^ 2) (2 * yEval c xC yC * v) yC := by
    have := hf.pow 2; simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using this
  have hHd : HasDerivAt (fun y => Pcoef c xC y * yEval c xC y^2 + Qcoef c xC y * yEval c xC y
      + Rcoef c y)
      ((2*yC) * (yEval c xC yC)^2 + Pcoef c xC yC * (2 * yEval c xC yC * v)
        + ((c*(c-xC)+(c*xC-xC^2)-3*yC^2) * yEval c xC yC + Qcoef c xC yC * v) + (-2*c)) yC :=
    ((hP'.mul hsq).add (hQ'.mul hf)).add hR'
  have heq := hHd0.unique hHd
  rw [hyEvalC, hQval, show Pcoef c xC yC = (xC-c)^2+yC^2 from rfl] at heq
  have hv_eq : v = (xC ^ 2 + yC ^ 2) / ((xC - c) ^ 2 + yC ^ 2) := by
    rw [eq_div_iff (by positivity)]
    have hc2 : c ^ 2 * yC = 2 * c := by nlinarith [harea]
    have key : yC * (((xC - c) ^ 2 + yC ^ 2) * v) = yC * (xC ^ 2 + yC ^ 2) := by
      nlinarith [heq, hc2]
    have hcancel := mul_left_cancel₀ (ne_of_gt hyC) key
    linarith [hcancel, mul_comm ((xC - c) ^ 2 + yC ^ 2) v]
  rw [hv_eq] at hf
  exact hf
/-
The partial derivative `∂(yEval)/∂xD` at `C = (xC,yC)` equals `0` (when `c·yC = 2`).
This is the lower-left entry of the Jacobian. Proved by implicit differentiation of `quad_root`
with respect to `xD`, exactly as in `yEval_hasDerivAt_y`. The numerator
`∂P/∂xD·yC² + ∂Q/∂xD·yC = yC·(4 - 2·c·yC) = 0`.
-/
lemma yEval_hasDerivAt_x (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    HasDerivAt (fun x => yEval c x yC) 0 xC := by
  convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
  exact fun x => yC;
  · exact hasDerivAt_const _ _;
  · filter_upwards [ ( Metric.ball_mem_nhds xC zero_lt_one ) ] with x hx;
    convert fmap_fixed c x yC hc hyC ( by linarith ) |> And.right using 1
/-
The partial derivative `∂(xEval)/∂xD` at `C = (xC,yC)` equals `1` (when `c·yC = 2`).
Since `xEval c x yC = (2 - (c - x)·yEval c x yC)/yC`, and `∂yEval/∂xD = 0` (`yEval_hasDerivAt_x`)
with `yEval c xC yC = yC` (`fmap_fixed`), the derivative is `yC/yC = 1`.
-/
lemma xEval_hasDerivAt_x (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    HasDerivAt (fun x => xEval c x yC) 1 xC := by
  convert HasDerivAt.div_const ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( hasDerivAt_id xC ) |> HasDerivAt.mul <| HasDerivAt.congr_of_eventuallyEq ( yEval_hasDerivAt_x c xC yC hc hyC harea ) <| Filter.eventuallyEq_of_mem ( Metric.ball_mem_nhds _ hyC ) fun x hx => rfl ) ) yC using 1 ; ring_nf;
  rw [ fmap_fixed c xC yC hc hyC harea |>.2, mul_inv_cancel₀ hyC.ne' ]
/-- Translation: the derivative of `t ↦ f (a + t)` at `0` is the derivative of `f` at `a`. -/
lemma hasDerivAt_translate {f : ℝ → ℝ} {a d : ℝ} (h : HasDerivAt f d a) :
    HasDerivAt (fun t : ℝ => f (a + t)) d 0 := by
  have h2 : HasDerivAt f d (a + (0:ℝ)) := by simpa using h
  simpa using h2.comp (0:ℝ) ((hasDerivAt_id (0:ℝ)).const_add a)
/-- The value of a directional derivative `fderiv g C (single j 1)` is the derivative of the
restriction of `g` to the line `t ↦ C + t • single j 1`. -/
lemma fderiv_apply_single_eq {g : Pt → ℝ} {C : Pt} {j : Fin 2} (hg : DifferentiableAt ℝ g C)
    {d : ℝ} (hd : HasDerivAt (fun t : ℝ => g (C + t • EuclideanSpace.single j (1:ℝ))) d 0) :
    fderiv ℝ g C (EuclideanSpace.single j (1:ℝ)) = d := by
  have hline : HasDerivAt (fun t : ℝ => C + t • EuclideanSpace.single j (1:ℝ))
      (EuclideanSpace.single j (1:ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (EuclideanSpace.single j (1:ℝ))).const_add C
  have hf : HasFDerivAt g (fderiv ℝ g C) (C + (0:ℝ) • EuclideanSpace.single j (1:ℝ)) := by
    simpa using hg.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => g (C + t • EuclideanSpace.single j (1:ℝ)))
      (fderiv ℝ g C (EuclideanSpace.single j (1:ℝ))) 0 :=
    hf.comp_hasDerivAt 0 hline
  exact hcomp.unique hd
/-- The Jacobian determinant of `fmap c` at `C = (xC,yC)` is nonzero (it equals
`(xC²+yC²)/((xC-c)²+yC²) > 0`). -/
lemma fmap_fderiv_det_ne (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    (fderiv ℝ (fmap c) (!₂[xC, yC] : Pt)).det ≠ 0 := by
  set C : Pt := !₂[xC, yC] with hC
  have hdiff : DifferentiableAt ℝ (fmap c) C :=
    (fmap_contDiffAt c xC yC hyC harea).differentiableAt (by norm_num)
  set V := (xC ^ 2 + yC ^ 2) / ((xC - c) ^ 2 + yC ^ 2) with hV
  have hVpos : 0 < V := by rw [hV]; positivity
  have hcomp_fderiv : ∀ (i : Fin 2),
      HasFDerivAt (fun D : Pt => (fmap c D) i)
        ((EuclideanSpace.proj i).comp (fderiv ℝ (fmap c) C)) C := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp C hdiff.hasFDerivAt
  have hdiff_comp : ∀ (i : Fin 2), DifferentiableAt ℝ (fun D : Pt => (fmap c D) i) C :=
    fun i => (hcomp_fderiv i).differentiableAt
  have hentry : ∀ (i j : Fin 2),
      (fderiv ℝ (fmap c) C (EuclideanSpace.single j (1:ℝ))) i
        = fderiv ℝ (fun D => (fmap c D) i) C (EuclideanSpace.single j (1:ℝ)) := by
    intro i j
    rw [(hcomp_fderiv i).fderiv]; rfl
  have hM00 : fderiv ℝ (fun D => (fmap c D) 0) C (EuclideanSpace.single 0 (1:ℝ)) = 1 := by
    apply fderiv_apply_single_eq (hdiff_comp 0)
    have heq : (fun t : ℝ => (fmap c (C + t • EuclideanSpace.single (0:Fin 2) (1:ℝ))) 0)
        = fun t => xEval c (xC + t) yC := by
      funext t; rw [hC]; simp [fmap, EuclideanSpace.single_apply]
    rw [heq]
    exact hasDerivAt_translate (xEval_hasDerivAt_x c xC yC hc hyC harea)
  have hM10 : fderiv ℝ (fun D => (fmap c D) 1) C (EuclideanSpace.single 0 (1:ℝ)) = 0 := by
    apply fderiv_apply_single_eq (hdiff_comp 1)
    have heq : (fun t : ℝ => (fmap c (C + t • EuclideanSpace.single (0:Fin 2) (1:ℝ))) 1)
        = fun t => yEval c (xC + t) yC := by
      funext t; rw [hC]; simp [fmap, EuclideanSpace.single_apply]
    rw [heq]
    exact hasDerivAt_translate (yEval_hasDerivAt_x c xC yC hc hyC harea)
  have hM11 : fderiv ℝ (fun D => (fmap c D) 1) C (EuclideanSpace.single 1 (1:ℝ)) = V := by
    apply fderiv_apply_single_eq (hdiff_comp 1)
    have heq : (fun t : ℝ => (fmap c (C + t • EuclideanSpace.single (1:Fin 2) (1:ℝ))) 1)
        = fun t => yEval c xC (yC + t) := by
      funext t; rw [hC]; simp [fmap, EuclideanSpace.single_apply]
    rw [heq, hV]
    exact hasDerivAt_translate (yEval_hasDerivAt_y c xC yC hc hyC harea)
  set b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis with hb
  set L := fderiv ℝ (fmap c) C with hLdef
  have hdet : L.det = (LinearMap.toMatrix b b L.toLinearMap).det := by
    rw [LinearMap.det_toMatrix]
  rw [hdet, Matrix.det_fin_two]
  have hMij : ∀ (i j : Fin 2),
      LinearMap.toMatrix b b L.toLinearMap i j = (L (EuclideanSpace.single j (1:ℝ))) i := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    simp [hb, EuclideanSpace.basisFun_toBasis]
  rw [hMij, hMij, hMij, hMij]
  rw [show (L (EuclideanSpace.single (0:Fin 2) (1:ℝ))) 0 = (1:ℝ) from by
        rw [hLdef, hentry]; exact hM00,
     show (L (EuclideanSpace.single (1:Fin 2) (1:ℝ))) 1 = V from by
        rw [hLdef, hentry]; exact hM11,
     show (L (EuclideanSpace.single (0:Fin 2) (1:ℝ))) 1 = (0:ℝ) from by
        rw [hLdef, hentry]; exact hM10]
  simp only [mul_zero, sub_zero, one_mul]
  exact ne_of_gt hVpos
/-- The determinant of a continuous linear self-map of `Pt` depends continuously on the map. -/
lemma continuous_clm_det : Continuous (fun L : Pt →L[ℝ] Pt => L.det) := by
  set b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis with hb
  have heq : (fun L : Pt →L[ℝ] Pt => L.det)
      = fun L : Pt →L[ℝ] Pt => (LinearMap.toMatrix b b (L : Pt →ₗ[ℝ] Pt)).det := by
    funext L; rw [LinearMap.det_toMatrix]
  rw [heq]
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  have hcont : Continuous (fun L : Pt →L[ℝ] Pt => (L (EuclideanSpace.single j (1:ℝ)))) :=
    (ContinuousLinearMap.apply ℝ Pt (EuclideanSpace.single j (1:ℝ))).continuous
  have heq2 : (fun L : Pt →L[ℝ] Pt => LinearMap.toMatrix b b (L : Pt →ₗ[ℝ] Pt) i j)
      = fun L : Pt →L[ℝ] Pt => (EuclideanSpace.proj i) (L (EuclideanSpace.single j (1:ℝ))) := by
    funext L
    rw [hb]
    simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_toBasis, EuclideanSpace.proj]
  rw [heq2]
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hcont
/-
**Local diffeomorphism data for `fmap`.**  Near `C = (xC,yC)` (with `c·yC = 2`) the map `fmap c`
is a `C¹` local diffeomorphism: there is a ball `ball C r0` on which it is differentiable with
continuous derivative, injective, with Jacobian determinant bounded below by `m > 0` and is
`M`-Lipschitz toward `C`.  These are exactly the hypotheses needed for `overlap_of_diffeo`.
-/
lemma fmap_isDiffeoData (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    ∃ (m M r0 : ℝ), 0 < m ∧ 0 < M ∧ 0 < r0 ∧
      (∀ x ∈ Metric.ball (!₂[xC, yC] : Pt) r0,
        HasFDerivWithinAt (fmap c) (fderiv ℝ (fmap c) x) (Metric.ball (!₂[xC, yC] : Pt) r0) x) ∧
      (∀ x ∈ Metric.ball (!₂[xC, yC] : Pt) r0, m ≤ |(fderiv ℝ (fmap c) x).det|) ∧
      Set.InjOn (fmap c) (Metric.ball (!₂[xC, yC] : Pt) r0) ∧
      (∀ x ∈ Metric.ball (!₂[xC, yC] : Pt) r0,
        dist (fmap c x) (!₂[xC, yC] : Pt) ≤ M * dist x (!₂[xC, yC] : Pt)) := by
  -- Set `C := !₂[xC, yC] : Pt`.
  set C : Pt := !₂[xC, yC];
  obtain ⟨rInj, hrInj_pos, hrInj⟩ : ∃ rInj > 0, Set.InjOn (fmap c) (Metric.ball C rInj) := by
    have h_cont_diff : ContDiffAt ℝ 1 (fmap c) C := by
      exact fmap_contDiffAt c xC yC hyC harea;
    have h_inv_fun : HasStrictFDerivAt (fmap c) (fderiv ℝ (fmap c) C) C := by
      exact h_cont_diff.hasStrictFDerivAt ( by norm_num );
    have := h_inv_fun.isLittleO;
    rw [ Asymptotics.isLittleO_iff ] at this;
    -- Choose $c_1 = \frac{1}{2} \inf_{\|v\|=1} \|Df(C)v\|$.
    obtain ⟨c1, hc1_pos, hc1⟩ : ∃ c1 > 0, ∀ v : Pt, ‖v‖ = 1 → ‖(fderiv ℝ (fmap c) C) v‖ ≥ 2 * c1 := by
      have h_inv_fun : ∀ v : Pt, ‖v‖ = 1 → ‖(fderiv ℝ (fmap c) C) v‖ > 0 := by
        intro v hv; have := fmap_fderiv_det_ne c xC yC hc hyC harea; simp_all +decide [ ContinuousLinearMap.det ] ;
        intro h; have := LinearMap.ker_eq_bot.mp ( show LinearMap.ker ( fderiv ℝ ( fmap c ) C |> ContinuousLinearMap.toLinearMap ) = ⊥ from ?_ ) ; simp_all +decide ;
        · exact absurd ( this ( show ( fderiv ℝ ( fmap c ) C ) v = ( fderiv ℝ ( fmap c ) C ) 0 by aesop ) ) ( by aesop );
        · exact LinearMap.ker_eq_bot_of_injective ( LinearEquiv.injective ( LinearMap.equivOfDetNeZero _ this ) );
      have h_inv_fun : ∃ c1 > 0, ∀ v : Pt, ‖v‖ = 1 → ‖(fderiv ℝ (fmap c) C) v‖ ≥ c1 := by
        have h_compact : IsCompact {v : Pt | ‖v‖ = 1} := by
          convert ( isCompact_sphere ( 0 : Pt ) 1 ) using 1 ; ext ; simp +decide
        have h_min : ∃ v ∈ {v : Pt | ‖v‖ = 1}, ∀ w ∈ {v : Pt | ‖v‖ = 1}, ‖(fderiv ℝ (fmap c) C) v‖ ≤ ‖(fderiv ℝ (fmap c) C) w‖ := by
          have h_min : ContinuousOn (fun v : Pt => ‖(fderiv ℝ (fmap c) C) v‖) {v : Pt | ‖v‖ = 1} := by
            exact Continuous.continuousOn ( by continuity );
          exact h_compact.exists_isMinOn ⟨ EuclideanSpace.single 0 1, by norm_num ⟩ h_min;
        exact ⟨ ‖( fderiv ℝ ( fmap c ) C ) h_min.choose‖, h_inv_fun _ h_min.choose_spec.1, fun v hv => h_min.choose_spec.2 _ hv ⟩;
      exact ⟨ h_inv_fun.choose / 2, half_pos h_inv_fun.choose_spec.1, fun v hv => by linarith [ h_inv_fun.choose_spec.2 v hv ] ⟩;
    obtain ⟨ r, hr ⟩ := Metric.mem_nhds_iff.mp ( this hc1_pos );
    refine' ⟨ r / 2, half_pos hr.1, fun x hx y hy hxy => _ ⟩;
    have := hr.2 ( show ( x, y ) ∈ Metric.ball ( C, C ) r from ?_ );
    · contrapose! hc1;
      refine' ⟨ ( ‖x - y‖⁻¹ : ℝ ) • ( x - y ), _, _ ⟩ <;> simp_all +decide [ norm_smul, sub_eq_zero ];
      rw [ inv_mul_eq_div, div_lt_iff₀ ] <;> nlinarith [ norm_pos_iff.mpr ( sub_ne_zero.mpr hc1 ), norm_sub_rev ( ( fderiv ℝ ( fmap c ) C ) x ) ( ( fderiv ℝ ( fmap c ) C ) y ) ];
    · simp_all +decide [ Prod.dist_eq ];
      constructor <;> linarith;
  -- Set `m := |(Df C).det| / 2` and `M := ‖Df C‖ + 1`.
  obtain ⟨m, hm_pos, hm⟩ : ∃ m > 0, ∀ᶠ x in nhds C, m ≤ |(fderiv ℝ (fmap c) x).det| := by
    have h_cont_det : ContinuousAt (fun x => |(fderiv ℝ (fmap c) x).det|) C := by
      have h_cont_det : ContinuousAt (fun x => (fderiv ℝ (fmap c) x)) C := by
        have h_cont : ContDiffAt ℝ 1 (fmap c) C := by
          exact fmap_contDiffAt c xC yC hyC harea;
        have := h_cont;
        rw [ contDiffAt_one_iff ] at this;
        obtain ⟨ f', u, hu, hf', hf'' ⟩ := this; exact ContinuousAt.congr ( hf'.continuousAt hu ) ( Filter.eventuallyEq_of_mem hu fun x hx => HasFDerivAt.fderiv ( hf'' x hx ) ▸ rfl ) ;
      exact ContinuousAt.abs ( continuous_clm_det.continuousAt.comp h_cont_det );
    exact ⟨ |(fderiv ℝ (fmap c) C).det| / 2, half_pos ( abs_pos.mpr ( by simpa using fmap_fderiv_det_ne c xC yC hc hyC harea ) ), h_cont_det.eventually ( le_mem_nhds ( half_lt_self ( abs_pos.mpr ( by simpa using fmap_fderiv_det_ne c xC yC hc hyC harea ) ) ) ) ⟩
  obtain ⟨M, hM_pos, hM⟩ : ∃ M > 0, ∀ᶠ x in nhds C, ‖fderiv ℝ (fmap c) x‖ ≤ M := by
    have h_cont : ContinuousAt (fun x => ‖fderiv ℝ (fmap c) x‖) C := by
      have h_cont : ContDiffAt ℝ 1 (fmap c) C := by
        exact fmap_contDiffAt c xC yC hyC harea;
      have := h_cont.continuousAt_fderiv;
      exact ContinuousAt.norm ( this one_ne_zero );
    exact ⟨ ‖fderiv ℝ ( fmap c ) C‖ + 1, by positivity, h_cont.eventually ( ge_mem_nhds <| lt_add_one _ ) ⟩;
  obtain ⟨r0, hr0_pos, hr0⟩ : ∃ r0 > 0, Metric.ball C r0 ⊆ Metric.ball C rInj ∧ (∀ x ∈ Metric.ball C r0, m ≤ |(fderiv ℝ (fmap c) x).det|) ∧ (∀ x ∈ Metric.ball C r0, ‖fderiv ℝ (fmap c) x‖ ≤ M) ∧ (∀ x ∈ Metric.ball C r0, DifferentiableAt ℝ (fmap c) x) := by
    have h_diff : ∀ᶠ x in nhds C, DifferentiableAt ℝ (fmap c) x := by
      have := fmap_contDiffAt c xC yC hyC harea;
      exact this.eventually ( by norm_num ) |> fun h => h.mono fun x hx => hx.differentiableAt ( by norm_num );
    obtain ⟨ r0, hr0 ⟩ := Metric.mem_nhds_iff.mp ( hm.and ( hM.and h_diff ) );
    exact ⟨ Min.min r0 rInj, lt_min hr0.1 hrInj_pos, Metric.ball_subset_ball ( min_le_right _ _ ), fun x hx => hr0.2 ( Metric.ball_subset_ball ( min_le_left _ _ ) hx ) |>.1, fun x hx => hr0.2 ( Metric.ball_subset_ball ( min_le_left _ _ ) hx ) |>.2.1, fun x hx => hr0.2 ( Metric.ball_subset_ball ( min_le_left _ _ ) hx ) |>.2.2 ⟩;
  refine' ⟨ m, M, r0, hm_pos, hM_pos, hr0_pos, _, _, _, _ ⟩;
  · exact fun x hx => DifferentiableAt.hasFDerivAt ( hr0.2.2.2 x hx ) |> HasFDerivAt.hasFDerivWithinAt;
  · exact hr0.2.1;
  · exact hrInj.mono hr0.1;
  · intro x hx
    have h_lip : ‖fmap c x - fmap c C‖ ≤ M * ‖x - C‖ := by
      have := @Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le;
      specialize this (fun x hx => (hr0.2.2.2 x hx).hasFDerivAt.hasFDerivWithinAt) (fun x hx => hr0.2.2.1 x hx) (convex_ball C r0) (Metric.mem_ball_self hr0_pos) hx;
      exact this;
    convert h_lip using 1;
    rw [ dist_eq_norm, show fmap c C = C from by
                        ext i; fin_cases i <;> simp +decide [ fmap ] ;
                        · exact fmap_fixed c xC yC hc hyC harea |>.1;
                        · exact fmap_fixed c xC yC hc hyC harea |>.2 ]
/-
**Sign conditions near `C`.**  All the algebraic sign conditions used to build the cyclic
quadrilateral hold on a small ball around `C = (xC,yC)`: they hold strictly at `C` and are
continuous, so they persist on a neighborhood.
-/
lemma fmap_sign_conditions (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    ∃ ε1 > 0, ∀ x : Pt, dist x (!₂[xC, yC] : Pt) < ε1 →
      0 < x 1 ∧ 0 < Pcoef c (x 0) (x 1) ∧ 0 ≤ discr c (x 0) (x 1)
        ∧ Qcoef c (x 0) (x 1) < 0 ∧ 0 < 2 * Pcoef c (x 0) (x 1) * yC + Qcoef c (x 0) (x 1) := by
  convert Metric.eventually_nhds_iff.mp _ using 1;
  refine' Filter.eventually_and.mpr ⟨ _, _ ⟩;
  · have h_proj_cont : Continuous (fun x : Pt => x 1) := by
      fun_prop;
    exact h_proj_cont.continuousAt.eventually ( lt_mem_nhds hyC );
  · refine' Filter.eventually_and.mpr ⟨ _, _ ⟩;
    · refine' Metric.eventually_nhds_iff.mpr _;
      have h_cont : Continuous (fun y : Pt => Pcoef c (y 0) (y 1)) := by
        apply_rules [ Continuous.add, Continuous.mul, continuous_const, continuous_apply ];
        · exact continuous_apply 0 |> Continuous.comp <| continuous_induced_dom;
        · exact continuous_apply 0 |> Continuous.comp <| continuous_induced_dom;
        · fun_prop;
        · fun_prop;
      exact Metric.mem_nhds_iff.mp ( h_cont.continuousAt.eventually ( lt_mem_nhds <| show 0 < Pcoef c xC yC from by unfold Pcoef; nlinarith ) );
    · refine' Filter.eventually_and.mpr ⟨ _, _ ⟩;
      · refine' ContinuousAt.preimage_mem_nhds _ _;
        · unfold discr Qcoef Pcoef Rcoef; fun_prop;
        · refine' Ici_mem_nhds _;
          unfold discr Qcoef Pcoef Rcoef; norm_num; ring_nf;
          rw [ show c = 2 / yC by rw [ eq_div_iff hyC.ne' ] ; linarith ] ; ring_nf;
          field_simp;
          nlinarith [ sq_nonneg ( xC * yC - 2 ), sq_nonneg ( xC * yC ^ 2 - 2 * yC ), sq_nonneg ( xC ^ 2 * yC - 2 * xC ), sq_nonneg ( xC ^ 2 * yC ^ 2 - 4 ), pow_pos hyC 3, pow_pos hyC 4, pow_pos hyC 5, pow_pos hyC 6, pow_pos hyC 7, pow_pos hyC 8 ];
      · refine' Filter.eventually_and.mpr ⟨ _, _ ⟩;
        · refine' ContinuousAt.preimage_mem_nhds ( show ContinuousAt ( fun x : Pt => Qcoef c ( x.ofLp 0 ) ( x.ofLp 1 ) ) ( !₂[xC, yC] ) from _ ) ( Iio_mem_nhds _ );
          · refine' Continuous.continuousAt _;
            apply_rules [ Continuous.sub, Continuous.add, Continuous.mul, continuous_const, continuous_apply ];
            all_goals fun_prop;
          · unfold Qcoef;
            nlinarith! [ sq_nonneg ( xC - c ), sq_nonneg ( yC - c ), mul_pos hc hyC ];
        · refine' ContinuousAt.preimage_mem_nhds ( show ContinuousAt ( fun x : Pt => 2 * Pcoef c ( x.ofLp 0 ) ( x.ofLp 1 ) * yC + Qcoef c ( x.ofLp 0 ) ( x.ofLp 1 ) ) _ from _ ) ( Ioi_mem_nhds _ );
          · unfold Pcoef Qcoef; fun_prop;
          · unfold Pcoef Qcoef; norm_num [ harea ] ; ring_nf ;
            nlinarith [ sq_nonneg ( xC - c ), sq_nonneg ( yC - 1 ), mul_pos hc hyC ]
/-- **The analytic overlap (perturbation + density).**  Given a configuration, there is a point
`D = (xD, yD)` in `S`, lying just below the apex `C` (`0 < yD`, `c·yD < 2`, i.e. `yD < yC`), inside
the region where the perturbation map is a local diffeomorphism (`discr ≥ 0`, `Pcoef > 0`,
`Qcoef < 0`, `2·Pcoef·yC + Qcoef > 0`), and such that its image `E = f(D)` is also in `S`.
This is the heart of the second half of the paper: it combines the inverse/implicit function theorem
(local invertibility of `f`), the change-of-variables formula, and the Lebesgue density of `S` at
`C` in an overlap argument. -/
lemma exists_lower_pair (S : Set Pt) (c xC yC : ℝ) (h : Config S c xC yC) :
    ∃ xD yD : ℝ, (!₂[xD, yD] : Pt) ∈ S
      ∧ (!₂[xEval c xD yD, yEval c xD yD] : Pt) ∈ S
      ∧ 0 < yD ∧ c * yD < 2 ∧ 0 < Pcoef c xD yD ∧ 0 ≤ discr c xD yD
      ∧ Qcoef c xD yD < 0 ∧ 0 < 2 * Pcoef c xD yD * yC + Qcoef c xD yD := by
  have hc := h.c_pos
  have hyC := h.yC_pos
  have harea := h.area
  obtain ⟨m, M, r0, hm, hM, hr0, hderiv, hdet, hinj, hLip⟩ :=
    fmap_isDiffeoData c xC yC hc hyC harea
  obtain ⟨ε1, hε1, hsign⟩ := fmap_sign_conditions c xC yC hc hyC harea
  have hdens : IsDensityPt S (!₂[xC, yC] : Pt) := h.dens
  set ε := min ε1 r0 with hεdef
  have hεpos : 0 < ε := lt_min hε1 hr0
  obtain ⟨D, hDε, hDbelow, hDS, hfDS⟩ :=
    overlap_of_diffeo S (!₂[xC, yC] : Pt) (fmap c) (fun x => fderiv ℝ (fmap c) x)
      m M r0 hm hM hr0 h.meas hderiv hdet hinj hLip hdens ε hεpos
  have hsignD := hsign D (lt_of_lt_of_le hDε (min_le_left _ _))
  have hD1lt : D 1 < yC := by
    have h2 := hDbelow
    simpa using h2
  refine ⟨D 0, D 1, ?_, ?_, hsignD.1, ?_, hsignD.2.1, hsignD.2.2.1,
    hsignD.2.2.2.1, hsignD.2.2.2.2⟩
  · have hDeq : (!₂[D 0, D 1] : Pt) = D := by
      ext i; fin_cases i <;> simp
    rw [hDeq]; exact hDS
  · have hEeq : (!₂[xEval c (D 0) (D 1), yEval c (D 0) (D 1)] : Pt) = fmap c D := rfl
    rw [hEeq]; exact hfDS
  · have h2 : c * D 1 < c * yC := mul_lt_mul_of_pos_left hD1lt hc
    rwa [harea] at h2
/-- **Second half of the proof.** The perturbation argument: given a configuration, one finds two
further points `D, E ∈ S` such that `A B E D` is a unit cyclic quadrilateral. -/
lemma exists_quad_of_config (S : Set Pt) (c xC yC : ℝ) (h : Config S c xC yC) :
    ∃ D E : Pt, D ∈ S ∧ E ∈ S ∧
      UnitCyclicQuad (!₂[(0 : ℝ), (0 : ℝ)] : Pt) (!₂[c, (0 : ℝ)] : Pt) E D := by
  obtain ⟨xD, yD, hDS, hES, hyD, hyD', hP, hdisc, hQ, hpos⟩ := exists_lower_pair S c xC yC h
  have hc := h.c_pos
  have hyC := h.yC_pos
  have harea := h.area
  have hyEpos : 0 < yEval c xD yD := yEval_pos c xD yD hP hQ
  have hyDlt : yD < yC := by
    have : c * yD < c * yC := by rw [harea]; exact hyD'
    exact lt_of_mul_lt_mul_left this hc.le
  have hyElt : yEval c xD yD < yC :=
    yEval_lt_yC c xD yD yC hyC harea hyD hyDlt hP hdisc hpos
  have hcyE : c * yEval c xD yD < 2 := by
    have : c * yEval c xD yD < c * yC := by exact mul_lt_mul_of_pos_left hyElt hc
    rwa [harea] at this
  refine ⟨!₂[xD, yD], !₂[xEval c xD yD, yEval c xD yD], hDS, hES, ?_, ?_, ?_⟩
  · exact concyclic_ABED c xD yD hyD hc hP hdisc
  · exact convex_ABED c xD yD hc hyD hyD' hyEpos hcyE
  · exact quadArea_ABED c xD yD hyD.ne'
/- ===================== Main ===================== -/
/-- **Theorem (Kovac-Predojevic).**
Every measurable planar set `A` of infinite Lebesgue measure contains the four vertices of a
cyclic quadrilateral of area `1`. -/
theorem exists_unitCyclicQuad_of_volume_infinite
    (A : Set Pt) (hA : MeasurableSet A) (hA_inf : volume A = ⊤) :
    ∃ P Q R S : Pt, P ∈ A ∧ Q ∈ A ∧ R ∈ A ∧ S ∈ A ∧ UnitCyclicQuad P Q R S := by
  obtain ⟨a, b, v1, v2, c, xC, yC, hab, hcfg⟩ := exists_config A hA hA_inf
  obtain ⟨D, E, hD, hE, hquad⟩ := exists_quad_of_config (rigid a b v1 v2 '' A) c xC yC hcfg
  obtain ⟨pA, hpA, hpAeq⟩ := hcfg.memA
  obtain ⟨pB, hpB, hpBeq⟩ := hcfg.memB
  obtain ⟨pE, hpE, hpEeq⟩ := hE
  obtain ⟨pD, hpD, hpDeq⟩ := hD
  refine ⟨pA, pB, pE, pD, hpA, hpB, hpE, hpD, ?_⟩
  have key := (unitCyclicQuad_rigid_iff (v1 := v1) (v2 := v2) hab pA pB pE pD).mp
  rw [hpAeq, hpBeq, hpEeq, hpDeq] at key
  exact key hquad

end CyclicQuad

-- ============================================================
-- KovacPredojevicT2
-- ============================================================

/-!
# Polygons of unit area with vertices in sets of infinite planar measure
Formalization of Theorem `thm:congruent` from Kovač–Predojević,
"Polygons of unit area with vertices in sets of infinite planar measure".
There exists a planar set `S` of infinite Lebesgue measure such that every convex
polygon with congruent sides and all vertices in `S` has area strictly less than `1`.
The plane is `EuclideanSpace ℝ (Fin 2)`, so `dist` is the Euclidean distance and
`volume` is the planar Lebesgue (area) measure.  A convex polygon is given by its
cyclic sequence of vertices `C : ZMod n → EuclideanSpace ℝ (Fin 2)` (`n ≥ 3`); the
counter-clockwise convexity is expressed by the cross-product positivity condition,
its sides are the segments `[C i, C (i+1)]`, and its *area* is the Lebesgue measure
of the convex hull of the vertices.
## Proof status
The top-level statement `thm_congruent` is assembled from the lemmas below.  The
following analytic/measure-theoretic ingredients are fully proved:
`volume_Sset_top` (the set has infinite area), `volume_tri_prod` / `volume_tri`
(the area of a triangle cut from the axes), `hyparea_identity` (Lemma `lm:hyparea`),
`tri_convex`, and `exists_support_triangle` (the convex hull lies in the support
triangle).  The reduction `area_lt_one` is proved from the two lemmas below, with
the small-side (`a < 2`) case fully discharged.
`exists_support_line` (existence of the tangent/secant support line of the hyperbola
lying above all vertices) is now proved, by splitting on whether a common tangent
exists: the tangent (Case A) case is elementary, and the secant (`support_line_caseB`)
case is assembled from `caseB_minimizer` (`= caseB_min_point` + `caseB_contacts`, the
analytic minimizer of the support function) and `caseB_adjacent` (contiguity of the
maximizing face), the latter resting on `turn_left` and `chord_side` (convex position:
three cyclically-ordered vertices form a counter-clockwise triangle).
`chord_side` is now fully proved.  Note that it requires *strict* convexity
(`hsconv : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < cross (C (i+1) - C i) (C j - C i)`), i.e. the
hypothesis that the vertices are in genuinely convex position (every non-adjacent
vertex lies strictly to the left of each edge).  This is the faithful notion of a
"convex polygon": under merely *weak* convexity (`0 ≤ cross …`, the original `hconv`)
the statement is in fact **false**, since weak convexity also admits degenerate
multiply-traced configurations.  For instance the "triangle traced twice"
`C = !«(0,0),(-1,0),(0,-1),(0,0),(-1,0),(0,-1)»` (n = 6) satisfies `hconv`, yet for
`a = 0, s = 2, t = 2` one computes `cross (C (a+4) - C a) (C (a+2) - C a) = 1 > 0`,
violating the conclusion.  Strict convexity excludes exactly these degenerate cases:
the lone remaining branch of the angle-sorting induction (`cross (g 1) (g m) = 0`)
becomes vacuous because `hsconv` forces `cross (g m) (g (n-1)) > 0`.
The strict-convexity hypothesis `hsconv` is threaded through `caseB_adjacent`,
`support_line_caseB`, `exists_support_line`, `exists_support_triangle`, `area_lt_one`
and the top-level `thm_congruent` (whose statement now characterises convex polygons
by strict convexity; the weak `hconv` is recovered internally where needed).
`area_lt_one_of_large` (the large-side `a ≥ 2` case) is now also fully proved, via a
width/total-variation argument rather than the paper's leftmost/rightmost adjacency
argument.  Assuming `1 ≤ area`, the support triangle gives `(x₁+x₂)² ≤ 2a²` and
`xmax ≤ x₁+x₂`.  Each side has horizontal extent `≥ √(a²-1/16)` (`edge_dx_ge`, vertices
lie in the strip `0 < y < 1/4`), and the total `x`-variation of the convex polygon is
`≤ 2·(xmax - xmin)` (`two_width_ge_sum`, cyclic unimodality of `x`).  Hence
`n·√(a²-1/16) ≤ 2(x₁+x₂) ≤ 2√2·a`, forcing `n < 3`, a contradiction.  The unimodality
rests on `x_valley` (the `x`-coordinate is a single valley when read from the rightmost
vertex), whose convex-position core is `no_interior_peak_alg` (an interior `x`-peak
below the maximum would make the two diagonals of a convex quadrilateral cross at a
point with contradictory `x`-coordinate).
-/
namespace Kovac
/-- The 2×2 determinant / signed cross product of two planar vectors. -/
noncomputable def cross (u v : EuclideanSpace ℝ (Fin 2)) : ℝ := u 0 * v 1 - u 1 * v 0
/-- Membership predicate for the set `S = { (x,y) : x > 1, y > 0, 4xy < 1 }`. -/
def inS (p : EuclideanSpace ℝ (Fin 2)) : Prop := 1 < p 0 ∧ 0 < p 1 ∧ 4 * p 0 * p 1 < 1
/-- The set `S = { (x,y) : x > 1, y > 0, 4xy < 1 }`. -/
def Sset : Set (EuclideanSpace ℝ (Fin 2)) := {p | inS p}
/-
The set `S` has infinite planar Lebesgue measure.
-/
theorem volume_Sset_top : volume Sset = ⊤ := by
  refine' eq_top_iff.mpr _;
  -- For each natural number `k ≥ 1`, consider the box where the first coordinate lies in `Ioo (k:ℝ) (k+1)` and the second coordinate lies in `Ioo 0 (1/(4*(k+1)))`.
  have h_boxes : ∀ k : ℕ, k ≥ 1 → volume {p : EuclideanSpace ℝ (Fin 2) | k < p 0 ∧ p 0 < k + 1 ∧ 0 < p 1 ∧ p 1 < 1 / (4 * (k + 1))} = ENNReal.ofReal (1 / (4 * (k + 1))) := by
    intro k hk
    set box_k : Set (Fin 2 → ℝ) := {p : Fin 2 → ℝ | k < p 0 ∧ p 0 < k + 1 ∧ 0 < p 1 ∧ p 1 < 1 / (4 * (k + 1))}
    have h_box_k : volume {p : EuclideanSpace ℝ (Fin 2) | k < p 0 ∧ p 0 < k + 1 ∧ 0 < p 1 ∧ p 1 < 1 / (4 * (k + 1))} = volume box_k := by
      convert ( MeasureTheory.MeasurePreserving.measure_preimage ( show MeasureTheory.MeasurePreserving ( fun p : EuclideanSpace ℝ ( Fin 2 ) => p.ofLp ) volume volume from ?_ ) ?_ ) using 1;
      · rfl;
      · exact PiLp.volume_preserving_ofLp _;
      · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.inter ( measurableSet_lt measurable_const ( measurable_pi_apply 0 ) ) ( MeasurableSet.inter ( measurableSet_lt ( measurable_pi_apply 0 ) measurable_const ) ( MeasurableSet.inter ( measurableSet_lt measurable_const ( measurable_pi_apply 1 ) ) ( measurableSet_lt ( measurable_pi_apply 1 ) measurable_const ) ) ) );
    -- The volume of the box is the product of the lengths of its sides.
    have h_box_volume : volume box_k = ENNReal.ofReal ((k + 1 - k) * (1 / (4 * (k + 1)))) := by
      have h_box_volume : volume box_k = volume (Set.pi Set.univ fun i : Fin 2 => if i = 0 then Set.Ioo (k : ℝ) (k + 1) else Set.Ioo 0 (1 / (4 * (k + 1) : ℝ))) := by
        congr with p ; simp +decide [ Fin.forall_fin_two ] ; aesop;
      erw [ h_box_volume, MeasureTheory.Measure.pi_pi ] ; norm_num;
    aesop;
  -- Since these boxes are pairwise disjoint and their union is contained in `Sset`, we can apply the countable additivity of the volume measure.
  have h_union : volume (⋃ k : ℕ, ⋃ hk : k ≥ 1, {p : EuclideanSpace ℝ (Fin 2) | k < p 0 ∧ p 0 < k + 1 ∧ 0 < p 1 ∧ p 1 < 1 / (4 * (k + 1))}) = ∑' k : ℕ, if k ≥ 1 then ENNReal.ofReal (1 / (4 * (k + 1))) else 0 := by
    rw [ MeasureTheory.measure_iUnion ];
    · congr with k ; aesop;
    · intro k l hkl; simp_all +decide [ Set.disjoint_left ] ;
      intro p hk₁ hk₂ hk₃ hk₄ hk₅ hl₁ hl₂ hl₃; contrapose! hkl; exact Nat.le_antisymm ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith } ) ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith } ) ;
    · intro k; by_cases hk : 1 ≤ k <;> simp +decide [ hk ];
      fun_prop;
  -- Since the series $\sum_{k=1}^{\infty} \frac{1}{4(k+1)}$ diverges, we have $\sum' k : ℕ, if k ≥ 1 then ENNReal.ofReal (1 / (4 * (k + 1))) else 0 = \top$.
  have h_diverges : ∑' k : ℕ, (if k ≥ 1 then ENNReal.ofReal (1 / (4 * (k + 1))) else 0) = ⊤ := by
    have h_diverges : ¬ Summable (fun k : ℕ => if k ≥ 1 then (1 / (4 * (k + 1) : ℝ)) else 0) := by
      erw [ ← summable_nat_add_iff 1 ] ; norm_num;
      erw [ summable_mul_right_iff ] <;> norm_num ; exact_mod_cast mt ( summable_nat_add_iff 2 |>.1 ) Real.not_summable_natCast_inv;
    contrapose! h_diverges;
    convert ENNReal.summable_toReal _;
    rotate_left;
    use fun k => if k ≥ 1 then ENNReal.ofReal ( 1 / ( 4 * ( k + 1 ) ) ) else 0;
    · convert h_diverges using 1;
    · split_ifs <;> norm_num [ ENNReal.toReal_ofReal ( by positivity : 0 ≤ ( 4 * ( ↑‹ℕ› + 1 ) : ℝ ) ⁻¹ ) ];
      rw [ ENNReal.toReal_ofReal ( by positivity ) ];
  refine' h_diverges ▸ h_union ▸ MeasureTheory.measure_mono _;
  simp +decide [ Set.subset_def, Sset ];
  intro p k hk₁ hk₂ hk₃ hk₄ hk₅; exact ⟨ by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ], hk₃, by norm_num at *; nlinarith [ mul_inv_cancel₀ ( by linarith : ( k : ℝ ) + 1 ≠ 0 ) ] ⟩ ;
/-- The closed triangle cut from the first quadrant by the line with positive
`x`-intercept `p` and `y`-intercept `q`. -/
def tri (p q : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 0 / p + z 1 / q ≤ 1}
/-
The triangle `tri p q` is convex.
-/
theorem tri_convex (p q : ℝ) : Convex ℝ (tri p q) := by
  intro x hx y hy a b ha hb hab;
  simp_all +decide [ tri ];
  exact ⟨ by nlinarith, by nlinarith, by rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ring_nf at *; nlinarith ⟩
/-
The same triangle, but as a subset of `ℝ × ℝ`.
-/
theorem volume_tri_prod (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    volume {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 / p + z.2 / q ≤ 1}
      = ENNReal.ofReal (p * q / 2) := by
  erw [ MeasureTheory.Measure.prod_apply ];
  · rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
    change ∫⁻ x in Set.Icc 0 p, ENNReal.ofReal ( q * ( 1 - x / p ) ) = ENNReal.ofReal ( p * q / 2 );
    · rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      · congr 1
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp.le]
        have hfun : (fun x : ℝ => q * (1 - x / p)) = (fun x => q - (q / p) * x) := by
          funext x; field_simp
        rw [hfun, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) 0 p)
            (Continuous.intervalIntegrable (by fun_prop) 0 p), intervalIntegral.integral_const,
            intervalIntegral.integral_const_mul, integral_id]
        simp only [smul_eq_mul]; field_simp; ring
      · exact Continuous.integrableOn_Icc ( by continuity );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using mul_nonneg hq.le ( sub_nonneg.2 <| div_le_one_of_le₀ hx.2 hp.le );
    · norm_num;
    · filter_upwards [ ] with x ; by_cases hx : 0 ≤ x <;> by_cases hx' : x ≤ p <;> simp +decide [ *, Set.indicator ];
      · rw [ show { a : ℝ | 0 ≤ a ∧ x / p + a / q ≤ 1 } = Set.Icc 0 ( q * ( 1 - x / p ) ) from ?_ ];
        · simp +decide [ Real.volume_Icc ];
        · exact Set.ext fun y => ⟨ fun hy => ⟨ hy.1, by nlinarith [ hy.2, mul_div_cancel₀ x hp.ne', mul_div_cancel₀ y hq.ne' ] ⟩, fun hy => ⟨ hy.1, by nlinarith [ hy.2, mul_div_cancel₀ x hp.ne', mul_div_cancel₀ y hq.ne' ] ⟩ ⟩;
      · exact MeasureTheory.measure_mono_null ( fun y hy => by nlinarith [ hy.1, hy.2, div_mul_cancel₀ x hp.ne', div_mul_cancel₀ y hq.ne', mul_pos hp hq ] ) ( MeasureTheory.measure_empty );
  · exact MeasurableSet.inter ( measurableSet_le measurable_const measurable_fst ) ( MeasurableSet.inter ( measurableSet_le measurable_const measurable_snd ) ( measurableSet_le ( measurable_fst.div_const p |> Measurable.add <| measurable_snd.div_const q ) measurable_const ) )
/-
The area of the triangle `tri p q` is `p*q/2`.
-/
theorem volume_tri (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    volume (tri p q) = ENNReal.ofReal (p * q / 2) := by
  -- The set `tri p q` is the preimage of the set `{z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 / p + z.2 / q ≤ 1}` under the map `e := (volume_preserving_finTwoArrow ℝ).comp PiLp.volume_preserving_ofLp`.
  set e : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun z => (z 0, z 1);
  rw [ show tri p q = e ⁻¹' { z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 / p + z.2 / q ≤ 1 } from ?_ ];
  · convert volume_tri_prod p q hp hq using 1;
    convert ( MeasureTheory.MeasurePreserving.measure_preimage <| ?_ ) _;
    · convert ( MeasureTheory.volume_preserving_finTwoArrow ℝ ).comp ( PiLp.volume_preserving_ofLp _ ) using 1;
    · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.inter ( measurableSet_le measurable_const measurable_fst ) ( MeasurableSet.inter ( measurableSet_le measurable_const measurable_snd ) ( measurableSet_le ( measurable_fst.div_const p |> Measurable.add <| measurable_snd.div_const q ) measurable_const ) ) );
  · aesop
/-
Algebraic identity behind Lemma `lm:hyparea`: the triangle the secant of the
hyperbola `4xy=1` through `(x₁,1/(4x₁))` and `(x₂,1/(4x₂))` cuts from the axes has
area `(x₁+x₂)²/(8 x₁ x₂) = 1/2 + (x₁-x₂)²/(8 x₁ x₂)`.
-/
theorem hyparea_identity (x1 x2 : ℝ) (h1 : 0 < x1) (h2 : 0 < x2) :
    (x1 + x2) ^ 2 / (8 * x1 * x2) = 1 / 2 + (x1 - x2) ^ 2 / (8 * x1 * x2) := by
  have h : (8 : ℝ) * x1 * x2 ≠ 0 := by positivity
  field_simp
  ring
/-
**Analytic core of Case B.**  When for every contact `t ≥ 1` some vertex lies
strictly above the tangent `x + 4t²y = 2t`, the support function
`h t = ⨆ᵢ (C i 0 + 4t² · C i 1 - 2t)` is positive and coercive on `[1,∞)`, hence
attains a positive minimum `m` at some `t > 1`.  At that minimizer two vertices attain
the maximum, one with `8 · C iR 1 · t ≤ 2` (`y ≤ 1/(4t)`) and one with
`2 ≤ 8 · C iL 1 · t` (`y ≥ 1/(4t)`): these are the two contacts of the narrowest
secant support line.
-/
theorem caseB_min_point
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (hn : 3 ≤ n)
    (hS : ∀ i : ZMod n, inS (C i))
    (hB : ∀ t : ℝ, 1 ≤ t → ∃ i : ZMod n, 2 * t < C i 0 + 4 * t ^ 2 * C i 1) :
    ∃ (t m : ℝ), 1 < t ∧ 0 < m ∧
      (∀ i : ZMod n, C i 0 + 4 * t ^ 2 * C i 1 - 2 * t ≤ m) ∧
      (∀ s : ℝ, 1 ≤ s → ∃ i : ZMod n, m ≤ C i 0 + 4 * s ^ 2 * C i 1 - 2 * s) := by
  revert hB;
  intro hB
  haveI : NeZero n := ⟨by linarith⟩
  set h : ℝ → ℝ := fun s => Finset.univ.sup' Finset.univ_nonempty (fun i => (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s) with hh_def
  have h_cont : Continuous h := by
    fun_prop
  have h_pos : ∀ s : ℝ, 1 ≤ s → 0 < h s := by
    intro s hs; obtain ⟨ i, hi ⟩ := hB s hs; exact lt_of_lt_of_le ( by linarith ) ( Finset.le_sup' ( fun i => ( C i |> fun x => x.ofLp 0 + 4 * s ^ 2 * x.ofLp 1 - 2 * s ) ) ( Finset.mem_univ i ) ) ;
  have h_coercive : Filter.Tendsto h Filter.atTop Filter.atTop := by
    -- Fix an arbitrary $i0$.
    obtain ⟨i0, hi0⟩ : ∃ i0 : ZMod n, 0 < (C i0) 1 := by
      exact ⟨ 0, hS 0 |>.2.1 ⟩;
    -- Since $4 * (C i0) 1 > 0$, we have $h(s) \geq (C i0) 0 + 4 * s^2 * (C i0) 1 - 2 * s$.
    have h_lower_bound : ∀ s : ℝ, 1 ≤ s → h s ≥ (C i0) 0 + 4 * s^2 * (C i0) 1 - 2 * s := by
      exact fun s hs => Finset.le_sup' ( fun i => ( C i |> fun x => x.ofLp 0 ) + 4 * s ^ 2 * ( C i |> fun x => x.ofLp 1 ) - 2 * s ) ( Finset.mem_univ i0 );
    refine' Filter.tendsto_atTop.mpr _;
    intro b; filter_upwards [ Filter.eventually_ge_atTop 1, Filter.eventually_gt_atTop ( ( |b - ( C i0 |> fun x => x.ofLp 0 )| + 2 ) / ( 4 * ( C i0 |> fun x => x.ofLp 1 ) ) + 1 ) ] with s hs₁ hs₂; cases abs_cases ( b - ( C i0 |> fun x => x.ofLp 0 ) ) <;> nlinarith [ h_lower_bound s hs₁, mul_div_cancel₀ ( |b - ( C i0 |> fun x => x.ofLp 0 )| + 2 ) ( by positivity : ( 4 * ( C i0 |> fun x => x.ofLp 1 ) ) ≠ 0 ), mul_le_mul_of_nonneg_left hs₂.le hi0.le ] ;
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 1 < t ∧ ∀ s : ℝ, 1 ≤ s → h t ≤ h s := by
    -- Since $h$ is continuous and coercive, it must attain a global minimum on $[1, \infty)$.
    obtain ⟨t, ht⟩ : ∃ t : ℝ, 1 ≤ t ∧ ∀ s : ℝ, 1 ≤ s → h t ≤ h s := by
      -- By the properties of continuous functions on compact intervals, $h$ attains its minimum on $[1, M]$ for some $M > 1$.
      obtain ⟨M, hM⟩ : ∃ M : ℝ, 1 < M ∧ ∀ s : ℝ, M ≤ s → h s > h 1 := by
        exact Filter.eventually_atTop.mp ( h_coercive.eventually_gt_atTop ( h 1 ) ) |> fun ⟨ M, hM ⟩ ↦ ⟨ Max.max M 2, by norm_num, fun s hs ↦ hM s ( le_trans ( le_max_left _ _ ) hs ) ⟩;
      -- By the properties of continuous functions on compact intervals, $h$ attains its minimum on $[1, M]$.
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Icc 1 M, ∀ s ∈ Set.Icc 1 M, h t ≤ h s := by
        exact ( IsCompact.exists_isMinOn ( CompactIccSpace.isCompact_Icc ) ⟨ 1, Set.left_mem_Icc.mpr hM.1.le ⟩ h_cont.continuousOn );
      exact ⟨ t, ht.1.1, fun s hs => if hs' : s ≤ M then ht.2 s ⟨ hs, hs' ⟩ else by linarith [ hM.2 s ( le_of_not_ge hs' ), ht.2 1 ⟨ by norm_num, by linarith ⟩ ] ⟩;
    by_cases ht_eq_one : t = 1;
    · -- For each `i`, `φ i` is the parabola `4*C i 1*s^2 - 2*s + C i 0` whose derivative at `s = 1` is `8*C i 1 - 2 < 0` (as `C i 1 < 1/4`); so each `φ i` is strictly decreasing immediately to the right of `1`.
      have h_deriv_neg : ∀ i : ZMod n, deriv (fun s : ℝ => (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s) 1 < 0 := by
        intro i; norm_num [ mul_comm ] ; nlinarith [ hS i |>.1, hS i |>.2.1, hS i |>.2.2 ] ;
      -- Since each `φ i` is strictly decreasing immediately to the right of `1`, there exists a `δ > 0` such that for all `s ∈ (1, 1 + δ)`, `φ i s < φ i 1`.
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ s ∈ Set.Ioo 1 (1 + δ), ∀ i : ZMod n, (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s < (C i) 0 + 4 * 1^2 * (C i) 1 - 2 * 1 := by
        have h_deriv_neg : ∀ i : ZMod n, ∃ δ > 0, ∀ s ∈ Set.Ioo 1 (1 + δ), (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s < (C i) 0 + 4 * 1^2 * (C i) 1 - 2 * 1 := by
          intro i
          have h_deriv_neg_i : deriv (fun s : ℝ => (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s) 1 < 0 := h_deriv_neg i
          have h_deriv_neg_i_pos : ∃ δ > 0, ∀ s ∈ Set.Ioo 1 (1 + δ), (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s < (C i) 0 + 4 * 1^2 * (C i) 1 - 2 * 1 := by
            have := Metric.tendsto_nhdsWithin_nhds.mp ( HasDerivAt.tendsto_slope_zero ( hasDerivAt_deriv_iff.mpr <| show DifferentiableAt ℝ ( fun s : ℝ => ( C i |> fun x => x.ofLp 0 ) + 4 * s ^ 2 * ( C i |> fun x => x.ofLp 1 ) - 2 * s ) 1 from by norm_num [ mul_comm ] ) );
            obtain ⟨ δ, hδ₁, H ⟩ := this _ ( neg_pos.mpr h_deriv_neg_i ) ; use δ, hδ₁; intro s hs; have := H ( show ( s - 1 ) ≠ 0 from sub_ne_zero.mpr hs.1.ne' ) ( abs_lt.mpr ⟨ by linarith [ hs.1, hs.2 ], by linarith [ hs.1, hs.2 ] ⟩ ) ; norm_num at *;
            nlinarith [ abs_lt.mp this, inv_mul_cancel₀ ( by linarith : ( s - 1 ) ≠ 0 ) ]
          exact h_deriv_neg_i_pos;
        choose δ hδ_pos hδ using h_deriv_neg;
        -- Since there are finitely many `i`, we can take the minimum of the `δ i`'s.
        obtain ⟨δ_min, hδ_min_pos, hδ_min⟩ : ∃ δ_min > 0, ∀ i : ZMod n, δ_min ≤ δ i := by
          have h_min : ∃ i : ZMod n, ∀ j : ZMod n, δ i ≤ δ j := by
            simpa using Finset.exists_min_image Finset.univ ( fun i => δ i ) ⟨ 0, Finset.mem_univ 0 ⟩;
          exact ⟨ δ h_min.choose, hδ_pos _, h_min.choose_spec ⟩;
        exact ⟨ δ_min, hδ_min_pos, fun s hs i => hδ i s ⟨ hs.1, by linarith [ hs.2, hδ_min i ] ⟩ ⟩;
      -- Since `h` is the supremum of the `φ i` functions, and each `φ i` is strictly decreasing immediately to the right of `1`, `h` must also be strictly decreasing immediately to the right of `1`.
      have h_h_decreasing : ∀ s ∈ Set.Ioo 1 (1 + δ), h s < h 1 := by
        grind +suggestions;
      exact absurd ( h_h_decreasing ( 1 + δ / 2 ) ⟨ by linarith, by linarith ⟩ ) ( by subst ht_eq_one; linarith [ ht.2 ( 1 + δ / 2 ) ( by linarith ) ] );
    · exact ⟨ t, lt_of_le_of_ne ht.1 ( Ne.symm ht_eq_one ), ht.2 ⟩
  use t, h t;
  simp +zetaDelta at *;
  exact ⟨ ht.1, h_pos t ht.1.le, fun i => ⟨ i, le_rfl ⟩, ht.2 ⟩
/-
**Contact extraction.**  At an interior global minimizer `t > 1` of the support
function (value `m`, with `hsup` the upper bound and `hglob` global minimality), two
active vertices straddle the tangency height `1/(4t)`: one with `8·C iR 1·t ≤ 2` and
one with `2 ≤ 8·C iL 1·t`.  This is the one-sided derivative test for the kinked
minimum.
-/
theorem caseB_contacts
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (hn : 3 ≤ n)
    (hS : ∀ i : ZMod n, inS (C i))
    (t m : ℝ) (ht1 : 1 < t)
    (hsup : ∀ i : ZMod n, C i 0 + 4 * t ^ 2 * C i 1 - 2 * t ≤ m)
    (hglob : ∀ s : ℝ, 1 ≤ s → ∃ i : ZMod n, m ≤ C i 0 + 4 * s ^ 2 * C i 1 - 2 * s) :
    (∃ iR : ZMod n, C iR 0 + 4 * t ^ 2 * C iR 1 - 2 * t = m ∧ 8 * C iR 1 * t ≤ 2) ∧
    (∃ iL : ZMod n, C iL 0 + 4 * t ^ 2 * C iL 1 - 2 * t = m ∧ 2 ≤ 8 * C iL 1 * t) := by
  constructor;
  · by_contra! h_contra;
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, δ < t - 1 ∧ ∀ i, (C i).ofLp 0 + 4 * (t - δ) ^ 2 * (C i).ofLp 1 - 2 * (t - δ) < m := by
      have hδ_exists : ∀ i, ∃ δ_i > 0, ∀ δ, 0 < δ ∧ δ < δ_i → (C i).ofLp 0 + 4 * (t - δ) ^ 2 * (C i).ofLp 1 - 2 * (t - δ) < m := by
        intro i
        by_cases hi : (C i).ofLp 0 + 4 * t ^ 2 * (C i).ofLp 1 - 2 * t = m;
        · use (8 * (C i).ofLp 1 * t - 2) / (8 * (C i).ofLp 1);
          exact ⟨ div_pos ( by linarith [ h_contra i hi ] ) ( by linarith [ h_contra i hi, show 0 < ( C i |> fun x => x.ofLp 1 ) from by have := hS i; exact this.2.1 ] ), fun δ hδ => by nlinarith [ h_contra i hi, show 0 < ( C i |> fun x => x.ofLp 1 ) from by have := hS i; exact this.2.1, mul_div_cancel₀ ( 8 * ( C i |> fun x => x.ofLp 1 ) * t - 2 ) ( by linarith [ h_contra i hi, show 0 < ( C i |> fun x => x.ofLp 1 ) from by have := hS i; exact this.2.1 ] : ( 8 * ( C i |> fun x => x.ofLp 1 ) ) ≠ 0 ), mul_pos hδ.1 ( show 0 < ( C i |> fun x => x.ofLp 1 ) from by have := hS i; exact this.2.1 ) ] ⟩;
        · have hδ_exists : Filter.Tendsto (fun δ => (C i).ofLp 0 + 4 * (t - δ) ^ 2 * (C i).ofLp 1 - 2 * (t - δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((C i).ofLp 0 + 4 * t ^ 2 * (C i).ofLp 1 - 2 * t)) := by
            exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
          have := Metric.tendsto_nhdsWithin_nhds.mp hδ_exists ( m - ( ( C i |> fun x => x.ofLp 0 ) + 4 * t ^ 2 * ( C i |> fun x => x.ofLp 1 ) - 2 * t ) ) ( sub_pos.mpr <| lt_of_le_of_ne ( hsup i ) hi );
          exact ⟨ this.choose, this.choose_spec.1, fun δ hδ => by linarith [ abs_lt.mp ( this.choose_spec.2 hδ.1 ( by simpa [ abs_of_pos hδ.1 ] using hδ.2 ) ) ] ⟩;
      choose δ hδ_pos hδ using hδ_exists;
      obtain ⟨δ_min, hδ_min_pos, hδ_min⟩ : ∃ δ_min > 0, ∀ i, δ_min ≤ δ i := by
        cases n <;> [ tauto; exact ⟨ Finset.min' ( Finset.univ.image δ ) ⟨ _, Finset.mem_image_of_mem δ ( Finset.mem_univ 0 ) ⟩, by have := Finset.min'_mem ( Finset.univ.image δ ) ⟨ _, Finset.mem_image_of_mem δ ( Finset.mem_univ 0 ) ⟩ ; aesop, fun i => Finset.min'_le _ _ <| Finset.mem_image_of_mem δ <| Finset.mem_univ i ⟩ ];
      exact ⟨ Min.min δ_min ( t - 1 ) / 2, by linarith [ lt_min hδ_min_pos ( sub_pos.mpr ht1 ) ], by linarith [ min_le_left δ_min ( t - 1 ), min_le_right δ_min ( t - 1 ) ], fun i => hδ i _ ⟨ by linarith [ lt_min hδ_min_pos ( sub_pos.mpr ht1 ) ], by linarith [ min_le_left δ_min ( t - 1 ), min_le_right δ_min ( t - 1 ), hδ_min i ] ⟩ ⟩;
    exact absurd ( hglob ( t - δ ) ( by linarith ) ) ( by rintro ⟨ i, hi ⟩ ; linarith [ hδ.2 i ] );
  · contrapose! hglob;
    -- Choose $s = t + \delta$ for some small $\delta > 0$.
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ i : ZMod n, (C i).ofLp 0 + 4 * (t + δ) ^ 2 * (C i).ofLp 1 - 2 * (t + δ) < m := by
      have h_cont : ∀ i : ZMod n, ∃ δ_i > 0, ∀ δ, 0 < δ ∧ δ < δ_i → (C i).ofLp 0 + 4 * (t + δ) ^ 2 * (C i).ofLp 1 - 2 * (t + δ) < m := by
        intro i
        by_cases h_eq : (C i).ofLp 0 + 4 * t ^ 2 * (C i).ofLp 1 - 2 * t = m;
        · exact ⟨ ( 2 - 8 * ( C i |> fun x => x.ofLp 1 ) * t ) / ( 8 * ( C i |> fun x => x.ofLp 1 ) ), div_pos ( by linarith [ hglob i h_eq ] ) ( mul_pos ( by norm_num ) ( by linarith [ hS i |>.2.1 ] ) ), fun δ hδ => by nlinarith [ hglob i h_eq, hδ.1, hδ.2, mul_div_cancel₀ ( 2 - 8 * ( C i |> fun x => x.ofLp 1 ) * t ) ( by linarith [ hS i |>.2.1 ] : ( 8 * ( C i |> fun x => x.ofLp 1 ) ) ≠ 0 ), mul_pos hδ.1 ( by linarith [ hS i |>.2.1 ] : 0 < ( C i |> fun x => x.ofLp 1 ) ) ] ⟩;
        · have h_cont : Filter.Tendsto (fun δ => (C i).ofLp 0 + 4 * (t + δ) ^ 2 * (C i).ofLp 1 - 2 * (t + δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((C i).ofLp 0 + 4 * t ^ 2 * (C i).ofLp 1 - 2 * t)) := by
            exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
          have := Metric.tendsto_nhdsWithin_nhds.mp h_cont ( m - ( ( C i |> fun x => x.ofLp 0 ) + 4 * t ^ 2 * ( C i |> fun x => x.ofLp 1 ) - 2 * t ) ) ( sub_pos.mpr <| lt_of_le_of_ne ( hsup i ) h_eq );
          exact ⟨ this.choose, this.choose_spec.1, fun δ hδ => by linarith [ abs_lt.mp ( this.choose_spec.2 hδ.1 ( by simpa [ abs_of_pos hδ.1 ] using hδ.2 ) ) ] ⟩;
      choose δ hδ_pos hδ using h_cont;
      cases n <;> norm_num at *;
      exact ⟨ Finset.min' ( Finset.univ.image δ ) ⟨ _, Finset.mem_image_of_mem δ ( Finset.mem_univ 0 ) ⟩ / 2, half_pos ( Finset.min'_mem ( Finset.univ.image δ ) ⟨ _, Finset.mem_image_of_mem δ ( Finset.mem_univ 0 ) ⟩ |> fun x => by aesop ), fun i => hδ i _ ( half_pos ( Finset.min'_mem ( Finset.univ.image δ ) ⟨ _, Finset.mem_image_of_mem δ ( Finset.mem_univ 0 ) ⟩ |> fun x => by aesop ) ) ( by linarith [ Finset.min'_le _ _ ( Finset.mem_image_of_mem δ ( Finset.mem_univ i ) ), hδ_pos i ] ) ⟩;
    exact ⟨ t + δ, by linarith, hδ ⟩
/-- **Analytic core of Case B.**  Combines `caseB_min_point` and `caseB_contacts`:
the support function attains a positive minimum at some `t > 1`, where two vertices
attain the maximum straddling the tangency height `1/(4t)`. -/
theorem caseB_minimizer
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (hn : 3 ≤ n)
    (hS : ∀ i : ZMod n, inS (C i))
    (hB : ∀ t : ℝ, 1 ≤ t → ∃ i : ZMod n, 2 * t < C i 0 + 4 * t ^ 2 * C i 1) :
    ∃ (t m : ℝ), 1 < t ∧ 0 < m ∧
      (∀ i : ZMod n, C i 0 + 4 * t ^ 2 * C i 1 - 2 * t ≤ m) ∧
      (∃ iR : ZMod n, C iR 0 + 4 * t ^ 2 * C iR 1 - 2 * t = m ∧ 8 * C iR 1 * t ≤ 2) ∧
      (∃ iL : ZMod n, C iL 0 + 4 * t ^ 2 * C iL 1 - 2 * t = m ∧ 2 ≤ 8 * C iL 1 * t) := by
  obtain ⟨t, m, ht1, hm, hsup, hglob⟩ := caseB_min_point n C hn hS hB
  obtain ⟨hR, hL⟩ := caseB_contacts n C hn hS t m ht1 hsup hglob
  exact ⟨t, m, ht1, hm, hsup, hR, hL⟩
/-
Consecutive edges of a counter-clockwise convex polygon turn left.
-/
theorem turn_left
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2))
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i)) :
    ∀ i : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C (i + 1 + 1) - C (i + 1)) := by
  intro i;
  -- Apply `hconv` with `j = i + 1 + 1`.
  specialize hconv i (i + 1 + 1);
  unfold cross at *; norm_num at *; linarith;
/-- **Chord-side / convex position.**  For a counter-clockwise convex polygon
(`hconv`), three vertices in cyclic order `a`, `a+s`, `a+s+t` (with `s, t ≥ 1` and
`s + t < n`) form a counter-clockwise triangle: the middle vertex `a+s` lies weakly to
the right of the directed chord `a → a+s+t`. -/
theorem chord_side
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2))
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (a : ZMod n) (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hst : s + t < n) :
    cross (C (a + ((s + t : ℕ) : ZMod n)) - C a) (C (a + (s : ZMod n)) - C a) ≤ 0 := by
  haveI : NeZero n := ⟨by omega⟩
  set g : ℕ → EuclideanSpace ℝ (Fin 2) := fun k => C (a + (k : ZMod n)) - C a with hg
  have hcastn : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have h0 : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
      rw [← Nat.cast_one (R := ZMod n), ← Nat.cast_add, Nat.sub_add_cancel (by omega)]
      exact ZMod.natCast_self n
    exact eq_neg_of_add_eq_zero_left h0
  -- All chords `g k = C (a+k) - C a` are weakly left of the first edge `g 1 = e_a` …
  have hA : ∀ k : ℕ, 0 ≤ cross (g 1) (g k) := by
    intro k; have := hconv a (a + (k : ZMod n)); simpa [hg, Nat.cast_one] using this
  -- … consecutive fan triangles at `a` are counter-clockwise …
  have hB : ∀ k : ℕ, 0 ≤ cross (g k) (g (k + 1)) := by
    intro k
    have h := hconv (a + (k : ZMod n)) a
    have hcast : ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 := by push_cast; ring
    have he : cross (g k) (g (k + 1))
        = cross (C (a + (k : ZMod n) + 1) - C (a + (k : ZMod n))) (C a - C (a + (k : ZMod n))) := by
      simp only [hg, hcast]; unfold cross; simp [PiLp.sub_apply]; ring_nf
    rw [he]; have h2 : a + (k : ZMod n) + 1 = (a + (k : ZMod n)) + 1 := by ring
    rw [h2]; exact h
  -- … and all `g k` are weakly left of the last edge `g (n-1) = -e_{a-1}`.
  have hC : ∀ k : ℕ, 0 ≤ cross (g k) (g (n - 1)) := by
    intro k
    have h := hconv (a - 1) (a + (k : ZMod n))
    have heq : a - 1 + 1 = a := by ring
    rw [heq] at h
    have he : cross (g k) (g (n - 1))
        = cross (C a - C (a - 1)) (C (a + (k : ZMod n)) - C (a - 1)) := by
      simp only [hg, hcastn]
      have h3 : a + (-1 : ZMod n) = a - 1 := by ring
      rw [h3]; unfold cross; simp [PiLp.sub_apply]; ring
    rw [he]; exact h
  -- Angle sorting: `0 ≤ cross (g s) (g m)` for `s ≤ m ≤ s+t`, by induction on `m`.
  have key : ∀ m : ℕ, s ≤ m → m ≤ s + t → 0 ≤ cross (g s) (g m) := by
    intro m hsm hmst
    induction m, hsm using Nat.le_induction with
    | base => have h0 : cross (g s) (g s) = 0 := by unfold cross; ring
              rw [h0]
    | succ m hm ih =>
      have ihv := ih (by omega)
      -- two Grassmann–Plücker relations (references `g 1` and `g (n-1)`)
      have P1 : cross (g 1) (g m) * cross (g s) (g (m + 1))
          = cross (g 1) (g (m + 1)) * cross (g s) (g m)
            + cross (g 1) (g s) * cross (g m) (g (m + 1)) := by unfold cross; ring
      have P2 : cross (g m) (g (n - 1)) * cross (g s) (g (m + 1))
          = cross (g (m + 1)) (g (n - 1)) * cross (g s) (g m)
            + cross (g s) (g (n - 1)) * cross (g m) (g (m + 1)) := by unfold cross; ring
      have hsum : (cross (g 1) (g m) + cross (g m) (g (n - 1))) * cross (g s) (g (m + 1))
          = (cross (g 1) (g (m + 1)) + cross (g (m + 1)) (g (n - 1))) * cross (g s) (g m)
            + (cross (g 1) (g s) + cross (g s) (g (n - 1))) * cross (g m) (g (m + 1)) := by
        nlinarith [P1, P2]
      have hP : 0 ≤ cross (g 1) (g m) + cross (g m) (g (n - 1)) := by
        have := hA m; have := hC m; linarith
      have hRHS : 0 ≤ (cross (g 1) (g (m + 1)) + cross (g (m + 1)) (g (n - 1))) * cross (g s) (g m)
            + (cross (g 1) (g s) + cross (g s) (g (n - 1))) * cross (g m) (g (m + 1)) := by
        have h1 := hA (m + 1); have h2 := hC (m + 1); have h3 := hA s; have h4 := hC s
        have h5 := hB m
        have hc1 : 0 ≤ cross (g 1) (g (m + 1)) + cross (g (m + 1)) (g (n - 1)) := by linarith
        have hc2 : 0 ≤ cross (g 1) (g s) + cross (g s) (g (n - 1)) := by linarith
        have := mul_nonneg hc1 ihv; have := mul_nonneg hc2 h5; linarith
      rcases lt_or_eq_of_le hP with hPpos | hPzero
      · -- generic case: the combined coefficient is positive, so divide
        have hX : 0 ≤ (cross (g 1) (g m) + cross (g m) (g (n - 1))) * cross (g s) (g (m + 1)) := by
          rw [hsum]; exact hRHS
        by_contra hcon; push_neg at hcon
        nlinarith [mul_pos hPpos (neg_pos.mpr hcon)]
      · -- degenerate case `cross (g 1) (g m) = cross (g m) (g (n-1)) = 0`
        -- (the chord `g m` would be parallel to both bounding edges).  Under strict
        -- convexity (`hsconv`) this is impossible: `cross (g m) (g (n-1)) > 0`,
        -- contradicting `hPzero`.
        exfalso
        have hm_lb : 1 ≤ m := le_trans hs hm
        have hm_ub : m ≤ n - 2 := by omega
        -- `(m : ZMod n) ≠ 0` and `≠ -1` since `1 ≤ m ≤ n-2`.
        have hne0 : (m : ZMod n) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
        have hnen1 : (m : ZMod n) ≠ -1 := by
          rw [Ne, ← hcastn, ZMod.natCast_eq_natCast_iff]
          intro h
          have h' : m % n = (n - 1) % n := h
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
          omega
        have hne_a : a + (m : ZMod n) ≠ a - 1 := by
          intro hcon; apply hnen1
          have h2 : a + (m : ZMod n) = a + (-1) := by rw [hcon]; ring
          exact add_left_cancel h2
        have hne_a2 : a + (m : ZMod n) ≠ a := by
          intro hcon; apply hne0
          have h2 : a + (m : ZMod n) = a + 0 := by rw [hcon]; ring
          exact add_left_cancel h2
        have hpos : 0 < cross (g m) (g (n - 1)) := by
          have h := hsconv (a - 1) (a + (m : ZMod n)) hne_a
            (by rw [show a - 1 + 1 = a from by ring]; exact hne_a2)
          rw [show a - 1 + 1 = a from by ring] at h
          have he : cross (g m) (g (n - 1))
              = cross (C a - C (a - 1)) (C (a + (m : ZMod n)) - C (a - 1)) := by
            simp only [hg, hcastn]
            have h3 : a + (-1 : ZMod n) = a - 1 := by ring
            rw [h3]; unfold cross; simp [PiLp.sub_apply]; ring
          rw [he]; exact h
        have h1 : 0 ≤ cross (g 1) (g m) := hA m
        linarith [hPzero]
  -- transfer back to the stated goal
  have hfin := key (s + t) (by omega) (by omega)
  have hgoal : cross (C (a + ((s + t : ℕ) : ZMod n)) - C a) (C (a + (s : ZMod n)) - C a)
       = - cross (g s) (g (s + t)) := by
    simp only [hg]; unfold cross; simp [PiLp.sub_apply]; ring
  rw [hgoal]; linarith
/-
**Contiguity of the maximizing face.**  For a counter-clockwise convex polygon
(`hconv`) and the linear functional `ℓ z = z 0 + c · z 1`, the vertices attaining the
maximum value `d` form a single edge.  If the maximizers split (via `hstrip`) into a
`≤ lo` group (witnessed by `L`) and a `≥ hi` group (witnessed by `R`) with `lo < hi`,
then some side `(k, k+1)` joins the two groups.
-/
theorem caseB_adjacent
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (hn : 3 ≤ n)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (c d lo hi : ℝ)
    (hsupp : ∀ j : ZMod n, C j 0 + c * C j 1 ≤ d)
    (hstrip : ∀ j : ZMod n, C j 0 + c * C j 1 = d → C j 0 ≤ lo ∨ hi ≤ C j 0)
    (hlohi : lo < hi)
    (hR : ∃ R : ZMod n, C R 0 + c * C R 1 = d ∧ hi ≤ C R 0)
    (hL : ∃ L : ZMod n, C L 0 + c * C L 1 = d ∧ C L 0 ≤ lo) :
    ∃ k : ZMod n, (hi ≤ C k 0 ∧ C (k + 1) 0 ≤ lo) ∨ (hi ≤ C (k + 1) 0 ∧ C k 0 ≤ lo) := by
  by_contra h_contra;
  -- Set `jL` and `jR` as described.
  obtain ⟨R, hR₁, hR₂⟩ := hR
  obtain ⟨L, hL₁, hL₂⟩ := hL
  haveI : NeZero n := ⟨by omega⟩
  set jL := (L - R).val
  have hjL_pos : 1 ≤ jL := by
    by_cases hL_eq_R : L = R;
    · grind;
    · exact Nat.pos_of_ne_zero fun h => hL_eq_R <| sub_eq_zero.mp <| ZMod.val_injective n <| by aesop;
  have hjL_lt_n : jL < n := by
    exact ZMod.val_lt _
  set jR := (R - L).val
  have hjR_pos : 1 ≤ jR := by
    simp +zetaDelta at *;
    by_cases hRL : R = L;
    · grind;
    · exact Nat.pos_of_ne_zero ( by simp +decide [ sub_eq_zero, hRL ] )
  have hjR_lt_n : jR < n := by
    exact ZMod.val_lt _
  have hj_sum : jL + jR = n := by
    have h_sum : (L - R).val + (R - L).val ≡ 0 [MOD n] := by
      simp +decide [ ← ZMod.natCast_eq_natCast_iff ];
    obtain ⟨ k, hk ⟩ := Nat.modEq_zero_iff_dvd.mp h_sum;
    nlinarith [ show k = 1 by nlinarith ];
  -- Let `i` be the smallest index in `[1, jL]` such that `C (R + i).0 < hi`.
  obtain ⟨i, hi_pos, hi_lt⟩ : ∃ i : ℕ, 1 ≤ i ∧ i ≤ jL ∧ (C (R + i)).ofLp 0 < hi ∧ ∀ j : ℕ, 1 ≤ j → j < i → (C (R + j)).ofLp 0 ≥ hi := by
    have hi_exists : ∃ i : ℕ, 1 ≤ i ∧ i ≤ jL ∧ (C (R + i)).ofLp 0 < hi := by
      use jL;
      simp +zetaDelta at *;
      exact ⟨ hjL_pos, by linarith ⟩;
    exact ⟨ Nat.find hi_exists, Nat.find_spec hi_exists |>.1, Nat.find_spec hi_exists |>.2.1, Nat.find_spec hi_exists |>.2.2, fun j hj₁ hj₂ => not_lt.1 fun hj₃ => Nat.find_min hi_exists hj₂ ⟨ hj₁, by linarith [ Nat.find_spec hi_exists |>.2.1 ], hj₃ ⟩ ⟩;
  -- Let `x := R + i`.
  set x := R + i
  have hx_lt_hi : (C x).ofLp 0 < hi := by
    linarith
  have hx_ge_lo : lo < (C x).ofLp 0 := by
    simp +zetaDelta at *;
    induction hi_pos <;> simp_all +decide [ ← add_assoc ]
  have hphi_x_neg : (C x).ofLp 0 + c * (C x).ofLp 1 - d < 0 := by
    exact lt_of_le_of_ne ( sub_nonpos_of_le ( hsupp x ) ) fun h => by cases hstrip x ( by linarith ) <;> linarith;
  -- Let `i'` be the smallest index in `[1, jR]` such that `C (L + i').0 > lo`.
  obtain ⟨i', hi'_pos, hi'_lt⟩ : ∃ i' : ℕ, 1 ≤ i' ∧ i' ≤ jR ∧ (C (L + i')).ofLp 0 > lo ∧ ∀ j : ℕ, 1 ≤ j → j < i' → (C (L + j)).ofLp 0 ≤ lo := by
    have hi'_exists : ∃ i' : ℕ, 1 ≤ i' ∧ i' ≤ jR ∧ (C (L + i')).ofLp 0 > lo := by
      use jR;
      simp +zetaDelta at *;
      exact ⟨ hjR_pos, by linarith ⟩;
    exact ⟨ Nat.find hi'_exists, Nat.find_spec hi'_exists |>.1, Nat.find_spec hi'_exists |>.2.1, Nat.find_spec hi'_exists |>.2.2, fun j hj₁ hj₂ => not_lt.1 fun hj₃ => Nat.find_min hi'_exists hj₂ ⟨ hj₁, by linarith [ Nat.find_spec hi'_exists |>.2.1 ], hj₃ ⟩ ⟩;
  -- Let `y := L + i'`.
  set y := L + i'
  have hy_gt_lo : (C y).ofLp 0 > lo := by
    linarith
  have hy_le_hi : (C y).ofLp 0 < hi := by
    contrapose! h_contra;
    use y - 1;
    rcases i' with ( _ | i' ) <;> simp_all +decide;
    simp +zetaDelta at *;
    by_cases hi'_pos : 1 ≤ i' <;> simp_all +decide [ add_sub_assoc ]
  have hphi_y_neg : (C y).ofLp 0 + c * (C y).ofLp 1 - d < 0 := by
    grind +qlia;
  -- Apply `chord_side` to get the inequalities for `gx` and `gy`.
  have hgxy : cross (C L - C R) (C x - C R) ≤ 0 ∧ cross (C y - C R) (C L - C R) ≤ 0 := by
    apply And.intro;
    · convert chord_side n C hconv hsconv R i ( jL - i ) hi_pos ( Nat.sub_pos_of_lt ( lt_of_le_of_ne hi_lt.1 ( by aesop_cat ) ) ) ( by omega ) using 1 ; norm_num [ x ];
      simp +zetaDelta at *;
      rw [ Nat.cast_sub hi_lt.1 ] ; norm_num [ add_assoc, ZMod.natCast_zmod_val ];
    · convert chord_side n C hconv hsconv R ( jL ) i' hjL_pos hi'_pos _ using 1;
      · simp +zetaDelta at *;
        ring_nf;
      · by_cases hi'_eq_jR : i' = jR;
        · simp +zetaDelta at *;
          simp_all +decide;
        · omega;
  unfold cross at *;
  norm_num [ EuclideanSpace.norm_eq ] at *;
  cases le_or_gt 0 c <;> nlinarith
/-
**Support line existence, secant (Case B) case.**  When no common tangent line of
the hyperbola lies above all vertices (i.e. for every contact `t ≥ 1` some vertex is
strictly above the tangent `x + 4t² y = 2t`), the polygon must poke above the
hyperbola, and the line through the side that crosses the hyperbola is the required
secant support line.  Its two hyperbola contacts `x₁ ≤ x₂` lie on that side, so
`x₁, x₂ ≥ 1` and `|x₁ - x₂| ≤ a`.
-/
theorem support_line_caseB
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hn : 3 ≤ n) (ha : 0 < a)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hca : ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i))
    (hB : ∀ t : ℝ, 1 ≤ t → ∃ i : ZMod n, 2 * t < C i 0 + 4 * t ^ 2 * C i 1) :
    ∃ x1 x2 : ℝ, 1 ≤ x1 ∧ 1 ≤ x2 ∧ |x1 - x2| ≤ a ∧
      ∀ i : ZMod n, C i 0 + 4 * x1 * x2 * C i 1 ≤ x1 + x2 := by
  -- Let's choose the minimizer data from `caseB_minimizer n C hn hS hB`.
  obtain ⟨t, m, ht1, hm0, hsup, iR, hiR, hL, hiL⟩ := caseB_minimizer n C hn hS hB;
  obtain ⟨k, hk⟩ := caseB_adjacent n C hn hconv hsconv (4 * t ^ 2) (2 * t + m) ((2 * t + m - Real.sqrt ((2 * t + m) ^ 2 - 4 * t ^ 2)) / 2) ((2 * t + m + Real.sqrt ((2 * t + m) ^ 2 - 4 * t ^ 2)) / 2) (fun j => by
    linarith [ hsup j ]) (fun j hj => by
    contrapose! hj;
    have := hS j;
    obtain ⟨ h₁, h₂, h₃ ⟩ := this;
    nlinarith [ mul_pos hm0 h₂, mul_pos hm0 ( sub_pos.mpr ht1 ), mul_pos h₂ ( sub_pos.mpr ht1 ), Real.sqrt_nonneg ( ( 2 * t + m ) ^ 2 - 4 * t ^ 2 ), Real.mul_self_sqrt ( show 0 <= ( 2 * t + m ) ^ 2 - 4 * t ^ 2 by nlinarith ) ]) (by
  linarith [ Real.sqrt_pos.mpr ( show 0 < ( 2 * t + m ) ^ 2 - 4 * t ^ 2 by nlinarith ) ]) (by
  obtain ⟨ R, hR₁, hR₂ ⟩ := iR;
  refine' ⟨ R, by linarith, _ ⟩;
  have h_sqrt : Real.sqrt ((2 * t + m) ^ 2 - 4 * t ^ 2) ≤ 2 * (C R).ofLp 0 - (2 * t + m) := by
    rw [ Real.sqrt_le_left ] <;> nlinarith [ hS R |>.1, hS R |>.2.1, hS R |>.2.2, mul_pos ( sub_pos.mpr ht1 ) ( sub_pos.mpr hm0 ) ];
  linarith) (by
  refine' ⟨ hiR, _, _ ⟩ <;> try linarith;
  rw [ le_div_iff₀ ] <;> norm_num;
  rw [ le_sub_comm, Real.sqrt_le_left ] <;> nlinarith [ sq_nonneg ( ( C hiR ).ofLp 0 - 1 ), hS hiR |>.1, hS hiR |>.2.1, hS hiR |>.2.2 ]);
  refine' ⟨ ( 2 * t + m - Real.sqrt ( ( 2 * t + m ) ^ 2 - 4 * t ^ 2 ) ) / 2, ( 2 * t + m + Real.sqrt ( ( 2 * t + m ) ^ 2 - 4 * t ^ 2 ) ) / 2, _, _, _, _ ⟩ <;> norm_num at *;
  · cases hk <;> nlinarith [ hS k, hS ( k + 1 ), ( hS k ) |>.1, ( hS ( k + 1 ) ) |>.1 ];
  · nlinarith [ Real.sqrt_nonneg ( ( 2 * t + m ) ^ 2 - 4 * t ^ 2 ) ];
  · have h_dist : |(C k).ofLp 0 - (C (k + 1)).ofLp 0| ≤ a := by
      have := hca k; rw [ dist_eq_norm ] at this; norm_num [ EuclideanSpace.norm_eq ] at this ⊢; exact (by
      exact this ▸ Real.abs_le_sqrt ( by nlinarith only ));
    cases hk <;> rw [ abs_le ] at * <;> constructor <;> linarith [ Real.sqrt_nonneg ( ( 2 * t + m ) ^ 2 - 4 * t ^ 2 ) ];
  · intro i; convert hsup i using 1 <;> ring_nf;
    rw [ Real.sq_sqrt ] <;> nlinarith
/-- **Support line existence** (geometric core of the area bound).  There is a tangent
or secant line `x + 4 x₁ x₂ y = x₁ + x₂` of the hyperbola `4xy = 1` with all vertices
on its lower side, i.e. `C i 0 + 4 x₁ x₂ · C i 1 ≤ x₁ + x₂` for every vertex.  Its two
hyperbola-contact abscissae `x₁, x₂` are `≥ 1` (case A: a single tangency point
`x₁ = x₂`; case B: the two points where a side of the polygon crosses the hyperbola),
with gap at most the side length `a`.
The proof splits on whether a common tangent above all vertices exists.  Case A is
elementary; the genuine planar-geometric content is in `support_line_caseB`. -/
theorem exists_support_line
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hn : 3 ≤ n) (ha : 0 < a)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hca : ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i)) :
    ∃ x1 x2 : ℝ, 1 ≤ x1 ∧ 1 ≤ x2 ∧ |x1 - x2| ≤ a ∧
      ∀ i : ZMod n, C i 0 + 4 * x1 * x2 * C i 1 ≤ x1 + x2 := by
  by_cases hCaseA : ∃ t : ℝ, 1 ≤ t ∧ ∀ i : ZMod n, C i 0 + 4 * t ^ 2 * C i 1 ≤ 2 * t
  · -- Case A: a common tangent line lies above every vertex; take `x₁ = x₂ = t`.
    obtain ⟨t, ht1, htle⟩ := hCaseA
    refine ⟨t, t, ht1, ht1, ?_, ?_⟩
    · rw [sub_self, abs_zero]; exact ha.le
    · intro i; have h := htle i; nlinarith [h]
  · -- Case B: no common tangent; use the secant through the crossing side.
    push_neg at hCaseA
    exact support_line_caseB n C a hn ha hconv hsconv hca hS hCaseA
/-- The convex hull of the polygon lies in the triangle cut from the coordinate axes
by the support line of `exists_support_line` (`x`-intercept `x₁ + x₂`, `y`-intercept
`(x₁ + x₂)/(4 x₁ x₂)`).  This follows from `exists_support_line` together with
convexity of `tri` (`convexHull_min`). -/
theorem exists_support_triangle
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hn : 3 ≤ n) (ha : 0 < a)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hca : ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i)) :
    ∃ x1 x2 : ℝ, 1 ≤ x1 ∧ 1 ≤ x2 ∧ |x1 - x2| ≤ a ∧
      convexHull ℝ (Set.range C) ⊆ tri (x1 + x2) ((x1 + x2) / (4 * x1 * x2)) := by
  obtain ⟨x1, x2, hx1, hx2, hdist, hline⟩ := exists_support_line n C a hn ha hconv hsconv hca hS
  refine ⟨x1, x2, hx1, hx2, hdist, ?_⟩
  have hp : (0 : ℝ) < x1 + x2 := by linarith
  have h4 : (0 : ℝ) < 4 * x1 * x2 := by positivity
  have hq : (0 : ℝ) < (x1 + x2) / (4 * x1 * x2) := by positivity
  refine convexHull_min ?_ (tri_convex _ _)
  rintro _ ⟨i, rfl⟩
  obtain ⟨hxi1, hyi1, _⟩ := hS i
  refine ⟨by linarith, le_of_lt hyi1, ?_⟩
  have hkey : C i 0 / (x1 + x2) + C i 1 / ((x1 + x2) / (4 * x1 * x2))
      = (C i 0 + 4 * x1 * x2 * C i 1) / (x1 + x2) := by
    rw [div_div_eq_mul_div, ← add_div]
    ring_nf
  rw [hkey, div_le_one hp]
  exact hline i
/-
**Edge `x`-projection bound.**  Each side of the polygon has horizontal extent at
least `√(a² - 1/16)`: both endpoints lie in the strip `0 < y < 1/4` (since
`1 < x` and `4xy < 1` give `y < 1/(4x) < 1/4`), so the vertical extent of a side is
`< 1/4`, and Pythagoras with side length `a` gives the bound.
-/
theorem edge_dx_ge
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (ha : 2 ≤ a)
    (hca : ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i)) (i : ZMod n) :
    Real.sqrt (a ^ 2 - 1 / 16) ≤ |C (i + 1) 0 - C i 0| := by
  rw [ Real.sqrt_le_iff ];
  simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
  have := hca i; rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at this <;> try linarith;
  have := hS i; have := hS ( i + 1 ) ; norm_num [ inS ] at *; nlinarith [ mul_pos ( sub_pos.mpr this.1 ) ( sub_pos.mpr this.2.1 ), mul_pos ( sub_pos.mpr ( hS i |>.1 ) ) ( sub_pos.mpr ( hS i |>.2.1 ) ) ] ;
/-
Reindexing a sum over `ZMod n` as a sum over `range n` starting from any base `R`:
the map `i ↦ R + i` is a bijection `Fin n ≃ ZMod n`.
-/
theorem sum_range_zmod (n : ℕ) [NeZero n] (R : ZMod n) (h : ZMod n → ℝ) :
    ∑ i ∈ Finset.range n, h (R + (i : ZMod n)) = ∑ i : ZMod n, h i := by
  rcases n with ( _ | _ | n ) <;> norm_num [ Finset.sum_range ] at *;
  · exact False.elim <| NeZero.ne 0 rfl;
  · simp +decide [ Fin.eq_zero ];
  · erw [ Finset.sum_equiv ( Equiv.addLeft R ) ] ; aesop;
    simp +decide [ ZMod, Fin.add_def ]
/-
**No interior `x`-peak (algebraic core).**  Four points `r, a, b, c` in
counter-clockwise convex position (here `a, b, c` are three further vertices with the
convex-position cross inequalities `h1`-`h4` relative to the rightmost vertex `r`) cannot
have `b` as a strict local `x`-maximum below `r`: if `a 0 < b 0`, `c 0 < b 0` and
`b 0 ≤ r 0`, the two diagonals `r–b` and `a–c` of the convex quadrilateral `r,a,b,c`
cross, and the `x`-coordinate of the crossing point is simultaneously `≥ b 0` (it lies
on segment `r–b`, both of whose endpoints have `x ≥ b 0`) and `< b 0` (it lies on
segment `a–c`, both of whose endpoints have `x < b 0`) — a contradiction.
-/
theorem no_interior_peak_alg (r a b c : EuclideanSpace ℝ (Fin 2))
    (hab : a 0 < b 0) (hcb : c 0 < b 0) (hbr : b 0 ≤ r 0)
    (h1 : cross (b - r) (a - r) ≤ 0) (h2 : 0 < cross (b - r) (c - r))
    (h3 : cross (c - a) (b - a) ≤ 0) :
    False := by
  contrapose! h1; contrapose! h2; norm_num [ cross ] at *;
  nlinarith
/-
**Cyclic unimodality of the `x`-coordinate (valley form).**  If `R` is a vertex of
maximal `x`-coordinate, then walking by `+1` from `R` the `x`-coordinate first weakly
decreases (down to the minimum) and then weakly increases (back up to the maximum):
there is a split index `k ≤ n` with `x` non-increasing on `[0,k)` and non-decreasing on
`[k,n)`.  This is the convex-position input; were there an interior local `x`-maximum
below `R`, three cyclically ordered vertices around it would violate `chord_side`.
-/
theorem x_valley (n : ℕ) [NeZero n] (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (hn : 3 ≤ n)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (R : ZMod n) (hR : ∀ j : ZMod n, C j 0 ≤ C R 0) :
    ∃ k : ℕ, k ≤ n ∧
      (∀ i : ℕ, i < k → C (R + ((i + 1 : ℕ) : ZMod n)) 0 ≤ C (R + (i : ZMod n)) 0) ∧
      (∀ i : ℕ, k ≤ i → i < n → C (R + (i : ZMod n)) 0 ≤ C (R + ((i + 1 : ℕ) : ZMod n)) 0) := by
  by_contra! h_contra;
  -- Let `k` be the smallest index such that `f(R+((k+1):ℕ)) > f(R+(k:ℕ))`.
  obtain ⟨k, hk⟩ : ∃ k ≤ n, (∀ i < k, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0) ∧ (k = n ∨ (C (R + (k + 1 : ℕ))).ofLp 0 > (C (R + (k : ℕ))).ofLp 0) := by
    have h_exists_k : ∃ k ≤ n, (∀ i < k, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0) ∧ (k = n ∨ ¬(∀ i < k + 1, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0)) := by
      have h_exists_k : ∃ k ≤ n, ¬(∀ i < k + 1, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0) := by
        exact ⟨ n, le_rfl, fun h => by obtain ⟨ i, hi₁, hi₂, hi₃ ⟩ := h_contra n le_rfl ( fun i hi => h i ( by linarith ) ) ; linarith [ h i ( by linarith ) ] ⟩;
      obtain ⟨k, hk⟩ : ∃ k ≤ n, ¬(∀ i < k + 1, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0) ∧ ∀ j < k, (∀ i < j + 1, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0) := by
        exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2, fun j hj => by exact Classical.not_not.1 fun h => Nat.find_min h_exists_k hj ⟨ Nat.le_trans ( Nat.le_of_lt hj ) ( Nat.find_spec h_exists_k |>.1 ), h ⟩ ⟩;
      exact ⟨ k, hk.1, fun i hi => hk.2.2 i hi i ( Nat.lt_succ_self _ ), Or.inr hk.2.1 ⟩;
    grind;
  obtain ⟨j, hj⟩ : ∃ j, k ≤ j ∧ j < n ∧ (C (R + (j + 1 : ℕ))).ofLp 0 < (C (R + (j : ℕ))).ofLp 0 ∧ ∀ i, k ≤ i → i < j → (C (R + (i + 1 : ℕ))).ofLp 0 ≥ (C (R + (i : ℕ))).ofLp 0 := by
    have := Nat.find_spec ( h_contra k hk.1 hk.2.1 );
    exact ⟨ _, this.1, this.2.1, this.2.2, fun i hi₁ hi₂ => not_lt.1 fun hi₃ => Nat.find_min ( h_contra k hk.1 hk.2.1 ) hi₂ ⟨ hi₁, by linarith, hi₃ ⟩ ⟩;
  -- By `hR`, we have `f(R+k) < f(R+j)`.
  have h_lt : (C (R + (k : ℕ))).ofLp 0 < (C (R + (j : ℕ))).ofLp 0 := by
    have h_lt : ∀ i, k + 1 ≤ i → i ≤ j → (C (R + (i : ℕ))).ofLp 0 ≥ (C (R + (k + 1 : ℕ))).ofLp 0 := by
      intro i hi₁ hi₂; induction hi₁ <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
      grind;
    grind;
  have h1 : cross (C (R + (j : ℕ)) - C R) (C (R + (k : ℕ)) - C R) ≤ 0 := by
    convert chord_side n C hconv _ R k ( j - k ) _ _ _ using 1;
    · simp +decide [ hj.1 ];
    · exact hsconv;
    · rcases k with ( _ | k ) <;> norm_num at *;
      exact absurd ( hk.resolve_left ( by linarith ) ) ( not_lt_of_ge ( hR _ ) );
    · exact Nat.sub_pos_of_lt ( lt_of_le_of_ne hj.1 ( by rintro rfl; linarith ) );
    · omega
  have h2 : 0 < cross (C (R + (j : ℕ)) - C R) (C (R + (j + 1 : ℕ)) - C R) := by
    convert hsconv ( R + j ) R _ _ using 1 <;> norm_num [ add_assoc ];
    · unfold cross; simp +decide [ sub_eq_iff_eq_add ] ; ring;
    · intro h; simp_all +decide [ ZMod.natCast_eq_zero_iff ] ;
      linarith [ Nat.le_of_dvd ( by linarith [ show k > 0 from Nat.pos_of_ne_zero fun h => by subst h; specialize h_contra 0; aesop ] ) h ];
    · grind +qlia
  have h3 : cross (C (R + (j + 1 : ℕ)) - C (R + (k : ℕ))) (C (R + (j : ℕ)) - C (R + (k : ℕ))) ≤ 0 := by
    convert chord_side n C hconv hsconv ( R + k ) ( j - k ) 1 _ _ _ using 1 <;> norm_num [ hj.1, hj.2.1 ];
    · ring_nf;
    · exact Nat.sub_pos_of_lt ( lt_of_le_of_ne hj.1 ( by rintro rfl; linarith ) );
    · by_cases h_eq : j = n - 1;
      · rcases n with ( _ | _ | n ) <;> simp_all +decide;
        linarith [ hR ( R + ( n + 1 ) ) ];
      · omega
  exact no_interior_peak_alg (C R) (C (R + (k : ℕ))) (C (R + (j : ℕ))) (C (R + (j + 1 : ℕ))) h_lt hj.2.2.1 (hR (R + (j : ℕ))) h1 h2 h3
/-
**Unimodality / total `x`-variation of a convex polygon.**  For a (strictly)
convex counter-clockwise polygon the sum of the absolute horizontal extents of the
sides equals twice the horizontal width `xmax - xmin`; in particular it is `≤` that.
Going around the polygon, the `x`-coordinate rises monotonically from the leftmost to
the rightmost vertex and then falls back monotonically, so each of the two arcs
contributes exactly `xmax - xmin` to the total variation.
-/
theorem two_width_ge_sum
    (n : ℕ) [NeZero n] (C : ZMod n → EuclideanSpace ℝ (Fin 2))
    (hn : 3 ≤ n)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hne : (Finset.univ : Finset (ZMod n)).Nonempty) :
    ∑ i : ZMod n, |C (i + 1) 0 - C i 0|
      ≤ 2 * (Finset.univ.sup' hne (fun i => C i 0) - Finset.univ.inf' hne (fun i => C i 0)) := by
  obtain ⟨R, hR⟩ : ∃ R : ZMod n, ∀ j : ZMod n, (C j).ofLp 0 ≤ (C R).ofLp 0 := by
    simpa using Finset.exists_max_image Finset.univ ( fun j => ( C j |> fun x => x.ofLp 0 ) ) hne;
  obtain ⟨ k, hk ⟩ := x_valley n C hn hconv hsconv R hR;
  -- By `sum_range_zmod`, we can reindex the sum to start from `R`.
  have h_sum_reindex : ∑ i : ZMod n, abs ((C (i + 1)).ofLp 0 - (C i).ofLp 0) = ∑ i ∈ Finset.range n, abs ((C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0 - (C (R + (i : ℕ) : ZMod n)).ofLp 0) := by
    rw [ ← sum_range_zmod ];
    norm_num [ add_assoc ];
    convert rfl;
  -- Split the sum into two parts: one over the range $k$ and one over the range $n-k$.
  have h_split_sum : ∑ i ∈ Finset.range n, abs ((C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0 - (C (R + (i : ℕ) : ZMod n)).ofLp 0) = (∑ i ∈ Finset.range k, (C (R + (i : ℕ) : ZMod n)).ofLp 0 - ∑ i ∈ Finset.range k, (C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0) + (∑ i ∈ Finset.Ico k n, (C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0 - ∑ i ∈ Finset.Ico k n, (C (R + (i : ℕ) : ZMod n)).ofLp 0) := by
    rw [ ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_Ico_consecutive _ _ hk.1 ];
    · rw [ ← Finset.sum_range_add_sum_Ico _ hk.1 ];
      exact congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun i hi => by rw [ abs_sub_comm, abs_of_nonneg ] ; linarith [ hk.2.1 i ( Finset.mem_range.mp hi ) ] ) ( by rw [ Finset.sum_congr rfl fun i hi => abs_of_nonneg ( sub_nonneg.mpr ( hk.2.2 i ( Finset.mem_Ico.mp hi |>.1 ) ( Finset.mem_Ico.mp hi |>.2 ) ) ) ] ; norm_num );
    · linarith;
  -- Apply the telescoping sum property to each part.
  have h_telescope : (∑ i ∈ Finset.range k, (C (R + (i : ℕ) : ZMod n)).ofLp 0 - ∑ i ∈ Finset.range k, (C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0) = (C R).ofLp 0 - (C (R + k : ZMod n)).ofLp 0 ∧ (∑ i ∈ Finset.Ico k n, (C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0 - ∑ i ∈ Finset.Ico k n, (C (R + (i : ℕ) : ZMod n)).ofLp 0) = (C (R + n : ZMod n)).ofLp 0 - (C (R + k : ZMod n)).ofLp 0 := by
    constructor;
    · convert Finset.sum_range_sub' ( fun i => ( C ( R + i ) ).ofLp 0 ) k using 1 ; norm_num;
      norm_num;
    · rw [ Finset.sum_Ico_eq_sub _ hk.1, Finset.sum_Ico_eq_sub _ hk.1 ];
      have := Finset.sum_range_sub ( fun i => ( C ( R + i ) |> fun x => x.ofLp 0 ) ) n; have := Finset.sum_range_sub ( fun i => ( C ( R + i ) |> fun x => x.ofLp 0 ) ) k; norm_num [ add_assoc, Finset.sum_range_succ ] at *; linarith;
  simp_all +decide [ Finset.inf'_eq_csInf_image ];
  linarith [ show ( Finset.univ.sup' hne fun x => ( C x |> fun y => y.ofLp 0 ) ) ≥ ( C R |> fun y => y.ofLp 0 ) from Finset.le_sup' ( fun x => ( C x |> fun y => y.ofLp 0 ) ) ( Finset.mem_univ R ), show ( sInf ( Set.range fun x => ( C x |> fun y => y.ofLp 0 ) ) ) ≤ ( C ( R + k ) |> fun y => y.ofLp 0 ) from csInf_le ( Set.finite_range _ |> Set.Finite.bddBelow ) ( Set.mem_range_self _ ) ]
/-
**Large-side case.**  When the common side length is at least `2`, the area is
strictly less than `1`.  Suppose not, i.e. `1 ≤ area`.  The support triangle
(`exists_support_triangle`) gives contacts `x₁, x₂ ≥ 1` with `|x₁ - x₂| ≤ a` and
`area ≤ 1/2 + (x₁-x₂)²/(8x₁x₂)`; with `1 ≤ area` this forces `4x₁x₂ ≤ (x₁-x₂)² ≤ a²`,
hence `(x₁+x₂)² = (x₁-x₂)² + 4x₁x₂ ≤ 2a²`.  Every vertex has `x ≤ x₁+x₂` (it lies
below the support line), so the width is `xmax - xmin ≤ x₁+x₂ ≤ √2·a`.  On the other
hand, by `two_width_ge_sum` and `edge_dx_ge`,
`n·√(a²-1/16) ≤ ∑ |Δxᵢ| ≤ 2(xmax-xmin) ≤ 2√2·a`, so `3√(a²-1/16) ≤ 2√2·a`, i.e.
`a² ≤ 9/16`, contradicting `a ≥ 2`.
-/
theorem area_lt_one_of_large
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hn : 3 ≤ n) (ha : 2 ≤ a)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hca : ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i)) :
    volume (convexHull ℝ (Set.range C)) < 1 := by
  contrapose! hS;
  -- By contradiction, assume all vertices lie in `S`.
  by_contra h_all_in_S
  push_neg at h_all_in_S;
  haveI : NeZero n := ⟨by omega⟩
  have hne : (Finset.univ : Finset (ZMod n)).Nonempty := Finset.univ_nonempty
  obtain ⟨x1, x2, hx1, hx2, hdist, hsub⟩ := exists_support_triangle n C a hn (by linarith) hconv hsconv hca h_all_in_S
  set p := x1 + x2
  set q := (x1 + x2) / (4 * x1 * x2) with hq_def
  have hp_pos : 0 < p := by
    exact add_pos_of_pos_of_nonneg ( zero_lt_one.trans_le hx1 ) ( zero_le_one.trans hx2 )
  have hq_pos : 0 < q := by
    positivity
  have h_area_bound : volume (convexHull ℝ (Set.range C)) ≤ ENNReal.ofReal (1 / 2 + (x1 - x2)^2 / (8 * x1 * x2)) := by
    refine' le_trans ( MeasureTheory.measure_mono hsub ) _;
    rw [ volume_tri p q hp_pos hq_pos ];
    grind +qlia;
  have h_sum_bound : (n : ℝ) * Real.sqrt (a^2 - 1/16) ≤ 2 * (x1 + x2) := by
    have h_sum_bound : ∑ i : ZMod n, |C (i + 1) 0 - C i 0| ≤ 2 * (x1 + x2) := by
      refine' le_trans ( two_width_ge_sum n C hn hconv hsconv hne ) _;
      gcongr;
      refine' sub_le_iff_le_add'.mpr _;
      refine' Finset.sup'_le _ _ _;
      intro i hi; have := hsub ( subset_convexHull ℝ _ <| Set.mem_range_self i ) ; simp_all +decide [ tri ] ;
      exact le_trans ( show ( C i |> fun z => z.ofLp 0 ) ≤ x1 + x2 from by have := this.2.2; rw [ div_add_div, div_le_iff₀ ] at this <;> nlinarith ) ( le_add_of_nonneg_left <| Finset.le_inf' _ _ fun x hx => by have := h_all_in_S x; exact this.1.le.trans' <| by norm_num );
    refine le_trans ?_ h_sum_bound;
    exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun i _ => edge_dx_ge n C a ha hca h_all_in_S i );
  have h_final_bound : 4 * x1 * x2 ≤ (x1 - x2)^2 := by
    have h_final_bound : 1 ≤ 1 / 2 + (x1 - x2)^2 / (8 * x1 * x2) := by
      contrapose! hS;
      exact lt_of_le_of_lt h_area_bound ( ENNReal.ofReal_lt_one.mpr hS );
    nlinarith [ mul_pos ( zero_lt_one.trans_le hx1 ) ( zero_lt_one.trans_le hx2 ), div_mul_cancel₀ ( ( x1 - x2 ) ^ 2 ) ( by positivity : ( 8 * x1 * x2 ) ≠ 0 ) ];
  have h_final_bound : (n : ℝ)^2 * (a^2 - 1/16) ≤ 8 * a^2 := by
    have h_final_bound : (n : ℝ)^2 * (a^2 - 1/16) ≤ 4 * (x1 + x2)^2 := by
      nlinarith only [ show 0 ≤ ( n : ℝ ) * Real.sqrt ( a ^ 2 - 1 / 16 ) by positivity, h_sum_bound, Real.mul_self_sqrt ( show 0 ≤ a ^ 2 - 1 / 16 by nlinarith only [ ha ] ) ];
    exact h_final_bound.trans ( by nlinarith only [ abs_le.mp hdist, ‹4 * x1 * x2 ≤ ( x1 - x2 ) ^ 2› ] );
  nlinarith [ show ( n : ℝ ) ≥ 3 by norm_cast, sq_nonneg ( a - 2 ), mul_le_mul_of_nonneg_left ( show ( n : ℝ ) ≥ 3 by norm_cast ) ( show 0 ≤ a by positivity ) ]
/-- The inner content of the theorem: a convex (ccw) polygon with congruent sides
and all vertices in `S` has area `< 1`. -/
theorem area_lt_one
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2))
    (hn : 3 ≤ n)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hcong : ∃ a : ℝ, 0 < a ∧ ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i)) :
    volume (convexHull ℝ (Set.range C)) < 1 := by
  obtain ⟨a, ha, hca⟩ := hcong
  rcases lt_or_ge a 2 with hlt | hge
  · -- Small side: the area bound already gives `< 1`.
    obtain ⟨x1, x2, hx1, hx2, hdist, hsub⟩ :=
      exists_support_triangle n C a hn ha hconv hsconv hca hS
    have hp : 0 < x1 + x2 := by linarith
    have hq : 0 < (x1 + x2) / (4 * x1 * x2) := by positivity
    have hbound :
        volume (convexHull ℝ (Set.range C))
          ≤ ENNReal.ofReal (1 / 2 + (x1 - x2) ^ 2 / (8 * x1 * x2)) := by
      calc volume (convexHull ℝ (Set.range C))
            ≤ volume (tri (x1 + x2) ((x1 + x2) / (4 * x1 * x2))) := measure_mono hsub
        _ = ENNReal.ofReal ((x1 + x2) * ((x1 + x2) / (4 * x1 * x2)) / 2) :=
              volume_tri _ _ hp hq
        _ = ENNReal.ofReal (1 / 2 + (x1 - x2) ^ 2 / (8 * x1 * x2)) := by
              rw [← hyparea_identity x1 x2 (by linarith) (by linarith)]
              congr 1
              field_simp
              ring
    refine lt_of_le_of_lt hbound ?_
    have hxx : (1 : ℝ) ≤ x1 * x2 := by nlinarith
    have habs : (x1 - x2) ^ 2 ≤ a ^ 2 := by nlinarith [abs_nonneg (x1 - x2), sq_abs (x1 - x2)]
    have hlt1 : 1 / 2 + (x1 - x2) ^ 2 / (8 * x1 * x2) < 1 := by
      have h8 : 0 < 8 * x1 * x2 := by nlinarith
      have hhalf : (x1 - x2) ^ 2 / (8 * x1 * x2) < 1 / 2 := by
        rw [div_lt_iff₀ h8]; nlinarith
      linarith
    calc ENNReal.ofReal (1 / 2 + (x1 - x2) ^ 2 / (8 * x1 * x2))
          < ENNReal.ofReal 1 := by
            exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hlt1
      _ = 1 := by simp
  · -- Large side: handled by the projection argument.
    exact area_lt_one_of_large n C a hn hge hconv hsconv hca hS
/-- **Theorem `thm:congruent`.**  There exists a planar set `S` of infinite Lebesgue
measure such that every convex polygon with congruent sides and all vertices in `S`
has area strictly less than `1`. -/
theorem thm_congruent :
    ∃ S : Set (EuclideanSpace ℝ (Fin 2)), volume S = ⊤ ∧
      ∀ (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)),
        3 ≤ n →
        (∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i)) →
        (∃ a : ℝ, 0 < a ∧ ∀ i : ZMod n, dist (C i) (C (i + 1)) = a) →
        (∀ i : ZMod n, inS (C i)) →
        volume (convexHull ℝ (Set.range C)) < 1 := by
  refine ⟨Sset, volume_Sset_top, ?_⟩
  intro n C hn hsconv hcong hS
  -- Strict convexity (`hsconv`) yields the weak convexity `hconv` used internally.
  have hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i) := by
    intro i j
    by_cases hji : j = i
    · rw [hji]
      have h0 : cross (C (i + 1) - C i) (C i - C i) = 0 := by unfold cross; simp
      rw [h0]
    · by_cases hji1 : j = i + 1
      · rw [hji1]
        have h0 : cross (C (i + 1) - C i) (C (i + 1) - C i) = 0 := by unfold cross; ring
        rw [h0]
      · exact (hsconv i j hji hji1).le
  exact area_lt_one n C hn hconv hsconv hcong hS
end Kovac

/-- **Erdős Problem 353.** Resolved by Koizumi [Ko25] and Kovač–Predojević [KoPr24].
The website asks five sub-questions; the answers are **YES, YES, YES, YES, NO**:

1. (YES) Every measurable `S ⊂ ℝ²` of infinite measure contains an isosceles trapezoid
   of area `1` (Koizumi).
2. (YES) Every measurable `S` of positive measure that is unbounded contains an
   isosceles triangle of area `1` (Koizumi).
3. (YES) Every measurable `S` of positive measure that is unbounded contains a
   right-angled triangle of area `1` (Koizumi).
4. (YES) Every measurable `S` of infinite measure contains the vertices of a
   cyclic quadrilateral of area `1` (Kovač–Predojević).
5. (NO) There exists a measurable `S` of infinite measure such that every convex
   polygon with congruent sides and vertices in `S` has area strictly less than `1`
   (Kovač–Predojević). -/
theorem erdos_353 :
    -- (1) Isosceles trapezoid: YES
    (∀ S : Set (EuclideanSpace ℝ (Fin 2)),
        MeasurableSet S → volume S = ⊤ →
        ∃ A B C D, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ Koizumi.IsoTrapArea1 A B C D) ∧
    -- (2) Isosceles triangle: YES
    (∀ S : Set (EuclideanSpace ℝ (Fin 2)),
        MeasurableSet S → 0 < volume S → ¬ Bornology.IsBounded S →
        ∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ Koizumi.IsoscelesTriangleArea1 A B C) ∧
    -- (3) Right-angled triangle: YES
    (∀ S : Set (EuclideanSpace ℝ (Fin 2)),
        MeasurableSet S → 0 < volume S → ¬ Bornology.IsBounded S →
        ∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ Koizumi.RightTriangleArea1 A B C) ∧
    -- (4) Cyclic quadrilateral: YES
    (∀ A : Set (EuclideanSpace ℝ (Fin 2)),
        MeasurableSet A → volume A = ⊤ →
        ∃ P Q R T : EuclideanSpace ℝ (Fin 2),
          P ∈ A ∧ Q ∈ A ∧ R ∈ A ∧ T ∈ A ∧ CyclicQuad.UnitCyclicQuad P Q R T) ∧
    -- (5) Convex polygon with congruent sides: NO (counterexample exists)
    (∃ S : Set (EuclideanSpace ℝ (Fin 2)), volume S = ⊤ ∧
        ∀ (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)),
          3 ≤ n →
          (∀ i j : ZMod n, j ≠ i → j ≠ i + 1 →
            0 < Kovac.cross (C (i + 1) - C i) (C j - C i)) →
          (∃ a : ℝ, 0 < a ∧ ∀ i : ZMod n, dist (C i) (C (i + 1)) = a) →
          (∀ i : ZMod n, C i ∈ S) →
          volume (convexHull ℝ (Set.range C)) < 1) := by
  refine ⟨Koizumi.thm_trapezoid,
          fun S hS hpos hunb => (Koizumi.thm_iso_right S hS hpos hunb).1,
          fun S hS hpos hunb => (Koizumi.thm_iso_right S hS hpos hunb).2,
          CyclicQuad.exists_unitCyclicQuad_of_volume_infinite,
          ?_⟩
  -- For sub-claim (5), use `Kovac.Sset` directly so the membership `C i ∈ S`
  -- unfolds to `Kovac.inS (C i)` definitionally.
  refine ⟨Kovac.Sset, Kovac.volume_Sset_top, ?_⟩
  intro n C hn hconv hcong hvert
  obtain ⟨_, _, hS_prop⟩ := Kovac.thm_congruent
  exact hS_prop n C hn hconv hcong hvert

#print axioms erdos_353
-- 'Erdos353.erdos_353' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos353
