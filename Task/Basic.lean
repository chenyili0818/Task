import Mathlib.Analysis.Convex.Intrinsic

open AffineSubspace Set

open scoped Pointwise

variable {𝕜 V W Q P : Type*}

section LineSegmentPrinciple

variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
  {s t : Set P} {x y: P}

/-
参考 Convex analysis (Ralph Tyrell Rockafellar) thm6.1
设 C 是 ℝ^n 中的凸集，若 x ∈ ri C 且 y ∈ cl C，则对于 0 ≤ λ ≤ 1，有 (1 - λ) • x + λ • y ∈ ri C
-/
theorem openSegment_sub_intrinsicInterior [OrderedSemiring 𝕜] [AddCommMonoid P][SMul 𝕜 P]
    (hs : Convex 𝕜 s)(hx : x ∈ closure s)(hy : y ∈ intrinsicInterior 𝕜 s):
    openSegment 𝕜 x y ⊆ intrinsicInterior 𝕜 s := sorry

end LineSegmentPrinciple

section affinespan
/-
参考 Convex analysis (Ralph Tyrell Rockafellar) thm6.2
如果 C 是 ℝ^n 中的凸集，则 cl(C) 和 ri(C) 是 ℝ^n 中的凸集，并且它们具有相同的仿射包。
-/
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P] [AddCommMonoid P]
  [OrderedSemiring 𝕜] [SMul 𝕜 P] {s: Set P}

theorem convex_intrinsicInterior (h : Convex 𝕜 s) :
    Convex 𝕜 (intrinsicInterior 𝕜 s) := sorry

theorem affinespan_intrinsicInterior (h : Convex 𝕜 s) :
    affineSpan 𝕜 s = affineSpan 𝕜 (intrinsicInterior 𝕜 s) := sorry

end affinespan

section intrinsicInterior_closure_comm
/-
Convex analysis (Ralph Tyrell Rockafellar) thm6.3
对于 ℝ^n 中的任何凸集 C
1. cl(ri(C)) = cl(C)
2. ri(cl(C)) = ri(C)
3. 如果 C_bar 是另一个非空凸集，则以下条件等价：
  (i) C 和 C_bar 具有相同的相对内点集
  (ii) C 和 C_bar 具有相同的闭包
  (iii) ri(C) ⊆ C_bar ⊆ cl(C)
-/
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P] [AddCommMonoid P]
  [OrderedSemiring 𝕜] [SMul 𝕜 P] {s t: Set P}

theorem closure_intrinsicInterior (h : Convex 𝕜 s) :
  closure (intrinsicInterior 𝕜 s) = closure s := sorry

theorem intrinsicInterior_closure (h : Convex 𝕜 s) :
  intrinsicInterior 𝕜 (closure s) = intrinsicInterior 𝕜 s := sorry

theorem intrinsicInterior_tfae (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
  [closure s = closure t, intrinsicInterior 𝕜 s = intrinsicInterior 𝕜 t,
  intrinsicInterior 𝕜 s ⊆ t ∧ t ⊆ closure s].TFAE := sorry

end intrinsicInterior_closure_comm

section Prolongation

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {s : Set V}

/-
Convex analysis (Ralph Tyrell Rockafellar) thm6.4
Let s be a non-empty convex subset of ℝ^n. Then z ∈ ri s (intrinsic interior of C)
if and only if for every x ∈ s, there exists μ > 1 such that (1 - μ) • x + μ • z ∈ s.
-/
theorem intrinsicInterior_iff {z : V}(hs : Convex ℝ s) (ns : s.Nonempty):
    z ∈ intrinsicInterior ℝ s ↔ ∀ x ∈ s, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ s:=by sorry
-- /-
-- 习题：
-- 假设 X 是一个无约束优化问题，优化的目标函数为凹函数，
-- 如果 X 的solution set 包含 X 定义域的相对内点，则 f 在 X 上为常数，即 X.solution_set = X。
-- -/
-- variable {X : OptimizationProblem V}

-- theorem solusion_set_eq_domain (huniv : X.constrained_domain = univ)(h : ConcaveOn ℝ X.domain X.objective)
--     (hinter : X.solution_set ∩ (intrinsicInterior ℝ X.domain) ≠ ∅ ):
--   X.solution_set = X.domain := sorry

end Prolongation


section intersection
/-
Convex analysis (Ralph Tyrell Rockafellar) thm6.5
设 {C_i} 是 ℝ^n 中的凸集族，且交集的相对内部非空。
1. cl(⋂ C_i) = ⋂ cl(C_i)
2. 若 I 为有限集，则 ri(⋂ C_i) = ⋂ ri(C_i)
-/
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P] [AddCommMonoid P]
  [OrderedSemiring 𝕜] [SMul 𝕜 P] {ι : Sort*} {s : ι → Set P}

theorem iIntersection_closure_eq_intrinsicInterior_closure (h : ∀ (i : ι), Convex 𝕜 (s i))
    (hinter : ⋂ i, (intrinsicInterior 𝕜 (s i)) ≠ ∅) :
  ⋂ i, closure (s i) = closure (⋂ i, s i) := sorry

theorem intrinsicInterior_iIntersection_sub_iIntersection_intrinsicInterior (h : ∀ (i : ι), Convex 𝕜 (s i))
    (hinter : ⋂ i, (intrinsicInterior 𝕜 (s i)) ≠ ∅) :
  intrinsicInterior 𝕜 (⋂ i, s i) ⊆ ⋂ i, intrinsicInterior 𝕜 (s i):= sorry

theorem iIntersection_intrinsicInterior_sub_intrinsicInterior_iIntersection [Finite ι] (h : ∀ (i : ι), Convex 𝕜 (s i)) :
  ⋂ i, intrinsicInterior 𝕜 (s i) ⊆ intrinsicInterior 𝕜 (⋂ i, s i) := sorry

theorem iIntersection_intrinsicInterior_eq_intrinsicInterior_iIntersection [Finite ι] (h : ∀ (i : ι), Convex 𝕜 (s i))
    (hinter : ⋂ i, (intrinsicInterior 𝕜 (s i)) ≠ ∅):
    ⋂ i, intrinsicInterior 𝕜 (s i) = intrinsicInterior 𝕜 (⋂ i, s i) := by
  apply Subset.antisymm
  exact iIntersection_intrinsicInterior_sub_intrinsicInterior_iIntersection h
  exact intrinsicInterior_iIntersection_sub_iIntersection_intrinsicInterior h hinter

end intersection
