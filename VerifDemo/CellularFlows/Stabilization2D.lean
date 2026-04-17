/-
  Cellular Flows — Self-Stabilization (2D Grid, Failure-Free)
  =============================================================

  Extends the 1D `Stabilization.lean` result to the N×N 2D grid of
  `multiColorTS`. Starting from ANY MCState (not just the canonical
  `multiColorTS.init`) in which no cell is failed, the Route subroutine
  recovers correct dist values within Δ(x) rounds, where Δ(x) is the
  grid diameter.

  Paper reference: Corollary 7, Section 4.3 (stabilization after the
  last fail transition). This file handles the failure-free 2D case:
  no cells are failed throughout, but the initial dist/next values are
  arbitrary.

  KEY OBSERVATION: `multiColorTS.next` forces:
    - target cells to have `s'.dist c i = .fin 0`
    - failed cells to have `s'.dist c i = .inf`
    - non-target non-failed cells to recompute via Bellman-Ford on 2D
  REGARDLESS of the pre-state's dist/next values. Thus, even from a
  garbage starting state, the routing table recovers within the grid
  diameter rounds.

  THEOREMS PROVED
    1. multiColorTS_next_failed_preserved — failed flag unchanged
    2. reachableFromInK_MC_preserves_nonFailed — no failures preserved
    3. mc_kStepLowerBound — after k steps, dist ≥ min(k, manhattan i target)
    4. mc_route_self_stabilizes — after k+1 steps from ANY failure-free
       state, cells with manhattan ≤ k have correct dist.
-/
import VerifDemo.CellularFlows.MultiColorProofs

set_option autoImplicit false

namespace CellularFlows

/- ------------------------------------------------------------------- -/
/- ReachableFromInK_MC: k-step reachability from an ARBITRARY starting -/
/- state (not required to satisfy `multiColorTS.init`).                -/

/-- k-step reachability from an arbitrary starting state via `multiColorTS.next`.
    Unlike `ReachableInK (multiColorTS ..)`, this does not require `s₀` to
    satisfy `multiColorTS.init`, so `s₀` can have garbage dist/next values. -/
inductive ReachableFromInK_MC {n nc : Nat} (targets : Fin nc → CellId2D n) :
    MCState n nc → Nat → MCState n nc → Prop where
  | refl (s₀ : MCState n nc) : ReachableFromInK_MC targets s₀ 0 s₀
  | step (s₀ s s' : MCState n nc) (k : Nat) :
      ReachableFromInK_MC targets s₀ k s →
      (multiColorTS n nc targets).next s s' →
      ReachableFromInK_MC targets s₀ (k + 1) s'

/- ------------------------------------------------------------------- -/
/- The `failed` field is preserved by `multiColorTS.next`.             -/

/-- One step of `multiColorTS` preserves the `failed` predicate pointwise. -/
theorem multiColorTS_next_failed_preserved (n nc : Nat)
    (targets : Fin nc → CellId2D n) (s s' : MCState n nc)
    (hstep : (multiColorTS n nc targets).next s s') :
    ∀ i : CellId2D n, s'.failed i = s.failed i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hfail⟩ := hstep
  exact hfail

/-- If no cell is failed in `s₀` and we reach `s` via `multiColorTS`, then
    no cell is failed in `s`. -/
theorem reachableFromInK_MC_preserves_nonFailed (n nc : Nat)
    (targets : Fin nc → CellId2D n) :
    ∀ k s₀ s, ReachableFromInK_MC targets s₀ k s →
      (∀ i : CellId2D n, s₀.failed i = false) →
      ∀ i : CellId2D n, s.failed i = false := by
  intro k s₀ s hr hff
  induction hr with
  | refl => exact hff
  | step _t t' _k _hr_t hstep ih =>
    intro i
    rw [multiColorTS_next_failed_preserved n nc targets _ t' hstep i]
    exact ih i

/- ------------------------------------------------------------------- -/
/- Local DistVal helpers (these are private in MultiColorProofs.lean,  -/
/- so we re-prove them locally to keep this file self-contained).       -/

private theorem dv_dmin_inf_left (a : DistVal) : DistVal.dmin .inf a = a := by
  cases a with | fin _ => rfl | inf => rfl

private theorem dv_dmin_inf_right (a : DistVal) : DistVal.dmin a .inf = a := by
  cases a with | fin _ => rfl | inf => rfl

private theorem dv_dmin_fin_fin (a b : Nat) :
    DistVal.dmin (.fin a) (.fin b) = .fin (Nat.min a b) := rfl

private theorem dv_succ_fin (m : Nat) : DistVal.succ (.fin m) = .fin (m + 1) := rfl
private theorem dv_succ_inf : DistVal.succ .inf = .inf := rfl

/-- manhattan = 0 implies equal cells (local copy of the private helper
    in MultiColorProofs.lean). -/
private theorem manhattan_eq_zero_imp_local {n : Nat} (i t : CellId2D n)
    (h : manhattan i t = 0) : i = t := by
  simp [manhattan] at h
  have hr : i.1.val = t.1.val := by have := h.1; split at this <;> omega
  have hc : i.2.val = t.2.val := by have := h.2; split at this <;> omega
  exact Prod.ext (Fin.ext hr) (Fin.ext hc)

/- ------------------------------------------------------------------- -/
/- When all cells are non-failed, nonFailedNeighbors2D = neighbors2D.  -/

/-- When the `failed` predicate is uniformly false, the list of non-failed
    2D neighbors equals the full 2D neighbor list. -/
theorem nonFailedNeighbors2D_eq_neighbors2D_local {n : Nat}
    (failed : CellId2D n → Bool) (i : CellId2D n)
    (hff : ∀ j : CellId2D n, failed j = false) :
    nonFailedNeighbors2D failed i = neighbors2D i := by
  unfold nonFailedNeighbors2D
  suffices h : ∀ (l : List (CellId2D n)), List.filter (fun j => !failed j) l = l by
    exact h (neighbors2D i)
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.filter, hff x, ih]

/- ------------------------------------------------------------------- -/
/- Step-indexed distance lower bound: after k rounds from arbitrary   -/
/- garbage, dist ≥ min(k, manhattan i (targets c)).                    -/

/-- After `k` rounds from an arbitrary start, every cell's distance (for
    every color c) is at least `min(k, manhattan i (targets c))`.
    At k=0 this is trivial (bound = 0). Each step strengthens the bound
    by 1 for every cell, bounded above by the cell's true manhattan
    distance to the target. -/
def mcKStepLowerBound {n nc : Nat} (targets : Fin nc → CellId2D n) (k : Nat)
    (s : MCState n nc) : Prop :=
  ∀ c : Fin nc, ∀ i : CellId2D n, ∀ m : Nat,
    s.dist c i = .fin m → m ≥ Nat.min k (manhattan i (targets c))

/-- Base: any state trivially satisfies the 0-step lower bound. -/
theorem mcKStepLowerBound_zero {n nc : Nat} (targets : Fin nc → CellId2D n)
    (s : MCState n nc) :
    mcKStepLowerBound targets 0 s := by
  intro c i m _
  simp

/- ------------------------------------------------------------------- -/
/- Generalized minDist2D lower bound: each cell j in the list lower    -/
/- bounded by its own bound — we specialize to the manhattan-style.    -/

/-- Helper (dmin version): if a finite minimum is at most the two operands'
    finite values, then the lower bound propagates. Concretely:
      dmin (fin a) b = fin m, with a ≥ bound and b's finite m' also ≥ bound,
    implies m ≥ bound. -/
private theorem dmin_ge_bound_local (a : Nat) (b : DistVal) (m bound : Nat)
    (ha : a ≥ bound) (hb : ∀ mb, b = .fin mb → mb ≥ bound)
    (hdmin : DistVal.dmin (.fin a) b = .fin m) : m ≥ bound := by
  cases b with
  | inf =>
    simp [DistVal.dmin] at hdmin
    omega
  | fin mb =>
    have hge_b := hb mb rfl
    simp [DistVal.dmin] at hdmin
    subst hdmin
    simp [Nat.min_def]; split <;> omega

/-- Local minDist2D lower bound (pointwise): if every cell j in the list
    has dist j = .fin mj → mj ≥ bound, then minDist2D dist cells = .fin m
    implies m ≥ bound. (Duplicates the private helper in MultiColorProofs.) -/
private theorem minDist2D_lb_local {n : Nat} (dist : CellId2D n → DistVal)
    (cells : List (CellId2D n)) (bound : Nat)
    (hlb : ∀ j : CellId2D n, j ∈ cells → ∀ mj : Nat, dist j = .fin mj → mj ≥ bound) :
    ∀ m : Nat, minDist2D dist cells = .fin m → m ≥ bound := by
  induction cells with
  | nil => intro m hmin; simp [minDist2D] at hmin
  | cons x xs ih =>
    intro m hmin
    cases xs with
    | nil =>
      simp [minDist2D] at hmin
      exact hlb x (by simp) m hmin
    | cons y ys =>
      simp only [minDist2D] at hmin
      have hlb_x : ∀ mj, dist x = .fin mj → mj ≥ bound :=
        hlb x (by simp)
      have hlb_rest : ∀ j : CellId2D n, j ∈ (y :: ys) →
          ∀ mj, dist j = .fin mj → mj ≥ bound :=
        fun j hj => hlb j (by simp [hj])
      cases hdx : dist x with
      | inf =>
        rw [hdx, dv_dmin_inf_left] at hmin
        exact ih hlb_rest m hmin
      | fin mx =>
        have hge_x := hlb_x mx hdx
        apply dmin_ge_bound_local mx (minDist2D dist (y :: ys)) m bound hge_x
        · exact ih hlb_rest
        · rw [hdx] at hmin; exact hmin

/-- Neighbor membership fact: for any j ∈ neighbors2D i we have
    areNeighbors2D i j. (Accesses the existing public theorem in
    MultiColorProofs.) -/
private theorem nbrs2D_mem_areNeighbors_local {n : Nat} (i j : CellId2D n)
    (hj : j ∈ neighbors2D i) : areNeighbors2D i j :=
  neighbors2D_mem_areNeighbors i j hj

/-- The step case of `mcKStepLowerBound`: one `multiColorTS` step
    strengthens the lower bound from k to k+1, provided all cells are
    non-failed in the predecessor state. -/
theorem mcKStepLowerBound_step (n nc : Nat) (targets : Fin nc → CellId2D n)
    (k : Nat) (s s' : MCState n nc)
    (hff : ∀ i : CellId2D n, s.failed i = false)
    (hlb : mcKStepLowerBound targets k s)
    (hstep : (multiColorTS n nc targets).next s s') :
    mcKStepLowerBound targets (k + 1) s' := by
  intro c i m hm
  obtain ⟨hroute_target, _hroute_failed, hroute_bf,
          _, _, _, _, _, _, _, _, _, _, _, _hfail_frame⟩ := hstep
  by_cases hitarget : i = targets c
  · -- target cell: dist = fin 0, m = 0. min (k+1) (manhattan i target) = 0.
    subst hitarget
    have ⟨hd, _⟩ := hroute_target c _ rfl
    rw [hd] at hm; cases hm
    -- manhattan (targets c) (targets c) = 0
    simp [manhattan_self_eq]
  · -- non-target non-failed cell: Bellman-Ford update on 2D.
    have hfail_i : s.failed i = false := hff i
    have hbf := hroute_bf c i hitarget hfail_i
    rw [nonFailedNeighbors2D_eq_neighbors2D_local s.failed i hff] at hbf
    rw [hbf.1] at hm
    cases hmd : minDist2D (s.dist c) (neighbors2D i) with
    | inf => rw [hmd, dv_succ_inf] at hm; cases hm
    | fin md =>
      rw [hmd, dv_succ_fin] at hm; cases hm
      -- Goal: md + 1 ≥ min (k+1) (manhattan i (targets c))
      -- Strategy: for every neighbor j, dist j = fin mj → mj ≥ min k (manhattan j (targets c)).
      -- By triangle inequality (manhattan j target + 1 ≥ manhattan i target), so
      -- mj ≥ min k (manhattan i target - 1). Thus md ≥ min k (manhattan i target - 1).
      -- Then md + 1 ≥ min (k+1) (manhattan i target).
      by_cases hman_zero : manhattan i (targets c) = 0
      · -- manhattan i target = 0 means i = target, contradicts hitarget
        exact absurd (manhattan_eq_zero_imp_local i (targets c) hman_zero) hitarget
      · have hman_pos : manhattan i (targets c) > 0 := by omega
        -- Prove md ≥ min k (manhattan i target - 1)
        have hmd_lb : md ≥ Nat.min k (manhattan i (targets c) - 1) := by
          apply minDist2D_lb_local (s.dist c) (neighbors2D i)
                (Nat.min k (manhattan i (targets c) - 1))
                _ md hmd
          intro j hj mj hmj
          have hge_j := hlb c j mj hmj
          -- hge_j : mj ≥ min k (manhattan j (targets c))
          have hneigh : areNeighbors2D i j :=
            nbrs2D_mem_areNeighbors_local i j hj
          have htri : manhattan j (targets c) + 1 ≥ manhattan i (targets c) :=
            manhattan_neighbor_triangle i j (targets c) hneigh
          -- So manhattan j target ≥ manhattan i target - 1.
          -- Since Nat.min is monotone in its second argument: min k (man j) ≥ min k (man i - 1).
          have hmj_ge_left : mj ≥ k ∨ mj ≥ manhattan j (targets c) := by
            rcases Nat.le_total k (manhattan j (targets c)) with hkj | hkj
            · left
              have heq : Nat.min k (manhattan j (targets c)) = k := Nat.min_eq_left hkj
              omega
            · right
              have heq : Nat.min k (manhattan j (targets c)) = manhattan j (targets c) :=
                Nat.min_eq_right hkj
              omega
          -- Goal: mj ≥ min k (manhattan i target - 1).
          have hmin_le_k : Nat.min k (manhattan i (targets c) - 1) ≤ k :=
            Nat.min_le_left _ _
          have hmin_le_i : Nat.min k (manhattan i (targets c) - 1) ≤
              manhattan i (targets c) - 1 := Nat.min_le_right _ _
          rcases hmj_ge_left with h | h
          · omega
          · -- h : mj ≥ manhattan j target; htri : man j + 1 ≥ man i
            omega
        -- From hmd_lb conclude md + 1 ≥ min (k+1) (manhattan i target).
        have hmin_eq : Nat.min k (manhattan i (targets c) - 1) + 1 =
            Nat.min (k + 1) (manhattan i (targets c)) := by
          rcases Nat.le_total k (manhattan i (targets c) - 1) with hc | hc
          · have hL : Nat.min k (manhattan i (targets c) - 1) = k := Nat.min_eq_left hc
            have hR : Nat.min (k + 1) (manhattan i (targets c)) = k + 1 :=
              Nat.min_eq_left (by omega)
            rw [hL, hR]
          · have hL : Nat.min k (manhattan i (targets c) - 1) =
                manhattan i (targets c) - 1 := Nat.min_eq_right hc
            have hR : Nat.min (k + 1) (manhattan i (targets c)) =
                manhattan i (targets c) := Nat.min_eq_right (by omega)
            rw [hL, hR]; omega
        omega

/-- After k steps from an arbitrary failure-free start, the step-indexed
    lower bound holds. -/
theorem mcKStepLowerBound_at_k (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ k s₀ s, ReachableFromInK_MC targets s₀ k s →
      (∀ i : CellId2D n, s₀.failed i = false) →
      mcKStepLowerBound targets k s := by
  intro k s₀ s hr hff
  induction hr with
  | refl => exact mcKStepLowerBound_zero targets s₀
  | step t t' j hr_t hstep ih =>
    -- Need: failed is uniformly false at t so mcKStepLowerBound_step applies
    have hff_t : ∀ i : CellId2D n, t.failed i = false :=
      reachableFromInK_MC_preserves_nonFailed n nc targets j s₀ t hr_t hff
    exact mcKStepLowerBound_step n nc targets j t t' hff_t ih hstep

/- ------------------------------------------------------------------- -/
/- 2D self-stabilization (paper Corollary 7, 2D failure-free).          -/

/-- ★ 2D SELF-STABILIZATION (paper Corollary 7, 2D failure-free case).
    Starting from ANY MCState in which no cell is failed, after k+1
    rounds of `multiColorTS`, every cell i with
    `manhattan i (targets c) ≤ k` has `dist c i = .fin (manhattan i (targets c))`.

    This generalizes `route_self_stabilizes` (1D line case) to the
    N×N grid. The proof follows the same pattern as `mc_route_convergence`
    (Lemma 6 on 2D) but starts from an arbitrary initial state via
    `ReachableFromInK_MC` instead of `ReachableInK multiColorTS`.

    The `+1` accounts for the first step establishing target cells'
    `dist = fin 0` (prior to which `s₀.dist c (targets c)` could be
    anything). -/
theorem mc_route_self_stabilizes (n nc : Nat) (targets : Fin nc → CellId2D n)
    (hn : n > 0) :
    ∀ k : Nat, ∀ s₀ s : MCState n nc,
      (∀ i : CellId2D n, s₀.failed i = false) →
      ReachableFromInK_MC targets s₀ (k + 1) s →
      ∀ c : Fin nc, ∀ i : CellId2D n,
        manhattan i (targets c) ≤ k →
        s.dist c i = .fin (manhattan i (targets c)) := by
  intro k
  induction k with
  | zero =>
    -- After 1 step from s₀, target has dist = fin 0. Cells with
    -- manhattan ≤ 0 must equal target, so have correct dist.
    intro s₀ s hff hr c i hle
    have hman : manhattan i (targets c) = 0 := by omega
    have heq : i = targets c := manhattan_eq_zero_imp_local i (targets c) hman
    subst heq
    cases hr with
    | step _t _s' _k _hr_t hstep =>
      obtain ⟨htarget, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hstep
      rw [(htarget c _ rfl).1]; congr 1; exact hman.symm
  | succ k ih =>
    -- After k+2 steps, cells with manhattan ≤ k+1 have correct dist.
    intro s₀ s' hff hr c i hle
    cases hr with
    | step t _s' _k hr_t hstep =>
      obtain ⟨hroute_target, _hroute_failed, hroute_bf,
              _, _, _, _, _, _, _, _, _, _, _, _hfail_frame⟩ := hstep
      by_cases hitarget : i = targets c
      · subst hitarget
        rw [(hroute_target c _ rfl).1]; congr 1
        exact (manhattan_self_eq (targets c)).symm
      · -- Non-target: Bellman-Ford update on 2D neighbors.
        have hff_t : ∀ j : CellId2D n, t.failed j = false :=
          reachableFromInK_MC_preserves_nonFailed n nc targets (k + 1) s₀ t hr_t hff
        have hfail_i : t.failed i = false := hff_t i
        have hbf := hroute_bf c i hitarget hfail_i
        rw [nonFailedNeighbors2D_eq_neighbors2D_local t.failed i hff_t] at hbf
        rw [hbf.1]
        -- IH: cells at manhattan ≤ k in `t` have correct dist
        have hih := ih s₀ t hff hr_t
        -- Existence of a closer neighbor:
        have hman_pos : manhattan i (targets c) > 0 := by
          rcases Nat.eq_zero_or_pos (manhattan i (targets c)) with h0 | hpos
          · exact absurd (manhattan_eq_zero_imp_local i (targets c) h0) hitarget
          · exact hpos
        obtain ⟨j, hj_mem, hj_man⟩ :=
          exists_closer_neighbor hn i (targets c) hitarget
        have hj_le : manhattan j (targets c) ≤ k := by omega
        have hj_dist : t.dist c j = .fin (manhattan j (targets c)) :=
          hih c j hj_le
        -- So minDist2D t.dist (neighbors2D i) ≤ fin (manhattan j target).
        obtain ⟨r, hr_eq, hr_le⟩ :=
          minDist2D_le_mem_local (t.dist c) (neighbors2D i) j
            (manhattan j (targets c)) hj_mem hj_dist
        -- Step-indexed lower bound on t: m ≥ min (k+1) (manhattan j target).
        have hlb := mcKStepLowerBound_at_k n nc targets (k + 1) s₀ t hr_t hff
        have hlb_min : r ≥ manhattan i (targets c) - 1 := by
          apply minDist2D_lb_local (t.dist c) (neighbors2D i)
                (manhattan i (targets c) - 1) _ r hr_eq
          intro j' hj' mj hmj
          have hge_j := hlb c j' mj hmj
          -- hge_j : mj ≥ min (k+1) (manhattan j' target)
          have hneigh : areNeighbors2D i j' :=
            nbrs2D_mem_areNeighbors_local i j' hj'
          have htri : manhattan j' (targets c) + 1 ≥ manhattan i (targets c) :=
            manhattan_neighbor_triangle i j' (targets c) hneigh
          -- Split on min.
          rcases Nat.le_total (k + 1) (manhattan j' (targets c)) with hcase | hcase
          · have heq : Nat.min (k + 1) (manhattan j' (targets c)) = k + 1 :=
              Nat.min_eq_left hcase
            rw [heq] at hge_j
            -- hge_j : mj ≥ k + 1; i.man ≤ k + 1 so i.man - 1 ≤ k ≤ mj
            omega
          · have heq : Nat.min (k + 1) (manhattan j' (targets c)) =
                manhattan j' (targets c) := Nat.min_eq_right hcase
            rw [heq] at hge_j
            -- hge_j : mj ≥ man j' target;
            -- htri : man j' target + 1 ≥ man i target; so mj ≥ man i target - 1
            omega
        have hr_val : r = manhattan i (targets c) - 1 := by omega
        rw [hr_eq, hr_val, dv_succ_fin]
        congr 1; omega
where
  /-- Local version of the public minDist2D_le_mem helper: if j ∈ cells and
      dist j = .fin m, then minDist2D has a finite value ≤ m. -/
  minDist2D_le_mem_local {n : Nat} (dist : CellId2D n → DistVal)
      (cells : List (CellId2D n)) (j : CellId2D n) (m : Nat)
      (hj : j ∈ cells) (hdj : dist j = .fin m) :
      ∃ r : Nat, minDist2D dist cells = .fin r ∧ r ≤ m := by
    induction cells with
    | nil => simp at hj
    | cons x xs ih =>
      cases xs with
      | nil =>
        simp at hj; subst hj
        exact ⟨m, by simp [minDist2D, hdj], Nat.le_refl m⟩
      | cons y ys =>
        simp only [minDist2D]
        rcases List.mem_cons.mp hj with rfl | hxs
        · rw [hdj]
          cases hmr : minDist2D dist (y :: ys) with
          | inf =>
            rw [dv_dmin_inf_right]
            exact ⟨m, rfl, Nat.le_refl m⟩
          | fin r =>
            rw [dv_dmin_fin_fin]
            exact ⟨Nat.min m r, rfl, Nat.min_le_left m r⟩
        · have ⟨r, hr, hle⟩ := ih hxs
          cases hdx : dist x with
          | inf =>
            rw [dv_dmin_inf_left]
            exact ⟨r, hr, hle⟩
          | fin mx =>
            rw [hr, dv_dmin_fin_fin]
            exact ⟨Nat.min mx r, rfl, Nat.le_trans (Nat.min_le_right mx r) hle⟩

end CellularFlows
