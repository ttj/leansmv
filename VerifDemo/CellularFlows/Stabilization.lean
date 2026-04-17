/-
  Cellular Flows — Self-Stabilization (1D Line, Failure-Free)
  =============================================================

  Extends Lemma 6 / Corollary 7 to cover the paper's "stabilizing"
  claim: starting from ANY RouteState (not just the canonical
  `routeFFTS.init`), the Route subroutine recovers correct dist/next
  values within O(n) rounds.

  Paper reference: Corollary 7, Section 4.3 (stabilization after the
  last fail transition). This file handles the failure-free 1D case:
  no cells are failed throughout, but the initial dist/next values are
  arbitrary.

  KEY OBSERVATION: `routeTS.next` forces:
    - target cells to have `s'.dist = .fin 0`
    - failed cells to have `s'.dist = .inf`
    - non-target non-failed cells to recompute via Bellman-Ford
  REGARDLESS of the pre-state's dist/next values. Thus, even from a
  garbage starting state, the routing table recovers within `diameter`
  rounds.

  THEOREMS PROVED
    1. routeTS_preserves_nonFailed — failed = 0 is preserved
    2. kStepLowerBound — after k steps, dist ≥ min(k, i.val)
    3. route_self_stabilizes — after k+1 steps from ANY failure-free
       state, cells at distance ≤ k have correct dist
    4. route_next_self_stabilizes — similarly for next-hop pointers
-/
import VerifDemo.CellularFlows.RouteProofs

namespace CellularFlows

/- ------------------------------------------------------------------- -/
/- ReachableFromInK: k-step reachability from an ARBITRARY starting    -/
/- state (not required to satisfy `routeTS.init`).                     -/

/-- k-step reachability from an arbitrary starting state via `routeTS.next`.
    Unlike `ReachableInK (routeTS n)`, this does not require `s₀` to satisfy
    `routeTS.init`, so `s₀` can have garbage dist/next values. -/
inductive ReachableFromInK {n : Nat} : RouteState n → Nat → RouteState n → Prop where
  | refl (s₀ : RouteState n) : ReachableFromInK s₀ 0 s₀
  | step (s₀ s s' : RouteState n) (k : Nat) :
      ReachableFromInK s₀ k s → (routeTS n).next s s' →
      ReachableFromInK s₀ (k + 1) s'

/- ------------------------------------------------------------------- -/
/- The `failed` field is preserved by `routeTS.next`.                  -/

/-- One step of `routeTS` preserves the `failed` predicate pointwise. -/
theorem routeTS_next_failed_preserved (n : Nat) (s s' : RouteState n)
    (hstep : (routeTS n).next s s') :
    ∀ i : Fin n, s'.failed i = s.failed i := by
  exact hstep.1

/-- If no cell is failed in `s₀` and we reach `s` via `routeTS`, then no
    cell is failed in `s`. -/
theorem reachableFromInK_preserves_nonFailed (n : Nat) :
    ∀ k s₀ s, ReachableFromInK s₀ k s →
      (∀ i : Fin n, s₀.failed i = false) →
      ∀ i : Fin n, s.failed i = false := by
  intro k s₀ s hr hff
  induction hr with
  | refl => exact hff
  | step t t' _k _hr_t hstep ih =>
    intro i
    rw [routeTS_next_failed_preserved n t t' hstep i]
    exact ih i

/- ------------------------------------------------------------------- -/
/- When all cells are non-failed, nonFailedNeighbors = neighbors1D.    -/

/-- When the `failed` predicate is uniformly false, the list of non-failed
    neighbors equals the full neighbor list. -/
theorem nonFailedNeighbors_eq_neighbors1D {n : Nat}
    (failed : Fin n → Bool) (i : Fin n)
    (hff : ∀ j : Fin n, failed j = false) :
    nonFailedNeighbors failed i = neighbors1D i := by
  unfold nonFailedNeighbors
  suffices h : ∀ (l : List (Fin n)), List.filter (fun j => !failed j) l = l by
    exact h (neighbors1D i)
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.filter, hff x, ih]

/- ------------------------------------------------------------------- -/
/- Step-indexed distance lower bound: after k rounds from arbitrary   -/
/- garbage, dist ≥ min(k, i.val). This generalises `distLowerBound`   -/
/- which only works from the canonical init state.                    -/

/-- After `k` rounds from an arbitrary start, every cell's distance is
    at least `min(k, i.val)`.  At k=0 this is trivial (bound = 0).
    Each step strengthens the bound by 1 for every cell. -/
def kStepLowerBound {n : Nat} (k : Nat) (s : RouteState n) : Prop :=
  ∀ i : Fin n, ∀ m : Nat, s.dist i = .fin m → m ≥ Nat.min k i.val

/-- Base: any state trivially satisfies the 0-step lower bound. -/
theorem kStepLowerBound_zero {n : Nat} (s : RouteState n) :
    kStepLowerBound 0 s := by
  intro i m _
  simp

/-- Helper: if j.val ≥ b and k.val ≥ b, then for a `minDist` over the
    pair `[j, k]`, the result (if finite) is ≥ b. Generalises
    `minDist_pair_ge` (which is `private` in RouteProofs).  -/
private theorem minDist_pair_ge_arb {n : Nat} (dist : Fin n → DistVal)
    (j k : Fin n) (bound : Nat)
    (hlb : ∀ i : Fin n, ∀ mv : Nat, dist i = .fin mv → mv ≥ Nat.min bound i.val)
    (hjb : j.val ≥ bound) (hkb : k.val ≥ bound)
    (m : Nat) (hm : minDist dist [j, k] = .fin m) : m ≥ bound := by
  simp only [minDist] at hm
  cases hdj : dist j with
  | inf =>
    rw [hdj, DistVal.dmin_inf_left] at hm
    have := hlb k m hm
    -- m ≥ min bound k.val; combined with k.val ≥ bound, m ≥ bound
    have hmin : Nat.min bound k.val = bound := by
      simp [Nat.min_def]; omega
    rw [hmin] at this; exact this
  | fin mj =>
    cases hdk : dist k with
    | inf =>
      rw [hdj, hdk, DistVal.dmin_inf_right] at hm
      cases hm
      have := hlb j m hdj
      have hmin : Nat.min bound j.val = bound := by
        simp [Nat.min_def]; omega
      rw [hmin] at this; exact this
    | fin mk =>
      rw [hdj, hdk, DistVal.dmin_fin_fin_eq] at hm
      cases hm
      have hmj_ge := hlb j mj hdj
      have hmk_ge := hlb k mk hdk
      have hminj : Nat.min bound j.val = bound := by
        simp [Nat.min_def]; omega
      have hmink : Nat.min bound k.val = bound := by
        simp [Nat.min_def]; omega
      rw [hminj] at hmj_ge
      rw [hmink] at hmk_ge
      simp [Nat.min_def]; split <;> omega

/-- The step case of `kStepLowerBound`: a `routeTS` step strengthens the
    lower bound from k to k+1, provided all cells are non-failed. -/
theorem kStepLowerBound_step (n : Nat) (k : Nat) (s s' : RouteState n)
    (hff : ∀ i : Fin n, s.failed i = false)
    (hlb : kStepLowerBound k s)
    (hstep : (routeTS n).next s s') :
    kStepLowerBound (k + 1) s' := by
  intro i m hm
  obtain ⟨_hfail_eq, htarget, _hfailed_cells, hothers⟩ := hstep
  by_cases hiz : i.val = 0
  · -- target cell: dist = fin 0, so m = 0 ≥ min(k+1, 0) = 0
    rw [(htarget i hiz).1] at hm; cases hm
    simp [hiz]
  · have hipos : i.val > 0 := by omega
    have hstep_i := hothers i (hff i) hiz
    rw [nonFailedNeighbors_eq_neighbors1D s.failed i hff] at hstep_i
    rw [hstep_i.1] at hm
    -- m = (minDist s.dist (neighbors1D i)).succ.  Need m ≥ min(k+1, i.val).
    cases hmd : minDist s.dist (neighbors1D i) with
    | inf => rw [hmd, DistVal.succ_inf] at hm; cases hm
    | fin md =>
      rw [hmd, DistVal.succ_fin] at hm; cases hm
      -- Goal: md + 1 ≥ min(k+1, i.val)
      -- Strategy: show md ≥ min(k, i.val - 1), then +1 gives min(k+1, i.val).
      -- Introduce a reusable equality: min(k, i-1) + 1 = min(k+1, i.val)
      -- (for i.val > 0, which we have via hipos)
      have hmin_eq : Nat.min k (i.val - 1) + 1 = Nat.min (k + 1) i.val := by
        rcases Nat.le_total k (i.val - 1) with hc | hc
        · have hL : Nat.min k (i.val - 1) = k := Nat.min_eq_left hc
          have hR : Nat.min (k + 1) i.val = k + 1 := Nat.min_eq_left (by omega)
          rw [hL, hR]
        · have hL : Nat.min k (i.val - 1) = i.val - 1 := Nat.min_eq_right hc
          have hR : Nat.min (k + 1) i.val = i.val := Nat.min_eq_right (by omega)
          rw [hL, hR]; omega
      by_cases hright : i.val + 1 < n
      · -- interior: neighbors = [i-1, i+1]
        rw [neighbors1D_interior i hipos hright] at hmd
        have hmd_ge : md ≥ Nat.min k (i.val - 1) := by
          apply minDist_pair_ge_arb s.dist _ _ (Nat.min k (i.val - 1)) _ _ _ md hmd
          · intro j mv hj
            have h1 := hlb j mv hj  -- mv ≥ min k j.val
            -- Goal: mv ≥ min (min k (i.val - 1)) j.val
            -- Extract concrete bounds from h1 via case-split.
            have h1a : mv ≥ k ∨ mv ≥ j.val := by
              rcases Nat.le_total k j.val with hkj | hkj
              · left
                have heq : Nat.min k j.val = k := Nat.min_eq_left hkj
                omega
              · right
                have heq : Nat.min k j.val = j.val := Nat.min_eq_right hkj
                omega
            have hL : Nat.min k (i.val - 1) ≤ k := Nat.min_le_left _ _
            have hX1 : Nat.min (Nat.min k (i.val - 1)) j.val ≤ Nat.min k (i.val - 1) :=
              Nat.min_le_left _ _
            have hX2 : Nat.min (Nat.min k (i.val - 1)) j.val ≤ j.val :=
              Nat.min_le_right _ _
            omega
          · -- Goal: (⟨i.val - 1, _⟩ : Fin n).val ≥ min k (i.val - 1)
            have h : Nat.min k (i.val - 1) ≤ i.val - 1 := Nat.min_le_right _ _
            show i.val - 1 ≥ Nat.min k (i.val - 1); omega
          · -- Goal: (⟨i.val + 1, _⟩ : Fin n).val ≥ min k (i.val - 1)
            have h : Nat.min k (i.val - 1) ≤ i.val - 1 := Nat.min_le_right _ _
            show i.val + 1 ≥ Nat.min k (i.val - 1); omega
        -- Combine: md ≥ min k (i-1); goal md + 1 ≥ min (k+1) i.val
        omega
      · -- last cell: neighbors = [i-1]
        rw [neighbors1D_last i hipos hright] at hmd
        simp only [minDist] at hmd
        have h_left_lb := hlb ⟨i.val - 1, by omega⟩ md hmd
        -- h_left_lb : md ≥ min k (i.val - 1) (after reducing ⟨i.val-1,_⟩.val)
        have h_left_lb' : md ≥ Nat.min k (i.val - 1) := h_left_lb
        omega

/-- After k steps from an arbitrary failure-free start, the step-indexed
    lower bound holds. -/
theorem kStepLowerBound_at_k (n : Nat) :
    ∀ k s₀ s, ReachableFromInK s₀ k s →
      (∀ i : Fin n, s₀.failed i = false) →
      kStepLowerBound k s := by
  intro k s₀ s hr hff
  induction hr with
  | refl => exact kStepLowerBound_zero s₀
  | step t t' j hr_t hstep ih =>
    -- Need: failed is uniformly false at t so kStepLowerBound_step applies
    have hff_t : ∀ i : Fin n, t.failed i = false :=
      reachableFromInK_preserves_nonFailed n j s₀ t hr_t hff
    exact kStepLowerBound_step n j t t' hff_t ih hstep

/- ------------------------------------------------------------------- -/
/- Self-stabilization of Route (paper Corollary 7, 1D failure-free).   -/

/-- ★ SELF-STABILIZATION (paper Corollary 7, 1D failure-free case).
    Starting from ANY RouteState in which no cell is failed, after k+1
    rounds of `routeTS`, every cell at distance ≤ k from the target has
    `dist i = .fin i.val`.

    Compared to `route_convergence`, this theorem starts from an
    arbitrary initial state (not just the canonical `routeFFTS.init`),
    capturing the paper's "stabilizing" claim: the system recovers
    correct routing state even from a garbage configuration. The `+1`
    in `k + 1` accounts for the first step establishing the target's
    `dist = .fin 0` (prior to which `s₀.dist 0` could have been anything).

    Proof by induction on k, mirroring `route_convergence`:
    - At step 1 (k = 0): the target has `dist = fin 0` by the step
      relation.
    - At step k+2 (inductive step): the previous state has correct
      dist for cells at distance ≤ k (IH); `kStepLowerBound` gives the
      right neighbor at position i.val+1 dist ≥ i.val+1 (finite case);
      so the Bellman-Ford update picks the left neighbor, giving
      `.succ (fin (i.val - 1)) = fin i.val`. -/
theorem route_self_stabilizes (n : Nat) (_hn : n > 0) :
    ∀ k : Nat, ∀ s₀ s : RouteState n,
      (∀ i : Fin n, s₀.failed i = false) →
      ReachableFromInK s₀ (k + 1) s →
      ∀ i : Fin n, i.val ≤ k → s.dist i = .fin i.val := by
  intro k
  induction k with
  | zero =>
    -- After 1 step from s₀, the target has dist = fin 0.
    intro s₀ s hff hr i hle
    have hi : i.val = 0 := by omega
    cases hr with
    | step t s _k _hr_t hstep =>
      obtain ⟨_, htarget, _, _⟩ := hstep
      rw [(htarget i hi).1]; congr 1; omega
  | succ k ih =>
    -- After k+2 steps from s₀, cells at distance ≤ k+1 have correct dist.
    intro s₀ s' hff hr i hle
    cases hr with
    | step t _s' _k hr_t hstep =>
      obtain ⟨_, htarget, _hfailed_cells, hothers⟩ := hstep
      by_cases hiz : i.val = 0
      · rw [(htarget i hiz).1]; congr 1; omega
      · have hipos : i.val > 0 := by omega
        have hff_t : ∀ j : Fin n, t.failed j = false :=
          reachableFromInK_preserves_nonFailed n (k + 1) s₀ t hr_t hff
        have hstep_i := hothers i (hff_t i) hiz
        rw [nonFailedNeighbors_eq_neighbors1D t.failed i hff_t] at hstep_i
        rw [hstep_i.1]
        -- IH: cells at distance ≤ k in `t` have correct dist
        have hih := ih s₀ t hff hr_t
        suffices hmid : minDist t.dist (neighbors1D i) = .fin (i.val - 1) by
          rw [hmid, DistVal.succ_fin]; congr 1; omega
        -- Left neighbor converged by IH (i - 1 ≤ k)
        have hleft_dist : t.dist ⟨i.val - 1, by omega⟩ = .fin (i.val - 1) := by
          have h := hih ⟨i.val - 1, by omega⟩ (by simp; omega)
          simp at h; exact h
        -- Step-indexed lower bound on `t`: m ≥ min(k+1, j.val)
        have hlb := kStepLowerBound_at_k n (k + 1) s₀ t hr_t hff
        by_cases hright : i.val + 1 < n
        · -- interior: neighbors = [i-1, i+1]
          rw [neighbors1D_interior i hipos hright, minDist_pair, hleft_dist]
          cases hdr : t.dist ⟨i.val + 1, hright⟩ with
          | inf => exact DistVal.dmin_inf_right _
          | fin m =>
            -- m ≥ min(k+1, i+1); since i ≤ k+1, min(k+1, i+1) ≥ i.val
            have hge : m ≥ Nat.min (k + 1) (i.val + 1) := by
              have h1 := hlb ⟨i.val + 1, hright⟩ m hdr
              exact h1
            -- We need m ≥ i.val
            have hm_ge_i : m ≥ i.val := by
              have hmin_ge : Nat.min (k + 1) (i.val + 1) ≥ i.val := by
                simp [Nat.min_def]; split <;> omega
              omega
            rw [DistVal.dmin_fin_fin_eq]; congr 1; simp [Nat.min_def]; omega
        · -- last: neighbors = [i-1]
          rw [neighbors1D_last i hipos hright, minDist_singleton, hleft_dist]

/- ------------------------------------------------------------------- -/
/- Self-stabilization of next-hop (paper Corollary 7, full form).      -/

/-- ★ NEXT-HOP SELF-STABILIZATION (paper Corollary 7, 1D failure-free).
    Starting from ANY RouteState in which no cell is failed, after k+2
    rounds of `routeTS`, every non-target cell `i` with `i.val ≤ k+1`
    has `next i = some ⟨i.val - 1, _⟩` (points to the left neighbor).

    Why k+2 and not k+1 (as for dist)? Because `next i` at round k+2 is
    `argminDist t.dist (neighbors1D i)` where `t` is the state at round
    k+1; we need `t`'s dist values to be correct for i's neighbors at
    round k+1. By `route_self_stabilizes`, that requires the state at
    round k+1 to come from a start-state via (k+1)-step reachability,
    which is exactly what `ReachableFromInK s₀ (k + 2)` witnesses after
    peeling off the final step.  -/
theorem route_next_self_stabilizes (n : Nat) (hn : n > 0) :
    ∀ k : Nat, ∀ s₀ s : RouteState n,
      (∀ i : Fin n, s₀.failed i = false) →
      ReachableFromInK s₀ (k + 2) s →
      ∀ i : Fin n, i.val > 0 → i.val ≤ k + 1 →
        s.next i = some ⟨i.val - 1, by omega⟩ := by
  intro k s₀ s' hff hr i hipos hle
  cases hr with
  | step t _s' _k hr_t hstep =>
    obtain ⟨_, _htarget, _hfailed_cells, hothers⟩ := hstep
    have hiz : i.val ≠ 0 := by omega
    have hff_t : ∀ j : Fin n, t.failed j = false :=
      reachableFromInK_preserves_nonFailed n (k + 1) s₀ t hr_t hff
    have hstep_i := hothers i (hff_t i) hiz
    rw [nonFailedNeighbors_eq_neighbors1D t.failed i hff_t] at hstep_i
    rw [hstep_i.2]
    -- By route_self_stabilizes on t (reachable in k+1 steps), left neighbor
    -- at position i-1 ≤ k has correct dist.
    have hleft_dist : t.dist ⟨i.val - 1, by omega⟩ = .fin (i.val - 1) := by
      have h := route_self_stabilizes n hn k s₀ t hff hr_t
                  ⟨i.val - 1, by omega⟩ (by simp; omega)
      simp at h; exact h
    have hlb := kStepLowerBound_at_k n (k + 1) s₀ t hr_t hff
    by_cases hright : i.val + 1 < n
    · -- interior: neighbors = [i-1, i+1]
      rw [neighbors1D_interior i hipos hright]
      cases hdr : t.dist ⟨i.val + 1, hright⟩ with
      | inf =>
        exact argminDist_pair_left_inf t.dist _ _ (i.val - 1) hleft_dist hdr
      | fin m =>
        have h1 := hlb ⟨i.val + 1, hright⟩ m hdr
        -- h1 : m ≥ min (k + 1) (⟨i.val+1,_⟩.val) = min (k+1) (i.val+1)
        have hge : m ≥ Nat.min (k + 1) (i.val + 1) := h1
        have hm_ge_i : m ≥ i.val := by
          rcases Nat.le_total (k + 1) (i.val + 1) with hc | hc
          · have heq : Nat.min (k + 1) (i.val + 1) = k + 1 := Nat.min_eq_left hc
            rw [heq] at hge; omega
          · have heq : Nat.min (k + 1) (i.val + 1) = i.val + 1 := Nat.min_eq_right hc
            rw [heq] at hge; omega
        exact argminDist_pair_left_le t.dist _ _ (i.val - 1) m hleft_dist hdr
          (by omega)
    · -- last cell: neighbors = [i-1]
      rw [neighbors1D_last i hipos hright]
      exact argminDist_singleton_fin t.dist _ (i.val - 1) hleft_dist

end CellularFlows
