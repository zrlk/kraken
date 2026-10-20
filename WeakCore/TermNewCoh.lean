import WeakCore.TermReadClsDefs
import WeakCore.TermB5

/-! # TermNewCoh: `NewCohF`

A message a thread step appends at a label of the stepper's cut is at most the stepper's new
coherence at its location (in fact equal).  Every appended message is at a fresh label
(`FreshIn`, absent from the global store) or is written by the step's final write primitive:
`storeUnits` (`TermPiece.storeUnits_newCoh`), `stepRmw` (`stepRmw_newCoh`) or `stepRmwPair`
(`stepRmwPair_newCoh`), each of which sets coherence at the written location to the new
timestamp.
-/

namespace TermNewCoh

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermB5 TermReadClsDefs
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)

/-! ## §1 Final write primitives -/

theorem stepRmw_newCoh_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → mem'[t]? = some m → th'.vs.coh m.loc = t := by
  intro t m ht hm
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact absurd (TermMem.lt_of_get hm) (by omega)
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hl := TermMem.lt_of_get hm
        simp only [Array.size_push] at hl
        obtain rfl : t = mem.size := by omega
        rw [Array.getElem?_push_size, Option.some.injEq] at hm
        subst hm
        first
          | (rw [lockFence_coh]; simp)
          | (split <;> simp [Promises.stepFence])
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm' : mem[tw]? with
      | none => simp [hm'] at hf
      | some pm =>
          simp only [hm', Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨-, rfl, rfl⟩ := hf
          exact absurd (TermMem.lt_of_get hm) (by omega)

theorem stepRmw_newCoh {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → mem'[t]? = some m → th'.vs.coh m.loc = t := by
  exact stepRmw_newCoh_at (th := if arch = .tso then Promises.stepFence th .sy else th) h

theorem stepRmwPair_newCoh {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : WeakMem.Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → mem'[t]? = some m → th'.vs.coh m.loc = t := by
  intro t m ht hm
  rcases stepRmwPair_shape h with ⟨rfl, -⟩ | ⟨⟨m0, m1, rfl, h0, h1⟩, -, -, hc0, hc1⟩
  · exact absurd (TermMem.lt_of_get hm) (by omega)
  · have hlt := TermMem.lt_of_get hm
    simp only [Array.size_push] at hlt
    have g0 : ((mem.push m0).push m1)[mem.size]? = some m0 := by simp [Array.getElem?_push]
    have g1 : ((mem.push m0).push m1)[mem.size + 1]? = some m1 := by
      rw [show mem.size + 1 = (mem.push m0).size from (Array.size_push _).symm, Array.getElem?_push_size]
    rcases Nat.lt_or_ge t (mem.size + 1) with hl | hl
    · obtain rfl : t = mem.size := by omega
      rw [g0] at hm; cases hm
      rw [h0]; exact hc0
    · obtain rfl : t = mem.size + 1 := by omega
      rw [g1] at hm; cases hm
      rw [h1]; exact hc1

/-! ## §2 Operations -/

/-- New messages of `s'` (past `s`) sit at the coherence of `s'`. -/
def NC (s s' : St) : Prop :=
  ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → s'.vs.coh m.loc = t

theorem units_nc {k : Promises.Knobs} {arch : Arch} {pw : Word} {b : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {s s1 s' : St}
    (hm1 : s1.mem = s.mem) (hs : s' ∈ storeUnits k arch pw b rel us ws 0 s1) : NC s s' :=
  fun t m ht hm => TermPiece.storeUnits_newCoh us ws 0 s1 s' hs t m (by rw [hm1]; exact ht) hm

theorem evalOp_newCoh {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (hpl : PromLt s) (h : r ∈ evalOp g env σs s op) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      FreshIn g s.nalloc r.1.nalloc m.loc.label ∨ r.1.vs.coh m.loc = t := by
  intro t m ht hm
  have key : (∃ a v o rel, op = .store rel a v o) ∨ (∃ a v, op = .xchg a v) ∨
      (∃ bb i v, op = .xchgAt bb i v) ∨ (∃ bb i p v, op = .xchgAtF bb i p v) ∨
      (∃ bb i x, op = .bufInit bb i x) ∨ (∃ bb i v, op = .stl bb i v) ∨
      (∃ bb wi jl v, op = .stlw bb wi jl v) ∨ (∃ rel a v0 v1 tk, op = .stp rel a v0 v1 tk) ∨
      (∃ o acq rel a v, op = .fetch o acq rel a v) ∨ OpTgt op = [] := by
    cases op <;> simp [OpTgt]
  rcases key with ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | hO
  rotate_left 9
  · exact (evalOp_new hpl h t m ht hm).imp id (fun ⟨_, ha, _⟩ => by rw [hO] at ha; cases ha)
  all_goals
    right
    simp only [evalOp] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (simp only [List.mem_map] at h
         obtain ⟨s', hs, rfl⟩ := h
         exact units_nc rfl hs t m ht hm)
      | (simp only [List.mem_flatMap, List.mem_map] at h
         obtain ⟨x, hx, y, hy, rfl⟩ := h
         obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
         exact units_nc k1 hy t m ht hm)
      | (simp only [List.mem_flatMap] at h
         obtain ⟨x, hx, h⟩ := h
         split at h
         · simp only [List.mem_map] at h
           obtain ⟨y, hy, rfl⟩ := h
           obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
           exact units_nc k1 hy t m ht hm
         · simp at h)
      | (simp only [List.mem_map] at h
         obtain ⟨⟨mem', th'⟩, hx, rfl⟩ := h
         exact stepRmw_newCoh hx t m ht hm)

/-! ## §3 Thread steps -/

theorem tstep_newCoh {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hpl : PromLt (stOf mem pairs th)) (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → r.1[t]? = some m →
      FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨ r.2.2.vs.coh m.loc = t := by
  intro t m ht hm
  simp only [tstep] at h
  split at h <;> rename_i hT
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; dsimp only at hm
       exact absurd (TermMem.lt_of_get hm) (by omega))
    | (simp only [List.mem_singleton] at h; subst h; dsimp only [fenceS, stOf] at hm
       exact absurd (TermMem.lt_of_get hm) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm
       exact absurd (TermMem.lt_of_get hm) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm
       exact absurd (TermMem.lt_of_get hm) (by omega))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_newCoh hpl hx t m ht hm
         | exact .inr (stepRmw_newCoh hx t m ht hm)
         | (obtain ⟨mem', pairs', th'⟩ := x
            exact .inr (stepRmwPair_newCoh hx t m ht hm)))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact .inl ((newIn_projInj (X := fun _ => False) hpl hx hy t m ht hm).resolve_right id))

/-! ## §4 `NewCohF` -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

theorem tctx_newCoh : NewCohF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y t m cl ht hm hsto
  obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
  obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce2, -, -, -, -, -⟩ := hRE0
  have hmi : MemInv (gOf p k arch c i) (CE η2) (stOf c.mem c.pairs th) := by rw [hce2]; exact hm0
  rcases tstep_newCoh (MemInv_promLt hmi) X.hr t m ht hm with hF | hc
  · have hsG : Eg.sto m.loc.label = some cl := cutSto_sub (by rw [Y.1] at hsto; exact hsto)
    rw [(X.inv.gfresh X.hth r.2.2.nalloc _ hF).1] at hsG
    cases hsG
  · exact Nat.le_of_eq hc.symm

#print axioms tctx_newCoh

end

end TermNewCoh
