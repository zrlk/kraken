import WeakCore.TermInterf
import WeakCore.TermPlantF

/-!
# B5: `newPair` and `newForeignTyped` (ObligationsF fields N14, N13)

* `newPair_of : NewPairF` — a new message in a two-word unit (`TwoAtT`) of a cell
  comes as a recorded pair.  Operationally (`tstep_newR`, `tstep_newOp` keeping
  `storeUnits_roles`' `NewRole` and `stepRmwPair_shape`'s pair entry), typed
  (`UnitsAt`/`SWAt` of the written component), and by layout (`twoAt_twoAtT`: a
  component's two-word unit and a `TwoAtT` unit start together or are disjoint).
* `newForeignTyped_of : NewForeignTypedF` — B2 (`newMsg_wordOK_other`) on the
  step's own post `MemInv`, at an initialised offset; every write at another
  thread's cell is at an initialised offset (`ForeignIni`: buffer index ops need an
  `own` handle; every other write goes through a `ptr`/`loc` target, whose `VR`
  carries `IniAt`).
-/

namespace TermB5

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)

/-! ## 1. Operational: where a new message is, with its pair facts -/

/-- (B5) The role of a new message at word `j` of a unit list written from `b`,
with its pair facts: a one-word unit; a new pair start (recorded, second word
next); or a pair's second word after a new pair start at or past `n0`. -/
def RoleR (us : List Acc) (b : Address) (n0 : Nat) (mem : Memory) (pairs : List Ts) (t j : Nat) : Prop :=
  TermFul.OneAt us j ∨
  (TwoAt us j ∧ t ∈ pairs ∧ ∃ m1 : Msg, mem[t + 1]? = some m1 ∧ m1.loc = offs b (j + 1)) ∨
  (∃ (jj q : Nat) (m0 : Msg), j = jj + 1 ∧ TwoAt us jj ∧ t = q + 1 ∧ n0 ≤ q ∧ q ∈ pairs ∧
    mem[q]? = some m0 ∧ m0.loc = offs b jj)

theorem roleR_of {us : List Acc} {b : Address} {M0 : Nat} {s' : St} {t j : Nat}
    (h : NewRole us b 0 M0 s' t j) : RoleR us b M0 s'.mem s'.pairs t j := by
  rcases h with h | ⟨h1, h2, m1, h3, h4⟩ | ⟨jj, q, m0, h1, h2, h3, h4, h5, h6, h7⟩
  · exact .inl (oneAt_ful h)
  · exact .inr (.inl ⟨h1, h2, m1, h3, by rw [h4, Nat.zero_add]⟩)
  · exact .inr (.inr ⟨jj, q, m0, h1, h2, h3, h4, h5, h6, by rw [h7, Nat.zero_add]⟩)

/-- (B5) The write an operation's new message comes from: a `storeUnits` call
(`UnitsOp`), an `stp`'s pair, or a `fetch`'s RMW, from address `b` with units `us`. -/
def OpNewR (g : G) (env : Env) (s : St) (op : Op) (b : Address) (us : List Acc) : Prop :=
  (∃ pw rel ws, TermFul.UnitsOp g env s op pw b rel us ws) ∨
  (∃ rel a v0 v1 tk t pw, op = .stp rel a v0 v1 tk ∧ evalAt env a = some (t, [pw]) ∧
    addrOf pw = some b ∧ us = [.two]) ∨
  (∃ o acq rel a v t pw, op = .fetch o acq rel a v ∧ evalAt env a = some (t, [pw]) ∧
    addrOf pw = some b ∧ us = [.one])

/-- (B5) A new message of an operation at `loc`, in its role. -/
def NewR (g : G) (env : Env) (s : St) (op : Op) (mem : Memory) (pairs : List Ts) (t : Nat) (loc : Address) :
    Prop :=
  ∃ b us j, OpNewR g env s op b us ∧ loc = offs b j ∧ RoleR us b s.mem.size mem pairs t j

theorem units_newR {k : Promises.Knobs} {arch : Arch} {g : G} {env : Env} {op : Op} {pw : Word}
    {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {s s1 s' : St}
    (hm1 : s1.mem = s.mem) (hs : s' ∈ storeUnits k arch pw b rel us ws 0 s1)
    (hU : TermFul.UnitsOp g env s op pw b rel us ws) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → NewR g env s op s'.mem s'.pairs t m.loc := by
  intro t m ht hm
  obtain ⟨-, -, h3⟩ := storeUnits_roles us ws 0 s1 s' hs
  obtain ⟨j, hl, hr⟩ := h3 t m (by rw [hm1]; exact ht) hm
  rw [hm1] at hr
  exact ⟨b, us, j, .inl ⟨pw, rel, ws, hU⟩, by rw [hl, Nat.zero_add], roleR_of hr⟩

theorem evalOp_store_newR {g : G} {env : Env} {σs : List Ty} {s : St} {rel : Bool} {a v : At}
    {o : Option At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.store rel a v o)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      NewR g env s (.store rel a v o) r.1.mem r.1.pairs t m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_newR rfl hs (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_xchg_newR {g : G} {env : Env} {σs : List Ty} {s : St} {a v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.xchg a v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      NewR g env s (.xchg a v) r.1.mem r.1.pairs t m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
       exact units_newR k1 hy (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_xchgAt_newR {g : G} {env : Env} {σs : List Ty} {s : St} {bb i v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.xchgAt bb i v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      NewR g env s (.xchgAt bb i v) r.1.mem r.1.pairs t m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
       exact units_newR k1 hy (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_xchgAtF_newR {g : G} {env : Env} {σs : List Ty} {s : St} {bb i : At} {p : List Nat}
    {v : At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.xchgAtF bb i p v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      NewR g env s (.xchgAtF bb i p v) r.1.mem r.1.pairs t m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
       exact units_newR k1 hy (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_bufInit_newR {g : G} {env : Env} {σs : List Ty} {s : St} {bb i x : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.bufInit bb i x)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      NewR g env s (.bufInit bb i x) r.1.mem r.1.pairs t m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_newR rfl hs (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_stl_newR {g : G} {env : Env} {σs : List Ty} {s : St} {bb i v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.stl bb i v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      NewR g env s (.stl bb i v) r.1.mem r.1.pairs t m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
         exact units_newR k1 hy (by dsimp only [TermFul.UnitsOp]; fillx)
       · simp at h)

theorem evalOp_stlw_newR {g : G} {env : Env} {σs : List Ty} {s : St} {bb wi jl v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.stlw bb wi jl v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      NewR g env s (.stlw bb wi jl v) r.1.mem r.1.pairs t m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
         exact units_newR k1 hy (by dsimp only [TermFul.UnitsOp]; fillx)
       · simp at h)

theorem evalOp_stp_newR {g : G} {env : Env} {σs : List Ty} {s : St} {rel : Bool} {a v0 v1 tk : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.stp rel a v0 v1 tk)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      NewR g env s (.stp rel a v0 v1 tk) r.1.mem r.1.pairs t m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       intro t m ht hm
       obtain ⟨-, -, h3⟩ := storeUnits_roles _ _ 0 s s' hs
       obtain ⟨j, hl, hr⟩ := h3 t m ht hm
       exact ⟨_, _, j, .inr (.inl ⟨_, _, _, _, _, _, _, rfl, ‹_›, ‹_›, rfl⟩),
         by rw [hl, Nat.zero_add], roleR_of hr⟩)

theorem evalOp_fetch_newR {g : G} {env : Env} {σs : List Ty} {s : St} {o : FetchOp} {acq rel : Bool}
    {a v : At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.fetch o acq rel a v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      NewR g env s (.fetch o acq rel a v) r.1.mem r.1.pairs t m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨⟨mem', th'⟩, hx, rfl⟩ := h
       intro t m ht hm
       have hl := rmw_newLoc hx t m ht hm
       exact ⟨_, [.one], 0, .inr (.inr ⟨_, _, _, _, _, _, _, rfl, ‹_›, ‹_›, rfl⟩),
         by rw [TermStepper.offs_zero]; exact hl, .inl (.here _)⟩)

/-- **(B5, operation)**: every message an operation appends is at one of its
fresh labels or a `NewR` position. -/
theorem evalOp_newR {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (hpl : PromLt s) (h : r ∈ evalOp g env σs s op) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      FreshIn g s.nalloc r.1.nalloc m.loc.label ∨ NewR g env s op r.1.mem r.1.pairs t m.loc := by
  intro t m ht hm
  cases op
  case spawn => simp [evalOp] at h
  case store => exact .inr (evalOp_store_newR h t m ht hm)
  case xchg => exact .inr (evalOp_xchg_newR h t m ht hm)
  case xchgAt => exact .inr (evalOp_xchgAt_newR h t m ht hm)
  case xchgAtF => exact .inr (evalOp_xchgAtF_newR h t m ht hm)
  case bufInit => exact .inr (evalOp_bufInit_newR h t m ht hm)
  case stl => exact .inr (evalOp_stl_newR h t m ht hm)
  case stlw => exact .inr (evalOp_stlw_newR h t m ht hm)
  case stp => exact .inr (evalOp_stp_newR h t m ht hm)
  case fetch => exact .inr (evalOp_fetch_newR h t m ht hm)
  all_goals exact (evalOp_new hpl h t m ht hm).imp id (fun ⟨_, ha, _⟩ => by simp [OpTgt] at ha)

/-- A `casp` appends its two words as a recorded pair. -/
theorem rmwPair_newR {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : WeakMem.Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → mem'[t]? = some m →
      (m.loc = a ∧ t ∈ pairs' ∧ ∃ m1 : Msg, mem'[t + 1]? = some m1 ∧ m1.loc = a.next) ∨
      (m.loc = a.next ∧ ∃ (q : Nat) (m0 : Msg), t = q + 1 ∧ mem.size ≤ q ∧ q ∈ pairs' ∧
        mem'[q]? = some m0 ∧ m0.loc = a) := by
  intro t m ht hm
  rcases stepRmwPair_shape h with ⟨rfl, -⟩ | ⟨⟨m0, m1, rfl, h0, h1⟩, rfl, -⟩
  · exact absurd (lt_of_get hm) (by omega)
  · have hlt := lt_of_get hm
    simp only [Array.size_push] at hlt
    have g0 : ((mem.push m0).push m1)[mem.size]? = some m0 := by simp [Array.getElem?_push]
    have g1 : ((mem.push m0).push m1)[mem.size + 1]? = some m1 := by
      rw [show mem.size + 1 = (mem.push m0).size from (Array.size_push _).symm, Array.getElem?_push_size]
    have hp : mem.size ∈ pairs ++ [mem.size] := by simp
    rcases Nat.lt_or_ge t (mem.size + 1) with hl | hl
    · obtain rfl : t = mem.size := by omega
      rw [g0] at hm; cases hm
      exact .inl ⟨h0, hp, m1, g1, h1⟩
    · obtain rfl : t = mem.size + 1 := by omega
      rw [g1] at hm; cases hm
      exact .inr ⟨h1, mem.size, m0, rfl, Nat.le_refl _, hp, g0, h0⟩

/-- (B5) Where a thread step's new message at `loc` is, with its pair facts. -/
def TermNewR (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (mem' : Memory) (pairs' : List Ts) (t : Nat)
    (loc : Address) : Prop :=
  (∃ x op e, th.term = .let_ x op e ∧ NewR g th.env (stOf mem pairs th) op mem' pairs' t loc) ∨
  (∃ acq rel w e v tn ok fail tw pw, th.term = .cas acq rel w e v tn ok fail ∧
    evalAt th.env w = some (tw, [pw]) ∧ addrOf pw = some loc) ∨
  (∃ acq rel w e0 e1 v0 v1 tn ok fail tw pw A, th.term = .casp acq rel w e0 e1 v0 v1 tn ok fail ∧
    evalAt th.env w = some (tw, [pw]) ∧ addrOf pw = some A ∧
    ((loc = A ∧ t ∈ pairs' ∧ ∃ m1 : Msg, mem'[t + 1]? = some m1 ∧ m1.loc = A.next) ∨
     (loc = A.next ∧ ∃ (q : Nat) (m0 : Msg), t = q + 1 ∧ mem.size ≤ q ∧ q ∈ pairs' ∧
        mem'[q]? = some m0 ∧ m0.loc = A)))

/-- **(B5, thread step, operational, with pairs)**: every message a thread step
appends is at one of its fresh labels or a `TermNewR` position. -/
theorem tstep_newR {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hpl : PromLt (stOf mem pairs th)) (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → r.1[t]? = some m →
      FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨ TermNewR g mem pairs th r.1 r.2.1 t m.loc := by
  intro t m ht hm
  simp only [tstep] at h
  split at h <;> rename_i hT
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; dsimp only at hm; exact absurd (lt_of_get hm) (by omega))
    | (simp only [List.mem_singleton] at h; subst h; dsimp only [fenceS, stOf] at hm
       exact absurd (lt_of_get hm) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm
       exact absurd (lt_of_get hm) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm
       exact absurd (lt_of_get hm) (by omega))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact (evalOp_newR hpl hx t m ht hm).imp id (fun h => .inl ⟨_, _, _, hT, h⟩)
         | exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, _, _, hT, ‹_›,
             by rw [rmw_newLoc hx t m ht hm]; assumption⟩))
         | (obtain ⟨mem', pairs', th'⟩ := x
            exact .inr (.inr (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hT, ‹_›, ‹_›,
              rmwPair_newR hx t m ht hm⟩))))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact .inl ((newIn_projInj (X := fun _ => False) hpl hx hy t m ht hm).resolve_right id))

/-! ## 2. Typed: the written component, own or initialised (`ForeignIni`)

Copies of `TermTyped`'s `*_ua`/`fetch_sw`/`cas_sw` and `TermStepper`'s
`pair_ua`/`stp_ua`/`casp_ua`, keeping one more conjunct: the target cell is the
thread's own (buffer index ops: an `own` handle, `ModeOK`) or the component is
initialised (`IniAt η.ini`: a `ptr` targets a whole non-buffer cell, a `loc`
carries `IniAt (modeIni μ …)`). -/

open TermTyped

/-- (B5) Units `us` of a component `U` at `b` of `b`'s cell, which is the
thread's own or initialised at `b`. -/
def UnitsAtI (η : TEnv) (b : Address) (us : List Acc) : Prop :=
  ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ accs U = some us ∧
    (c.owner = some η.tid ∨ IniAt η.ini c b U)

/-- `ptr_target` with the target's initialisation. -/
theorem ptr_targetI {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ IniAt η.ini c b U := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VR hvars hp
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rcases ht with rfl | rfl
  · simp only [VR] at hv
    obtain ⟨a', c, hws, hoff, hsto, hcty, -, hacc⟩ := hv
    have hpw : pw.val = .loc a' 0 := by simpa using hws
    have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
    subst e
    refine ⟨c, c.ty, hsto, ?_, hcty, IniAt_of_ne fun N e' hc => hacc (by rw [hc]; simp [accs])⟩
    rw [hoff]; exact Fd_AtOff Fd.refl hacc
  · simp only [VR] at hv
    rcases hv with ⟨hws, -⟩ | ⟨a', c, U, hws, hsto, hat, hFd, -, hini⟩
    · have hpw : pw.val = .null := by simpa using hws
      simp [addrOf, hpw] at hb
    · have hpw : pw.val = .loc a' 0 := by simpa using hws
      have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
      subst e
      exact ⟨c, U, hsto, hat, hFd, IniAt_mono (fun l => modeIni_le_ini _ _ _ l) hini⟩

/-- `tgt_sw` with the target's initialisation. -/
theorem tgt_swI {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b)
    (hacc : accs (cl ρ η.wit 0 0 u) = some [.one]) : UnitsAtI η b [.one] := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := ptr_targetI hvars hp ht hea hb
  exact ⟨c, U, hsto, hat, (Fd_accs hFd).trans hacc, .inr hini⟩

theorem cell_uaI {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {a : At} {t u rt ru : Ty} {μ μr : Mode} {pw : Word} {b : Address}
    {us : List Acc}
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u)) (ho : cx.opaqueOK u = true)
    (hea : evalAt env a = some (rt, [pw])) (hcr : cellOf rt = some (μr, ru)) (hb : addrOf pw = some b)
    (hus : accs ru = some us) : UnitsAtI η b us := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := ptr_targetI hi.2.1 hp (cell_cases hc) hea hb
  have hacc : accs U = some us := by
    rw [Fd_accs hFd, ← pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc ho hea hcr,
      hus]
  exact ⟨_, _, hsto, hat, hacc, .inr hini⟩

theorem store_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {rl : Bool} {a v : At}
    {tok : Option At} {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.store rl a v tok) c') (hsc : OpScope cx (.store rl a v tok))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.store rl a v tok) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | storeOwn hp _ hc _ hu' hsub _ =>
      exact cell_uaI hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
  | storePub hp _ hc _ hu' hsub _ _ =>
      exact cell_uaI hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
  | storeRgn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeCap hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeWordGive hp hw | storeWordKeep hp hw | storeWordHand hp hw =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      rcases ht with rfl | rfl
      · exact cell_uaI hi hE htv hp rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus
      · exact cell_uaI hi hE htv hp rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus

theorem xchg_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {a v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchg a v) c') (hsc : OpScope cx (.xchg a v))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchg a v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | xchg hp hx hu' hsub _ =>
      cases hx with
      | rgn _ hc _ _ _ => exact absurd hc (hsc _ hp _ _)
      | own _ hc _ =>
          exact cell_uaI hi hE htv hp hc (sub_opaqueOK (hsub.elim id id)
            (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus

theorem xchgAt_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAt bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAt bb i v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, hea, hei, -, hbe, hnj, hb, hus, rfl⟩ := hu
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, c, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, hmo, -, -, -,
        htb, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      exact ⟨_, _, hsto, hat, (buf_accs hi hE hp hbuf ho htb hea hbe).symm.trans hus, .inl hmo⟩

theorem xchgAtF_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At} {q : List Nat}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAtF bb i q v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAtF bb i q v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, us0, c0, o0, hea, hei, -, hbe, hnj, hb, hus0, hco0, hus, rfl⟩ :=
    hu
  cases hop with
  | xchgAtF hp hbuf hct hopu _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, cc, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, hmo, -,
        hsku, hsig, htbu, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus0] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      obtain ⟨cR, o, hco, -, -, -, hato⟩ := compOff_rt q _ _ u0 us0 hct hsku hsig hus0
      rw [hco0] at hco
      simp only [Option.some.injEq, Prod.mk.injEq] at hco
      obtain ⟨rfl, rfl⟩ := hco
      refine ⟨_, _, hsto, ?_, (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho
        (lt_of_guardT (TermStep.tb_compTy q _ _ hct htbu) hi.2.2.2.2.1)).symm.trans
        ((accs_of_elyt (compOff_lyt q _ _ u0 c0 o0 hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2
          hco0)).symm.trans hus), .inl hmo⟩
      simpa [offs, Nat.add_assoc] using AtOff_trans hat hato

/-- (BII, shared; `bufInit_uaI`, `TermBiiF.bufInit_uaIP`) **Inversion of a typed `bufInit`'s units**: the
handle names an own cell at offset `0` of its location, the written slot `jv` (the index's value) is
below the buffer length, and the units start at that slot. -/
theorem bufInit_inv {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.bufInit bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.bufInit bb i v) pw b rel us ws) :
    ∃ rt rti wi ad c N U jv, evalAt env bb = some (rt, [pw]) ∧ pw.val = .loc ad 0 ∧
      evalAt env i = some (rti, [wi]) ∧ numOf [wi] = some jv ∧ b = offs ad (jv * nWords us) ∧
      η.sto ad.label = some c ∧ ModeOK η.tid η.pfr η.seen Mode.own ad.label c [pw] ∧
      IniAt (modeIni Mode.own η.ini η.rini) c ad (.array (.lit N) U) ∧ AtOff c.ty ad.offset (.array (.lit N) U) ∧
      jv < N ∧ accs U = some us := by
  obtain ⟨-, rt, t1, t2, iws, μ0, u0, j0, a0, μ', n', e', ψ, hea, hei, -, hbe, hnj, hb, hus, -, rfl⟩ := hu
  cases hop with
  | bufInit hu' hbuf hint heq hlt hu2 hsub _ =>
      obtain ⟨t, u, n, k, jj, c₁, tv, c₂, hu', hbuf, hint, heq, hlt, hu2, hsub⟩ :
          ∃ t u n k jj c₁ tv c₂, cx.use bb = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧
            IntIdx c₁ i jj ∧ EqI c₁ jj k ∧ LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u :=
        ⟨_, _, _, _, _, _, _, _, hu', hbuf, hint, heq, hlt, hu2, hsub⟩
      have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
        unfold bufOf at hbuf; split at hbuf
        · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
          obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
        · simp at hbuf
      subst ht
      have htu := use_TvOK hu' htv
      obtain ⟨hi1, rb, wsb, hea', hvb, hlb⟩ := use_FInv hu' hi
      have hJK : ev ρ jj = ev ρ k := heq ρ hi1.1
      have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wsi, hei', hvi, -⟩ := peek_VR hi1.2.1 hpi
      obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intS hti hvi)
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [VR] at hvb
      obtain ⟨hv, -⟩ := hvb
      rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, hmo, hini0⟩
      · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
        simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
        omega
      obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hwv : pw.val = .loc ad 0 := by simpa using hws
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      simp only [cl, clI_zero] at hat0 hini0
      have htb1 : tb c₁.ke.length u = true := by
        have h := htu.2.1
        rw [← htu.2.2] at h
        simp [tb] at h
        exact h
      have ho : c₁.opaqueOK u = true :=
        sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu2).1)
      have hacc : accs (cl ρ η.wit 0 0 u) = some us :=
        (accs_WitL hi1.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho (lt_of_guardT htb1 hi1.2.2.2.2.1)).symm.trans
          ((accs_of_elyt (buf_lyt hlb.2.2.2.2 hbe).2).symm.trans hus)
      exact ⟨_, _, wi, a0, c, _, _, _, hea, hwv, hei, hnj, rfl, hsto, hmo, hini0, hat0, by omega, hacc⟩

theorem bufInit_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.bufInit bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.bufInit bb i v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, -, -, ad, c, N, U, jv, -, -, -, -, rfl, hsto, hmo, -, hat0, hjv, hacc⟩ :=
    bufInit_inv hop hi hE htv hu
  have hel := AtOff.elem (n := N) hacc hjv (AtOff.here (Or.inl (by simp [hacc])))
  refine ⟨_, _, hsto, ?_, hacc, .inl hmo⟩
  simpa [offs] using AtOff_trans hat0 hel

theorem stl_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stl bb i v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stl bb i v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rfl, rt, t1, t2, iws, vs, μ0, u0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, hbe, hnj, -,
    hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stl hp hbuf hlo hint hlt hltk _ _ _ =>
      obtain ⟨t, u, n, k, jj, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jj q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i jj ∧
          LtI cx jj (.smul q.2.lanes n) ∧ LtI cx jj (.smul q.2.lanes k) :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu hlt hltk
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wwi, hei', hwi, -⟩ := atom_num hi.2.1 hpi hti
      have hJ0 : ev ρ jj < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
      have hJk0 : ev ρ jj < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
      have hJ : ev ρ jj / w.lanes < ev ρ n :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
      have hJk : ev ρ jj / w.lanes < ev ρ k :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
      obtain ⟨rt', pw', ad, c, μr, ur, us', hea', hwv, hbe', hus', hsto, hat, hmo, -, hsku, -⟩ :=
        slot_viewN (ev ρ jj / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
      obtain ⟨rfl, rfl⟩ := hlo0
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jj / w.lanes * nWords [Acc.one] = ev ρ jj / w.lanes := by simp [nWords, Acc.size]
      rw [e1] at hat
      exact ⟨_, _, hsto, hat, by simp [cl, accs], .inl hmo⟩

theorem stlw_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb wi jl v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stlw bb wi jl v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stlw bb wi jl v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rfl, rt, t1, t2, t3, iws, jws, vs, μ0, u0, i0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, -,
    hbe, hni, -, -, hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk _ _ _ _ _ =>
      obtain ⟨t, u, n, k, jw, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jw q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
          LtI cx jw n ∧ LtI cx jw k :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨rt', w', ad, c, μr, ur, us', rti, wwi, hea', hwv, hei', hni', hbe', hus', hsto, hat, hmo, -,
        hsku, -, -, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hni] at hni'
      simp only [Option.some.injEq] at hni'
      subst hni'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
      rw [e1] at hat
      exact ⟨_, _, hsto, hat, by simp [cl, accs], .inl hmo⟩

theorem fetch_swI {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool}
    {a v : At} {t : Ty} {pw : Word} {loc : Address}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some loc) : UnitsAtI η loc [.one] := by
  cases hop with
  | fetchCell hp _ hc =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_swI hi.2.1 hp (cell_cases hc) hea hb (by simp [cl, accs])
      · exact tgt_swI hi.2.1 hp (cell_cases hc) hea hb (by simp [cl, accs])
  | fetchEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ := word_mode ht ht' hμ'
      exact tgt_swI hi.2.1 hp ht hea hb
        (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep])
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact tgt_swI hi.2.1 hp ht hea hb (by simp [cl, accs, hok.1.1.1.1])

theorem cas_swI {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String}
    {ok fail : Expr} {t : Ty} {pw : Word} {loc : Address}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some loc) : UnitsAtI η loc [.one] := by
  cases hT with
  | casCell hp _ hc hraw =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_swI hi.2.1 hp (cell_cases hc) hea hb (accs_cl_one hraw)
      · exact tgt_swI hi.2.1 hp (cell_cases hc) hea hb (accs_cl_one hraw)
  | casShare hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_swI hi.2.1 hp ht hea hb (by simp [cl, accs, hg])
  | casTake hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_swI hi.2.1 hp ht hea hb (by simp [cl, accs, hg])
  | casEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      rcases hsc _ hp with ⟨μ', r', P', ht', hμ'⟩ | ⟨u, -, hnw⟩
      · have hμ := word_mode ht ht' hμ'
        exact tgt_swI hi.2.1 hp ht hea hb
          (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep])
      · rw [hw] at hnw; cases hnw


/-- `pair_ua` with the target's initialisation. -/
theorem pair_uaI {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) : UnitsAtI η b [.two] := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := ptr_targetI hvars hp ht hea hb
  refine ⟨c, U, hsto, hat, (Fd_accs hFd).trans ?_, .inr hini⟩
  rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [cl, accs]

theorem stp_uaI {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {x : String} {rel : Bool} {a v0 v1 tk : At} {t : Ty} {pw : Word}
    {b : Address} (hop : OpT p cx x (.stp rel a v0 v1 tk) c') (hsc : OpScope cx (.stp rel a v0 v1 tk))
    (hi : FInv ρ η σs K cx env) (hea : evalAt env a = some (t, [pw])) (hb : addrOf pw = some b) :
    UnitsAtI η b [.two] := by
  have hp : ∃ t, cx.peek a = .ok t := by cases hop <;> exact ⟨_, ‹_›⟩
  obtain ⟨t', hp⟩ := hp
  obtain ⟨μ, r, P, ht, -⟩ := hsc t' hp
  exact pair_uaI hi.2.1 hp ht (.inl ⟨r, P, rfl⟩) hea hb

theorem casp_uaI {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {acq rel : Bool} {w e0 e1 v0 v1 : At} {tn : String} {ok fail : Expr}
    {tw : Ty} {pw : Word} {A : Address}
    (hT : Typed p cx (.casp acq rel w e0 e1 v0 v1 tn ok fail))
    (hsc : StepScope cx (.casp acq rel w e0 e1 v0 v1 tn ok fail))
    (hi : FInv ρ η σs K cx env) (hea : evalAt env w = some (tw, [pw])) (hb : addrOf pw = some A) :
    UnitsAtI η A [.two] := by
  have hp : ∃ t, cx.peek w = .ok t := by cases hT <;> exact ⟨_, ‹_›⟩
  obtain ⟨t, hp⟩ := hp
  obtain ⟨μ, u, ht, -, hu⟩ := hsc t hp
  exact pair_uaI hi.2.1 hp ht hu hea hb

/-- The dispatcher over the `storeUnits`-issuing ops. -/
theorem unitsOp_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {op : Op}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x op c') (hsc : OpScope cx op)
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s op pw b rel us ws) : UnitsAtI η b us := by
  cases op
  case store => exact store_uaI hop hsc hi hE htv hu
  case xchg => exact xchg_uaI hop hsc hi hE htv hu
  case xchgAt => exact xchgAt_uaI hop hi hE htv hu
  case xchgAtF => exact xchgAtF_uaI hop hi hE htv hu
  case bufInit => exact bufInit_uaI hop hi hE htv hu
  case stl => exact stl_uaI hop hi htv hu
  case stlw => exact stlw_uaI hop hi htv hu
  all_goals simp [TermFul.UnitsOp] at hu

/-- (B5) A typed new position with its role. -/
def NewPosR (η : TEnv) (n0 : Nat) (mem : Memory) (pairs : List Ts) (t : Nat) (loc : Address) : Prop :=
  ∃ b us j, UnitsAtI η b us ∧ loc = offs b j ∧ RoleR us b n0 mem pairs t j

theorem twoAt_two0 : TwoAt [.two] 0 := ⟨0, rfl, rfl⟩

/-- **(B5, thread step, typed, with pairs)**: every message a typed, in-scope
thread's step appends is at one of its fresh labels or at a `NewPosR`. -/
theorem tstep_newPosR {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {r : Memory × List Ts × TTh} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → r.1[t]? = some m →
      FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨ NewPosR η mem.size r.1 r.2.1 t m.loc := by
  intro t m ht hmt
  refine (tstep_newR (MemInv_promLt hm) h t m ht hmt).imp id ?_
  rintro (⟨x, op, e, hterm, b, us, j, hn, hl, hr⟩ | ⟨acq, rel, w, e, v, tn, ok, fail, tw, pw, hterm, hea, hb⟩ |
      ⟨acq, rel, w, e0, e1, v0, v1, tn, ok, fail, tw, pw, A, hterm, hea, hb, hl⟩)
  · rw [hterm] at hT hsc
    cases hT with
    | let_ hop _ =>
        refine ⟨b, us, j, ?_, hl, hr⟩
        rcases hn with ⟨pw, rel, ws, hu⟩ | ⟨rel, a, v0, v1, tk, t', pw, rfl, hea, hb, rfl⟩ |
            ⟨o, acq, rel, a, v, t', pw, rfl, hea, hb, rfl⟩
        · exact unitsOp_uaI hop hsc hi hE htv hu
        · exact stp_uaI hop hsc hi hea hb
        · exact fetch_swI hop hsc hi hE htv hm hea hb
  · rw [hterm] at hT hsc
    exact ⟨m.loc, [.one], 0, cas_swI hT hsc hi hE htv hm hea hb, (TermStepper.offs_zero _).symm, .inl (.here _)⟩
  · rw [hterm] at hT hsc
    have hua := casp_uaI hT hsc hi hea hb
    rcases hl with ⟨hl, ht1, m1, h1, hl1⟩ | ⟨hl, q, m0, hq, hle, hqp, h0, hl0⟩
    · exact ⟨A, [.two], 0, hua, by rw [hl, TermStepper.offs_zero], .inr (.inl ⟨twoAt_two0, ht1, m1, h1, hl1⟩)⟩
    · exact ⟨A, [.two], 1, hua, hl, .inr (.inr ⟨0, q, m0, rfl, twoAt_two0, hq, hle, hqp, h0,
        by rw [hl0, TermStepper.offs_zero]⟩)⟩


/-! ## 3. Layout and initialisation -/

/-- Inside one laid-out segment: a two-word unit of a component (at `o`) and a
two-word unit of the segment start together or are disjoint. -/
theorem twoAt_twoAt_seg {S U : Ty} {o jj o' : Nat} {L us : List Acc} (h1 : AtOff S o U)
    (hL : accs S = some L) (hus : accs U = some us) (hj : TwoAt us jj) (htw : TwoAt L o') :
    (o + jj = o' ∨ o + jj + 2 ≤ o' ∨ o' + 2 ≤ o + jj) ∧ o + jj + 2 ≤ nWords L := by
  obtain ⟨pre, post, e, hn⟩ := AtOff_embed h1 hL hus
  have h2 : TwoAt L (o + jj) := by
    have := TwoAt_embed (pre := pre) (post := post) hj
    rw [← e, hn] at this; exact this
  exact ⟨twoAt_twoAt h2 htw, TwoAt_lt h2⟩

/-- **Layout (B5)**: a two-word unit of a component `U` (at `o`) of `T` and a
two-word unit of `T` (`TwoAtT`) start at the same word or are disjoint. -/
theorem twoAt_twoAtT {T U : Ty} {o jj o2 : Nat} {us : List Acc} (h1 : AtOff T o U) (hus : accs U = some us)
    (hj : TwoAt us jj) (h2 : TwoAtT T o2) : o + jj = o2 ∨ o + jj + 2 ≤ o2 ∨ o2 + 2 ≤ o + jj := by
  obtain ⟨b, S, L, o', hseg, hL, htw, rfl⟩ := h2
  rcases hseg with ⟨rfl, rfl, -⟩ | ⟨N, usS, jS, rfl, husS, hjS, rfl⟩
  · have := (twoAt_twoAt_seg h1 hL hus hj htw).1; omega
  · rw [hL] at husS; cases husS
    rcases AtOff_arr_elem h1 rfl with hU | ⟨us', j', o'', hus', hj', ho, hat⟩
    · subst hU; simp [accs] at hus
    · rw [hL] at hus'; cases hus'
      obtain ⟨hc, hb⟩ := twoAt_twoAt_seg hat hL hus hj htw
      have hlt := TwoAt_lt htw
      subst ho
      rcases Nat.lt_trichotomy j' jS with hlt' | rfl | hgt
      · have hm : (j' + 1) * nWords L ≤ jS * nWords L := Nat.mul_le_mul_right _ hlt'
        rw [Nat.succ_mul] at hm
        omega
      · omega
      · have hm : (jS + 1) * nWords L ≤ j' * nWords L := Nat.mul_le_mul_right _ hgt
        rw [Nat.succ_mul] at hm
        omega

theorem roleR_lt {us : List Acc} {b : Address} {n0 : Nat} {mem : Memory} {pairs : List Ts} {t j : Nat}
    (h : RoleR us b n0 mem pairs t j) : j < nWords us := by
  rcases h with h | ⟨h, -⟩ | ⟨jj, -, -, rfl, h, -⟩
  · exact TermFul.OneAt_lt h
  · have := TwoAt_lt h; omega
  · have := TwoAt_lt h; omega

theorem offs_eq_mk {b : Address} {j : Nat} {l : AllocLabel} {o : Nat} (h : offs b j = ⟨l, o⟩) :
    b.label = l ∧ ∀ x : Nat, b.offset = x → x + j = o := by
  cases b with
  | mk bl bo =>
    simp only [offs, Address.mk.injEq] at h
    exact ⟨h.1, fun x hx => by subst hx; exact h.2⟩

theorem offs_mk_eq {b : Address} {j : Nat} {l : AllocLabel} {o : Nat} (hl : b.label = l)
    (ho : ∀ x : Nat, b.offset = x → x + j = o) : offs b j = ⟨l, o⟩ := by
  cases b with
  | mk bl bo => simp only [offs, Address.mk.injEq]; exact ⟨hl, ho bo rfl⟩

/-- **(ForeignIni)** A word of an initialised component (`IniAt`) is at an
initialised offset (`InitR`). -/
theorem initR_of_iniAt {E : TEnv} {c : Cell} {b : Address} {U : Ty} {us : List Acc} {j : Nat}
    (hini : IniAt E.ini c b U) (hus : accs U = some us) (hj : j < nWords us) :
    InitR E c b.label (b.offset + j) := by
  intro N e us' hT hus'
  obtain ⟨x, hx⟩ : ∃ x : Nat, b.offset = x := ⟨_, rfl⟩
  rw [hx]
  rcases hini N e hT with ⟨hU, -⟩ | ⟨us2, j2, o, hus2, hj2, hjo, hato⟩
  · rw [hU, hT] at hus; simp [accs] at hus
  · rw [hus'] at hus2; cases hus2
    rw [hx] at hjo
    have hb : o + nWords us ≤ nWords us' := by
      obtain ⟨pre, post, e1, hn⟩ := AtOff_embed hato hus' hus
      subst e1; subst hn
      simp only [TermSound.nWords_append]; omega
    have h2 : (j2 + 1) * nWords us' ≤ E.ini b.label * nWords us' := Nat.mul_le_mul_right _ hj2
    rw [Nat.succ_mul] at h2
    omega

theorem initR_mono {E E' : TEnv} {c : Cell} {l : AllocLabel} {o : Nat} (hi : E.ini l ≤ E'.ini l)
    (h : InitR E c l o) : InitR E' c l o :=
  fun N e us hT hus => Nat.lt_of_lt_of_le (h N e us hT hus) (Nat.mul_le_mul_right _ hi)

/-! ## 4. At a reachable thread step -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **(B5 at the system)** every new message of a thread step is at a fresh label
of the stepper or at a `NewPosR` of one of its cuts. -/
theorem tctx_newPosR {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) :
    ∀ (t : Nat) (m : Msg), c.mem.size ≤ t → c'.mem[t]? = some m →
      FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label ∨
        ∃ S0, NewPosR (Cut Eg i S0) c.mem.size c'.mem c'.pairs t m.loc := by
  intro t m ht hm
  obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
  have hmt : r.1[t]? = some m := by rw [← X.e1]; exact hm
  obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce2, hEO2, hTy2, hTv2, hF2, hRt2, -⟩ := hRE0
  have Y2 : EnvAt p Eg i th (Tot i) S0 ρ2 η2 cx2 Rf2 Rs2 :=
    ⟨hce2, congrArg TEnv.tid hce2, hEO2, hTy2, hTv2, hF2, hRt2⟩
  have hm2 : MemInv (gOf p k arch c i) (CE η2) (stOf c.mem c.pairs th) := by rw [hce2]; exact hm0
  have hs : StepScope cx2 th.term := by
    rcases hsc X Y2 with hs | hR
    · exact hs
    · have hk : r.1 = c.mem := (frame_keep hR hTy2.1 hTy2.2 hF2 hEO2 hTv2 hm2 r X.hr).1
      rw [hk, Array.getElem?_eq_none ht] at hmt; cases hmt
  have hFi : FInv ρ2 η2 th.σs (Resume p th.stack) cx2 th.env :=
    FInvR_FInv (hTv2.2.2.2.2.2.2.2)
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs2 E rd ws R h) hF2
  rcases tstep_newPosR hEO2 hTy2.1 hTv2 hFi hm2 hs X.hr t m ht hmt with hF | hN0
  · exact .inl hF
  · right
    refine ⟨S0, ?_⟩
    have hN : NewPosR (Cut Eg (gOf p k arch c i).i S0) c.mem.size r.1 r.2.1 t m.loc := by
      rw [← hce2]; exact hN0
    rw [X.e1, X.e2]; exact hN

/-- **N14 `newPair`** (B5): new messages in a two-word unit of a cell come as
recorded pairs. -/
theorem newPair_of (hsc : StepScopeF p k arch Sp Init MintOK c0) : NewPairF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z t m l o cl ht hm hc htw
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  have key : ∀ o', m.loc = ⟨l, o'⟩ → ∃ b us j, (∃ U, AtOff cl.ty b.offset U ∧ accs U = some us) ∧
      b.label = l ∧ (∀ x : Nat, b.offset = x → x + j = o') ∧ RoleR us b c.mem.size c'.mem c'.pairs t j := by
    intro o' hlo
    rcases tctx_newPosR hsc X t m ht hm with hF | ⟨S0, b, us, j, ⟨c1, U, hsto, hat, hus, -⟩, hl, hr⟩
    · rw [hlo] at hF; rw [(hfr l hF).1] at hc; cases hc
    · obtain ⟨hbl, hbo⟩ := offs_eq_mk (hl.symm.trans hlo)
      have hc1 : Eg.sto b.label = some c1 := cutSto_sub hsto
      rw [hbl, hc] at hc1; cases hc1
      exact ⟨b, us, j, ⟨U, hat, hus⟩, hbl, hbo, hr⟩
  refine ⟨fun hlo => ?_, fun hlo => ?_⟩
  · obtain ⟨b, us, j, ⟨U, hat, hus⟩, hbl, hbo, hr⟩ := key o hlo
    obtain ⟨x, hx⟩ : ∃ x : Nat, b.offset = x := ⟨_, rfl⟩
    have hbo' := hbo x hx
    rw [hx] at hat
    rcases hr with hj | ⟨hj, hp, m1, h1, hl1⟩ | ⟨jj, q, m0, rfl, hj, -, -, -, -, -⟩
    · have := (TermPlantF.oneAt_twoAtT hat hus hj htw).1; omega
    · exact ⟨hp, m1, h1, by rw [hl1]; exact offs_mk_eq hbl (fun y hy => by have := hbo y hy; omega)⟩
    · have := twoAt_twoAtT hat hus hj htw; omega
  · obtain ⟨b, us, j, ⟨U, hat, hus⟩, hbl, hbo, hr⟩ := key (o + 1) hlo
    obtain ⟨x, hx⟩ : ∃ x : Nat, b.offset = x := ⟨_, rfl⟩
    have hbo' := hbo x hx
    rw [hx] at hat
    rcases hr with hj | ⟨hj, -, -, -, -⟩ | ⟨jj, q, m0, rfl, hj, hq, hle, hqp, h0, hl0⟩
    · have := (TermPlantF.oneAt_twoAtT hat hus hj htw).2; omega
    · have := twoAt_twoAtT hat hus hj htw; omega
    · exact ⟨q, hq, hle, hqp, m0, h0, by rw [hl0]; exact offs_mk_eq hbl (fun y hy => by have := hbo y hy; omega)⟩

/-- **N13 `newForeignTyped`** (B2 at every offset): a new message at another
thread's cell is typed at the step's witness.  The cell is shared (it is in the
stepper's cut), the offset is initialised (`ForeignIni`: `UnitsAtI` of a cell
not the stepper's own gives `IniAt`), and B2 (`newMsg_wordOK_other`) applies at
the step's own post `MemInv`. -/
theorem newForeignTyped_of (hsc : StepScopeF p k arch Sp Init MintOK c0) : NewForeignTypedF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z t m l o cl ht hm hlo hc hown
  obtain ⟨S1, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
    rw [(hfr l hF).1] at hc; cases hc
  have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
    rw [← Y.1]; exact Z.1
  have hmt : r.1[t]? = some m := by rw [← X.e1]; exact hm
  rcases tctx_newPosR hsc X t m ht hm with hF | ⟨S0, b, us, j, ⟨c1, U, hsto, hat, hus, hoi⟩, hl, hr⟩
  · rw [hlo] at hF; exact absurd hF hnF
  obtain ⟨hbl, hbo⟩ := offs_eq_mk (hl.symm.trans hlo)
  have hc1 : cutSto Eg i l = some c1 := by rw [← hbl]; exact hsto
  have hcl : c1 = cl := by rw [cutSto_sub hc1] at hc; exact Option.some.inj hc
  subst hcl
  have hsh : Eg.Shared l := by
    rcases (cutSto_some.1 hc1).2 with h | h
    · exact absurd h hown
    · exact h
  obtain ⟨f, hpf⟩ := hsh
  have hI0 : InitR (Cut Eg i S0) c1 l o := by
    rcases hoi with h | h
    · exact absurd h hown
    · have e : b.offset + j = o := hbo _ rfl
      have := initR_of_iniAt h hus (roleR_lt hr); rw [hbl, e] at this; exact this
  have hsto' : E'.sto l = some c1 := by
    rcases hF0.2.2.1 l with e | ⟨hF, -⟩
    · rw [e]; exact cutSto_shared hc ⟨f, hpf⟩
    · exact absurd hF hnF
  have htid : E'.tid = i := hF0.2.1
  have hpf' : E'.pfr l = some f := by
    rcases hF0.2.2.2.2.2.1 l with e | ⟨e, -⟩ | ⟨hF, -, -⟩
    · rw [e]; exact hpf
    · exact absurd hpf (by rw [show Eg.pfr l = (Cut Eg i S).pfr l from rfl, e]; simp)
    · exact absurd hF hnF
  have hI : InitR E' c1 l o := initR_mono (hF0.2.2.2.2.1 l).1 hI0
  have hnp : t ∉ (stOf r.1 r.2.1 r.2.2).promises :=
    tstep_newNotProm (MemInv_promLt hm0) (MemInv_nopair hm0) X.hr ht
  exact newMsg_wordOK_other Z.2.2.1 hsto' (by rw [htid]; exact hown) hpf' (X.inv.frle l c1 f hc hpf) hI ht hnp
    hmt hlo

end

#print axioms tstep_newR
#print axioms ptr_targetI
#print axioms unitsOp_uaI
#print axioms tstep_newPosR
#print axioms twoAt_twoAtT
#print axioms initR_of_iniAt
#print axioms tctx_newPosR
#print axioms newPair_of
#print axioms newForeignTyped_of

/-! ## 5. `promNoTwoPost` and the `SysInvN` clause `PromNoTwoOK`

`PromNoTwoOK` (`TermMainDefs`, `SysInvN.promNoTwo`): its preservation by thread
steps, promise steps and its initial truth are proved below. -/

/-- `PromNoTwoOK` at the source of every reachable thread step. -/
def PromNoTwoTF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → PromNoTwoOK Eg c

/-- `PromNoTwoOK` holds where no thread has a promise. -/
theorem promNoTwoOK_init {Eg : GEnv} {c : Cfg} (h : ∀ (j : Nat) (th : TTh), c.ths[j]? = some th → th.promises = []) :
    PromNoTwoOK Eg c := by
  intro j th t m cl hj ht
  rw [h j th hj] at ht; cases ht

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`PromNoTwoOK` after a promise step**: the new promise by `promNoTwoP`
(`PromNoTwoPF`), old ones unchanged (the plant keeps `sto`). -/
theorem promNoTwoOK_promise (hnt : PromNoTwoPF p k arch Sp Init MintOK c0) {c : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address}
    {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (h : PromNoTwoOK Eg c) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) (n : Nat) :
    PromNoTwoOK (EgP Eg P N j n) (promise c j a v w) := by
  intro k' thk t m cl hk ht hm hsto o htw
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hmem : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [hpi.1]
  have hsto' : Eg.sto m.loc.label = some cl := hsto
  have hold : ∀ thk0, c.ths[k']? = some thk0 → t ∈ thk0.promises → m.loc.offset ≠ o ∧ m.loc.offset ≠ o + 1 :=
    fun thk0 hk0 ht0 => by
      have hlt := X.inv.plt k' thk0 t hk0 ht0
      rw [hmem, push_lt hlt] at hm
      exact h k' thk0 t m cl hk0 ht0 hm hsto' o htw
  by_cases hkj : k' = j
  · subst hkj
    rw [hpi.2.1] at hk; cases hk
    rcases List.mem_append.1 ht with ht | ht
    · exact hold th X.hth ht
    · simp only [List.mem_singleton] at ht; subst ht
      rw [hmem, Array.getElem?_push_size] at hm; cases hm
      exact hnt X cl hsto' o htw
  · rw [promise_other X.hth hkj] at hk
    exact hold thk hk ht

/-- **`PromNoTwoOK` after a thread step** (cells keep their types; the step's
promises are old ones).  A promise at a label the step allocates is the
stepper's (`GFreshL`, `PromsDisj`), fulfilled along its certificate from `c'`
by a single-word write (`certified_promTypedX` at the step's own post state,
stage A; `SWOne_holds`), a `.one` unit of a component, so in no `TwoAtT` unit. -/
theorem promNoTwoOK_thread (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : TermPlantF.CertRunT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (h : PromNoTwoOK Eg c) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PromNoTwoOK (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  intro k' thk t m cl hk ht hm hsto o htw
  obtain ⟨th0, hk0, hsub, hki, hnki⟩ := tctx_old X hk
  have ht0 := hsub t ht
  have hlt := X.inv.plt k' th0 t hk0 ht0
  have hm0 : c.mem[t]? = some m := by rw [← tctx_pre X t hlt]; exact hm
  by_cases hF : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label
  · obtain ⟨j0, hj0, hj1, hl0⟩ := hF
    have hfl := X.inv.fresh i th X.hth j0 hj0
    have htth : t ∈ th.promises := hfl.2.2.2.2 t m hm0 hl0
    have hkeq : k' = i := Classical.byContradiction fun hne =>
      X.inv.disj i k' th th0 t (Ne.symm hne) X.hth hk0 htth ht0
    subst hkeq
    obtain ⟨-, rfl⟩ := hki rfl
    have hsto' : E'.sto m.loc.label = some cl := by
      have e := post_sto_fresh (Eg := Eg) (E' := E') ⟨j0, hj0, hj1, hl0⟩
      rw [← e]; exact hsto
    have hAP := TermXFO.anchPost (hV0 := hV0) X Y.1 Z hS hPfr (hrun X S hS).1
    obtain ⟨hFt, hRE, hm', -⟩ := Z
    have hg : gOf p k arch c' k' = gOf p k arch c k' := TermTyped.gOf_thread X.hc'
    have hSC0 : StoClo (CE η) := by
      rw [Y.1]; exact fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
    have hbo : (gOf p k arch c' k').boxFence = true := by rw [hg]; exact X.inv.bf
    have hst : stOf c'.mem c'.pairs r.2.2 = stOf r.1 r.2.1 r.2.2 := by rw [X.e1, X.e2]
    have h0 := TermNoHold.InvAtXF_ofA (p := p) (k := k) (arch := arch) (Ea := Cut Eg k' S) X.e3 hRE.thInvE (by rw [hg, hst]; exact hm')
      (StoClo_EFoot hFt hSC0) hbo (by rw [hst]; exact hAP.1) (.inr hAP.2)
    obtain ⟨thx, E, hthx, hx, hTEx, hmx, hSCx, hbox, hfb, hfr, -, -, -, hIH0⟩ := h0
    have hX : InvAtX p k arch k' E' _ _ c' (Ea := Cut Eg k' S) := ⟨thx, E, hthx, hx, hTEx, hmx, hSCx, hbox, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
    have hsc := fun c1 h1 h2 => ((hrun X S hS).2 c1 h1 h2).1
    have hwin := fun c1 h1 h2 => ((hrun X S hS).2 c1 h1 h2).2
    have htp : t ∈ TermFul.promsOf c' k' := by rw [TermFul.promsOf_some X.e3]; exact ht
    obtain ⟨c1, c2, th1, th2, ρ1, η1, cx1, E2, -, -, -, -, -, -, hx1, hE, hT, htv, hi, hmi, hscope, hpa, -, -, -, -, -,
      -, -, hsw, -⟩ := certified_promTypedX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX (TermTyped.tidAt_mono hAP.2 (TermTyped.tidAt_thread X.hc' (TermMain.tidAt_cut X.inv k' S))) X.cert htp hm
    obtain ⟨cl1, o1, U, us, j1, hcl1, h1o, hus, hj, ho⟩ :=
      SWOne_holds p _ _ _ _ ρ1 η1 cx1 _ _ hE hT htv hi hmi (TermTyped.scopeD_SW hscope hsw) hpa hsw
    rw [hx1.2.2.2.2.1 _ _ hsto'] at hcl1
    cases hcl1
    have hoff : m.loc.offset = o1 + j1 := ho
    rw [hoff]
    exact TermPlantF.oneAt_twoAtT h1o hus hj htw
  · have hsto' : Eg.sto m.loc.label = some cl := by
      have e := post_sto_old (Eg := Eg) (E' := E') hF
      rw [← e]; exact hsto
    exact h k' th0 t m cl hk0 ht0 hm0 hsto' o htw

/-- **N6 `promNoTwoPost`**, given the candidate clause at the source of every
thread step (`PromNoTwoTF`): `promNoTwoOK_thread`, restricted to shared cells. -/
theorem promNoTwoPost_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : TermPlantF.CertRunT p k arch Sp Init MintOK c0)
    (hnt : PromNoTwoTF p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : PromNoTwoPostF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr k' thk t m hk ht hm cl hsto
    _ o htw
  exact promNoTwoOK_thread (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X Y Z hS hPfr (hnt X) k' thk t m cl hk ht hm hsto o htw

end

#print axioms promNoTwoOK_init
#print axioms promNoTwoOK_promise
#print axioms promNoTwoOK_thread
#print axioms promNoTwoPost_of

end TermB5
#print axioms TermB5.bufInit_inv
