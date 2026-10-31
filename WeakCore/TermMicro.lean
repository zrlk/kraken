/-
# TermMicro — the micro-step machine

One memory event per machine step.  `tstep` is factored as a pure *plan*
(`tstepP`, a tree of memory events whose later nodes are functions of the
earlier events' results), the *events* (`evSem`, each one `Promises` rule or
the allocator event) and a *commit* (the plan's leaf, a function of the local
state after the last event).  The micro machine (`tstepMμ`, `CfgM`, `StepM`)
performs one event per step; other threads interleave between events.

Nothing in `TermRun` changes: `tstep` and every lemma about it stay valid.

Built by check-promises.sh (`leanb TermMicro`).  The micro configuration
mirrors the coarse one: the thread capacity `Cfg.cap`/`Cfg.n` (labels are
striped by it), the proof-only `G.zf`/`G.pf` fields, the `δ` output of `TOut`,
and every field of `SysInvN` (see `SysInvMμ`).  The micro core (`evalOp_eq`,
`tstep_plan`, `tstep_eq_run`) is independent of the details of the store,
load and RMW rules: it holds unchanged with store forwarding (`VState.fwd`),
the successful-CAS result view and the x86 locked-RMW leading fence.
-/
import WeakCore.TermMain

namespace TermMicro

open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §1 Memory events -/

/-- One memory event, with exactly the arguments `TermRun` passes to the
machine rule (scratch registers: 0 = address word, 1 and 2 = data). -/
inductive MemOp where
  | load (pw : Word) (a : Address) (acq : Bool)
  | loadPair (pw : Word) (a : Address) (acq : Bool)
  | store (pw : Word) (a : Address) (w : Word) (rel : Bool)
  | storePair (pw : Word) (a : Address) (w0 w1 : Word) (rel : Bool)
  | rmw (pw : Word) (a : Address) (kind : WeakMem.RmwKind) (nw : Word) (acq rel : Bool)
  | rmwPair (pw : Word) (a : Address) (x0 x1 : Val) (n0 n1 : Word) (acq rel : Bool)
  | fence (f : WeakMem.Fence)
  /-- The allocator (not a `Promises` rule): `allocBuf` at the thread's next
  fresh label. -/
  | alloc (n : Nat) (zero : Option (List Val))

/-- What one event does to the local state, and the words it returns. -/
def evSem (g : G) : MemOp → St → List (St × List Word)
  | .load pw a acq, s =>
      (Promises.stepLoad g.arch s.mem s.pairs (mth s pw pw pw) 1 a [0] acq).map fun th =>
        ({ s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1] }, [th.regs 1])
  | .loadPair pw a acq, s =>
      (Promises.stepLoadPair g.arch s.mem s.pairs (mth s pw pw pw) 1 2 a [0] acq).map fun th =>
        ({ s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1, th.regs 2] },
          [th.regs 1, th.regs 2])
  | .store pw a w rel, s =>
      (Promises.stepStore g.k g.arch s.mem (mth s pw w w) a (dataE 1 w) [0] rel).map fun x =>
        ({ s with mem := x.1, vs := x.2.vs, promises := x.2.promises }, [])
  | .storePair pw a w0 w1 rel, s =>
      let r := Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) a (dataE 1 w0) (dataE 2 w1) [0] rel
      [({ s with mem := r.1, pairs := r.2.1, vs := r.2.2.vs, promises := r.2.2.promises }, [])]
  | .rmw pw a kind nw acq rel, s =>
      (Promises.stepRmw g.k g.arch s.mem s.pairs (mth s pw nw nw) 1 a kind (dataE 1 nw) [0] acq rel).map
        fun x =>
          ({ s with mem := x.1, vs := x.2.vs, promises := x.2.promises,
                    undefs := s.undefs + countUndef [x.2.regs 1] }, [x.2.regs 1])
  | .rmwPair pw a x0 x1 n0 n1 acq rel, s =>
      (Promises.stepRmwPair g.arch s.mem s.pairs (mth s pw n0 n1) 1 2 a x0 x1 (dataE 1 n0) (dataE 2 n1)
          [0] acq rel).map fun x =>
        ({ s with mem := x.1, pairs := x.2.1, vs := x.2.2.vs, promises := x.2.2.promises,
                  undefs := s.undefs + countUndef [x.2.2.regs 1, x.2.2.regs 2] },
          [x.2.2.regs 1, x.2.2.regs 2])
  | .fence f, s => [(fenceS s f, [])]
  | .alloc n zero, s =>
      let r := allocBuf (freshLabel g.lbase g.n g.i s.nalloc) n zero s
      [(r.1, [r.2])]

/-! ## §2 Plans -/

/-- A plan: memory events, each continuation a function of the event's
result words; `alt` is pure nondeterminism, `fail` a stuck computation. -/
inductive Plan (α : Type) where
  | done : α → Plan α
  | fail : Plan α
  | alt : Plan α → Plan α → Plan α
  | ev : MemOp → (List Word → Plan α) → Plan α

def Plan.bind {α β : Type} : Plan α → (α → Plan β) → Plan β
  | .done a, f => f a
  | .fail, _ => .fail
  | .alt p q, f => .alt (p.bind f) (q.bind f)
  | .ev o k, f => .ev o (fun r => (k r).bind f)

def ofList {α : Type} : List α → Plan α
  | [] => .fail
  | a :: as => .alt (.done a) (ofList as)

def ofOpt {α : Type} : Option α → Plan α
  | some a => .done a
  | none => .fail

/-- Perform every event of a plan, one after the other, nothing in between. -/
def run (g : G) {α : Type} : Plan α → St → List (St × α)
  | .done a, s => [(s, a)]
  | .fail, _ => []
  | .alt p q, s => run g p s ++ run g q s
  | .ev o k, s => (evSem g o s).flatMap fun x => run g (k x.2) x.1

theorem run_bind (g : G) {α β : Type} (p : Plan α) (f : α → Plan β) (s : St) :
    run g (p.bind f) s = (run g p s).flatMap fun x => run g (f x.2) x.1 := by
  induction p generalizing s with
  | done a => simp [Plan.bind, run]
  | fail => simp [Plan.bind, run]
  | alt p q ihp ihq => simp [Plan.bind, run, ihp, ihq, List.flatMap_append]
  | ev o k ih =>
      simp only [Plan.bind, run, ih, List.flatMap_assoc]

theorem run_ofList (g : G) {α : Type} (l : List α) (s : St) :
    run g (ofList l) s = l.map fun a => (s, a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofList, run, ih]

theorem run_ofOpt (g : G) {α : Type} (o : Option α) (s : St) :
    run g (ofOpt o) s = (ol o).map fun a => (s, a) := by
  cases o <;> rfl

/-! ## §3 The plans of `TermRun`'s memory helpers, and their equations -/

/-- `loadUnits` as events: one `load`/`loadPair` per unit. -/
def loadP (pw : Word) (a : Address) (acq : Bool) : List Acc → Nat → Plan (List Word)
  | [], _ => .done []
  | .one :: us, k => .ev (.load pw (offs a k) acq) fun r =>
      match r with
      | [w] => (loadP pw a acq us (k + 1)).bind fun ws => .done (w :: ws)
      | _ => .fail
  | .two :: us, k => .ev (.loadPair pw (offs a k) acq) fun r =>
      match r with
      | [w0, w1] => (loadP pw a acq us (k + 2)).bind fun ws => .done (w0 :: w1 :: ws)
      | _ => .fail

/-- `storeUnits` as events: one `store`/`storePair` per unit. -/
def storeP (pw : Word) (a : Address) (rel : Bool) : List Acc → List Word → Nat → Plan Unit
  | [], _, _ => .done ()
  | .one :: us, w :: ws, i => .ev (.store pw (offs a i) w rel) fun _ => storeP pw a rel us ws (i + 1)
  | .two :: us, w0 :: w1 :: ws, i =>
      .ev (.storePair pw (offs a i) w0 w1 rel) fun _ => storeP pw a rel us ws (i + 2)
  | _, _, _ => .fail

/-- `alloc` as events: the allocator event, then the initialising stores. -/
def allocP (us : List Acc) (ws : List Word) : Plan Word :=
  .ev (.alloc (nWords us) none) fun r =>
    match r with
    | [pw] =>
        match addrOf pw with
        | some a => (storeP pw a false us ws 0).bind fun _ => .done pw
        | none => .fail
    | _ => .fail

theorem loadUnits_eq (g : G) (pw : Word) (a : Address) (acq : Bool) :
    ∀ (us : List Acc) (k : Nat) (s : St),
      loadUnits g.arch pw a acq us k s = run g (loadP pw a acq us k) s
  | [], _, _ => rfl
  | .one :: us, k, s => by
      simp only [loadUnits, loadP, run, evSem, List.flatMap_map, run_bind]
      congr 1
      funext th
      rw [← loadUnits_eq g pw a acq us (k + 1)]
      simp [run, List.flatMap_singleton', List.map_eq_flatMap]
  | .two :: us, k, s => by
      simp only [loadUnits, loadP, run, evSem, List.flatMap_map, run_bind]
      congr 1
      funext th
      rw [← loadUnits_eq g pw a acq us (k + 2)]
      simp [run, List.map_eq_flatMap]

theorem storeUnits_eq (g : G) (pw : Word) (a : Address) (rel : Bool) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St),
      storeUnits g.k g.arch pw a rel us ws i s = (run g (storeP pw a rel us ws i) s).map (·.1)
  | [], _, _, _ => rfl
  | .one :: us, w :: ws, i, s => by
      simp only [storeUnits, storeP, run, evSem, List.flatMap_map, List.map_flatMap]
      congr 1
      funext x
      exact storeUnits_eq g pw a rel us ws (i + 1) _
  | .one :: _, [], _, _ => rfl
  | .two :: us, w0 :: w1 :: ws, i, s => by
      simp only [storeUnits, storeP, run, evSem, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact storeUnits_eq g pw a rel us ws (i + 2) _
  | .two :: _, [], _, _ => rfl
  | .two :: _, [_], _, _ => rfl

theorem alloc_eq (g : G) (us : List Acc) (ws : List Word) (s : St) :
    alloc g.k g.arch (freshLabel g.lbase g.n g.i s.nalloc) us ws s = run g (allocP us ws) s := by
  simp only [alloc, allocP, run, evSem, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h2 : (allocBuf (freshLabel g.lbase g.n g.i s.nalloc) (nWords us) none s).snd =
      cst (.loc ⟨freshLabel g.lbase g.n g.i s.nalloc, 0⟩ 0) := rfl
  rw [h2]
  show _ = run g ((storeP _ ⟨freshLabel g.lbase g.n g.i s.nalloc, 0⟩ false us ws 0).bind fun _ => .done _) _
  rw [run_bind, storeUnits_eq, List.map_map, List.map_eq_flatMap]
  rfl

/-- `injM` as events: pure for niche/wide tiers; for the boxed tier the
allocator, the initialising stores, and the `dmb ishst`. -/
def injP (g : G) (t : Ty) (j : Nat) (p : List Word) : Plan (List Word) :=
  if isBoxed t then
    match (armsOf t)[j]?.bind accs with
    | some us => (allocP (.one :: us) (cst (.num j) :: p)).bind fun pw =>
        if g.boxFence then .ev (.fence .st) (fun _ => .done [pw]) else .done [pw]
    | none => .fail
  else ofOpt (ofArm t j p)

/-- `projM` as events: for the boxed tier the tag load, then the payload
loads of the arm the tag selects (a later event chosen by an earlier result). -/
def projP (_g : G) (t : Ty) (ws : List Word) : Plan (Nat × List Word) :=
  if isBoxed t then
    match ws with
    | [pw] =>
        match addrOf pw with
        | some b =>
            (loadP pw b false [.one] 0).bind fun tw =>
              match tw with
              | [tag] =>
                  match tag.val with
                  | .num j =>
                      match (armsOf t)[j]?.bind accs with
                      | some us => (loadP pw b false us 1).bind fun p => .done (j, p)
                      | none => .fail
                  | _ => .fail
              | _ => .fail
        | none => .fail
    | _ => .fail
  else ofOpt (asArm t ws)

theorem injM_eq (g : G) (s : St) (t : Ty) (j : Nat) (p : List Word) :
    injM g s t j p = run g (injP g t j p) s := by
  unfold injM injP
  by_cases hb : isBoxed t = true
  · simp only [hb, ↓reduceIte]
    cases (armsOf t)[j]?.bind accs with
    | none => rfl
    | some us =>
        simp only
        rw [alloc_eq, run_bind, List.map_eq_flatMap]
        congr 1
        funext x
        cases g.boxFence <;> simp [run, evSem]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [run_ofOpt]
    cases ofArm t j p <;> rfl

theorem projM_eq (g : G) (s : St) (t : Ty) (ws : List Word) :
    projM g s t ws = run g (projP g t ws) s := by
  unfold projM projP
  by_cases hb : isBoxed t = true
  · simp only [hb, ↓reduceIte]
    match ws with
    | [pw] =>
        simp only
        cases addrOf pw with
        | none => rfl
        | some b =>
            simp only
            rw [loadUnits_eq, run_bind]
            congr 1
            funext x
            match x with
            | (s1, [tag]) =>
                simp only
                cases tag.val <;> try rfl
                rename_i j
                simp only
                cases (armsOf t)[j]?.bind accs with
                | none => rfl
                | some us =>
                    simp only
                    rw [loadUnits_eq, run_bind, List.map_eq_flatMap]
                    rfl
            | (_, []) => rfl
            | (_, _ :: _ :: _) => rfl
    | [] => rfl
    | _ :: _ :: _ => rfl
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [run_ofOpt]
    cases asArm t ws <;> rfl

/-! ## §4 The plan of an operation -/

/-- The operations that touch neither memory nor the thread's views. -/
def opPure : Op → Bool
  | .inl .. | .inr .. | .new _ _ | .publish _ | .intoRgn .. | .load .. | .store .. | .fence _ | .ldp .. | .stp ..
  | .fetch .. | .ldl .. | .ldlw .. | .stlw .. | .stl .. | .xchg .. | .xchgAt .. | .loadAt .. | .xchgAtF ..
  | .loadAtF .. | .newBuf .. | .bufInit .. => false
  | _ => true

theorem optBind_eq {α β : Type} (o : Option α) (f : α → Option β) :
    o.bind f = match o with | none => none | some a => f a := by cases o <;> rfl

theorem optMap_eq {α β : Type} (o : Option α) (f : α → β) :
    o.map f = match o with | none => none | some a => some (f a) := by cases o <;> rfl

/-- **A pure operation's outcome does not depend on the local state**: the
state it returns is the one it was given, and the rest is a function of the
environment alone.  So its plan is computed at any state (`default`). -/
theorem evalOp_pure (g : G) (env : Env) (σs : List Ty) (s : St) (op : Op) (h : opPure op = true) :
    evalOp g env σs s op = (evalOp g env σs default op).map fun x => (s, x.2) := by
  cases op <;> simp only [opPure, Bool.false_eq_true] at h <;> simp only [evalOp]
  all_goals (try rfl)
  all_goals (try simp only [bind, optBind_eq, optMap_eq, ol])
  all_goals (repeat' split)
  all_goals (try rfl)
  all_goals (simp_all)

/-- The plan of one operation (`evalOp` with its memory accesses as events). -/
def evalOpP (g : G) (env : Env) (σs : List Ty) : Op → Plan (Ty × List Word)
  | .inl τ a =>
      match evalAt env a with
      | some (t, ws) =>
          (projP g t ws).bind fun x =>
            (injP g (Ty.sum t (close σs τ)) x.1 x.2).bind fun q => .done (Ty.sum t (close σs τ), q)
      | none => .fail
  | .inr τ a =>
      match evalAt env a with
      | some (t, ws) =>
          (projP g t ws).bind fun x =>
            (injP g (Ty.sum (close σs τ) t) ((armsOf (close σs τ)).length + x.1) x.2).bind fun q =>
              .done (Ty.sum (close σs τ) t, q)
      | none => .fail
  | .new a _ =>
      match evalAt env a with
      | none => .fail
      | some (t, ws) =>
          match accs t with
          | none => .fail
          | some us => (allocP us ws).bind fun pw => .done (.ptr .own t, [pw])
  | .publish a =>
      match evalAt env a with
      | some x =>
          match x.1 with
          | .ptr _ u => .ev (.fence .st) fun _ => .done (.ptr .pub u, x.2)
          | .refine (.loc _ (.array n u)) ψ =>
              .ev (.fence .st) fun _ => .done (.refine (.loc .pub (.array n u)) ψ, x.2)
          | _ => .fail
      | none => .fail
  | .intoRgn _ a =>
      match evalAt env a with
      | some x =>
          match x.1 with
          | .ptr _ u => .ev (.fence .st) fun _ => .done (.ptr (.rgn (.lit 0)) u, x.2)
          | .refine (.loc _ (.array n u)) ψ =>
              .ev (.fence .st) fun _ => .done (.refine (.loc (.rgn (.lit 0)) (.array n u)) ψ, x.2)
          | _ => .fail
      | none => .fail
  | .load acq a =>
      match evalAt env a with
      | some (t, [pw]) =>
          match cellOf t, addrOf pw with
          | some (_, u), some b =>
              match accs u with
              | some us =>
                  (loadP pw b acq us 0).bind fun ws =>
                    .done (if (wordOf t).isSome then Ty.int else u, ws)
              | none => .fail
          | _, _ => .fail
      | _ => .fail
  | .store rel a v _ =>
      match evalAt env a, evalAt env v with
      | some (t, [pw]), some (_, ws) =>
          match cellOf t, addrOf pw with
          | some (_, u), some b =>
              match accs u with
              | some us => (storeP pw b rel us ws 0).bind fun _ => .done (.unit, [])
              | none => .fail
          | _, _ => .fail
      | _, _ => .fail
  | .fence f => .ev (.fence (toWFence f)) fun _ => .done (.unit, [])
  | .ldp acq a _ _ =>
      match evalAt env a with
      | some (t, [pw]) =>
          if pairRef t then
            match addrOf pw with
            | some b => (loadP pw b acq [.two] 0).bind fun ws => .done (.prod .int .int, ws)
            | none => .fail
          else .fail
      | _ => .fail
  | .stp rel a v0 v1 _ =>
      match evalAt env a, evalAt env v0, evalAt env v1 with
      | some (t, [pw]), some (_, w0), some (_, w1) =>
          match word2Of t, addrOf pw with
          | some _, some b => (storeP pw b rel [.two] (w0 ++ w1) 0).bind fun _ => .done (.unit, [])
          | _, _ => .fail
      | _, _, _ => .fail
  | .fetch o acq rel a v =>
      match evalAt env a, evalAt env v with
      | some (t, [pw]), some (_, [nw]) =>
          match addrOf pw with
          | some b =>
              .ev (.rmw pw b o.kind nw acq rel) fun r =>
                match r with
                | [rd] => .done (fetchRtTy t, [rd])
                | _ => .fail
          | none => .fail
      | _, _ => .fail
  | .ldl b i =>
      match evalAt env b, evalAt env i with
      | some (t, [pw]), some (_, iws) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match lanesOf u with
              | some (sg, w) =>
                  (loadP pw (offs a (j / w.lanes)) false [.one] 0).bind fun old =>
                    match numOf old with
                    | some x => .done (.fix sg w, [cst (.num (laneN w x (j % w.lanes)))])
                    | none => .fail
              | none => .fail
          | _, _, _ => .fail
      | _, _ => .fail
  | .ldlw b wi jl =>
      match evalAt env b, evalAt env wi, evalAt env jl with
      | some (t, [pw]), some (_, iws), some (_, jws) =>
          match bufElem t, numOf iws, numOf jws, addrOf pw with
          | some (_, u), some i, some j, some a =>
              match lanesOf u with
              | some (sg, w) =>
                  (loadP pw (offs a i) false [.one] 0).bind fun old =>
                    match numOf old with
                    | some x => .done (.fix sg w, [cst (.num (laneN w x (j % w.lanes)))])
                    | none => .fail
              | none => .fail
          | _, _, _, _ => .fail
      | _, _, _ => .fail
  | .stlw b wi jl v =>
      match evalAt env b, evalAt env wi, evalAt env jl, evalAt env v with
      | some (t, [pw]), some (_, iws), some (_, jws), some (_, vs) =>
          match bufElem t, numOf iws, numOf jws, numOf vs, addrOf pw with
          | some (_, u), some i, some j, some y, some a =>
              match lanesOf u with
              | some (_, w) =>
                  (loadP pw (offs a i) false [.one] 0).bind fun old =>
                    match numOf old with
                    | some x =>
                        (storeP pw (offs a i) false [.one] [cst (.num (setLaneN w x (j % w.lanes) y))] 0).bind
                          fun _ => .done (.unit, [])
                    | none => .fail
              | none => .fail
          | _, _, _, _, _ => .fail
      | _, _, _, _ => .fail
  | .stl b i v =>
      match evalAt env b, evalAt env i, evalAt env v with
      | some (t, [pw]), some (_, iws), some (_, vs) =>
          match bufElem t, numOf iws, numOf vs, addrOf pw with
          | some (_, u), some j, some y, some a =>
              match lanesOf u with
              | some (_, w) =>
                  (loadP pw (offs a (j / w.lanes)) false [.one] 0).bind fun old =>
                    match numOf old with
                    | some x =>
                        (storeP pw (offs a (j / w.lanes)) false [.one]
                            [cst (.num (setLaneN w x (j % w.lanes) y))] 0).bind fun _ => .done (.unit, [])
                    | none => .fail
              | none => .fail
          | _, _, _, _ => .fail
      | _, _, _ => .fail
  | .xchg a v =>
      match evalAt env a, evalAt env v with
      | some (t, [pw]), some (_, ws) =>
          match cellOf t, addrOf pw with
          | some (_, u), some b =>
              match accs u with
              | some us =>
                  (loadP pw b false us 0).bind fun old =>
                    (storeP pw b false us ws 0).bind fun _ => .done (u, old)
              | none => .fail
          | _, _ => .fail
      | _, _ => .fail
  | .xchgAt b i v =>
      match evalAt env b, evalAt env i, evalAt env v with
      | some (t, [pw]), some (_, iws), some (_, xs) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match accs u with
              | some us =>
                  (loadP pw (offs a (j * nWords us)) false us 0).bind fun old =>
                    (storeP pw (offs a (j * nWords us)) false us xs 0).bind fun _ => .done (u, old)
              | none => .fail
          | _, _, _ => .fail
      | _, _, _ => .fail
  | .loadAt b i =>
      match evalAt env b, evalAt env i with
      | some (t, [pw]), some (_, iws) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match accs u with
              | some us => (loadP pw (offs a (j * nWords us)) false us 0).bind fun old => .done (u, old)
              | none => .fail
          | _, _, _ => .fail
      | _, _ => .fail
  | .xchgAtF b i p v =>
      match evalAt env b, evalAt env i, evalAt env v with
      | some (t, [pw]), some (_, iws), some (_, xs) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match accs u, compOff u p with
              | some us, some (c, o) =>
                  match accs c with
                  | some cs =>
                      (loadP pw (offs a (j * nWords us + o)) false cs 0).bind fun old =>
                        (storeP pw (offs a (j * nWords us + o)) false cs xs 0).bind fun _ => .done (c, old)
                  | none => .fail
              | _, _ => .fail
          | _, _, _ => .fail
      | _, _, _ => .fail
  | .loadAtF b i p =>
      match evalAt env b, evalAt env i with
      | some (t, [pw]), some (_, iws) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match accs u, compOff u p with
              | some us, some (c, o) =>
                  match accs c with
                  | some cs =>
                      (loadP pw (offs a (j * nWords us + o)) false cs 0).bind fun old => .done (c, old)
                  | none => .fail
              | _, _ => .fail
          | _, _, _ => .fail
      | _, _ => .fail
  | .newBuf n τ =>
      match evalAt env n with
      | some x =>
          match numOf x.2 with
          | some k =>
              match accs (close σs τ) with
              | some us =>
                  .ev (.alloc (k * nWords us)
                      (if zeroableIn [] [] (close σs τ) then zeroWords (close σs τ) else none)) fun r =>
                    match r with
                    | [pw] =>
                        .done (.refine (.loc .own (.array (.lit k) (close σs τ)))
                          (.ini (.lit (if (if zeroableIn [] [] (close σs τ) then zeroWords (close σs τ)
                            else none).isSome then k else 0))), [pw])
                    | _ => .fail
              | none => .fail
          | none => .fail
      | none => .fail
  | .bufInit b i x =>
      match evalAt env b, evalAt env i, evalAt env x with
      | some (t, [pw]), some (_, iws), some (_, xs) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match accs u, t with
              | some us, .refine (.loc μ (.array n _)) _ =>
                  (storeP pw (offs a (j * nWords us)) false us xs 0).bind fun _ =>
                    .done (.refine (.loc μ (.array n u)) (.ini (.lit (j + 1))), [pw])
              | _, _ => .fail
          | _, _, _ => .fail
      | _, _, _ => .fail
  | op => ofList ((evalOp g env σs default op).map (·.2))

theorem filterMap_eq_flatMap {α β : Type} (f : α → Option β) (l : List α) :
    l.filterMap f = l.flatMap fun a => ol (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.filterMap_cons, List.flatMap_cons, ih]
      cases f a <;> rfl

/-- `evalOp_eq` for `bufInit` (its result type is matched on `t` too). -/
theorem evalOp_eq_bufInit (g : G) (env : Env) (σs : List Ty) (s : St) (b i x : At) :
    evalOp g env σs s (.bufInit b i x) = run g (evalOpP g env σs (.bufInit b i x)) s := by
  simp only [evalOp, evalOpP]
  cases evalAt env b with
  | none => rfl
  | some p1 =>
    obtain ⟨t, ws⟩ := p1
    match ws with
    | [] => rfl
    | _ :: _ :: _ => rfl
    | [pw] =>
      cases evalAt env i with
      | none => rfl
      | some p2 =>
        cases evalAt env x with
        | none => rfl
        | some p3 =>
          simp only
          cases bufElem t with
          | none => rfl
          | some p4 =>
            cases numOf p2.2 with
            | none => rfl
            | some j =>
              cases addrOf pw with
              | none => rfl
              | some a =>
                simp only
                cases accs p4.2 with
                | none => rfl
                | some us =>
                  try simp only
                  cases t <;> try rfl
                  rename_i t' ψ
                  cases t' <;> try rfl
                  rename_i μ t''
                  cases t'' <;> try rfl
                  simp only
                  rw [storeUnits_eq, run_bind, List.map_eq_flatMap]
                  simp only [List.flatMap_map, run]

-- **`evalOp` is its plan, run with nothing in between.**
set_option maxHeartbeats 2000000 in
theorem evalOp_eq (g : G) (env : Env) (σs : List Ty) (s : St) (op : Op) :
    evalOp g env σs s op = run g (evalOpP g env σs op) s := by
  by_cases hp : opPure op = true
  · rw [evalOp_pure g env σs s op hp]
    cases op <;> simp only [opPure, Bool.false_eq_true] at hp <;> simp only [evalOpP, run_ofList, List.map_map] <;> rfl
  · cases op <;> simp only [opPure, not_true_eq_false] at hp
    case bufInit b i x => exact evalOp_eq_bufInit g env σs s b i x
    all_goals simp only [evalOp, evalOpP]
    all_goals (try simp only [bind, optBind_eq, optMap_eq, ol])
    all_goals (repeat' split)
    all_goals (try simp only [loadUnits_eq, storeUnits_eq, projM_eq, injM_eq, alloc_eq, filterMap_eq_flatMap,
      run_bind, run, evSem, List.map_eq_flatMap, List.flatMap_assoc, List.flatMap_cons,
      List.flatMap_nil, List.append_nil])
    all_goals (try rfl)
    all_goals (try (intros; subst_vars))
    all_goals (try (exfalso; solve_by_elim (maxDepth := 14)))
    all_goals (try simp_all)
    all_goals (try (exfalso; solve_by_elim (maxDepth := 14)))
    all_goals (try (congr 1; funext x; split <;> simp_all [run, run_bind]))
    all_goals rfl

/-! ## §5 The plan of a thread step -/

/-- The outcomes of a step that touches no memory, computed without memory. -/
def silentOut (g : G) (th : TTh) : List TTh := (tstep g #[] [] th).map (·.2.2)

/-- **The plan of `tstep`**: the leaf is the commit, a function of the local
state after the last event. -/
def tstepP (g : G) (th : TTh) : Plan (St → TTh) :=
  match th.term with
  | .let_ _ (.call ..) _ => ofList ((silentOut g th).map fun th' _ => th')
  | .let_ _ (.callc ..) _ => ofList ((silentOut g th).map fun th' _ => th')
  | .let_ x (.new a T) e =>
      (evalOpP g th.env th.σs (.new a T)).bind fun r =>
        .done fun s' =>
          let th' := withS { th with term := e, env := (x, r.1, r.2) :: th.env } s'
          match T, r.2.map (·.val) with
          | some T, [WeakMem.Val.loc l _] =>
              let u := close th.σs T
              { th' with tys := th.tys ++ [(l.label, u, u.wf 0 0 && (progTgts g.p).contains u)] }
          | _, _ => th'
  | .let_ x op e =>
      (evalOpP g th.env th.σs op).bind fun r =>
        .done fun s' => withS { th with term := e, env := (x, r.1, r.2) :: th.env } s'
  | .region a _ pn tn e =>
      match evalAt th.env a with
      | some (.ptr _ u, ws) =>
          .ev (.fence .st) fun _ => .done fun s' =>
            withS { th with term := e,
                            env := (tn, .tok (.lit 0) none, []) :: (pn, .ptr (.rgn (.lit 0)) u, ws) :: th.env } s'
      | some (.refine (.loc _ u) ψ, ws) =>
          .ev (.fence .st) fun _ => .done fun s' =>
            withS { th with term := e,
                            env := (tn, .tok (.lit 0) none, []) ::
                                   (pn, .refine (.loc (.rgn (.lit 0)) u) ψ, ws) :: th.env } s'
      | _ => .fail
  | .case a x e₁ y e₂ =>
      match evalAt th.env a with
      | some (t@(.sum u w), ws) =>
          (projP g t ws).bind fun r =>
            let n := (armsOf u).length
            let (ty, j', x', e') := if r.1 < n then (u, r.1, x, e₁) else (w, r.1 - n, y, e₂)
            (injP g ty j' r.2).bind fun q =>
              .done fun s2 => withS { th with term := e', env := (x', ty, q) :: th.env } s2
      | _ => .fail
  | .cas acq rel w e v t ok fail =>
      match evalAt th.env w, evalAt th.env e, evalAt th.env v with
      | some (_, [pw]), some (_, [ew]), some (_, [nw]) =>
          match addrOf pw with
          | some b =>
              .ev (.rmw pw b (.cas ew.val) nw acq rel) fun r =>
                match r with
                | [rd] => .done fun s' =>
                    withS (if rd.val == ew.val then { th with term := ok, env := (t, .unit, []) :: th.env }
                           else { th with term := fail }) s'
                | _ => .fail
          | none => .fail
      | _, _, _ => .fail
  | .casp acq rel w e0 e1 v0 v1 t ok fail =>
      match evalAt th.env w, evalAt th.env e0, evalAt th.env e1, evalAt th.env v0, evalAt th.env v1 with
      | some (_, [pw]), some (_, [x0]), some (_, [x1]), some (_, [n0]), some (_, [n1]) =>
          match addrOf pw with
          | some b =>
              .ev (.rmwPair pw b x0.val x1.val n0 n1 acq rel) fun r =>
                match r with
                | [r0, r1] => .done fun s' =>
                    withS (if r0.val == x0.val && r1.val == x1.val then
                             { th with term := ok, env := (t, .unit, []) :: th.env }
                           else { th with term := fail }) s'
                | _ => .fail
          | none => .fail
      | _, _, _, _, _ => .fail
  | _ => ofList ((silentOut g th).map fun th' _ => th')

/-- The commit: memory and pairs from the last event, the thread from the leaf. -/
def commit (x : St × (St → TTh)) : Memory × List Ts × TTh := (x.1.mem, x.1.pairs, x.2 x.1)

-- **`tstep` factored**: its plan, run with nothing in between, then committed.
set_option maxHeartbeats 4000000 in
theorem tstep_plan (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) :
    tstep g mem pairs th = (run g (tstepP g th) (stOf mem pairs th)).map commit := by
  obtain ⟨term, env, σs, stack, vs, promises, nalloc, undefs⟩ := th
  cases term
  case let_ x op e =>
    cases op
    case call f ix a ts =>
      simp only [tstep, tstepP, silentOut, run_ofList, List.map_map]
      simp only [optBind_eq, optMap_eq, ol]
      repeat' split
      all_goals (try rfl)
      all_goals simp_all
    case callc f a =>
      simp only [tstep, tstepP, silentOut, run_ofList, List.map_map]
      simp only [optBind_eq, optMap_eq, ol]
      repeat' split
      all_goals (try rfl)
      all_goals simp_all
    case new =>
      simp only [tstep, tstepP]
      rw [evalOp_eq, run_bind, List.map_flatMap, List.map_eq_flatMap]
      rfl
    all_goals
      simp only [tstep, tstepP]
      rw [evalOp_eq, run_bind, List.map_flatMap, List.map_eq_flatMap]
      rfl
  all_goals simp only [tstep, tstepP, silentOut, run_ofList, List.map_map]
  all_goals (try simp only [optBind_eq, optMap_eq, ol])
  all_goals (repeat' split)
  all_goals (try simp only [projM_eq, injM_eq, run_bind, run, evSem, List.map_flatMap, List.map_eq_flatMap,
    List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, commit])
  all_goals (try rfl)
  all_goals (try (intros; subst_vars))
  all_goals (try (exfalso; solve_by_elim (maxDepth := 14)))
  all_goals (try simp_all)
  all_goals (try (exfalso; solve_by_elim (maxDepth := 14)))
  all_goals rfl

/-! ## §6 The micro machine: one memory event per step -/

/-- A micro thread: between ops (`idle`), or in the middle of one (`busy`):
`base` is the thread at the op's start with its local fields (`vs`,
`promises`, `nalloc`, `undefs`) current, `q` the rest of the op's plan. -/
inductive TThM where
  | idle (th : TTh)
  | busy (base : TTh) (q : Plan (St → TTh))

/-- The local fields of a micro thread. -/
def TThM.base : TThM → TTh
  | .idle th => th
  | .busy b _ => b

/-- One micro step of a busy thread: at most one event (`ev`), or the
commit (`done`). -/
def act (g : G) (mem : Memory) (pairs : List Ts) (base : TTh) :
    Plan (St → TTh) → List (Memory × List Ts × TThM)
  | .done f => [(mem, pairs, .idle (f (stOf mem pairs base)))]
  | .fail => []
  | .alt p q => act g mem pairs base p ++ act g mem pairs base q
  | .ev o k => (evSem g o (stOf mem pairs base)).map fun x =>
      (x.1.mem, x.1.pairs, .busy (withS base x.1) (k x.2))

/-- **One micro step of one thread** (`tstepμ`).  An idle thread plans its
next op and performs its first event (or commits at once if it has none). -/
def tstepMμ (g : G) (mem : Memory) (pairs : List Ts) : TThM → List (Memory × List Ts × TThM)
  | .idle th => act g mem pairs th (tstepP g th)
  | .busy base q => act g mem pairs base q

/-- A run of micro steps of one thread, nothing else in between, whose
intermediate states are busy and which ends at the first idle state. -/
inductive BusyRun (g : G) : Memory × List Ts × TThM → Memory × List Ts × TTh → Prop
  | fin {mem pairs x mem' pairs' th'} : (mem', pairs', TThM.idle th') ∈ tstepMμ g mem pairs x →
      BusyRun g (mem, pairs, x) (mem', pairs', th')
  | mid {mem pairs x mem' pairs' base q r} : (mem', pairs', TThM.busy base q) ∈ tstepMμ g mem pairs x →
      BusyRun g (mem', pairs', .busy base q) r → BusyRun g (mem, pairs, x) r

/-- How a micro successor continues a `BusyRun` to `r`. -/
def Cont (g : G) (y : Memory × List Ts × TThM) (r : Memory × List Ts × TTh) : Prop :=
  y = (r.1, r.2.1, .idle r.2.2) ∨ ∃ base q, y.2.2 = .busy base q ∧ BusyRun g y r

theorem busyRun_iff (g : G) (mem : Memory) (pairs : List Ts) (x : TThM) (r : Memory × List Ts × TTh) :
    BusyRun g (mem, pairs, x) r ↔ ∃ y ∈ tstepMμ g mem pairs x, Cont g y r := by
  constructor
  · intro h
    cases h with
    | fin hm => exact ⟨_, hm, Or.inl rfl⟩
    | mid hm hr => exact ⟨_, hm, Or.inr ⟨_, _, rfl, hr⟩⟩
  · rintro ⟨⟨m', ps', y⟩, hy, hc⟩
    rcases hc with he | ⟨base, q, hq, hr⟩
    · obtain ⟨r1, r2, r3⟩ := r
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact .fin hy
    · simp only at hq
      subst hq
      exact .mid hy hr

theorem stOf_withS (base : TTh) (s : St) : stOf s.mem s.pairs (withS base s) = s := by
  cases s; rfl

/-- **A plan's run is a `BusyRun` of the micro machine.** -/
theorem run_iff_busy (g : G) :
    ∀ (q : Plan (St → TTh)) (base : TTh) (mem : Memory) (pairs : List Ts) (r : Memory × List Ts × TTh),
      r ∈ (run g q (stOf mem pairs base)).map commit ↔ BusyRun g (mem, pairs, .busy base q) r
  | .done f, base, mem, pairs, r => by
      rw [busyRun_iff]
      simp only [run, commit, List.map_cons, List.map_nil, List.mem_singleton, tstepMμ, act, Cont]
      constructor
      · rintro rfl
        exact ⟨_, rfl, Or.inl rfl⟩
      · rintro ⟨y, rfl, hc⟩
        rcases hc with he | ⟨_, _, hq, _⟩
        · obtain ⟨r1, r2, r3⟩ := r
          simp only [Prod.mk.injEq, TThM.idle.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          rfl
        · cases hq
  | .fail, base, mem, pairs, r => by
      rw [busyRun_iff]
      simp [run, tstepMμ, act]
  | .alt p q, base, mem, pairs, r => by
      have hp := run_iff_busy g p base mem pairs r
      have hq := run_iff_busy g q base mem pairs r
      rw [busyRun_iff] at hp hq ⊢
      simp only [run, List.map_append, List.mem_append, tstepMμ, act] at hp hq ⊢
      rw [hp, hq]
      constructor
      · rintro (⟨y, hy, hc⟩ | ⟨y, hy, hc⟩)
        · exact ⟨y, Or.inl hy, hc⟩
        · exact ⟨y, Or.inr hy, hc⟩
      · rintro ⟨y, hy | hy, hc⟩
        · exact Or.inl ⟨y, hy, hc⟩
        · exact Or.inr ⟨y, hy, hc⟩
  | .ev o k, base, mem, pairs, r => by
      rw [busyRun_iff]
      simp only [run, tstepMμ, act, List.map_flatMap, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨x, hx, hr⟩
        have hk := (run_iff_busy g (k x.2) (withS base x.1) x.1.mem x.1.pairs r).1
          (by rw [stOf_withS]; exact List.mem_map.2 hr)
        exact ⟨_, ⟨x, hx, rfl⟩, Or.inr ⟨_, _, rfl, hk⟩⟩
      · rintro ⟨y, ⟨x, hx, rfl⟩, hc⟩
        rcases hc with he | ⟨b', q', hq, hb⟩
        · simp only [Prod.mk.injEq] at he
          cases he.2.2
        · refine ⟨x, hx, ?_⟩
          have := (run_iff_busy g (k x.2) (withS base x.1) x.1.mem x.1.pairs r).2 hb
          rw [stOf_withS] at this
          exact List.mem_map.1 this

/-! ## §7 Micro configurations and the micro machine `StepM` -/

structure CfgM where
  mem   : Memory
  pairs : List Ts := []
  ths   : Array TThM
  lbase : Nat := 0
  boxFence : Bool := true
  /-- see `Cfg.cap` (thread capacity) -/
  cap : Nat := 0
  /-- see `Cfg.trace` (E1: the observable events so far) -/
  trace : List Event := []

/-- `Cfg.n`: labels are striped by the capacity. -/
def CfgM.n (c : CfgM) : Nat := max c.cap c.ths.size

/-- `tysOf` of a micro configuration: every thread's records (a busy thread's are its base's). -/
def tysOfM (c : CfgM) (l : AllocLabel) : Option (Ty × Bool) :=
  c.ths.toList.findSome? fun th => (th.base.tys.find? (·.1 == l)).map (·.2)

def gOfM (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : CfgM) (i : Nat) : G :=
  ⟨p, k, arch, c.n, i, c.lbase, c.boxFence, fun _ => False, fun _ => True, tysOfM c⟩

def threadStepsM (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : CfgM) (i : Nat) : List CfgM :=
  match c.ths[i]? with
  | none => []
  | some th =>
      (tstepMμ (gOfM p k arch c i) c.mem c.pairs th).map fun x =>
        { c with mem := x.1, pairs := x.2.1, ths := c.ths.set! i x.2.2 }

/-- A promise records its timestamp in the thread's local fields, idle or busy. -/
def TThM.prom : TThM → Ts → TThM
  | .idle th, n => .idle { th with promises := th.promises ++ [n] }
  | .busy b q, n => .busy { b with promises := b.promises ++ [n] } q

def promiseM (c : CfgM) (i : Nat) (a : Address) (v : Val) (w : Ts) : CfgM :=
  match c.ths[i]? with
  | none => c
  | some th => { c with mem := c.mem.push ⟨a, v, w⟩, ths := c.ths.set! i (th.prom c.mem.size) }

/-- A coarse configuration as a micro one: every thread idle. -/
def embed (c : Cfg) : CfgM :=
  { mem := c.mem, pairs := c.pairs, ths := c.ths.map .idle, lbase := c.lbase, boxFence := c.boxFence,
    cap := c.cap, trace := c.trace }

/-- Micro steps of thread `i` alone, promises included (also mid-op). -/
inductive SoloM (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) : CfgM → CfgM → Prop
  | refl (c) : SoloM p k arch i c c
  | thread {c c' c''} : c' ∈ threadStepsM p k arch c i → SoloM p k arch i c' c'' → SoloM p k arch i c c''
  | prom {c c''} (a v w) : w < c.mem.size → SoloM p k arch i (promiseM c i a v w) c'' →
      SoloM p k arch i c c''
  | ext {c c' c''} : c' ∈ extSteps c i → SoloM p k arch i (embed c') c'' → SoloM p k arch i (embed c) c''

/-- Idle with no outstanding promise. -/
def TThM.clear : TThM → Bool
  | .idle th => th.promises.isEmpty
  | .busy .. => false

def noPromisesM (c : CfgM) (i : Nat) : Bool := (c.ths[i]?.map TThM.clear).getD true

/-- A certificate: a solo micro run to an idle state with no promises. -/
def CertifiedM (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : CfgM) (i : Nat) : Prop :=
  ∃ c', SoloM p k arch i c c' ∧ noPromisesM c' i = true

/-- **The micro machine**: `TermRun.Step`'s two constructors, one memory event
(or one commit) per thread step. -/
inductive StepM (p : Prog) (k : Promises.Knobs) (arch : Arch) : CfgM → CfgM → Prop
  | thread {c c'} (i) : c' ∈ threadStepsM p k arch c i → CertifiedM p k arch c' i → StepM p k arch c c'
  | prom {c} (i a v w) : i < c.ths.size → w < c.mem.size →
      CertifiedM p k arch (promiseM c i a v w) i → StepM p k arch c (promiseM c i a v w)

inductive StepsM (p : Prog) (k : Promises.Knobs) (arch : Arch) : CfgM → CfgM → Prop
  | refl (c : CfgM) : StepsM p k arch c c
  | step {c c' c'' : CfgM} : StepM p k arch c c' → StepsM p k arch c' c'' → StepsM p k arch c c''

/-- Thread steps of thread `i` only (no promises). -/
inductive ThPath (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) : CfgM → CfgM → Prop
  | refl (c) : ThPath p k arch i c c
  | step {c c' c''} : c' ∈ threadStepsM p k arch c i → ThPath p k arch i c' c'' → ThPath p k arch i c c''

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}

theorem SoloM.trans {i : Nat} {c c' c'' : CfgM} (h1 : SoloM p k arch i c c') (h2 : SoloM p k arch i c' c'') :
    SoloM p k arch i c c'' := by
  induction h1 with
  | refl => exact h2
  | thread hs _ ih => exact .thread hs (ih h2)
  | prom a v w hw _ ih => exact .prom a v w hw (ih h2)
  | ext hs _ ih => exact .ext hs (ih h2)

theorem ThPath.solo {i : Nat} {c c' : CfgM} (h : ThPath p k arch i c c') : SoloM p k arch i c c' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .thread hs ih

/-- **A path of thread steps ending certified is a run of `StepM`**: every
intermediate configuration is certified by the rest of the path followed by
the final certificate. -/
theorem ThPath.steps {i : Nat} {c c' : CfgM} (h : ThPath p k arch i c c') (hc : CertifiedM p k arch c' i) :
    StepsM p k arch c c' := by
  induction h with
  | refl => exact .refl _
  | step hs hp ih =>
      obtain ⟨c'', hs'', hn⟩ := hc
      exact .step (.thread _ hs ⟨c'', hp.solo.trans hs'', hn⟩) (ih ⟨c'', hs'', hn⟩)

theorem set_set {α : Type} (xs : Array α) (i : Nat) (a b : α) : (xs.set! i a).set! i b = xs.set! i b := by
  simp [Array.set!]

theorem size_set {α : Type} (xs : Array α) (i : Nat) (a : α) : (xs.set! i a).size = xs.size := by
  simp [Array.set!]

theorem map_set {α β : Type} (f : α → β) (xs : Array α) (i : Nat) (a : α) :
    (xs.set! i a).map f = (xs.map f).set! i (f a) := by
  simp [Array.set!]

/-- A micro step to a busy thread keeps its base's records. -/
theorem act_tys {g : G} {mem : Memory} {pairs : List Ts} {base : TTh} :
    ∀ (q : Plan (St → TTh)) {mem' : Memory} {pairs' : List Ts} {b : TTh} {q' : Plan (St → TTh)},
      (mem', pairs', TThM.busy b q') ∈ act g mem pairs base q → b.tys = base.tys
  | .done _, _, _, _, _, h => by simp [act] at h
  | .fail, _, _, _, _, h => by simp [act] at h
  | .alt p q, _, _, _, _, h => by
      simp only [act, List.mem_append] at h
      rcases h with h | h
      · exact act_tys p h
      · exact act_tys q h
  | .ev o k, _, _, _, _, h => by
      simp only [act, List.mem_map] at h
      obtain ⟨_, -, h⟩ := h
      simp only [Prod.mk.injEq, TThM.busy.injEq] at h
      rw [← h.2.2.1]; rfl

theorem act_busy_tys {g : G} {mem : Memory} {pairs : List Ts} {x : TThM} {mem' : Memory}
    {pairs' : List Ts} {b : TTh} {q : Plan (St → TTh)} (h : (mem', pairs', TThM.busy b q) ∈ tstepMμ g mem pairs x) :
    (TThM.busy b q).base.tys = x.base.tys := by
  cases x with
  | idle th => exact act_tys _ h
  | busy b0 q0 => exact act_tys _ h

/-- Replacing one micro thread by one whose base has the same records keeps `tysOfM`. -/
theorem tysOfM_set {cm d : CfgM} {i : Nat} {x y : TThM} (hth : cm.ths[i]? = some x)
    (hd : d.ths = cm.ths.set! i y) (ht : y.base.tys = x.base.tys) : tysOfM d = tysOfM cm := by
  funext l
  simp only [tysOfM, hd, Array.toList_set!]
  have hl : cm.ths.toList[i]? = some x := by simpa using hth
  refine findSome_set_same _ ?_ _ _ hl
  simp [ht]

/-- **A `BusyRun` of thread `i` is a path of micro thread steps** in any
micro configuration that holds its start. -/
theorem busy_path {i : Nat} {g : G} {x : Memory × List Ts × TThM} {r : Memory × List Ts × TTh}
    (h : BusyRun g x r) :
    ∀ (cm : CfgM), cm.ths[i]? = some x.2.2 → cm.mem = x.1 → cm.pairs = x.2.1 → gOfM p k arch cm i = g →
      ThPath p k arch i cm { cm with mem := r.1, pairs := r.2.1, ths := cm.ths.set! i (.idle r.2.2) } := by
  induction h with
  | fin hm =>
      intro cm hth hmem hpairs hg
      refine .step ?_ (.refl _)
      unfold threadStepsM
      rw [hth, hg, hmem, hpairs]
      exact List.mem_map.2 ⟨_, hm, rfl⟩
  | @mid mem pairs x mem' pairs' base q r hm _ ih =>
      intro cm hth hmem hpairs hg
      have hstep : { cm with mem := mem', pairs := pairs', ths := cm.ths.set! i (.busy base q) } ∈
          threadStepsM p k arch cm i := by
        unfold threadStepsM
        rw [hth, hg, hmem, hpairs]
        exact List.mem_map.2 ⟨_, hm, rfl⟩
      refine .step hstep ?_
      have := ih { cm with mem := mem', pairs := pairs', ths := cm.ths.set! i (.busy base q) }
        (TermStep.arr_get_set_eq _ hth) rfl rfl (by
          rw [← hg]; unfold gOfM
          rw [tysOfM_set hth rfl (act_busy_tys hm)]; simp [CfgM.n, size_set])
      simpa [set_set] using this

end

/-! ## §8 Equivalence: a `tstep` is a solo `BusyRun`; coarse runs are micro runs -/

/-- **`tstep_eq_run`**: `r` is an outcome of `tstep` iff the micro machine,
running that thread alone with nothing in between, goes from `idle th`
through busy states to `idle r.2.2`, producing `r.1`/`r.2.1`. -/
theorem tstep_eq_run (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (r : Memory × List Ts × TTh) :
    r ∈ tstep g mem pairs th ↔ BusyRun g (mem, pairs, .idle th) r := by
  rw [tstep_plan, run_iff_busy, busyRun_iff, busyRun_iff]
  exact Iff.rfl

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}

theorem embed_get (c : Cfg) (i : Nat) : (embed c).ths[i]? = (c.ths[i]?).map TThM.idle := by
  simp [embed]

/-- An embedded configuration has its coarse records. -/
theorem tysOfM_embed (c : Cfg) : tysOfM (embed c) = tysOf c := by
  funext l; simp [tysOfM, tysOf, embed, List.findSome?_map, Function.comp_def, TThM.base]

theorem gOfM_embed (c : Cfg) (i : Nat) : gOfM p k arch (embed c) i = gOf p k arch c i := by
  unfold gOfM; rw [tysOfM_embed]; simp [gOf, embed, CfgM.n, Cfg.n]

/-- A coarse thread step is a path of micro thread steps. -/
theorem threadSteps_path {c c' : Cfg} {i : Nat} (h : c' ∈ threadSteps p k arch c i) :
    ThPath p k arch i (embed c) (embed c') := by
  obtain ⟨th, mem', pairs', th', hth, hr, rfl⟩ := TermStep.step_thread_inv h
  have hb := (tstep_eq_run _ _ _ th _).1 hr
  have := busy_path (p := p) (k := k) (arch := arch) (i := i) hb (embed c)
    (by rw [embed_get, hth]; rfl) rfl rfl (gOfM_embed c i)
  simpa [embed, map_set] using this

theorem promise_embed (c : Cfg) (i : Nat) (a : Address) (v : Val) (w : Ts) :
    promiseM (embed c) i a v w = embed (promise c i a v w) := by
  unfold promiseM promise
  rw [embed_get]
  cases c.ths[i]? with
  | none => rfl
  | some th => simp [embed, map_set, TThM.prom]

theorem solo_sim {i : Nat} {c c' : Cfg} (h : Solo p k arch i c c') : SoloM p k arch i (embed c) (embed c') := by
  induction h with
  | refl => exact .refl _
  | thread hs _ ih => exact (threadSteps_path hs).solo.trans ih
  | prom a v w hw _ ih =>
      refine .prom a v w hw ?_
      rw [promise_embed]
      exact ih
  | ext hs _ ih => exact .ext hs ih

theorem noPromises_embed (c : Cfg) (i : Nat) : noPromisesM (embed c) i = noPromises c i := by
  unfold noPromisesM noPromises
  rw [embed_get]
  cases c.ths[i]? <;> rfl

/-- **Coarse certificates are micro certificates.**  The converse fails: a
promise made in the middle of an op can be fulfilled by a later event of the
same op, which the coarse machine cannot express. -/
theorem certified_certifiedM {c : Cfg} {i : Nat} (h : Certified p k arch c i) :
    CertifiedM p k arch (embed c) i := by
  obtain ⟨c', hs, hn⟩ := h
  exact ⟨embed c', solo_sim hs, by rw [noPromises_embed]; exact hn⟩

theorem StepsM.trans {c c' c'' : CfgM} (h1 : StepsM p k arch c c') (h2 : StepsM p k arch c' c'') :
    StepsM p k arch c c'' := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

/-- **`step_sim`**: every coarse machine step is a run of the micro machine. -/
theorem step_sim {c c' : Cfg} (h : Step p k arch c c') : StepsM p k arch (embed c) (embed c') := by
  cases h with
  | thread i hs hc => exact (threadSteps_path hs).steps (certified_certifiedM hc)
  | prom i a v w hi hw hc =>
      rw [← promise_embed]
      refine .step (.prom i a v w (by simpa [embed] using hi) hw ?_) (.refl _)
      rw [promise_embed]
      exact certified_certifiedM hc

/-- Coarse runs are micro runs: the coarse reachable set embeds in the micro one. -/
theorem steps_sim {c c' : Cfg} (h : TermStep.Steps p k arch c c') : StepsM p k arch (embed c) (embed c') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact (step_sim hs).trans ih

end

/-! ## §9 The micro invariant and the target theorem (statement only)

`SysInvMμ` is `SysInvN` read at the *base* configuration (every thread at its
op's start with its local fields current), with `thr` split: an idle thread
satisfies `ThSys` as before; a busy one the pending-op clause `PendSys`. -/

section
open CoreTyping TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermMain

/-- The coarse view of a micro configuration: every thread at its op's start,
local fields current. -/
def baseCfg (c : CfgM) : Cfg :=
  { mem := c.mem, pairs := c.pairs, ths := c.ths.map TThM.base, lbase := c.lbase, boxFence := c.boxFence,
    cap := c.cap, trace := c.trace }

/-- The events performed so far: `tr` (each event with its result words) leads
from plan `p` to the residual `q`, `alt` choices resolved on the way. -/
inductive PlanTrace {α : Type} : Plan α → List (MemOp × List Word) → Plan α → Prop
  | nil (p : Plan α) : PlanTrace p [] p
  | altL {p q r : Plan α} {tr : List (MemOp × List Word)} : PlanTrace p tr r → PlanTrace (.alt p q) tr r
  | altR {p q r : Plan α} {tr : List (MemOp × List Word)} : PlanTrace q tr r → PlanTrace (.alt p q) tr r
  | ev {o : MemOp} {k : List Word → Plan α} {res : List Word} {tr : List (MemOp × List Word)} {r : Plan α} :
      PlanTrace (k res) tr r → PlanTrace (.ev o k) ((o, res) :: tr) r

/-- Same code position: term, environment, type arguments, frames. -/
def SameCode (a b : TTh) : Prop := a.term = b.term ∧ a.env = b.env ∧ a.σs = b.σs ∧ a.stack = b.stack

/-- The rest of the op, run now with nothing in between, ends where the coarse
stepper lemma's output (`TOut`) holds, measured from the current state. -/
def ResidualOK (p : Prog) (g : G) (η : TEnv) (mem : Memory) (pairs : List Ts) (base : TTh)
    (q : Plan (St → TTh)) (Rf Rs H : Res) (cr db : Ts → Res) : Prop :=
  ∀ r ∈ (run g q (stOf mem pairs base)).map commit,
    ∃ (E' : TEnv) (Tot' HP' HS' C F : Res) (cr' db' δ : Ts → Res),
      TOut p g η (stOf mem pairs base) base r E' Tot' HP' HS' C F cr' db' Rf Rs H cr db δ

/-- **The pending-op clause** of busy thread `g.i`: it began the op at `th0`
(same code as `base`); the events done so far are a prefix of the op's plan;
it is typed at the op's term at its cut; memory satisfies its memory
invariants at its current local state (other threads may have grown memory);
and the rest of the op is typed against current memory. -/
def PendSys (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (base : TTh) (q : Plan (St → TTh))
    (Eg : GEnv) (Tot HP HS : Res) (cr db : Ts → Res) : Prop :=
  ∃ (th0 : TTh) (tr : List (MemOp × List Word)), PlanTrace (tstepP g th0) tr q ∧ SameCode th0 base ∧
    ∃ (S : AllocLabel → Prop) (ρ : Nat → Nat) (η : TEnv) (cx : Cx) (Rf Rs : Res),
      EnvAt p Eg g.i base Tot S ρ η cx Rf Rs ∧
      MemInv g (Cut Eg g.i S) (stOf mem pairs base) ∧
      MemHeldP (Cut Eg g.i S) (stOf mem pairs base) HP ∧ MemHeldS (Cut Eg g.i S) (stOf mem pairs base) HS ∧
      PromCr (Cut Eg g.i S) (stOf mem pairs base) cr db ∧
      ResidualOK p g η mem pairs base q Rf Rs (HP + HS) cr db

/-- **The micro invariant.** -/
structure SysInvMμ (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop)
    (c : CfgM) (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) : Prop where
  idle : ∀ i th, c.ths[i]? = some (.idle th) →
    ThSys p (gOfM p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i)
  busy : ∀ i base q, c.ths[i]? = some (.busy base q) →
    PendSys p (gOfM p k arch c i) c.mem c.pairs base q Eg (Tot i) (HP i) HS (cr i) (db i)
  held : MemHeldG Eg (baseCfg c) HS
  clo : GStoClo Eg
  shty : SharedTyOK Eg
  proms : PromsOK Eg (baseCfg c)
  fpok : ∀ i th (S : AllocLabel → Prop), (baseCfg c).ths[i]? = some th → FpOK (Cut Eg i S) (stOf c.mem c.pairs th)
  fresh : ∀ i th, (baseCfg c).ths[i]? = some th → ∀ j, th.nalloc ≤ j →
    GFreshL Eg (baseCfg c) th (freshLabel c.lbase c.n i j)
  bal : ∃ M, MintOK M ∧
    thSum c.ths.size (fun i => Tot i + pSumAt (baseCfg c) i (cr i) + HP i) + HS ≤
      Init + M + thSum c.ths.size (fun i => pSumAt (baseCfg c) i (db i))
  knet : ∀ key, ExclKey key → KeyNet (baseCfg c) Tot HP HS cr db key
  bf : c.boxFence = true
  boxtop : BoxTopG Eg (baseCfg c)
  disj : PromsDisj (baseCfg c)
  fpfree : FpOwnFree Eg (baseCfg c)
  plt : AllPromLt (baseCfg c)
  vwr : VWrLe (baseCfg c)
  frle : FrontierLe Eg c.mem.size
  rle : ∀ l, Eg.rini l ≤ Eg.ini l
  bnamed : GBoxNamed Eg
  -- The remaining fields are the rest of `SysInvN`'s fields, read at
  -- `baseCfg c` verbatim, so that `SysInvMμ` stays `SysInvN` read at the
  -- base configuration plus the pending-op clause.
  cmg : TermSys.GStoMg Eg
  zwIni : TermZwIni.ZwIniG Eg
  predHold : TermPredHold.PredHoldG Eg (baseCfg c)
  rid : ∃ rc, TermMain.RidOK (baseCfg c) Tot HP HS cr db rc
  promIni : TermMain.PromIniOK Eg (baseCfg c)
  promTy : TermMain.PromTyAOK Eg (baseCfg c)
  promNU : TermMain.PromNotUndef (baseCfg c)
  ownF : TermMain.OwnFreshZ (baseCfg c) Tot HP HS cr
  promNoTwo : TermMain.PromNoTwoOK Eg (baseCfg c)
  undefAt : TermUndefZ.UndefAtG Eg (TermRun.Cfg.mem (baseCfg c))
  ownKeyOwn : TermMain.OwnKeyOwnG (baseCfg c) Eg Tot
  ownPub : TermMain.OwnPubG (baseCfg c) Eg Tot HP HS
  boxPV : TermBoxZ.BoxPV Eg
  boxFrOwn : TermBoxZ.BoxFrOwn Eg (baseCfg c)
  boxFrLe : TermBoxZ.BoxFrLe Eg (Array.size (TermRun.Cfg.mem (baseCfg c)))
  vwrLt : ∀ (i : Nat) (th : TermRun.TTh), (TermRun.Cfg.ths (baseCfg c))[i]? = some th → WeakMem.VState.vWr (TermRun.TTh.vs th) ≤ Array.size (TermRun.Cfg.mem (baseCfg c)) - 1
  boxFrLt : TermBoxZ.BoxFrLe Eg (Array.size (TermRun.Cfg.mem (baseCfg c)) - 1)
  frlt : TermSys.FrontierLe Eg (Array.size (TermRun.Cfg.mem (baseCfg c)) - 1)
  payOwn : TermBoxZ.PayOwn Eg
  boxSto : TermBoxZ.BoxSto Eg
  ownCoh : ∀ (i : Nat) (th : TermRun.TTh) (S : WeakMem.AllocLabel → Prop), (TermRun.Cfg.ths (baseCfg c))[i]? = some th → TermOwnCohZ.OwnCohZ (TermCut.Cut Eg i S) (TermRun.stOf (TermRun.Cfg.mem (baseCfg c)) (TermRun.Cfg.pairs (baseCfg c)) th)
  riniCoh : ∀ (i : Nat) (th : TermRun.TTh) (S : WeakMem.AllocLabel → Prop), (TermRun.Cfg.ths (baseCfg c))[i]? = some th → TermTyped.RiniCoh (TermCut.Cut Eg i S) (TermRun.stOf (TermRun.Cfg.mem (baseCfg c)) (TermRun.Cfg.pairs (baseCfg c)) th)
  promInCut : TermPtrStab.PromInCut Eg (baseCfg c)
  promClos : TermMain.PromClosG Eg (baseCfg c)
  stoNI : TermMain.StoNI Eg
  undefLow : TermUndefLow.UndefLowG Eg (TermRun.Cfg.mem (baseCfg c))
  promAbove : TermOverCr.PromAboveG (baseCfg c)
  msgWords : TermMain.MsgWordsG Eg (baseCfg c)
  fgnClos : TermMain.FgnPromClosG Eg (baseCfg c)
  cellOwn : TermMain.CellOwnerLiveM Eg (baseCfg c)
  ptrGL : Promises.Knobs.storeDepRts k = true → TermPtrRts.PtrRtsGL Eg Tot HP (baseCfg c)
  granW : Promises.Knobs.storeDepRts k = true → Array.size (TermRun.Cfg.ths (baseCfg c)) = 0 ∨ TermPtrRts.GranuleW (TermCut.GEnv.sto Eg) (TermRun.Cfg.mem (baseCfg c)) (TermRun.Cfg.pairs (baseCfg c))
  stoLay : Promises.Knobs.storeDepRts k = true → ∀ (l : WeakMem.AllocLabel) (cl : TermSound.Cell), TermCut.GEnv.sto Eg l = some cl → TermSound.LayT (TermSound.Cell.ty cl)
  boxPlantSep : Promises.Knobs.storeDepRts k = true → TermPtrRts.BoxPlantSep Eg Tot HP (baseCfg c)
  fgnCnt : Promises.Knobs.storeDepRts k = true → TermMain.FgnPromCntG Eg (baseCfg c)
  pool : ∃ pl, TermPool.PoolTag Eg (baseCfg c) pl ∧ TermOverCr.OverCrG Eg (baseCfg c) (TermPool.crPl cr pl) ∧ (∃ M, MintOK M ∧ (TermSys.thSum (Array.size (TermRun.Cfg.ths (baseCfg c))) fun i => Tot i + TermSys.pSumAt (baseCfg c) i (TermPool.crPl cr pl i) + HP i) + HS ≤ Init + M + TermSys.thSum (Array.size (TermRun.Cfg.ths (baseCfg c))) fun i => TermSys.pSumAt (baseCfg c) i (db i)) ∧ (∀ (key : TermSound.Key), TermMain.ExclKey key → TermMain.KeyNet (baseCfg c) Tot HP HS (TermPool.crPl cr pl) db key) ∧ ∃ rc, TermMain.RidOK (baseCfg c) Tot HP HS (TermPool.crPl cr pl) db rc
  plantIdx : Promises.Knobs.storeDepRts k = true → TermPlantAtT.PlantIdxG TermPtrRts.tminG Eg Tot HP (baseCfg c)
  cfgCoh : TermLiveProps.CfgCoh (baseCfg c)
  stoW : ∀ (l : WeakMem.AllocLabel) (cl : TermSound.Cell), TermCut.GEnv.sto Eg l = some cl → TermA4.wrapTop (TermSound.Cell.ty cl) = true
  freshU : TermSys.FreshU (TermRun.Cfg.n (baseCfg c)) Eg (baseCfg c) Tot HP HS cr

def SysInvMμx (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c : CfgM) : Prop :=
  ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
    SysInvMμ p k arch Init MintOK c Eg Tot HP HS cr db

/-- **The target theorem `sysInv_stepMμ`, as a statement**: the micro
invariant is preserved by every micro step from a micro-reachable
configuration.  Not proved. -/
def SysInvStepMμ (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : CfgM}, StepsM p k arch (embed c0) c → SysInvMμx p k arch Init MintOK c → StepM p k arch c c' →
    SysInvMμx p k arch Init MintOK c'

variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}

theorem baseCfg_embed (c : Cfg) : baseCfg (embed c) = c := by
  cases c
  simp only [baseCfg, embed, Array.map_map]
  congr
  have : (TThM.base ∘ TThM.idle) = id := funext fun _ => rfl
  rw [this, Array.map_id]

/-- **At an all-idle configuration the micro invariant is `SysInvN`**: the
two invariants agree on the coarse reachable set's image. -/
theorem sysInvM_embed {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) :
    SysInvMμ p k arch Init MintOK (embed c) Eg Tot HP HS cr db := by
  have hb := baseCfg_embed c
  refine
    { idle := ?_, busy := ?_, held := by rw [hb]; exact h.held, clo := h.clo, shty := h.shty,
      proms := by rw [hb]; exact h.proms, fpok := by rw [hb]; exact h.fpok,
      fresh := by rw [hb]; simpa [embed, CfgM.n, Cfg.n] using h.fresh, bal := by rw [hb]; simpa [embed] using h.bal,
      knet := by rw [hb]; exact h.knet, bf := h.bf, boxtop := by rw [hb]; exact h.boxtop,
      disj := by rw [hb]; exact h.disj, fpfree := by rw [hb]; exact h.fpfree, plt := by rw [hb]; exact h.plt,
      vwr := by rw [hb]; exact h.vwr, frle := h.frle, rle := h.rle, bnamed := h.bnamed,
      cmg := by first | (rw [hb]; exact h.cmg) | exact h.cmg,
      zwIni := by first | (rw [hb]; exact h.zwIni) | exact h.zwIni,
      predHold := by first | (rw [hb]; exact h.predHold) | exact h.predHold,
      rid := by first | (rw [hb]; exact h.rid) | exact h.rid,
      promIni := by first | (rw [hb]; exact h.promIni) | exact h.promIni,
      promTy := by first | (rw [hb]; exact h.promTy) | exact h.promTy,
      promNU := by first | (rw [hb]; exact h.promNU) | exact h.promNU,
      ownF := by first | (rw [hb]; exact h.ownF) | exact h.ownF,
      promNoTwo := by first | (rw [hb]; exact h.promNoTwo) | exact h.promNoTwo,
      undefAt := by first | (rw [hb]; exact h.undefAt) | exact h.undefAt,
      ownKeyOwn := by first | (rw [hb]; exact h.ownKeyOwn) | exact h.ownKeyOwn,
      ownPub := by first | (rw [hb]; exact h.ownPub) | exact h.ownPub,
      boxPV := by first | (rw [hb]; exact h.boxPV) | exact h.boxPV,
      boxFrOwn := by first | (rw [hb]; exact h.boxFrOwn) | exact h.boxFrOwn,
      boxFrLe := by first | (rw [hb]; exact h.boxFrLe) | exact h.boxFrLe,
      vwrLt := by first | (rw [hb]; exact h.vwrLt) | exact h.vwrLt,
      boxFrLt := by first | (rw [hb]; exact h.boxFrLt) | exact h.boxFrLt,
      frlt := by first | (rw [hb]; exact h.frlt) | exact h.frlt,
      payOwn := by first | (rw [hb]; exact h.payOwn) | exact h.payOwn,
      boxSto := by first | (rw [hb]; exact h.boxSto) | exact h.boxSto,
      ownCoh := by first | (rw [hb]; exact h.ownCoh) | exact h.ownCoh,
      riniCoh := by first | (rw [hb]; exact h.riniCoh) | exact h.riniCoh,
      promInCut := by first | (rw [hb]; exact h.promInCut) | exact h.promInCut,
      promClos := by first | (rw [hb]; exact h.promClos) | exact h.promClos,
      stoNI := by first | (rw [hb]; exact h.stoNI) | exact h.stoNI,
      undefLow := by first | (rw [hb]; exact h.undefLow) | exact h.undefLow,
      promAbove := by first | (rw [hb]; exact h.promAbove) | exact h.promAbove,
      msgWords := by first | (rw [hb]; exact h.msgWords) | exact h.msgWords,
      fgnClos := by first | (rw [hb]; exact h.fgnClos) | exact h.fgnClos,
      cellOwn := by first | (rw [hb]; exact h.cellOwn) | exact h.cellOwn,
      ptrGL := by first | (rw [hb]; exact h.ptrGL) | exact h.ptrGL,
      granW := by first | (rw [hb]; exact h.granW) | exact h.granW,
      stoLay := by first | (rw [hb]; exact h.stoLay) | exact h.stoLay,
      boxPlantSep := by first | (rw [hb]; exact h.boxPlantSep) | exact h.boxPlantSep,
      fgnCnt := by first | (rw [hb]; exact h.fgnCnt) | exact h.fgnCnt,
      pool := by first | (rw [hb]; exact h.pool) | exact h.pool,
      plantIdx := by first | (rw [hb]; exact h.plantIdx) | exact h.plantIdx,
      cfgCoh := by first | (rw [hb]; exact h.cfgCoh) | exact h.cfgCoh,
      stoW := by first | (rw [hb]; exact h.stoW) | exact h.stoW,
      freshU := by first | (rw [hb]; exact h.freshU) | exact h.freshU }
  · intro i th hth
    rw [embed_get] at hth
    obtain ⟨th', h1, h2⟩ := Option.map_eq_some_iff.1 hth
    injection h2 with h2
    subst h2
    rw [gOfM_embed]
    exact h.thr i _ h1
  · intro i base q hth
    rw [embed_get] at hth
    obtain ⟨th', _, h2⟩ := Option.map_eq_some_iff.1 hth
    cases h2

/-- With the target, the micro invariant holds at every micro-reachable
configuration (`sysInv_run`'s micro sibling). -/
theorem sysInvM_run {c0 : Cfg} (hstep : SysInvStepMμ p k arch Init MintOK c0)
    (h0 : SysInvNx p k arch Init MintOK c0) {c : CfgM} (h : StepsM p k arch (embed c0) c) :
    SysInvMμx p k arch Init MintOK c := by
  have key : ∀ c1 c, StepsM p k arch c1 c → StepsM p k arch (embed c0) c1 → SysInvMμx p k arch Init MintOK c1 →
      SysInvMμx p k arch Init MintOK c := by
    intro c1 c hs
    induction hs with
    | refl => exact fun _ hi => hi
    | step hs1 _ ih =>
        intro hpre hi
        exact ih (hpre.trans (.step hs1 (.refl _))) (hstep hpre hi hs1)
  obtain ⟨Eg, Tot, HP, HS, cr, db, hi⟩ := h0
  exact key _ _ h (.refl _) ⟨Eg, Tot, HP, HS, cr, db, sysInvM_embed hi⟩

end

#print axioms evalOp_eq
#print axioms tstep_plan
#print axioms tstep_eq_run
#print axioms certified_certifiedM
#print axioms step_sim
#print axioms steps_sim
#print axioms sysInvM_embed
#print axioms sysInvM_run

end TermMicro
