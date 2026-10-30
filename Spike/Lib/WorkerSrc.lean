/-
**The worker's source side after its print** (the source
half of the worker's rows: `store rel c 1`, `unpark j`, the exit).
ISA-generic. The target half and the relation (`Spike.Lib.Inv2Core`,
`Spike.Lib.HelloProt`) are separate; here the `c` protocol `CProt` is
split into its target part `CProtT`, its source part `CProtS` and the
link of the two store points (`cProt_iff`), and the worker's source rows
re-establish `CProtS`, taking the target facts as hypotheses.

The worker's code after `print` is `wkStore`: `let d = store rel c 1 in let w
= unpark j in ret `, on an empty stack.

- `wkStore`, `wkUnpark`, `WPass`: the store point (the worker past its
  store: at `wkUnpark` or `ret `, on an empty stack).
- `wTh`, `helloC`: hello's `CRec`, its `mviewS`/`obS` the view and ordering
  bound of the worker's store (`Promises.storeMview`/`storeOb` at the
  pointer word `cw` of `c`; they read only the views).
- `CProtT`, `CProtS`, `cProt_iff`: the split of `CProt`.
- `stepStore_append_mem`, `stepStore_fulfil_mem`, `tstep_store_mem`: the
  source store's outcomes.
- `AtStore`: the worker at its store.
- `store_append_src` (with `cProtS_append`): the store with no promise
  appends `c`'s `1`.
- `store_fulfil_src` (with `fulfil_ok`, `cProtS_fulfil`): the store fulfils
  the mirrored promise `kc`.
- `certified_store`, `promise_get`, `prom_c_src`, `prom_c_src_atStore`
  (with `cProtS_prom`): the promise of `c`'s `1` at view `S - 1` (G3), and
  its certificate.
- `cProtS_vs`: steps that keep the worker's views and promises keep
  `CProtS`.
- `unpark_src` (with `cProtS_unpark`): `unpark j` sets main's permit.
- `worker_done`: at `ret ` on an empty stack the worker has finished (its
  exit is no source step).
- `scov_coh`: the frozen-word cover (`Inv2Core.scov1`) under a store to a
  word that is not frozen.
-/
import Spike.Lib.WorkerSrcStep
import Spike.Lib.Inv2Rely
import Spike.Lib.HelloProt

namespace Spike.Lib.WorkerSrc

open CoreLang CoreTerm TermRun TermExtStep
open Kraken.Promising Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.WorkerSrcStep

/-! ## The store point -/

/-- The worker after its store: `let w = unpark j in ret `. -/
def wkUnpark : Expr := .let_ "w" (.ext .unpark (.var "j")) (.ret .unit)

/-- The worker at its store: `let d = store rel c 1 in wkUnpark`. -/
def wkStore : Expr := .let_ "d" (.store true (.var "c") (.lit 1) none) wkUnpark

/-- **The source worker is past its store**: at `wkUnpark` or `ret `, on an
empty stack (inside `print` the stack is not empty, and before `print` the
worker is at neither term). -/
def WPass (s1 : TTh) : Prop := s1.stack = [] ∧ (s1.term = wkUnpark ∨ s1.term = .ret .unit)

/-- The value the worker stores. -/
abbrev one : Word := cst (.num 1)

/-- The promise-machine thread of the worker's store at views `vs`: register
0 the pointer word `cw`, registers 1 and 2 the stored `1` (as `mth`). -/
def wTh (vs : WeakMem.VState) (cw : Word) : Promises.Thread :=
  { prog := [], regs := regsOf cw one one, vs := vs, promises := [] }

/-- **hello's flag record**: `c`'s words `cT`/`cS`, the target store point
`passT`, the source store point `WPass`, and the store's view and
ordering bound at the worker's views, the pointer word of `c` being `cw`
(the word the worker holds for `c`, fixed from the spawn on). -/
def helloC {I : ISA} (cT : Loc) (cS : WeakMem.Address) (passT : I.State → Prop) (k : Promises.Knobs)
    (arch : WeakMem.Arch) (cw : Word) : CRec I where
  cT := cT
  cS := cS
  passT := passT
  passS := WPass
  mviewS s1 := Promises.storeMview (wTh s1.vs cw) (dataE 1 one) [0] true
  obS s1 := Promises.storeOb k arch (wTh s1.vs cw) cS (dataE 1 one) [0]

/-- The view the store publishes at a source state is `helloC`'s `mviewS`. -/
theorem storeMview_mth (mem : WeakMem.Memory) (pairs : List Nat) (th : TTh) (cw : Word) :
    Promises.storeMview (mth (stOf mem pairs th) cw one one) (dataE 1 one) [0] true =
      Promises.storeMview (wTh th.vs cw) (dataE 1 one) [0] true := rfl

/-- The store's ordering bound at a source state is `helloC`'s `obS`. -/
theorem storeOb_mth (k : Promises.Knobs) (arch : WeakMem.Arch) (mem : WeakMem.Memory) (pairs : List Nat)
    (th : TTh) (cw : Word) (a : WeakMem.Address) :
    Promises.storeOb k arch (mth (stOf mem pairs th) cw one one) a (dataE 1 one) [0] =
      Promises.storeOb k arch (wTh th.vs cw) a (dataE 1 one) [0] := rfl

/-! ## The split of `CProt` -/

section Split

variable {I : ISA} (R : SpawnRec) (C : CRec I) (oc : Option (Nat × Nat))

/-- **The target part of the `c` protocol** (the rows keep it). -/
structure CProtT (tm : Memory) (t1 : Thread I) (ts : Nat → Option Nat) (tp : List Nat) : Prop where
  tmsg : ∀ k w, tm.get? k = some w → R.T < k → w.loc = C.cT → ∃ kc, oc = some (k, kc) ∧ w.tid = 1
  some_msg : ∀ Tc kc, oc = some (Tc, kc) →
    R.T < Tc ∧ ts kc = some Tc ∧ ∃ w, tm.get? Tc = some w ∧ w.loc = C.cT ∧ w.tid = 1 ∧ w.val = 1
  prom_worker : ∀ Tc kc, oc = some (Tc, kc) → Tc ∈ tp → Tc ∈ t1.prom
  pass_done : C.passT t1.st → ∃ Tc kc, oc = some (Tc, kc) ∧ Tc ∉ tp
  pass_prom : ¬ C.passT t1.st → ∀ Tc kc, oc = some (Tc, kc) → Tc ∈ tp

/-- **The source part of the `c` protocol** (the worker's source rows keep
it): `kc` the only source message to `c` after the spawn, of value `1`; a
mirrored promise is the source worker's; G1–G3. -/
structure CProtS (sm : WeakMem.Memory) (s1 : TermRun.TTh) (tp sp : List Nat) : Prop where
  smsg : ∀ k m, sm[k]? = some m → R.S ≤ k → m.loc = C.cS → ∃ Tc, oc = some (Tc, k)
  some_msg : ∀ Tc kc, oc = some (Tc, kc) → R.S ≤ kc ∧ ∃ m, sm[kc]? = some m ∧ m.loc = C.cS ∧ m.val = .num 1
  prom_worker : ∀ Tc kc, oc = some (Tc, kc) → Tc ∈ tp → kc ∈ s1.promises
  pre_lt : ¬ C.passS s1 → C.mviewS s1 < R.S ∧ C.obS s1 < R.S
  prom_view : ∀ Tc kc m, oc = some (Tc, kc) → kc ∈ sp → sm[kc]? = some m → R.S ≤ m.view + 1

/-- **`CProt` is its target part, its source part and the link of the two
store points.** -/
theorem cProt_iff {tm : Memory} {t1 : Thread I} {sm : WeakMem.Memory} {s1 : TermRun.TTh}
    {ts : Nat → Option Nat} {tp sp : List Nat} :
    CProt R C oc tm t1 sm s1 ts tp sp ↔
      CProtT R C oc tm t1 ts tp ∧ CProtS R C oc sm s1 tp sp ∧ (C.passT t1.st ↔ C.passS s1) := by
  constructor
  · intro h
    refine ⟨⟨h.tmsg, fun Tc kc hoc => ?_, fun Tc kc hoc htp => (h.prom_worker Tc kc hoc htp).1, h.pass_done,
      h.pass_prom⟩, ⟨h.smsg, fun Tc kc hoc => ?_, fun Tc kc hoc htp => (h.prom_worker Tc kc hoc htp).2, h.pre_lt,
      h.prom_view⟩, h.pass_iff⟩
    · obtain ⟨h1, -, h3, h4, -⟩ := h.some_msg Tc kc hoc
      exact ⟨h1, h3, h4⟩
    · obtain ⟨-, h2, -, -, h5⟩ := h.some_msg Tc kc hoc
      exact ⟨h2, h5⟩
  · rintro ⟨hT, hS, hl⟩
    refine ⟨hT.tmsg, hS.smsg, fun Tc kc hoc => ?_, fun Tc kc hoc htp => ⟨hT.prom_worker Tc kc hoc htp,
      hS.prom_worker Tc kc hoc htp⟩, hl, hT.pass_done, hT.pass_prom, hS.pre_lt, hS.prom_view⟩
    obtain ⟨h1, h3, h4⟩ := hT.some_msg Tc kc hoc
    obtain ⟨h2, h5⟩ := hS.some_msg Tc kc hoc
    exact ⟨h1, h2, h3, h4, h5⟩

end Split

/-! ## The source store's outcomes -/

/-- **The appending outcome of a store**: the message of the value and the
store's view at `mem.size`; the thread's coherence view at `a` becomes
`mem.size` and is unchanged elsewhere; the promises are kept. -/
theorem stepStore_append_mem (k : Promises.Knobs) (arch : WeakMem.Arch) (mem : WeakMem.Memory) (th : Promises.Thread)
    (a : WeakMem.Address) (e : WeakMem.Expr) (deps : List WeakMem.Reg) (rel : Bool) :
    ∃ th', (mem.push ⟨a, Promises.rmwNewVal th.regs e, Promises.storeMview th e deps rel⟩, th') ∈
        Promises.stepStore k arch mem th a e deps rel ∧ th'.promises = th.promises ∧ th'.vs.coh a = mem.size ∧
      ∀ b, b ≠ a → th'.vs.coh b = th.vs.coh b := by
  cases e <;>
    exact ⟨_, List.mem_append_left _ (List.mem_singleton.mpr rfl), rfl, by simp, fun b hb => by simp [hb]⟩

/-- **The fulfilling outcome of a store**: a promise `t` of the thread to `a`
with the store's value, whose view covers the store's view and above the
store's ordering bound, is fulfilled; memory is unchanged, `t` leaves the
promises; the coherence view at `a` becomes `t`, unchanged elsewhere. -/
theorem stepStore_fulfil_mem {k : Promises.Knobs} {arch : WeakMem.Arch} {mem : WeakMem.Memory} {th : Promises.Thread}
    {a : WeakMem.Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} {t : Nat} {m : WeakMem.Msg}
    (ht : t ∈ th.promises) (hm : mem[t]? = some m) (hl : m.loc = a) (hv : m.val = Promises.rmwNewVal th.regs e)
    (hmv : Promises.storeMview th e deps rel ≤ m.view) (hob : Promises.storeOb k arch th a e deps < t) :
    ∃ th', (mem, th') ∈ Promises.stepStore k arch mem th a e deps rel ∧ th'.promises = th.promises.erase t ∧
      th'.vs.coh a = t ∧ ∀ b, b ≠ a → th'.vs.coh b = th.vs.coh b := by
  refine ⟨{ th with
      vs := { th.vs with coh := fun b => if b = a then t else th.vs.coh b, vWr := max th.vs.vWr t,
                         mine := t :: th.vs.mine,
                         fwd := if k.fwdView then (t, Promises.fwdOf th.regs e deps) :: th.vs.fwd else th.vs.fwd }
      promises := th.promises.erase t }, ?_⟩
  cases e <;> simp only [Promises.rmwNewVal] at hv <;>
  · refine ⟨List.mem_append_right _ (List.mem_filterMap.mpr ⟨t, ht, ?_⟩), ?_, ?_, ?_⟩
    · simp only [hm, hl, hv, beq_self_eq_true, hmv, hob, decide_true, Bool.and_self, ite_true]
    · rfl
    · simp
    · intro b hb; simp [hb]

/-- **A store outcome is a `tstep` outcome**: at `let x = store rel a v none in
e` with the address word an untagged locative to a one-word cell, each
outcome `(mem', th1)` of the one unit's `stepStore` (the pointer word in
register 0, the value in register 1) is a successor binding `x` to ``,
with `th1`'s views and promises. -/
theorem tstep_store_mem {g : G} {mem : WeakMem.Memory} {pairs : List Nat} {th : TTh} {x : String} {rel : Bool}
    {a v : At} {e : Expr} {t tv : Ty} {pw wv : Word} {μ : Mode} {u : Ty} {sa : WeakMem.Address}
    (ht : th.term = .let_ x (.store rel a v none) e) (hea : evalAt th.env a = some (t, [pw]))
    (hev : evalAt th.env v = some (tv, [wv])) (hpw : pw.val = .loc sa 0) (hcell : cellOf t = some (μ, u))
    (hu : accs u = some [.one]) {mem' : WeakMem.Memory} {th1 : Promises.Thread}
    (hs : (mem', th1) ∈ Promises.stepStore g.k g.arch mem (mth (stOf mem pairs th) pw wv wv) sa (dataE 1 wv) [0] rel) :
    (mem', pairs, { th with term := e, env := (x, .unit, []) :: th.env, vs := th1.vs, promises := th1.promises }) ∈
      tstep g mem pairs th := by
  have hsu : { stOf mem pairs th with mem := mem', vs := th1.vs, promises := th1.promises } ∈
      storeUnits g.k g.arch pw sa rel [.one] [wv] 0 (stOf mem pairs th) := by
    simp only [storeUnits, SrcMem.offs_zero, List.mem_flatMap]
    exact ⟨_, hs, List.mem_singleton.mpr rfl⟩
  simp only [tstep, ht, evalOp, hea, hev, hcell, addrOf, hpw, hu, List.mem_map]
  exact ⟨_, ⟨_, hsu, rfl⟩, rfl⟩

/-! ## The worker at its store -/

/-- **The source worker at its store**, its pointer word for `c` being `cw`
(an untagged locative to `cS`, a one-word cell): term `wkStore`, empty
stack, no type variables. -/
structure AtStore (cw : Word) (cS : WeakMem.Address) (th : TTh) : Prop where
  term : th.term = wkStore
  stack : th.stack = []
  σs : th.σs = []
  c : ∃ t μ u, evalAt th.env (.var "c") = some (t, [cw]) ∧ cellOf t = some (μ, u) ∧ accs u = some [.one]
  cw : cw.val = .loc cS 0

/-- The worker past its store binds `d` to ``. -/
def afterStore (th : TTh) (vs : WeakMem.VState) (prom : List Nat) : TTh :=
  { th with term := wkUnpark, env := ("d", .unit, []) :: th.env, vs := vs, promises := prom }

theorem wPass_afterStore {th : TTh} (hst : th.stack = []) (vs : WeakMem.VState) (prom : List Nat) :
    WPass (afterStore th vs prom) := ⟨hst, .inl rfl⟩

theorem not_wPass_atStore {cw : Word} {cS : WeakMem.Address} {th : TTh} (h : AtStore cw cS th) : ¬ WPass th := by
  rintro ⟨-, h1 | h1⟩ <;> rw [h.term] at h1 <;> simp [wkStore, wkUnpark] at h1

/-- The store's `tstep` outcome from the promise machine's (`tstep_store_mem`
at the worker's store). -/
theorem atStore_tstep {g : G} {mem : WeakMem.Memory} {pairs : List Nat} {th : TTh} {cw : Word} {cS : WeakMem.Address}
    (h : AtStore cw cS th) {mem' : WeakMem.Memory} {th1 : Promises.Thread}
    (hs : (mem', th1) ∈ Promises.stepStore g.k g.arch mem (mth (stOf mem pairs th) cw one one) cS (dataE 1 one) [0] true) :
    (mem', pairs, afterStore th th1.vs th1.promises) ∈ tstep g mem pairs th := by
  obtain ⟨t, μ, u, hc, hcell, hu⟩ := h.c
  exact tstep_store_mem (v := .lit 1) (tv := .intS (.lit 1)) h.term hc rfl h.cw hcell hu hs

variable {P : SrcParams} {p : Prog}

/-! ## The store, appending -/

/-- **The worker's store with no promise appends** `c`'s `1` at the store's
view (`mviewS`) as message `s.mem.size`: a source step of thread 1 with the
empty trace; the worker is past its store, its coherence view at `cS` is
the new message and unchanged elsewhere. -/
theorem store_append_src (hP : UsesWc P p) {s : Cfg} {th : TTh} {cw : Word} {cS : WeakMem.Address}
    (hi : s.ths[1]? = some th) (hA : AtStore cw cS th) (hp : th.promises = []) (hex : mainExit s = []) :
    ∃ vs, (source P p).step 1 s []
        { s with mem := s.mem.push ⟨cS, .num 1, Promises.storeMview (wTh th.vs cw) (dataE 1 one) [0] true⟩,
                 ths := s.ths.set! 1 (afterStore th vs []) } ∧
      vs.coh cS = s.mem.size ∧ ∀ b, b ≠ cS → vs.coh b = th.vs.coh b := by
  obtain ⟨th1, hs, hp1, hc1, hc2⟩ := stepStore_append_mem P.k P.arch s.mem (mth (stOf s.mem s.pairs th) cw one one) cS
    (dataE 1 one) [0] true
  have hp1' : th1.promises = [] := by rw [hp1]; exact hp
  have hm := atStore_tstep (g := gOf p P.k P.arch s 1) hA hs
  rw [hp1'] at hm
  refine ⟨th1.vs, ?_, hc1, hc2⟩
  exact tstep_source_i_nil hP (by decide) hi hm rfl hex

/-- **`CProtS` after the append**: from `oc = none`, the new message
`sm.size` (at or after the spawn) is `kc`, paired with the target's `Tc`;
the worker past its store; `Tc` not mirrored and `kc` no promise. -/
theorem cProtS_append {I : ISA} {R : SpawnRec} {C : CRec I} {sm : WeakMem.Memory} {s1 s1' : TTh} {tp sp tp' sp' : List Nat}
    {Tc mv : Nat} (h : CProtS R C none sm s1 tp sp) (hS : R.S ≤ sm.size) (hpass : C.passS s1')
    (htp : Tc ∉ tp') (hsp : sm.size ∉ sp') :
    CProtS R C (some (Tc, sm.size)) (sm.push ⟨C.cS, .num 1, mv⟩) s1' tp' sp' := by
  refine ⟨fun k m hk hkS hl => ?_, fun Tc' kc hoc => ?_, fun Tc' kc hoc htp' => ?_, fun hn => absurd hpass hn,
    fun Tc' kc m hoc hkc => ?_⟩
  · rw [Array.getElem?_push] at hk
    split at hk
    · rename_i he; subst he; exact ⟨Tc, rfl⟩
    · obtain ⟨Tc', h'⟩ := h.smsg k m hk hkS hl; cases h'
  · cases hoc
    exact ⟨hS, ⟨C.cS, .num 1, mv⟩, by simp, rfl, rfl⟩
  · cases hoc; exact absurd htp' htp
  · cases hoc; exact absurd hkc hsp

/-! ## The store, fulfilling -/

/-- **The fulfilment side conditions from `CProtS`**: before its store, with
`kc` a promise of the worker in `sp`, the store's view is at most `kc`'s
(G1, G3: `mviewS < S ≤ m.view + 1`) and its ordering bound below `kc` (G2:
`obS < S ≤ kc`). -/
theorem fulfil_ok {I : ISA} {R : SpawnRec} {C : CRec I} {sm : WeakMem.Memory} {s1 : TTh} {tp sp : List Nat}
    {Tc kc : Nat} {m : WeakMem.Msg} (h : CProtS R C (some (Tc, kc)) sm s1 tp sp) (hpass : ¬ C.passS s1)
    (hkc : kc ∈ sp) (hm : sm[kc]? = some m) :
    C.mviewS s1 ≤ m.view ∧ C.obS s1 < kc := by
  obtain ⟨h1, h2⟩ := h.pre_lt hpass
  have h3 := h.prom_view Tc kc m rfl hkc hm
  have h4 := (h.some_msg Tc kc rfl).1
  omega

/-- **The worker's store fulfils its promise `kc`** of `c`'s `1`: a source
step of thread 1 with the empty trace; memory is unchanged, `kc` leaves the
promises; the worker's coherence view at `cS` is `kc`, unchanged elsewhere. -/
theorem store_fulfil_src (hP : UsesWc P p) {s : Cfg} {th : TTh} {cw : Word} {cS : WeakMem.Address} {kc : Nat}
    {m : WeakMem.Msg} (hi : s.ths[1]? = some th) (hA : AtStore cw cS th) (hp : th.promises = [kc])
    (hm : s.mem[kc]? = some m) (hl : m.loc = cS) (hv : m.val = .num 1)
    (hmv : Promises.storeMview (wTh th.vs cw) (dataE 1 one) [0] true ≤ m.view)
    (hob : Promises.storeOb P.k P.arch (wTh th.vs cw) cS (dataE 1 one) [0] < kc) (hex : mainExit s = []) :
    ∃ vs, (source P p).step 1 s [] { s with ths := s.ths.set! 1 (afterStore th vs []) } ∧
      vs.coh cS = kc ∧ ∀ b, b ≠ cS → vs.coh b = th.vs.coh b := by
  obtain ⟨th1, hs, hp1, hc1, hc2⟩ := stepStore_fulfil_mem (k := P.k) (arch := P.arch) (deps := [0]) (rel := true)
    (th := mth (stOf s.mem s.pairs th) cw one one) (e := dataE 1 one) (t := kc) (by simp [mth, stOf, hp]) hm hl
    (by rw [hv]; rfl) hmv hob
  have hp1' : th1.promises = [] := by rw [hp1]; simp [mth, stOf, hp]
  have hm' := atStore_tstep (g := gOf p P.k P.arch s 1) hA hs
  rw [hp1'] at hm'
  refine ⟨th1.vs, ?_, hc1, hc2⟩
  have := tstep_source_i_nil (mem' := s.mem) (pairs' := s.pairs) hP (by decide) hi hm' rfl hex
  exact this

/-- **`CProtS` after the fulfilment**: `oc` and memory unchanged; the worker
past its store; `Tc` no longer mirrored; `kc` was in `sp` (so G3 held for
it). -/
theorem cProtS_fulfil {I : ISA} {R : SpawnRec} {C : CRec I} {sm : WeakMem.Memory} {s1 s1' : TTh}
    {tp sp tp' sp' : List Nat} {Tc kc : Nat} (h : CProtS R C (some (Tc, kc)) sm s1 tp sp) (hkc : kc ∈ sp)
    (hpass : C.passS s1') (htp : Tc ∉ tp') :
    CProtS R C (some (Tc, kc)) sm s1' tp' sp' := by
  refine ⟨h.smsg, h.some_msg, fun Tc' kc' hoc htp' => ?_, fun hn => absurd hpass hn, fun Tc' kc' m hoc _ hm => ?_⟩
  · cases hoc; exact absurd htp' htp
  · cases hoc; exact h.prom_view Tc kc m rfl hkc hm

/-! ## The promise -/

/-- **A certificate at the store**: with the worker at its store, its one
promise `t` a message of `c`'s `1` at a view covering the store's and above
its ordering bound, the fulfilment is a certificate. -/
theorem certified_store {k : Promises.Knobs} {arch : WeakMem.Arch} {c : Cfg} {th : TTh} {cw : Word}
    {cS : WeakMem.Address} {t w : Nat} (hi : c.ths[1]? = some th) (hA : AtStore cw cS th) (hp : th.promises = [t])
    (hm : c.mem[t]? = some ⟨cS, .num 1, w⟩) (hmv : Promises.storeMview (wTh th.vs cw) (dataE 1 one) [0] true ≤ w)
    (hob : Promises.storeOb k arch (wTh th.vs cw) cS (dataE 1 one) [0] < t) :
    Certified p k arch c 1 := by
  obtain ⟨th1, hs, hp1, -, -⟩ := stepStore_fulfil_mem (k := k) (arch := arch) (deps := [0]) (rel := true)
    (th := mth (stOf c.mem c.pairs th) cw one one) (e := dataE 1 one) (t := t) (by simp [mth, stOf, hp]) hm rfl rfl
    hmv hob
  have hp1' : th1.promises = [] := by rw [hp1]; simp [mth, stOf, hp]
  have hm' := atStore_tstep (g := gOf p k arch c 1) hA hs
  refine certified_of_solo (.thread (SrcMem.mem_threadSteps hi hm') (.refl _))
    (certified_nil (getElem?_set!_self hi _) ?_)
  simp [afterStore, hp1']

/-- Thread `i` after its promise: the promise appended. -/
theorem promise_get {c : Cfg} {i : Nat} {th : TTh} (hi : c.ths[i]? = some th) (a : WeakMem.Address) (v : WeakMem.Val)
    (w : Nat) : (promise c i a v w).ths[i]? = some { th with promises := th.promises ++ [c.mem.size] } ∧
      (promise c i a v w).mem = c.mem.push ⟨a, v, w⟩ := by
  unfold promise
  rw [hi]
  exact ⟨getElem?_set!_self hi _, rfl⟩

/-- **The promise of `c`'s `1`**, certified, is a source step of thread 1 with
the empty trace (`prom_source_i`). The view is the caller's; G3 asks for
`S - 1`. -/
theorem prom_c_src (hP : UsesWc P p) {s : Cfg} {cS : WeakMem.Address} {w : Nat} (hlt : 1 < s.ths.size)
    (hw : w < s.mem.size) (hc : Certified p P.k P.arch (promise s 1 cS (.num 1) w) 1) (hex : mainExit s = []) :
    (source P p).step 1 s [] (promise s 1 cS (.num 1) w) :=
  prom_source_i hP (by decide) hlt hw hc hex

/-- **The promise of `c`'s `1` at the store**: with the worker at its store
and no promise, a promise at view `w` covering the store's view, the store's
ordering bound below the memory size, is a source step of thread 1 (the
certificate is the fulfilment, `certified_store`). -/
theorem prom_c_src_atStore (hP : UsesWc P p) {s : Cfg} {th : TTh} {cw : Word} {cS : WeakMem.Address} {w : Nat}
    (hi : s.ths[1]? = some th) (hA : AtStore cw cS th) (hp : th.promises = []) (hw : w < s.mem.size)
    (hmv : Promises.storeMview (wTh th.vs cw) (dataE 1 one) [0] true ≤ w)
    (hob : Promises.storeOb P.k P.arch (wTh th.vs cw) cS (dataE 1 one) [0] < s.mem.size) (hex : mainExit s = []) :
    (source P p).step 1 s [] (promise s 1 cS (.num 1) w) := by
  have hlt : 1 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  obtain ⟨h1, h2⟩ := promise_get hi cS (.num 1) w
  refine prom_c_src hP hlt hw (certified_store (cw := cw) h1 ⟨hA.term, hA.stack, hA.σs, hA.c, hA.cw⟩
    (by simp [hp]) ?_ hmv hob) hex
  rw [h2]; simp

/-- **`CProtS` after the promise** of `c`'s `1` at view `S - 1` (G3): from
`oc = none`, the new message `sm.size` is `kc`, the worker's promise;
G1/G2 read only the views and the store point, which the promise keeps. -/
theorem cProtS_prom {I : ISA} {R : SpawnRec} {C : CRec I} {sm : WeakMem.Memory} {s1 : TTh} {tp sp tp' sp' : List Nat}
    {Tc : Nat} (h : CProtS R C none sm s1 tp sp) (hS : R.S ≤ sm.size) (hS0 : 0 < R.S)
    (hvs : ∀ th : TTh, th.vs = s1.vs → C.mviewS th = C.mviewS s1 ∧ C.obS th = C.obS s1)
    (hpass : ∀ th : TTh, th.term = s1.term → th.stack = s1.stack → (C.passS th ↔ C.passS s1)) :
    CProtS R C (some (Tc, sm.size)) (sm.push ⟨C.cS, .num 1, R.S - 1⟩)
      { s1 with promises := s1.promises ++ [sm.size] } tp' sp' := by
  refine ⟨fun k m hk hkS hl => ?_, fun Tc' kc hoc => ?_, fun Tc' kc hoc _ => ?_, fun hn => ?_,
    fun Tc' kc m hoc _ hm => ?_⟩
  · rw [Array.getElem?_push] at hk
    split at hk
    · rename_i he; subst he; exact ⟨Tc, rfl⟩
    · obtain ⟨Tc', h'⟩ := h.smsg k m hk hkS hl; cases h'
  · cases hoc
    exact ⟨hS, ⟨C.cS, .num 1, R.S - 1⟩, by simp, rfl, rfl⟩
  · cases hoc; simp
  · rw [hpass { s1 with promises := s1.promises ++ [sm.size] } rfl rfl] at hn
    obtain ⟨e1, e2⟩ := hvs { s1 with promises := s1.promises ++ [sm.size] } rfl
    rw [e1, e2]; exact h.pre_lt hn
  · cases hoc
    simp at hm
    subst hm
    simp only
    omega

/-- `helloC`'s `mviewS`/`obS` read only the views, and its store point only
the term and stack (the side conditions of `cProtS_prom`, `cProtS_vs`). -/
theorem helloC_vs {I : ISA} {cT : Loc} {cS : WeakMem.Address} {passT : I.State → Prop} {k : Promises.Knobs}
    {arch : WeakMem.Arch} {cw : Word} {s1 : TTh} :
    (∀ th : TTh, th.vs = s1.vs → (helloC cT cS passT k arch cw).mviewS th = (helloC cT cS passT k arch cw).mviewS s1 ∧
        (helloC cT cS passT k arch cw).obS th = (helloC cT cS passT k arch cw).obS s1) ∧
      ∀ th : TTh, th.term = s1.term → th.stack = s1.stack →
        ((helloC cT cS passT k arch cw).passS th ↔ (helloC cT cS passT k arch cw).passS s1) := by
  refine ⟨fun th h => ?_, fun th h1 h2 => ?_⟩
  · simp only [helloC, h, and_self]
  · simp only [helloC, WPass, h1, h2]

/-- **Steps that keep the worker's views and promises keep `CProtS`**, when
they do not leave the store point before the store (local steps, a frame
pop, `unpark` after the store) and memory is kept. -/
theorem cProtS_vs {I : ISA} {R : SpawnRec} {C : CRec I} {oc : Option (Nat × Nat)} {sm : WeakMem.Memory}
    {s1 s1' : TTh} {tp sp : List Nat} (h : CProtS R C oc sm s1 tp sp)
    (hvs : C.mviewS s1' = C.mviewS s1 ∧ C.obS s1' = C.obS s1) (hp : s1'.promises = s1.promises)
    (hpass : ¬ C.passS s1' → ¬ C.passS s1) :
    CProtS R C oc sm s1' tp sp :=
  ⟨h.smsg, h.some_msg, fun Tc kc hoc htp => hp ▸ h.prom_worker Tc kc hoc htp,
    fun hn => hvs.1 ▸ hvs.2 ▸ h.pre_lt (hpass hn), h.prom_view⟩

/-! ## `unpark` and the exit -/

/-- **The worker's `unpark j`** after its store, naming main (`thrOfTid s jw =
some 0`): a source step of thread 1 with the empty trace; main gets a permit
carrying the worker's release view; the worker moves to `ret `; memory is
kept. -/
theorem unpark_src (hP : UsesWc P p) {s : Cfg} {th th0 : TTh} {jw : Word} {rt : Ty}
    (hi : s.ths[1]? = some th) (h0 : s.ths[0]? = some th0) (ht : th.term = wkUnpark) (hp : th.promises = [])
    (hj : evalAt th.env (.var "j") = some (rt, [jw])) (hw : thrOfTid s jw = some 0) (hex : mainExit s = []) :
    ∃ s', (source P p).step 1 s [] s' ∧ s'.mem = s.mem ∧
      s'.ths[0]? = some { th0 with permit := some (max (th0.permit.getD 0) (relView th.vs)) } ∧
      s'.ths[1]? = some { th with term := .ret .unit, env := ("w", ExtName.unpark.sig.2, []) :: th.env } := by
  have hc : Certified p P.k P.arch (extCfg s 1 th "w" .unpark (.ret .unit) [jw] []) 1 :=
    certified_nil (extCfg_ths_self hi "w" .unpark (.ret .unit) [jw] [] (by decide)) (by simpa using hp)
  obtain ⟨g0, g1⟩ := wake_unpark_get (x := "w") (e := .ret .unit) (by decide) hi h0 hw
  exact ⟨_, unpark_src_i hP (by decide) hi ht hj hc hex, by rw [wake_mem]; simp [extCfg], g0, g1⟩

/-- **`CProtS` after `unpark`**: the worker stays past its store, its views
and promises kept. -/
theorem cProtS_unpark {I : ISA} {R : SpawnRec} {C : CRec I} {oc : Option (Nat × Nat)} {sm : WeakMem.Memory}
    {s1 s1' : TTh} {tp sp : List Nat} (h : CProtS R C oc sm s1 tp sp) (hpass : C.passS s1')
    (hp : s1'.promises = s1.promises) : CProtS R C oc sm s1' tp sp :=
  ⟨h.smsg, h.some_msg, fun Tc kc hoc htp => hp ▸ h.prom_worker Tc kc hoc htp, fun hn => absurd hpass hn,
    h.prom_view⟩

/-- **The worker's exit**: at `ret ` on an empty stack the worker has
finished (`isDone`) and takes no thread step; its target `exit` pairs with
no source step. -/
theorem worker_done {g : G} {mem : WeakMem.Memory} {pairs : List Nat} {th : TTh} {a : At} (ht : th.term = .ret a)
    (hst : th.stack = []) : isDone th = true ∧ tstep g mem pairs th = [] := by
  refine ⟨by simp [isDone, ht, hst], ?_⟩
  simp [tstep, ht, hst]

/-! ## The frozen-word cover -/

/-- **The frozen-word cover under a store to a word that is not frozen**
(`Inv2Core.scov1`): a pushed message outside the frozen words, and a
coherence view raised at most at that word, keep it. -/
theorem scov_coh {sm : WeakMem.Memory} {frzS : WeakMem.Address → Prop} {coh coh' : WeakMem.Address → Nat}
    (h : ∀ k m, sm[k]? = some m → frzS m.loc → k ≤ coh m.loc) (hc : ∀ b, frzS b → coh b ≤ coh' b) :
    ∀ k m, sm[k]? = some m → frzS m.loc → k ≤ coh' m.loc :=
  fun k m hk hz => Nat.le_trans (h k m hk hz) (hc _ hz)

end Spike.Lib.WorkerSrc
