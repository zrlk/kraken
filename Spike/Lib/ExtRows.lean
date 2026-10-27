/-
**The source-local rows of `Out` under the one-thread invariant**: for an
instruction step of the canonical machine (`Spike.Lib.ExtThread.step_cases`,
first case: one `stepOne` outcome `o`) from a thread whose state has an
`Out` row, the rows the source matches by a local run keep `Inv1` and land
in the fragment.

- `row_silent`, `row_choice`: no memory access (`inv1_silent`).
- `row_rtLoad`: a load at a runtime address, any value (`inv1_rtLoad`).
- `row_rtStore`: a one-word store outside every placed label
  (`MemSide.ofLabels`'s `rt`, `Inv1.rtStore`).
- `row_load`, `row_store`: the one-word load and store rows, target side,
  with the source's load of the latest message / store, at the untagged
  locative the address word is (`Inv1.load_src`, `Inv1.store_src`).
- `out_local`: the case analysis of an `Out` row under
  `MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl` off a system call,
  for code whose trees write words only, the memory satisfying `MemInv G`
  (a runtime load reads a `G` value), and the words the thread owns reading as
their values (`OwnOk`): a local row (source
  local run, fragment, `Inv1`), or the instruction is a one-word load or
  store (`Out.load`, `Out.store`) or one of the two accesses of an exchange
  (`Out.holdLoad`, `Out.xchgStore`): matched by a source memory step or
  stutter, not here; or the two runtime steps of a buffer allocation
  (`Out.ctrRmw`, the heap counter's add, a stutter into the hold, `Inv1`
  kept; `Out.alloc`, memory unchanged, `Inv1` kept), matched by the
  consumer.
- `out_mem`: the memory after the outcome (unchanged, or one word
  appended: a runtime store of a `G` value, a store row's or an exchange's).
- `out_localP`, `out_memP`: the same under outstanding promises, the value
  invariant `G` for the messages not promised and the initial values only
  (`MsgsExcept`, as on a certification run); `out_memP` also says whether
  the word written is appended or fulfils a promise.
- `out_progress`, `out_no_error`: off a system call an `Out` row has an
  outcome with no promise (a thread with no promise, its values at most
  `|M|`: a load reads `exists_read`'s timestamp, a store writes at
  `|M| + 1`), and no error outcome.
-/
import Spike.Lib.ExtThread
import Spike.Lib.Mem
import Scc.Sem.RowsSrc
import Spike.Bridge.Progress
import Spike.Lib.RtRmw
import Scc.Sem.OwnWord
import Scc.Sem.CertStep

namespace Spike.Lib.ExtRows

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.Lower Scc.Sem Spike.Lib.ExtThread
open Kraken.Promising.Live.TicketStep (ctx0)

variable {I : ISA} {A : Arch} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory}
  {sm : WeakMem.Memory} {tid : Nat} {outs : List (Except String (Kraken.Promising.Outcome I))}
  {o : Kraken.Promising.Outcome I} {p : Prog} {X : Frag I} {c : Ctl} {G : Loc → Val → Prop}
  {mh mc mcl : Nat} {mu mo : Nat → Ty → Nat} {mown : I.State → List (Loc × Val)} {mmp : Loc → Bool → Prop}
  {mab : I.State → Prop} {mpl : I.State → Ctl → Prop} {mxa : WeakMem.AllocLabel → Nat → Nat → Frag I}

/-- **The runtime words a thread owns read as their values** (`MemSide.own`):
each is a word, and the latest write of it not promised has the value
(`OwnVal`). -/
def OwnOk (own : List (Loc × Val)) (tm : Memory) (prom : List Time) : Prop :=
  ∀ L v, (L, v) ∈ own → L.bytes = 8 ∧ OwnVal tm prom L.addr.toNat v

/-- A read of the latest write not promised of an owned word returns its
value. -/
theorem OwnOk.read {own : List (Loc × Val)} {tm : Memory} {prom : List Time} (h : OwnOk own tm prom) {a tr : Nat}
    {v : Val} (hl : TLatestP tm prom a tr) (hr : tm.read? (wordLoc a) tr = some v) :
    ∀ w, (wordLoc a, w) ∈ own → v = w := by
  intro w hw
  obtain ⟨-, k, hk, hv⟩ := h _ _ hw
  have he : wordLoc (wordLoc a).addr.toNat = wordLoc a := by simp only [wordLoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold TLatestP at hk
  rw [he] at hk hv
  rw [hl.unique hk, hv] at hr
  exact (Option.some.inj hr).symm

/-- An 8-byte location is the word at its address. -/
theorem loc_wordLoc {L : Loc} (h : L.bytes = 8) : L = wordLoc L.addr.toNat := by
  obtain ⟨a, b⟩ := L
  simp only at h
  subst h
  simp [wordLoc]

/-- **The silent row** (`Out.silent`). -/
theorem row_silent (h : Inv1 Λ lbl lsize ts t tm sm) (hstep : stepOne A t tid tm = some outs)
    (ho : .ok o ∈ outs) {s' : I.State} {c' : Ctl} (hex : I.exec t.st = some (.done s')) (hx : X s' c') :
    X o.thread.st c' ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  obtain ⟨-, -, hP, hi⟩ := inv1_silent h hex (silentTree_done s') hstep ho
  exact ⟨hP ▸ hx, hi⟩

/-- **The choice row** (`Out.choice`). -/
theorem row_choice (h : Inv1 Λ lbl lsize ts t tm sm) (hstep : stepOne A t tid tm = some outs)
    (ho : .ok o ∈ outs) {P : I.State → Prop} {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    (hs : SilentTree P tree) (hx : ∀ s', P s' → ∃ c', LocalRun p c c' ∧ X s' c') :
    ∃ c', LocalRun p c c' ∧ X o.thread.st c' ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  obtain ⟨-, -, hP, hi⟩ := inv1_silent h hex hs hstep ho
  obtain ⟨c', hr, hx'⟩ := hx _ hP
  exact ⟨c', hr, hx', hi⟩

/-- **The runtime-load row** (`Out.rtLoad`). -/
theorem row_rtLoad (h : Inv1 Λ lbl lsize ts t tm sm) (hstep : stepOne A t tid tm = some outs)
    (ho : .ok o ∈ outs) {kl : Kraken.LoadKind} {L : Loc} {g : Val → I.State} {c' : Ctl}
    (hex : I.exec t.st = some (.load kl false L fun v => .done (g v))) (hx : ∀ v, X (g v) c') :
    X o.thread.st c' ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  obtain ⟨-, -, ⟨v, hv⟩, hi⟩ := inv1_rtLoad h hex hstep ho
  exact ⟨hv ▸ hx v, hi⟩

/-- **The runtime-store row** (`Out.rtStore`): a one-word store outside
every placed label (`MemSide.ofLabels`). -/
theorem row_rtStore (h : Inv1 Λ lbl lsize ts t tm sm) (hstep : stepOne A t tid tm = some outs)
    (ho : .ok o ∈ outs) {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : I.State}
    (hex : I.exec t.st = some (.store kr false L V fun _ => .done s')) (hL : L.bytes = 8)
    {rd : TermRun.Word → Prop} {mK : Option (Kernel.Abi I)} {mG : Loc → Val → Prop}
    (hrt : (MemSide.ofLabels rd lbl lsize mK mG mh mc mu mo mcl mown mmp mab mpl mxa).rt L.addr.toNat) :
    o.thread.st = s' ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm :=
  h.rtStore A hex hL hrt hstep ho

/-- **The load row** (`Out.load`), target side, with the source load of
the latest message at the untagged locative `w` names: memory and promises
stay, `Inv1` holds, and the value read represents the latest source
message's (`Inv1.load_src`, with `wordAddr_of_valRep_loc0`). -/
theorem row_load (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) (hstep : stepOne A t tid tm = some outs)
    (ho : .ok o ∈ outs) {kl : Kraken.LoadKind} {A' : BitVec 64} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl false ⟨A', 8⟩ fun v => .done (g v))) {w : TermRun.Word}
    (hv : ValRep lbl w.val A'.toNat) {sa : WeakMem.Address} (hw : w.val = .loc sa 0) {j : Nat}
    (hj : MemRel.SLatest sm sa j) (arch : WeakMem.Arch) (pairs : List Nat) (th : Promises.Thread)
    (dst : WeakMem.Reg) (deps : List WeakMem.Reg) (acq : Bool) :
    o.mem = tm ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm ∧
      ∃ v, o.thread.st = g v ∧ ∃ m th', sm[j]? = some m ∧ th' ∈ Promises.stepLoad arch sm pairs th dst sa deps acq ∧
        th'.regs dst = ⟨m.val, m.view, j⟩ ∧ ValRep lbl m.val v.toNat := by
  rw [hw] at hv
  rw [← wordLoc_toNat] at hex
  exact h.load_src hwf A hex hstep ho (wordAddr_of_valRep_loc0 hv) hj arch pairs th dst deps acq

/-- **The store row** (`Out.store`), target side, with any outcome of a
promise-free source store to the untagged locative `w` names of a value
`V` represents: `Inv1` holds after both (`Inv1.store_src`, with
`wordAddr_of_valRep_loc0`). The offset bound `hoff` is the source's. -/
theorem row_store (h : Inv1 Λ lbl lsize ts t tm sm) (hstep : stepOne A t tid tm = some outs)
    (ho : .ok o ∈ outs) {kr : Kraken.StoreKind} {A' : BitVec 64} {V : Val} {s' : I.State}
    (hex : I.exec t.st = some (.store kr false ⟨A', 8⟩ V fun _ => .done s')) {w : TermRun.Word}
    (hv : ValRep lbl w.val A'.toNat) {sa : WeakMem.Address} (hw : w.val = .loc sa 0)
    {k : Promises.Knobs} {arch : WeakMem.Arch} {th : Promises.Thread} {e : WeakMem.Expr}
    {deps : List WeakMem.Reg} {rel : Bool} (hp : th.promises = []) (hoff : sa.offset < lsize sa.label)
    (hV : ValRep lbl (Promises.rmwNewVal th.regs e) V.toNat)
    {x : WeakMem.Memory × Promises.Thread} (hx : x ∈ Promises.stepStore k arch sm th sa e deps rel) :
    o.thread.st = s' ∧ x.2.promises = [] ∧
      ∃ q, Inv1 Λ lbl lsize (fun k => if k = sm.size then some q else ts k) o.thread o.mem x.1 := by
  rw [hw] at hv
  rw [← wordLoc_toNat] at hex
  exact h.store_src A hex hstep ho hp (wordAddr_of_valRep_loc0 hv) hoff hV hx

/-- **`out_local` under outstanding promises**: the runtime memory's value
invariant for the messages not promised (`hGm`, `MsgsExcept`) and the
initial values (`hGi`) only, as on a certification run (a runtime load reads
a message not promised: `stepOne_load_msgsExcept`,
`msgsExcept_read_tlatestP`). -/
theorem out_localP {K : Kernel.Abi I} {rd : TermRun.Word → Prop} (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) (hns : K.atSys t.st = false)
    (hw8 : ∀ tree, I.exec t.st = some tree → Wide8Tree tree)
    (hGm : MsgsExcept (fun m => G m.loc m.val) t.prom tm) (hGi : ∀ l, G l (tm.initVal l))
    (hown : OwnOk (mown t.st) tm t.prom)
    (hout : Out p lbl (MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl mown mmp mab mpl mxa) X t.st c) :
    (∃ c', LocalRun p c c' ∧ X o.thread.st c' ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm) ∨
      (∃ (kl : Kraken.LoadKind) (A : BitVec 64) (g : Val → I.State) (x : String) (a : At) (e : Expr) (ty : Ty)
          (w : TermRun.Word) (sa : WeakMem.Address),
        I.exec t.st = some (.load kl false ⟨A, 8⟩ fun v => .done (g v)) ∧ c.term = .let_ x (.load true a) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ w.val = .loc sa 0 ∧
        ∀ (v : Val) (w' : TermRun.Word), rd w' → ValRep lbl w'.val (v.setWidth 64).toNat →
          X (g v) ⟨e, (x, loadTy ty, [w']) :: c.env, none⟩) ∨
      (∃ (kr : Kraken.StoreKind) (A : BitVec 64) (V : Val) (s' : I.State) (x : String) (a b : At) (e : Expr)
          (ty tb : Ty) (w wb : TermRun.Word) (sa : WeakMem.Address),
        I.exec t.st = some (.store kr false ⟨A, 8⟩ V fun _ => .done s') ∧ c.term = .let_ x (.store true a b none) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ w.val = .loc sa 0 ∧
        TermRun.evalAt c.env b = some (tb, [wb]) ∧ ValRep lbl wb.val V.toNat ∧
        X s' ⟨e, (x, .unit, []) :: c.env, none⟩) ∨
      (∃ (kl : Kraken.LoadKind) (A : BitVec 64) (g : Val → I.State) (x : String) (sa : WeakMem.Address) (u : Ty)
          (v : At) (e : Expr),
        I.exec t.st = some (.load kl false ⟨A, 8⟩ fun r => .done (g r)) ∧ XchgSite c x sa u v e ∧
        ValRep lbl (.loc sa 0) A.toNat ∧ c.hold = none ∧
        ∀ (r : Val) (w' : TermRun.Word), rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
          X (g r) { c with hold := some (A.toNat, w') }) ∨
      (∃ (kr : Kraken.StoreKind) (A : BitVec 64) (V : Val) (s' : I.State) (x : String) (sa : WeakMem.Address)
          (u : Ty) (v : At) (e : Expr) (tv : Ty) (wv wold : TermRun.Word),
        I.exec t.st = some (.store kr false ⟨A, 8⟩ V fun _ => .done s') ∧ XchgSite c x sa u v e ∧
        ValRep lbl (.loc sa 0) A.toNat ∧ c.hold = some (A.toNat, wold) ∧
        TermRun.evalAt c.env v = some (tv, [wv]) ∧ ValRep lbl wv.val V.toNat ∧
        X s' ⟨e, (x, u, [wold]) :: c.env, none⟩) ∨
      (∃ (x : String) (a : At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word) (n : Nat) (old : Val),
        c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some n ∧
        c.hold = none ∧ (∃ tr, TLatestP tm t.prom mc tr ∧ tm.read? (wordLoc mc) tr = some old) ∧
        (∀ w, (wordLoc mc, w) ∈ mown t.st → old = w) ∧
        ((old.setWidth 64).toNat ≤ mcl →
          X o.thread.st { c with hold := some (mc, TermRun.cst (.num (old.setWidth 64).toNat)) }) ∧
        Inv1 Λ lbl lsize ts o.thread o.mem sm) ∨
      (∃ (s' : I.State) (A : BitVec 64) (x : String) (a : At) (τ : Ty) (e : Expr) (ta : Ty)
          (ws : List TermRun.Word) (k : Nat) (wold : TermRun.Word) (old : Nat) (us : List TermRun.Acc),
        o.thread.st = s' ∧ c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧
        TermRun.numOf ws = some k ∧ c.hold = some (mc, wold) ∧ TermRun.numOf [wold] = some old ∧
        A.toNat = mh + 16 * old + mo k τ ∧ old + mu k τ ≤ mcl ∧ TermRun.accs (TermRun.close [] τ) = some us ∧
        (∀ (l : WeakMem.AllocLabel) (ini : Nat), lbl l = none →
          mxa l A.toNat (k * TermRun.nWords us) s'
            ⟨e, (x, .refine (.loc .own (.array (.lit k) (TermRun.close [] τ))) (.ini (.lit ini)),
              [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩) ∧
        o.mem = tm ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm) := by
  cases hout with
  | silent s' c' he hr hx =>
    obtain ⟨hx', hi⟩ := row_silent h hstep ho he hx
    exact .inl ⟨c', hr, hx', hi⟩
  | choice P tree he hs hx => exact .inl (row_choice h hstep ho he hs hx)
  | load kl A' g x a e ty w he ht hev hv hX htag =>
    obtain ⟨sa, hsa⟩ := htag
    exact .inr (.inl ⟨kl, A', g, x, a, e, ty, w, sa, he, ht, hev, hv, hsa, hX⟩)
  | store kr A' V s' x a b e ty tb w wb he ht hev hv hevb hvb hX htag =>
    obtain ⟨sa, hsa⟩ := htag
    exact .inr (.inr (.inl ⟨kr, A', V, s', x, a, b, e, ty, tb, w, wb, sa, he, ht, hev, hv, hsa, hevb, hvb, hX⟩))
  | rtStore kr L V s' c' he hrt _ _ hr hx =>
    have hL : L.bytes = 8 := (hw8 _ he).1
    obtain ⟨hst, hi⟩ := row_rtStore h hstep ho he hL hrt
    exact .inl ⟨c', hr, hst ▸ hx, hi⟩
  | rtLoad kl L g c' he _ _ hr hx =>
    obtain ⟨-, -, -, hi⟩ := inv1_rtLoad h he hstep ho
    by_cases hL : L.bytes = 8
    · obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, loc_wordLoc hL⟩
      obtain ⟨-, tr, v, hv, hl, hrd⟩ := stepOne_load_tlatestP A he hstep ho h.coh
      exact .inl ⟨c', hr, hv ▸ hx v (msgsExcept_read_tlatestP hGm hGi hl hrd) (hown.read hl hrd), hi⟩
    · have hno : ∀ w, (L, w) ∉ mown t.st := fun w hw => hL (hown _ _ hw).1
      obtain ⟨v, hv, hGv⟩ := stepOne_load_msgsExcept he hstep ho hGm hGi
      exact .inl ⟨c', hr, hv ▸ hx v hGv fun w hw => absurd hw (hno w), hi⟩
  | rtRmw k L op g c' he hrt _ hr hx =>
    obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, loc_wordLoc (hw8 _ he).1⟩
    obtain ⟨old, tr, hst, hl, hrd, -⟩ :=
      stepOne_rmw_cases A he hstep ho h.coh fun q hq => (h.mem.tq_le q hq).2
    obtain ⟨-, -, -, -, hi⟩ := RtRmw.inv1_rtRmw A h he hrt hstep ho
    exact .inl ⟨c', hr, hst ▸ (hx old (msgsExcept_read_tlatestP hGm hGi hl hrd) (hown.read hl hrd)).2, hi⟩
  | sys K' _ hK hs =>
    cases hK
    rw [hns] at hs
    cases hs
  | emit K' _ _ _ _ hK hae =>
    cases hK
    rw [hns] at hae
    cases hae
  | holdLoad kl A' g x sa u v e he hx hA hh hX =>
    exact .inr (.inr (.inr (.inl ⟨kl, A', g, x, sa, u, v, e, he, hx, hA, hh, hX⟩)))
  | xchgStore kr A' V s' x sa u v e tv wv wold he hx hA hh hev hv hX =>
    exact .inr (.inr (.inr (.inr (.inl ⟨kr, A', V, s', x, sa, u, v, e, tv, wv, wold, he, hx, hA, hh, hev, hv, hX⟩))))
  | ctrRmw k op g x a τ e ta ws n he hrt _ ht hev hn hh hop hX =>
    obtain ⟨old, tr, hst, hlat, hr, -⟩ :=
      stepOne_rmw_cases A (a := mc) he hstep ho h.coh fun q hq => (h.mem.tq_le q hq).2
    obtain ⟨-, -, -, -, hi⟩ := RtRmw.inv1_rtRmw A h (a := mc) he hrt hstep ho
    have hoo := hown.read hlat hr
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨x, a, τ, e, ta, ws, n, old, ht, hev, hn, hh, ⟨tr, hlat, hr⟩, hoo,
      fun hc => hst ▸ (hX old (msgsExcept_read_tlatestP hGm hGi hlat hr) hoo hc).2, hi⟩)))))
  | alloc s' A' x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX =>
    obtain ⟨hm, -, hP, hi⟩ := inv1_silent h he (silentTree_done s') hstep ho
    exact .inr (.inr (.inr (.inr (.inr (.inr ⟨s', A', x, a, τ, e, ta, ws, k, wold, old, us, hP, ht, hev, hk, hh,
      hold, hA, hc, hu, hX, hm, hi⟩)))))

/-- **An `Out` row off a system call**, under `MemSide.ofLabels` with the
machine's kernel model, for code whose trees from `t.st` write words only
(`hw8`), the memory satisfying the runtime memory's value invariant (`hG`,
so a runtime load reads a `G` value): the source matches by a
local run, the thread lands in the fragment and `Inv1` holds; or the row is
a one-word load or store (`Out.load`, `Out.store`), its data returned with
the address word an untagged locative (`row_load`, `row_store` then apply);
or the row is the load or the store of an exchange (`Out.holdLoad`,
`Out.xchgStore`), its data returned; or the row is the heap counter's add
at a buffer allocation (`Out.ctrRmw`: the source stutters into the hold of
the old count, a value read at the counter, when within the arena's cells,
`Inv1` kept) or the allocation's
last instruction (`Out.alloc`, memory unchanged, `Inv1` kept), their data
returned. -/
theorem out_local {K : Kernel.Abi I} {rd : TermRun.Word → Prop} (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) (hns : K.atSys t.st = false)
    (hw8 : ∀ tree, I.exec t.st = some tree → Wide8Tree tree)
    (hG : MemInv G tm) (hown : OwnOk (mown t.st) tm t.prom)
    (hout : Out p lbl (MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl mown mmp mab mpl mxa) X t.st c) :
    (∃ c', LocalRun p c c' ∧ X o.thread.st c' ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm) ∨
      (∃ (kl : Kraken.LoadKind) (A : BitVec 64) (g : Val → I.State) (x : String) (a : At) (e : Expr) (ty : Ty)
          (w : TermRun.Word) (sa : WeakMem.Address),
        I.exec t.st = some (.load kl false ⟨A, 8⟩ fun v => .done (g v)) ∧ c.term = .let_ x (.load true a) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ w.val = .loc sa 0 ∧
        ∀ (v : Val) (w' : TermRun.Word), rd w' → ValRep lbl w'.val (v.setWidth 64).toNat →
          X (g v) ⟨e, (x, loadTy ty, [w']) :: c.env, none⟩) ∨
      (∃ (kr : Kraken.StoreKind) (A : BitVec 64) (V : Val) (s' : I.State) (x : String) (a b : At) (e : Expr)
          (ty tb : Ty) (w wb : TermRun.Word) (sa : WeakMem.Address),
        I.exec t.st = some (.store kr false ⟨A, 8⟩ V fun _ => .done s') ∧ c.term = .let_ x (.store true a b none) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ w.val = .loc sa 0 ∧
        TermRun.evalAt c.env b = some (tb, [wb]) ∧ ValRep lbl wb.val V.toNat ∧
        X s' ⟨e, (x, .unit, []) :: c.env, none⟩) ∨
      (∃ (kl : Kraken.LoadKind) (A : BitVec 64) (g : Val → I.State) (x : String) (sa : WeakMem.Address) (u : Ty)
          (v : At) (e : Expr),
        I.exec t.st = some (.load kl false ⟨A, 8⟩ fun r => .done (g r)) ∧ XchgSite c x sa u v e ∧
        ValRep lbl (.loc sa 0) A.toNat ∧ c.hold = none ∧
        ∀ (r : Val) (w' : TermRun.Word), rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
          X (g r) { c with hold := some (A.toNat, w') }) ∨
      (∃ (kr : Kraken.StoreKind) (A : BitVec 64) (V : Val) (s' : I.State) (x : String) (sa : WeakMem.Address)
          (u : Ty) (v : At) (e : Expr) (tv : Ty) (wv wold : TermRun.Word),
        I.exec t.st = some (.store kr false ⟨A, 8⟩ V fun _ => .done s') ∧ XchgSite c x sa u v e ∧
        ValRep lbl (.loc sa 0) A.toNat ∧ c.hold = some (A.toNat, wold) ∧
        TermRun.evalAt c.env v = some (tv, [wv]) ∧ ValRep lbl wv.val V.toNat ∧
        X s' ⟨e, (x, u, [wold]) :: c.env, none⟩) ∨
      (∃ (x : String) (a : At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word) (n : Nat) (old : Val),
        c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some n ∧
        c.hold = none ∧ (∃ tr, TLatestP tm t.prom mc tr ∧ tm.read? (wordLoc mc) tr = some old) ∧
        (∀ w, (wordLoc mc, w) ∈ mown t.st → old = w) ∧
        ((old.setWidth 64).toNat ≤ mcl →
          X o.thread.st { c with hold := some (mc, TermRun.cst (.num (old.setWidth 64).toNat)) }) ∧
        Inv1 Λ lbl lsize ts o.thread o.mem sm) ∨
      (∃ (s' : I.State) (A : BitVec 64) (x : String) (a : At) (τ : Ty) (e : Expr) (ta : Ty)
          (ws : List TermRun.Word) (k : Nat) (wold : TermRun.Word) (old : Nat) (us : List TermRun.Acc),
        o.thread.st = s' ∧ c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧
        TermRun.numOf ws = some k ∧ c.hold = some (mc, wold) ∧ TermRun.numOf [wold] = some old ∧
        A.toNat = mh + 16 * old + mo k τ ∧ old + mu k τ ≤ mcl ∧ TermRun.accs (TermRun.close [] τ) = some us ∧
        (∀ (l : WeakMem.AllocLabel) (ini : Nat), lbl l = none →
          mxa l A.toNat (k * TermRun.nWords us) s'
            ⟨e, (x, .refine (.loc .own (.array (.lit k) (TermRun.close [] τ))) (.ini (.lit ini)),
              [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩) ∧
        o.mem = tm ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm) :=
  out_localP h hstep ho hns hw8 (MemInv.msgsExcept hG t.prom) hG.1 hown hout

/-! ## Progress off a system call -/

/-- **The last index below `N` satisfying `Q`**, if one does. -/
theorem exists_last (Q : Nat → Prop) : ∀ N, (∀ k, Q k → k < N) → (∃ k, Q k) → ∃ j, Q j ∧ ∀ k, j < k → ¬ Q k
  | 0, hb, ⟨k, hk⟩ => absurd (hb k hk) (Nat.not_lt_zero _)
  | N + 1, hb, h => by
    by_cases hN : Q N
    · exact ⟨N, hN, fun k hk hq => by have := hb k hq; omega⟩
    · refine exists_last Q N (fun k hk => ?_) h
      have := hb k hk
      have : k ≠ N := fun e => hN (e ▸ hk)
      omega

/-- **Some timestamp of a location is readable from any view**: the last
write to it, else the initial write; no later write to it. -/
theorem exists_read (mem : Memory) (l : Loc) :
    ∃ ts v, ts ≤ mem.last ∧ mem.read? l ts = some v ∧ ∀ hi, mem.writeIn l ts hi = false := by
  let Q : Nat → Prop := fun k => 0 < k ∧ ∃ w : Msg, mem.get? k = some w ∧ w.loc = l
  have hnQ : ∀ ts, (∀ k, ts < k → ¬ Q k) → ∀ hi, mem.writeIn l ts hi = false := by
    intro ts hq hi
    unfold Memory.writeIn
    rw [List.any_eq_false]
    intro i _
    split
    · rename_i w hw
      simp only [beq_iff_eq]
      intro hl
      exact hq (ts + i + 1) (by omega) ⟨by omega, w, hw, hl⟩
    · simp
  by_cases hex : ∃ k, Q k
  · obtain ⟨j, ⟨hj0, w, hw, hl⟩, hlast⟩ := exists_last Q (mem.last + 1)
      (fun k ⟨_, w, hw, _⟩ => Nat.lt_succ_of_le (mem.last_le_of_get?_eq_some hw)) hex
    refine ⟨j, w.val, mem.last_le_of_get?_eq_some hw, ?_, hnQ j hlast⟩
    unfold Memory.read?
    simp [Nat.pos_iff_ne_zero.mp hj0, hw, hl]
  · exact ⟨0, mem.initVal l, Nat.zero_le _, by simp [Memory.read?], hnQ 0 fun k _ hk => hex ⟨k, hk⟩⟩


/-- **A thread with no promise at a load has an outcome** with no promise:
it reads `exists_read`'s timestamp. -/
theorem load_ok {t : Thread I} {tid : Nat} {mem : Memory} (hp : t.prom = []) {kl : Kraken.LoadKind} {L : Loc}
    {g : Val → I.State} (hex : I.exec t.st = some (.load kl false L fun v => .done (g v))) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  obtain ⟨ts, v, hle, hr, hw⟩ := exists_read mem L
  have hx := (mem_readSuccs A (iv := instrViews t (I.deps t.st)) (c := ctx0 tid t mem) (k := kl) (xcl := false)
    (l := L) (noRet := false)).mpr ⟨ts, v, rfl, hle, hr, hw _, by simp [hp]⟩
  obtain ⟨th, hth⟩ := Spike.Bridge.finishInstr_nonempty t (I.deps t.st) (instrViews t (I.deps t.st)) (g v)
    (readNext A (instrViews t (I.deps t.st)) (ctx0 tid t mem) kl false L false ts v)
  obtain ⟨outs, o, hs, ho, rfl, -⟩ := (stepOne_ok_iff A tid hex).mpr
    ⟨g v, _, (run_load_iff A tid _).mpr ⟨ts, v, hx, rfl⟩, hth, rfl⟩
  exact ⟨outs, o, hs, ho, (finishInstr_relKey hth).1.trans ((readSuccs_prom A _ hx).trans hp)⟩

/-- **A thread with no promise, its values at most `|M|`, at a store has an
outcome** with no promise: the write at the fresh timestamp `|M| + 1`,
above every view. -/
theorem store_ok {t : Thread I} {tid : Nat} {mem : Memory} (hp : t.prom = []) (hb : t.Bnd mem.last)
    {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false L V fun _ => .done s)) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  have hc : Ctx.Bnd (ctx0 tid t mem) := ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  have hiv : ((instrViews t (I.deps t.st)).forStore (ctx0 tid t mem).stores).Le mem.last :=
    (instrViews_le hb.regs _).forStore _
  have hle := writePre_le A hc hiv kr (l := L) (extra := 0) (Nat.zero_le _)
  have hw := (mem_writeSuccs_iff A tid ((instrViews t (I.deps t.st)).forStore (ctx0 tid t mem).stores)
    (c := ctx0 tid t mem) (k := kr) (xcl := false) (l := L) (v := V) (tr := none) (extra := 0) (xr := 0)).mpr
    (.inr ⟨by
      unfold writeOk
      simp only [Bool.and_true, decide_eq_true_eq]
      exact Nat.lt_succ_of_le hle, rfl⟩)
  obtain ⟨th, hth⟩ := Spike.Bridge.finishInstr_nonempty t (I.deps t.st) (instrViews t (I.deps t.st)) s _
  obtain ⟨outs, o, hs, ho, rfl, -⟩ := (stepOne_ok_iff A tid hex).mpr
    ⟨s, _, (run_store_iff A tid _).mpr ⟨rfl, hw⟩, hth, rfl⟩
  refine ⟨outs, o, hs, ho, (finishInstr_relKey hth).1.trans ?_⟩
  simp [afterWrite, promiseNowCtx, hp]


/-- **An `Out` row off a system call has an outcome** for a thread with no
promise and its values at most `|M|`, with no promise after it. -/
theorem out_progress {K : Kernel.Abi I} {rd : TermRun.Word → Prop} {t : Thread I} {tid : Nat} {mem : Memory}
    (hp : t.prom = []) (hb : t.Bnd mem.last) (hns : K.atSys t.st = false)
    (hout : Out p lbl (MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl mown mmp mab mpl mxa) X t.st c) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  have hsil : ∀ {P : I.State → Prop} {tree : EvTree I.State}, I.exec t.st = some tree → SilentTree P tree →
      ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
    intro P tree he hs
    obtain ⟨s, -, hall⟩ := stepOne_silent_exists A tid (mem := mem) he hs
    obtain ⟨th, hth⟩ := Spike.Bridge.finishInstr_nonempty t (I.deps t.st) (instrViews t (I.deps t.st)) s
      (ctx0 tid t mem)
    obtain ⟨outs, o, hs, ho, rfl, -⟩ := hall th hth
    exact ⟨outs, o, hs, ho, (finishInstr_relKey hth).1.trans hp⟩
  cases hout with
  | silent s' c' he => exact hsil he (silentTree_done s')
  | choice P tree he hs => exact hsil he hs
  | load kl A' g x a e ty w he => exact load_ok hp he
  | store kr A' V s' x a b e ty tb w wb he => exact store_ok hp hb he
  | rtStore kr L V s' c' he => exact store_ok hp hb he
  | rtLoad kl L g c' he => exact load_ok hp he
  | rtRmw k L op g c' he => exact RtRmw.rmw_ok A hp hb he
  | sys K' _ hK hs =>
    cases hK
    rw [hns] at hs
    cases hs
  | emit K' _ _ _ _ hK hae =>
    cases hK
    rw [hns] at hae
    cases hae
  | holdLoad kl A' g x sa u v e he => exact load_ok hp he
  | xchgStore kr A' V s' x sa u v e tv wv wold he => exact store_ok hp hb he
  | ctrRmw k op g x a τ e ta ws n he => exact RtRmw.rmw_ok A hp hb he
  | alloc s' A' x a τ e ta ws k _ _ _ he => exact hsil he (silentTree_done s')

/-- **An `Out` row off a system call has no error outcome.** -/
theorem out_no_error {K : Kernel.Abi I} {rd : TermRun.Word → Prop} {t : Thread I} {tid : Nat} {mem : Memory}
    (hns : K.atSys t.st = false)
    (hout : Out p lbl (MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl mown mmp mab mpl mxa) X t.st c)
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hs : stepOne A t tid mem = some outs) (m : String) :
    (.error m : Except String (Kraken.Promising.Outcome I)) ∉ outs := by
  cases hout with
  | silent s' c' he => exact stepOne_silent_no_error A tid he (silentTree_done s') hs m
  | choice P tree he hsl => exact stepOne_silent_no_error A tid he hsl hs m
  | load kl A' g x a e ty w he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_load_ok A _ _ _ _ _ _) hs m
  | store kr A' V s' x a b e ty tb w wb he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_store_ok A _ _ _ _ _ _ _) hs m
  | rtStore kr L V s' c' he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_store_ok A _ _ _ _ _ _ _) hs m
  | rtLoad kl L g c' he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_load_ok A _ _ _ _ _ _) hs m
  | rtRmw k L op g c' he =>
    exact Spike.Bridge.stepOne_no_error A he (RtRmw.runTree_rmw_ok A _ _ _ _ _ _ _) hs m
  | sys K' _ hK hsy =>
    cases hK
    rw [hns] at hsy
    cases hsy
  | emit K' _ _ _ _ hK hae =>
    cases hK
    rw [hns] at hae
    cases hae
  | holdLoad kl A' g x sa u v e he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_load_ok A _ _ _ _ _ _) hs m
  | xchgStore kr A' V s' x sa u v e tv wv wold he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_store_ok A _ _ _ _ _ _ _) hs m
  | ctrRmw k op g x a τ e ta ws n he =>
    exact Spike.Bridge.stepOne_no_error A he (RtRmw.runTree_rmw_ok A _ _ _ _ _ _ _) hs m
  | alloc s' A' x a τ e ta ws k _ _ _ he => exact stepOne_silent_no_error A tid he (silentTree_done s') hs m

/-- **An `Out` row off a system call has an instruction.** -/
theorem out_exec {K : Kernel.Abi I} {rd : TermRun.Word → Prop} {s : I.State} (hns : K.atSys s = false)
    (h : Out p lbl (MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl mown mmp mab mpl mxa) X s c) :
    (I.exec s).isSome := by
  cases h with
  | silent s' c' he => rw [he]; rfl
  | choice P t he hs => rw [he]; rfl
  | load _ _ _ _ _ _ _ _ he => rw [he]; rfl
  | store _ _ _ _ _ _ _ _ _ _ _ _ he => rw [he]; rfl
  | rtStore _ _ _ _ _ he => rw [he]; rfl
  | rtLoad _ _ _ _ he => rw [he]; rfl
  | rtRmw _ _ _ _ _ he => rw [he]; rfl
  | sys K' _ hK hs => cases hK; rw [hns] at hs; cases hs
  | emit K' _ _ _ _ hK hae => cases hK; rw [hns] at hae; cases hae
  | holdLoad _ _ _ _ _ _ _ _ he => rw [he]; rfl
  | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he => rw [he]; rfl
  | ctrRmw _ _ _ _ _ _ _ _ _ _ he => rw [he]; rfl
  | alloc _ _ _ _ _ _ _ _ _ _ _ _ he => rw [he]; rfl


/-- **The memory and promises after an `Out` row's outcome** off a system
call, under outstanding promises (`out_localP`'s `hGm`, `hGi`): unchanged,
or one one-word message of the thread written, appended (promises
unchanged) or fulfilling an outstanding promise of it (memory unchanged),
of `out_mem`'s kinds. -/
theorem out_memP {K : Kernel.Abi I} {rd : TermRun.Word → Prop}
    (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) (hns : K.atSys t.st = false)
    (hw8 : ∀ tree, I.exec t.st = some tree → Wide8Tree tree)
    (hGm : MsgsExcept (fun m => G m.loc m.val) t.prom tm) (hGi : ∀ l, G l (tm.initVal l))
    (hown : OwnOk (mown t.st) tm t.prom)
    (hout : Out p lbl (MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl mown mmp mab mpl mxa) X t.st c) :
    (o.mem = tm ∧ o.thread.prom = t.prom) ∨ ∃ (L : Loc) (V : Val), L.bytes = 8 ∧
      ((o.mem = (tm.append ⟨L, V, tid⟩).1 ∧ o.thread.prom = t.prom) ∨
        ∃ q ∈ t.prom, tm.get? q = some ⟨L, V, tid⟩ ∧ o.mem = tm ∧ o.thread.prom = t.prom.erase q) ∧
      ((¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat) ∧ mmp L true ∧ G L V ∨
        (∃ (x : String) (a b : At) (e : Expr) (ty : Ty) (w : TermRun.Word) (sa : WeakMem.Address),
          c.term = .let_ x (.store true a b none) e ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
          ValRep lbl w.val L.addr.toNat ∧ w.val = .loc sa 0) ∨
        (∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : At) (e : Expr),
          XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) L.addr.toNat) ∨
        (¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat) ∧ mmp L true ∧
          (∃ (x : String) (a : At) (τ : Ty) (e : Expr), c.term = .let_ x (.newBuf a τ) e) ∧
          ((∀ v tr, tm.read? (wordLoc mc) tr = some v → (v.setWidth 64).toNat ≤ mcl) → G L V)) := by
  have hpl : ∀ q ∈ t.prom, q ≤ tm.last := fun q hq => (h.mem.tq_le q hq).2
  cases hout with
  | silent s' c' he =>
    obtain ⟨hm, hp, -⟩ := inv1_silent h he (silentTree_done s') hstep ho; exact .inl ⟨hm, hp⟩
  | choice P tree he hs => obtain ⟨hm, hp, -⟩ := inv1_silent h he hs hstep ho; exact .inl ⟨hm, hp⟩
  | load kl A' g x a e ty w he => obtain ⟨hm, hp, -⟩ := inv1_rtLoad h he hstep ho; exact .inl ⟨hm, hp⟩
  | rtLoad kl L g c' he => obtain ⟨hm, hp, -⟩ := inv1_rtLoad h he hstep ho; exact .inl ⟨hm, hp⟩
  | store kr A' V s' x a b e ty tb w wb he ht hev hv hevb hvb hX htag =>
    obtain ⟨sa, hsa⟩ := htag
    rw [← wordLoc_toNat] at he
    rcases (stepOne_store_cases A he hstep ho hpl).2 with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
    · rw [wordLoc_toNat] at hg
      exact .inr ⟨_, V, rfl, .inr ⟨q, hq, hg, hm, hp⟩, .inr (.inl ⟨x, a, b, e, ty, w, sa, ht, hev, hv, hsa⟩)⟩
    · rw [wordLoc_toNat] at hm
      exact .inr ⟨_, V, rfl, .inl ⟨hm, hp⟩, .inr (.inl ⟨x, a, b, e, ty, w, sa, ht, hev, hv, hsa⟩)⟩
  | rtStore kr L V s' c' he hrt hmp hGV =>
    have hL : L.bytes = 8 := (hw8 _ he).1
    have hLw : L = wordLoc L.addr.toNat := loc_wordLoc hL
    have he' := he
    rw [hLw] at he'
    rcases (stepOne_store_cases A he' hstep ho hpl).2 with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
    · rw [← hLw] at hg
      exact .inr ⟨L, V, hL, .inr ⟨q, hq, hg, hm, hp⟩, .inl ⟨hrt, hmp, hGV⟩⟩
    · rw [← hLw] at hm
      exact .inr ⟨L, V, hL, .inl ⟨hm, hp⟩, .inl ⟨hrt, hmp, hGV⟩⟩
  | rtRmw k L op g c' he hrt hmp hr hX =>
    obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, loc_wordLoc (hw8 _ he).1⟩
    obtain ⟨old, tr, -, hl, hrd, ⟨-, hm, hp⟩ | ⟨new, hnew, ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩⟩⟩ :=
      stepOne_rmw_cases A he hstep ho h.coh hpl
    · exact .inl ⟨hm, hp⟩
    · exact .inr ⟨_, new, rfl, .inr ⟨q, hq, hg, hm, hp⟩,
        .inl ⟨hrt, hmp, (hX old (msgsExcept_read_tlatestP hGm hGi hl hrd) (hown.read hl hrd)).1 new hnew⟩⟩
    · exact .inr ⟨_, new, rfl, .inl ⟨hm, hp⟩,
        .inl ⟨hrt, hmp, (hX old (msgsExcept_read_tlatestP hGm hGi hl hrd) (hown.read hl hrd)).1 new hnew⟩⟩
  | sys K' _ hK hs =>
    cases hK
    rw [hns] at hs
    cases hs
  | emit K' _ _ _ _ hK hae =>
    cases hK
    rw [hns] at hae
    cases hae
  | holdLoad kl A' g x sa u v e he => obtain ⟨hm, hp, -⟩ := inv1_rtLoad h he hstep ho; exact .inl ⟨hm, hp⟩
  | alloc s' A' x a τ e ta ws k _ _ _ he =>
    obtain ⟨hm, hp, -⟩ := inv1_silent h he (silentTree_done s') hstep ho; exact .inl ⟨hm, hp⟩
  | ctrRmw k op g x a τ e ta ws n he hrt hmp ht hev hn hh hop hX =>
    obtain ⟨old, tr, -, hl, hr, ⟨-, hm, hp⟩ | ⟨new, hnew, hw⟩⟩ :=
      stepOne_rmw_cases A (a := mc) he hstep ho h.coh hpl
    · exact .inl ⟨hm, hp⟩
    · have hk : (∀ v tr, tm.read? (wordLoc mc) tr = some v → (v.setWidth 64).toNat ≤ mcl) → G (wordLoc mc) new :=
        fun hc => by
          rw [hop old] at hnew
          cases hnew
          exact (hX old (msgsExcept_read_tlatestP hGm hGi hl hr) (hown.read hl hr) (hc old tr hr)).1
      rcases hw with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
      · exact .inr ⟨_, new, rfl, .inr ⟨q, hq, hg, hm, hp⟩, .inr (.inr (.inr ⟨hrt, hmp, ⟨x, a, τ, e, ht⟩, hk⟩))⟩
      · exact .inr ⟨_, new, rfl, .inl ⟨hm, hp⟩, .inr (.inr (.inr ⟨hrt, hmp, ⟨x, a, τ, e, ht⟩, hk⟩))⟩
  | xchgStore kr A' V s' x sa u v e tv wv wold he hx hA =>
    rw [← wordLoc_toNat] at he
    rcases (stepOne_store_cases A he hstep ho hpl).2 with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
    · rw [wordLoc_toNat] at hg
      exact .inr ⟨_, V, rfl, .inr ⟨q, hq, hg, hm, hp⟩, .inr (.inr (.inl ⟨x, sa, u, v, e, hx, hA⟩))⟩
    · rw [wordLoc_toNat] at hm
      exact .inr ⟨_, V, rfl, .inl ⟨hm, hp⟩, .inr (.inr (.inl ⟨x, sa, u, v, e, hx, hA⟩))⟩

/-- **The memory after an `Out` row's outcome** off a system call:
unchanged, or one message of the thread appended, by the runtime-store or
runtime-RMW row (outside every placed label, mapped for writing, a `G`
value: memory before holds `G` values, `hG`, and the words the thread owns
read as their values, `hown`), by the store row (at the word the row's
untagged locative names), by the store of an exchange (at the word of the
exchange's address) or by the heap counter's add at a buffer allocation
(outside every placed label, mapped for writing, a `G` value if the
counter's values are within the arena's cells);
the message is one word. -/
theorem out_mem {K : Kernel.Abi I} {rd : TermRun.Word → Prop}
    (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) (hns : K.atSys t.st = false)
    (hw8 : ∀ tree, I.exec t.st = some tree → Wide8Tree tree) (hG : MemInv G tm) (hown : OwnOk (mown t.st) tm t.prom)
    (hout : Out p lbl (MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl mown mmp mab mpl mxa) X t.st c) :
    o.mem = tm ∨ ∃ (L : Loc) (V : Val), o.mem = (tm.append ⟨L, V, tid⟩).1 ∧ L.bytes = 8 ∧
      ((¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat) ∧ mmp L true ∧ G L V ∨
        (∃ (x : String) (a b : At) (e : Expr) (ty : Ty) (w : TermRun.Word) (sa : WeakMem.Address),
          c.term = .let_ x (.store true a b none) e ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
          ValRep lbl w.val L.addr.toNat ∧ w.val = .loc sa 0) ∨
        (∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : At) (e : Expr),
          XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) L.addr.toNat) ∨
        (¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat) ∧ mmp L true ∧
          (∃ (x : String) (a : At) (τ : Ty) (e : Expr), c.term = .let_ x (.newBuf a τ) e) ∧
          ((∀ v tr, tm.read? (wordLoc mc) tr = some v → (v.setWidth 64).toNat ≤ mcl) → G L V)) := by
  rcases out_memP h hstep ho hns hw8 (MemInv.msgsExcept hG t.prom) hG.1 hown hout with ⟨hm, -⟩ |
    ⟨L, V, hL, ⟨hm, -⟩ | ⟨-, -, -, hm, -⟩, hk⟩
  · exact .inl hm
  · exact .inr ⟨L, V, hm, hL, hk⟩
  · exact .inl hm

end Spike.Lib.ExtRows
