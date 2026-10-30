/-
**The heap counter's add as a row with its write**: `ExtRows.out_localP`
with the counter's add (`Out.ctrRmw`) also giving the outcome's write of the
counter word (`CtrW`: the new count appended, or fulfilling an outstanding
promise above a view covering the thread's unpromised messages). An
allocation-capable consumer needs it: when no outcome writes the counter
word, the row is not the counter's add (`out_localW`).

- `CtrW`: the write of `new` at the counter word, appended or fulfilling.
- `out_localW`: `out_localP`, the counter's add with its `CtrW`.
- `out_memW`: `out_memP`, the counter's add's word the counter's.
- `ctrRmw_row`: the counter's add from its premises (`Out.ctrRmw`'s,
  without an `Out`): the old count read at the latest write not promised,
  `Inv1`, the write (`CtrW`), the landing for an old count within the cells.
-/
import Spike.Lib.ExtRows

namespace Spike.Lib.CtrRows

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.Lower Scc.Sem Spike.Lib.ExtThread Spike.Lib.ExtRows

variable {I : ISA} {A : Arch} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory}
  {sm : WeakMem.Memory} {tid : Nat} {outs : List (Except String (Kraken.Promising.Outcome I))}
  {o : Kraken.Promising.Outcome I} {p : Prog} {X : Frag I} {c : Ctl} {G : Loc → Val → Prop}
  {mh mc mcl : Nat} {mu mo : Nat → Ty → Nat} {mown : I.State → List (Loc × Val)} {mmp : Loc → Bool → Prop}
  {mab : I.State → Prop} {mpl : I.State → Ctl → Prop} {mxa : WeakMem.AllocLabel → Nat → Nat → Frag I}
  {mlo : Nat → Prop}

/-- **The outcome `o` writes `new` at the counter word `mc`** (thread
`tid`): fulfilling an outstanding promise `q` of the message, above a view
covering the thread's unpromised messages (memory unchanged, `q` erased),
or appending it (promises unchanged); `stepOne_rmw_cases`' write. -/
def CtrW (t : Thread I) (tm : Memory) (o : Kraken.Promising.Outcome I) (tid mc : Nat) (new : Val) : Prop :=
  (∃ q ∈ t.prom, tm.get? q = some ⟨wordLoc mc, new, tid⟩ ∧
      (∃ vs : Views, CohCoversP vs t.prom tm ∧ vs.getCoh (wordLoc mc) < q) ∧
      o.mem = tm ∧ o.thread.prom = t.prom.erase q) ∨
    (o.mem = (tm.append ⟨wordLoc mc, new, tid⟩).1 ∧ o.thread.prom = t.prom)

/-- **The counter's add from its premises** (`Out.ctrRmw`'s, under
`MemSide.ofLabels`, without the `Out`): the old count `old` read at the
latest write of the counter word not promised, owned words agreeing, `Inv1`
kept, the outcome writing the new count (`CtrW`), and, the old count within
the cells, the landing. -/
theorem ctrRmw_row {rd : TermRun.Word → Prop} {K : Option (Kernel.Abi I)} (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs)
    (hGm : MsgsExcept (fun m => G m.loc m.val) t.prom tm) (hGi : ∀ l, G l (tm.initVal l))
    (hown : OwnOk (mown t.st) tm t.prom) {k : Kraken.RmwKind} {op : Val → Option Val} {g : Val → I.State}
    {n : Nat} {τ : Ty}
    (he : I.exec t.st = some (.rmw k false ⟨BitVec.ofNat 64 mc, 8⟩ op fun v => .done (g v)))
    (hrt : (MemSide.ofLabels rd lbl lsize K G mh mc mu mo mcl mown mmp mab mpl mxa
      (lo := mlo)).rt (BitVec.ofNat 64 mc).toNat)
    (hop : ∀ old, op old = some ((old.setWidth 64 + BitVec.ofNat 64 (mu n τ)).setWidth 128))
    {Y : Val → I.State → Prop}
    (hX : ∀ old, G ⟨BitVec.ofNat 64 mc, 8⟩ old → (∀ w, (⟨BitVec.ofNat 64 mc, 8⟩, w) ∈ mown t.st → old = w) →
      (old.setWidth 64).toNat ≤ mcl → mlo (old.setWidth 64).toNat →
      G ⟨BitVec.ofNat 64 mc, 8⟩ ((old.setWidth 64 + BitVec.ofNat 64 (mu n τ)).setWidth 128) ∧ Y old (g old)) :
    ∃ old : Val, (∃ tr, TLatestP tm t.prom mc tr ∧ tm.read? (wordLoc mc) tr = some old) ∧
      (∀ w, (wordLoc mc, w) ∈ mown t.st → old = w) ∧
      ((old.setWidth 64).toNat ≤ mcl → mlo (old.setWidth 64).toNat → Y old o.thread.st) ∧
      Inv1 Λ lbl lsize ts o.thread o.mem sm ∧
      CtrW t tm o tid mc ((old.setWidth 64 + BitVec.ofNat 64 (mu n τ)).setWidth 128) := by
  obtain ⟨old, tr, hst, hlat, hr, hw⟩ :=
    stepOne_rmw_cases A (a := mc) he hstep ho h.coh fun q hq => (h.mem.tq_le q hq).2
  obtain ⟨-, -, -, -, hi⟩ := RtRmw.inv1_rtRmw A h (a := mc) he hrt hstep ho
  have hoo := hown.read hlat hr
  refine ⟨old, ⟨tr, hlat, hr⟩, hoo, fun hc hl =>
    hst ▸ (hX old (msgsExcept_read_tlatestP hGm hGi hlat hr) hoo hc hl).2,
    hi, ?_⟩
  rcases hw with ⟨hn, -⟩ | ⟨new, hnew, hw⟩
  · rw [hop old] at hn; cases hn
  · rw [hop old] at hnew
    cases hnew
    exact hw

/-- **`out_localP` with the counter's add writing** (`CtrW`): an `Out`
row off a system call under `MemSide.ofLabels`, under outstanding promises,
as `ExtRows.out_localP` gives it, the counter's add (`Out.ctrRmw`) also
giving the outcome's write of the new count. -/
theorem out_localW {K : Kernel.Abi I} {rd : TermRun.Word → Prop} (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) (hns : K.atSys t.st = false)
    (hw8 : ∀ tree, I.exec t.st = some tree → Wide8Tree tree)
    (hGm : MsgsExcept (fun m => G m.loc m.val) t.prom tm) (hGi : ∀ l, G l (tm.initVal l))
    (hown : OwnOk (mown t.st) tm t.prom)
    (hout : Out p lbl (MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl mown mmp mab mpl mxa
      (lo := mlo)) X t.st c) :
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
        ((old.setWidth 64).toNat ≤ mcl → mlo (old.setWidth 64).toNat →
          X o.thread.st { c with hold := some (mc, TermRun.cst (.num (old.setWidth 64).toNat)) }) ∧
        Inv1 Λ lbl lsize ts o.thread o.mem sm ∧
        CtrW t tm o tid mc ((old.setWidth 64 + BitVec.ofNat 64 (mu n τ)).setWidth 128)) ∨
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
  | fence k s' c' he hr hx =>
    obtain ⟨hx', hi⟩ := row_fence h hstep ho he hx
    exact .inl ⟨c', hr.local, hx', hi⟩
  | holdLoad kl A' g x sa u v e he hx hA hh hX =>
    exact .inr (.inr (.inr (.inl ⟨kl, A', g, x, sa, u, v, e, he, hx, hA, hh, hX⟩)))
  | xchgStore kr A' V s' x sa u v e tv wv wold he hx hA hh hev hv hX =>
    exact .inr (.inr (.inr (.inr (.inl ⟨kr, A', V, s', x, sa, u, v, e, tv, wv, wold, he, hx, hA, hh, hev, hv, hX⟩))))
  | ctrRmw k op g x τ e n he hrt _ hs hh hop hX =>
    obtain ⟨a, ta, ws, ht, hev, hn⟩ := hs.resolve_right fun h => h.1
    obtain ⟨old, hlat, hoo, hland, hi, hw⟩ := ctrRmw_row (Y := fun old s' =>
        X s' { c with hold := some (mc, TermRun.cst (.num (old.setWidth 64).toNat)) }) h hstep ho hGm hGi hown he
      hrt hop hX
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨x, a, τ, e, ta, ws, n, old, ht, hev, hn, hh, hlat, hoo, hland, hi,
      hw⟩)))))
  | alloc s' A' x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX =>
    obtain ⟨hm, -, hP, hi⟩ := inv1_silent h he (silentTree_done s') hstep ho
    exact .inr (.inr (.inr (.inr (.inr (.inr ⟨s', A', x, a, τ, e, ta, ws, k, wold, old, us, hP, ht, hev, hk, hh,
      hold, hA, hc, hu, hX, hm, hi⟩)))))
  | newStore _ _ _ _ _ _ _ _ _ _ _ hN => exact hN.elim

/-- **`out_memP` with the counter's word named** (`ExtRows.out_memP`, its
last kind, the counter's add, also saying the word written is the
counter's): the memory and promises after an `Out` row's outcome off a
system call under outstanding promises. -/
theorem out_memW {K : Kernel.Abi I} {rd : TermRun.Word → Prop}
    (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) (hns : K.atSys t.st = false)
    (hw8 : ∀ tree, I.exec t.st = some tree → Wide8Tree tree)
    (hGm : MsgsExcept (fun m => G m.loc m.val) t.prom tm) (hGi : ∀ l, G l (tm.initVal l))
    (hown : OwnOk (mown t.st) tm t.prom)
    (hout : Out p lbl (MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl mown mmp mab mpl mxa
      (lo := mlo)) X t.st c) :
    (o.mem = tm ∧ o.thread.prom = t.prom) ∨ ∃ (L : Loc) (V : Val), L.bytes = 8 ∧
      ((o.mem = (tm.append ⟨L, V, tid⟩).1 ∧ o.thread.prom = t.prom) ∨
        ∃ q ∈ t.prom, tm.get? q = some ⟨L, V, tid⟩ ∧ o.mem = tm ∧ o.thread.prom = t.prom.erase q) ∧
      ((¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat) ∧ mmp L true ∧ G L V ∨
        (∃ (x : String) (a b : At) (e : Expr) (ty : Ty) (w : TermRun.Word) (sa : WeakMem.Address),
          c.term = .let_ x (.store true a b none) e ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
          ValRep lbl w.val L.addr.toNat ∧ w.val = .loc sa 0) ∨
        (∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : At) (e : Expr),
          XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) L.addr.toNat) ∨
        L = wordLoc mc ∧ (¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat) ∧ mmp L true ∧
          (∃ (x : String) (a : At) (τ : Ty) (e : Expr), c.term = .let_ x (.newBuf a τ) e) ∧
          ((∀ v tr, tm.read? (wordLoc mc) tr = some v →
            (v.setWidth 64).toNat ≤ mcl ∧ mlo (v.setWidth 64).toNat) → G L V)) := by
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
  | fence k s' c' he => obtain ⟨hm, hp, -⟩ := inv1_fence h he hstep ho; exact .inl ⟨hm, hp⟩
  | holdLoad kl A' g x sa u v e he => obtain ⟨hm, hp, -⟩ := inv1_rtLoad h he hstep ho; exact .inl ⟨hm, hp⟩
  | alloc s' A' x a τ e ta ws k _ _ _ he =>
    obtain ⟨hm, hp, -⟩ := inv1_silent h he (silentTree_done s') hstep ho; exact .inl ⟨hm, hp⟩
  | newStore _ _ _ _ _ _ _ _ _ _ _ hN => exact hN.elim
  | ctrRmw k op g x τ e n he hrt hmp hs hh hop hX =>
    obtain ⟨a, ta, ws, ht, hev, hn⟩ := hs.resolve_right fun h => h.1
    obtain ⟨old, tr, -, hl, hr, ⟨-, hm, hp⟩ | ⟨new, hnew, hw⟩⟩ :=
      stepOne_rmw_cases A (a := mc) he hstep ho h.coh hpl
    · exact .inl ⟨hm, hp⟩
    · have hk : (∀ v tr, tm.read? (wordLoc mc) tr = some v →
            (v.setWidth 64).toNat ≤ mcl ∧ mlo (v.setWidth 64).toNat) → G (wordLoc mc) new :=
        fun hc => by
          rw [hop old] at hnew
          cases hnew
          exact (hX old (msgsExcept_read_tlatestP hGm hGi hl hr) (hown.read hl hr) (hc old tr hr).1 (hc old tr hr).2).1
      rcases hw with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
      · exact .inr ⟨_, new, rfl, .inr ⟨q, hq, hg, hm, hp⟩, .inr (.inr (.inr ⟨rfl, hrt, hmp, ⟨x, a, τ, e, ht⟩, hk⟩))⟩
      · exact .inr ⟨_, new, rfl, .inl ⟨hm, hp⟩, .inr (.inr (.inr ⟨rfl, hrt, hmp, ⟨x, a, τ, e, ht⟩, hk⟩))⟩
  | xchgStore kr A' V s' x sa u v e tv wv wold he hx hA =>
    rw [← wordLoc_toNat] at he
    rcases (stepOne_store_cases A he hstep ho hpl).2 with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
    · rw [wordLoc_toNat] at hg
      exact .inr ⟨_, V, rfl, .inr ⟨q, hq, hg, hm, hp⟩, .inr (.inr (.inl ⟨x, sa, u, v, e, hx, hA⟩))⟩
    · rw [wordLoc_toNat] at hm
      exact .inr ⟨_, V, rfl, .inl ⟨hm, hp⟩, .inr (.inr (.inl ⟨x, sa, u, v, e, hx, hA⟩))⟩

end Spike.Lib.CtrRows
