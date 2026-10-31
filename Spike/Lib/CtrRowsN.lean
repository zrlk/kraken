/-
**The counter's add and the box's initialising store as rows, where box
allocations are admitted**: `CtrRows.out_localW` / `out_memW` over the
memory side `MemSide.ofLabels … with newOk := N`. The counter's add is at
an allocation site (`AllocSite N`: a buffer, or, under `N`, a box), and the
box's initialising store (`Out.newStore`, under `N`) is one more kind: a
plain store of the box word at the base of the cell the allocator handed
out, the counter's old count held.

The initialising store is neither a runtime write (it is to the arena) nor
a store to a placed label (the box's label is placed by this very row,
`NewRow.row_newStore`), so it is returned with its premises and its
consumer places it.

- `out_localN`: `out_localW` with the counter's add over `AllocSite N` and
  the box's initialising store (its premises).
- `out_memN`: `out_memW` with the counter's add over `AllocSite N` and the
  box's initialising store's kind (the word at the cell's base, mapped for
  writing, the counter's old count held).
- `msN`: the memory side; `NewSt`: the initialising store's premises.
-/
import Spike.Lib.CtrRows

namespace Spike.Lib.CtrRowsN

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.Lower Scc.Sem Spike.Lib.ExtThread Spike.Lib.ExtRows Spike.Lib.CtrRows

variable {I : ISA} {A : Arch} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory}
  {sm : WeakMem.Memory} {tid : Nat} {outs : List (Except String (Kraken.Promising.Outcome I))}
  {o : Kraken.Promising.Outcome I} {p : Prog} {X : Frag I} {c : Ctl} {G : Loc → Val → Prop}
  {mh mc mcl : Nat} {mu mo : Nat → Ty → Nat} {mown : I.State → List (Loc × Val)} {mmp : Loc → Bool → Prop}
  {mab : I.State → Prop} {mpl : I.State → Ctl → Prop} {mxa : WeakMem.AllocLabel → Nat → Nat → Frag I}
  {mlo : Nat → Prop} {N : Prop}

/-- **The memory side with box allocations admitted where `N` holds**:
`MemSide.ofLabels` with `newOk := N`. -/
abbrev msN (rd : TermRun.Word → Prop) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (K : Kernel.Abi I) (G : Loc → Val → Prop) (mh mc : Nat) (mu mo : Nat → Ty → Nat) (mcl : Nat)
    (mown : I.State → List (Loc × Val)) (mmp : Loc → Bool → Prop) (mab : I.State → Prop)
    (mpl : I.State → Ctl → Prop) (mxa : WeakMem.AllocLabel → Nat → Nat → Frag I) (mlo : Nat → Prop)
    (N : Prop) : MemSide I :=
  { MemSide.ofLabels rd lbl lsize (some K) G mh mc mu mo mcl mown mmp mab mpl mxa (lo := mlo) with newOk := N }

/-- **The box's initialising store, its premises** (`Out.newStore`'s,
under `msN`): the store of `V` to the cell's base `A`, mapped for writing,
at `let x = new a in e` with `a` a one-word value `w` that `V` represents,
the counter's old count `old` held, `A` the cell's base within the cells,
and the landing for every label not yet placed. -/
def NewSt (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (mh mc : Nat) (mu mo : Nat → Ty → Nat) (mcl : Nat)
    (mmp : Loc → Bool → Prop) (mxa : WeakMem.AllocLabel → Nat → Nat → Frag I) (N : Prop) (s : I.State)
    (c : Ctl) : Prop :=
  ∃ (kr : Kraken.StoreKind) (A : BitVec 64) (V : Val) (s' : I.State) (x : String) (a : At) (ty : Ty) (e : Expr)
      (w wold : TermRun.Word) (old : Nat),
    N ∧ I.exec s = some (.store kr false ⟨A, 8⟩ V fun _ => .done s') ∧ mmp ⟨A, 8⟩ true ∧
      (∃ T, c.term = .let_ x (.new a T) e) ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧ TermRun.accs ty = some [.one] ∧
      ValRep lbl w.val V.toNat ∧ c.hold = some (mc, wold) ∧ TermRun.numOf [wold] = some old ∧
      A.toNat = mh + 16 * old + mo 1 ty ∧ old + mu 1 ty ≤ mcl ∧
      (∀ l, lbl l = none →
        mxa l A.toNat 1 s' ⟨e, (x, .ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩)

/-- **`out_localW` where box allocations are admitted** (`msN … N`): the
counter's add at an allocation site (`AllocSite N`), and the box's
initialising store (`NewSt`) one more row. -/
theorem out_localN {K : Kernel.Abi I} {rd : TermRun.Word → Prop} (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) (hns : K.atSys t.st = false)
    (hw8 : ∀ tree, I.exec t.st = some tree → Wide8Tree tree)
    (hGm : MsgsExcept (fun m => G m.loc m.val) t.prom tm) (hGi : ∀ l, G l (tm.initVal l))
    (hown : OwnOk (mown t.st) tm t.prom)
    (hout : Out p lbl (msN rd lbl lsize K G mh mc mu mo mcl mown mmp mab mpl mxa mlo N) X t.st c) :
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
      (∃ (x : String) (τ : Ty) (e : Expr) (n : Nat) (old : Val),
        AllocSite N c x n τ e ∧
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
        o.mem = tm ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm) ∨
      NewSt p lbl mh mc mu mo mcl mmp mxa N t.st c := by
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
    obtain ⟨hst, hi⟩ := row_rtStore (rd := rd) (mK := some K) (mG := G) (mh := mh) (mc := mc) (mu := mu)
      (mo := mo) (mcl := mcl) (mown := mown) (mmp := mmp) (mab := mab) (mpl := mpl) (mxa := mxa) (mlo := mlo)
      h hstep ho he hL hrt
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
    obtain ⟨old, hlat, hoo, hland, hi, hw⟩ := ctrRmw_row (Y := fun old s' =>
        X s' { c with hold := some (mc, TermRun.cst (.num (old.setWidth 64).toNat)) }) (mlo := mlo) (mmp := mmp)
      (mab := mab) (mpl := mpl) (mxa := mxa) (mh := mh) (mo := mo) (rd := rd) (K := some K) h hstep ho hGm hGi
      hown he hrt hop hX
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨x, τ, e, n, old, hs, hh, hlat, hoo, hland, hi, hw⟩)))))
  | alloc s' A' x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX =>
    obtain ⟨hm, -, hP, hi⟩ := inv1_silent h he (silentTree_done s') hstep ho
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨s', A', x, a, τ, e, ta, ws, k, wold, old, us, hP, ht, hev, hk,
      hh, hold, hA, hc, hu, hX, hm, hi⟩))))))
  | newStore kr A' V s' x a ty e w wold old hN he hm ht hev hu hv hh hold hA hc hX =>
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨kr, A', V, s', x, a, ty, e, w, wold, old, hN, he, hm, ht, hev,
      hu, hv, hh, hold, hA, hc, hX⟩))))))

/-- **`out_memW` where box allocations are admitted** (`msN … N`): the
memory and promises after an `Out` row's outcome off a system call under
outstanding promises; the counter's add at an allocation site
(`AllocSite N`), and one more write kind, the box's initialising store:
the word at the cell's base `heap + 16·old + off 1 t` (mapped for writing)
at `let x = new a in e`, `a` a one-word value that the value written
represents, the counter's old count `old` held, within the cells. -/
theorem out_memN {K : Kernel.Abi I} {rd : TermRun.Word → Prop}
    (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) (hns : K.atSys t.st = false)
    (hw8 : ∀ tree, I.exec t.st = some tree → Wide8Tree tree)
    (hGm : MsgsExcept (fun m => G m.loc m.val) t.prom tm) (hGi : ∀ l, G l (tm.initVal l))
    (hown : OwnOk (mown t.st) tm t.prom)
    (hout : Out p lbl (msN rd lbl lsize K G mh mc mu mo mcl mown mmp mab mpl mxa mlo N) X t.st c) :
    (o.mem = tm ∧ o.thread.prom = t.prom) ∨ ∃ (L : Loc) (V : Val), L.bytes = 8 ∧
      ((o.mem = (tm.append ⟨L, V, tid⟩).1 ∧ o.thread.prom = t.prom) ∨
        ∃ q ∈ t.prom, tm.get? q = some ⟨L, V, tid⟩ ∧ o.mem = tm ∧ o.thread.prom = t.prom.erase q) ∧
      ((¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat) ∧ mmp L true ∧ G L V ∨
        (∃ (x : String) (a b : At) (e : Expr) (ty : Ty) (w : TermRun.Word) (sa : WeakMem.Address),
          c.term = .let_ x (.store true a b none) e ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
          ValRep lbl w.val L.addr.toNat ∧ w.val = .loc sa 0) ∨
        (∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : At) (e : Expr),
          XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) L.addr.toNat) ∨
        (L = wordLoc mc ∧ (¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat) ∧ mmp L true ∧
          (∃ (x : String) (n : Nat) (τ : Ty) (e : Expr), AllocSite N c x n τ e) ∧
          ((∀ v tr, tm.read? (wordLoc mc) tr = some v →
            (v.setWidth 64).toNat ≤ mcl ∧ mlo (v.setWidth 64).toNat) → G L V)) ∨
        (∃ (x : String) (a : At) (e : Expr) (ty : Ty) (w wold : TermRun.Word) (old : Nat),
          N ∧ (∃ T, c.term = .let_ x (.new a T) e) ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
          TermRun.accs ty = some [.one] ∧ ValRep lbl w.val V.toNat ∧ c.hold = some (mc, wold) ∧
          TermRun.numOf [wold] = some old ∧ L.addr.toNat = mh + 16 * old + mo 1 ty ∧ old + mu 1 ty ≤ mcl ∧
          mmp L true)) := by
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
  | newStore kr A' V s' x a ty e w wold old hN he hmp ht hev hu hv hh hold hA hc hX =>
    rw [← wordLoc_toNat] at he
    rcases (stepOne_store_cases A he hstep ho hpl).2 with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
    · rw [wordLoc_toNat] at hg
      exact .inr ⟨_, V, rfl, .inr ⟨q, hq, hg, hm, hp⟩,
        .inr (.inr (.inr (.inr ⟨x, a, e, ty, w, wold, old, hN, ht, hev, hu, hv, hh, hold, hA, hc, hmp⟩)))⟩
    · rw [wordLoc_toNat] at hm
      exact .inr ⟨_, V, rfl, .inl ⟨hm, hp⟩,
        .inr (.inr (.inr (.inr ⟨x, a, e, ty, w, wold, old, hN, ht, hev, hu, hv, hh, hold, hA, hc, hmp⟩)))⟩
  | ctrRmw k op g x τ e n he hrt hmp hs hh hop hX =>
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
      · exact .inr ⟨_, new, rfl, .inr ⟨q, hq, hg, hm, hp⟩,
          .inr (.inr (.inr (.inl ⟨rfl, hrt, hmp, ⟨x, n, τ, e, hs⟩, hk⟩)))⟩
      · exact .inr ⟨_, new, rfl, .inl ⟨hm, hp⟩, .inr (.inr (.inr (.inl ⟨rfl, hrt, hmp, ⟨x, n, τ, e, hs⟩, hk⟩)))⟩
  | xchgStore kr A' V s' x sa u v e tv wv wold he hx hA =>
    rw [← wordLoc_toNat] at he
    rcases (stepOne_store_cases A he hstep ho hpl).2 with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
    · rw [wordLoc_toNat] at hg
      exact .inr ⟨_, V, rfl, .inr ⟨q, hq, hg, hm, hp⟩, .inr (.inr (.inl ⟨x, sa, u, v, e, hx, hA⟩))⟩
    · rw [wordLoc_toNat] at hm
      exact .inr ⟨_, V, rfl, .inl ⟨hm, hp⟩, .inr (.inr (.inl ⟨x, sa, u, v, e, hx, hA⟩))⟩

/-- info: 'Spike.Lib.CtrRowsN.out_localN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.CtrRowsN.out_localN

/-- info: 'Spike.Lib.CtrRowsN.out_memN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.CtrRowsN.out_memN

end Spike.Lib.CtrRowsN
