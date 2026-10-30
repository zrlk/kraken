/-
**Rows where the source's publication is admitted at a fence**: an `Out`
row under a memory side with `pub := P` is a fence row (its `FenceRun` under
`P`) or the same row under the memory side with no publication (`pub :=
False`); a row whose instruction is no fence is the latter outright. So the
rows of `CtrRowsN` (`out_localN`, `out_memN`) carry over, the fence row
returned with its `FenceRun` (a local run, or under `P` the publication step
then a local run).

- `Out.unpub`: an `Out` row is a fence row or one with no publication.
- `Out.unpub_of`: an `Out` row whose instruction is no fence is one with no
  publication (at any `pub`, `newOk`).
- `msNP`: `msN` with `pub := P`.
- `out_localNP`: `out_localN` under `msNP`, plus the fence row (its
  `FenceRun`, the thread's state and `Inv1` after it).
- `out_memNP`: `out_memN` under `msNP` (a fence moves neither memory nor
  promises).
-/
import Spike.Lib.CtrRowsN

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

section Unpub

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}

/-- **An `Out` row is a fence row or one with no publication**: a fence of
kind `k` to `s'` with the source's `FenceRun` under `ms.pub` to a control
landing in `X`, or the same row under `ms` with `pub := False`. -/
theorem Out.unpub {ms : MemSide I} {X : Frag I} {s : I.State} {c : Ctl} (h : Out p lbl ms X s c) :
    (∃ (k : Kraken.FenceKind) (s' : I.State) (c' : Ctl),
        I.exec s = some (.fence k fun _ => .done s') ∧ FenceRun p ms.pub k c c' ∧ X s' c') ∨
      Out p lbl { ms with pub := False } X s c := by
  cases h with
  | silent s' c' he hr hx => exact .inr (.silent s' c' he hr hx)
  | choice P t he hs hx => exact .inr (.choice P t he hs hx)
  | load kl A g x a e ty w he ht hev hv hx htag => exact .inr (.load kl A g x a e ty w he ht hev hv hx htag)
  | store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag =>
    exact .inr (.store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag)
  | rtStore kr L V s' c' he hrt hm hG hr hx => exact .inr (.rtStore kr L V s' c' he hrt hm hG hr hx)
  | rtLoad kl L g c' he hrt hm hr hx => exact .inr (.rtLoad kl L g c' he hrt hm hr hx)
  | rtRmw k L op g c' he hrt hm hr hx => exact .inr (.rtRmw k L op g c' he hrt hm hr hx)
  | sys K call hK ha hd hok hx => exact .inr (.sys K call hK ha hd hok hx)
  | holdLoad kl A g x sa u v e he hx hA hh hX => exact .inr (.holdLoad kl A g x sa u v e he hx hA hh hX)
  | xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX =>
    exact .inr (.xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX)
  | ctrRmw k op g x τ e n he hrt hm hs hh hop hX => exact .inr (.ctrRmw k op g x τ e n he hrt hm hs hh hop hX)
  | alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX =>
    exact .inr (.alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX)
  | newStore kr A V s' x a t e w wold old hN he hm ht hev hu hv hh hold hA hc hX =>
    exact .inr (.newStore kr A V s' x a t e w wold old hN he hm ht hev hu hv hh hold hA hc hX)
  | emit K buf n Pw Qw hK ha hd h0 hb hr hq => exact .inr (.emit K buf n Pw Qw hK ha hd h0 hb hr hq)
  | fence k s' c' he hr hx => exact .inl ⟨k, s', c', he, hr, hx⟩

/-- **An `Out` row whose instruction is no fence** is one with no
publication (`pub := False`), at any `pub` and `newOk`. -/
theorem Out.unpub_of {ms : MemSide I} {X : Frag I} {s : I.State} {c : Ctl} (h : Out p lbl ms X s c)
    (hnf : ∀ k t', I.exec s ≠ some (.fence k t')) : Out p lbl { ms with pub := False } X s c :=
  h.unpub.resolve_left fun ⟨k, _, _, he, _⟩ => hnf k _ he

end Unpub

namespace CtrRowsN

open Kraken.Promising.Lower Scc.Sem Spike.Lib.ExtThread Spike.Lib.ExtRows Spike.Lib.CtrRows

variable {I : ISA} {A : Arch} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory}
  {sm : WeakMem.Memory} {tid : Nat} {outs : List (Except String (Kraken.Promising.Outcome I))}
  {o : Kraken.Promising.Outcome I} {p : Prog} {X : Frag I} {c : Ctl} {G : Loc → Val → Prop}
  {mh mc mcl : Nat} {mu mo : Nat → Ty → Nat} {mown : I.State → List (Loc × Val)} {mmp : Loc → Bool → Prop}
  {mab : I.State → Prop} {mpl : I.State → Ctl → Prop} {mxa : WeakMem.AllocLabel → Nat → Nat → Frag I}
  {mlo : Nat → Prop} {N P : Prop}

/-- **The memory side with box allocations admitted where `N` holds and the
source's publication at a fence where `P` holds**: `msN` with `pub := P`. -/
abbrev msNP (rd : TermRun.Word → Prop) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (K : Kernel.Abi I) (G : Loc → Val → Prop) (mh mc : Nat) (mu mo : Nat → Ty → Nat) (mcl : Nat)
    (mown : I.State → List (Loc × Val)) (mmp : Loc → Bool → Prop) (mab : I.State → Prop)
    (mpl : I.State → Ctl → Prop) (mxa : WeakMem.AllocLabel → Nat → Nat → Frag I) (mlo : Nat → Prop)
    (N P : Prop) : MemSide I :=
  { msN rd lbl lsize K G mh mc mu mo mcl mown mmp mab mpl mxa mlo N with pub := P }

/-- **`out_localN` where the source's publication is admitted at a fence**
(`msNP … N P`): `out_localN`'s rows, or the fence row: a fence of kind `k`,
the source's `FenceRun` under `P` (a local run, or under `P` its publication
step then a local run) to `c'`, which lands in `X` with the thread's state
after the step, `Inv1` kept. -/
theorem out_localNP {K : Kernel.Abi I} {rd : TermRun.Word → Prop} (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) (hns : K.atSys t.st = false)
    (hw8 : ∀ tree, I.exec t.st = some tree → Wide8Tree tree)
    (hGm : MsgsExcept (fun m => G m.loc m.val) t.prom tm) (hGi : ∀ l, G l (tm.initVal l))
    (hown : OwnOk (mown t.st) tm t.prom)
    (hout : Out p lbl (msNP rd lbl lsize K G mh mc mu mo mcl mown mmp mab mpl mxa mlo N P) X t.st c) :
    (∃ (k : Kraken.FenceKind) (s' : I.State) (c' : Ctl),
        I.exec t.st = some (.fence k fun _ => .done s') ∧ FenceRun p P k c c' ∧ X o.thread.st c' ∧
        Inv1 Λ lbl lsize ts o.thread o.mem sm) ∨
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
  rcases hout.unpub with ⟨k, s', c', he, hr, hx⟩ | hout
  · obtain ⟨hx', hi⟩ := row_fence h hstep ho he hx
    exact .inl ⟨k, s', c', he, hr, hx', hi⟩
  · exact .inr (out_localN (mlo := mlo) h hstep ho hns hw8 hGm hGi hown hout)

/-- **`out_memN` where the source's publication is admitted at a fence**
(`msNP … N P`): `out_memN`'s conclusion at any `P`. The fence row needs no
disjunct of its own: a fence moves neither memory nor promises
(`inv1_fence`), so it lands in the first (`o.mem = tm`, promises kept)
whatever its `FenceRun`; every other row is one under `msN` (`Out.unpub`). -/
theorem out_memNP {K : Kernel.Abi I} {rd : TermRun.Word → Prop}
    (h : Inv1 Λ lbl lsize ts t tm sm)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) (hns : K.atSys t.st = false)
    (hw8 : ∀ tree, I.exec t.st = some tree → Wide8Tree tree)
    (hGm : MsgsExcept (fun m => G m.loc m.val) t.prom tm) (hGi : ∀ l, G l (tm.initVal l))
    (hown : OwnOk (mown t.st) tm t.prom)
    (hout : Out p lbl (msNP rd lbl lsize K G mh mc mu mo mcl mown mmp mab mpl mxa mlo N P) X t.st c) :
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
          N ∧ c.term = .let_ x (.new a) e ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
          TermRun.accs ty = some [.one] ∧ ValRep lbl w.val V.toNat ∧ c.hold = some (mc, wold) ∧
          TermRun.numOf [wold] = some old ∧ L.addr.toNat = mh + 16 * old + mo 1 ty ∧ old + mu 1 ty ≤ mcl ∧
          mmp L true)) := by
  rcases hout.unpub with ⟨k, s', c', he, -, -⟩ | hout
  · obtain ⟨hm, hp, -⟩ := inv1_fence h he hstep ho
    exact .inl ⟨hm, hp⟩
  · exact out_memN (mlo := mlo) h hstep ho hns hw8 hGm hGi hown hout

end CtrRowsN

/-- info: 'Spike.Lib.Out.unpub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Out.unpub

/-- info: 'Spike.Lib.Out.unpub_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Out.unpub_of

/-- info: 'Spike.Lib.CtrRowsN.out_localNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.CtrRowsN.out_localNP

/-- info: 'Spike.Lib.CtrRowsN.out_memNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.CtrRowsN.out_memNP

end Spike.Lib
