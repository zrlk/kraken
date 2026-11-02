/-
**The worker's store phase as a wake worker side** (C4, relation half;
data in `Spike/Lib/X64HelloW1.lean`, the print phase in
`Spike/Lib/X64HelloW1Print.lean`): past `print`'s return the source worker is
at wake's store tail (`X64HelloW1.StorePh`), on no frame, so its rows are
wake's at depth `0`, and `X64WakeW1`'s store, unpark and exit rows apply to
hello's worker unchanged.

- `StoreT`: the store phase's terms (`wkStore`, `wkUnpark`, `ret ()`).
- `localRun_storeT_eq`, `frameRun_storeT_eq`: from a store-phase control
  (with `c` bound, `EnvCJ`) every local run and every frame run on no frame
  is empty.
- `WiS D w`: `D.Wi w` at depth `0`, at a store-phase control with no hold
  and `EnvCJ`; `NoWrite D`: at `WiS` the worker is at no `write(1, …)`
  (the premise of the bridge: the output row `Out.emit` lands at `print`'s
  controls, which are not store-phase ones; see `NoWrite`).
- `closed_wiS`: `WiS D w` is closed under wake's thread rows `OutT` (every
  `OutTS` row of `D.Wi` from it is one).
- `wsideW D hcw hem`: the wake worker side (`X64WakeW1.WSide`) over
  `helloSrc` at `WiS`; `relW Q D hcw hem`: `Q` with wake's `PT1` at it.
- `pt1_of_pt1h`, `pt1h_of_pt1`: `PT1h` in the store phase is wake's `PT1`
  at `wsideW`, and back.
- `post_toW` (from `Post`'s parts in the store phase), `post_toW_pass` (past
  the store), `post_ofW`: `Post` at `PT1hE` (`PT1h` or mid-`write`) and at
  `relW` agree in the store phase; `post_ofW_store`: at `relW` the worker is in the store phase.
- `envCJ_consD`, `envCJ_consW`: `EnvCJ` survives binding `d` and `w`.

**Differences from wake's worker side**: `wsideW`'s fields are all
`X64WakeW1.WSide`'s; its `ms` is `D.ms w []` (the worker's memory side at depth
`0`), its `wk` is vacuous (`WiS` is never before the split,
`X64HelloB7b.wk_of_noPre`). `X64WakeW1.WCompat` at `relW` is not stated here.

x86-64 twin of `Spike/Lib/HelloW1Store.lean` (same names, namespaces with the `X64` prefix).

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only
live constants): `post_ofW_store`, `post_toW_pass`.
-/
import Spike.Lib.X64HelloW1Print
import Spike.Lib.X64HelloB7b
import Spike.Lib.X64WakeW1Src

namespace Spike.Lib.X64HelloW1Store

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.HelloProt
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.HelloSegThrS (OutTS)
open Spike.Lib.X64HelloW1 (WSideH PT1h StorePh PartsH PrintPh)
open Spike.Lib.X64WakeW1 (EnvCJ)

variable {ι : Type}

/-! ## The store phase's controls -/

/-- **The store phase's terms**: the store, the unpark, the return. -/
def StoreT (e : Expr) : Prop := e = wkStore ∨ e = wkUnpark ∨ e = .ret .unit

/-- A store-phase term is past the split. -/
theorem storeT_not_pre {e : Expr} (h : StoreT e) : ¬ X64WakeW1.PreSplit e := by
  rintro (h' | h') <;> rcases h with h | h | h <;> rw [h] at h' <;>
    simp [wkStore, wkUnpark, X64WakeW1.wkTail, X64WakeW1.wkBody] at h'

/-- A store-phase term that binds is the store or the unpark. -/
theorem storeT_let {e e' : Expr} {x : String} {op : Op} (h : StoreT e) (he : e = .let_ x op e') :
    (x = "d" ∧ op = .store true (.var "c") (.lit 1) none ∧ e' = wkUnpark) ∨
      (x = "w" ∧ op = .ext .unpark (.var "j") ∧ e' = .ret .unit) := by
  rcases h with h | h | h <;> rw [h] at he <;> simp_all [wkStore, wkUnpark]

/-- A store-phase term is a worker term. -/
theorem storeT_wTerm {e : Expr} (h : StoreT e) : X64WakeW1.WTerm e := by
  rcases h with h | h | h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr h)))

/-- **`EnvCJ` survives binding `d`** (`X64WakeW1.envCJ_cons`, which this file
does not import). -/
theorem envCJ_consD {cw : TermRun.Word} {env : TermRun.Env} (h : EnvCJ cw env) (ty : Ty) (ws : List TermRun.Word) :
    EnvCJ cw (("d", ty, ws) :: env) := by
  simpa [EnvCJ, TermRun.evalAt, TermRun.lookupE, List.find?_cons] using h

/-- **`EnvCJ` survives binding `w`.** -/
theorem envCJ_consW {cw : TermRun.Word} {env : TermRun.Env} (h : EnvCJ cw env) (ty : Ty) (ws : List TermRun.Word) :
    EnvCJ cw (("w", ty, ws) :: env) := by
  simpa [EnvCJ, TermRun.evalAt, TermRun.lookupE, List.find?_cons] using h

/-- **No local step from a store-phase control** (with `c` bound). -/
theorem localStep_storeT_false {p : Prog} {cw : TermRun.Word} {cS : WeakMem.Address} {c c' : Ctl}
    (h : LocalStep p c c') (ht : StoreT c.term) (hc : EnvCJ cw c.env) (hcw : cw.val = .loc cS 0) : False := by
  rcases ht with ht | ht | ht
  · exact X64WakeW1.localStep_wkStore_false h ht hc hcw
  · exact X64WakeW1.localStep_wkUnpark_false h ht
  · exact localStep_not_ret h .unit ht

/-- **A local run from a store-phase control is empty.** -/
theorem localRun_storeT_eq {p : Prog} {cw : TermRun.Word} {cS : WeakMem.Address} {c c' : Ctl}
    (hr : LocalRun p c c') (ht : StoreT c.term) (hc : EnvCJ cw c.env) (hcw : cw.val = .loc cS 0) : c' = c := by
  cases hr with
  | refl => rfl
  | step hs _ => exact (localStep_storeT_false hs ht hc hcw).elim

/-- **A frame run from a store-phase control on no frame is empty**: no
local step, no call, no frame to return into. -/
theorem frameRun_storeT_eq {p : Prog} {cw : TermRun.Word} {cS : WeakMem.Address} {c : Ctl}
    {q : Ctl × List TermRun.Frame} (hr : FrameRun p (c, []) q) (ht : StoreT c.term) (hc : EnvCJ cw c.env)
    (hcw : cw.val = .loc cS 0) : q = (c, []) := by
  cases hr with
  | refl => rfl
  | step hs _ =>
    cases hs with
    | loc h => exact (localStep_storeT_false h.toLocalStep ht hc hcw).elim
    | call hc' =>
      rcases storeT_let ht hc' with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h

/-! ## The invariant at depth `0` -/

/-- **The worker's invariant in the store phase**: `D.Wi w` at depth `0`,
at a store-phase control with no hold, `c` bound (`EnvCJ`). -/
def WiS (D : WSideH ι) (w : ι) : Frag isa := fun s c =>
  D.Wi w s c [] ∧ c.hold = none ∧ StoreT c.term ∧ EnvCJ (D.cw w) c.env

/-- **The bridge's premise: no output write in the store phase.** At `WiS`
the target worker is at no `write(1, …)` system call (under the depth-`0`
memory side's kernel model). `Out.emit` lands at the source controls of
`print`'s byte loop (`MemSide.bo`, `ByteOut`), which are not store-phase
ones, so `WiS` is not closed under it; the store phase's target code
(`stlr`, `swpal`, `exit`) has no such `svc`, which the instantiation shows
from `D.Wi`'s pcs. -/
def NoWrite (D : WSideH ι) : Prop :=
  ∀ w s c, WiS D w s c → ∀ (K : Abi isa) (buf n : Nat), (D.ms w []).K = some K → K.atSys s = true →
    decode K.nrs (K.nr s) (K.arg s) ≠ some (.write 1 buf n)

variable {D : WSideH ι}

/-- **The load-or-stutter rows of `D.Wi` from `WiS` are rows of `WiS`**: the
source stays (local runs are empty) or stores `c` into the unpark. -/
theorem outL_wiS (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hem : NoWrite D) {w : ι} {s : isa.State}
    {c : Ctl} (hY : WiS D w s c) (h : OutL helloSrc (D.lbl w) (D.ms w []) (fun s c => D.Wi w s c []) s c) :
    OutL helloSrc (D.lbl w) (D.ms w []) (WiS D w) s c := by
  obtain ⟨cS, hcS⟩ := hcw w
  obtain ⟨hW, hh, hS, hE⟩ := hY
  have hrun : ∀ {c'}, LocalRun helloSrc c c' → c' = c := fun hr => localRun_storeT_eq hr hS hE hcS
  have hstay : ∀ {s'}, D.Wi w s' c [] → WiS D w s' c := fun h => ⟨h, hh, hS, hE⟩
  cases h with
  | ldSt _ _ _ _ _ _ _ _ _ _ ht => rcases storeT_let hS ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
  | out h =>
    refine .out ?_
    cases h with
    | silent s' c' he hr hx => obtain rfl := hrun hr; exact .silent s' _ he (.refl _) (hstay hx)
    | choice P t he hs hx =>
      refine .choice P t he hs fun s' hp => ?_
      obtain ⟨c', hr, hx'⟩ := hx s' hp
      obtain rfl := hrun hr
      exact ⟨_, .refl _, hstay hx'⟩
    | load _ _ _ _ _ _ _ _ _ ht => rcases storeT_let hS ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
    | store kr A V s' x a b e ty tb w' wb he ht hev hv hevb hvb hx htag =>
      rcases storeT_let hS ht with ⟨rfl, -, rfl⟩ | ⟨-, h, -⟩
      · exact .store kr A V s' "d" a b wkUnpark ty tb w' wb he ht hev hv hevb hvb
          ⟨hx, rfl, .inr (.inl rfl), envCJ_consD hE _ _⟩ htag
      · cases h
    | rtStore kr L V s' c' he hrt hm hG hr hx =>
      obtain rfl := hrun hr; exact .rtStore kr L V s' _ he hrt hm hG (.refl _) (hstay hx)
    | rtLoad kl L g c' he hrt hm hr hx =>
      obtain rfl := hrun hr; exact .rtLoad kl L g _ he hrt hm (.refl _) fun v hG ho => hstay (hx v hG ho)
    | rtRmw k L op g c' he hrt hm hr hx =>
      obtain rfl := hrun hr
      exact .rtRmw k L op g _ he hrt hm (.refl _) fun old hG ho => ⟨(hx old hG ho).1, hstay (hx old hG ho).2⟩
    | sys K call hK ha hd hok hx =>
      refine .sys K call hK ha hd hok fun s' hs => ?_
      obtain ⟨c', hr, hx'⟩ := hx s' hs
      obtain rfl := hrun hr
      exact ⟨_, .refl _, hstay hx'⟩
    | holdLoad _ _ _ _ _ _ _ _ _ hx =>
      obtain ⟨-, ⟨_, _, _, _, ht, -⟩ | ⟨_, _, _, _, _, _, _, _, _, ht, -⟩⟩ := hx <;>
        rcases storeT_let hS ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
    | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ _ hx =>
      obtain ⟨-, ⟨_, _, _, _, ht, -⟩ | ⟨_, _, _, _, _, _, _, _, _, ht, -⟩⟩ := hx <;>
        rcases storeT_let hS ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
    | ctrRmw _ _ _ _ _ _ _ _ _ _ hs =>
      obtain ⟨_, _, _, ht, -⟩ | ⟨-, _, _, ⟨_, ht⟩, -⟩ := hs <;>
        rcases storeT_let hS ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
    | alloc s' A x a τ e ta ws k wold old us he ht hev hk hh' hold hA hc hu hX =>
      exact .alloc s' A x a τ e ta ws k wold old us he ht hev hk hh' hold hA hc hu hX
    | newStore kr A V s' x a t e w' wold old hN he hm ht hev hu hv hh' hold hA hc hX =>
      exact .newStore kr A V s' x a t e w' wold old hN he hm ht hev hu hv hh' hold hA hc hX
    | emit K buf n _ _ hK ha hd => exact (hem w s c ⟨hW, hh, hS, hE⟩ K buf n hK ha hd).elim
    | fence k s' c' he hr hx =>
      have hl : LocalRun helloSrc c c' := by
        cases hr with
        | loc h => exact h
        | pub _ hp _ =>
          obtain ⟨-, -, _, _, _, _, _, _, ⟨ht, -⟩ | ⟨_, ht, -⟩, -⟩ := hp <;>
            rcases storeT_let hS ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
      obtain rfl := hrun hl
      exact .fence k s' _ he (.loc (.refl _)) (hstay hx)

/-- **`WiS D w` is closed under wake's thread rows**: every `OutTS` row of
`D.Wi w` from it is an `OutT` row into it (frame runs are empty; the store
lands at the unpark, the unpark at the return). -/
theorem closed_wiS (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hem : NoWrite D) :
    ∀ w s c, WiS D w s c → OutT helloSrc (D.lbl w) (D.ms w []) (WiS D w) s c := by
  intro w s c hY
  obtain ⟨cS, hcS⟩ := hcw w
  have hY' := hY
  obtain ⟨hW, hh, hS, hE⟩ := hY
  have hfr : ∀ {c₁ fs₁}, FrameRun helloSrc (c, []) (c₁, fs₁) → c₁ = c ∧ fs₁ = [] := fun hr => by
    have := frameRun_storeT_eq hr hS hE hcS
    simpa only [Prod.mk.injEq] using this
  have hstay : ∀ {s'}, D.Wi w s' c [] → WiS D w s' c := fun h => ⟨h, hh, hS, hE⟩
  cases D.closed w s c [] hW with
  | pre c₁ fs₁ hr h =>
    obtain ⟨rfl, rfl⟩ := hfr hr
    exact .outL (outL_wiS hcw hem hY' h)
  | frame s' c' fs' he hr hx =>
    obtain ⟨rfl, rfl⟩ := hfr hr
    exact .outL (.out (.silent s' _ he (.refl _) (hstay hx)))
  | fnc k s' c' fs' he hr hx =>
    obtain ⟨rfl, rfl⟩ := hfr hr
    exact .fnc k s' _ he (.refl _) (hstay hx)
  | top c₁ hr h =>
    obtain ⟨rfl, -⟩ := hfr hr
    cases h with
    | outL h => exact .outL (outL_wiS hcw hem hY' h)
    | unpk k A B op g x a e ty jw he hrt hmp hop ht hh' hev hv hA hX =>
      rcases storeT_let hS ht with ⟨-, h, -⟩ | ⟨rfl, -, rfl⟩
      · cases h
      · exact .unpk k A B op g "w" a (.ret .unit) ty jw he hrt hmp hop ht hh' hev hv hA fun old hg ho =>
          ⟨(hX old hg ho).1, (hX old hg ho).2, rfl, .inr (.inr rfl), envCJ_consW hE _ _⟩
    | texit K a hK hat hd ht => exact .texit K a hK hat hd ht
    | fnc k s' c' he hr' hx =>
      obtain rfl := localRun_storeT_eq hr' hS hE hcS
      exact .fnc k s' _ he (.refl _) (hstay hx)

/-! ## The wake worker side -/

/-- **The store phase as a wake worker side** over `helloSrc`: the memory
side at depth `0`, the invariant `WiS`, hello's `cw` and `S`. -/
def wsideW (D : WSideH ι) (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hem : NoWrite D) : X64WakeW1.WSide ι where
  p := helloSrc
  lbl := D.lbl
  ms w := D.ms w []
  Wi := WiS D
  closed := closed_wiS hcw hem
  wk := X64HelloB7b.wk_of_noPre fun _ _ _ h => storeT_not_pre h.2.2.1
  cw := D.cw
  S := D.S

/-- **`KR` modulo the worker** (`relW`'s): `Q.KR` at a configuration with
the same kernel state, main's target thread and the source trace, and
main's source thread up to its permit. Wake's frame fields `WCompat.kr`,
`WCompatX.krp` (thread 1 arbitrary) keep it; `KrpW` gets `Q.KR` back. -/
def KRmod (Q : WakeRel) (w : Q.ι) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (x : Cfg) (sx : TermRun.Cfg), x.2 = t.2 ∧ x.1.threads[0]? = t.1.threads[0]? ∧ sx.trace = s.trace ∧
    (∃ (s0 : TermRun.TTh) (p : Option Nat), sx.ths[0]? = some s0 ∧ s.ths[0]? = some { s0 with permit := p }) ∧
    Q.KR w x sx

/-- **The kernel relation across a worker step setting main's source
permit**, with no byte of a worker `write` out and the worker after the step
in its invariant (`WCompatX.krp`'s twin at hello's `KR`; at `KRH`
`X64HelloWorkerRR.krh_permit`). -/
def KrpW (Q : WakeRel) (D : WSideH Q.ι) : Prop :=
  ∀ w t t' s s' (s0 : TermRun.TTh) (p : Option Nat), Q.KR w t s → t.2.wr 1 = 0 → t'.2 = t.2 →
    t'.1.threads[0]? = t.1.threads[0]? → s.ths[0]? = some s0 → s'.ths[0]? = some { s0 with permit := p } →
    s'.trace = s.trace →
    (∀ t1 s1, t'.1.threads[1]? = some t1 → s'.ths[1]? = some s1 → D.Wi w t1.st (Ctl.of s1) s1.stack) →
    Q.KR w t' s'

/-- **The relation with wake's worker data**: `Q` with `PT1` wake's at
`wsideW`, and `KR` `Q`'s modulo the worker (`KRmod`) with no byte of a
worker `write` out (`wr 1 = 0`;: hello's `KR` carries the
worker's `write` link `X64HelloKRE.Lk`, which reads thread 1, while wake's
frame fields `WCompat.kr`, `krp` leave thread 1 arbitrary). -/
def relW (Q : WakeRel) (D : WSideH Q.ι) (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hem : NoWrite D) :
    WakeRel :=
  { Q with PT1 := X64WakeW1.PT1 (wsideW D hcw hem), KR := fun w t s => KRmod Q w t s ∧ t.2.wr 1 = 0 }

/-- **`KRmod` holds at `Q.KR`.** -/
theorem kRmod_of {Q : WakeRel} {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {s0 : TermRun.TTh} (h : Q.KR w t s)
    (h0 : s.ths[0]? = some s0) : KRmod Q w t s :=
  ⟨t, s, rfl, rfl, rfl, ⟨s0, s0.permit, h0, by rw [h0]⟩, h⟩

/-- **`KRmod` is kept by wake's frame fields** (`kr`: main's source thread
kept). -/
theorem KRmod.frame {Q : WakeRel} {w : Q.ι} {t t' : Cfg} {s s' : TermRun.Cfg} (h : KRmod Q w t s)
    (a : t'.2 = t.2) (b : t'.1.threads[0]? = t.1.threads[0]?) (c : s'.ths[0]? = s.ths[0]?)
    (d : s'.trace = s.trace) : KRmod Q w t' s' := by
  obtain ⟨x, sx, h2, h0, htr, ⟨s0, p, hs0, hs⟩, hk⟩ := h
  exact ⟨x, sx, h2.trans a.symm, h0.trans b.symm, htr.trans d.symm, ⟨s0, p, hs0, c.trans hs⟩, hk⟩

/-- **`KRmod` is kept by wake's frame fields** (`krp`: main's source permit
set). -/
theorem KRmod.permit {Q : WakeRel} {w : Q.ι} {t t' : Cfg} {s s' : TermRun.Cfg} {s0 : TermRun.TTh}
    {p : Option Nat} (h : KRmod Q w t s) (a : t'.2 = t.2) (b : t'.1.threads[0]? = t.1.threads[0]?)
    (c : s.ths[0]? = some s0) (c' : s'.ths[0]? = some { s0 with permit := p }) (d : s'.trace = s.trace) :
    KRmod Q w t' s' := by
  obtain ⟨x, sx, h2, h0, htr, ⟨s0', p', hs0, hs⟩, hk⟩ := h
  rw [hs] at c
  cases c
  exact ⟨x, sx, h2.trans a.symm, h0.trans b.symm, htr.trans d.symm, ⟨s0', p, hs0, c'⟩, hk⟩

/-- **`Q.KR` from `KRmod`**, by `KrpW`, with no byte out and the worker in
its invariant. -/
theorem KRmod.kr {Q : WakeRel} {D : WSideH Q.ι} (hkrp : KrpW Q D) {w : Q.ι} {t : Cfg} {s : TermRun.Cfg}
    (h : KRmod Q w t s) (hwr : t.2.wr 1 = 0)
    (hW : ∀ t1 s1, t.1.threads[1]? = some t1 → s.ths[1]? = some s1 → D.Wi w t1.st (Ctl.of s1) s1.stack) :
    Q.KR w t s := by
  obtain ⟨x, sx, h2, h0, htr, ⟨s0, p, hs0, hs⟩, hk⟩ := h
  exact hkrp w x t sx s s0 p hk (by rw [h2]; exact hwr) h2.symm h0.symm hs0 hs htr.symm hW

variable {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D}

/-- **`PT1h` in the store phase is wake's `PT1`** at `wsideW`. -/
theorem pt1_of_pt1h {w : ι} {tm : Memory} {sm : WeakMem.Memory} {t1 : Thread isa} {s1 : TermRun.TTh}
    (h : PT1h D w tm sm t1 s1) (hS : StorePh (D.cw w) s1) : X64WakeW1.PT1 (wsideW D hcw hem) w tm sm t1 s1 := by
  obtain ⟨hW, hσ, -, hl, hp, hn⟩ := h
  obtain ⟨hst, ht, hE⟩ := hS
  rw [hst] at hW
  exact ⟨⟨hW, rfl, ht, hE⟩, hst, hσ, storeT_wTerm ht, fun hp' => (storeT_not_pre ht hp').elim, fun _ => hE,
    hl, hp, hn⟩

/-- **Wake's `PT1` at `wsideW` is `PT1h` in the store phase.** -/
theorem pt1h_of_pt1 {w : ι} {tm : Memory} {sm : WeakMem.Memory} {t1 : Thread isa} {s1 : TermRun.TTh}
    (h : X64WakeW1.PT1 (wsideW D hcw hem) w tm sm t1 s1) : PT1h D w tm sm t1 s1 ∧ StorePh (D.cw w) s1 := by
  obtain ⟨⟨hW, -, ht, hE⟩, hst, hσ, -, -, -, hl, hp, hn⟩ := h
  have hS : StorePh (D.cw w) s1 := ⟨hst, ht, hE⟩
  refine ⟨⟨?_, hσ, .inr hS, hl, hp, hn⟩, hS⟩
  rw [hst]
  exact hW

/-! ## `Post` at both worker data -/

/-- **`Post` in the store phase holds at wake's worker data**, from its
parts at `PT1h`. -/
theorem post_toW {Q : WakeRel} {D : WSideH Q.ι} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D}
    {Λ : Scc.Sem.Layout} {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
    {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}
    (hP : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hS : StorePh (D.cw w) s1) (hwr : t.2.wr 1 = 0) :
    (relW Q D hcw hem).Post Λ t s := by
  refine ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hP.th, hP.ths, hP.core, ?_, ?_, oc, hP.prot⟩,
    kRmod_of hP.kr (by rw [hP.ths]; rfl), hwr⟩
  · simp only [WakeRel.PTw, ite_true]
    exact ⟨hP.preC, hP.pt0⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, relW]
    exact pt1_of_pt1h hP.pt1 hS

/-- **`Post` at wake's worker data holds at `PT1hE`** (`KRmod.kr`: the
worker in `WiS`). -/
theorem post_ofW {Q : WakeRel} {D : WSideH Q.ι} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D}
    {Λ : Scc.Sem.Layout} (hpt1 : Q.PT1 = X64HelloEmitPh.PT1hE D) (hkrp : KrpW Q D) {t : Cfg} {s : TermRun.Cfg}
    (h : (relW Q D hcw hem).Post Λ t s) : Q.Post Λ t s := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hth, hs, hcore, hp0, hp1, hprot⟩, hkr, hwr⟩ := h
  simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, relW] at hp1
  have hp := pt1h_of_pt1 hp1
  refine ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hth, hs, hcore, hp0, ?_, hprot⟩, hkr.kr hkrp hwr ?_⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false]
    rw [hpt1]
    exact .inl hp.1
  · intro u1 v1 h1 h2
    obtain rfl : u1 = t1 := Option.some.inj (h1.symm.trans (by rw [hth]; rfl))
    obtain rfl : v1 = s1 := Option.some.inj (h2.symm.trans (by rw [hs]; rfl))
    exact hp.1.1

/-- info: 'Spike.Lib.X64HelloW1Store.closed_wiS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closed_wiS

/-- info: 'Spike.Lib.X64HelloW1Store.post_ofW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_ofW

end Spike.Lib.X64HelloW1Store

/-- info: 'Spike.Lib.X64HelloW1Store.storeT_not_pre' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.storeT_not_pre

/-- info: 'Spike.Lib.X64HelloW1Store.storeT_let' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.storeT_let

/-- info: 'Spike.Lib.X64HelloW1Store.storeT_wTerm' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.storeT_wTerm

/-- info: 'Spike.Lib.X64HelloW1Store.envCJ_consD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.envCJ_consD

/-- info: 'Spike.Lib.X64HelloW1Store.envCJ_consW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.envCJ_consW

/-- info: 'Spike.Lib.X64HelloW1Store.localStep_storeT_false'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64HelloW1Store.localStep_storeT_false

/-- info: 'Spike.Lib.X64HelloW1Store.localRun_storeT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.localRun_storeT_eq

/-- info: 'Spike.Lib.X64HelloW1Store.frameRun_storeT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.frameRun_storeT_eq

/-- info: 'Spike.Lib.X64HelloW1Store.outL_wiS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.outL_wiS

/-- info: 'Spike.Lib.X64HelloW1Store.kRmod_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.kRmod_of

/-- info: 'Spike.Lib.X64HelloW1Store.KRmod.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.KRmod.frame

/-- info: 'Spike.Lib.X64HelloW1Store.KRmod.permit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.KRmod.permit

/-- info: 'Spike.Lib.X64HelloW1Store.KRmod.kr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.KRmod.kr

/-- info: 'Spike.Lib.X64HelloW1Store.pt1_of_pt1h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.pt1_of_pt1h

/-- info: 'Spike.Lib.X64HelloW1Store.pt1h_of_pt1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.pt1h_of_pt1

/-- info: 'Spike.Lib.X64HelloW1Store.post_toW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.post_toW
