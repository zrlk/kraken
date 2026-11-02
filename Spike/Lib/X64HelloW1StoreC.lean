/-
**Wake's compatibility facts for the store phase** (C4, relation half; the bridge in
`Spike/Lib/X64HelloW1Store.lean`, hello's facts in
`Spike/Lib/X64HelloW1Print.lean`): `X64WakeW1.WCompat` at `relW`/`wsideW`, from
hello's `WCompatH` and the facts it does not state.

- `sysOkH_of_sysOk`: wake's system-call judgement (no `write`, no
  `exit_group` but `exit`) implies hello's (`WCompatH.sysOkH`'s disjunction).
- `sysOk_of_sysOkH`: back, at a state at no `write(1, …)` (`NoWrite`) and
  outside the abort-write phase `AbW`.
- `WStoreX Q D AbW`: the facts `X64WakeW1.WCompat` needs that `WCompatH` does
  not state, at depth `0` and the store-phase invariant `WiS`; each field
  names its owner.
- `wcompat_relW`: `WCompatH` and `WStoreX` give `X64WakeW1.WCompat` at `relW`.

x86-64 twin of `Spike/Lib/HelloW1StoreC.lean` (same names, namespaces with the `X64` prefix).

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only
live constants): `sysOkH_of_sysOk`.
-/
import Spike.Lib.X64HelloW1Store

namespace Spike.Lib.X64HelloW1Store

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core
open Spike.Lib.X64HelloW1 (WSideH PT1h WCompatH)
open Spike.Lib.X64WakeW1 (W1Mem)

/-! ## The two system-call judgements -/

/-- **Hello's system-call judgement is wake's** at a call that is no
`write(1, …)`, outside the abort-write phase. -/
theorem sysOk_of_sysOkH {AbW : isa.State → Prop} {s : isa.State} {call : Call}
    (h : call = .exit ∨ (∃ buf n, call = .write 1 buf n) ∨
      (AbW s ∧ ((∃ buf n, call = .write 2 buf n) ∨ call = .exitGroup abortStatus)) ∨
      ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v))
    (hw : ∀ buf n, call ≠ .write 1 buf n) (ha : ¬ AbW s) :
    call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v) := by
  rcases h with h | ⟨buf, n, h⟩ | ⟨h, -⟩ | h
  · exact .inl h
  · exact (hw buf n h).elim
  · exact (ha h).elim
  · exact .inr h

/-! ## The facts `WCompatH` does not state -/

/-- **The store phase's compatibility facts beyond `WCompatH`**, per ghost
record `w`, at depth `0` and the store-phase invariant `WiS`; each field
names its owner (as `X64WakeW1.WCompat`'s field of the same name). -/
structure WStoreX (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout)
    (AbW : isa.State → Prop) : Prop where
  /-- The unpark and exit rows' relation data are wake's. -/
  atUnpk : Q.atUnpk = X64WakeW1.atUnpk
  atTexit : Q.atTexit = X64WakeW1.atTexit
  /-- The rows' placement is the spawn's. -/
  lbl : ∀ w, D.lbl w = (Q.SR w).lbl
  /-- The depth-`0` rows' kernel model is the machine's. -/
  K : ∀ w, (D.ms w []).K = some abi
  /-- The depth-`0` rows' runtime invariant is the relation's. -/
  G : ∀ w, (D.ms w []).G = Q.G w
  /-- The depth-`0` rows' owned words are the worker's. -/
  own : ∀ w s, (D.ms w []).own s = Q.own w 1 s []
  /-- A word the worker may write as the runtime's at depth `0`
  is in its footprint, outside every placed label, in a shared region. -/
  mpW : ∀ w L, (D.ms w []).mp L true →
    (Q.P w).foot 1 L ∧ ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize L ∧ Consumer1.LocIn Λ.shared L
  /-- (with `NoWrite`) The store phase is outside the abort-write
  phase. -/
  noAbW : ∀ w s c, WiS D w s c → ¬ AbW s
  /-- The store phase's instructions keep the worker's owned words ... -/
  ownInstr : ∀ w s c tree, WiS D w s c → abi.atSys s = false → isa.exec s = some tree →
    Consumer1.OwnTree (fun s => Q.own w 1 s []) (Q.own w 1 s []) tree
  /-- ... and so do its system calls' returns. -/
  ownSys : ∀ w s c call, WiS D w s c → abi.atSys s = true → decode abi.nrs (abi.nr s) (abi.arg s) = some call →
    ∀ s' ∈ certSuccs abi s call, Q.own w 1 s' [] = Q.own w 1 s []
  /-- `X64WakeW1.WCompat.cT`, `cTin`, `cTfoot`, `cSfrz`. -/
  cT : ∀ w, ∃ a, (Q.C w).cT = wordLoc a ∧ wordAddr (Q.SR w).lbl (Q.C w).cS = some a ∧
    (Q.C w).cS.offset < (Q.SR w).lsize (Q.C w).cS.label
  cTin : ∀ w, Consumer1.LocIn Λ.shared (Q.C w).cT
  cTfoot : ∀ w, (Q.P w).foot 1 (Q.C w).cT
  cSfrz : ∀ w, ¬ (Q.P w).frzS (Q.C w).cS
  /-- The source memory is not empty at the spawn. -/
  Spos : ∀ w, 0 < (Q.SR w).S
  /-- The worker's footprint meets the placed labels only at `cT`. -/
  footLab : ∀ w L, (Q.P w).foot 1 L → InLabel (Q.SR w).lbl (Q.SR w).lsize L → L = (Q.C w).cT
  /-- A certified worker at a no-promise state has no promise. -/
  noProm : ∀ w x (t : Thread isa) mem, (Q.P w).noProm t.st →
    CertOkC Arch.tso (certSem abi Arch.tso μ x 1) 1 t mem → t.prom = []
  /-- main has not returned while the process runs (at `Q`'s `Post`,
  which `relW`'s implies, `post_ofW`) ... -/
  mainLive : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = []
  /-- ... and main's source thread id is its own. -/
  tid0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.tidLbl = some (X64WakeT1.mainTidLbl 2)

/-! ## Wake's facts at `relW` -/

/-- **Wake's compatibility facts at `relW`**: from hello's (`WCompatH`), the
store phase's further facts (`WStoreX`) and `NoWrite`. `sysOk` is
`sysOk_of_sysOkH` (no `write(1, …)` by `NoWrite`, no abort write by
`WStoreX.noAbW`); `pass`, `wide`, `noSite`, `sysExec`, `ownCov`, `ownDisj`
are `WCompatH`'s at depth `0`. -/
theorem wcompat_relW {Q : WakeRel} {D : WSideH Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
    {AbW : isa.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D}
    (hH : WCompatH Q D μ Λ arch AbW) (hX : WStoreX Q D μ Λ AbW) (hkrp : KrpW Q D) :
    X64WakeW1.WCompat (relW Q D hcw hem) (wsideW D hcw hem) μ Λ arch where
  pt1 := rfl
  atUnpk := hX.atUnpk
  atTexit := hX.atTexit
  lbl := hX.lbl
  K := hX.K
  G := hX.G
  own := hX.own
  mpW := hX.mpW
  wide w s c h := hH.wide w s c [] h.1
  noSite w s c h := hH.noSite w s c [] h.1
  sysExec w s c t h := hH.sysExec w s c [] t h.1
  sysOk w s c call h ha hd :=
    sysOk_of_sysOkH (hH.sysOkH w s c [] call h.1 ha hd)
      (fun buf n he => hem w s c h abi buf n (hX.K w) ha (hd.trans (congrArg some he)))
      (hX.noAbW w s c h)
  ownInstr := hX.ownInstr
  ownSys := hX.ownSys
  ownCov w s := hH.ownCov w s []
  ownDisj w s0 fs s := hH.ownDisj w s0 fs s []
  C := hH.C
  cwv := hH.cwv
  S := hH.S
  cT := hX.cT
  cTin := hX.cTin
  cTfoot := hX.cTfoot
  cSfrz := hX.cSfrz
  Spos := hX.Spos
  footLab := hX.footLab
  pass w s c h := by
    obtain ⟨hW, hh, hS, hE⟩ := h
    have hc : Ctl.of { term := c.term, env := c.env } = c := X64HelloW1.ctl_of_set {term := c.term, env := c.env} hh
    have := hH.pass w s { term := c.term, env := c.env } (by rw [hc]; exact hW) (.inr ⟨rfl, hS, hE⟩)
    simp only [WPass, true_and] at this
    exact this
  noProm := hX.noProm
  mainLive t s h := hX.mainLive t s (post_ofW hH.pt1 hkrp h)
  tid0 := hX.tid0
  pt0 := hH.pt0
  kr w t t' s s' h a b c d := ⟨h.1.frame a b c d, by rw [a]; exact h.2⟩

/-- info: 'Spike.Lib.X64HelloW1Store.wcompat_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wcompat_relW

end Spike.Lib.X64HelloW1Store

/-- info: 'Spike.Lib.X64HelloW1Store.sysOk_of_sysOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.sysOk_of_sysOkH
