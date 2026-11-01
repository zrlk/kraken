/-
**hello.w's worker side per record** (the twin of `Spike.Lib.WakeWorkerR`
at hello's frame-aware worker side `HelloW1.WSideH`, AArch64): each
record's invariant is `HelloWorkerSide.wi_existsH`'s at that record's own
placement `lbl w`, memory side `ms w` (at every stack of frames) and
frame-aware segment `hseg w` (`seg_wcWorkerS`, its entry `P w` and
control fact `Z w` parameters here), a `SegTCSX` segment whose invariant and
landings lie in a fragment `X w` (`HelloWorkerSideX.wi_existsHX`; a plain
`SegTCS` segment at `X := True` by `SegTCSX.ofS`).

- `helloDR`: the worker's side (`wi_existsHX` per record; `cw`, `S`, the
  buffer's `bufL`, `nB`, `mB` given per record, `S w := (SR w).S`);
  `helloDR_entry`, `helloDR_inv`, `helloDR_nn` (`NNH ∧ WideX`), `helloDR_X`
  (the invariant inside `X w`).
- `QIR`: `HelloQ.helloQ`'s relation data at `D := helloDR`.
- `krh_permit`: `WCompatX.krp`'s congruence at `KRH` (the twin of
  `WakeKR.kr_permit`).
- `WCompatXH`, `hx_IR`: wake's `WCompatX` over `WSideH` (its fields do not
  read the worker side), closed at `QIR` but for `Gc` (the flag store's
  value at `cT`, a premise as in `WakeAssembly.wCompatX_of`).
- `hC_IR`: `WCompatH` at `QIR`: `pt1`, `C`, `S` by `rfl`, `ownCov`,
  `ownDisj`, `pt0` by `HelloQ`, `kr` by `A64HelloWriteK.krh_frame1`, `wide`,
  `noSite`, `sysExec`, `sysOkH` by `HelloWorkerFields`; open: `cwv`
  (the spawn rows' pointer word) and `pass` (the target store point).
-/
import Spike.Lib.HelloQ
import Spike.Lib.HelloWorkerSideX
import Spike.Lib.HelloWorkerFields
import Spike.Lib.WakeKRP

namespace Spike.Lib.HelloWorkerRR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegThrS (OutTS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.HelloW1 (WSideH WCompatH)
open Spike.Lib.HelloQ (helloQ)
open Spike.Lib.A64HelloWriteK (KRH krh_frame1)
open Spike.Lib.A64.Flow.Worker (NNH AbW)
open Spike.Lib.A64.WideKeep (WideX)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

/-! ## The worker's side per record -/

section Side

variable {ι : Type} (exe : _root_.Executable) (endPc : Int64) (SR : ι → SpawnRec)
  (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isaLSE2)
  (P Z X : ι → FragS isaLSE2) (hK : ∀ w fs, (ms w fs).K = some abi)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ Z w s c fs) (X w) helloSrc (lbl w) (ms w) (P w)
    (fun _ _ _ => False))
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)

/-- **The worker's side per record**: `wi_existsH`'s invariant at each
record's segment. -/
noncomputable def helloDR : WSideH ι where
  lbl := lbl
  ms := ms
  Wi w := Classical.choose (HelloWorkerSideX.wi_existsHX (exe := exe) (endPc := endPc) (hK w) (hseg w))
  closed w := (Classical.choose_spec (HelloWorkerSideX.wi_existsHX (exe := exe) (endPc := endPc) (hK w) (hseg w))).2.2
  cw := cw
  S w := (SR w).S
  bufL := bufL
  nB := nB
  mB := mB

/-- `helloDR`'s invariant holds the segment's entries in `WideX exe`. -/
theorem helloDR_entry (w : ι) (s : State) (c : Ctl) (fs : List TermRun.Frame) (hP : P w s c fs)
    (hW : WideX exe s) : (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB).Wi w s c fs :=
  (Classical.choose_spec (HelloWorkerSideX.wi_existsHX (exe := exe) (endPc := endPc) (hK w) (hseg w))).1 s c fs hP hW

/-- `helloDR`'s invariant lies inside `NNH ∧ WideX`, with `Z` up to a
pending frame run. -/
theorem helloDR_inv : ∀ w s c fs, (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB).Wi w s c fs →
    NNH exe endPc s ∧ WideX exe s ∧ Pend helloSrc (Z w) s c fs := fun w s c fs h =>
  have h' := (Classical.choose_spec (HelloWorkerSideX.wi_existsHX (exe := exe) (endPc := endPc) (hK w)
    (hseg w))).2.1 s c fs h
  ⟨h'.1, h'.2.1, h'.2.2.1⟩

/-- `helloDR`'s invariant lies inside `NNH ∧ WideX` (`HelloWorkerFields`'
premise). -/
theorem helloDR_nn : ∀ w s c fs, (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB).Wi w s c fs →
    NNH exe endPc s ∧ WideX exe s :=
  fun w s c fs h => ⟨(helloDR_inv exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB w s c fs h).1,
    (helloDR_inv exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB w s c fs h).2.1⟩

/-- **`helloDR`'s invariant lies inside the landing fragment `X w`.** -/
theorem helloDR_X : ∀ w s c fs, (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB).Wi w s c fs →
    X w s c fs := fun w s c fs h =>
  ((Classical.choose_spec (HelloWorkerSideX.wi_existsHX (exe := exe) (endPc := endPc) (hK w)
    (hseg w))).2.1 s c fs h).2.2.2

/-- **The instance's relation at `helloDR`** (`helloQ`'s data, main side
`M`, the target store point `passT`). -/
noncomputable abbrev QIR (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (cT : ι → Loc)
    (cS : ι → WeakMem.Address) (pT : ι → Loc) (Pa : ι → Inv2Params isaLSE2) (G : ι → Loc → Val → Prop)
    (passT : State → Prop) (M : WakeM0.MSide ι) (r0 r1 : ι → Range) : WakeRel :=
  helloQ arch R1 ι SR cT cS pT Pa G passT M (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB) r0 r1

end Side

/-! ## The compatibility facts -/

/-- **`WCompatX.krp` at `KRH`**: the kernel relation is stable under a
worker step that keeps the kernel state, main's target thread and the
source trace and sets main's source permit. -/
theorem krh_permit {ι : Type} {r0 r1 : ι → Range} :
    ∀ w (t t' : Cfg) (s s' : TermRun.Cfg) (s0 : TermRun.TTh) (p : Option Nat), KRH r0 r1 w t s → t'.2 = t.2 →
      t'.1.threads[0]? = t.1.threads[0]? → s.ths[0]? = some s0 → s'.ths[0]? = some { s0 with permit := p } →
      SrcSem.traceOf s' = SrcSem.traceOf s → KRH r0 r1 w t' s' := by
  intro w t t' s s' s0 p ⟨hn, h0, h1, hh, hm, htr⟩ ht _ hs0 hs0' hs'
  rw [KRH, ht]
  exact ⟨hn, h0, h1, hh, fun hx s0' h => by rw [hs0'] at h; cases h; exact hm hx s0 hs0, hs' ▸ htr⟩

/-- **The worker's compatibility facts after the `WCompat` freeze, over
`WSideH`**: `WakeW1.WCompatX`'s fields (none reads the worker side). -/
structure WCompatXH (Q : WakeRel) (D : WSideH Q.ι) : Prop where
  /-- The worker's flag store value `1` is a `G` value at `cT`. -/
  Gc : ∀ w, Q.G w (Q.C w).cT 1
  /-- The worker owns no word after the spawn. -/
  own1 : ∀ w s, Q.own w 1 s [] = []
  /-- main's source thread has no promise after the spawn. -/
  sp0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.promises = []
  /-- main's per-thread relation is stable under a worker step that also
  sets main's source permit. -/
  pt0p : ∀ w tm sm t0 s0 tm' sm' (p : Option Nat), Q.PT0 w tm sm t0 s0 →
    WakeW1.W1Mem (Q.P w) (Q.C w).cS tm sm tm' sm' → Q.PT0 w tm' sm' t0 { s0 with permit := p }
  /-- The kernel relation is stable under a worker step, with no byte of the
  worker's `write` out, that keeps the kernel state, main's target thread and
  the source trace and sets main's source permit, the worker after it in
  `Wi` (`Lk`'s reverse conjunct). -/
  krp : ∀ w t t' s s' (s0 : TermRun.TTh) (p : Option Nat), Q.KR w t s → t.2.wr 1 = 0 → t'.2 = t.2 →
    t'.1.threads[0]? = t.1.threads[0]? → s.ths[0]? = some s0 → s'.ths[0]? = some { s0 with permit := p } →
    s'.trace = s.trace →
    (∀ t1 s1, t'.1.threads[1]? = some t1 → s'.ths[1]? = some s1 → D.Wi w t1.st (Ctl.of s1) s1.stack) →
    Q.KR w t' s'

section Compat

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}

/-- **`WCompatXH`** at `helloQ` (any worker side); open: `Gc`. -/
theorem hx_IR (Gc : ∀ w, G w (cT w) 1) :
    WCompatXH (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) D where
  Gc := Gc
  own1 _ _ := rfl
  sp0 _ tm sm _ _ h := WakeM0.PT0.promises_nil (tm := tm) (sm := sm) h
  pt0p _ tm sm _ _ tm' sm' p h _ := WakeM0.pt0_permit (tm := tm) (sm := sm) (tm' := tm') (sm' := sm') p h
  krp w t t' s s' s0 p h hw a b c d e hW :=
    ⟨krh_permit w t t' s s' s0 p h.1 a b c d (by simp only [SrcSem.traceOf, e]),
      HelloKRE.lk_wr0 (by rw [a]; exact hw) hW⟩

end Compat

section CompatH

variable {ι : Type} (exe : _root_.Executable) (endPc : Int64) (SR : ι → SpawnRec)
  (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isaLSE2)
  (P Z X : ι → FragS isaLSE2) (hK : ∀ w fs, (ms w fs).K = some abi)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ Z w s c fs) (X w) helloSrc (lbl w) (ms w) (P w)
    (fun _ _ _ => False))
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {r0 r1 : ι → Range}

/-- **`WCompatH`** at `QIR` (see the module doc); open: `cwv`, `pass`. -/
theorem hC_IR [Kraken.Executable.ValidLayout exe] {kp : Nat} {μ : Marks} {Λ : Scc.Sem.Layout}
    (hl : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    /- (the spawn rows) OPEN -/ (cwv : ∀ w, (cw w).val = .loc (cS w) 0)
    /- OPEN -/
    (pass : HelloW1.PassH (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB) passT) :
    WCompatH (QIR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB arch R1 cT cS pT Pa G passT M r0 r1)
      (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB) μ Λ arch (AbW exe) where
  pt1 := rfl
  C _ := rfl
  cwv := cwv
  S _ := rfl
  pass := pass
  wide := HelloWorkerFields.wideH (helloDR_nn exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
  noSite := HelloWorkerFields.noSiteH hl hend hμ (helloDR_nn exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
  sysExec := HelloWorkerFields.sysExecH (helloDR_nn exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
  sysOkH := HelloWorkerFields.sysOkH_of (helloDR_nn exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
  ownCov := HelloQ.ownCov
  ownDisj := HelloQ.ownDisj
  pt0 := HelloQ.pt0
  kr w t t' s s' h hw a _ c d hW :=
    ⟨krh_frame1 w t t' s s' h.1 a c (fun _ hx => by simpa only [SrcSem.traceOf, d] using hx),
      HelloKRE.lk_wr0 (by rw [a]; exact hw) hW⟩

end CompatH

/-- info: 'Spike.Lib.HelloWorkerRR.hC_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hC_IR

/-- info: 'Spike.Lib.HelloWorkerRR.hx_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hx_IR

end Spike.Lib.HelloWorkerRR
