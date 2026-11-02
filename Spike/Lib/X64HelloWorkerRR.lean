/-
**hello.w's worker side per record** (x86-64; the twin of `Spike/Lib/HelloWorkerRR.lean`): each record's
invariant is `X64HelloWorkerSideX.wi_existsHX`'s at that record's own placement `lbl w`, memory side `ms w` (at
every stack of frames) and frame-aware segment `hseg w` (its entry `P w` and control fact `Z w` parameters here), a
`SegTCSX` segment whose invariant and landings lie in a fragment `X w`.

- `helloDR`: the worker's side (`wi_existsHX` per record; `cw`, `S`, the buffer's `bufL`, `nB`, `mB` given per
  record, `S w := (SR w).S`); `helloDR_entry`, `helloDR_inv`, `helloDR_nn` (`NNH ∧ WideX`), `helloDR_X` (the
  invariant inside `X w`).
- `QIR`: `X64HelloQ.helloQ`'s relation data at `D := helloDR`.
- `hC_IR`: `WCompatH` at `QIR`: `pt1`, `C`, `S` by `rfl`, `ownCov`, `ownDisj`, `pt0` by `X64HelloQ`, `kr` by
  `X64HelloWriteK.krh_frame1`, `wide`, `noSite`, `sysExec`, `sysOkH` by `X64HelloWorkerFields`; open: `cwv` (the
  spawn rows' pointer word) and `pass` (the target store point).

## Differences from the AArch64 version

- `krh_permit`, `WCompatXH` and `hx_IR` (the part of the original that does not read the worker side) are in
  `Spike/Lib/X64HelloWorkerRRC.lean`, same namespace; this module imports it.
- Over x86-64's `NNH`, `AbW` (`X64HelloNN`), `WideX` (`X64WideKeep`), `helloSrc` (`X64HelloSrc`), the kernel
  model `Scc.Sem.X64.abi`, `Inv2Params isa` and `X64WakeM0.MSide`; the cells are `SccCode.helloCells` (AArch64
  `helloProg`). The proofs are the original's.
-/
import Spike.Lib.X64HelloWorkerRRC
import Spike.Lib.X64HelloWorkerSideX
import Spike.Lib.X64HelloWorkerFields

namespace Spike.Lib.X64HelloWorkerRR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.HelloSegThrS (OutTS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64HelloW1 (WSideH WCompatH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64HelloWriteK (KRH krh_frame1)
open Spike.Lib.X64.Flow.Worker (NNH AbW)
open Spike.Lib.X64.WideKeep (WideX)
open Scc.Cert.Rt.X64 (Lays endOf)

/-! ## The worker's side per record -/

section Side

variable {ι : Type} (exe : _root_.Executable) (endPc : Int64) (SR : ι → SpawnRec)
  (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isa)
  (P Z X : ι → FragS isa) (hK : ∀ w fs, (ms w fs).K = some abi)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ Z w s c fs) (X w) helloSrc (lbl w) (ms w) (P w)
    (fun _ _ _ => False))
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)

/-- **The worker's side per record**: `wi_existsHX`'s invariant at each
record's segment. -/
noncomputable def helloDR : WSideH ι where
  lbl := lbl
  ms := ms
  Wi w := Classical.choose (X64HelloWorkerSideX.wi_existsHX (exe := exe) (endPc := endPc) (hK w) (hseg w))
  closed w := (Classical.choose_spec (X64HelloWorkerSideX.wi_existsHX (exe := exe) (endPc := endPc) (hK w)
    (hseg w))).2.2
  cw := cw
  S w := (SR w).S
  bufL := bufL
  nB := nB
  mB := mB

/-- `helloDR`'s invariant holds the segment's entries in `WideX exe`. -/
theorem helloDR_entry (w : ι) (s : State) (c : Ctl) (fs : List TermRun.Frame) (hP : P w s c fs)
    (hW : WideX exe s) : (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB).Wi w s c fs :=
  (Classical.choose_spec (X64HelloWorkerSideX.wi_existsHX (exe := exe) (endPc := endPc) (hK w)
    (hseg w))).1 s c fs hP hW

/-- `helloDR`'s invariant lies inside `NNH ∧ WideX`, with `Z` up to a
pending frame run. -/
theorem helloDR_inv : ∀ w s c fs, (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB).Wi w s c fs →
    NNH exe endPc s ∧ WideX exe s ∧ Pend helloSrc (Z w) s c fs := fun w s c fs h =>
  have h' := (Classical.choose_spec (X64HelloWorkerSideX.wi_existsHX (exe := exe) (endPc := endPc) (hK w)
    (hseg w))).2.1 s c fs h
  ⟨h'.1, h'.2.1, h'.2.2.1⟩

/-- `helloDR`'s invariant lies inside `NNH ∧ WideX` (`X64HelloWorkerFields`'
premise). -/
theorem helloDR_nn : ∀ w s c fs, (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB).Wi w s c fs →
    NNH exe endPc s ∧ WideX exe s :=
  fun w s c fs h => ⟨(helloDR_inv exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB w s c fs h).1,
    (helloDR_inv exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB w s c fs h).2.1⟩

/-- **`helloDR`'s invariant lies inside the landing fragment `X w`.** -/
theorem helloDR_X : ∀ w s c fs, (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB).Wi w s c fs →
    X w s c fs := fun w s c fs h =>
  ((Classical.choose_spec (X64HelloWorkerSideX.wi_existsHX (exe := exe) (endPc := endPc) (hK w)
    (hseg w))).2.1 s c fs h).2.2.2

/-- **The instance's relation at `helloDR`** (`helloQ`'s data, main side
`M`, the target store point `passT`). -/
noncomputable abbrev QIR (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (cT : ι → Loc)
    (cS : ι → WeakMem.Address) (pT : ι → Loc) (Pa : ι → Inv2Params isa) (G : ι → Loc → Val → Prop)
    (passT : State → Prop) (M : X64WakeM0.MSide ι) (r0 r1 : ι → Range) : WakeRel :=
  helloQ arch R1 ι SR cT cS pT Pa G passT M (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB) r0 r1

end Side

/-! ## The compatibility facts -/

section CompatH

variable {ι : Type} (exe : _root_.Executable) (endPc : Int64) (SR : ι → SpawnRec)
  (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isa)
  (P Z X : ι → FragS isa) (hK : ∀ w fs, (ms w fs).K = some abi)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ Z w s c fs) (X w) helloSrc (lbl w) (ms w) (P w)
    (fun _ _ _ => False))
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {r0 r1 : ι → Range}

/-- **`WCompatH`** at `QIR` (see the module doc); open: `cwv`, `pass`, and the sides' owned words covered and
disjoint (`hcov1`, `hdisj`). -/
theorem hC_IR [Kraken.Executable.ValidLayout exe] {kp : Nat} {μ : Marks} {Λ : Scc.Sem.Layout}
    (hl : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    (cwv : ∀ w, (cw w).val = .loc (cS w) 0)
    (pass : X64HelloW1.PassH (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB) passT)
    (hcov1 : ∀ w s fs L v, (L, v) ∈ (ms w fs).own s → (Pa w).cov 1 L)
    (hdisj : ∀ w s0 s fs L v v', (L, v) ∈ (M.ms w).own s0 → (L, v') ∈ (ms w fs).own s → False) :
    WCompatH (QIR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB arch R1 cT cS pT Pa G passT M r0 r1)
      (helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB) μ Λ arch (AbW exe) where
  pt1 := rfl
  C _ := rfl
  cwv := cwv
  S _ := rfl
  pass := pass
  wide := X64HelloWorkerFields.wideH (helloDR_nn exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
  noSite := X64HelloWorkerFields.noSiteH hl hend hμ (helloDR_nn exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
  sysExec := X64HelloWorkerFields.sysExecH (helloDR_nn exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
  sysOkH := X64HelloWorkerFields.sysOkH_of (helloDR_nn exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
  ownCov := X64HelloQ.ownCov hcov1
  ownDisj := X64HelloQ.ownDisj hdisj
  pt0 := X64HelloQ.pt0
  kr w t t' s s' h hw a _ c d hW :=
    ⟨krh_frame1 w t t' s s' h.1 a c (fun _ hx => by simpa only [SrcSem.traceOf, d] using hx),
      X64HelloKRE.lk_wr0 (by rw [a]; exact hw) hW⟩

end CompatH

/-- info: 'Spike.Lib.X64HelloWorkerRR.hC_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hC_IR

/-- info: 'Spike.Lib.X64HelloWorkerRR.helloDR_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms helloDR_X

end Spike.Lib.X64HelloWorkerRR
