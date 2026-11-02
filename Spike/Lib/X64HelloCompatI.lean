/-
**hello.w on x86-64: the compatibility facts at a placed output** (the twin of `Spike/Lib/HelloCompatI.lean`):
at the runtime layout `L := RuntimeLayout.ofPlaceWX hp i` of a placed output whose cells are hello's (`ho`), the
loader's parse `hpa` (the trust boundary) and the canonical target's marks `μP`.

- `site_ofH`: a site label of the layout resolves in `L.exe` to its `codeLabel` address.
- `hello_hμP`: the marks' sites are the sites' labels in `L.exe` (`hμ` of `X64HelloWorkerRR.hC_IR`).
- `hoffP`: `helloM`'s `hoff` at `μP` (`X64HelloMainInv.hoff_ofPlaceW` through `AbOffW.marks_target`).
- `hC_IP`: `X64HelloWorkerRR.hC_IR` at `L.exe` (`Lays` from `L.lays`, `hμ` by `hello_hμP`); open as there
  (`cwv`, `pass`).
- `hC0P`: `X64HelloCompat0.hC0H` at `L`, `μP`, main's side `helloM … L.lab L.exe L.Λ μP (hoffP …)`: `noSite0`
  by `X64AbOffL.noSite_of_A_ofPlaceOK`, `abortAt0` from the memory side's abort sites the program's (`habt`, at
  `PhRec.μ L`); the memory side's other facts open (see `hC0H`).

**Where this differs from AArch64** (forced by the x86-64 shape): the placed output is a `PlaceWX` and its layout
`RuntimeLayout.ofPlaceWX`; the text is an `Scc.Sem.X64.Asm` whose cells are the output's (`cellsOf asm = some
o.prog`; AArch64: `textProgram asm = .ok o.prog`) and hello's are the byte-sized cells `SccCode.helloCells`
(AArch64: `helloProg`). The sites' labels resolve by `PlaceWX`'s phase check A6 (`sitesBy` over
`siteLabels`, as `PlaceWX.site_ofPlaceWX` for the take site), so `site_ofH` takes a member of `siteLabels`
(AArch64: a label of `helloProg`, and `hello_siteLabels`/`mem_of_anyH` decide the two sites are labels; not
needed here). The memory side's architecture is `Arch.tso` (AArch64: `Arch.armv8`).
-/
import Spike.Lib.X64HelloCompat0
import Spike.Lib.X64HelloWorkerRR
import Spike.Lib.X64WakeAbOffW
import Spike.Lib.X64SiteOfPlaceW

namespace Spike.Lib.X64HelloCompatI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloMainInv (helloM)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Scc.Cert.Rt.X64 (Lays endOf)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {H : Scc.Sem.Hooks isa} {E : Scc.Sem.Entry} {asm : Scc.Sem.X64.Asm}

/-- The canonical target's marks at the placed layout. -/
noncomputable abbrev μP (H : Scc.Sem.Hooks isa) (E : Scc.Sem.Entry) (asm : Scc.Sem.X64.Asm) : Marks :=
  (Scc.Sem.X64.target H E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ

/-- **A site label resolves to its loaded address**: A6 resolves every label of `siteLabels`, and the loaded
label there is its `codeLabel` address (`PlaceWX.lab_toNat`). -/
theorem site_ofH {l : String} (hl : l ∈ Scc.Cert.Rt.X64.siteLabels Λ0) :
    codeLabel Λ0.code.lo o.prog l =
      some ((RuntimeLayout.ofPlaceWX hp i).lab l).toBitVec.toNat := by
  have h6 := hp.a6
  simp only [Scc.Cert.PlaceOK.X64.a6, Bool.and_eq_true] at h6
  have h6 := h6.1
  unfold Scc.Cert.Rt.X64.phasesOk Scc.Cert.Rt.X64.phasesOkBy at h6
  rw [Scc.Cert.Rt.X64.codeT_eq] at h6
  split at h6
  · next T ss hT hs =>
    unfold Scc.Cert.Rt.X64.sitesBy at hs
    obtain ⟨a, ha⟩ := PlaceWX.codeLabel_of_mapM hs _ hl
    rw [ha, PlaceWX.lab_toNat hp i ha]
  · cases h6

/-- **The marks' transfer sites are hello's site labels in `L.exe`** (`hC_IR`'s `hμ`). -/
theorem hello_hμP (hpa : Scc.Sem.X64.cellsOf asm = some o.prog) :
    (μP hp i H E asm).site .take =
        some ((_root_.Executable.labels (RuntimeLayout.ofPlaceWX hp i).exe).label
          Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      (μP hp i H E asm).site .release =
        some ((_root_.Executable.labels (RuntimeLayout.ofPlaceWX hp i).exe).label
          Scc.Lower.Names.releaseSite).toBitVec.toNat := by
  rw [μP, Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target _ hpa]
  exact ⟨site_ofH hp i (by simp [Scc.Cert.Rt.X64.siteLabels, XferKind.label]),
    site_ofH hp i (by simp [Scc.Cert.Rt.X64.siteLabels, XferKind.label])⟩

/-- **`helloM`'s `hoff` at the target's marks.** -/
theorem hoffP (hpa : Scc.Sem.X64.cellsOf asm = some o.prog) :
    ∀ s c, Spike.Lib.X64WakeOff.AbOffA (RuntimeLayout.ofPlaceWX hp i).lab s c →
      ∀ k a, (μP hp i H E asm).abortAt k = some a → pcOf s ≠ a := by
  intro s c h
  rw [μP, Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target _ hpa]
  exact X64HelloMainInv.hoff_ofPlaceW hp i s c h

section Worker

variable {ι : Type} (endPc : Int64) (SR : ι → SpawnRec)
  (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isa)
  (P Z X : ι → FragS isa) (hK : ∀ w fs, (ms w fs).K = some abi)
  (hseg : ∀ w, HelloSegTCSX.SegTCSX
    (fun s c fs => Spike.Lib.X64.Flow.Worker.NNH (RuntimeLayout.ofPlaceWX hp i).exe endPc s ∧ Z w s c fs) (X w)
    X64HelloSrc.helloSrc (lbl w) (ms w) (P w) (fun _ _ _ => False))
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {r0 r1 : ι → Range}

/-- **`WCompatH` at the placed layout** (`hC_IR` with `Lays` and `hμ` discharged); open: `cwv`, `pass`, `hcov1`,
`hdisj`. -/
theorem hC_IP (ho : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hend : endPc = endOf (RuntimeLayout.ofPlaceWX hp i).exe SccCode.helloCells (RuntimeLayout.ofPlaceWX hp i).pfx)
    (cwv : ∀ w, (cw w).val = .loc (cS w) 0)
    (pass : X64HelloW1.PassH
      (X64HelloWorkerRR.helloDR (RuntimeLayout.ofPlaceWX hp i).exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
      passT)
    (hcov1 : ∀ w s fs L v, (L, v) ∈ (ms w fs).own s → (Pa w).cov 1 L)
    (hdisj : ∀ w s0 s fs L v v', (L, v) ∈ (M.ms w).own s0 → (L, v') ∈ (ms w fs).own s → False) :
    X64HelloW1.WCompatH
      (X64HelloWorkerRR.QIR (RuntimeLayout.ofPlaceWX hp i).exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB arch R1
        cT cS pT Pa G passT M r0 r1)
      (X64HelloWorkerRR.helloDR (RuntimeLayout.ofPlaceWX hp i).exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
      (μP hp i H E asm) (RuntimeLayout.ofPlaceWX hp i).Λ arch
      (Spike.Lib.X64.Flow.Worker.AbW (RuntimeLayout.ofPlaceWX hp i).exe) :=
  haveI := (RuntimeLayout.ofPlaceWX hp i).valid
  X64HelloWorkerRR.hC_IR (RuntimeLayout.ofPlaceWX hp i).exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB
    (by rw [← ho]; exact (RuntimeLayout.ofPlaceWX hp i).lays) hend (hello_hμP hp i hpa) cwv pass hcov1 hdisj

end Worker

section Main

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {D : WSideH ι} {r0 r1 : ι → Range}
  {ms : ι → MemSide isa} {cw : ι → TermRun.Word}

/-- **`WCompat0` at the placed layout and the target's marks**, main's side `helloM` at the records' placement,
`L.lab`, `L.exe`, `L.Λ`, `μP` (see the module doc). -/
theorem hC0P (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    /- the memory side -/
    (hK : ∀ w, (ms w).K = some abi) (hG : ∀ w, (ms w).G = G w)
    (hconst : ∀ w s s', (ms w).own s' = (ms w).own s)
    (hmp : ∀ w s L v, (L, v) ∈ (ms w).own s → ¬ (ms w).mp L true)
    (hcov : ∀ w s L v, (L, v) ∈ (ms w).own s → (Pa w).cov 0 L)
    (hmpW : ∀ w L, (ms w).mp L true →
      (Pa w).foot 0 L ∧ ¬ InLabel (SR w).lbl (SR w).lsize L ∧
        Consumer1.LocIn (RuntimeLayout.ofPlaceWX hp i).Λ.shared L)
    (hrt : ∀ w a, (ms w).rt a → ¬ ∃ l b, (SR w).lbl l = some b ∧ b ≤ a ∧ a < b + 8 * (SR w).lsize l)
    (hrdN : ∀ w (w' : TermRun.Word) n, w'.val = .num n → (ms w).rd w')
    (habt : ∀ w s, (ms w).abortAt s →
      ∃ k a, (Spike.Lib.X64.PhRec.μ (RuntimeLayout.ofPlaceWX hp i)).abortAt k = some a ∧ pcOf s = a)
    /- main's pointer word; the certified no-promise fact -/
    (hcw : ∀ w, (cw w).val = .loc (cS w) 0)
    (hnp : ∀ w x (t : Thread isa) mem, (Pa w).noProm t.st →
      CertOkC Arch.tso (certSem abi Arch.tso (μP hp i H E asm) x 0) 0 t mem → t.prom = []) :
    X64WakeM0.WCompat0
      (helloQ arch R1 ι SR cT cS pT Pa G passT
        (helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) ms cw (RuntimeLayout.ofPlaceWX hp i).lab
          (RuntimeLayout.ofPlaceWX hp i).exe (RuntimeLayout.ofPlaceWX hp i).Λ (μP hp i H E asm) (hoffP hp i hpa))
        D r0 r1)
      (helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) ms cw (RuntimeLayout.ofPlaceWX hp i).lab
        (RuntimeLayout.ofPlaceWX hp i).exe (RuntimeLayout.ofPlaceWX hp i).Λ (μP hp i H E asm) (hoffP hp i hpa))
      (μP hp i H E asm) (RuntimeLayout.ofPlaceWX hp i).Λ := by
  haveI := (RuntimeLayout.ofPlaceWX hp i).valid
  have hm : μP hp i H E asm = Spike.Lib.X64.PhRec.μ (RuntimeLayout.ofPlaceWX hp i) :=
    Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target _ hpa
  refine X64HelloCompat0.hC0H (fun _ => rfl) hK hG hconst hmp hcov hmpW hrt hrdN (by rw [hm]; exact habt)
    (by rw [hm]; exact fun s c h => Spike.Lib.X64AbOffL.noSite_of_A_ofPlaceOK hp i h) hcw hnp

end Main

end Place

end Spike.Lib.X64HelloCompatI

/-- info: 'Spike.Lib.X64HelloCompatI.hello_hμP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCompatI.hello_hμP

/-- info: 'Spike.Lib.X64HelloCompatI.hC_IP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCompatI.hC_IP

/-- info: 'Spike.Lib.X64HelloCompatI.hC0P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCompatI.hC0P
