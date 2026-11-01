/-
**hello.w on AArch64: the compatibility facts at a placed output** (the twin
of `Spike.Lib.WakeCompatI` and of `WakeAssemblyR.hC0R` for hello's
listing): at the runtime layout `L := RuntimeLayout.ofPlaceW hp i` of a
placed output whose program is hello's (`ho`), the loader's parse `hpa`
(the trust boundary) and the canonical target's marks `μP`.

- `hello_siteLabels`: both transfer sites are labels of `helloProg`.
- `hello_hμP`: the marks' sites are the sites' labels in `L.exe` (`hμ` of
  `HelloWorkerRR.hC_IR`; the twin of `WorkerSide.wake_hμ`).
- `hoffP`: `helloM`'s `hoff` at `μP` (`HelloMainInv.hoff_ofPlaceW` through
  `AbOffW.marks_target`).
- `hC_IP`, `hx_IP`: `HelloWorkerRR.hC_IR` / `hx_IR` at `L.exe` (`Lays` from
  `L.lays`, `hμ` by `hello_hμP`); open as there (`cwv`, `pass`; `Gc`).
- `hC0P`: `HelloCompat0.hC0H` at `L`, `μP`, main's side
  `helloM … L.lab L.exe L.Λ μP (hoffP …)`: `noSite0` by
  `A64AbOffL.noSite_of_A_ofPlaceOK`, `abortAt0` from the memory side's abort
  sites the program's (`habt`, at `PhRec.μ L`); the memory side's other facts
  open (see `hC0H`).
-/
import Spike.Lib.HelloCompat0
import Spike.Lib.HelloWorkerRR
import Spike.Lib.A64WakeAbOffW
import Spike.Lib.PlaceWRt

namespace Spike.Lib.HelloCompatI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.HelloMainInv (helloM)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

/-- A label the program has (by `labelName`) is a cell of it. -/
theorem mem_of_anyH {l : String} {prog : Program}
    (h : prog.any (fun d => Scc.Sem.A64.labelName d == some l) = true) : Directive.label l ∈ prog := by
  obtain ⟨d, hd, he⟩ := List.any_eq_true.mp h
  have : d = .label l := by cases d <;> simp_all [Scc.Sem.A64.labelName]
  exact this ▸ hd

/-- **Both transfer sites are labels of hello's program.** -/
theorem hello_siteLabels : Directive.label "scc_rt_take_site" ∈ helloProg ∧
    Directive.label "scc_rt_release_site" ∈ helloProg :=
  have h : helloProg.any (fun d => Scc.Sem.A64.labelName d == some "scc_rt_take_site") = true ∧
      helloProg.any (fun d => Scc.Sem.A64.labelName d == some "scc_rt_release_site") = true := by decide +kernel
  ⟨mem_of_anyH h.1, mem_of_anyH h.2⟩

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} {asm : String}

/-- The canonical target's marks at the placed layout. -/
noncomputable abbrev μP (H : Scc.Sem.Hooks isaLSE2) (E : Scc.Sem.Entry) (asm : String) : Marks :=
  (Scc.Sem.A64.target H E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ

/-- A label of hello's program resolves, in `L.exe`, to its `codeOf`
address: the site of `PhRec.μ L` at it. -/
theorem site_ofH (ho : o.prog = helloProg) {l : String} (hin : Directive.label l ∈ helloProg) :
    Scc.Cert.Link.A64.codeOf (RuntimeLayout.ofPlaceW hp i).Λ.code.lo o.prog l =
      some ((_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label l).toBitVec.toNat := by
  cases ha : Scc.Cert.Link.A64.codeOf (RuntimeLayout.ofPlaceW hp i).Λ.code.lo o.prog l with
  | none => exact absurd rfl (Scc.Cert.Link.A64.ne_label_of_codeOf ha _ (ho ▸ hin))
  | some a => rw [PlaceW.lab_toNat hp i ha]

/-- **The marks' transfer sites are hello's site labels in `L.exe`**
(`hC_IR`'s `hμ`). -/
theorem hello_hμP (ho : o.prog = helloProg) (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog) :
    (μP hp i H E asm).site .take =
        some ((_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
          Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      (μP hp i H E asm).site .release =
        some ((_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
          Scc.Lower.Names.releaseSite).toBitVec.toNat := by
  rw [μP, Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target _ hpa]
  exact ⟨site_ofH hp i ho hello_siteLabels.1, site_ofH hp i ho hello_siteLabels.2⟩

/-- **`helloM`'s `hoff` at the target's marks.** -/
theorem hoffP (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog) :
    ∀ s c, Spike.Lib.A64WakeOff.AbOffA (RuntimeLayout.ofPlaceW hp i).lab s c →
      ∀ k a, (μP hp i H E asm).abortAt k = some a → pcOf s ≠ a := by
  intro s c h
  rw [μP, Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target _ hpa]
  exact HelloMainInv.hoff_ofPlaceW hp i s c h

section Worker

variable {ι : Type} (endPc : Int64) (SR : ι → SpawnRec)
  (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isaLSE2)
  (P Z X : ι → FragS isaLSE2) (hK : ∀ w fs, (ms w fs).K = some abi)
  (hseg : ∀ w, HelloSegTCSX.SegTCSX
    (fun s c fs => Spike.Lib.A64.Flow.Worker.NNH (RuntimeLayout.ofPlaceW hp i).exe endPc s ∧ Z w s c fs) (X w)
    HelloSrc.helloSrc (lbl w) (ms w) (P w) (fun _ _ _ => False))
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {r0 r1 : ι → Range}

/-- **`WCompatH` at the placed layout** (`hC_IR` with `Lays` and `hμ`
discharged); open: `cwv`, `pass`. -/
theorem hC_IP (ho : o.prog = helloProg) (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hend : endPc = endOf (RuntimeLayout.ofPlaceW hp i).exe helloProg (RuntimeLayout.ofPlaceW hp i).pfx)
    (cwv : ∀ w, (cw w).val = .loc (cS w) 0)
    (pass : HelloW1.PassH
      (HelloWorkerRR.helloDR (RuntimeLayout.ofPlaceW hp i).exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
      passT) :
    HelloW1.WCompatH
      (HelloWorkerRR.QIR (RuntimeLayout.ofPlaceW hp i).exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB arch R1 cT cS
        pT Pa G passT M r0 r1)
      (HelloWorkerRR.helloDR (RuntimeLayout.ofPlaceW hp i).exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB)
      (μP hp i H E asm) (RuntimeLayout.ofPlaceW hp i).Λ arch
      (Spike.Lib.A64.Flow.Worker.AbW (RuntimeLayout.ofPlaceW hp i).exe) :=
  haveI := (RuntimeLayout.ofPlaceW hp i).valid
  HelloWorkerRR.hC_IR (RuntimeLayout.ofPlaceW hp i).exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB
    (by rw [← ho]; exact (RuntimeLayout.ofPlaceW hp i).lays) hend (hello_hμP hp i ho hpa) cwv pass

end Worker

section Main

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {D : WSideH ι} {r0 r1 : ι → Range}
  {ms : ι → MemSide isaLSE2} {cw : ι → TermRun.Word}

/-- **`WCompat0` at the placed layout and the target's marks**, main's side
`helloM` at the records' placement, `L.lab`, `L.exe`, `L.Λ`, `μP` (see the
module doc). -/
theorem hC0P (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    /- (5j) the memory side -/
    (hK : ∀ w, (ms w).K = some abi) (hG : ∀ w, (ms w).G = G w) (hown : ∀ w s, (ms w).own s = [])
    (hmpW : ∀ w L, (ms w).mp L true →
      (Pa w).foot 0 L ∧ ¬ InLabel (SR w).lbl (SR w).lsize L ∧
        Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared L)
    (hrt : ∀ w a, (ms w).rt a → ¬ ∃ l b, (SR w).lbl l = some b ∧ b ≤ a ∧ a < b + 8 * (SR w).lsize l)
    (hrdN : ∀ w (w' : TermRun.Word) n, w'.val = .num n → (ms w).rd w')
    (habt : ∀ w s, (ms w).abortAt s →
      ∃ k a, (Spike.Lib.A64.PhRec.μ (RuntimeLayout.ofPlaceW hp i)).abortAt k = some a ∧ pcOf s = a)
    /- (5j) main's pointer word; the certified no-promise fact -/
    (hcw : ∀ w, (cw w).val = .loc (cS w) 0)
    (hnp : ∀ w x (t : Thread isaLSE2) mem, (Pa w).noProm t.st →
      CertOkC Arch.armv8 (certSem abi Arch.armv8 (μP hp i H E asm) x 0) 0 t mem → t.prom = []) :
    WakeM0.WCompat0
      (helloQ arch R1 ι SR cT cS pT Pa G passT
        (helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) ms cw (RuntimeLayout.ofPlaceW hp i).lab
          (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ (μP hp i H E asm) (hoffP hp i hpa))
        D r0 r1)
      (helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) ms cw (RuntimeLayout.ofPlaceW hp i).lab
        (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ (μP hp i H E asm) (hoffP hp i hpa))
      (μP hp i H E asm) (RuntimeLayout.ofPlaceW hp i).Λ := by
  haveI := (RuntimeLayout.ofPlaceW hp i).valid
  have hm : μP hp i H E asm = Spike.Lib.A64.PhRec.μ (RuntimeLayout.ofPlaceW hp i) :=
    Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target _ hpa
  refine HelloCompat0.hC0H (fun _ => rfl) hK hG hown hmpW hrt hrdN (by rw [hm]; exact habt)
    (by rw [hm]; exact fun s c h => Spike.Lib.A64AbOffL.noSite_of_A_ofPlaceOK hp i h) hcw hnp

end Main

end Place

end Spike.Lib.HelloCompatI

/-- info: 'Spike.Lib.HelloCompatI.hello_hμP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCompatI.hello_hμP

/-- info: 'Spike.Lib.HelloCompatI.hC_IP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCompatI.hC_IP

/-- info: 'Spike.Lib.HelloCompatI.hC0P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCompatI.hC0P
