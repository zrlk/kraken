/-
**The remaining compatibility fields at the x86-64 instance** (x86-64 twin of `Spike/Lib/WakeInstFields.lean`): the fields of
`X64WakeW1.WCompatX`, `X64WakeW1.WCompat` (through
`X64WakeAssembly.wCompat_of`) and `X64WakeM0.WCompat0` not proved in
`X64WakeInst`, at `Q := X64WakeInst.wakeQI hp i T W ok arch R1 μT M D r0 r1 passT`
with main's side `X64WakeInst.wakeM hp i T W ok lab μT hoff` and the worker's
memory side `X64WakeInst.msW hp i T W`, over the ghost records satisfying `ok`.

- `GhOK Λ g`: the ghost record's facts the fields below need (the pointer
  words locatives to `cS`, the source memory nonempty, `cS` a placed word
  whose target word is `cT`, `cT` shared), with `ghOK_of` from the memory
  relation at the spawn. Instantiate `ok := GhOK L.Λ` (or `X64WakeOkW.okW`).
- `Gc_I`: the worker's flag store value `1` is a `G` value at `cT`.
- `noProm_I`, `noProm0_I`: a certified thread at a no-promise state has no
  promise (`WakeP.noProm_prom`), at `μT` the certification's marks.
- `rd1_I`: main's rows read every number.
- `abortAt0_I`: `wakeMs`' abort sites (`PhRec.μ L`'s) are the canonical
  target's (`X64.Flow.Worker.Wake.AbOffW.marks_target`).
- `G_I`, `own_I`, `ownConst1_I`, `ownMp1_I`, `ownCov1_I`: `WCompat.G`/`own`
  and `WCompatX`'s `ownConst1`/`ownMp1` and `WCompat.ownCov` at
  `D.ms := msW hp i T W`.
- `sysExec0_I`: from `X64WakeInst.wideX_I`.
- `cw0_I`, `cw_I`, `Spos_I`, `cT_I`, `cTin_I`: from `GhOK`.
- `hfrz_I`, `hfoot_I`: `spawn_of`'s static `Inv2Core` facts
  (`WakeP.wakeP_frz_cov`, `wakeP_foot_cov` at `wakeLocs_ok`).
- `hstart_I`: the pre-spawn machine loads the listing at the placed layout
  (`Scc.Cert.Link.X64.load_of_loadOk`, A1/A2 at the link).

**Where this differs from AArch64**: the worker's memory side is `msW hp i
T W` (A64 `wakeMs hp i`), so `own_I` reads `wakeOwnXW`'s thread-1 word and
the triple `ownConst1_I`, `ownMp1_I`, `ownCov1_I` is added (A64: the worker
owns nothing); `hfoot_I` carries `SelfOK T W` (as `X64WakeInst.footLab_I`);
`wide0_I` is in `X64WakeInst`; the certification's architecture is
`Arch.tso`; `abortAt0_I` reads the text's cells (`cellsOf`, A64
`textProgram`); `hstart_I` takes any entry `E` clear of the layout (A64:
`Entry.linux`) and the text's label offsets the output's (`hoffs`: the x64
loader checks the size table against them). `hoffs` is
discharged at the instance on the assembly side (the x86-64
`AssemblyR`) from the certificate's parse, next to `hpa`.
-/
import Spike.Lib.X64WakeInst
import Spike.Lib.X64WakeMsOfFields
import Spike.Lib.X64WakeAbOffW

namespace Spike.Lib.X64WakeInstFields

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeInst
open Spike.Lib.X64.Rt (RuntimeLayout)

/-! ## The ghost records' facts -/

/-- **A ghost record's facts**: main's and the worker's pointer words are
locatives to `cS`, the source memory at the spawn is nonempty, `cS` is a
word of a placed label whose target word is `cT`, and `cT` is shared. -/
def GhOK (Λ : Scc.Sem.Layout) (g : Gh) : Prop :=
  g.cwM.val = .loc g.cS 0 ∧ g.cwW.val = .loc g.cS 0 ∧ 0 < g.S ∧
    (∃ b, g.lbl g.cS.label = some b ∧ g.cS.offset < g.lsize g.cS.label ∧
      g.cT = Scc.Sem.wordLoc (b + 8 * g.cS.offset)) ∧
    Consumer1.LocIn Λ.shared g.cT

/-- **`GhOK` from the memory relation at the spawn**: `cS` placed at `b`
under the spawn's placement, the label regions in the address space. -/
theorem ghOK_of {Λ : Scc.Sem.Layout} {g : Gh} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (h : Scc.Sem.MemRelP Λ g.lbl g.lsize ts tm sm tp tq sp)
    (hsp : ∀ x, Λ.heap.contains x ∨ Λ.data.contains x → x < 2 ^ 64)
    (hM : g.cwM.val = .loc g.cS 0) (hW : g.cwW.val = .loc g.cS 0) (hS : 0 < g.S)
    {b : Nat} (hl : g.lbl g.cS.label = some b) (ho : g.cS.offset < g.lsize g.cS.label)
    (hT : g.cT = Scc.Sem.wordLoc (b + 8 * g.cS.offset)) : GhOK Λ g :=
  ⟨hM, hW, hS, ⟨b, hl, ho, hT⟩, hT ▸ X64WakeMsOf.cTin_of_placed h hsp hl ho⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) (T W : BitVec 64)
  {ok : Gh → Prop} {lab : String → Int64} {μT : Marks}
  {hoff : ∀ s c, Spike.Lib.X64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a}
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {M : X64WakeM0.MSide {g : Gh // ok g}}
  {D : X64WakeW1.WSide {g : Gh // ok g}} {r0 r1 : {g : Gh // ok g} → Range} {passT : State → Prop}

local notation "MI" => wakeM hp i T W ok lab μT hoff
local notation "QI" => wakeQI hp i T W ok arch R1 μT M D r0 r1 passT

/-- `WCompatX.Gc`. -/
theorem Gc_I : ∀ w, (QI).G w ((QI).C w).cT 1 := fun _ => WakeG.wakeG_cT _

/-- `WCompat.noProm` (thread `1`) at the certification's marks `μT`. -/
theorem noProm_I : ∀ w x (t : Thread isa) mem, ((QI).P w).noProm t.st →
    CertOkC Arch.tso (certSem abi Arch.tso μT x 1) 1 t mem → t.prom = [] :=
  fun _ _ _ _ hn hc => WakeP.noProm_prom hn hc

/-- `WCompat0.noProm0` (thread `0`) at the certification's marks `μT`. -/
theorem noProm0_I : ∀ w x (t : Thread isa) mem, ((QI).P w).noProm t.st →
    CertOkC Arch.tso (certSem abi Arch.tso μT x 0) 0 t mem → t.prom = [] :=
  fun _ _ _ _ hn hc => WakeP.noProm_prom hn hc

/-- `WCompat0.rd1`. -/
theorem rd1_I : ∀ w (w' : TermRun.Word), w'.val = .num 1 → ((MI).ms w).rd w' :=
  fun _ _ h => ⟨1, h⟩

/-- `WCompat0.abortAt0` at the canonical target's marks, of a text whose
cells are the layout's (`hpa`). -/
theorem abortAt0_I {H : Scc.Sem.Hooks isa} {E : Scc.Sem.Entry} {asm : Scc.Sem.X64.Asm}
    (hpa : Scc.Sem.X64.cellsOf asm = some (RuntimeLayout.ofPlaceWX hp i).prog) :
    ∀ w s, ((MI).ms w).abortAt s →
      ∃ k a, ((Scc.Sem.X64.target H E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ).abortAt k = some a ∧
        pcOf s = a := by
  intro w s h
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target _ hpa]
  exact h

/-- `WCompat.G` at `D.ms := msW hp i T W`. -/
theorem G_I : ∀ w : {g : Gh // ok g}, (msW hp i T W w.1).G = (QI).G w := fun _ => rfl

/-- `WCompat.own` at `D.ms := msW hp i T W`: the worker owns its self word. -/
theorem own_I : ∀ (w : {g : Gh // ok g}) s, (msW hp i T W w.1).own s = (QI).own w 1 s [] :=
  fun _ _ => rfl

/-- `WCompatX.ownConst1`. -/
theorem ownConst1_I : ∀ w s s', (QI).own w 1 s' [] = (QI).own w 1 s [] := fun _ _ _ => rfl

/-- `WCompatX.ownMp1` at `D.ms := msW hp i T W`. -/
theorem ownMp1_I : ∀ (w : {g : Gh // ok g}) s L v, (L, v) ∈ (QI).own w 1 s [] →
    ¬ (msW hp i T W w.1).mp L true :=
  fun w s L v hm => X64WakeOwnX.ownMp1XW (wakeMs hp i w.1) T W w s L v hm

/-- `WCompat.ownCov`. -/
theorem ownCov1_I : ∀ w s L v, (L, v) ∈ (QI).own w 1 s [] → ((QI).P w).cov 1 L :=
  fun w s L v hm => X64WakeOwnX.ownCov1XW T W w s L v hm

/-- `WCompat0.sysExec0`. -/
theorem sysExec0_I : ∀ w s c t, (MI).Mi w s c → abi.atSys s = true →
    isa.exec s = some t → ∃ m, t = .fault m :=
  X64WakeMsOf.sysExec_of_exe' (exe := (RuntimeLayout.ofPlaceWX hp i).exe)
    fun w s c h => (wideX_I hp i T W w s c h).2

/-! ### From `GhOK` -/

variable {Λ' : Scc.Sem.Layout} (hok : ∀ g, ok g → GhOK Λ' g)
include hok

/-- `WCompat0.cw0`. -/
theorem cw0_I : ∀ w, ((MI).cw w).val = .loc ((QI).C w).cS 0 :=
  fun w => (hok w.1 w.2).1

/-- `WCompat.cwv` at `cw := (·.1.cwW)` (the worker's word: the spawn's
argument word, an untagged locative to `cS`). -/
theorem cw_I : ∀ w : {g : Gh // ok g}, w.1.cwW.val = .loc ((QI).C w).cS 0 :=
  fun w => (hok w.1 w.2).2.1

/-- `WCompat.Spos`. -/
theorem Spos_I : ∀ w, 0 < ((QI).SR w).S :=
  fun w => (hok w.1 w.2).2.2.1

/-- `WCompat.cT`. -/
theorem cT_I : ∀ w, ∃ a, ((QI).C w).cT = Scc.Sem.wordLoc a ∧
    Scc.Sem.wordAddr ((QI).SR w).lbl ((QI).C w).cS = some a ∧
    ((QI).C w).cS.offset < ((QI).SR w).lsize ((QI).C w).cS.label := by
  intro w
  obtain ⟨b, hl, ho, hT⟩ := (hok w.1 w.2).2.2.2.1
  obtain ⟨x, hx, ha, ho'⟩ := X64WakeMsOf.cT_of_placed hl ho
  exact ⟨x, hT.trans hx, ha, ho'⟩

/-- `WCompat.cTin` at the layout `Λ'` of `GhOK`. -/
theorem cTin_I : ∀ w, Consumer1.LocIn Λ'.shared ((QI).C w).cT :=
  fun w => (hok w.1 w.2).2.2.2.2

omit hok in
/-- `spawn_of`'s `hfrz`. -/
theorem hfrz_I : ∀ w t l, t < 2 → ((QI).P w).frz l → ((QI).P w).cov t l :=
  fun _ => WakeP.wakeP_frz_cov

omit hok in
/-- `spawn_of`'s `hfoot`, given the self words' separation (`SelfOK`). -/
theorem hfoot_I (hself : ∀ w : {g : Gh // ok g}, SelfOK T W w.1) :
    ∀ w t u l, t < 2 → u < 2 → t ≠ u → ((QI).P w).foot u l → ¬ ((QI).P w).cov t l :=
  fun w => WakeP.wakeP_foot_cov (wakeLocs_ok hp i T W w.1 (hself w))

omit hok in
/-- `WakeObligations.hstart` at the placed layout, of a text parsing to the
output (`hpa`) with the output's label offsets (`hoffs`). -/
theorem hstart_I {asm : Scc.Sem.X64.Asm} (hpa : Scc.Cert.Link.X64.parsesTo asm o.prog o.secs = true)
    (hoffs : asm.labelOffs = o.labelOffs) :
    ∃ d, (target (kernel 1) Entry.linux).load asm (RuntimeLayout.ofPlaceWX hp i).Λ = some d :=
  ⟨_, Scc.Cert.Link.X64.load_of_loadOk hpa (hoffs ▸ PlaceWX.loadOk_link_of_placeWX (i := i) hp)
    (PlaceWX.clear_link_of_placeWX (i := i) hp)⟩

end Inst

end Spike.Lib.X64WakeInstFields

/-- info: 'Spike.Lib.X64WakeInstFields.abortAt0_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInstFields.abortAt0_I

/-- info: 'Spike.Lib.X64WakeInstFields.cT_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInstFields.cT_I

/-- info: 'Spike.Lib.X64WakeInstFields.hfoot_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInstFields.hfoot_I

/-- info: 'Spike.Lib.X64WakeInstFields.hstart_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInstFields.hstart_I

/-- info: 'Spike.Lib.X64WakeInstFields.sysExec0_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInstFields.sysExec0_I
