/-
**the compatibility fields at the instance** (AArch64): the fields of `WakeW1.WCompatX`, `WakeW1.WCompat` (through
`WakeAssembly.wCompat_of`) and `WakeM0.WCompat0` of the worker's side, at
`Q := WakeInst.wakeQI hp i ok arch R1 μT M D r0 r1` with main's side
`M := WakeInst.wakeM hp i ok lab μT hoff` (both threads' memory side
`WakeInst.wakeMs hp i`), over the ghost records satisfying `ok`.

- `GhOK Λ g`: the ghost record's facts the fields below need (the pointer
  words locatives to `cS`, the source memory nonempty, `cS` a placed word
  whose target word is `cT`, `cT` shared), with `ghOK_of` from the memory
  relation at the spawn. Instantiate `ok := GhOK L.Λ`.

- `Gc_I`: the worker's flag store value `1` is a `G` value at `cT`.
- `noProm_I`, `noProm0_I`: a certified thread at a no-promise state has no
  promise (`WakeP.noProm_prom`), at `μT` the certification's marks.
- `rd1_I`: main's rows read every word (`wakeMs`' read side is `True`).
- `abortAt0_I`: `wakeMs`' abort sites (`PhRec.μ L`'s) are the canonical
  target's (`AbOffW.marks_target`).
- `G_I`, `own_I`: `WCompat.G`/`own` at `D.ms := wakeMs hp i`.
- `cw0_I`, `cw_I`, `Spos_I`, `cT_I`, `cTin_I`: from `GhOK` (`cw_I` is
  `WCompat.cwv` at `cw := (·.1.cwW)`).
- `wide0_I`, `sysExec0_I`: from `WakeInst.wideX_I`.
- `hfrz_I`, `hfoot_I`: `spawn_of`'s static `Inv2Core` facts
  (`WakeP.wakeP_frz_cov`, `wakeP_foot_cov` at `wakeLocs_ok`).
- `hstart_I`: the pre-spawn machine loads the listing at the placed layout
  (`load_of_loadOk`, A1/A2 at the link).
-/
import Spike.Lib.WakeInst
import Spike.Lib.WakeMsOfFields
import Spike.Lib.A64WakeAbOffW
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeInstFields

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeInst
open Spike.Lib.A64.Rt (RuntimeLayout)

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
  ⟨hM, hW, hS, ⟨b, hl, ho, hT⟩, hT ▸ WakeMsOf.cTin_of_placed h hsp hl ho⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {ok : Gh → Prop} {lab : String → Int64} {μT : Marks}
  {hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a}
  {arch : WeakMem.Arch} {R1 : WakeA64.Cfg → TermRun.Cfg → Prop} {M : WakeM0.MSide {g : Gh // ok g}}
  {D : WakeW1.WSide {g : Gh // ok g}} {r0 r1 : {g : Gh // ok g} → Range}

/-- `WCompatX.Gc`. -/
theorem Gc_I : ∀ w, (wakeQI hp i ok arch R1 μT M D r0 r1).G w ((wakeQI hp i ok arch R1 μT M D r0 r1).C w).cT 1 :=
  fun _ => WakeG.wakeG_cT _

/-- `WCompat.noProm` (thread `1`) at the certification's marks `μT`. -/
theorem noProm_I : ∀ w x (t : Thread isaLSE2) mem, ((wakeQI hp i ok arch R1 μT M D r0 r1).P w).noProm t.st →
    CertOkC Arch.armv8 (certSem abi Arch.armv8 μT x 1) 1 t mem → t.prom = [] :=
  fun _ _ _ _ hn hc => WakeP.noProm_prom hn hc

/-- `WCompat0.noProm0` (thread `0`) at the certification's marks `μT`. -/
theorem noProm0_I : ∀ w x (t : Thread isaLSE2) mem, ((wakeQI hp i ok arch R1 μT M D r0 r1).P w).noProm t.st →
    CertOkC Arch.armv8 (certSem abi Arch.armv8 μT x 0) 0 t mem → t.prom = [] :=
  fun _ _ _ _ hn hc => WakeP.noProm_prom hn hc

/-- `WCompat0.rd1`. -/
theorem rd1_I : ∀ w (w' : TermRun.Word), w'.val = .num 1 → ((wakeM hp i ok lab μT hoff).ms w).rd w' :=
  fun _ _ h => ⟨1, h⟩

/-- `WCompat0.abortAt0` at the canonical target's marks, of a text parsing
to the layout's program (`hpa`). -/
theorem abortAt0_I {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} {asm : String}
    (hpa : Scc.Sem.A64.textProgram asm = .ok (RuntimeLayout.ofPlaceW hp i).prog) :
    ∀ w s, ((wakeM hp i ok lab μT hoff).ms w).abortAt s →
      ∃ k a, ((Scc.Sem.A64.target H E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ).abortAt k = some a ∧
        pcOf s = a := by
  intro w s h
  rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target _ hpa]
  exact h

/-- `WCompat.G` at `D.ms := wakeMs hp i`. -/
theorem G_I : ∀ w : {g : Gh // ok g}, (wakeMs hp i w.1).G = (wakeQI hp i ok arch R1 μT M D r0 r1).G w := fun _ => rfl

/-- `WCompat.own` at `D.ms := wakeMs hp i`. -/
theorem own_I : ∀ (w : {g : Gh // ok g}) s, (wakeMs hp i w.1).own s = [] := fun _ _ => rfl

/-- `WCompat0.wide0`. -/
theorem wide0_I : ∀ w s c, (wakeM hp i ok lab μT hoff).Mi w s c → Scc.Cert.WideA64.WideSt s :=
  fun w s c h => (wideX_I hp i w s c h).1

/-- `WCompat0.sysExec0`. -/
theorem sysExec0_I : ∀ w s c t, (wakeM hp i ok lab μT hoff).Mi w s c → abi.atSys s = true →
    isaLSE2.exec s = some t → ∃ m, t = .fault m :=
  WakeMsOf.sysExec_of_exe' (exe := (RuntimeLayout.ofPlaceW hp i).exe) fun w s c h => (wideX_I hp i w s c h).2

/-! ### From `GhOK` -/

variable {Λ' : Scc.Sem.Layout} (hok : ∀ g, ok g → GhOK Λ' g)
include hok

/-- `WCompat0.cw0`. -/
theorem cw0_I : ∀ w, ((wakeM hp i ok lab μT hoff).cw w).val =
    .loc ((wakeQI hp i ok arch R1 μT M D r0 r1).C w).cS 0 :=
  fun w => (hok w.1 w.2).1

/-- `WCompat.cwv` at `cw := (·.1.cwW)` (the worker's word: the spawn's
argument word, an untagged locative to `cS`, at any view). -/
theorem cw_I : ∀ w : {g : Gh // ok g}, w.1.cwW.val = .loc ((wakeQI hp i ok arch R1 μT M D r0 r1).C w).cS 0 :=
  fun w => (hok w.1 w.2).2.1

/-- `WCompat.Spos`. -/
theorem Spos_I : ∀ w, 0 < ((wakeQI hp i ok arch R1 μT M D r0 r1).SR w).S :=
  fun w => (hok w.1 w.2).2.2.1

/-- `WCompat.cT`. -/
theorem cT_I : ∀ w, ∃ a, ((wakeQI hp i ok arch R1 μT M D r0 r1).C w).cT = Scc.Sem.wordLoc a ∧
    Scc.Sem.wordAddr ((wakeQI hp i ok arch R1 μT M D r0 r1).SR w).lbl ((wakeQI hp i ok arch R1 μT M D r0 r1).C w).cS =
      some a ∧
    ((wakeQI hp i ok arch R1 μT M D r0 r1).C w).cS.offset <
      ((wakeQI hp i ok arch R1 μT M D r0 r1).SR w).lsize ((wakeQI hp i ok arch R1 μT M D r0 r1).C w).cS.label := by
  intro w
  obtain ⟨b, hl, ho, hT⟩ := (hok w.1 w.2).2.2.2.1
  obtain ⟨x, hx, ha, ho'⟩ := WakeMsOf.cT_of_placed hl ho
  exact ⟨x, hT.trans hx, ha, ho'⟩

/-- `WCompat.cTin` at the layout `Λ'` of `GhOK`. -/
theorem cTin_I : ∀ w, Consumer1.LocIn Λ'.shared ((wakeQI hp i ok arch R1 μT M D r0 r1).C w).cT :=
  fun w => (hok w.1 w.2).2.2.2.2

omit hok in
/-- `spawn_of`'s `hfrz`. -/
theorem hfrz_I : ∀ w t l, t < 2 → ((wakeQI hp i ok arch R1 μT M D r0 r1).P w).frz l →
    ((wakeQI hp i ok arch R1 μT M D r0 r1).P w).cov t l :=
  fun _ => WakeP.wakeP_frz_cov

omit hok in
/-- `spawn_of`'s `hfoot`. -/
theorem hfoot_I : ∀ w t u l, t < 2 → u < 2 → t ≠ u → ((wakeQI hp i ok arch R1 μT M D r0 r1).P w).foot u l →
    ¬ ((wakeQI hp i ok arch R1 μT M D r0 r1).P w).cov t l :=
  fun w => WakeP.wakeP_foot_cov (wakeLocs_ok hp i w.1)

omit hok in
/-- `WakeObligations.hstart` at the placed layout, of a listing parsing to
the output (`hpa`). -/
theorem hstart_I {asm : String} (hpa : Scc.Cert.Link.A64.parsesTo asm o.prog o.secs = true) :
    ∃ d, (target (kernel 1) Entry.linux).load asm (RuntimeLayout.ofPlaceW hp i).Λ = some d :=
  ⟨_, Scc.Cert.Link.A64.load_of_loadOk hpa (PlaceW.loadOk_link_of_placeW (i := i) hp)
    (PlaceW.clear_link_of_placeW (i := i) hp)⟩

end Inst

/-- info: 'Spike.Lib.WakeInstFields.abortAt0_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms abortAt0_I

end Spike.Lib.WakeInstFields
