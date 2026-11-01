/-
**hello.w on AArch64: main's permit, limit and exit pieces past the clone**
(the twin of `Spike.Lib.WakeMainInstD`): the fields `hS`, `htp4`, `htls`,
`hexit` of `HelloMainHRD.MainInstH` at a placed output (`L :=
RuntimeLayout.ofPlaceW hp i`), hello's memory side `HelloMs.helloMs L G lbl
lsize` (any value invariant `G`, the spawn's placement `lbl`/`lsize`), main's
TCB `tp = L.pinA + 0 + 8`, at a frame `R` with frame condition `DFrame R m0`:

- `hS_IH` (`hS`): the park's store of `0` to `tp + 16` (`WakeHS.permit_free`,
  the word pinned, `WakeMainInstD.locIn_tp16_I`), given `G` at the word and
  value (`hG`);
- `htp4_IH` (`htp4`): `WakeMainInst.htp4_I`;
- `limOk_IH`: the limit load's `LimOk` at `tp + 8` (`WakeHS.lim_free`), given
  `G`'s values at the word within the room (`hroom`);
- `htls_IH` (`htls`): `Hello.AbOffAt.seg_waitTlsW` with `hW` from
  `A64HelloMainSF.tlsW_mainR` and the landing from `limOk_IH` (at hello's
  labels `LoopCode.loopLabs_hello`, runs `HelloRunsOff.wait_off`,
  `hello_flag_ne`);
- `hexit_IH` (`hexit`): past the wait loop's load the word read is the
  number `1` (`rd_numH`), so the source's test takes `wlRet`, which returns
  `0` (`SrcSem.mainExit`);
- `mainInstH_I`: `MainInstH` from the above at the region
  `⟨Rm.base, -144, 48⟩`.

At hello's root value invariant `wakeG (GOf2H L m0') cT` (wake's shape;
`WakeInst.wakeG'` at the record's flag word): `hG_permitH` discharges `hS`'s
`hG`, `hroom_limH` `limOk`'s `hroom` given the flag word not the limit word,
which `cT_ne_IH` gives for a flag word in a placed label; `mainInstH_G`
assembles `MainInstH` there.

Open premises (as `WakeMainInstD`'s): `hA0`/`hoff` per word
(`WakeMainFlag.hA0_of`/`hAoff_of` at `locIn_tp16_I`/`locIn_tp8_I`), `hm` (the
memory relation at the spawn), `hZ` (main's frame above stack 0's guard), the
source facts `hval`/`hloc`/`hin` (`HelloMainSrc.src_piecesH`), the flag word
shared (`hsh`), and the instance's `hprog`, `hw`.
-/
import Spike.Lib.HelloMs
import Spike.Lib.HelloMainHRD
import Spike.Lib.WakeMainInstD
import Spike.Lib.A64HelloMainSF
import Spike.Lib.A64HelloLoopCode
import Spike.Lib.A64HelloRunsOff
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.HelloMainInstD

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (ValRep LocRep MemRelP Range)
open Spike.Lib.A64.Flow
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.HelloMs (helloMs)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloMainInv (mainWRH)
open Spike.Lib.WakeMainSrc (waitC)
open Spike.Lib.WakeM0 (wlIf)
open Spike.Lib.A64.HelloLabels (pfx)
open Spike.Lib.A64.Flow.Worker.Hello.MainPost (mainSp1)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)
open Spike.Lib.WakeMainInstD (unmapped_I pinned_j)
open Spike.Lib.A64.PhRec (m0Of)

/-- **A word `helloMs` reads representing `1` is the number `1`** (as
`WakeInst.rd_num`). -/
theorem rd_numH {L : RuntimeLayout} {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} (w' : TermRun.Word) (hr : (helloMs L G lbl lsize).rd w')
    (hv : ValRep lbl w'.val 1) : w'.val = .num 1 := by
  obtain ⟨n, hn⟩ := hr
  rw [hn] at hv ⊢
  rw [hv.2]

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}

/-- **`hS` at the instance**: the park's store of `0` to main's permit word
`tp + 16` under `helloMs`, in the frame `R` from `m0`, given the word
unloadable there (`hA0`, `hoff`) and `G` of the word at `0` (`hG`). -/
theorem hS_IH {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tq0 tq sp)
    {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64)
    {R : Region} {m0 : MachineData} (hA0 : Mem.loadInt m0.dmem (tp + 16#64) 8 = none)
    (hoff : (tp + 16#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 16#64).toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ (tp + 16#64).toNat))
    (hG : G ⟨tp + 16#64, 8⟩ ((0#64).setWidth 128))
    {exe : _root_.Executable} {endPc : Int64} :
    Ret0.StOk (helloMs (RuntimeLayout.ofPlaceW hp i) G lbl lsize) (DFrame R m0) exe endPc (tp + 16#64) 0#64 := by
  have hu := unmapped_I hA0 hoff
  subst htp
  have hfree := WakeHS.permit_free hp i hm
  have ha := pinned_j hp i (j := 3) (by decide) (by decide)
  rw [← WakeHS.permit_eq] at ha
  refine ⟨hfree, ⟨WakeChildSt.stOk_pinned.mapped_K0_pinned hp i ha, fun _ => ⟨fun k hk => ?_, ?_⟩⟩, hG, hu⟩
  · exact .inr (.inr (ha k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))
  · rintro ⟨l, b, hl, hx⟩
    exact hfree ⟨l, b, hl, by simpa using hx⟩

/-- **`htp4` at the instance**: main's permit word is 4-aligned. -/
theorem htp4_IH {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64) :
    (tp + 16#64).toNat % 4 = 0 :=
  WakeMainInst.htp4_I hp i htp

/-- **The flag's target word is not main's limit word**: a flag word in a
placed label (`hT`) is not `tp + 8`, which is in none (`WakeHS.lim_free`). -/
theorem cT_ne_IH {cT : Loc} {cS : WeakMem.Address} {b : Nat} (hl : lbl cS.label = some b)
    (ho : cS.offset < lsize cS.label) (hT : cT = Scc.Sem.wordLoc (b + 8 * cS.offset))
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tq0 tq sp) :
    (⟨(RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 8#64, 8⟩ : Loc) ≠ cT := by
  intro h
  have hx : (Scc.Sem.lrange lsize cS.label b).contains (b + 8 * cS.offset) := by
    have h1 : @LT.lt Nat _ cS.offset (lsize cS.label) := ho
    simp only [Scc.Sem.lrange, Range.contains]; omega
  have hs := Spike.Lib.WakeGOf.heapData_of_placed hm hl hx
  have hw := (PlaceW.wf_link_of_placeW i hp).inSpace
  have hd := (hw _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hp i).Λ.data ∈ (RuntimeLayout.ofPlaceW hp i).Λ.regions)).2
  have hh := (hw _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hp i).Λ.heap ∈ (RuntimeLayout.ofPlaceW hp i).Λ.regions)).2
  have hlt : b + 8 * cS.offset < 2 ^ 64 := by
    simp only [Range.contains] at hs; omega
  refine WakeHS.lim_free hp i hm ⟨cS.label, b, hl, ?_⟩
  rw [show (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 8#64 = cT.addr by rw [← h], hT]
  simp only [Scc.Sem.wordLoc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact hx

/-- **The limit load's `LimOk` at the instance**: main's limit word `tp + 8`
under `helloMs`, in the frame `R` from `m0` (`hA0`, `hoff` as `hS_IH`'s),
with `G`'s values at the word within the room up to `Z` (`hroom`). -/
theorem limOk_IH {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tq0 tq sp)
    {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64)
    {R : Region} {m0 : MachineData} (hA0 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ (tp + 8#64).toNat))
    {Z : BitVec 64} (hroom : ∀ v : Val, G ⟨tp + 8#64, 8⟩ v → (v.setWidth 64).toNat ≤ Z.toNat)
    {exe : _root_.Executable} {endPc : Int64} :
    Ret0.LimOk (helloMs (RuntimeLayout.ofPlaceW hp i) G lbl lsize) (DFrame R m0) exe endPc (tp + 8#64) Z := by
  have hu := unmapped_I hA0 hoff
  subst htp
  have ha := pinned_j hp i (j := 2) (by decide) (by decide)
  rw [← WakeHS.lim_eq] at ha
  exact ⟨WakeHS.lim_free hp i hm, ⟨Spike.Lib.A64Consumer.mapped_K0_of_mem fun k hk => .inr (ha k hk), nofun⟩,
    hu, hroom⟩

/-- **`htls` at the instance**: `wc_waitLoop`'s limit load from `.tls` to
`.n1` inside `mainWRH`, in the frame `R` from `m0`, the limit's values within
the room up to `x9`'s address `R.addr (-32)` (`hroom`), the flag's word
`cA` shared (`hsh`), given `limOk_IH`'s premises and the source side's
(`hval`, `hloc`, `hin`). -/
theorem htls_IH (hprog : o.prog = helloProg) (hw : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    {endPc : Int64} (hend : endPc = endOf (RuntimeLayout.ofPlaceW hp i).exe helloProg (RuntimeLayout.ofPlaceW hp i).pfx)
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tq0 tq sp)
    {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64)
    {R : Region} {m0 : MachineData} (hA0 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ (tp + 8#64).toNat))
    (hroom : ∀ v : Val, G ⟨tp + 8#64, 8⟩ v → (v.setWidth 64).toNat ≤ (R.addr (-32)).toNat)
    {w : TermRun.Word} {cA x29 ra : BitVec 64}
    (hsh : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared ⟨cA, 8⟩) (hval : ValRep lbl w.val cA.toNat)
    (hloc : LocRep lbl w.val cA.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    SegW (mainWRH (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
        (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize) (fun _ _ => False)
      helloSrc lbl (helloMs (RuntimeLayout.ofPlaceW hp i) G lbl lsize)
      (At (RuntimeLayout.ofPlaceW hp i).exe endPc R (DFrame R m0)
        (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
          pfx (waitC w) "d" wlIf (.ptr .pub .int)
          (fun w' => (helloMs (RuntimeLayout.ofPlaceW hp i) G lbl lsize).rd w' ∧ ValRep lbl w'.val 1)
          cA x29 ra tp .tls))
      (At (RuntimeLayout.ofPlaceW hp i).exe endPc R (DFrame R m0)
        (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
          pfx (waitC w) "d" wlIf (.ptr .pub .int)
          (fun w' => (helloMs (RuntimeLayout.ofPlaceW hp i) G lbl lsize).rd w' ∧ ValRep lbl w'.val 1)
          cA x29 ra tp .n1)) := by
  haveI := (RuntimeLayout.ofPlaceW hp i).valid
  have hl : Lays (RuntimeLayout.ofPlaceW hp i).exe helloProg (RuntimeLayout.ofPlaceW hp i).pfx := by
    rw [← hprog]; exact (RuntimeLayout.ofPlaceW hp i).lays
  have hL := limOk_IH hp i hm htp hA0 hoff hroom (exe := (RuntimeLayout.ofPlaceW hp i).exe) (endPc := endPc)
  have hrt8 : ¬ ∃ l b, lbl l = some b ∧ (Scc.Sem.lrange lsize l b).contains (tp + 8#64).toNat := hL.rt
  have hpc : (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
      pfx (waitC w) "d" wlIf (.ptr .pub .int)
      (fun w' => (helloMs (RuntimeLayout.ofPlaceW hp i) G lbl lsize).rd w' ∧ ValRep lbl w'.val 1)
      cA x29 ra tp .tls).pc =
      (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label (pfx ++ ".stack_check") +
        Int64.ofNat (4 * 2) := by
    rw [(Spike.Lib.A64.Flow.Worker.Hello.LoopCode.loopLabs_hello hl).2.1]
    show _ + 4 + 4 = _
    rw [Int64.add_assoc]; rfl
  have hruns := Spike.Lib.A64.HelloRunsOff.wait_off hl
  have hc0 : (waitC w).term ≠ WakeMLive.wlRet := by
    simp [waitC, Spike.Lib.WakeMainSrc.waitBody, WakeMLive.wlRet]
  have hfv0 : ∀ y ∈ Scc.Sem.exprFv (waitC w).term, y = "c" := by
    simp [waitC, Spike.Lib.WakeMainSrc.waitBody, Scc.Sem.exprFv, Scc.Sem.atVars, Scc.Sem.opVars, Scc.Sem.opAts]
  have hm0 := Spike.Lib.A64WakeMainL.labMapped_c0 (c0 := waitC w) rfl (Spike.Lib.WakeMainSrc.waitC_ev w) hval
    (hin.imp fun _ h => h.1) (Spike.Lib.WakeLabMapped.mapped_K0_of_shared hsh)
  refine Spike.Lib.A64.Flow.Worker.Hello.AbOffAt.seg_waitTlsW hl hend hpc (FStable.dframe _ _)
    (fun s c h => (Spike.Lib.A64HelloMainSF.tlsW_mainR hl hend hpc hruns (WakeMainInst.hwide_I hp i hw) hc0 hfv0
      (by simp [waitC, TermRun.lookupE]) hloc hm0 (Spike.Lib.A64.HelloRunsOff.hello_flag_ne hl) hrt8 rfl rfl
      (Spike.Lib.WakeMainSrc.waitC_ev w) hin s c h).1) ?_
  intro m σ c hA hD hJ
  have ha : rAddr σ.regs .X10 8 = tp + 8#64 := Ret0.rAddr_x10 hJ.2 8
  rw [ha]
  refine ⟨hL.rt, hL.mp, hL.unmapped m hD, c, .refl c, fun v hv => ⟨rfl, ?_, ?_⟩⟩
  · show SO.le Spike.Lib.A64.WaitLoop.oX (Spike.Lib.A64.WaitLoop.oX.kill .X10) = true; decide
  · have hroom' := hL.room v hv
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, -⟩ := hJ
    have h9 := hA.so (.reg .X9) (-32) rfl
    refine ⟨⟨h1, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64] using h2
    · simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64] using h3
    · simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64] using h4
    · rw [show (ldStep .X10 (v.setWidth 64) σ).regs.TPIDR_EL0 = σ.regs.TPIDR_EL0 from
        Spike.Lib.A64.KeepTP.setRegOrZr_tp _ _ _]; exact h5
    · simp only [Reg64s.getRegOrSp64, Reg64s.getXReg] at h9
      simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, h9] using hroom'

/-- **`hexit` at the instance**: past the wait loop's load, the word read is
the number `1` (`rd_numH`), so the source's test takes `wlRet`, a placed
control whose return is `exit` with code `0`; for any state predicate `X`. -/
theorem hexit_IH {L : RuntimeLayout} {w : TermRun.Word} {X : State → Ctl → Prop} :
    ∀ s c', Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
      (fun w' => (helloMs L G lbl lsize).rd w' ∧ ValRep lbl w'.val 1) c' → X s c' →
      ¬ (helloMs L G lbl lsize).abortAt s → MainExit helloSrc (helloMs L G lbl lsize) s c' 0 := by
  rintro s c' ⟨w', ⟨hr, hv⟩, rfl⟩ - -
  have h1 := rd_numH w' hr hv
  have ha : TermRun.evalAt (("d", loadTy (.ptr .pub .int), [w']) :: (waitC w).env) (.var "d")
      = some (loadTy (.ptr .pub .int), [w']) := by
    simp [TermRun.evalAt, TermRun.lookupE, List.find?]
  have hs := LowerNode.localStep_ifeq (p := helloSrc) (n := 1) (m := 1)
    (c := ⟨wlIf, ("d", loadTy (.ptr .pub .int), [w']) :: (waitC w).env, none⟩)
    (ta := loadTy (.ptr .pub .int)) (tb := .intS (.lit 1)) (wb := TermRun.cst (.num 1))
    rfl ha rfl h1 rfl
  rw [ite_eq_left rfl] at hs
  refine ⟨_, .single hs, ⟨fun _ _ => none, ?_, ?_, ?_⟩, ?_⟩
  · intro x ty ws hl k wd wp hk hp
    cases hp
  · intro x hx
    simp [WakeMLive.wlRet, Scc.Sem.exprFv, Scc.Sem.atVars] at hx
  · intro x k n h
    cases h
  · intro s0 th h0 ht he hst
    unfold Scc.Sem.SrcSem.mainExit
    simp only [h0, ht, hst, he]
    rfl

/-- **`MainInstH` at the instance** (`hS_IH`, `htp4_IH`, `htls_IH`,
`hexit_IH` at the region `⟨Rm.base, -144, 48⟩`): `G` at the permit word
(`hG`) and the limit word's values within the room up to `x9`'s address
(`hroom`) open. -/
theorem mainInstH_I (hprog : o.prog = helloProg) (hw : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    {endPc : Int64} (hend : endPc = endOf (RuntimeLayout.ofPlaceW hp i).exe helloProg (RuntimeLayout.ofPlaceW hp i).pfx)
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tq0 tq sp)
    {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64)
    {Rm : Region} {m0 : MachineData}
    (hA16 : Mem.loadInt m0.dmem (tp + 16#64) 8 = none)
    (hoff16 : (tp + 16#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 16#64).toNat : Int) + 8 ≤ Rm.base.toNat + -144 ∨ (Rm.base.toNat : Int) + 48 ≤ (tp + 16#64).toNat))
    (hA8 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff8 : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ Rm.base.toNat + -144 ∨ (Rm.base.toNat : Int) + 48 ≤ (tp + 8#64).toNat))
    (hG : G ⟨tp + 16#64, 8⟩ ((0#64).setWidth 128))
    (hroom : ∀ v : Val, G ⟨tp + 8#64, 8⟩ v →
      (v.setWidth 64).toNat ≤ ((⟨Rm.base, -144, 48⟩ : Region).addr (-32)).toNat)
    {w : TermRun.Word} {cA x29 ra : BitVec 64}
    (hsh : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared ⟨cA, 8⟩) (hval : ValRep lbl w.val cA.toNat)
    (hloc : LocRep lbl w.val cA.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    HelloMainHRD.MainInstH (RuntimeLayout.ofPlaceW hp i).exe endPc (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize
      (helloMs (RuntimeLayout.ofPlaceW hp i) G lbl lsize) m0 Rm cA x29 ra tp w where
  hS := hS_IH hp i hm htp (R := ⟨Rm.base, -144, 48⟩) hA16 hoff16 hG
  htp4 := htp4_IH hp i htp
  htls := htls_IH hp i hprog hw hend hm htp (R := ⟨Rm.base, -144, 48⟩) hA8 hoff8 hroom hsh hval hloc hin
  hexit := hexit_IH

/-! ## At hello's root value invariant `wakeG (GOf2H L m0') cT` -/

/-- **`G` at main's permit word** under `wakeG (GOf2H L m0') cT`, any value
(`hS_IH`'s `hG`): the word is neither limit word. -/
theorem hG_permitH {m0' : Memory} {cT : Loc} {tp : BitVec 64}
    (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64) (v : Val) :
    WakeG.wakeG (HelloGOf2H.GOf2H (RuntimeLayout.ofPlaceW hp i) m0') cT ⟨tp + 16#64, 8⟩ v := by
  subst htp
  refine .inr ?_
  rw [WakeHS.permit_eq]
  exact HelloGOf2H.gOf2H_ne (Spike.Lib.A64.PhRec.pin_ne (by decide)) (HelloGOf2H.pin_ne2H (by decide)) _

/-- **The limit word's values within the room** under
`wakeG (GOf2H L (m0Of …)) cT`, for any `Z` at least stack 0's limit (`hZ`),
the flag word not the limit word (`hcT`; `cT_ne_IH`): `limOk_IH`'s
`hroom`. -/
theorem hroom_limH {cT : Loc} {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64)
    (hcT : (⟨(RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 8#64, 8⟩ : Loc) ≠ cT)
    {Z : BitVec 64} (hZ : (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ Z.toNat) :
    ∀ v : Val, WakeG.wakeG (HelloGOf2H.GOf2H (RuntimeLayout.ofPlaceW hp i)
        (m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs)) cT ⟨tp + 8#64, 8⟩ v →
      (v.setWidth 64).toNat ≤ Z.toNat := by
  subst htp
  intro v hv
  have hg' := Spike.Lib.WakeG.wakeG_off hv hcT
  rw [WakeHS.lim_eq, ← Spike.Lib.A64.Rt.limA_tcb0] at hg'
  exact PlaceW.room_of_le hp i hZ v (HelloGOf2H.gOf_of_gOf2H hg')

/-- **`MainInstH` at hello's root value invariant** `wakeG (GOf2H L (m0Of …))
cT` (`mainInstH_I` with `hG_permitH`, `hroom_limH`; the flag word `cT` in a
placed label at `cS`, `hl`/`ho`/`hT`; `x9`'s address above stack 0's guard,
`hZ`). -/
theorem mainInstH_G (hprog : o.prog = helloProg) (hw : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    {endPc : Int64} (hend : endPc = endOf (RuntimeLayout.ofPlaceW hp i).exe helloProg (RuntimeLayout.ofPlaceW hp i).pfx)
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tq0 tq sp)
    {cT : Loc} {cS : WeakMem.Address} {b : Nat} (hl : lbl cS.label = some b)
    (ho : cS.offset < lsize cS.label) (hT : cT = Scc.Sem.wordLoc (b + 8 * cS.offset))
    {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64)
    {Rm : Region} {m0 : MachineData}
    (hA16 : Mem.loadInt m0.dmem (tp + 16#64) 8 = none)
    (hoff16 : (tp + 16#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 16#64).toNat : Int) + 8 ≤ Rm.base.toNat + -144 ∨ (Rm.base.toNat : Int) + 48 ≤ (tp + 16#64).toNat))
    (hA8 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff8 : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ Rm.base.toNat + -144 ∨ (Rm.base.toNat : Int) + 48 ≤ (tp + 8#64).toNat))
    (hZ : (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -144, 48⟩ : Region).addr (-32)).toNat)
    {w : TermRun.Word} {cA x29 ra : BitVec 64}
    (hsh : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared ⟨cA, 8⟩) (hval : ValRep lbl w.val cA.toNat)
    (hloc : LocRep lbl w.val cA.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    HelloMainHRD.MainInstH (RuntimeLayout.ofPlaceW hp i).exe endPc (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize
      (helloMs (RuntimeLayout.ofPlaceW hp i)
        (WakeG.wakeG (HelloGOf2H.GOf2H (RuntimeLayout.ofPlaceW hp i)
          (m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs)) cT) lbl lsize) m0 Rm cA x29 ra tp w :=
  mainInstH_I hp i hprog hw hend hm htp hA16 hoff16 hA8 hoff8 (hG_permitH hp i htp _)
    (hroom_limH hp i htp (cT_ne_IH hp i hl ho hT hm) hZ) hsh hval hloc hin

end Inst

end Spike.Lib.HelloMainInstD

/-- info: 'Spike.Lib.HelloMainInstD.rd_numH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.rd_numH

/-- info: 'Spike.Lib.HelloMainInstD.hS_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.hS_IH

/-- info: 'Spike.Lib.HelloMainInstD.htp4_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.htp4_IH

/-- info: 'Spike.Lib.HelloMainInstD.cT_ne_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.cT_ne_IH

/-- info: 'Spike.Lib.HelloMainInstD.limOk_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.limOk_IH

/-- info: 'Spike.Lib.HelloMainInstD.htls_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.htls_IH

/-- info: 'Spike.Lib.HelloMainInstD.hexit_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.hexit_IH

/-- info: 'Spike.Lib.HelloMainInstD.mainInstH_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.mainInstH_I

/-- info: 'Spike.Lib.HelloMainInstD.hG_permitH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.hG_permitH

/-- info: 'Spike.Lib.HelloMainInstD.hroom_limH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.hroom_limH

/-- info: 'Spike.Lib.HelloMainInstD.mainInstH_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInstD.mainInstH_G
