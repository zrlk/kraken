import Kraken.X64.Examples.Sbr.SessionBin.Api
import Kraken.X64.Examples.Sbr.SessionBin.WitEnv
import Kraken.X64.Examples.Sbr.SessionBin.WitMemCalls

/-!
# Non-vacuity of the five entry-point theorems

The hypotheses of the five theorems of `Api.lean` are jointly satisfiable: under one ambient code
(`WitEnv.wCE`, the laid-out image of every text of `SbrBinary` and stand-ins for the external
routines), one setup `WitEnv.wS` and one allocator state `WitEnv.wX` (a bump allocator's heap
with room for init's element), each theorem's hypotheses hold of concrete parameters and a
concrete machine state (registers and data memory).

* `init_of`, …, `apply_of`: generic over the code. A memory satisfying an entry point's `h_mem`,
  and the register values, give a machine state meeting all of that theorem's hypotheses.
* `wit_init`, `wit_decode`, `wit_usac`, `wit_config`, `wit_apply`: at the witness environment.
  The pieces come from `WitImage` (`wPlaced`), `WitEnv` (`wInitExt`, `wEnvOK`, `wStackBound`)
  and `WitMemCalls` (the memories). The element of the four post-init theorems is in the state
  `ff_aac_sbr_ctx_alloc_init` leaves (`SReach.init`); it is not obtained by running init.
* `wit_session`: all five at once, stated only in the specification's vocabulary.
* `wit_init_success`: init's allocations can succeed. The stand-in `av_mallocz` returns a
  non-null block from the witnessed heap, and the stand-in `av_tx_init` returns `0`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init

namespace Kraken.Examples.Sbr.SessionBin.Wit

/-! ## Machine states from register values and a memory -/

/-- The registers of a call: `rdi`, `rsi`, `rdx`, `rcx`, `r8` and `rsp`; the others 0. -/
def callRegs (rdi rsi rdx rcx r8 rsp : BitVec 64) : Reg64s :=
  { rdi := .ofBitVec rdi, rsi := .ofBitVec rsi, rdx := .ofBitVec rdx, rcx := .ofBitVec rcx,
    r8 := .ofBitVec r8, rsp := .ofBitVec rsp }

/-- The call state with these registers and the data memory `m`. -/
def callState (rdi rsi rdx rcx r8 rsp : BitVec 64) (m : Mem 64) : MachineData :=
  { regs := callRegs rdi rsi rdx rcx r8 rsp, dmem := m }

section
variable {rdi rsi rdx rcx r8 rsp : BitVec 64} {m : Mem 64}

theorem callState_rdi : (callState rdi rsi rdx rcx r8 rsp m).regs.get64 .rdi = rdi := by
  simp [callState, callRegs, Reg64s.get64]
theorem callState_rsi : (callState rdi rsi rdx rcx r8 rsp m).regs.get64 .rsi = rsi := by
  simp [callState, callRegs, Reg64s.get64]
theorem callState_rdx : (callState rdi rsi rdx rcx r8 rsp m).regs.get64 .rdx = rdx := by
  simp [callState, callRegs, Reg64s.get64]
theorem callState_rcx : (callState rdi rsi rdx rcx r8 rsp m).regs.get64 .rcx = rcx := by
  simp [callState, callRegs, Reg64s.get64]
theorem callState_r8 : (callState rdi rsi rdx rcx r8 rsp m).regs.get64 .r8 = r8 := by
  simp [callState, callRegs, Reg64s.get64]
theorem callState_rsp : (callState rdi rsi rdx rcx r8 rsp m).regs.get64 .rsp = rsp := by
  simp [callState, callRegs, Reg64s.get64]
theorem callState_dmem : (callState rdi rsi rdx rcx r8 rsp m).dmem = m := rfl

end

theorem setWidth_32_64 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  simp

/-! ## From a memory to all hypotheses of a theorem

For each theorem of `Api.lean`: given its assumptions on the code and the setup, the pure side
conditions, and a memory satisfying its `h_mem`, a machine state meets all of its hypotheses.
The conclusions are the theorems' hypotheses, verbatim, under `∃`. -/

section Generic
variable [CodeEnv] {S : Setup}

theorem init_of {X : Mem 64 → Prop} (h_bin : SbrBinary) (h_ext : InitExt S X)
    (ac che_slot : BitVec 64) (id_aac : BitVec 32) (avctx fdsp : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64)
    (hm : ∃ m : Mem 64, m =⋆
        StackAt ra sp (initStack S.k)
      ⋆ AcInit S ac avctx fdsp er ps
      ⋆ 8 ?@ che_slot
      ⋆ SharedData S
      ⋆ X
      ⋆ Rest) :
    SbrBinary ∧ InitExt S X ∧
    ∃ (ac che_slot : BitVec 64) (id_aac : BitVec 32) (avctx fdsp : BitVec 64) (er ps : BitVec 32)
      (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
      t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che_slot
      ∧ (t.regs.get64 .rdx).setWidth 32 = id_aac ∧ t.regs.get64 .rsp = sp
      ∧ t.dmem =⋆
          StackAt ra sp (initStack S.k)
        ⋆ AcInit S ac avctx fdsp er ps
        ⋆ 8 ?@ che_slot
        ⋆ SharedData S
        ⋆ X
        ⋆ Rest := by
  obtain ⟨m, hm⟩ := hm
  exact ⟨h_bin, h_ext, ac, che_slot, id_aac, avctx, fdsp, er, ps, sp, Rest, ra,
    callState ac che_slot (id_aac.setWidth 64) 0 0 sp m, callState_rdi, callState_rsi,
    by rw [callState_rdx, setWidth_32_64], callState_rsp, hm⟩

theorem decode_of (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che gb : BitVec 64) (cnt : BitVec 32) (avctx : BitVec 64) (er ps : BitVec 32)
    (buf : BitVec 64) (i sib p8 pad : BitVec 32) (L : Nat)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64)
    (h_align : StackAligned sp) (h_rd : ReaderOK i p8 L)
    (hm : ∃ m : Mem 64, m =⋆
        StackAt ra sp (decStack S.k)
      ⋆ SbrInitialized S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ DecReader gb buf i sib p8 pad L
      ⋆ DecScratch ac avctx
      ⋆ Rest) :
    SbrBinary ∧ StackBound S ∧
    ∃ (ac che gb : BitVec 64) (cnt : BitVec 32) (avctx : BitVec 64) (er ps : BitVec 32)
      (buf : BitVec 64) (i sib p8 pad : BitVec 32) (L : Nat)
      (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
      t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
      ∧ t.regs.get64 .rdx = gb ∧ (t.regs.get64 .r8).setWidth 32 = cnt
      ∧ t.regs.get64 .rsp = sp ∧ StackAligned sp ∧ ReaderOK i p8 L
      ∧ t.dmem =⋆
          StackAt ra sp (decStack S.k)
        ⋆ SbrInitialized S che ac
        ⋆ AcFields ac avctx er ps
        ⋆ DecReader gb buf i sib p8 pad L
        ⋆ DecScratch ac avctx
        ⋆ Rest := by
  obtain ⟨m, hm⟩ := hm
  exact ⟨h_bin, h_stk, ac, che, gb, cnt, avctx, er, ps, buf, i, sib, p8, pad, L, sp, Rest, ra,
    callState ac che gb 0 (cnt.setWidth 64) sp m, callState_rdi, callState_rsi, callState_rdx,
    by rw [callState_r8, setWidth_32_64], callState_rsp,
    h_align, h_rd, hm⟩

theorem usac_of (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che ue gb : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (buf : BitVec 64) (i p8 : BitVec 32) (L : Nat) (uev : List UInt8)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64)
    (h_align : StackAligned sp) (h_rd : ReaderOK i p8 L) (h_uev : UsacSbrOK uev)
    (hm : ∃ m : Mem 64, m =⋆
        StackAt ra sp (usacStack S.k)
      ⋆ SbrInitialized S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ UsacReader gb buf i p8 L
      ⋆ uev =@ (ue + 0xc#64)
      ⋆ Rest) :
    SbrBinary ∧ StackBound S ∧
    ∃ (ac che ue gb : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
      (buf : BitVec 64) (i p8 : BitVec 32) (L : Nat) (uev : List UInt8)
      (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
      t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
      ∧ t.regs.get64 .rdx = ue ∧ t.regs.get64 .rcx = gb
      ∧ t.regs.get64 .rsp = sp ∧ StackAligned sp
      ∧ ReaderOK i p8 L ∧ UsacSbrOK uev
      ∧ t.dmem =⋆
          StackAt ra sp (usacStack S.k)
        ⋆ SbrInitialized S che ac
        ⋆ AcFields ac avctx er ps
        ⋆ UsacReader gb buf i p8 L
        ⋆ uev =@ (ue + 0xc#64)
        ⋆ Rest := by
  obtain ⟨m, hm⟩ := hm
  exact ⟨h_bin, h_stk, ac, che, ue, gb, avctx, er, ps, buf, i, p8, L, uev, sp, Rest, ra,
    callState ac che ue gb 0 sp m, callState_rdi, callState_rsi, callState_rdx, callState_rcx,
    callState_rsp,
    h_align, h_rd, h_uev, hm⟩

theorem config_of (h_bin : SbrBinary)
    (ac che : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64)
    (hm : ∃ m : Mem 64, m =⋆
        StackAt ra sp 0
      ⋆ SbrInitialized S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ Rest) :
    SbrBinary ∧
    ∃ (ac che : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
      (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
      t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
      ∧ t.regs.get64 .rsp = sp
      ∧ t.dmem =⋆
          StackAt ra sp 0
        ⋆ SbrInitialized S che ac
        ⋆ AcFields ac avctx er ps
        ⋆ Rest := by
  obtain ⟨m, hm⟩ := hm
  exact ⟨h_bin, ac, che, avctx, er, ps, sp, Rest, ra, callState ac che 0 0 0 sp m,
    callState_rdi, callState_rsi, callState_rsp, hm⟩

theorem apply_of (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che L R : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64)
    (h_align : StackAligned sp) (h_out : isAligned 32 L = true ∧ isAligned 32 R = true)
    (hm : ∃ m : Mem 64, m =⋆
        StackAt ra sp (applyStack S.k)
      ⋆ SbrReady S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R
      ⋆ Rest) :
    SbrBinary ∧ StackBound S ∧
    ∃ (ac che L R : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
      (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
      t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
      ∧ t.regs.get64 .rcx = L ∧ t.regs.get64 .r8 = R
      ∧ t.regs.get64 .rsp = sp ∧ StackAligned sp
      ∧ (isAligned 32 L = true ∧ isAligned 32 R = true)
      ∧ t.dmem =⋆
          StackAt ra sp (applyStack S.k)
        ⋆ SbrReady S che ac
        ⋆ AcFields ac avctx er ps
        ⋆ OutBuffers L R
        ⋆ Rest := by
  obtain ⟨m, hm⟩ := hm
  exact ⟨h_bin, h_stk, ac, che, L, R, avctx, er, ps, sp, Rest, ra, callState ac che 0 L R sp m,
    callState_rdi, callState_rsi, callState_rcx, callState_r8, callState_rsp, h_align, h_out, hm⟩

end Generic

/-! ## The five theorems' hypotheses, jointly, at one environment

One ambient code `WitEnv.wCE`, one setup `WitEnv.wS`, one allocator state `WitEnv.wX`. Each
theorem states the corresponding `Api.lean` theorem's assumptions and hypotheses, verbatim, at
concrete values. -/

section Concrete
open Kraken.Examples.Sbr.WitEnv Kraken.Examples.Sbr.WitMem
attribute [local instance] wLayout wCE

/-- **`ff_aac_sbr_ctx_alloc_init_spec`'s hypotheses hold.** -/
theorem wit_init :
    SbrBinary ∧ InitExt wS wX ∧
    ∃ (ac che_slot : BitVec 64) (id_aac : BitVec 32) (avctx fdsp : BitVec 64) (er ps : BitVec 32)
      (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
      t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che_slot
      ∧ (t.regs.get64 .rdx).setWidth 32 = id_aac ∧ t.regs.get64 .rsp = sp
      ∧ t.dmem =⋆
          StackAt ra sp (initStack wS.k)
        ⋆ AcInit wS ac avctx fdsp er ps
        ⋆ 8 ?@ che_slot
        ⋆ SharedData wS
        ⋆ wX
        ⋆ Rest :=
  init_of wPlaced wInitExt acW cheSlotW idW avctxW fdspW erW psW spW RestW raW mem_init

/-- **`ff_aac_sbr_decode_extension_spec`'s hypotheses hold.** -/
theorem wit_decode :
    SbrBinary ∧ StackBound wS ∧
    ∃ (ac che gb : BitVec 64) (cnt : BitVec 32) (avctx : BitVec 64) (er ps : BitVec 32)
      (buf : BitVec 64) (i sib p8 pad : BitVec 32) (L : Nat)
      (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
      t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
      ∧ t.regs.get64 .rdx = gb ∧ (t.regs.get64 .r8).setWidth 32 = cnt
      ∧ t.regs.get64 .rsp = sp ∧ StackAligned sp ∧ ReaderOK i p8 L
      ∧ t.dmem =⋆
          StackAt ra sp (decStack wS.k)
        ⋆ SbrInitialized wS che ac
        ⋆ AcFields ac avctx er ps
        ⋆ DecReader gb buf i sib p8 pad L
        ⋆ DecScratch ac avctx
        ⋆ Rest :=
  decode_of wPlaced wStackBound acW cheW gbW 0 avctxW erW psW bufW iW sibW p8W padW LW spW RestW raW
    spW_aligned readerOK_W (mem_dec wEnvOK)

/-- **`ff_aac_sbr_decode_usac_data_spec`'s hypotheses hold.** -/
theorem wit_usac :
    SbrBinary ∧ StackBound wS ∧
    ∃ (ac che ue gb : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
      (buf : BitVec 64) (i p8 : BitVec 32) (L : Nat) (uev : List UInt8)
      (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
      t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
      ∧ t.regs.get64 .rdx = ue ∧ t.regs.get64 .rcx = gb
      ∧ t.regs.get64 .rsp = sp ∧ StackAligned sp
      ∧ ReaderOK i p8 L ∧ UsacSbrOK uev
      ∧ t.dmem =⋆
          StackAt ra sp (usacStack wS.k)
        ⋆ SbrInitialized wS che ac
        ⋆ AcFields ac avctx er ps
        ⋆ UsacReader gb buf i p8 L
        ⋆ uev =@ (ue + 0xc#64)
        ⋆ Rest :=
  usac_of wPlaced wStackBound acW cheW ueW gbW avctxW erW psW bufW iW p8W LW uevW spW RestW raW
    spW_aligned readerOK_W usacSbrOK_W (mem_usac wEnvOK)

/-- **`ff_aac_sbr_config_usac_spec`'s hypotheses hold.** -/
theorem wit_config :
    SbrBinary ∧
    ∃ (ac che : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
      (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
      t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
      ∧ t.regs.get64 .rsp = sp
      ∧ t.dmem =⋆
          StackAt ra sp 0
        ⋆ SbrInitialized wS che ac
        ⋆ AcFields ac avctx er ps
        ⋆ Rest :=
  config_of wPlaced acW cheW avctxW erW psW spW RestW raW (mem_config wEnvOK)

/-- **`ff_aac_sbr_apply_spec`'s hypotheses hold.** -/
theorem wit_apply :
    SbrBinary ∧ StackBound wS ∧
    ∃ (ac che L R : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
      (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
      t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
      ∧ t.regs.get64 .rcx = L ∧ t.regs.get64 .r8 = R
      ∧ t.regs.get64 .rsp = sp ∧ StackAligned sp
      ∧ (isAligned 32 L = true ∧ isAligned 32 R = true)
      ∧ t.dmem =⋆
          StackAt ra sp (applyStack wS.k)
        ⋆ SbrReady wS che ac
        ⋆ AcFields ac avctx er ps
        ⋆ OutBuffers L R
        ⋆ Rest :=
  apply_of wPlaced wStackBound acW cheW outLW outRW avctxW erW psW spW RestW raW spW_aligned out_aligned
    (mem_apply wEnvOK)

end Concrete

/-! ## All five at once -/

section Session
open Kraken.Examples.Sbr.WitEnv
attribute [local instance] wLayout

/-- **One code, one setup, one allocator state for all five theorems.** For some ambient code
`C`, setup `S` and state `X`: the code is the binary's (`SbrBinary`), init's externals meet their
contracts (`InitExt S X`), the stack bound holds (`StackBound S`), and for each of the five
theorems of `Api.lean` there are parameters and a machine state meeting all its hypotheses. -/
theorem wit_session :
    ∃ (C : CodeEnv) (S : Setup) (X : Mem 64 → Prop), letI := C;
    SbrBinary ∧ InitExt S X ∧ StackBound S
    -- `ff_aac_sbr_ctx_alloc_init_spec`
    ∧ (∃ (ac che_slot : BitVec 64) (id_aac : BitVec 32) (avctx fdsp : BitVec 64)
        (er ps : BitVec 32) (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64)
        (t : MachineData),
        t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che_slot
        ∧ (t.regs.get64 .rdx).setWidth 32 = id_aac ∧ t.regs.get64 .rsp = sp
        ∧ t.dmem =⋆
            StackAt ra sp (initStack S.k)
          ⋆ AcInit S ac avctx fdsp er ps
          ⋆ 8 ?@ che_slot
          ⋆ SharedData S
          ⋆ X
          ⋆ Rest)
    -- `ff_aac_sbr_decode_extension_spec`
    ∧ (∃ (ac che gb : BitVec 64) (cnt : BitVec 32) (avctx : BitVec 64) (er ps : BitVec 32)
        (buf : BitVec 64) (i sib p8 pad : BitVec 32) (L : Nat)
        (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
        t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
        ∧ t.regs.get64 .rdx = gb ∧ (t.regs.get64 .r8).setWidth 32 = cnt
        ∧ t.regs.get64 .rsp = sp ∧ StackAligned sp ∧ ReaderOK i p8 L
        ∧ t.dmem =⋆
            StackAt ra sp (decStack S.k)
          ⋆ SbrInitialized S che ac
          ⋆ AcFields ac avctx er ps
          ⋆ DecReader gb buf i sib p8 pad L
          ⋆ DecScratch ac avctx
          ⋆ Rest)
    -- `ff_aac_sbr_decode_usac_data_spec`
    ∧ (∃ (ac che ue gb : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
        (buf : BitVec 64) (i p8 : BitVec 32) (L : Nat) (uev : List UInt8)
        (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
        t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
        ∧ t.regs.get64 .rdx = ue ∧ t.regs.get64 .rcx = gb
        ∧ t.regs.get64 .rsp = sp ∧ StackAligned sp
        ∧ ReaderOK i p8 L ∧ UsacSbrOK uev
        ∧ t.dmem =⋆
            StackAt ra sp (usacStack S.k)
          ⋆ SbrInitialized S che ac
          ⋆ AcFields ac avctx er ps
          ⋆ UsacReader gb buf i p8 L
          ⋆ uev =@ (ue + 0xc#64)
          ⋆ Rest)
    -- `ff_aac_sbr_config_usac_spec`
    ∧ (∃ (ac che : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
        (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
        t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
        ∧ t.regs.get64 .rsp = sp
        ∧ t.dmem =⋆
            StackAt ra sp 0
          ⋆ SbrInitialized S che ac
          ⋆ AcFields ac avctx er ps
          ⋆ Rest)
    -- `ff_aac_sbr_apply_spec`
    ∧ (∃ (ac che L R : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
        (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData),
        t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che
        ∧ t.regs.get64 .rcx = L ∧ t.regs.get64 .r8 = R
        ∧ t.regs.get64 .rsp = sp ∧ StackAligned sp
        ∧ (isAligned 32 L = true ∧ isAligned 32 R = true)
        ∧ t.dmem =⋆
            StackAt ra sp (applyStack S.k)
          ⋆ SbrReady S che ac
          ⋆ AcFields ac avctx er ps
          ⋆ OutBuffers L R
          ⋆ Rest) :=
  ⟨wCE, wS, wX, wPlaced, wInitExt, wStackBound, wit_init.2.2, wit_decode.2.2, wit_usac.2.2,
    wit_config.2, wit_apply.2.2⟩

end Session

/-! ## Init's success branch is reachable -/

section Success
open Kraken.Examples.Sbr.WitEnv Kraken.Examples.Sbr.WitMem
attribute [local instance] wLayout wCE

/-- `wit_init`'s memory, with the allocator's heap in its first state `wXAt wHeapStart` (the
pointer cell holds `wHeapStart`, the whole heap `[wHeapStart, wHeapEnd)` free). -/
theorem mem_init_at : ∃ m : Mem 64, m =⋆
      StackAt raW spW (initStack wS.k)
    ⋆ AcInit wS acW avctxW fdspW erW psW
    ⋆ 8 ?@ cheSlotW
    ⋆ SharedData wS
    ⋆ wXAt wHeapStart
    ⋆ RestW := by
  have hX : Witness.SatIn (wXAt wHeapStart) [(0x400000000, 0x400000008), (0x400001000, 0x400101000)] := by
    unfold wXAt
    exact Witness.SatIn.sep (Witness.SatIn.val (Int.toBytes_length _ _) (by decide +kernel))
      (Witness.SatIn.sep (Witness.SatIn.block (Nat.le_refl _) (by decide +kernel)) sat_true
        (by decide +kernel)) (by decide +kernel)
  obtain ⟨m, hm, -⟩ := Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep
    (Witness.SatIn.sep (Witness.SatIn.sep sat_stackInit sat_acInit (by decide +kernel))
      (Witness.SatIn.block (n := 8) (a := cheSlotW) (Nat.le_refl _) (by decide +kernel))
      (by decide +kernel)) sat_shared (by decide +kernel)) hX (by decide +kernel))
    Witness.SatIn.emp (by decide +kernel)
  exact ⟨m, hm⟩

/-- The heap's first state is a state of `wX`. -/
theorem wXAt_start_wX {m : Mem 64} (h : wXAt wHeapStart m) : wX m :=
  ⟨wHeapStart, by decide, by decide, h⟩

/-- **Init's success branch is reachable at the witness environment.** This is about the
stand-ins' behaviour, not a run of `ff_aac_sbr_ctx_alloc_init`. `InitExt wS wX` (`wInitExt`)
allows `av_mallocz` to fail and `av_tx_init` to fail; here the stand-ins are shown to succeed:

1. a memory meeting `wit_init`'s `h_mem` exists in which the heap is in its first state
   `wXAt wHeapStart` (`mem_init_at`; that state is a state of `wX`, so this is an instance of
   `wit_init`'s memory);
2. init's request, `0x88ba0` bytes, is at most `0x100000`;
3. from the heap state `wXAt wHeapStart`, the stand-in `av_mallocz(n)` with `n ≤ 0x100000`
   returns `wHeapStart`, which is not `NULL`, with `n` zero bytes there and the heap back in a
   state of `wX` (`AvMalloczSpec`'s success disjunct);
4. the stand-in `av_tx_init` returns `0` from any state meeting `AvTxInitSpec`'s precondition,
   with `*ctx = 0` (the context `wEnv.Ctx 0` owns nothing) and `*tx = tx_stub`. Both of init's
   `av_tx_init` calls therefore succeed.

Not shown: that `ff_aac_sbr_ctx_alloc_init` as a whole returns `0` in a particular run.
`ff_aac_sbr_ctx_alloc_init_spec` allows the failure branches. -/
theorem wit_init_success :
    (∃ m : Mem 64, m =⋆
        StackAt raW spW (initStack wS.k)
      ⋆ AcInit wS acW avctxW fdspW erW psW
      ⋆ 8 ?@ cheSlotW
      ⋆ SharedData wS
      ⋆ wXAt wHeapStart
      ⋆ RestW)
    ∧ (∀ m, wXAt wHeapStart m → wX m)
    ∧ 0x88ba0 ≤ 0x100000
    ∧ cenv.ProcSpec (entry "av_mallocz")
        (fun (R : Mem 64 → Prop) ra t => (arg0 t).toNat ≤ 0x100000
          ∧ CallPre wS.k (wXAt wHeapStart ⋆ R) ra t)
        (fun R ra t s => s.regs.get64 .rax = wHeapStart ∧ wHeapStart ≠ 0#64
          ∧ CallPost wS.k ((Session.zs (arg0 t).toNat =@ wHeapStart ⋆ wX) ⋆ R) ra t s)
    ∧ cenv.ProcSpec (entry "av_tx_init")
        (fun (R : Mem 64 → Prop) ra t =>
          CallPre wS.k ((8 ?@ arg0 t ⋆ (8 ?@ arg1 t ⋆ Init.TxIn wS.env.TxTab wX t)) ⋆ R) ra t)
        (fun R ra t s => s.regs.get64 .rax = 0#64
          ∧ CallPost wS.k (TxOkF wS.env.TxTab wX t ⋆ R) ra t s) :=
  ⟨mem_init_at, fun _ => wXAt_start_wX, by decide, wMalloczOk wS.k,
    wTxInitOk wS.env.TxTab wX wS.k⟩

end Success

end Kraken.Examples.Sbr.SessionBin.Wit
