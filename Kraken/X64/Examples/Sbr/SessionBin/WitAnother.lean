import Kraken.X64.Examples.Sbr.SessionBin.Witness

/-!
# Non-vacuity of init with an element already there

The hypotheses of `ff_aac_sbr_ctx_alloc_init_another_spec` and
`ff_aac_sbr_ctx_alloc_init_another_ready_spec` hold together, at the witness of
`Witness.lean` (`wit_session`'s code `wCE`, setup `wS` and allocator state `wX`): the stack, an
element at `cheW` in the state init leaves (initialized and ready), `*ac`'s three fields, the
slot `*che_slot` and the allocator's heap (`[wHeapStart, wHeapEnd)`, 1 MiB, with room for a second
element's `0x88ba0` bytes) are disjoint regions of one memory. As in `Witness.lean`, the element
is in the state init leaves; it is not obtained by running init.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init

namespace Kraken.Examples.Sbr.SessionBin.Wit

section Concrete
open Kraken.Examples.Sbr.WitEnv Kraken.Examples.Sbr.WitMem
attribute [local instance] wLayout wCE

/-- The memory of init with an element already there, with the element `E` (initialized or
ready) at `cheW`. -/
theorem mem_another {E : Mem 64 → Prop} (hE : Witness.SatIn E elemL) : ∃ m : Mem 64, m =⋆
      StackAt raW spW (initStack wS.k)
    ⋆ E
    ⋆ AcFields acW avctxW erW psW
    ⋆ 8 ?@ cheSlotW
    ⋆ wX
    ⋆ RestW := by
  obtain ⟨m, hm, -⟩ := Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep
    (Witness.SatIn.sep (Witness.SatIn.sep sat_stackInit hE (by decide +kernel))
      sat_acFields (by decide +kernel))
      (Witness.SatIn.block (n := 8) (a := cheSlotW) (Nat.le_refl _) (by decide +kernel))
      (by decide +kernel)) sat_wX (by decide +kernel))
    Witness.SatIn.emp (by decide +kernel)
  exact ⟨m, hm⟩

/-- The machine state of a call with these registers and a memory `m` meets the register
equations of init. -/
theorem regs_init (ac che_slot sp : BitVec 64) (id_aac : BitVec 32) (m : Mem 64) :
    (callState ac che_slot (id_aac.setWidth 64) 0 0 sp m).regs.get64 .rdi = ac
    ∧ (callState ac che_slot (id_aac.setWidth 64) 0 0 sp m).regs.get64 .rsi = che_slot
    ∧ ((callState ac che_slot (id_aac.setWidth 64) 0 0 sp m).regs.get64 .rdx).setWidth 32
        = id_aac
    ∧ (callState ac che_slot (id_aac.setWidth 64) 0 0 sp m).regs.get64 .rsp = sp :=
  ⟨callState_rdi, callState_rsi, by rw [callState_rdx, setWidth_32_64], callState_rsp⟩

end Concrete

section Session
open Kraken.Examples.Sbr.WitEnv Kraken.Examples.Sbr.WitMem
attribute [local instance] wLayout

/-- **Init with an element already there: the hypotheses hold.** For some ambient code `C`,
setup `S` and allocator state `X`: the code is the binary's (`SbrBinary`), init's externals meet
their contracts (`InitExt S X`), and there are parameters and a machine state meeting all
hypotheses of `ff_aac_sbr_ctx_alloc_init_another_spec` (an initialized element) and, at the same
code, setup and state, of `ff_aac_sbr_ctx_alloc_init_another_ready_spec` (a ready element). -/
theorem wit_init_another :
    ∃ (C : CodeEnv) (S : Setup) (X : Mem 64 → Prop), letI := C;
    SbrBinary ∧ InitExt S X
    -- `ff_aac_sbr_ctx_alloc_init_another_spec`
    ∧ (∃ (ac che₁ che_slot : BitVec 64) (id_aac : BitVec 32) (avctx : BitVec 64)
        (er ps : BitVec 32) (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64)
        (t : MachineData),
        t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che_slot
        ∧ (t.regs.get64 .rdx).setWidth 32 = id_aac ∧ t.regs.get64 .rsp = sp
        ∧ t.dmem =⋆
            StackAt ra sp (initStack S.k)
          ⋆ SbrInitialized S che₁ ac
          ⋆ AcFields ac avctx er ps
          ⋆ 8 ?@ che_slot
          ⋆ X
          ⋆ Rest)
    -- `ff_aac_sbr_ctx_alloc_init_another_ready_spec`
    ∧ (∃ (ac che₁ che_slot : BitVec 64) (id_aac : BitVec 32) (avctx : BitVec 64)
        (er ps : BitVec 32) (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64)
        (t : MachineData),
        t.regs.get64 .rdi = ac ∧ t.regs.get64 .rsi = che_slot
        ∧ (t.regs.get64 .rdx).setWidth 32 = id_aac ∧ t.regs.get64 .rsp = sp
        ∧ t.dmem =⋆
            StackAt ra sp (initStack S.k)
          ⋆ SbrReady S che₁ ac
          ⋆ AcFields ac avctx er ps
          ⋆ 8 ?@ che_slot
          ⋆ X
          ⋆ Rest) := by
  letI := wCE
  obtain ⟨m1, h1⟩ := mem_another (sat_initialized wEnvOK)
  obtain ⟨m2, h2⟩ := mem_another (sat_ready wEnvOK)
  obtain ⟨r1, r2, r3, r4⟩ := regs_init acW cheSlotW spW idW m1
  obtain ⟨s1, s2, s3, s4⟩ := regs_init acW cheSlotW spW idW m2
  exact ⟨wCE, wS, wX, wPlaced, wInitExt,
    ⟨acW, cheW, cheSlotW, idW, avctxW, erW, psW, spW, RestW, raW, _, r1, r2, r3, r4, h1⟩,
    ⟨acW, cheW, cheSlotW, idW, avctxW, erW, psW, spW, RestW, raW, _, s1, s2, s3, s4, h2⟩⟩

end Session

end Kraken.Examples.Sbr.SessionBin.Wit
