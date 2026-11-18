import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# The statements, for `lake challenge`

The top theorems, the per-procedure theorems and the satisfiability of their hypotheses,
stated over the specification alone, each with `sorry` as its proof.
`lake challenge --config scripts/sbr/challenge.json` checks that
`KrakenSbrChallenge/Solution.lean` proves each with the same statement, using only the permitted
axioms, and replays the proofs through the kernel in a separate process. This library is outside
`Kraken/` (its own `lean_lib`, not a default target), so the `sorry`s here are not part of the
proof; `scripts/sbr/challenge.sh` checks that they are the only proofs in this file.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init

namespace Kraken.Examples.Sbr

variable [CodeEnv]

theorem ff_aac_sbr_apply_linked (hpl : SbrPlaced) (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env)
    (hslots : SbrSlots e) (hasm : SbrAssumed k e) : ApplySpec k e := by
  sorry

end Kraken.Examples.Sbr

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

theorem sbr_session_safe (B : SbrBinary) (S : Setup) (X : Mem 64 → Prop) (hx : InitExt S X)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) :
    InitSafe S X ∧ DecSafe S ∧ UsacSafe S ∧ ConfigSafe S ∧ ApplySafe S := by
  sorry

end Kraken.Examples.Sbr.SessionBin

/-! ## The per-procedure theorems (`SessionBin/Api.lean`) -/

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

theorem SbrReady.initialized {S : Setup} {che ac : BitVec 64} {m : Mem 64}
    (h : SbrReady S che ac m) : SbrInitialized S che ac m := by
  sorry

theorem ff_aac_sbr_ctx_alloc_init_spec {S : Setup} {X : Mem 64 → Prop}
    (h_bin : SbrBinary) (h_ext : InitExt S X)
    (ac che_slot : BitVec 64) (id_aac : BitVec 32) (avctx fdsp : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che_slot)
    (h_id : (t.regs.get64 .rdx).setWidth 32 = id_aac) (h_sp : t.regs.get64 .rsp = sp)
    (h_mem : t.dmem =⋆
        StackAt ra sp (initStack S.k)          -- return address; free stack below
      ⋆ AcInit S ac avctx fdsp er ps           -- *ac as the AAC decoder set it up
      ⋆ 8 ?@ che_slot                          -- the slot for the new pointer
      ⋆ SharedData S                           -- tables and state shared with the element
      ⋆ X                                      -- the allocator's and transforms' state
      ⋆ Rest) :                                -- everything else the caller owns
    Returns "ff_aac_sbr_ctx_alloc_init" t ra (fun s => AbiReturn t s ∧
      ((ret32 s = 0#32 ∧ ∃ p : BitVec 64, s.dmem =⋆
            StackAfter sp (initStack S.k)      -- the stack region, back
          ⋆ SbrInitialized S p ac              -- the new element
          ⋆ AcFields ac avctx er ps            -- *ac's three fields
          ⋆ PtrAt che_slot p                   -- *che_slot = p
          ⋆ X
          ⋆ Rest)                              -- holds again (see `..._keeps_the_rest`)
      ∨ ((ret32 s).toInt < 0 ∧ s.dmem =⋆
            StackAfter sp (initStack S.k)
          ⋆ InitFailed S che_slot id_aac       -- what the failed call left
          ⋆ AcInit S ac avctx fdsp er ps
          ⋆ SharedData S
          ⋆ X
          ⋆ Rest))) := by
  sorry

theorem ff_aac_sbr_decode_extension_spec {S : Setup}
    (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che gb : BitVec 64) (cnt : BitVec 32) (avctx : BitVec 64) (er ps : BitVec 32)
    (buf : BitVec 64) (i sib p8 pad : BitVec 32) (L : Nat)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_gb : t.regs.get64 .rdx = gb) (h_cnt : (t.regs.get64 .r8).setWidth 32 = cnt)
    (h_sp : t.regs.get64 .rsp = sp) (h_align : StackAligned sp) (h_rd : ReaderOK i p8 L)
    (h_mem : t.dmem =⋆
        StackAt ra sp (decStack S.k)           -- return address; free stack below
      ⋆ SbrInitialized S che ac                -- the element
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ DecReader gb buf i sib p8 pad L        -- *gb and its buffer
      ⋆ DecScratch ac avctx                    -- fields decode may overwrite
      ⋆ Rest) :                                -- everything else the caller owns
    ReturnsOrTraps "ff_aac_sbr_decode_extension" t ra (fun s => AbiReturn t s
      ∧ ret32 s = cnt ∧ ∃ (i' er' : BitVec 32), ReaderOK i' p8 L ∧ s.dmem =⋆
          StackAfter sp (decStack S.k)         -- the stack region, back
        ⋆ SbrReady S che ac                    -- the element, now ready
        ⋆ AcFields ac avctx er' ps             -- ext_sample_rate may change
        ⋆ DecReader gb buf i' sib p8 pad L     -- index advanced, in bounds; bytes unspecified
        ⋆ DecScratch ac avctx                  -- contents unspecified
        ⋆ Rest) := by                          -- holds again (see `..._keeps_the_rest`)
  sorry

theorem ff_aac_sbr_decode_usac_data_spec {S : Setup}
    (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che ue gb : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (buf : BitVec 64) (i p8 : BitVec 32) (L : Nat) (uev : List UInt8)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_ue : t.regs.get64 .rdx = ue) (h_gb : t.regs.get64 .rcx = gb)
    (h_sp : t.regs.get64 .rsp = sp) (h_align : StackAligned sp)
    (h_rd : ReaderOK i p8 L) (h_uev : UsacSbrOK uev)
    (h_mem : t.dmem =⋆
        StackAt ra sp (usacStack S.k)          -- return address; free stack below
      ⋆ SbrInitialized S che ac                -- the element
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ UsacReader gb buf i p8 L               -- *gb and its buffer
      ⋆ uev =@ (ue + 0xc#64)                   -- ue->sbr, twelve bytes
      ⋆ Rest) :                                -- everything else the caller owns
    ReturnsOrTraps "ff_aac_sbr_decode_usac_data" t ra (fun s => AbiReturn t s
      ∧ ∃ i' : BitVec 32, ReaderOK i' p8 L ∧
        ((ret32 s = 0#32 ∧ s.dmem =⋆
            StackAfter sp (usacStack S.k)
          ⋆ SbrReady S che ac                  -- result 0: the element is ready
          ⋆ AcFields ac avctx er ps
          ⋆ UsacReader gb buf i' p8 L          -- index advanced, in bounds
          ⋆ uev =@ (ue + 0xc#64)
          ⋆ Rest)
        ∨ (ret32 s ≠ 0#32 ∧ s.dmem =⋆
            StackAfter sp (usacStack S.k)
          ⋆ SbrInitialized S che ac            -- otherwise: still initialized
          ⋆ AcFields ac avctx er ps
          ⋆ UsacReader gb buf i' p8 L
          ⋆ uev =@ (ue + 0xc#64)
          ⋆ Rest))) := by
  sorry

theorem ff_aac_sbr_config_usac_spec {S : Setup} (h_bin : SbrBinary)
    (ac che : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_sp : t.regs.get64 .rsp = sp)
    (h_mem : t.dmem =⋆
        StackAt ra sp 0                        -- return address only
      ⋆ SbrInitialized S che ac                -- the element
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ Rest) :                                -- everything else the caller owns
    Returns "ff_aac_sbr_config_usac" t ra (fun s => AbiReturn t s ∧ ret32 s = 0#32 ∧ s.dmem =⋆
        StackAfter sp 0
      ⋆ SbrReady S che ac                      -- the element, now ready
      ⋆ AcFields ac avctx er ps
      ⋆ Rest) := by                            -- holds again (see `..._keeps_the_rest`)
  sorry

theorem ff_aac_sbr_apply_spec {S : Setup}
    (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che L R : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_L : t.regs.get64 .rcx = L) (h_R : t.regs.get64 .r8 = R)
    (h_sp : t.regs.get64 .rsp = sp) (h_align : StackAligned sp)
    (h_out : isAligned 32 L = true ∧ isAligned 32 R = true)
    (h_mem : t.dmem =⋆
        StackAt ra sp (applyStack S.k)         -- return address; free stack below
      ⋆ SbrReady S che ac                      -- the element, ready
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ OutBuffers L R                         -- the output buffers
      ⋆ Rest) :                                -- everything else the caller owns
    Returns "ff_aac_sbr_apply" t ra (fun s => AbiReturn t s ∧ s.dmem =⋆
        StackAfter sp (applyStack S.k)
      ⋆ SbrReady S che ac                      -- still ready
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R                         -- written, contents unspecified
      ⋆ Rest) := by                            -- holds again (see `..._keeps_the_rest`)
  sorry

theorem ff_aac_sbr_apply_only_its_regions {S : Setup}
    (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che L R : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_L : t.regs.get64 .rcx = L) (h_R : t.regs.get64 .r8 = R)
    (h_sp : t.regs.get64 .rsp = sp) (h_align : StackAligned sp)
    (h_out : isAligned 32 L = true ∧ isAligned 32 R = true)
    (h_mem : t.dmem =⋆
        StackAt ra sp (applyStack S.k)
      ⋆ SbrReady S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R) :                      -- and nothing else
    Returns "ff_aac_sbr_apply" t ra (fun s => AbiReturn t s ∧ s.dmem =⋆
        StackAfter sp (applyStack S.k)
      ⋆ SbrReady S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R) := by
  sorry

theorem ff_aac_sbr_apply_keeps_the_rest {S : Setup}
    (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che L R : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (r : Mem 64) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_L : t.regs.get64 .rcx = L) (h_R : t.regs.get64 .r8 = R)
    (h_sp : t.regs.get64 .rsp = sp) (h_align : StackAligned sp)
    (h_out : isAligned 32 L = true ∧ isAligned 32 R = true)
    (h_mem : t.dmem =⋆
        StackAt ra sp (applyStack S.k)
      ⋆ SbrReady S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R
      ⋆ (· = r)) :                             -- the rest: exactly the bytes r
    Returns "ff_aac_sbr_apply" t ra (fun s => AbiReturn t s ∧ s.dmem =⋆
        StackAfter sp (applyStack S.k)
      ⋆ SbrReady S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R
      ⋆ (· = r)) := by                            -- the same bytes r
  sorry

end Kraken.Examples.Sbr.SessionBin

/-! ## The satisfiability of the per-procedure theorems' hypotheses (`SessionBin/Witness.lean`) -/

namespace Kraken.Examples.Sbr.SessionBin.Wit

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
          ⋆ Rest) := by
  sorry

end Kraken.Examples.Sbr.SessionBin.Wit
