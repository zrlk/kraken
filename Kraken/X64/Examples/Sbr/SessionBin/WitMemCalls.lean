import Kraken.X64.Examples.Sbr.SessionBin.WitMemElem

/-!
# Memory witnesses: the five entry points' memories

For each entry point of `SessionBin/Api.lean`, a memory satisfying its `h_mem` exactly as stated
there, at concrete objects, under the witness code `WitEnv.wCE`, `wS` and `wX`:

* `mem_init`: the stack, `*ac` as the decoder set it up (with `ac->fdsp` and its routine table),
  the slot `*che_slot`, the shared data, the allocator's heap `wX`, nothing else;
* `mem_dec`, `mem_usac`, `mem_config`, `mem_apply`: the stack, the element at `cheW` at the init
  state (`SbrInitialized`, resp. `SbrReady`, given `EnvOK wS wEnv`), `*ac`'s three fields, the
  call's objects (bit reader with an in-bounds index, `ue->sbr`, output buffers), nothing else.

The objects (`Rest` is `emp` throughout):

| object | address | size |
|---|---|---|
| stack (`rsp = spW`) | `[0x2007f0000, 0x200800000)` | return address and 64 KiB below |
| `ac` fields | `acW + 0x8`, `+0x2550`, `+0x57e0`, `+0x57f4`, `+0x5800`, `+0x8850` | 4 or 8 |
| `ac->avctx->profile` | `avctxW + 0x2b0` | 4 |
| `float_dsp` slots | `fdspW`, `+0x30`, `+0x38` | 8 |
| `che_slot` | `0x200810000` | 8 |
| `*gb`, its buffer | `0x200900000`, `0x200901000` | 0x18, 64 |
| `ue->sbr` | `0x200a0000c` | 12 |
| output buffers | `0x200b00000`, `0x200b04000` | 8192 each |
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init
open Kraken.Examples.Sbr.SessionBin
open Kraken.Examples.Sbr.Witness (SatIn InL DisjL)
open Kraken.Examples.Sbr.WitEnv

namespace Kraken.Examples.Sbr.WitMem

/-! ## The objects -/

/-- `rsp` at the call (`rsp + 8` is 16-aligned). -/
abbrev spW : BitVec 64 := 0x2007FFFF8#64

/-- The return address. -/
abbrev raW : Int64 := 0x401000

/-- `ac->oc[1].m4ac.ext_sample_rate`, `ac->oc[1].m4ac.ps`. -/
abbrev erW : BitVec 32 := 24000#32
abbrev psW : BitVec 32 := 0#32

/-- `id_aac`. -/
abbrev idW : BitVec 32 := 0#32

/-- The slot for the new element pointer. -/
abbrev cheSlotW : BitVec 64 := 0x200810000#64

/-- The bit reader `*gb` and its buffer of `LW` bytes, index `iW`, `size_in_bits = sibW`,
`size_in_bits_plus8 = p8W`. -/
abbrev gbW : BitVec 64 := 0x200900000#64
abbrev bufW : BitVec 64 := 0x200901000#64
abbrev iW : BitVec 32 := 0#32
abbrev sibW : BitVec 32 := 120#32
abbrev p8W : BitVec 32 := 128#32
abbrev padW : BitVec 32 := 0#32
abbrev LW : Nat := 64

/-- The USAC element configuration `ue` and its twelve bytes `ue->sbr`. -/
abbrev ueW : BitVec 64 := 0x200a00000#64
abbrev uevW : List UInt8 := List.replicate 12 0

/-- The output buffers. -/
abbrev outLW : BitVec 64 := 0x200b00000#64
abbrev outRW : BitVec 64 := 0x200b04000#64

/-- Nothing else. -/
abbrev RestW : Mem 64 → Prop := Std.ExtHashMap.emp

attribute [local instance] wCE

/-! ## The pieces -/

theorem sat_true : SatIn (fun _ => True) [] := ⟨∅, trivial, fun k hk => by simp at hk⟩

/-- The heap: the allocator's pointer at its start, the whole heap free. -/
theorem sat_wX : SatIn wX [(0x400000000, 0x400000008), (0x400001000, 0x400101000)] := by
  have h : SatIn (Apply.c8 wHeapPtr wHeapStart ⋆ ((wHeapEnd - wHeapStart).toNat ?@ wHeapStart
      ⋆ fun _ => True)) ([(0x400000000, 0x400000008)] ++ ([(0x400001000, 0x400101000)] ++ [])) :=
    Witness.SatIn.sep (Witness.SatIn.val (Int.toBytes_length _ _) (by decide +kernel))
      (Witness.SatIn.sep (Witness.SatIn.block (Nat.le_refl _) (by decide +kernel)) sat_true
        (by decide +kernel)) (by decide +kernel)
  exact SatIn.imp h fun m hm => ⟨wHeapStart, by decide +kernel, by decide +kernel, hm⟩

/-- `*ac`'s three fields. -/
theorem sat_acFields : SatIn (AcFields acW avctxW erW psW)
    [(0x200100008, 0x200100010), (0x2001057f4, 0x2001057f8), (0x200105800, 0x200105804)] := by
  unfold AcFields
  exact SatIn.cover (by msat) (by decide +kernel)

/-- `*ac` as the decoder set it up: the fields, `ac->fdsp`, the `float_dsp` slots. -/
theorem sat_acInit : SatIn (AcInit wS acW avctxW fdspW erW psW)
    [(0x200100008, 0x200100010), (0x2001057f4, 0x2001057f8), (0x200105800, 0x200105804),
     (0x200102550, 0x200102558), (0x200200000, 0x200200040)] := by
  unfold AcInit FdspW
  have := sat_acFields
  exact SatIn.cover (by msat) (by decide +kernel)

/-- The shared data. -/
theorem sat_shared : SatIn (SharedData wS)
    [(0x300200000, 0x300202040), (0x400000, 0x48a000), (0x300000000, 0x300014000),
     (0x300100000, 0x300114000)] := by
  unfold SharedData
  exact SatIn.cover (Witness.SatIn.sep (Witness.SatIn.block (Nat.le_refl _) (by decide +kernel))
    (Witness.SatIn.sep (Witness.SatIn.block (Nat.le_refl _) (by decide +kernel))
      (Witness.SatIn.sep (Witness.SatIn.block (Nat.le_refl _) (by decide +kernel)) sat_cstP
        (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

/-- The stack: the return address and `d ≤ 0x10000` bytes below `rsp`. -/
syntax "stack_tac" : tactic
macro_rules
  | `(tactic| stack_tac) => `(tactic|
      (unfold StackAt; rw [Reserve_eq _ _ (by decide +kernel)];
       exact SatIn.cover (by msat) (by decide +kernel)))

theorem sat_stackInit : SatIn (StackAt raW spW (initStack wS.k)) [(0x2007f0000, 0x200800000)] := by
  stack_tac

theorem sat_stackDec : SatIn (StackAt raW spW (decStack wS.k)) [(0x2007f0000, 0x200800000)] := by
  stack_tac

theorem sat_stackUsac : SatIn (StackAt raW spW (usacStack wS.k)) [(0x2007f0000, 0x200800000)] := by
  stack_tac

theorem sat_stackCfg : SatIn (StackAt raW spW 0) [(0x2007f0000, 0x200800000)] := by
  stack_tac

theorem sat_stackApply : SatIn (StackAt raW spW (applyStack wS.k)) [(0x2007f0000, 0x200800000)] := by
  stack_tac

theorem sat_decReader : SatIn (DecReader gbW bufW iW sibW p8W padW LW)
    [(0x200900000, 0x200900018), (0x200901000, 0x200901040)] := by
  unfold DecReader
  exact SatIn.cover (by msat) (by decide +kernel)

theorem sat_usacReader : SatIn (UsacReader gbW bufW iW p8W LW)
    [(0x200900000, 0x200900018), (0x200901000, 0x200901040)] := by
  unfold UsacReader
  exact SatIn.cover (by msat) (by decide +kernel)

theorem sat_scratch : SatIn (DecScratch acW avctxW)
    [(0x2001057e0, 0x2001057e4), (0x200108850, 0x200108854), (0x2007002b0, 0x2007002b4)] := by
  unfold DecScratch AcX
  exact SatIn.cover (by msat) (by decide +kernel)

theorem sat_uev : SatIn (uevW =@ (ueW + 0xc#64)) [(0x200a0000c, 0x200a00018)] :=
  Witness.SatIn.val (List.length_replicate (n := 12) (a := (0 : UInt8))) (by decide +kernel)

theorem sat_out : SatIn (OutBuffers outLW outRW) [(0x200b00000, 0x200b06000)] := by
  unfold OutBuffers
  exact SatIn.cover (by msat) (by decide +kernel)

/-! ## The five memories -/

/-- `ff_aac_sbr_ctx_alloc_init`'s memory. -/
theorem mem_init : ∃ m : Mem 64, m =⋆
      StackAt raW spW (initStack wS.k)
    ⋆ AcInit wS acW avctxW fdspW erW psW
    ⋆ 8 ?@ cheSlotW
    ⋆ SharedData wS
    ⋆ wX
    ⋆ RestW := by
  obtain ⟨m, hm, -⟩ := (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep sat_stackInit
      sat_acInit (by decide +kernel))
      (Witness.SatIn.block (n := 8) (a := cheSlotW) (Nat.le_refl _) (by decide +kernel)) (by decide +kernel))
      sat_shared (by decide +kernel))
      sat_wX (by decide +kernel))
      Witness.SatIn.emp (by decide +kernel))
  exact ⟨m, hm⟩

/-- `ff_aac_sbr_decode_extension`'s memory. -/
theorem mem_dec (hE : EnvOK wS wEnv) : ∃ m : Mem 64, m =⋆
      StackAt raW spW (decStack wS.k)
    ⋆ SbrInitialized wS cheW acW
    ⋆ AcFields acW avctxW erW psW
    ⋆ DecReader gbW bufW iW sibW p8W padW LW
    ⋆ DecScratch acW avctxW
    ⋆ RestW := by
  obtain ⟨m, hm, -⟩ := (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep sat_stackDec
      (sat_initialized hE) (by decide +kernel))
      sat_acFields (by decide +kernel))
      sat_decReader (by decide +kernel))
      sat_scratch (by decide +kernel))
      Witness.SatIn.emp (by decide +kernel))
  exact ⟨m, hm⟩

/-- `ff_aac_sbr_decode_usac_data`'s memory. -/
theorem mem_usac (hE : EnvOK wS wEnv) : ∃ m : Mem 64, m =⋆
      StackAt raW spW (usacStack wS.k)
    ⋆ SbrInitialized wS cheW acW
    ⋆ AcFields acW avctxW erW psW
    ⋆ UsacReader gbW bufW iW p8W LW
    ⋆ uevW =@ (ueW + 0xc#64)
    ⋆ RestW := by
  obtain ⟨m, hm, -⟩ := (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep sat_stackUsac
      (sat_initialized hE) (by decide +kernel))
      sat_acFields (by decide +kernel))
      sat_usacReader (by decide +kernel))
      sat_uev (by decide +kernel))
      Witness.SatIn.emp (by decide +kernel))
  exact ⟨m, hm⟩

/-- `ff_aac_sbr_config_usac`'s memory. -/
theorem mem_config (hE : EnvOK wS wEnv) : ∃ m : Mem 64, m =⋆
      StackAt raW spW 0
    ⋆ SbrInitialized wS cheW acW
    ⋆ AcFields acW avctxW erW psW
    ⋆ RestW := by
  obtain ⟨m, hm, -⟩ := (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep sat_stackCfg
      (sat_initialized hE) (by decide +kernel))
      sat_acFields (by decide +kernel))
      Witness.SatIn.emp (by decide +kernel))
  exact ⟨m, hm⟩

/-- `ff_aac_sbr_apply`'s memory. -/
theorem mem_apply (hE : EnvOK wS wEnv) : ∃ m : Mem 64, m =⋆
      StackAt raW spW (applyStack wS.k)
    ⋆ SbrReady wS cheW acW
    ⋆ AcFields acW avctxW erW psW
    ⋆ OutBuffers outLW outRW
    ⋆ RestW := by
  obtain ⟨m, hm, -⟩ := (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep (Witness.SatIn.sep sat_stackApply
      (sat_ready hE) (by decide +kernel))
      sat_acFields (by decide +kernel))
      sat_out (by decide +kernel))
      Witness.SatIn.emp (by decide +kernel))
  exact ⟨m, hm⟩

/-! ## The pure side conditions -/

theorem spW_aligned : StackAligned spW := by decide +kernel

theorem readerOK_W : ReaderOK iW p8W LW := by unfold ReaderOK; decide +kernel

theorem usacSbrOK_W : UsacSbrOK uevW := by unfold UsacSbrOK; decide +kernel

theorem out_aligned : isAligned 32 outLW = true ∧ isAligned 32 outRW = true := by decide +kernel

end Kraken.Examples.Sbr.WitMem
