import Kraken.X64.Examples.Sbr.SessionBin.Defs
import Kraken.X64.Examples.Sbr.SessionBin.UsacAsmS
import Kraken.X64.Examples.Sbr.Parse.InitLinkBase
import Kraken.X64.Examples.Sbr.Parse.VlcWit

/-!
# A decoding session over the binary: the vocabulary of the headline theorem

The headline (`Top.lean`) speaks only of these names:
* `Setup`: the session's fixed parameters, chosen once by the caller;
* `Live S che ac`, `Ready S che ac`: "the SBR element at `che` (of the decoder `ac`) is in a
  state reachable from `ff_aac_sbr_ctx_alloc_init`" — and, for `Ready`, the last parse succeeded
  (what `ff_aac_sbr_apply` needs);
* `AcFields ac avctx er ps`: the three fields of `*ac` that the decoder sets and the SBR code
  reads (`avctx`, `oc[1].m4ac.ext_sample_rate`, `oc[1].m4ac.ps`); the caller owns them, with any
  values, between calls;
* `ElemOK che`: the element's address facts; the per-call obligations `DecCall`, `UsacCall`,
  `ConfigCall`, `ApplyCall`; the call objects `DecObj`, `UsacObjects`, `OutBufs`;
* `Ends f t ra Q stops`: a run entered at `f` returns to `ra` with `Q`, or reaches a stop.

The internal values (`SV`, `SReach`, the environment init produced) are hidden inside `Live`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-! ## Parameters -/

/-- The fixed parameters of a session, chosen once by the caller. -/
structure Setup where
  /-- Bytes of stack each external routine (`av_log`, `memcpy`, `powf`, …) may use. -/
  k : Nat
  /-- The caller's environment: `av_log`'s state, the transforms' contexts and tables, the
  table of `ff_ps_apply`, the `float_dsp` routines. -/
  env : Env
  /-- What libm's `powf` computes, on bit patterns. -/
  pw : BitVec 32 → BitVec 32 → BitVec 32
  /-- What libm's `log2f` computes, on bit patterns. -/
  lg : BitVec 32 → BitVec 32
  /-- The addresses of FFmpeg's ten SBR Huffman tables (`ff_aac_sbr_vlc`). -/
  sbrTabs : Nat → BitVec 64
  /-- The addresses of FFmpeg's ten PS Huffman tables. -/
  psTabs : Nat → BitVec 64

/-- The SBR Huffman tables: FFmpeg's, at `S.sbrTabs`. -/
abbrev Setup.vs (S : Setup) : Nat → Vlc.VlcTab := VlcWit.vS S.sbrTabs

/-- The PS Huffman tables: FFmpeg's, at `S.psTabs`. -/
abbrev Setup.vp (S : Setup) : Nat → Ps.VlcTab := VlcWit.vP S.psTabs

/-- A call state whose first two arguments are `ac`, `che`. -/
def tAt (che ac : BitVec 64) : MachineData :=
  { regs := (({} : Reg64s).set64 .rdi ac).set64 .rsi che }

theorem tAt_arg0 (che ac : BitVec 64) : arg0 (tAt che ac) = ac := by
  simp [tAt, arg0]

theorem tAt_arg1 (che ac : BitVec 64) : arg1 (tAt che ac) = che := by
  simp [tAt, arg1]

variable [CodeEnv]

/-! ## The element -/

/-- The three fields of `*ac` that the decoder sets and the SBR code reads: `ac->avctx`,
`ac->oc[1].m4ac.ext_sample_rate`, `ac->oc[1].m4ac.ps`. -/
def AcFields (ac avctx : BitVec 64) (er ps : BitVec 32) : Mem 64 → Prop :=
  c8 (ac + 0x8#64) avctx ⋆ (cell4 (ac + 0x57f4#64) er ⋆ cell4 (ac + 0x5800#64) ps)

/-- The element's memory at the values `σ`, by its addresses: `SessW` without `AcFields`. -/
def ElemAt (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (che ac : BitVec 64) : Mem 64 → Prop :=
  let t := tAt che ac
  DecExt.SbrF (toDS σ) (sbrA t) ⋆ (PsRest σ.1 t ⋆ (ArrW t ⋆ (DspW e t ⋆ (FnW e σ.1 t
    ⋆ (c8 (ac + 0x2550#64) σ.1.fdsp ⋆ (CstW ⋆ PStat vs vp))))))

/-- The environment the element was set up in meets the session's external contracts. -/
def EnvOK (S : Setup) (e : Env) : Prop :=
  SessionAssumed S.k e S.vs S.vp S.pw S.lg ∧ SbrSlots e

/-- The element at `che` in a state reachable from init with flag `ok`: its memory (the whole
allocation at `che`, and `ac->fdsp`) in some environment meeting the contracts. -/
def ElemState (S : Setup) (che ac : BitVec 64) (ok : Bool) : Mem 64 → Prop :=
  fun m => ∃ (e : Env) (i : InitIn) (σ : SV), EnvOK S e ∧ SReach (σInit i) σ ok
    ∧ (ElemAt e S.vs S.vp σ che ac ⋆ Init.InitGap che) m

/-- **The SBR element at `che` is live**: in a state reachable from `ff_aac_sbr_ctx_alloc_init`
by calls of the entry points. -/
def Live (S : Setup) (che ac : BitVec 64) : Mem 64 → Prop :=
  fun m => ∃ ok, ElemState S che ac ok m

/-- **The SBR element at `che` is ready**: live, and the last parse succeeded (what
`ff_aac_sbr_apply` needs). -/
def Ready (S : Setup) (che ac : BitVec 64) : Mem 64 → Prop :=
  ElemState S che ac true

/-- `SessW` is the element and the caller's `ac` fields. -/
theorem sessW_split (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (t : MachineData) : SessW e vs vp σ t = (ElemAt e vs vp σ (arg1 t) (arg0 t)
      ⋆ AcFields (arg0 t) σ.1.avctx σ.1.extRate σ.1.ps) := by
  have hs : sbrA (tAt (arg1 t) (arg0 t)) = sbrA t := by simp only [sbrA, tAt_arg1]
  have h1 : PsRest σ.1 (tAt (arg1 t) (arg0 t)) = PsRest σ.1 t := by unfold PsRest; rw [hs]
  have h2 : ArrW (tAt (arg1 t) (arg0 t)) = ArrW t := by unfold ArrW; rw [hs]
  have h3 : DspW e (tAt (arg1 t) (arg0 t)) = DspW e t := by unfold DspW; rw [hs]
  have h4 : FnW e σ.1 (tAt (arg1 t) (arg0 t)) = FnW e σ.1 t := by unfold FnW; rw [hs]
  unfold SessW ElemAt AcW AcFields
  simp only [h1, h2, h3, h4, hs]
  generalize DecExt.SbrF (toDS σ) (sbrA t) = A
  generalize PsRest σ.1 t = B
  generalize ArrW t = C
  generalize DspW e t = D
  generalize FnW e σ.1 t = F
  generalize CstW ⋆ PStat vs vp = G
  simp only [c8]
  generalize Int.toBytes 8 σ.1.avctx.toInt =@ (arg0 t + 0x8#64) = X1
  generalize Int.toBytes 8 σ.1.fdsp.toInt =@ (arg0 t + 0x2550#64) = X2
  generalize cell4 (arg0 t + 0x57f4#64) σ.1.extRate = X3
  generalize cell4 (arg0 t + 0x5800#64) σ.1.ps = X4
  ac_rfl

/-- The element does not read the caller's `ac` fields or memory. -/
theorem elemAt_frame (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (R : Mem 64 → Prop) (a : BitVec 64) (er ps : BitVec 32) (che ac : BitVec 64) :
    ElemAt e vs vp ({ σ.1 with R := R, avctx := a, extRate := er, ps := ps }, σ.2) che ac
      = ElemAt e vs vp σ che ac := rfl

/-- The element's address facts: `che` 32-aligned, the element well below the top of the
address space (no wrap, and apply's signed address arithmetic in range). -/
def ElemOK (che : BitVec 64) : Prop :=
  isAligned 32 che = true ∧ (che + 0x28920#64 + 0x5fcc0#64).toInt + 1280 < 2 ^ 63
  ∧ (che + 0x28920#64).toNat + 0x60000 < 2 ^ 64

/-! ## Runs -/

/-- A run of the code entered at `f` in state `t` either returns to `ra` in a state `s` with
`Q s`, or reaches an address in `stops`. -/
def Ends (f : Label) (t : MachineData) (ra : Int64) (Q : MachineData → Prop)
    (stops : Int64 → Prop) : Prop :=
  Eventually cenv.instrStep (fun st => (st.2 = ra ∧ Q st.1) ∨ stops st.2) (t, entry f)

/-- The allowed stops: `abort` (an `av_assert0` in `read_sbr_grid`) and the bounds trap `ud1` of
`read_sbr_envelope`. -/
abbrev Traps (a : Int64) : Prop := DecExt.DStops a

/-- No stop allowed. -/
abbrev NoStops (_ : Int64) : Prop := False

/-- The 32-bit return value. -/
abbrev ret32 (s : MachineData) : BitVec 32 := (s.regs.get64 .rax).setWidth 32

/-! ## Stack reservations -/

/-- `ff_aac_sbr_decode_extension`'s stack. -/
abbrev decStack (k : Nat) : Nat := DecExt.decNeed (decKc k)
/-- `ff_aac_sbr_decode_usac_data`'s stack. -/
abbrev usacStack (k : Nat) : Nat := Usac.usacNeed (usacK k)
/-- `ff_aac_sbr_apply`'s stack. -/
abbrev applyStack (k : Nat) : Nat := applyNeed k

/-! ## The calls' objects and obligations -/

/-- The objects of a `decode_usac_data` call, in plain terms. -/
structure UsacIn where
  /-- `ue` (the USAC element configuration). -/
  ue : BitVec 64
  /-- `gb` (the bit reader). -/
  g : BitVec 64
  /-- The reader's buffer. -/
  buf : BitVec 64
  /-- The reader's `size_in_bits_plus8`. -/
  p8 : BitVec 32
  /-- The buffer's length in bytes. -/
  L : Nat
  /-- The twelve bytes of `ue->sbr`. -/
  uev : List UInt8

/-- The parser's view of a `decode_usac_data` call. -/
def UsacIn.q (u : UsacIn) (che ac : BitVec 64) (Rc : Mem 64 → Prop) : Usac.UQ :=
  ⟨Rc, ac, che, u.ue, u.g, u.buf, u.p8, u.L, u.uev, fun _ => True, fun _ => True⟩

/-- A `decode_usac_data` call's objects: `*gb` at index `i`, the buffer, `ue->sbr`, the rest. -/
def UsacObjects (u : UsacIn) (che ac : BitVec 64) (Rc : Mem 64 → Prop) (i : BitVec 32) :
    Mem 64 → Prop :=
  UsacObj (u.q che ac Rc) i

/-- `ff_aac_sbr_apply`'s output buffers `L`, `R` (2048 floats each). -/
def OutBufs (t : MachineData) : Mem 64 → Prop := Blocks [(arg3 t, 8192), (arg4 t, 8192)]

/-- What the caller guarantees at a `ff_aac_sbr_decode_extension(ac, che, gb, crc, cnt, id)`
call. -/
structure DecCall (che ac : BitVec 64) (b : Rdr) (i : BitVec 32) (t : MachineData) : Prop where
  /-- `ac` and `che` are the first two arguments. -/
  args : arg0 t = ac ∧ arg1 t = che
  /-- The element's address facts. -/
  elem : ElemOK che
  /-- The reader's index and size are in bounds and its buffer is owned. -/
  rd : b.r.ok i
  /-- The stack is 16-aligned at the call (ABI). -/
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true
  /-- The stack has room for `sbr_reset`'s frame below this one. -/
  stk : 0x70 + 0x9d0 + 8 ≤ (t.regs.get64 .rsp).toNat

/-- What the caller guarantees at a `ff_aac_sbr_decode_usac_data(ac, che, ue, gb, …)` call. -/
structure UsacCall (che ac : BitVec 64) (u : UsacIn) (i : BitVec 32) (t : MachineData) :
    Prop where
  /-- `ac`, `che`, `ue`, `gb` are the first four arguments. -/
  args : arg0 t = ac ∧ arg1 t = che ∧ arg2 t = u.ue ∧ arg3 t = u.g
  /-- The element's address facts. -/
  elem : ElemOK che
  /-- The reader's index is within `size_in_bits_plus8`, which fits its buffer. -/
  rd : i.toNat ≤ u.p8.toNat ∧ u.p8.toNat < 2 ^ 31 ∧ u.p8.toNat / 8 + 4 ≤ u.L ∧ u.L < 2 ^ 32
  /-- `ue->sbr` has twelve bytes; its default header's `start_freq` (4 bits), `limiter_bands`,
  `limiter_gains` (2 bits each) are in range. -/
  ue : u.uev.length = 12 ∧ u8 u.uev 1 < 16 ∧ u8 u.uev 6 < 4 ∧ u8 u.uev 7 < 4
  /-- `ue->sbr`'s default header `freq_scale` is in range (2 bits). -/
  uev3 : u8 u.uev 3 ≤ 3
  /-- The stack is 16-aligned at the call (ABI). -/
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true
  /-- The stack has room for `sbr_reset`'s frame below this one. -/
  stk : 0x50 + 0x9d0 + 8 ≤ (t.regs.get64 .rsp).toNat

/-- What the caller guarantees at a `ff_aac_sbr_config_usac(ac, che, ue)` call. -/
structure ConfigCall (che ac : BitVec 64) (t : MachineData) : Prop where
  /-- `ac` and `che` are the first two arguments. -/
  args : arg0 t = ac ∧ arg1 t = che

/-- What the caller guarantees at a `ff_aac_sbr_apply(ac, che, id, L, R)` call. -/
structure ApplyCall (che ac : BitVec 64) (t : MachineData) : Prop where
  /-- `ac` and `che` are the first two arguments. -/
  args : arg0 t = ac ∧ arg1 t = che
  /-- The element's address facts. -/
  elem : ElemOK che
  /-- The output buffers are 32-aligned. -/
  out : isAligned 32 (arg3 t) = true ∧ isAligned 32 (arg4 t) = true
  /-- The stack is 16-aligned at the call (ABI). -/
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true

end Kraken.Examples.Sbr.SessionBin
