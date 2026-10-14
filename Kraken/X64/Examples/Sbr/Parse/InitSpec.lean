import Kraken.X64.Examples.Sbr.Parse.InitFoot

/-!
# `ff_aac_sbr_ctx_alloc_init`: the specification

`ff_aac_sbr_ctx_alloc_init(ac, che, id_aac)` (`libavcodec/aacsbr_template.c`, FFmpeg n8.1,
l.70-113) allocates the channel element `ExtChannelElement` (`av_mallocz`, 0x88ba0 bytes), stores
it to `*che`, sets the two `predictor_state` pointers, `kx[0] = kx[1]`, `id_aac`, the stores of
`sbr_turnoff` and both `synthesis_filterbank_samples_offset`, initialises the two `av_tx` MDCT
contexts, `sbr->ps.dsp` (`ff_ps_ctx_init`, inlined: `ff_psdsp_init`), `sbr->dsp`
(`ff_sbrdsp_init`) and the four `sbr->c` slots (`aacsbr_func_ptr_init`, inlined). `ac` is not
read.

* The callees are assumed contracts (`InitAssumed`): `av_mallocz`, `av_tx_init`,
  `ff_psdsp_init`, `ff_sbrdsp_init`. They share an abstract state `X` (the allocator's, the cpu
  flags); `av_tx_init` also uses the `av_tx` tables `TxTab`, leaves its context owned as
  `Ctx c` and returns a function satisfying `TxSpec`; `ff_sbrdsp_init` leaves the `sbr->dsp`
  slots `DspSlotsOK` (the routines of `ff_sbrdsp_init_x86` with SSE, SSE2, SSE3, as in
  `SbrSlots`).
* The precondition owns only `*che` (8 bytes), `TxTab` and `X`.
* The postcondition, on every return: `0` with `*che = p` and the element at `p` owned with the
  values `evInit` (`ElemS`: zero except the cells listed in `EV`), the two contexts owned
  (`Ctx`), the two functions `TxSpec`, the slots `DspSlotsOK`; or `-12` (`AVERROR(ENOMEM)`,
  `av_mallocz` failed) with `*che` as it was; or a negative result of `av_tx_init` with
  `*che = p` and the rest of what the routine allocated not described (`J`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr
open Kraken.Examples.Sbr.Apply (c8)
open Kraken.Examples.Sbr.Session (zs)

namespace Kraken.Examples.Sbr.Init

variable [CodeEnv]

/-! ## The assumed contracts -/

/-- Assumed: `av_mallocz(size)` (`libavutil/mem.c`) returns `NULL`, or a new address holding
`size` zero bytes, disjoint from the caller's memory; it uses the external state `X` and gives it
back. -/
abbrev AvMalloczSpec (X : Mem 64 → Prop) (need : Nat) : Prop :=
  cenv.ProcSpec (entry "av_mallocz")
    (fun (R : Mem 64 → Prop) ra t => CallPre need (X ⋆ R) ra t)
    (fun R ra t s => (s.regs.get64 .rax = 0#64 ∧ CallPost need (X ⋆ R) ra t s)
      ∨ (s.regs.get64 .rax ≠ 0#64
        ∧ CallPost need ((zs (arg0 t).toNat =@ s.regs.get64 .rax ⋆ X) ⋆ R) ra t s))

/-- What `av_tx_init` reads or writes besides `*ctx` and `*tx`: `*scale` (4 bytes at `r9`), the
stack argument `flags` (above the return address), the tables `TxTab`, the state `X`. -/
abbrev TxIn (TxTab X : Mem 64 → Prop) (t : MachineData) : Mem 64 → Prop :=
  4 ?@ arg5 t ⋆ (8 ?@ (t.regs.get64 .rsp + 8#64) ⋆ (TxTab ⋆ X))

/-- `*ctx` and `*tx` after `av_tx_init`: on success (`eax ≥ 0`) a context `c`, owned as `Ctx c`,
and a function `f`; otherwise any bytes. -/
abbrev TxOut (Ctx : BitVec 64 → Mem 64 → Prop) (t s : MachineData) (c : BitVec 64) (f : Int64) :
    Mem 64 → Prop :=
  if 0 ≤ ((s.regs.get64 .rax).setWidth 32).toInt then
    c8 (arg0 t) c ⋆ (FnCell (arg1 t) f ⋆ Ctx c)
  else 8 ?@ arg0 t ⋆ 8 ?@ arg1 t

/-- Assumed: `av_tx_init(ctx, tx, type, inv, len, scale, flags)` (`libavutil/tx.c`) writes
`*ctx` and `*tx` (`TxOut`), reads `*scale` and `flags`, and uses `TxTab` and `X`. On success
(`eax ≥ 0`) the function `f` it returns satisfies the `av_tx` contract `TxSpec` (the transform
on the context `c`, owned as `Ctx c`, with the tables `TxTab`, at `need` bytes of stack).
Nothing is assumed of the arguments. -/
abbrev AvTxInitSpec (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop) (need : Nat) :
    Prop :=
  cenv.ProcSpec (entry "av_tx_init")
    (fun (R : Mem 64 → Prop) ra t =>
      CallPre need ((8 ?@ arg0 t ⋆ (8 ?@ arg1 t ⋆ TxIn TxTab X t)) ⋆ R) ra t)
    (fun R ra t s => ∃ c f,
      (0 ≤ ((s.regs.get64 .rax).setWidth 32).toInt → TxSpec Ctx TxTab need f)
      ∧ CallPost need ((TxOut Ctx t s c f ⋆ TxIn TxTab X t) ⋆ R) ra t s)

/-- Assumed: `ff_psdsp_init(s)` (`libavcodec/aacpsdsp_template.c`) writes only `*s`
(`PSDSPContext`, 64 bytes) and uses `X`. -/
abbrev PsDspInitSpec (X : Mem 64 → Prop) (need : Nat) : Prop :=
  LeafSpec "ff_psdsp_init" need (fun t => 64 ?@ arg0 t ⋆ X) (fun _ => True)

/-- The fourteen `sbr->dsp` slots (`SBRDSPContext` order, as `DspW`) as `ff_sbrdsp_init` leaves
them. -/
structure Slots where
  sum64x5 : Int64
  sumSquare : Int64
  negOdd64 : Int64
  preShuffle : Int64
  postShuffle : Int64
  deintNeg : Int64
  deintBfly : Int64
  autocorr : Int64
  hfGen : Int64
  gfilt : Int64
  noise0 : Int64
  noise1 : Int64
  noise2 : Int64
  noise3 : Int64

/-- The bytes of a function pointer. -/
abbrev fb (f : Int64) : List UInt8 := Int.toBytes 8 f.toBitVec.toInt

/-- The slots' bytes. -/
def Slots.bytes (sl : Slots) : List UInt8 :=
  fb sl.sum64x5 ++ fb sl.sumSquare ++ fb sl.negOdd64 ++ fb sl.preShuffle ++ fb sl.postShuffle
    ++ fb sl.deintNeg ++ fb sl.deintBfly ++ fb sl.autocorr ++ fb sl.hfGen ++ fb sl.gfilt
    ++ fb sl.noise0 ++ fb sl.noise1 ++ fb sl.noise2 ++ fb sl.noise3

/-- The `sbr->dsp` slots as `ff_sbrdsp_init_x86` sets them with SSE, SSE2 and SSE3 present: the
fourteen `sbr->dsp` clauses of `SbrSlots`, stated of the slots. -/
structure DspSlotsOK (sl : Slots) : Prop where
  sum64x5 : sl.sum64x5 = entry "ff_sbr_sum64x5_sse"
  sumSquare : sl.sumSquare = entry "ff_sbr_sum_square_sse"
  preShuffle : sl.preShuffle = entry "ff_sbr_qmf_pre_shuffle_sse2"
  postShuffle : sl.postShuffle = entry "ff_sbr_qmf_post_shuffle_sse"
  hfGen : sl.hfGen = entry "ff_sbr_hf_gen_sse"
  autocorr : sl.autocorr = entry "ff_sbr_autocorrelate_sse"
    ∨ sl.autocorr = entry "ff_sbr_autocorrelate_sse3"
  gfilt : sl.gfilt = entry "ff_sbr_hf_g_filt_sse"
  noise0 : sl.noise0 = entry "ff_sbr_hf_apply_noise_0_sse2"
  noise1 : sl.noise1 = entry "ff_sbr_hf_apply_noise_1_sse2"
  noise2 : sl.noise2 = entry "ff_sbr_hf_apply_noise_2_sse2"
  noise3 : sl.noise3 = entry "ff_sbr_hf_apply_noise_3_sse2"
  negOdd64 : sl.negOdd64 = entry "ff_sbr_neg_odd_64_sse"
  deintNeg : sl.deintNeg = entry "ff_sbr_qmf_deint_neg_sse"
  deintBfly : sl.deintBfly = entry "ff_sbr_qmf_deint_bfly_sse2"

/-- Assumed: `ff_sbrdsp_init(s)` (`libavcodec/sbrdsp_template.c`, with
`ff_sbrdsp_init_x86`) writes only `*s` (`SBRDSPContext`, 0x70 bytes), leaving the slots
`DspSlotsOK`, and uses `X`. -/
abbrev SbrDspInitSpec (X : Mem 64 → Prop) (need : Nat) : Prop :=
  cenv.ProcSpec (entry "ff_sbrdsp_init")
    (fun (R : Mem 64 → Prop) ra t => CallPre need ((0x70 ?@ arg0 t ⋆ X) ⋆ R) ra t)
    (fun R ra t s => ∃ sl : Slots, DspSlotsOK sl
      ∧ CallPost need ((sl.bytes =@ arg0 t ⋆ X) ⋆ R) ra t s)

/-- The assumed contracts of the callees, with `need` bytes of stack each. -/
structure InitAssumed (need : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop) :
    Prop where
  mallocz : AvMalloczSpec X need
  txInit : AvTxInitSpec Ctx TxTab X need
  psdsp : PsDspInitSpec X need
  sbrdsp : SbrDspInitSpec X need

/-! ## The values after a successful run -/

/-- The results of a successful run: the element `p`, the two `av_tx` contexts and functions,
the `sbr->dsp` slots, and the 64 bytes `ff_psdsp_init` leaves in `sbr->ps.dsp`. -/
structure IR where
  p : BitVec 64
  anaCtx : BitVec 64
  anaFn : Int64
  synCtx : BitVec 64
  synFn : Int64
  sl : Slots
  psd : List UInt8

/-- The cells after a successful run (`id_aac` is the low half of `rdx` at entry). The other
bytes of the element are zero (`ElemS`). -/
def evInit (idAac : BitVec 32) (r : IR) : EV where
  pr0 := Int.toBytes 8 (r.p + 0x1e120#64).toInt
  pr1 := Int.toBytes 8 (r.p + 0x23520#64).toInt
  sr := Int.toBytes 8 0
  id := Int.toBytes 4 idAac.toInt
  usac := Int.toBytes 4 0
  spLo := Int.toBytes 4 (-1)
  spHi := Int.toBytes 2 (-1)
  kx0 := Int.toBytes 4 0
  kx1 := Int.toBytes 4 32
  m1 := Int.toBytes 4 0
  v0 := Int.toBytes 4 0x480
  e0 := Int.toBytes 4 (-1)
  v1 := Int.toBytes 4 0x480
  e1 := Int.toBytes 4 (-1)
  ps := r.psd
  anaC := Int.toBytes 8 r.anaCtx.toInt
  anaF := fb r.anaFn
  synC := Int.toBytes 8 r.synCtx.toInt
  synF := fb r.synFn
  dsp := r.sl.bytes
  c0 := fb (entry "sbr_lf_gen")
  c1 := fb (entry "sbr_hf_assemble")
  c2 := fb (entry "sbr_x_gen")
  c3 := fb (entry "sbr_hf_inverse_filter")

/-- After a successful run: `*che = p`, the element at `p` with the cells `evInit`, the two
contexts. -/
def InitOK (Ctx : BitVec 64 → Mem 64 → Prop) (che : BitVec 64) (idAac : BitVec 32) (r : IR) :
    Mem 64 → Prop :=
  c8 che r.p ⋆ (ElemS r.p (evInit idAac r) ⋆ (Ctx r.anaCtx ⋆ Ctx r.synCtx))

/-! ## The specification -/

/-- Own bytes (`push rbp`, three saved registers, `sub $0x18`), the return slot of a call, the
callee's `k`. -/
abbrev initNeed (k : Nat) : Nat := 0x40 + k

/-- The id at entry. -/
abbrev idOf (t : MachineData) : BitVec 32 := (arg2 t).setWidth 32

abbrev InitPre (k : Nat) (TxTab X : Mem 64 → Prop) (R : Mem 64 → Prop) (ra : Int64)
    (t : MachineData) : Prop :=
  CallPre (initNeed k) ((8 ?@ arg1 t ⋆ (TxTab ⋆ X)) ⋆ R) ra t

/-- The three outcomes (the result is `eax`). -/
abbrev InitPost (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t s : MachineData) : Prop :=
  let ret := (s.regs.get64 .rax).setWidth 32
  (ret = 0#32 ∧ ∃ r : IR, r.psd.length = 64 ∧ DspSlotsOK r.sl
      ∧ TxSpec Ctx TxTab k r.anaFn ∧ TxSpec Ctx TxTab k r.synFn
      ∧ CallPost (initNeed k) ((InitOK Ctx (arg1 t) (idOf t) r ⋆ (TxTab ⋆ X)) ⋆ R) ra t s)
  ∨ (ret = 0xfffffff4#32 ∧ CallPost (initNeed k) ((8 ?@ arg1 t ⋆ (TxTab ⋆ X)) ⋆ R) ra t s)
  ∨ (ret.toInt < 0 ∧ ∃ (p : BitVec 64) (J : Mem 64 → Prop),
      CallPost (initNeed k) ((c8 (arg1 t) p ⋆ (J ⋆ (TxTab ⋆ X))) ⋆ R) ra t s)

/-- `ff_aac_sbr_ctx_alloc_init` with its callees at `k` bytes of stack. -/
abbrev InitSpec (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "ff_aac_sbr_ctx_alloc_init") (InitPre k TxTab X) (InitPost k Ctx TxTab X)

end Kraken.Examples.Sbr.Init
