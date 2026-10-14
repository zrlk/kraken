import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.CfgTable
import Kraken.Rules.FrameLemmas
import Kraken.Rules.IndirectCall
import Kraken.Rules.IntMisc
import Kraken.Rules.PackedSse
import Kraken.Rules.ScalarFloat
import Kraken.Rules.HelperLemmas
import Kraken.Rules.ViewLemmas
import Kraken.Rules.SepStep
import Kraken.Rules.LexVar
import Kraken.X64.Examples.Sbr.Spec
import Kraken.X64.Examples.Sbr.DequantFloat

/-!
# `ff_aac_sbr_apply`: the specification

`libavcodec/aacsbr_template.c` (FFmpeg n8.1), `ff_aac_sbr_apply(ac, che, id_aac, L, R)`.
This file is hand-written and holds only definitions: the logical variables (`Args`,
`DV`, `Env`), the addresses, the footprint `ApplyF` and its groups, the well-formedness
invariant `SbrWF`, the layout conditions `LayoutC`, the constants `CstW`, and
`ApplySpec` itself. Everything the statement of `ff_aac_sbr_apply_linked` says about
`ff_aac_sbr_apply` is defined here or in `Spec.lean`; no proof is needed to read it.

The text, the control-flow table and the block obligations are generated into
`ApplyTable.lean`, which imports this file; the proof is in `Apply/*.lean` and
`Apply.lean`.
-/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem

namespace Kraken.Examples.Sbr.Apply

/-! ## The logical variables -/

/-- The values of one `SBRData` (`sbr->data[ch]`, `libavcodec/sbr.h`) the code reads
and depends on. Byte arrays are lists of bytes; `u8 bs i` reads one. -/
structure DV where
  /-- `bs_num_env` (`int`, +0x8). -/
  nenv : Nat
  /-- `bs_freq_res[0..8]` (+0xc). -/
  freqRes : List UInt8
  /-- `bs_num_noise` (`int`, +0x18). -/
  nnoise : Nat
  /-- `bs_invf_mode[2][5]` (+0x27). -/
  invf : List UInt8
  /-- `synthesis_filterbank_samples_offset` (`int`, +0x3900). -/
  vOff : BitVec 32
  /-- `Ypos` (`int`, +0x7920). -/
  ypos : Nat
  /-- `t_env[0..8]`, `t_env_num_env_old` (+0x15a9c, 10 bytes). -/
  te : List UInt8
  /-- `t_q[0..2]` (+0x15aa6). -/
  tq : List UInt8
  /-- `f_indexnoise`, `f_indexsine` (+0x15aac, 8 bytes). -/
  idx : BitVec 64

/-- The function addresses reachable from `ff_aac_sbr_apply`: the fourteen
`sbr->dsp` slots (`SBRDSPContext`, `libavcodec/sbrdsp.h`), the four `sbr->c` slots,
`sbr->mdct_ana_fn`, and the `AVFloatDSPContext` slots used here and by
`sbr_qmf_synthesis` (with `mdct_fn`, in `qfs`). -/
structure Fns where
  sum64x5 : Int64
  sumSquare : Int64
  preShuffle : Int64
  postShuffle : Int64
  autocorr : Int64
  hfGen : Int64
  hfs : HfFns
  qfs : QmfFns
  lfGen : Int64
  hfAsm : Int64
  xGen : Int64
  hfInv : Int64
  mdctAna : Int64
  fmulRev : Int64

/-- The parameters of the specification: the function addresses, the owned state of
an `av_tx` context, the shared static tables of `av_tx` (`TxTab`) and of the PS
decoder (`PsTab`), and the state outside the footprint that `av_log` may read. -/
structure Env where
  fs : Fns
  Ctx : BitVec 64 → Mem 64 → Prop
  TxTab : Mem 64 → Prop
  PsTab : Mem 64 → Prop
  Ext : Mem 64 → Prop

/-- The logical variables: the caller's memory `R` and the decoder-state values. -/
structure Args where
  R : Mem 64 → Prop
  /-- `sbr->start`, `ready_for_dequant`, `id_aac`, `reset`, `bs_smoothing_mode`,
  `kx_and_m_pushed`. -/
  start : BitVec 32
  ready : BitVec 32
  idAac : BitVec 32
  reset : BitVec 32
  smooth : BitVec 32
  pushed : BitVec 32
  /-- `sbr->k[0]`, `kx[0..1]`, `m[0..1]`. -/
  k0 : Nat
  kx0 : Nat
  kx1 : Nat
  m0 : Nat
  m1 : Nat
  /-- `bs_limiter_gains`, `bs_interpol_freq`, `bs_coupling`. -/
  limGains : Nat
  interpol : BitVec 32
  coupling : BitVec 32
  /-- `n[0..1]`, `n_q`, `n_lim`, `num_patches`. -/
  n0 : Nat
  n1 : Nat
  nq : Nat
  nlim : Nat
  npatch : Nat
  /-- `patch_num_subbands[6]`, `patch_start_subband[6]` (bytes). -/
  pnum : List UInt8
  pstart : List UInt8
  /-- `f_tablelow[25]`, `f_tablehigh[49]`, `f_tablenoise[6]`, `f_tablelim[30]`
  (`uint16_t`, as bytes). -/
  ftLow : List UInt8
  ftHigh : List UInt8
  ftNoise : List UInt8
  ftLim : List UInt8
  /-- The two channels' `SBRData` values. -/
  d0 : DV
  d1 : DV
  /-- `sbr->sample_rate`. -/
  sampleRate : BitVec 32
  /-- `ac->avctx`, `ac->fdsp`, the extension sample rate and the PS flag. -/
  avctx : BitVec 64
  fdsp : BitVec 64
  extRate : BitVec 32
  ps : BitVec 32
  /-- The `av_tx` contexts `sbr->mdct_ana`, `sbr->mdct`. -/
  anaCtx : BitVec 64
  synCtx : BitVec 64
  /-- `sbr->ps.common` (`PSCommonContext`, 764 bytes at `sbr + 0x2b600`) and
  `sbr->ps.opd_hist ++ ipd_hist` (68 bytes at `sbr + 0x4c150`), see `PsWF`. -/
  psc : List UInt8
  psh : List UInt8
  /-- `sbr->spectrum_params` (`SpectrumParameters`, 6 bytes at `sbr + 0x1c`): bytes 0..3 and
  4..5, the two stores of `sbr_turnoff`'s `memset(&sbr->spectrum_params, -1, 6)`. Byte 0 is
  `bs_start_freq`. -/
  spLo : BitVec 32
  spHi : BitVec 16

/-- The frequency tables `ff_aac_sbr_apply` does not modify: `k[0]`, `n[0..1]`, `n_q`,
`n_lim`, `num_patches`, `patch_num_subbands`, `patch_start_subband`,
`f_tablelow/high/noise/lim` (written only by `sbr_make_f_master`, `sbr_make_f_derived`,
`sbr_make_f_tablelim` and `sbr_hf_calc_npatches`, from the parser's `sbr_reset` and header).
And `start` with `spectrum_params` are kept, or cleared together: the only writes of
`sbr->start` and `sbr->spectrum_params` reachable from apply are `sbr_turnoff`'s `start = 0`
and `memset(&sbr->spectrum_params, -1, …)` (`aacsbr_template.c`:58-68). -/
def Args.KeepT (x y : Args) : Prop :=
  y.k0 = x.k0 ∧ y.n0 = x.n0 ∧ y.n1 = x.n1 ∧ y.nq = x.nq ∧ y.nlim = x.nlim
  ∧ y.npatch = x.npatch ∧ y.pnum = x.pnum ∧ y.pstart = x.pstart ∧ y.ftLow = x.ftLow
  ∧ y.ftHigh = x.ftHigh ∧ y.ftNoise = x.ftNoise ∧ y.ftLim = x.ftLim
  ∧ ((y.start = 0 ∧ y.spLo = BitVec.allOnes 32 ∧ y.spHi = BitVec.allOnes 16)
      ∨ (y.start = x.start ∧ y.spLo = x.spLo ∧ y.spHi = x.spHi))

/-- The decoder state `ff_aac_sbr_apply` does not modify (INV-D5): both channels'
`bs_num_env`, `t_env`/`t_env_num_env_old`, `bs_freq_res`, `t_q`, and the PS common
context (only the grid parser, `read_sbr_grid`, and the PS parser write them), and the
frequency tables with `start` kept or cleared (`KeepT`). -/
abbrev Args.KeepD (x y : Args) : Prop :=
  y.d0.nenv = x.d0.nenv ∧ y.d0.te = x.d0.te ∧ y.d1.nenv = x.d1.nenv ∧ y.d1.te = x.d1.te
  ∧ y.d0.freqRes = x.d0.freqRes ∧ y.d1.freqRes = x.d1.freqRes
  ∧ y.d0.tq = x.d0.tq ∧ y.d1.tq = x.d1.tq ∧ y.psc = x.psc ∧ x.KeepT y

/-- What stays fixed while the body runs (also across `sbr_turnoff`): the caller's rest,
the pointers and rates the final state is stated with, and (`KeepD`, one nested
conjunct) the decoder state apply does not write. Entries where the arguments evolve
(the channel loop) read `∃ y, x.Keep y ∧ SbrWF y ∧ … ∧ (s.dmem =⋆ Mm k e y ra t₀ …)`. -/
abbrev Args.Keep (x y : Args) : Prop :=
  y.R = x.R ∧ y.avctx = x.avctx ∧ y.fdsp = x.fdsp ∧ y.extRate = x.extRate ∧ y.ps = x.ps
  ∧ y.anaCtx = x.anaCtx ∧ y.synCtx = x.synCtx ∧ y.sampleRate = x.sampleRate ∧ x.KeepD y

/-- Channel `ch`'s values. -/
abbrev Args.d (x : Args) (ch : Nat) : DV := if ch = 0 then x.d0 else x.d1

/-- `sbr_turnoff`'s effect on the scalar fields: `start = ready = 0`, `kx[1] = 32`,
`m[1] = 0` (the other fields it writes are raw in the footprint). -/
abbrev Args.turnoff (x : Args) : Args := { x with start := 0, ready := 0, kx1 := 32, m1 := 0 }

/-- `sbr_turnoff`'s `memset(&sbr->spectrum_params, -1, sizeof(SpectrumParameters))`. -/
abbrev Args.spSet (x : Args) : Args :=
  { x with spLo := BitVec.allOnes 32, spHi := BitVec.allOnes 16 }

/-- I1: a stopped decoder has `spectrum_params.bs_start_freq = 0xFF` (`sbr_turnoff`'s memset;
a header that sets `start` also sets `bs_start_freq`). -/
def Args.I1 (x : Args) : Prop := x.start = 0 → x.spLo.setWidth 8 = 0xFF#8

/-- The prologue's `kx_and_m_pushed` step (before `sbr_dequant`): `kx[0] = kx[1]`, `m[0] = m[1]`
unless pushed; then `kx_and_m_pushed = 0`. -/
abbrev Args.push (x : Args) : Args :=
  { x with kx0 := if x.pushed = 0 then x.kx1 else x.kx0,
           m0 := if x.pushed = 0 then x.m1 else x.m0, pushed := 0 }

/-- `sbr_qmf_synthesis` on channel 0 / 1 writes `synthesis_filterbank_samples_offset`
(`*v_off`): the values with that field `v`. -/
abbrev Args.setV0 (x : Args) (v : BitVec 32) : Args := { x with d0 := { x.d0 with vOff := v } }
abbrev Args.setV1 (x : Args) (v : BitVec 32) : Args := { x with d1 := { x.d1 with vOff := v } }

/-- D5 path fact (a), aacsbr_template.c:1693-1697: after the prologue's element-type check
(`id_aac != sbr->id_aac` → `sbr_turnoff`), a live state's `sbr->id_aac` equals the `id_aac`
argument (the low 32 bits of `rdx` at entry). -/
def IdLive (t : MachineData) (y : Args) : Prop :=
  y.start ≠ 0 → y.idAac = BitVec.setWidth 32 (arg2 t)

/-- D5 path facts carried in the channel loop: (a) `IdLive`; (b) the loop runs channel 1 only
for a CPE (`ch < (id_aac == TYPE_CPE) + 1`, aacsbr_template.c:1700). -/
def ChLive (t : MachineData) (ch : Nat) (y : Args) : Prop :=
  IdLive t y ∧ (ch ≠ 0 → BitVec.setWidth 32 (arg2 t) = 1#32)


/-- Byte `i` of a byte array. -/
abbrev u8 (bs : List UInt8) (i : Nat) : Nat := (bs.getD i 0).toNat

/-- Element `i` of a little-endian `uint16_t` array. -/
abbrev u16 (bs : List UInt8) (i : Nat) : Nat := u8 bs (2 * i) + 256 * u8 bs (2 * i + 1)

variable [CodeEnv]

/-! ## Addresses -/

/-- `sbr` (the element's `SpectralBandReplication`, at `che + 0x28920`). -/
abbrev sbrA (t : MachineData) : BitVec 64 := arg1 t + 0x28920#64

/-- `&sbr->data[ch]` (`SBRData` is 0x15ac0 bytes at `sbr + 0x80`). -/
abbrev dA (t : MachineData) (ch : Nat) : BitVec 64 :=
  sbrA t + BitVec.ofNat 64 (0x80 + 0x15ac0 * ch)

/-- `downsampled` (`ac->oc[1].m4ac.ext_sample_rate < sbr->sample_rate`): 0 or 1. -/
abbrev dsN (x : Args) : Nat := if x.extRate.toInt < x.sampleRate.toInt then 1 else 0

abbrev c8 (a v : BitVec 64) : Mem 64 → Prop := Int.toBytes 8 v.toInt =@ a

abbrev c4 (a : BitVec 64) (v : Nat) : Mem 64 → Prop := Int.toBytes 4 (v : Int) =@ a

/-! ## The footprint (groups; each a `def`, opened by its view lemma) -/

/-- The scalar fields of `*sbr`. -/
def ScW (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  cell4 s x.sampleRate ⋆ (cell4 (s + 0x4#64) x.start ⋆ (cell4 (s + 0x8#64) x.ready
    ⋆ (cell4 (s + 0xc#64) x.idAac ⋆ (4 ?@ (s + 0x10#64) ⋆ (cell4 (s + 0x18#64) x.reset
    ⋆ (cell4 (s + 0x1c#64) x.spLo ⋆ (Int.toBytes 2 x.spHi.toInt =@ (s + 0x20#64)
    ⋆ (c4 (s + 0x30#64) x.limGains ⋆ (cell4 (s + 0x34#64) x.interpol
    ⋆ (cell4 (s + 0x38#64) x.smooth ⋆ (cell4 (s + 0x3c#64) x.coupling
    ⋆ (c4 (s + 0x40#64) x.k0 ⋆ (c4 (s + 0x54#64) x.kx0 ⋆ (c4 (s + 0x58#64) x.kx1
    ⋆ (c4 (s + 0x5c#64) x.m0 ⋆ (c4 (s + 0x60#64) x.m1
    ⋆ cell4 (s + 0x64#64) x.pushed))))))))))))))))

/-- The frequency tables and their sizes, and the patches. -/
def TabW (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  c4 (s + 0x4c1e0#64) x.n0 ⋆ (c4 (s + 0x4c1e4#64) x.n1 ⋆ (c4 (s + 0x4c1e8#64) x.nq
    ⋆ (c4 (s + 0x4c1ec#64) x.nlim ⋆ (x.ftLow =@ (s + 0x4c252#64)
    ⋆ (x.ftHigh =@ (s + 0x4c284#64) ⋆ (x.ftNoise =@ (s + 0x4c2e6#64)
    ⋆ (x.ftLim =@ (s + 0x4c2f2#64) ⋆ (c4 (s + 0x4c330#64) x.npatch
    ⋆ (x.pnum =@ (s + 0x4c334#64) ⋆ x.pstart =@ (s + 0x4c33a#64))))))))))

/-- The scalar fields of `sbr->data[ch]` with values `v`. -/
def DScW (v : DV) (t : MachineData) (ch : Nat) : Mem 64 → Prop :=
  let d := dA t ch
  4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
    ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64)
    ⋆ (4 ?@ (d + 0x64#64) ⋆ (cell4 (d + 0x3900#64) v.vOff ⋆ (8 ?@ (d + 0x3904#64)
    ⋆ (c4 (d + 0x7920#64) v.ypos ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
    ⋆ Int.toBytes 8 v.idx.toInt =@ (d + 0x15aac#64))))))))))))

/-- The raw arrays of `sbr->data[ch]` (`d = &sbr->data[ch]`):
`synthesis_filterbank_samples` (9216 bytes at `d + 0x80`),
`analysis_filterbank_samples` (5248 at `d + 0x2480`; its first 2048 bytes are part of
the larger synthesis window, see `qmfVSize`), `bw_array[5]`, `W[2][32][32][2]`,
then `Y[2][38][64][2]` together with the first 24 bytes of `g_temp` (38936 bytes at
`d + 0x7930`, see `HfData`), the rest of `g_temp` (8040), `q_temp[42][48]`
(8064), `s_indexmapped`, the envelope and noise factors. The scalar gaps:
`bs_add_harmonic_flag` (`d + 0x4`), `bs_add_harmonic` (`d + 0x31`), `bs_amp_res`
(`d + 0x64`), `e_a` (`d + 0x3904`), all in `DScW`. Per-object views:
`gtemp_rejoin` (`Y[0]`, `Y[1]`, `g_temp ++ q_temp`), `a3_overread_carve`. -/
def DArrW (t : MachineData) (ch : Nat) : Mem 64 → Prop :=
  let d := dA t ch
  Blocks [(d + 0x80#64, 9216), (d + 0x2480#64, 5248), (d + 0x390c#64, 20),
    (d + 0x3920#64, 16384), (d + 0x7930#64, 38936), (d + 0x11148#64, 8040),
    (d + 0x130b0#64, 8064),
    (d + 0x15030#64, 432), (d + 0x151e0#64, 432), (d + 0x15390#64, 1728),
    (d + 0x15a50#64, 15), (d + 0x15a60#64, 60)]

/-- The work arrays of `*sbr` (`s = sbr`): `X_low`, `X_high`, `X[0]`, `X[1]` (0x4c00
bytes each), `alpha0/1`, `e_origmapped`, `q_mapped`, `s_mapped`, `e_curr`, `q_m`,
`s_m`, `gain` (1536 bytes each), `qmf_filter_scratch`. The PS state at
`s + 0x2b600` is `PsW`. ScW gap name: `usac`/`inter_tes` (`s + 0x10`, 4 bytes). -/
def ArrW (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  Blocks [(s + 0x4c340#64, 10240), (s + 0x4eb40#64, 20480),
    (s + 0x53b40#64, 0x4c00), (s + 0x58740#64, 0x4c00), (s + 0x5d340#64, 512),
    (s + 0x5d540#64, 512), (s + 0x5d740#64, 1536), (s + 0x5dd40#64, 1536),
    (s + 0x5e340#64, 384), (s + 0x5e4c0#64, 1536), (s + 0x5eac0#64, 1536),
    (s + 0x5f0c0#64, 1536), (s + 0x5f6c0#64, 1536), (s + 0x5fcc0#64, 1280)]

/-- `sbr->ps` (`PSContext`, 0x20be0 bytes at `sbr + 0x2b600`): `ps->common` (764
bytes, values `x.psc`), padding, the raw middle, `opd_hist ++ ipd_hist` (68 bytes,
values `x.psh`), the rest (with `dsp`). Owning the whole struct over-approximates the
writes of `ff_ps_apply` (`[768, 134036)`). -/
def PsW (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let p := sbrA t + 0x2b600#64
  x.psc =@ p ⋆ (4 ?@ (p + 764#64) ⋆ (133200 ?@ (p + 768#64)
    ⋆ (x.psh =@ (p + 133968#64) ⋆ 76 ?@ (p + 134036#64))))

/-- The `sbr->dsp` slots. -/
def DspW (e : Env) (t : MachineData) : Mem 64 → Prop :=
  let p := sbrA t + 0x601e0#64
  FnCell p e.fs.sum64x5 ⋆ (FnCell (p + 0x8#64) e.fs.sumSquare
    ⋆ (FnCell (p + 0x10#64) e.fs.qfs.negOdd64 ⋆ (FnCell (p + 0x18#64) e.fs.preShuffle
    ⋆ (FnCell (p + 0x20#64) e.fs.postShuffle ⋆ (FnCell (p + 0x28#64) e.fs.qfs.deintNeg
    ⋆ (FnCell (p + 0x30#64) e.fs.qfs.deintBfly ⋆ (FnCell (p + 0x38#64) e.fs.autocorr
    ⋆ (FnCell (p + 0x40#64) e.fs.hfGen ⋆ (FnCell (p + 0x48#64) e.fs.hfs.gfilt
    ⋆ (FnCell (p + 0x50#64) e.fs.hfs.noise0 ⋆ (FnCell (p + 0x58#64) e.fs.hfs.noise1
    ⋆ (FnCell (p + 0x60#64) e.fs.hfs.noise2 ⋆ FnCell (p + 0x68#64) e.fs.hfs.noise3))))))))))))

/-- The other function-pointer cells (`sbr->c`, the `av_tx` fields, `*ac->fdsp`), the
`av_tx` contexts, the `av_tx` tables `TxTab` and the PS tables `PsTab` (all disjoint
by `⋆`), and `Ext`. -/
def FnW (e : Env) (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  Int.toBytes 8 x.anaCtx.toInt =@ (s + 0x601c0#64) ⋆ (FnCell (s + 0x601c8#64) e.fs.mdctAna
    ⋆ (Int.toBytes 8 x.synCtx.toInt =@ (s + 0x601d0#64) ⋆ (FnCell (s + 0x601d8#64) e.fs.qfs.tx
    ⋆ (FnCell (s + 0x60250#64) e.fs.lfGen ⋆ (FnCell (s + 0x60258#64) e.fs.hfAsm
    ⋆ (FnCell (s + 0x60260#64) e.fs.xGen ⋆ (FnCell (s + 0x60268#64) e.fs.hfInv
    ⋆ (FnCell x.fdsp e.fs.qfs.fmul ⋆ (FnCell (x.fdsp + 0x30#64) e.fs.qfs.fmulAdd
    ⋆ (FnCell (x.fdsp + 0x38#64) e.fs.fmulRev ⋆ (e.Ctx x.anaCtx ⋆ (e.Ctx x.synCtx
    ⋆ (e.TxTab ⋆ (e.PsTab ⋆ e.Ext))))))))))))))

/-- The fields of `*ac`. -/
def AcW (x : Args) (t : MachineData) : Mem 64 → Prop :=
  Int.toBytes 8 x.avctx.toInt =@ (arg0 t + 0x8#64)
    ⋆ (Int.toBytes 8 x.fdsp.toInt =@ (arg0 t + 0x2550#64)
    ⋆ (cell4 (arg0 t + 0x57f4#64) x.extRate ⋆ cell4 (arg0 t + 0x5800#64) x.ps))

/-- The read-only constants of the code (`.rodata.cst*`, `.lrodata` of `aacsbr.o`); the
value of `LCPI14_4` (`1E20`, compared against by the dequantisation assert, see
`DequantFloatModel`) is known; `sbr_hf_assemble`'s (`HfData`: `ff_sbr_noise_table`, `ps_noise*`,
`.LCPI17_*`, the mask `.LCPI17_11 = {0x1ff, 3, 0, 0}` with its contents); and
`pd_reverse` of `float_dsp.o`, the mask `vector_fmul_reverse` reads (note F1,
`VectorFmulRevF`). -/
def CstW : Mem 64 → Prop :=
  Blocks [(lab "LCPI14_0", 4), (lab "LCPI14_5", 4), (lab "LCPI14_6", 4), (lab "LCPI14_9", 4),
    (lab "LCPI14_10", 4), (lab "LCPI14_11", 4), (lab "LCPI14_12", 4), (lab "LCPI14_13", 4),
    (lab "LCPI14_14", 4), (lab "LCPI14_15", 4), (lab "LCPI14_16", 4), (lab "LCPI14_17", 4),
    (lab "LCPI14_3", 8), (lab "LCPI14_1", 16), (lab "LCPI14_2", 16),
    (lab "LCPI14_8", 16), (lab "exp2_tab", 16), (lab "bw_tab", 16), (lab "limgain", 16),
    (lab "sbr_qmf_window_ds", 1280), (lab "ff_ps_neg", 16), (lab "ps_mask", 16),
    (lab "LCPI19_0", 4), (lab "LCPI19_1", 4), (lab "LCPI19_2", 16), (lab "ps_mask3", 16),
    (lab "sbr_qmf_window_us", 2560), (lab "LCPI15_1", 4), (lab "ps_mask2", 16),
    (lab "ff_sbr_noise_table", 4160), (lab "ps_noise0", 16), (lab "ps_noise13", 48), (lab "ps_noise2", 16),
    (lab "LCPI17_6", 4), (lab "LCPI17_7", 4), (lab "LCPI17_8", 4), (lab "LCPI17_9", 4),
    (lab "LCPI17_10", 4), (lab "LCPI17_12", 4), (lab "pd_reverse", 32)]
    ⋆ (Int.toBytes 8 dbl1E20.toInt =@ lab "LCPI14_4" ⋆ Int.toBytes 16 0x3000001ff =@ lab "LCPI17_11")

/-- The output buffers `L`, `R` (`8192 >>> downsampled` bytes each). -/
def OutW (x : Args) (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg3 t, 8192 >>> dsN x), (arg4 t, 8192 >>> dsN x)]

/-- The whole footprint. -/
abbrev ApplyF (e : Env) (x : Args) (t : MachineData) : Mem 64 → Prop :=
  ScW x t ⋆ (TabW x t ⋆ (DScW x.d0 t 0 ⋆ (DScW x.d1 t 1 ⋆ (DArrW t 0 ⋆ (DArrW t 1
    ⋆ (ArrW t ⋆ (PsW x t ⋆ (DspW e t ⋆ (FnW e x t ⋆ (AcW x t ⋆ (CstW ⋆ OutW x t)))))))))))

/-! ## `SbrWF` -/

/-- What `ff_aac_sbr_apply` needs of one channel's `SBRData` (kinds as in `Spec.lean`'s
`SbrWF` section: all invariants of the decoder unless marked). `live` says the channel's
grid is the output of a successful `read_sbr_grid` (`SbrWF` passes `start ≠ 0` for
channel 0 and `start ≠ 0 ∧ id_aac = CPE` for channel 1): `read_sbr_grid` stores the
grid before its checks (`aacsbr_template.c:662-735` vs. `740-752`), so after a rejected
grid `t_env` can be non-monotone or above 19, and the `t_env` clauses hold only for
live data. Note A1: the borders are bounded by `numTimeSlots + 3 = 19`, not 16
(`aacsbr_template.c:651, 756-772, 788`). `synthesis_filterbank_samples_offset ≤ 1664`
(`aacsbr_template.c:88-89, 1427-1432`); see `qmfVSize`. -/
def DWF (live : Prop) (v : DV) : Prop :=
  v.freqRes.length = 9 ∧ v.invf.length = 10 ∧ v.te.length = 10 ∧ v.tq.length = 3
  ∧ v.nenv ≤ 8
  ∧ (∀ e, e ≤ v.nenv → u8 v.freqRes e ≤ 1)   -- bs_freq_res[1..bs_num_env] is read
  ∧ v.nnoise ≤ 2 ∧ (∀ i, i < 5 → u8 v.invf i ≤ 3)
  ∧ v.ypos ≤ 1
  ∧ u8 v.te 9 ≤ 19
  ∧ (∀ q, q ≤ v.nnoise → u8 v.tq q ≤ 19)
  ∧ v.idx.toNat % 2 ^ 32 ≤ 515 ∧ v.idx.toNat / 2 ^ 32 < 4
  ∧ v.vOff.toInt ≤ 1664 ∧ v.vOff.toNat % 8 = 0
  ∧ (live → 1 ≤ v.nenv ∧ (∀ e, e ≤ v.nenv → u8 v.te e ≤ 19)
      ∧ (∀ e, e < v.nenv → u8 v.te e < u8 v.te (e + 1)))

/-- The frequency tables of a started decoder: each table inside the high band
`[kx[1], kx[1] + m[1]]`, nondecreasing; the patches inside `X_low`/`X_high`.

The last four conjuncts are the M4-F1 facts. They hold because, while `start == 1`, every
table field is the output of the last successful `sbr_make_f_master` + `sbr_make_f_derived`:
both are called only from `sbr_reset`, which calls `sbr_turnoff` (`start = 0`) on any
failure; `start = 1` is set only by a header, and the next header is forced to reset; and
`sbr_turnoff` does not clear the tables, hence the `start ≠ 0` guard in `SbrWF`.
Code citations are to libavcodec/aacsbr_template.c (FFmpeg n8.1):
* F1 `f_tablenoise[0] = kx[1]`: `kx[1] = f_tablehigh[0]` (l.565),
  `f_tablelow[0] = f_tablehigh[0]` (l.578), `f_tablenoise[0] = f_tablelow[0]` (l.606).
* F2 `f_tablenoise[n_q] = kx[1] + m[1]`: `kx[1] + m[1] = f_tablehigh[n[1]]` (l.564-565). The
  last noise border step divides by 1 (l.609), so it is `f_tablelow[n[0]]`, which is
  `f_tablehigh[n[1]]` (l.560, l.579-581).
* F3 `1 ≤ n_q` (`FFMAX(1, …)`, l.593-596; `n_q ≤ 5` is checked at l.600-604).
* F5 `Σ patch_num_subbands ≤ m[1]`: `usb` starts at `kx[1]` (l.498), each counted patch adds
  `sb - usb` and sets `usb = sb` (l.530-536), and `sb ≤ f_master[n_master] = kx[1] + m[1]`
  (l.504-506, 516-517, 541, 562); l.546 only drops the last patch.
With F2, F5 and the nondecreasing `f_tablenoise` (F4, above), `sbr_hf_gen`'s noise band search
(l.1499-1513) ends with `g ≤ n_q - 1 ≤ 4`, so `bw_array[g]` stays in `bw_array[5]`. -/
def TabWF (x : Args) : Prop :=
  x.ftLow.length = 50 ∧ x.ftHigh.length = 98 ∧ x.ftNoise.length = 12 ∧ x.ftLim.length = 60
  ∧ x.pnum.length = 6 ∧ x.pstart.length = 6
  ∧ 1 ≤ x.m1
  ∧ (∀ i, i ≤ x.n1 → x.kx1 ≤ u16 x.ftHigh i ∧ u16 x.ftHigh i ≤ x.kx1 + x.m1)
  ∧ (∀ i, i ≤ x.n0 → x.kx1 ≤ u16 x.ftLow i ∧ u16 x.ftLow i ≤ x.kx1 + x.m1)
  ∧ (∀ i, i ≤ x.nq → x.kx1 ≤ u16 x.ftNoise i ∧ u16 x.ftNoise i ≤ x.kx1 + x.m1)
  ∧ (∀ i, i ≤ x.nlim → x.kx1 ≤ u16 x.ftLim i ∧ u16 x.ftLim i ≤ x.kx1 + x.m1)
  ∧ (∀ i, i < x.n1 → u16 x.ftHigh i < u16 x.ftHigh (i + 1))   -- f_master: vDk > 0
  ∧ (∀ i, i < x.n0 → u16 x.ftLow i ≤ u16 x.ftLow (i + 1))
  ∧ (∀ i, i < x.nq → u16 x.ftNoise i ≤ u16 x.ftNoise (i + 1))
  ∧ (∀ i, i < x.nlim → u16 x.ftLim i ≤ u16 x.ftLim (i + 1))
  ∧ (∀ i, i < x.npatch → u8 x.pstart i + u8 x.pnum i ≤ 32)
  ∧ x.kx1 + (List.range x.npatch).foldl (fun a i => a + u8 x.pnum i) 0 ≤ 64
  ∧ u16 x.ftNoise 0 = x.kx1                                                   -- F1
  ∧ u16 x.ftNoise x.nq = x.kx1 + x.m1                                         -- F2
  ∧ 1 ≤ x.nq                                                                  -- F3
  ∧ (List.range x.npatch).foldl (fun a i => a + u8 x.pnum i) 0 ≤ x.m1         -- F5

/-- `SbrWF`: the decoder-state invariant `ff_aac_sbr_apply` assumes (M1–M3 clauses
of `Spec.lean` plus the bounds the build's checks and `sbr_mapping`'s loops need). -/
def SbrWF (x : Args) : Prop :=
  x.kx0 ≤ 32 ∧ x.kx1 ≤ 32 ∧ x.kx0 + x.m0 ≤ 64 ∧ x.kx1 + x.m1 ≤ 64 ∧ x.m1 ≤ 48 ∧ x.k0 ≤ 32
  ∧ x.limGains ≤ 3 ∧ x.n0 ≤ 24 ∧ x.n1 ≤ 48 ∧ x.nq ≤ 5 ∧ x.nlim ≤ 29 ∧ x.npatch ≤ 6
  ∧ (x.start ≠ 0 → TabWF x)
  ∧ DWF (x.start ≠ 0) x.d0 ∧ DWF (x.start ≠ 0 ∧ x.idAac = 1) x.d1
  ∧ PsWF x.psc x.psh

/-- Layout: alignments of the data and of the 16/32-byte constants read by aligned vector
operations (`LCPI14_1/2/8`, `sbr_qmf_window_ds/us`, `ff_ps_neg`, `ps_mask`, `ps_mask2`, `ps_mask3`, `ps_noise0/13/2`,
and `pd_reverse` of `float_dsp.o`, note F1, `VectorFmulRevC`; facts
of the linked object's section layout), the stack convention, the signed bound of
`qmf_post_shuffle`'s operand. -/
def LayoutC (x : Args) (t : MachineData) : Prop :=
  isAligned 32 (arg1 t) = true ∧ isAligned 32 (sbrA t) = true
  ∧ isAligned 32 (arg3 t) = true ∧ isAligned 32 (arg4 t) = true
  ∧ isAligned 16 (t.regs.get64 .rsp + 8#64) = true
  ∧ isAligned 16 (lab "LCPI14_1") = true ∧ isAligned 16 (lab "LCPI14_2") = true
  ∧ isAligned 16 (lab "LCPI14_8") = true ∧ isAligned 32 (lab "sbr_qmf_window_ds") = true
  ∧ isAligned 16 (lab "ff_ps_neg") = true
  ∧ (isAligned 16 (lab "ps_mask") = true
      ∧ isAligned 32 (lab "sbr_qmf_window_us") = true ∧ isAligned 16 (lab "ps_mask2") = true)
  ∧ isAligned 16 (lab "ps_mask3") = true
  ∧ (isAligned 16 (lab "ps_noise0") = true ∧ isAligned 16 (lab "ps_noise13") = true
      ∧ isAligned 16 (lab "ps_noise2") = true)
  ∧ isAligned 32 (lab "pd_reverse") = true
  ∧ (sbrA t + 0x5fcc0#64).toInt + 1280 < 2 ^ 63

def ApplyC (x : Args) (t : MachineData) : Prop := SbrWF x ∧ LayoutC x t

/-! ## The specification -/

/-- Own bytes (`push rbp`, five saved registers, `sub $0x198`), then the deepest
call: `sbr_hf_assemble`'s return-address slot and its `0x290 + k`. -/
abbrev applyNeed (k : Nat) : Nat := 0x460 + k

abbrev ApplyPre (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (applyNeed k) (ApplyF e x t ⋆ x.R) ra t ∧ ApplyC x t

/-- On return the footprint is owned again, with other contents: the same groups at
values `y` (the pointers that place them unchanged), with the decoder state apply
does not write unchanged (`KeepD`, INV-D5: both channels' `bs_num_env`, `t_env`,
`bs_freq_res`, `t_q`, `ps->common`, and the frequency tables with `k[0]`; `start` and
`spectrum_params` kept, or cleared together by `sbr_turnoff`, so that I1 is kept,
`Args.KeepT.i1`), and with the decoder invariant `SbrWF`
re-established for `y` (the fields apply writes: both channels'
`synthesis_filterbank_samples_offset`, from `sbr_qmf_synthesis`, and the PS phase
histories, from `ff_ps_apply`), so that `ApplyC y t` holds again (`LayoutC` does not
depend on the values). -/
abbrev ApplyFPost (e : Env) (x : Args) (t : MachineData) : Mem 64 → Prop :=
  fun m => ∃ y : Args, y.extRate = x.extRate ∧ y.fdsp = x.fdsp ∧ y.anaCtx = x.anaCtx
    ∧ y.synCtx = x.synCtx ∧ y.sampleRate = x.sampleRate ∧ x.KeepD y ∧ SbrWF y
    ∧ y.avctx = x.avctx ∧ y.ps = x.ps ∧ ApplyF e y t m

abbrev ApplyPost (k : Nat) (e : Env) (x : Args) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (applyNeed k) (ApplyFPost e x t ⋆ x.R) ra t s

/-- The callees at `k` bytes of stack: the proved `SBRDSPContext` contracts at the
slot contents, the C procedures of the cluster (the `sbr->c` slots hold them,
`ff_aacsbr_func_ptr_init`), and the assumed contracts. -/
abbrev ApplyCallees (k : Nat) (e : Env) : Prop :=
  LeafSpecAt e.fs.sum64x5 0 Sum64x5F Sum64x5C
  ∧ LeafSpecAt e.fs.sumSquare 0 SumSquareF SumSquareC
  ∧ LeafSpecAt e.fs.preShuffle 0 QmfPreShuffleF QmfPreShuffleC
  ∧ LeafSpecAt e.fs.postShuffle 0 QmfPostShuffleF QmfPostShuffleC
  ∧ LeafSpecAt e.fs.hfGen 0 HfGenF HfGenC
  ∧ e.fs.lfGen = entry "sbr_lf_gen" ∧ LfGenSpec k
  ∧ e.fs.hfInv = entry "sbr_hf_inverse_filter" ∧ HfInverseFilterSpec e.fs.autocorr
  ∧ e.fs.hfAsm = entry "sbr_hf_assemble" ∧ HfAssembleSpec k e.fs.hfs
  ∧ e.fs.xGen = entry "sbr_x_gen" ∧ XGenSpec k
  ∧ QmfSynthesisSpec 0 k e.Ctx e.TxTab e.fs.qfs ∧ QmfSynthesisSpec 1 k e.Ctx e.TxTab e.fs.qfs
  ∧ TxSpec e.Ctx e.TxTab k e.fs.mdctAna ∧ VectorFmulRevSpec k e.fs.fmulRev
  ∧ MemcpySpec k ∧ MemsetSpec k ∧ PsApplySpec e.PsTab k ∧ AvLogSpec e.Ext k ∧ AbortSpec

/-- `ff_aac_sbr_apply(ac, che, id_aac, L, R)` with its callees at `k` bytes of stack.
What the statement does and does not say:
1. hf_assemble's footprint includes the 24 bytes after Y[Ypos] (see `HfData`,
   `a2_row_spill`). For Ypos=0 the theorem itself bounds the access to Y[1] by these
   24 bytes; for Ypos=1 those bytes belong to `g_temp`, which hf_assemble owns anyway,
   so the 24-byte bound there rests on `a2_row_spill` and the row-crossing discipline
   (HfAssemble crosses a row of `Y` only through `a2_row_spill`; checked by tv.sh),
   not on the footprint.
2. The synthesis footprint in `v0` is `qmfVSize`; the call site carves it with
   `a3_overread_carve` when it is the larger window.
3. Granularity: the theorem bounds each procedure's accesses by the union of the bytes
   it owns; reads and writes are not distinguished; within `ApplyF`'s union, object and
   row boundaries are not enforced by the theorem (splitting an owned union into
   objects does not change it). Items 1 and 2 are fixed at the hf_assemble and
   synthesis boundaries and by `a2_row_spill`.
4. Trusted: `ff_ps_apply` given `PsWF`, `top ≤ 64` and 16-alignment (`PsApplySpec`);
   `av_tx` with its tables `TxTab` (`TxSpec`); `float_dsp` for `1 ≤ len < 2^30`;
   `memcpy`, `memset`, `av_log`; the placement of the text (`Program.PlacedIn`); the x86
   dsp initialisation (the slot contents, by cpu flags). -/
abbrev ApplySpec (k : Nat) (e : Env) : Prop :=
  cenv.ProcSpec (entry "ff_aac_sbr_apply") (ApplyPre k e) (ApplyPost k e)

/-! ## I1 and the precondition

`ApplyFPost` keeps I1 (`Args.KeepD.i1`). The values of `spectrum_params` in `ScW` add no
assumption: `ScW` is `ScWRaw` (those six bytes unknown) at some values (`scWRaw_eq`). -/

/-- I1 survives apply: `start` and `spectrum_params` are kept, or cleared together. -/
theorem Args.KeepT.i1 {x y : Args} (h : x.KeepT y) (hx : x.I1) : y.I1 := by
  unfold Args.KeepT at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := h
  intro hy
  rcases h with ⟨-, hl, -⟩ | ⟨hs, hl, -⟩
  · rw [hl]; decide
  · rw [hl]; exact hx (hs ▸ hy)

theorem Args.KeepD.i1 {x y : Args} (h : x.KeepD y) (hx : x.I1) : y.I1 :=
  h.2.2.2.2.2.2.2.2.2.i1 hx

/-- The postcondition keeps I1: input I1 and apply give output I1. -/
theorem applyFPost_i1 {e : Env} {x : Args} {t : MachineData} {m : Mem 64} (hx : x.I1)
    (h : ApplyFPost e x t m) : ∃ y : Args, y.I1 ∧ ApplyF e y t m := by
  obtain ⟨y, -, -, -, -, -, hk, -, -, -, hm⟩ := h
  exact ⟨y, hk.i1 hx, hm⟩

theorem sep_ex_l {α : Type} (P : α → Mem 64 → Prop) (R : Mem 64 → Prop) :
    ((fun m => ∃ v, P v m) ⋆ R) = fun m => ∃ v, (P v ⋆ R) m := by
  funext m; apply propext; constructor
  · rintro ⟨a, b, h1, h2, ⟨v, hv⟩, hr⟩; exact ⟨v, a, b, h1, h2, hv, hr⟩
  · rintro ⟨v, a, b, h1, h2, hv, hr⟩; exact ⟨a, b, h1, h2, ⟨v, hv⟩, hr⟩

theorem sep_ex_r {α : Type} (P : α → Mem 64 → Prop) (L : Mem 64 → Prop) :
    (L ⋆ fun m => ∃ v, P v m) = fun m => ∃ v, (L ⋆ P v) m := by
  funext m; apply propext; constructor
  · rintro ⟨a, b, h1, h2, hl, ⟨v, hv⟩⟩; exact ⟨v, a, b, h1, h2, hl, hv⟩
  · rintro ⟨v, a, b, h1, h2, hl, hv⟩; exact ⟨a, b, h1, h2, hl, ⟨v, hv⟩⟩

theorem toBytes_ofInt_ofBytes (n : Nat) (bs : List UInt8) (h : bs.length = n) :
    Int.toBytes n (BitVec.ofInt (8 * n) (Int.ofBytes bs)).toInt = bs := by
  rw [BitVec.toInt_ofInt, ← Int.toBytes_emod, Int.take]
  have e : (Int.ofBytes bs).bmod (2 ^ (8 * n)) % (2 ^ (8 * n) : Int)
      = Int.ofBytes bs % 2 ^ (8 * n) := Int.bmod_emod
  rw [e, show Int.ofBytes bs % 2 ^ (8 * n) = (Int.ofBytes bs).take (8 * n) from rfl,
    Int.toBytes_emod, ← h, Int.toBytes_ofBytes_all]

/-- An unknown `n`-byte region is a known one with some `8n`-bit value. -/
theorem block_eq_exists (a : BitVec 64) (n : Nat) (hn : n ≤ 2 ^ 64) :
    (n ?@ a) = fun m => ∃ v : BitVec (8 * n), (Int.toBytes n v.toInt =@ a) m := by
  funext m; apply propext; constructor
  · rintro ⟨-, bs, hlen, h⟩
    exact ⟨BitVec.ofInt (8 * n) (Int.ofBytes bs), by
      show (Int.toBytes n _).At a = m; rw [toBytes_ofInt_ofBytes n bs hlen]; exact h⟩
  · rintro ⟨v, h⟩
    exact ⟨hn, _, Int.toBytes_length .., h⟩


/-- `ScW` with the six bytes of `spectrum_params` unknown (`6 ?@`), as the footprint was
stated before they had values. -/
def ScWRaw (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  cell4 s x.sampleRate ⋆ (cell4 (s + 0x4#64) x.start ⋆ (cell4 (s + 0x8#64) x.ready
    ⋆ (cell4 (s + 0xc#64) x.idAac ⋆ (4 ?@ (s + 0x10#64) ⋆ (cell4 (s + 0x18#64) x.reset ⋆ (6 ?@ (s + 0x1c#64)
    ⋆ (c4 (s + 0x30#64) x.limGains ⋆ (cell4 (s + 0x34#64) x.interpol
    ⋆ (cell4 (s + 0x38#64) x.smooth ⋆ (cell4 (s + 0x3c#64) x.coupling
    ⋆ (c4 (s + 0x40#64) x.k0 ⋆ (c4 (s + 0x54#64) x.kx0 ⋆ (c4 (s + 0x58#64) x.kx1
    ⋆ (c4 (s + 0x5c#64) x.m0 ⋆ (c4 (s + 0x60#64) x.m1
    ⋆ cell4 (s + 0x64#64) x.pushed)))))))))))))))

/-- The precondition is unchanged in meaning: the raw `spectrum_params` bytes are the valued
cells at some `spLo`, `spHi` (and `Args` is universally quantified in `ApplySpec`). -/
theorem scWRaw_eq (x : Args) (t : MachineData) :
    ScWRaw x t = fun m => ∃ (lo : BitVec 32) (hi : BitVec 16),
      ScW { x with spLo := lo, spHi := hi } t m := by
  unfold ScWRaw ScW
  dsimp only
  rw [Block.split_at (sbrA t + 0x1c#64) 6 4 (by decide) (by decide),
    block_eq_exists (sbrA t + 0x1c#64) 4 (by decide),
    block_eq_exists (sbrA t + 0x1c#64 + BitVec.ofNat 64 4) (6 - 4) (by decide),
    Std.ExtHashMap.sep_assoc]
  simp only [sep_ex_l, sep_ex_r, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
    Nat.reduceSub, Nat.reduceMul]
  funext m
  exact propext ⟨fun ⟨v, w, h⟩ => ⟨w, v, h⟩, fun ⟨w, v, h⟩ => ⟨v, w, h⟩⟩

