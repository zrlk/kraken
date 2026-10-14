import Kraken.X64.Examples.Sbr.Parse.DecExtText
import Kraken.X64.Examples.Sbr.ParseModel
import Kraken.X64.Examples.Sbr.Parse.LibGb

/-!
# `ff_aac_sbr_decode_extension`: the specification

`ff_aac_sbr_decode_extension(ac, che, gb_host, crc, cnt, id_aac)` (`libavcodec/aacsbr_template.c`,
FFmpeg n8.1) parses one SBR extension payload of `cnt` bytes from the bit reader `*gb_host` into
the decoder state `sbr = &che->sbr` (at `che + 0x28920`). It copies the reader to its frame,
advances `*gb_host` by `cnt * 8 - 4` bits (clamped), reads an optional header
(`read_sbr_header`), runs `sbr_reset` if one was requested, and, if the decoder is started, reads
the channel element and its extensions (`read_sbr_data`, inlined). It returns `cnt`.

* The decoder-state values are `DS`: the model's `Args` and `Hid` (`ParseModel.lean`) and the
  raw scalars of `*sbr` the code and its callees read (`usac`, `bs_amp_res_header`, the six bytes
  of `spectrum_params`, which hold `Hid.start` and `Hid.xover`; `Hid.lb` is the cell
  `bs_limiter_bands`, see `DS.ok`).
* The footprint `DecF` owns the decoder state the parser reads or writes (`SbrF`: the scalars,
  both `SBRData`, `ps->common`, the frequency tables), the reader `*gb_host`, the fields of
  `*ac` and `ac->avctx->profile`, the bitstream buffer with the bytes after it, the read-only
  tables, and `Ext`, the state of the callees outside the footprint (logging, static tables).
* The callees are assumed contracts (hypotheses, `DecCallees`), stated on the same groups.
* The postcondition is the conclusion of `ParseModel.decext_spec`: `MI` and the live clauses
  `LiveC` hold of the values left, on every return. A run may also end at `abort` (reached from
  `read_sbr_grid`'s assertion) or at the compiler's bounds trap in `read_sbr_envelope` (`ud1` at
  `read_sbr_envelope.L60f9`): the spec is a `ProcSpecS` with these two stops (`DStops`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.DecExt

/-! ## Values -/

/-- The decoder-state values: the model's `Args` and `Hid`, and the raw scalars `sbr->usac`,
`sbr->bs_amp_res_header` and the six bytes of `spectrum_params`. -/
structure DS where
  a : Args
  h : Hid
  usac : BitVec 32
  amp : BitVec 32
  sp : List UInt8
  /-- `sbr->inter_tes` (+0x14, read by `read_sbr_envelope`). -/
  it : BitVec 32

/-- The lengths of the byte arrays of the footprint (so that each list cell is the array). -/
def Lens (x : Args) : Prop :=
  x.ftLow.length = 50 ∧ x.ftHigh.length = 98 ∧ x.ftNoise.length = 12 ∧ x.ftLim.length = 60
  ∧ x.pnum.length = 6 ∧ x.pstart.length = 6 ∧ x.psc.length = 764

/-- `Hid.start` is `spectrum_params.bs_start_freq` (byte 0), `Hid.xover` is
`spectrum_params.bs_xover_band` (byte 2); the array lengths. -/
def DS.ok (d : DS) : Prop :=
  d.sp.length = 6 ∧ d.h.start = u8 d.sp 0 ∧ d.h.xover = u8 d.sp 2 ∧ Lens d.a

/-- The invariant of the raw scalars: the field width of `bs_limiter_bands` (2 bits). -/
def DS.si (d : DS) : Prop := d.h.lb ≤ 3

/-- The bit reader: the buffer, `size_in_bits_plus8`, and the bytes `[buf, buf + L)` owned. -/
structure Rd where
  buf : BitVec 64
  p8 : BitVec 32
  L : Nat

/-- The reader's precondition: every read loads at most 4 bytes at `buf + index / 8` with
`index ≤ size_in_bits_plus8`. -/
def Rd.ok (r : Rd) (i : BitVec 32) : Prop :=
  i.toNat ≤ r.p8.toNat ∧ r.p8.toNat < 2 ^ 31 ∧ r.p8.toNat / 8 + 4 ≤ r.L ∧ r.L < 2 ^ 32

/-- `&sbr->data[b]`. -/
abbrev chA (s : BitVec 64) (b : Bool) : BitVec 64 := if b then s + 0x15b40#64 else s + 0x80#64

/-- The values of `sbr->data[b]`. -/
abbrev chV (d : DS) (b : Bool) : DV := if b then d.a.d1 else d.a.d0

/-- `DS` with `sbr->data[b]` at the values `v`. -/
def DS.setCh (d : DS) (b : Bool) (v : DV) : DS :=
  if b then { d with a := { d.a with d1 := v } } else { d with a := { d.a with d0 := v } }

/-- The fields of `SBRData` `read_sbr_grid` writes: `bs_num_env`, `bs_freq_res`, `bs_num_noise`,
`t_env` (with `t_env_num_env_old`), `t_q`. -/
abbrev dvGrid (v : DV) (n : Nat) (fr : List UInt8) (nn : Nat) (te tq : List UInt8) : DV :=
  { v with nenv := n, freqRes := fr, nnoise := nn, te := te, tq := tq }

/-- `read_sbr_grid`'s outcome on the values `v` left, result `ret` (`Grid.GridOut`): `DWF False`,
the border bound, `ret ∈ {0, -1}`, a live grid on `0`. -/
def GridV (v : DV) (ret : BitVec 32) : Prop :=
  DWF False v ∧ u8 v.te v.nenv ≤ 19 ∧ (ret = 0#32 ∨ ret = 0xffffffff#32)
  ∧ (ret = 0#32 → 1 ≤ v.nenv ∧ (∀ e, e ≤ v.nenv → u8 v.te e ≤ 19)
      ∧ (∀ e, e < v.nenv → u8 v.te e < u8 v.te (e + 1)))

/-- The fields of `Args` outside the footprint, and those no routine of the parser writes. -/
def XKeep (x y : Args) : Prop :=
  y.R = x.R ∧ y.fdsp = x.fdsp ∧ y.anaCtx = x.anaCtx ∧ y.synCtx = x.synCtx ∧ y.psh = x.psh
  ∧ y.avctx = x.avctx ∧ y.ps = x.ps

variable [CodeEnv]

/-! ## The footprint groups -/

/-- The scalar fields of `*sbr` at `s` (`0x0`–`0x80`). -/
def SbrS (d : DS) (s : BitVec 64) : Mem 64 → Prop :=
  cell4 s d.a.sampleRate ⋆ (cell4 (s + 0x4#64) d.a.start ⋆ (cell4 (s + 0x8#64) d.a.ready
  ⋆ (cell4 (s + 0xc#64) d.a.idAac ⋆ (cell4 (s + 0x10#64) d.usac ⋆ (cell4 (s + 0x14#64) d.it
  ⋆ (cell4 (s + 0x18#64) d.a.reset ⋆ (d.sp =@ (s + 0x1c#64)
  ⋆ (2 ?@ (s + 0x22#64) ⋆ (cell4 (s + 0x24#64) d.amp ⋆ (4 ?@ (s + 0x28#64)
  ⋆ (c4 (s + 0x2c#64) d.h.lb ⋆ (c4 (s + 0x30#64) d.a.limGains ⋆ (cell4 (s + 0x34#64) d.a.interpol
  ⋆ (cell4 (s + 0x38#64) d.a.smooth ⋆ (cell4 (s + 0x3c#64) d.a.coupling
  ⋆ (c4 (s + 0x40#64) d.a.k0 ⋆ (16 ?@ (s + 0x44#64) ⋆ (c4 (s + 0x54#64) d.a.kx0
  ⋆ (c4 (s + 0x58#64) d.a.kx1 ⋆ (c4 (s + 0x5c#64) d.a.m0 ⋆ (c4 (s + 0x60#64) d.a.m1
  ⋆ (cell4 (s + 0x64#64) d.a.pushed ⋆ 0x18 ?@ (s + 0x68#64)))))))))))))))))))))))

/-- One `SBRData` at `d` (`0x15ac0` bytes) with values `v`; the fields outside `DV` are raw. -/
def DataF (v : DV) (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
  ⋆ (3 ?@ (d + 0x15#64) ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (11 ?@ (d + 0x1c#64)
  ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64) ⋆ (3 ?@ (d + 0x61#64)
  ⋆ (4 ?@ (d + 0x64#64) ⋆ (0x3898 ?@ (d + 0x68#64) ⋆ (cell4 (d + 0x3900#64) v.vOff
  ⋆ (4 ?@ (d + 0x3904#64) ⋆ (4 ?@ (d + 0x3908#64) ⋆ (0x4014 ?@ (d + 0x390c#64)
  ⋆ (c4 (d + 0x7920#64) v.ypos
  ⋆ (0xe178 ?@ (d + 0x7924#64) ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
  ⋆ (3 ?@ (d + 0x15aa9#64) ⋆ (Apply.c8 (d + 0x15aac#64) v.idx ⋆ 12 ?@ (d + 0x15ab4#64))))))))))))))))))))))

/-- The frequency tables (`n`, `n_q`, `n_lim`, `f_master` raw, the four tables, the patches)
at `s + 0x4c1e0`. -/
def TabF (x : Args) (s : BitVec 64) : Mem 64 → Prop :=
  c4 (s + 0x4c1e0#64) x.n0 ⋆ (c4 (s + 0x4c1e4#64) x.n1 ⋆ (c4 (s + 0x4c1e8#64) x.nq
  ⋆ (c4 (s + 0x4c1ec#64) x.nlim ⋆ (98 ?@ (s + 0x4c1f0#64) ⋆ (x.ftLow =@ (s + 0x4c252#64)
  ⋆ (x.ftHigh =@ (s + 0x4c284#64) ⋆ (x.ftNoise =@ (s + 0x4c2e6#64)
  ⋆ (x.ftLim =@ (s + 0x4c2f2#64) ⋆ (2 ?@ (s + 0x4c32e#64) ⋆ (c4 (s + 0x4c330#64) x.npatch
  ⋆ (x.pnum =@ (s + 0x4c334#64) ⋆ x.pstart =@ (s + 0x4c33a#64))))))))))))

/-- The decoder state at `sbr = s`: the scalars, `data[0]`, `data[1]`, `ps->common`, the
tables. -/
def SbrF (d : DS) (s : BitVec 64) : Mem 64 → Prop :=
  SbrS d s ⋆ (DataF d.a.d0 (s + 0x80#64) ⋆ (DataF d.a.d1 (s + 0x15b40#64)
  ⋆ (d.a.psc =@ (s + 0x2b600#64) ⋆ TabF d.a s)))

/-- A `GetBitContext` at `g` as the callees see it: `buffer`, `index = i`, `size_in_bits`
(raw), `size_in_bits_plus8`. -/
abbrev GbR (g : BitVec 64) (r : Rd) (i : BitVec 32) : Mem 64 → Prop := GbW g r.buf i r.p8

/-- The bitstream bytes and the table `ceil_log2` (read by `read_sbr_grid`). -/
abbrev BufW (r : Rd) : Mem 64 → Prop := Blocks [(r.buf, r.L), (lab "ceil_log2", 6)]

/-- `ac->avctx` at `ac + 8`. -/
abbrev AvW (ac : BitVec 64) (x : Args) : Mem 64 → Prop := Apply.c8 (ac + 8#64) x.avctx

/-! ## The callees' contracts (assumed)

Each callee of the decoder state gets the whole decoder state `SbrF` at `sbr`, its bit reader at
`gb`, the bitstream, `ac->avctx`, the jump table of `read_sbr_grid` and `Ext`, and gives them
back. What it may change is stated on the values. The logical variable `CA` names the addresses
(`sbr`, `ac`, the reader), so a contract also covers a callee whose arguments do not include
them (`read_sbr_dtdf` gets `sbr->usac` and `ch_data`). -/

structure CA where
  R : Mem 64 → Prop
  d : DS
  s : BitVec 64
  ac : BitVec 64
  g : BitVec 64
  r : Rd
  i : BitVec 32

/-- A callee's footprint at the values `d` and index `i`. -/
abbrev CF (Ext : Mem 64 → Prop) (c : CA) (d : DS) (i : BitVec 32) : Mem 64 → Prop :=
  SbrF d c.s ⋆ (GbR c.g c.r i ⋆ (BufW c.r ⋆ (AvW c.ac d.a ⋆ (Grid.JtW ⋆ Ext))))

/-- The convention and the footprint at entry, the reader's precondition. -/
abbrev CPre (need : Nat) (Ext : Mem 64 → Prop) (c : CA) (ra : Int64) (t : MachineData) : Prop :=
  CallPre need (CF Ext c c.d c.i ⋆ c.R) ra t ∧ c.r.ok c.i ∧ c.d.ok

/-- The convention and the footprint at the return, at values `d'` and index `i'`. -/
abbrev CPost (need : Nat) (Ext : Mem 64 → Prop) (c : CA) (ra : Int64) (t s : MachineData)
    (P : DS → Prop) : Prop :=
  ∃ d' i', P d' ∧ d'.ok ∧ XKeep c.d.a d'.a ∧ i'.toNat ≤ c.r.p8.toNat
    ∧ CallPost need (CF Ext c d' i' ⋆ c.R) ra t s

/-- `read_sbr_header(sbr, gb, 0)` (l.188-247), from `MI` with `reset = 0` (and no address wrap of
`*sbr`, for `sbr_make_f_tablelim`; `bs_limiter_bands ≤ 3`): the values left satisfy `HI`
(`ParseModel.hdr_spec`) and keep `id_aac`; the channels, `ps->common`, `kx`, `m`, `bs_coupling` and `sample_rate` are not written
by it; `usac = is_usac = 0`; the field widths of `bs_freq_scale`, `bs_alter_scale` and
`bs_limiter_bands`. -/
abbrev HdrSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "read_sbr_header")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ arg0 t = c.s ∧ arg1 t = c.g
      ∧ (arg2 t).setWidth 32 = 0#32 ∧ MI (c.d.a, c.d.h) ∧ c.d.a.reset = 0
      ∧ c.s.toNat + 0x60000 < 2 ^ 64 ∧ c.d.h.lb ≤ 3)
    (fun c ra t s => CPost need Ext c ra t s fun d' => HI (d'.a, d'.h)
      ∧ d'.a.idAac = c.d.a.idAac ∧ d'.a.d0 = c.d.a.d0 ∧ d'.a.d1 = c.d.a.d1
      ∧ d'.a.psc = c.d.a.psc ∧ d'.a.coupling = c.d.a.coupling
      ∧ d'.usac = 0#32 ∧ u8 d'.sp 3 < 4 ∧ u8 d'.sp 4 < 2 ∧ d'.h.lb < 4)

/-- `sbr_reset(ac, sbr)` (l.1113-1124) with `reset ≠ 0`, from `HI` and the header's field widths
(`sbr_reset`'s `ResetC`), no address wrap of `*sbr`, the ABI stack alignment, the k-free stack
need (`resetStkMin + 8 ≤ rsp`, `resetStkMin = 0x9d0`): `MI`
(`ParseModel.reset_step`), `id_aac` kept, `DS.si` kept. -/
abbrev ResetSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "sbr_reset")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ arg0 t = c.ac ∧ arg1 t = c.s
      ∧ HI (c.d.a, c.d.h) ∧ c.d.a.reset ≠ 0
      ∧ u8 c.d.sp 3 ≤ 3 ∧ u8 c.d.sp 4 ≤ 1 ∧ c.d.h.lb ≤ 3 ∧ c.s.toNat + 0x60000 < 2 ^ 64
      ∧ isAligned 16 (t.regs.get64 .rsp + 8#64) = true ∧ 0x9d0 + 8 ≤ (t.regs.get64 .rsp).toNat)
    (fun c ra t s => CPost need Ext c ra t s fun d' => MI (d'.a, d'.h)
      ∧ d'.a.idAac = c.d.a.idAac ∧ d'.a.psc = c.d.a.psc ∧ (c.d.si → d'.si))

/-- `read_sbr_dtdf(sbr->usac, gb, ch_data, 0)` (l.837-856; the compiled routine takes `usac`),
with `bs_num_env ≤ 8`, `bs_num_noise ≤ 2` in both channels: no value of `DS` changes. -/
abbrev DtdfSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "read_sbr_dtdf")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ (arg0 t).setWidth 32 = c.d.usac ∧ arg1 t = c.g
      ∧ (arg2 t = c.s + 0x80#64 ∨ arg2 t = c.s + 0x15b40#64) ∧ (arg3 t).setWidth 32 = 0#32
      ∧ c.d.a.d0.nenv ≤ 8 ∧ c.d.a.d0.nnoise ≤ 2 ∧ c.d.a.d1.nenv ≤ 8 ∧ c.d.a.d1.nnoise ≤ 2)
    (fun c ra t s => CPost need Ext c ra t s fun d' => d' = c.d)

/-- `invfRead` on channel `ch` of the values. -/
def DS.invf (d : DS) (ch : Nat) (vals : Nat → Nat) : DS :=
  if ch = 0 then { d with a := { d.a with d0 := invfRead d.a.nq d.a.d0 vals } }
  else { d with a := { d.a with d1 := invfRead d.a.nq d.a.d1 vals } }

/-- `read_sbr_invf(sbr, gb, ch_data)` (l.827-835), with `n_q ≤ 5` and both `bs_invf_mode` arrays
of 10 bytes: `invfRead` (`ParseModel`). -/
abbrev InvfSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "read_sbr_invf")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ arg0 t = c.s ∧ arg1 t = c.g
      ∧ (arg2 t = c.s + 0x80#64 ∨ arg2 t = c.s + 0x15b40#64)
      ∧ c.d.a.nq ≤ 5 ∧ c.d.a.d0.invf.length = 10 ∧ c.d.a.d1.invf.length = 10)
    (fun c ra t s => CPost need Ext c ra t s fun d' =>
      ∃ vals, d' = c.d.invf (if arg2 t = c.s + 0x80#64 then 0 else 1) vals)

/-- `read_sbr_envelope(ac, sbr, gb, ch_data, ch)` (l.858-925), with `DWF False` of both channels,
`n[0] ≤ 24`, `n[1] ≤ 48`, `sbr` 32-aligned: no value of `DS` changes (abstraction 6 of the
model: the outcome is free). A run may stop at the bounds trap `read_sbr_envelope.L60f9`. -/
abbrev EnvSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  ProcSpecS (fun a => a = entry "read_sbr_envelope.L60f9") (entry "read_sbr_envelope")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ arg0 t = c.ac ∧ arg1 t = c.s ∧ arg2 t = c.g
      ∧ (arg3 t = c.s + 0x80#64 ∨ arg3 t = c.s + 0x15b40#64)
      ∧ DWF False c.d.a.d0 ∧ DWF False c.d.a.d1 ∧ c.d.a.n0 ≤ 24 ∧ c.d.a.n1 ≤ 48
      ∧ c.s.toNat % 32 = 0)
    (fun c ra t s => CPost need Ext c ra t s fun d' => d' = c.d)

/-- `read_sbr_noise(ac, sbr, gb, ch_data, ch)` (l.927-964), with `n_q ≤ 5` and `bs_num_noise ≤ 2`
in both channels: no value of `DS` changes. -/
abbrev NoiseSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "read_sbr_noise")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ arg0 t = c.ac ∧ arg1 t = c.s ∧ arg2 t = c.g
      ∧ (arg3 t = c.s + 0x80#64 ∨ arg3 t = c.s + 0x15b40#64)
      ∧ c.d.a.nq ≤ 5 ∧ c.d.a.d0.nnoise ≤ 2 ∧ c.d.a.d1.nnoise ≤ 2)
    (fun c ra t s => CPost need Ext c ra t s fun d' => d' = c.d)

/-- `read_sbr_grid(ac, sbr, gb, &sbr->data[b])`, with `DWF False` of the channel and
`t_env[bs_num_env] ≤ 19` (the logical variable is the pair `(c, b)`): the channel's values become
`dvGrid` of new fields with `GridV`; a run may end at `abort` (the routine's assertion). -/
abbrev GridSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  ProcSpecA (entry "read_sbr_grid")
    (fun (cb : CA × Bool) ra t => CPre need Ext cb.1 ra t ∧ arg0 t = cb.1.ac ∧ arg1 t = cb.1.s
      ∧ arg2 t = cb.1.g ∧ arg3 t = chA cb.1.s cb.2 ∧ DWF False (chV cb.1.d cb.2)
      ∧ u8 (chV cb.1.d cb.2).te (chV cb.1.d cb.2).nenv ≤ 19)
    (fun cb ra t s => CPost need Ext cb.1 ra t s fun d' => ∃ n fr nn te tq,
      d' = cb.1.d.setCh cb.2 (dvGrid (chV cb.1.d cb.2) n fr nn te tq)
      ∧ GridV (dvGrid (chV cb.1.d cb.2) n fr nn te tq) ((s.regs.get64 .rax).setWidth 32))

/-- The logical variables of `ff_ps_read_data`'s contract. -/
structure PA where
  R : Mem 64 → Prop
  c : List UInt8
  g : BitVec 64
  r : Rd
  i : BitVec 32

/-- `ff_ps_read_data(avctx, gb, &sbr->ps.common, bits_left)` (aacps_common.c:133-289): the 764
bytes of `ps->common` keep `PsWF`'s clauses (the conclusion of `ParseModel.psread_wf`) and the
routine's own invariant `PI` (the bounds its array accesses need); the result is in
`[0, bits_left]`. -/
abbrev PsSpec (PI : List UInt8 → Prop) (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "ff_ps_read_data")
    (fun (p : PA) ra t => CallPre need ((p.c =@ arg2 t ⋆ (GbR p.g p.r p.i ⋆ (BufW p.r ⋆ Ext)))
        ⋆ p.R) ra t ∧ p.r.ok p.i ∧ arg1 t = p.g ∧ p.c.length = 764 ∧ PI p.c
      ∧ 0 ≤ ((arg3 t).setWidth 32).toInt)
    (fun p ra t s => ∃ c' i', (∀ h, PsWF p.c h → PsWF c' h) ∧ c'.length = 764 ∧ PI c'
      ∧ i'.toNat ≤ p.r.p8.toNat
      ∧ 0 ≤ ((s.regs.get64 .rax).setWidth 32).toInt
      ∧ ((s.regs.get64 .rax).setWidth 32).toInt ≤ ((arg3 t).setWidth 32).toInt
      ∧ CallPost need ((c' =@ arg2 t ⋆ (GbR p.g p.r i' ⋆ (BufW p.r ⋆ Ext))) ⋆ p.R) ra t s)

/-- Assumed: `avpriv_request_sample(avc, msg, ...)` touches only `Ext`. -/
abbrev AvReqSpec (Ext : Mem 64 → Prop) (need : Nat) : Prop :=
  LeafSpec "avpriv_request_sample" need (fun _ => Ext) (fun _ => True)

/-- The callees: `kc` bytes of stack for the decoder-state callees, `k` for the logging ones. -/
abbrev DecCallees (PI : List UInt8 → Prop) (kc k : Nat) (Ext : Mem 64 → Prop) : Prop :=
  HdrSpec kc Ext ∧ ResetSpec kc Ext ∧ DtdfSpec kc Ext ∧ InvfSpec kc Ext ∧ EnvSpec kc Ext
  ∧ NoiseSpec kc Ext ∧ PsSpec PI kc Ext ∧ GridSpec kc Ext
  ∧ AvLogSpec Ext k ∧ AvReqSpec Ext k

/-! ## The specification -/

/-- The logical variables: the caller's memory, the decoder-state values, the reader `*gb_host`
(`index`, `size_in_bits`, the four padding bytes after `size_in_bits_plus8`, which the copy of
the struct reads), `ac->oc[1].m4ac.sample_rate`. -/
structure XA where
  R : Mem 64 → Prop
  d : DS
  r : Rd
  i : BitVec 32
  sib : BitVec 32
  pad : BitVec 32
  sr : BitVec 32

/-- `*gb_host` at `g` with `index = i`. -/
abbrev GhW (g : BitVec 64) (X : XA) (i : BitVec 32) : Mem 64 → Prop :=
  Apply.c8 g X.r.buf ⋆ (cell4 (g + 8#64) i ⋆ (cell4 (g + 0xc#64) X.sib ⋆ (cell4 (g + 0x10#64) X.r.p8
  ⋆ cell4 (g + 0x14#64) X.pad)))

/-- The fields of `*ac` (`avctx`, `oc[1].m4ac.sample_rate`, `ext_sample_rate`, `ps`,
`warned_he_aac_mono`) and `ac->avctx->profile`. -/
def AcF (ac : BitVec 64) (x : Args) (sr : BitVec 32) : Mem 64 → Prop :=
  cell4 (ac + 0x57e0#64) sr ⋆ (cell4 (ac + 0x57f4#64) x.extRate ⋆ (cell4 (ac + 0x5800#64) x.ps
  ⋆ (4 ?@ (ac + 0x8850#64) ⋆ 4 ?@ (x.avctx + 0x2b0#64))))

/-- The footprint at the values `d` and host index `i`. -/
def DecF (Ext : Mem 64 → Prop) (X : XA) (t : MachineData) (d : DS) (i : BitVec 32) :
    Mem 64 → Prop :=
  SbrF d (sbrA t) ⋆ (GhW (arg2 t) X i ⋆ (AvW (arg0 t) d.a ⋆ (AcF (arg0 t) d.a X.sr
  ⋆ (BufW X.r ⋆ (Grid.JtW ⋆ Ext)))))

/-- `DS.si` (`bs_limiter_bands ≤ 3`) and the layout of `*che` (as `ApplySpec.LayoutC`:
`che` and `sbr` 32-aligned, the signed bound past `sbr + 0x5fcc0`), and no address wrap of
`*sbr` (`sbr_reset`, `sbr_make_f_tablelim`), and the stack below `rsp` reaching the k-free part
of `sbr_reset`'s need below this frame (`0x70` own bytes, `sbr_reset`'s `resetStkMin = 0x9d0`, its
return slot). -/
def DecL (X : XA) (t : MachineData) : Prop :=
  X.d.si ∧ isAligned 32 (arg1 t) = true ∧ isAligned 32 (sbrA t) = true
  ∧ (sbrA t + 0x5fcc0#64).toInt + 1280 < 2 ^ 63 ∧ (sbrA t).toNat + 0x60000 < 2 ^ 64
  ∧ 0x70 + 0x9d0 + 8 ≤ (t.regs.get64 .rsp).toNat

/-- The side conditions: the model invariant `MI` of the values, `ff_ps_read_data`'s invariant
`PI` of `ps->common`, the reader, the jump table's
layout, the stack alignment (`vmovaps` to the frame). -/
def DecC (PI : List UInt8 → Prop) (X : XA) (t : MachineData) : Prop :=
  MI (X.d.a, X.d.h) ∧ X.d.ok ∧ PI X.d.a.psc ∧ X.r.ok X.i ∧ Grid.JtC
  ∧ (isAligned 16 (t.regs.get64 .rsp + 8#64) = true ∧ DecL X t)

/-- Own bytes (`push rbp`, five saved registers, `sub $0x38`), the return slot of a call, and the
callee's reservation. -/
abbrev decNeed (kc : Nat) : Nat := 0x70 + kc

abbrev DecPre (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t : MachineData) : Prop :=
  CallPre (decNeed kc) (DecF Ext X t X.d X.i ⋆ X.R) ra t ∧ DecC PI X t

/-- What a return leaves: values with `MI` and `LiveC` (the conclusion of
`ParseModel.decext_spec`), `Hid` tied to `spectrum_params`, the fields outside the footprint
kept, the host reader advanced within `size_in_bits_plus8`, and `cnt` returned. -/
def DecOut (PI : List UInt8 → Prop) (X : XA) (d' : DS) : Prop :=
  MI (d'.a, d'.h) ∧ LiveC d'.a ∧ d'.ok ∧ PI d'.a.psc ∧ XKeep X.d.a d'.a ∧ d'.si

abbrev DecPost (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t s : MachineData) : Prop :=
  ∃ d' i', DecOut PI X d' ∧ i'.toNat ≤ X.r.p8.toNat
    ∧ (s.regs.get64 .rax).setWidth 32 = (arg4 t).setWidth 32
    ∧ CallPost (decNeed kc) (DecF Ext X t d' i' ⋆ X.R) ra t s

/-- The safe stops: `abort`'s entry (`read_sbr_grid`'s assertion) and the bounds trap of
`read_sbr_envelope` (`ud1`, an envelope index ≥ 6). -/
abbrev DStops (a : Int64) : Prop := a = abortA ∨ a = entry "read_sbr_envelope.L60f9"

/-- `ff_aac_sbr_decode_extension` with its callees: it returns with `DecPost` or reaches a stop
of `DStops`. -/
abbrev DecExtSpec (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) : Prop :=
  ProcSpecS DStops (entry "ff_aac_sbr_decode_extension") (DecPre PI kc Ext) (DecPost PI kc Ext)

end Kraken.Examples.Sbr.DecExt
