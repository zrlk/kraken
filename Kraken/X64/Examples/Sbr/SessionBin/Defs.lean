import Kraken.X64.Examples.Sbr.Session
import Kraken.X64.Examples.Sbr.Parse.DecExtSpec
import Kraken.X64.Examples.Sbr.Parse.UsacSpec
import Kraken.X64.Examples.Sbr.Parse.PsSpec
import Kraken.X64.Examples.Sbr.Parse.ResetSpec
import Kraken.X64.Examples.Sbr.Parse.EnvVlc
import Kraken.X64.Examples.Sbr.Parse.GridSpec
import Kraken.X64.Examples.Sbr.Parse.HdrText
import Kraken.X64.Examples.Sbr.Parse.TlimText
import Kraken.X64.Examples.Sbr.Parse.GridText
import Kraken.X64.Examples.Sbr.Parse.DtdfText
import Kraken.X64.Examples.Sbr.Parse.InvfText
import Kraken.X64.Examples.Sbr.Parse.EnvText
import Kraken.X64.Examples.Sbr.Parse.NoiseText
import Kraken.X64.Examples.Sbr.Parse.PsText
import Kraken.X64.Examples.Sbr.Parse.InitText

/-!
# A decoding session over the binary: definitions

`Session.session_call` proves one call of `ff_aac_sbr_apply` in a session whose parser is an
abstract relation (`ParseStep`). The session here has the parser's entry points as machine code,
each by its proved specification: `ff_aac_sbr_decode_extension` (`DecExt.DecExtSpec`),
`ff_aac_sbr_decode_usac_data` (`Usac.UsacSpec`), `ff_aac_sbr_config_usac` (`Usac.ConfigSpec`),
and `ff_aac_sbr_apply` (`ff_aac_sbr_apply_linked`), with the caller's frame steps in between.

* Values: one record `SV = Args × HV`. `Args` are apply's values (`spLo`/`spHi` hold the six
  bytes of `spectrum_params`); `HV` holds the raw scalars of `*sbr` only the parser reads. The
  parser's records are views of it (`toDS`, `toUSt`, with the model's `Hid` derived, `hidOf`),
  and a parser result gives the next value (`ofDS`, `ofUSt`).
* Memory: one description of the element between calls, `SessW`: `DecExt.SbrF` (all of `*sbr`
  the parser owns, typed as the parser types it), the groups only apply owns, and the parser's
  read-only data `PStat`. Each entry's footprint is a regrouping of `SessW` and the objects of
  the call (the bit reader, the bitstream, the output buffers, three fields of `*ac`).
* `SReach`: the values reachable from init, closed under what each entry's postcondition allows,
  with a flag `ok`: `ff_aac_sbr_apply` may follow (not after a failed USAC frame, which returns
  before apply, `aac/aacdec_usac.c`:1659-1661).
* `SInv`: the invariant on the values that every call keeps.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-! ## Values -/

/-- The raw scalars of `*sbr` that only the parser reads: `sbr->usac` (+0x10), `inter_tes`
(+0x14), `bs_amp_res_header` (+0x24), `bs_limiter_bands` (+0x2c). -/
structure HV where
  usac : BitVec 32
  it : BitVec 32
  amp : BitVec 32
  lb : Nat

/-- The session's values. `Args.R` is not used: the caller's memory is part of each call's
frame. -/
abbrev SV := Args × HV

/-- The six bytes of `spectrum_params` (`Args.spLo`, `Args.spHi`, as `ScW` stores them). -/
def spBytes (x : Args) : List UInt8 := Int.toBytes 4 x.spLo.toInt ++ Int.toBytes 2 x.spHi.toInt

/-- The model's hidden state: `bs_start_freq` (byte 0), `bs_xover_band` (byte 2) of
`spectrum_params`, and `bs_limiter_bands`. -/
def hidOf (σ : SV) : Hid := ⟨u8 (spBytes σ.1) 0, u8 (spBytes σ.1) 2, σ.2.lb⟩

/-- `ff_aac_sbr_decode_extension`'s values. -/
def toDS (σ : SV) : DecExt.DS := ⟨σ.1, hidOf σ, σ.2.usac, σ.2.amp, spBytes σ.1, σ.2.it⟩

/-- `ff_aac_sbr_decode_usac_data`'s values, with the reader's index `i`. -/
def toUSt (σ : SV) (i : BitVec 32) : Usac.USt :=
  ⟨σ.1, hidOf σ, i, σ.2.usac, σ.2.amp, spBytes σ.1⟩

/-- The `spectrum_params` fields of `Args` from six bytes. -/
def withSp (x : Args) (sp : List UInt8) : Args :=
  { x with spLo := BitVec.ofInt 32 (Int.ofBytes (sp.take 4)),
           spHi := BitVec.ofInt 16 (Int.ofBytes (sp.drop 4)) }

/-- The session's values after `ff_aac_sbr_decode_extension` returned with `d` (the parser's
`d.a.spLo`/`spHi` are not in its footprint; the bytes `d.sp` are). -/
def ofDS (d : DecExt.DS) : SV := (withSp d.a d.sp, ⟨d.usac, d.it, d.amp, d.h.lb⟩)

/-- The session's values after a USAC entry returned with `st`; `inter_tes` (raw in `UF`) is
`it`. -/
def ofUSt (st : Usac.USt) (it : BitVec 32) : SV := (withSp st.x st.sp, ⟨st.u, it, st.amp, st.h.lb⟩)

/-- `ff_aac_sbr_ctx_alloc_init`'s raw scalars: `av_mallocz` zeroes them. -/
def hvInit : HV := ⟨0, 0, 0, 0⟩

/-- The values after init. -/
def σInit (i : InitIn) : SV := (xInit i, hvInit)

/-! ## The invariant -/

/-- What every call keeps: the model invariant `MI` (with I1 on the bytes, `GridInv`, `Inv2`),
`ff_ps_read_data`'s invariant of `ps->common`, the width of `bs_limiter_bands`, the lengths of
the byte arrays. -/
def SInv (σ : SV) : Prop :=
  MI (σ.1, hidOf σ) ∧ Ps.PsInv σ.1.psc ∧ σ.2.lb ≤ 3 ∧ DecExt.Lens σ.1

/-! ## Steps -/

/-- The events of a session. -/
inductive Ev where
  | dec (id : BitVec 32)
  | usac (cpe : Bool)
  | config
  | apply
  | frame

/-- The value part of each entry's postcondition, with the flag `ok'` of the result. -/
inductive Step : Ev → SV → SV × Bool → Prop
  /-- `ff_aac_sbr_decode_extension`: `DecOut` (with `PsInv` as `PI`) at the values `d`. -/
  | dec {id : BitVec 32} {σ : SV} (d : DecExt.DS) :
      DecExt.DecOut Ps.PsInv ⟨σ.1.R, toDS σ, ⟨0, 0, 0⟩, 0, 0, 0, 0⟩ d →
      Step (.dec id) σ (ofDS d, true)
  /-- `ff_aac_sbr_decode_usac_data` with result `ret`: `UsacOut`, with the field width of
  `bs_limiter_bands` and the array lengths (the strengthened postcondition). -/
  | usac {cpe : Bool} {σ : SV} (st : Usac.USt) (ret it : BitVec 32) :
      MI (st.x, st.h) → (ret = 0#32 → LiveC st.x) → Usac.UKeep σ.1 st.x → Usac.SpOk st →
      st.h.lb ≤ 3 → DecExt.Lens st.x →
      Step (.usac cpe) σ (ofUSt st it, decide (ret = 0#32))
  /-- `ff_aac_sbr_config_usac`: `sbr_turnoff`. -/
  | config {σ : SV} (st : Usac.USt) (it : BitVec 32) :
      (st.x, st.h) = stOff (σ.1, hidOf σ) → Usac.SpOk st → Usac.UKeep σ.1 st.x →
      Step .config σ (ofUSt st it, true)
  /-- `ff_aac_sbr_apply`: `ApplyRel`; `sbr->usac` is raw in `ApplyF` (any `u`), the other raw
  scalars are outside it and kept. -/
  | apply {σ : SV} {y : Args} (u : BitVec 32) :
      ApplyRel σ.1 y → Step .apply σ ((y, { σ.2 with usac := u }), true)
  /-- The caller changes its memory and the `ac` fields (`FrameStep`). -/
  | frame {σ : SV} {x' : Args} (ok : Bool) : FrameStep σ.1 x' → Step .frame σ ((x', σ.2), ok)

/-- The values reachable from `σ₀`, with the flag `ok`. Apply steps only from `ok`; frame steps
keep the flag. -/
inductive SReach (σ₀ : SV) : SV → Bool → Prop
  | init : SReach σ₀ σ₀ true
  | step {σ σ' : SV} {ok ok' : Bool} (ev : Ev) :
      SReach σ₀ σ ok → (ev = .apply → ok = true) → (ev = .frame → ok' = ok) →
      Step ev σ (σ', ok') → SReach σ₀ σ' ok'

variable [CodeEnv]

/-! ## The memory between calls -/

/-- The parser's read-only data: `read_sbr_grid`'s jump table, `ceil_log2`, the SBR and PS
Huffman tables (with the PS constants `ConstW`), `sbr_reset`'s constants and `sbr_offset`, the
limiter table. -/
def PStat (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) : Mem 64 → Prop :=
  Grid.JtW ⋆ (Blocks [(lab "ceil_log2", 6)] ⋆ (Vlc.VlcW vs ⋆ (Ps.PsTabs vp
    ⋆ (Reset.CstR ⋆ Reset.BwR))))

/-- `sbr->ps` without `ps->common`: the rest of `PsW`. -/
def PsRest (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let p := sbrA t + 0x2b600#64
  4 ?@ (p + 764#64) ⋆ (133200 ?@ (p + 768#64) ⋆ (x.psh =@ (p + 133968#64)
    ⋆ 76 ?@ (p + 134036#64)))

/-- **The element between calls.** It depends on the call state only through `ac = arg0` and
`che = arg1`. -/
def SessW (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV) (t : MachineData) :
    Mem 64 → Prop :=
  DecExt.SbrF (toDS σ) (sbrA t) ⋆ (PsRest σ.1 t ⋆ (ArrW t ⋆ (DspW e t ⋆ (FnW e σ.1 t
    ⋆ (AcW σ.1 t ⋆ (CstW ⋆ PStat vs vp))))))

/-- The fields only `ff_aac_sbr_decode_extension` touches: `ac->oc[1].m4ac.sample_rate`,
`ac->warned_he_aac_mono`, `ac->avctx->profile`; owned by the caller per call, any contents. -/
def AcX (ac avctx : BitVec 64) : Mem 64 → Prop :=
  4 ?@ (ac + 0x57e0#64) ⋆ (4 ?@ (ac + 0x8850#64) ⋆ 4 ?@ (avctx + 0x2b0#64))

/-! ## Hypotheses -/

/-- Placement of every text: apply's cluster (`SbrPlaced`) and the parser's routines, and the
layout facts of the link (constant alignments, `read_sbr_grid`'s jump table). Not proved; the
evidence is the re-assembly check of the texts against the objects. -/
structure SessPlaced : Prop where
  /-- `ff_aac_sbr_apply` and its callees, and the dsp kernels, are placed as decoded. -/
  apply : SbrPlaced
  /-- `ff_aac_sbr_decode_extension` is placed as decoded. -/
  decExt : Program.PlacedIn DecExt.body
  /-- `ff_aac_sbr_decode_usac_data` is placed as decoded. -/
  usac : Program.PlacedIn Usac.body
  /-- `ff_aac_sbr_config_usac` is placed as decoded. -/
  config : Program.PlacedIn Usac.cbody
  /-- `read_sbr_header` is placed as decoded. -/
  hdr : Program.PlacedIn Hdr.body
  /-- `sbr_reset` is placed as decoded. -/
  reset : Program.PlacedIn Reset.body
  /-- `sbr_make_f_tablelim` is placed as decoded. -/
  tlim : Program.PlacedIn Tlim.body
  /-- `read_sbr_grid` is placed as decoded. -/
  grid : Program.PlacedIn Grid.body
  /-- `read_sbr_dtdf` is placed as decoded. -/
  dtdf : Program.PlacedIn Dtdf.body
  /-- `read_sbr_invf` is placed as decoded. -/
  invf : Program.PlacedIn Invf.body
  /-- `read_sbr_envelope` is placed as decoded. -/
  env : Program.PlacedIn Env.body
  /-- `read_sbr_noise` is placed as decoded. -/
  noise : Program.PlacedIn Noise.body
  /-- `ff_ps_read_data` is placed as decoded. -/
  ps : Program.PlacedIn Ps.body
  /-- `ff_aac_sbr_ctx_alloc_init` is placed as decoded. -/
  init : Program.PlacedIn Init.body
  /-- The link places `sbr_reset`'s `vmovdqa` constant `LCPI5_6` 16-aligned (as `LayoutC`'s
  label clauses). -/
  lcpi : isAligned 16 (lab "LCPI5_6") = true
  /-- The link places `ff_aac_sbr_apply`'s constants aligned (`LayoutC`'s label clauses). -/
  labs : isAligned 16 (lab "LCPI14_1") = true ∧ isAligned 16 (lab "LCPI14_2") = true
    ∧ isAligned 16 (lab "LCPI14_8") = true ∧ isAligned 32 (lab "sbr_qmf_window_ds") = true
    ∧ isAligned 16 (lab "ff_ps_neg") = true ∧ isAligned 16 (lab "ps_mask") = true
    ∧ isAligned 32 (lab "sbr_qmf_window_us") = true ∧ isAligned 16 (lab "ps_mask2") = true
    ∧ isAligned 16 (lab "ps_mask3") = true ∧ isAligned 16 (lab "ps_noise0") = true
    ∧ isAligned 16 (lab "ps_noise13") = true ∧ isAligned 16 (lab "ps_noise2") = true
    ∧ isAligned 32 (lab "pd_reverse") = true
  /-- The layout of `read_sbr_grid`'s jump table. -/
  jt : Grid.JtC

/-- The assumed external contracts and data facts, with `k` bytes of stack for each external
routine: `ps_apply`, the two transforms, `av_log` on the logging state `e.Ext`, `memcpy` and
`memset` as value contracts (apply's raw-footprint versions follow, `memcpy_of_val`,
`memset_of_val`), `avpriv_request_sample` on `e.Ext`, `powf`/`log2f` as the functions `pw`/`lg` on
`e.Ext` with the floating-point hypothesis `BandsOK` (which includes `NqOK`), and the shape of
the SBR and PS Huffman tables (`VlcC`). (`abort`'s specification holds of any code,
`abortSpec_holds`.) -/
structure SessionAssumed (k : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab)
    (pw : BitVec 32 → BitVec 32 → BitVec 32) (lg : BitVec 32 → BitVec 32) : Prop where
  psApply : PsApplySpec e.PsTab k
  txAna : TxSpec e.Ctx e.TxTab k e.fs.mdctAna
  txSyn : TxSpec e.Ctx e.TxTab k e.fs.qfs.tx
  avLog : AvLogSpec e.Ext k
  memcpyV : MemcpyValSpec k
  memsetV : MemsetValSpec k
  avReq : DecExt.AvReqSpec e.Ext k
  powf : Reset.PowfSpec ⟨e.Ext, pw, lg⟩ k
  log2f : Reset.Log2fSpec ⟨e.Ext, pw, lg⟩ k
  bands : Reset.BandsOK lg pw
  vlcS : Vlc.VlcC vs
  vlcP : Ps.VlcC vp

/-! ## The caller's frames -/

/-- The element's address facts, shared by the entries: `che` 32-aligned (so is `sbr`,
`sbrA_aligned`), the signed bound of apply's `qmf_post_shuffle` operand, no wrap of `*sbr`. -/
def ElemC (t : MachineData) : Prop :=
  isAligned 32 (arg1 t) = true
  ∧ (sbrA t + 0x5fcc0#64).toInt + 1280 < 2 ^ 63 ∧ (sbrA t).toNat + 0x60000 < 2 ^ 64

/-- The bit reader `*gb` of a `decode_extension` call: the reader (`buf`, `size_in_bits_plus8`,
the bytes owned), `size_in_bits`, the padding after `size_in_bits_plus8`. -/
structure Rdr where
  r : DecExt.Rd
  sib : BitVec 32
  pad : BitVec 32

/-- `*gb_host` at `g` with `index = i` (`DecExt.GhW`). -/
abbrev RdrW (g : BitVec 64) (b : Rdr) (i : BitVec 32) : Mem 64 → Prop :=
  Apply.c8 g b.r.buf ⋆ (cell4 (g + 8#64) i ⋆ (cell4 (g + 0xc#64) b.sib
    ⋆ (cell4 (g + 0x10#64) b.r.p8 ⋆ cell4 (g + 0x14#64) b.pad)))

/-- The objects of a `decode_extension` call besides the element: `*gb` at index `i`, the
bitstream bytes, the three `*ac` fields, the caller's rest `Rc`. -/
abbrev DecObj (b : Rdr) (avctx : BitVec 64) (Rc : Mem 64 → Prop) (i : BitVec 32)
    (t : MachineData) : Mem 64 → Prop :=
  RdrW (arg2 t) b i ⋆ (Blocks [(b.r.buf, b.r.L)] ⋆ (AcX (arg0 t) avctx ⋆ Rc))

/-- `ff_aac_sbr_decode_extension(ac, che, gb, crc, cnt, id_aac)` at the values `σ`: the
convention with the element and the call's objects, the reader's bound, the element's address
facts, the ABI alignment, and the stack below this frame for `sbr_reset`'s k-free part
(`0x70` own bytes, `0x9d0`, a return slot). -/
structure DecFrame (kc : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (b : Rdr) (i : BitVec 32) (Rc : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop where
  own : CallPre (DecExt.decNeed kc) (SessW e vs vp σ t ⋆ DecObj b σ.1.avctx Rc i t) ra t
  rd : b.r.ok i
  elem : ElemC t
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true
  stk : 0x70 + 0x9d0 + 8 ≤ (t.regs.get64 .rsp).toNat

/-- The objects of a `decode_usac_data` call: `*gb` (`GbU`) at index `i`, the bitstream bytes,
`ue->sbr` (12 bytes), the caller's rest. -/
abbrev UsacObj (q : Usac.UQ) (i : BitVec 32) : Mem 64 → Prop :=
  Usac.GbU q i ⋆ (Blocks [(q.buf, q.L)] ⋆ (q.uev =@ (q.ue + 0xc#64) ⋆ q.R))

/-- `ff_aac_sbr_decode_usac_data(ac, che, ue, gb, sbr_ch, indep_flag)` at the values `σ`
`q.Ext`, `q.Oth` are not used (the element's `PStat` and `e.Ext` serve). -/
structure UsacFrame (k : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (q : Usac.UQ) (i : BitVec 32) (ra : Int64) (t : MachineData) : Prop where
  own : CallPre (Usac.usacNeed k) (SessW e vs vp σ t ⋆ UsacObj q i) ra t
  args : arg0 t = q.a ∧ arg1 t = q.c ∧ arg2 t = q.ue ∧ arg3 t = q.g
  rd : i.toNat ≤ q.p8.toNat ∧ Usac.GbC q
  /-- `ue->sbr`: twelve bytes, the default header's `start_freq` (4 bits), `limiter_bands`,
  `limiter_gains` (2 bits each), as the configuration parser reads them. -/
  ue : q.uev.length = 12 ∧ u8 q.uev 1 < 16 ∧ u8 q.uev 6 < 4 ∧ u8 q.uev 7 < 4
  /-- `ue->sbr`'s default header `freq_scale` (2 bits, as the configuration parser reads it;
  copied into `spectrum_params` and read by `sbr_reset`). -/
  uev3 : u8 q.uev 3 ≤ 3
  elem : ElemC t
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true
  /-- Room below this frame for the k-free part of `sbr_reset`'s need. -/
  stk : 0x50 + 0x9d0 + 8 ≤ (t.regs.get64 .rsp).toNat

/-- `ff_aac_sbr_config_usac(ac, che, ue)` at the values `σ`. -/
structure ConfigFrame (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (Rc : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop where
  own : CallPre 0 (SessW e vs vp σ t ⋆ Rc) ra t

/-- `ff_aac_sbr_apply(ac, che, id_aac, L, R)` at the values `σ`: the element, the output
buffers, the caller's rest; the element's address facts, the ABI stack alignment, the output
buffers 32-aligned (with `SessPlaced.labs`, apply's `LayoutC`). -/
structure ApplyFrame (k : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (Rc : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop where
  own : CallPre (applyNeed k) (SessW e vs vp σ t ⋆ (OutW σ.1 t ⋆ Rc)) ra t
  elem : ElemC t
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true
  /-- The output buffers `L`, `R` 32-aligned. -/
  out : isAligned 32 (arg3 t) = true ∧ isAligned 32 (arg4 t) = true

end Kraken.Examples.Sbr.SessionBin
