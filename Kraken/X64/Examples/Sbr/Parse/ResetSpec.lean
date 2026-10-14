import Kraken.X64.Examples.Sbr.Parse.ResetText
import Kraken.X64.Examples.Sbr.ParseModel
import Kraken.X64.Examples.Sbr.Parse.LibCall

/-!
# `sbr_reset`: the specification

`sbr_reset(ac, sbr)` (`libavcodec/aacsbr_template.c`, FFmpeg n8.1) rebuilds the frequency
tables from `sbr->spectrum_params` (`sbr_make_f_master`, then `sbr_make_f_derived`, which calls
`sbr_hf_calc_npatches` and `sbr_make_f_tablelim`); on any failure it logs and calls
`sbr_turnoff`. In the object all of these except `sbr_make_f_tablelim` are inlined.

* Logical variables `RArgs`: the decoder values `x : Args` (`ApplySpec.lean`), the six bytes
  of `sbr->spectrum_params`, `bs_limiter_bands` and `sbr->usac`.
* The footprint `RF` holds the fields the routine reads or writes, byte by byte. The fields
  outside `Args` that it writes (`k[1]`, `k[2]`, `n_master`, `f_master`, both `e_a[1]`) are
  raw; `usac` is a cell (`sbr_turnoff` clears it).
* Callees: `av_log` (`AvLogSpec`), `memcpy` (copies its source), `sbr_make_f_tablelim` (the
  contract `TlimSpec`), and `powf`/`log2f` as functions `pw`/`lg` of their arguments.
* The postcondition is the conclusion of `ParseModel.reset_spec`, with the hidden byte of
  `bs_start_freq` (all of `spectrum_params` is `0xff` after `sbr_turnoff`).
* `BandsOK lg pw` is the one hypothesis on the floating-point results: for every integer input
  the code can reach, the band counts it computes from `log2f` and the band borders it computes
  from `powf` stay in range. It is a closed proposition over finitely many integer inputs.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.Reset

/-! ## The floating-point hypothesis -/

/-- `p`, multiplied by `b` `j` times (`prod *= base` of `make_bands`, as `vmulss`). -/
def chain (b p : BitVec 32) : Nat → BitVec 32
  | 0 => p
  | j + 1 => BitVec.f32mul b (chain b p j)

/-- The float `1.0f`. -/
abbrev f1 : BitVec 32 := 0x3f800000#32

/-- `make_bands(bands, start, stop, nb)` with `base = powf(stop / start, 1 / nb)`: every
`lrintf(prod)` of the loop is in `[0, 64]`. -/
def BandsAt (pw : BitVec 32 → BitVec 32 → BitVec 32) (start stop nb : Nat) : Prop :=
  ∀ j, 1 ≤ j → j < nb →
    let b := pw (BitVec.f32div (BitVec.sitof32 (BitVec.ofNat 32 stop))
                  (BitVec.sitof32 (BitVec.ofNat 32 start)))
                (BitVec.f32div f1 (BitVec.sitof32 (BitVec.ofNat 32 nb)))
    let v := (BitVec.f32toi64 (chain b (BitVec.sitof32 (BitVec.ofNat 32 start)) j)).toInt
    0 ≤ v ∧ v ≤ 64

/-- A band count: `2 * lrintf(h * log2f(stop / start))`, as the code computes it (`int`). -/
def nbOf (lg : BitVec 32 → BitVec 32) (start stop : Nat) (h : BitVec 32) : Int :=
  (BitVec.ofInt 32 (2 * (BitVec.f32toi64 (BitVec.f32mul
    (lg (BitVec.f32div (BitVec.sitof32 (BitVec.ofNat 32 stop))
      (BitVec.sitof32 (BitVec.ofNat 32 start)))) h)).toInt)).toInt

/-- `invwarp` (`.LCPI5_3`): `0.76923…f` if `bs_alter_scale`, else `1.0f`. -/
abbrev invwarp (alter : Nat) : BitVec 32 := if alter = 0 then f1 else 0x3f44ec4f#32

/-- `max_qmf_subbands` for a supported rate (the bound of the check `k[2] - k[0]`). -/
def maxQ (sr : Int) : Int := if sr ≤ 32000 then 48 else if sr = 44100 then 35 else 32

/-- `n_q`: `bs_noise_bands * log2f(k[2] / kx[1])` (`vmulss`), converted to int64 (`vcvtss2si`), is
below `2 ^ 32`: the code clamps it to `≥ 1` as an int64 and then truncates it to 32 bits. For every
`k[2] ≤ 64`, `kx[1] ≤ 32` and 8-bit `bs_noise_bands`. Decidable for a given `lg`. -/
def NqOK (lg : BitVec 32 → BitVec 32) : Prop :=
  ∀ k2, k2 ≤ 64 → ∀ kx, kx ≤ 32 → ∀ nb, nb < 256 →
    (BitVec.f32toi64 (BitVec.f32mul (lg (BitVec.f32div (BitVec.sitof32 (BitVec.ofNat 32 k2))
      (BitVec.sitof32 (BitVec.ofNat 32 kx)))) (BitVec.sitof32 (BitVec.ofNat 32 nb)))).toInt < 2 ^ 32

/-- **The floating-point hypothesis.** For every supported sample rate, every 4-bit
`bs_start_freq` (so `k[0] = k0Of …`), every `k[2] ∈ [k[0], 64]` with
`k[2] - k[0] ≤ max_qmf_subbands`, `bs_freq_scale ∈ {1, 2, 3}` and `bs_alter_scale ∈ {0, 1}`:
the first band count, when positive, is at most 48 and its `make_bands` borders are in
`[0, 64]`; with two regions the second band count is in `[2, 48]` and its borders are in
`[0, 64]`. These are the inputs the code can reach: it checks the rate, `k[2] ≤ 64` and
`k[2] - k[0]` before it calls `log2f`.

Memory safety needs the counts (the code writes `count` int16 into 49-entry stack arrays
before it checks them); the border ranges keep the int16 prefix sums from wrapping, so that
`f_master` is strictly increasing (`TabWF`). Decidable for given `lg`, `pw`; the quantifiers
range over finite sets of integers only. -/
def BandsOK (lg : BitVec 32 → BitVec 32) (pw : BitVec 32 → BitVec 32 → BitVec 32) : Prop :=
  (∀ sr ∈ rates, ∀ start, start < 16 → ∀ k2, k2 ≤ 64 → ∀ fs, 1 ≤ fs → fs ≤ 3 → ∀ alter, alter ≤ 1 →
  match rateRow sr with
  | none => True
  | some row =>
    let k0 := (k0Of sr row start).toNat
    k0 ≤ k2 → (k2 : Int) - k0 ≤ maxQ sr →
    let h0 := BitVec.sitof32 (BitVec.ofNat 32 (7 - fs))
    let k1 := if 110 * k0 < 49 * k2 then 2 * k0 else k2
    let nb0 := nbOf lg k0 k1 h0
    (0 < nb0 → nb0 ≤ 48 ∧ BandsAt pw k0 k1 nb0.toNat)
    ∧ (110 * k0 < 49 * k2 →
        let nb1 := nbOf lg k1 k2 (BitVec.f32mul h0 (invwarp alter))
        2 ≤ nb1 ∧ nb1 ≤ 48 ∧ BandsAt pw k1 k2 nb1.toNat))
  ∧ NqOK lg

/-! ## Logical variables and footprint -/

structure RArgs where
  /-- The decoder values (with the caller's memory `x.R`). -/
  x : Args
  /-- `sbr->spectrum_params` (6 bytes at `sbr + 0x1c`): `bs_start_freq`, `bs_stop_freq`,
  `bs_xover_band`, `bs_freq_scale`, `bs_alter_scale`, `bs_noise_bands`. -/
  sp : List UInt8
  /-- `sbr->bs_limiter_bands` (`sbr + 0x2c`). -/
  lb : BitVec 32
  /-- `sbr->usac` (`sbr + 0x10`): kept, or `0` after `sbr_turnoff`. -/
  us : BitVec 32

/-- The parameters: the callees' state `Ext` (`av_log`, `memcpy`, `powf`, `log2f`) and the
functions `powf`, `log2f`. -/
structure REnv where
  Ext : Mem 64 → Prop
  pw : BitVec 32 → BitVec 32 → BitVec 32
  lg : BitVec 32 → BitVec 32

variable [CodeEnv]

/-- The scalar fields of `*sbr` (`s = sbr`). -/
def ScR (x : Args) (sp : List UInt8) (lb us : BitVec 32) (t : MachineData) : Mem 64 → Prop :=
  let s := arg1 t
  cell4 s x.sampleRate ⋆ (cell4 (s + 0x4#64) x.start ⋆ (cell4 (s + 0x8#64) x.ready
    ⋆ (cell4 (s + 0x10#64) us ⋆ (sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x2c#64) lb
    ⋆ (c4 (s + 0x40#64) x.k0 ⋆ (8 ?@ (s + 0x44#64) ⋆ (c4 (s + 0x58#64) x.kx1
    ⋆ (c4 (s + 0x60#64) x.m1 ⋆ 4 ?@ (s + 0x68#64))))))))))

/-- The tables (the `TabW` cells) and `f_master` (raw). -/
def TabR (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := arg1 t
  c4 (s + 0x4c1e0#64) x.n0 ⋆ (c4 (s + 0x4c1e4#64) x.n1 ⋆ (c4 (s + 0x4c1e8#64) x.nq
    ⋆ (c4 (s + 0x4c1ec#64) x.nlim ⋆ (98 ?@ (s + 0x4c1f0#64) ⋆ (x.ftLow =@ (s + 0x4c252#64)
    ⋆ (x.ftHigh =@ (s + 0x4c284#64) ⋆ (x.ftNoise =@ (s + 0x4c2e6#64)
    ⋆ (x.ftLim =@ (s + 0x4c2f2#64) ⋆ (c4 (s + 0x4c330#64) x.npatch
    ⋆ (x.pnum =@ (s + 0x4c334#64) ⋆ x.pstart =@ (s + 0x4c33a#64)))))))))))

/-- The cells of `sbr->data[0..1]`: `e_a[1]` (raw) and `f_indexnoise`/`f_indexsine`. -/
def DR (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := arg1 t
  4 ?@ (s + 0x3988#64) ⋆ (c8 (s + 0x15b2c#64) x.d0.idx
    ⋆ (4 ?@ (s + 0x19448#64) ⋆ c8 (s + 0x2b5ec#64) x.d1.idx))

/-- Row `r` of `sbr_offset`, as bytes. -/
def sbrOffsetBytes (r : Nat) : List UInt8 :=
  ((sbrOffset.getD r []).map fun z => UInt8.ofNat (z % 256).toNat)

/-- The read-only data: `sbr_offset` (six rows of 16 signed bytes) and the constants. -/
def CstR : Mem 64 → Prop :=
  sbrOffsetBytes 0 =@ lab "sbr_offset_0" ⋆ (sbrOffsetBytes 1 =@ lab "sbr_offset_1"
    ⋆ (sbrOffsetBytes 2 =@ lab "sbr_offset_2" ⋆ (sbrOffsetBytes 3 =@ lab "sbr_offset_3"
    ⋆ (sbrOffsetBytes 4 =@ lab "sbr_offset_4" ⋆ (sbrOffsetBytes 5 =@ lab "sbr_offset_5"
    ⋆ (cell4 (lab "LCPI5_0") 0x42800000#32 ⋆ (cell4 (lab "LCPI5_1") 0x3d9d89d9#32
    ⋆ (cell4 (lab "LCPI5_8") 0xffffffff#32
    ⋆ (Int.toBytes 8 (0x3f8000003f44ec4f : Int) =@ lab "LCPI5_3"
    ⋆ (Int.toBytes 16 (0x3f80000000000000 : Int) =@ lab "LCPI5_2"
    ⋆ (Int.toBytes 16 (0x01000100010001000100010001000100 : Int) =@ lab "LCPI5_4"
    ⋆ (Int.toBytes 16 (0x0f0e0d0c0d0c09080d0c090805040100 : Int) =@ lab "LCPI5_6"
    ⋆ Int.toBytes 16 (0x0d0c090805040100 : Int) =@ lab "LCPI5_9"))))))))))))

/-- `sbr_make_f_tablelim`'s read-only table (12 bytes), passed through to it. -/
abbrev BwR : Mem 64 → Prop := Blocks [(lab "sbr_make_f_tablelim_bw", 12)]

/-- The whole footprint. -/
abbrev RF (e : REnv) (a : RArgs) (t : MachineData) : Mem 64 → Prop :=
  ScR a.x a.sp a.lb a.us t ⋆ (TabR a.x t ⋆ (DR a.x t ⋆ (c8 (arg0 t + 0x8#64) a.x.avctx
    ⋆ (CstR ⋆ (BwR ⋆ e.Ext)))))

/-- The side conditions: the sample rate fact used by the proof is only that `sbr->sample_rate`
is a cell of the footprint (the code dispatches on it; unsupported rates take the error path),
`bs_start_freq < 16`, `bs_freq_scale ≤ 3`, `bs_alter_scale ≤ 1` (the routine runs after a
header, which stores 4-, 2- and 1-bit values), the
`Scal` bounds and the table lengths of the decoder values, `bs_limiter_bands ≤ 3`, no address
wrap of `*sbr`, the ABI stack alignment (`vmovaps` on the frame) and the alignment of the
`vmovdqa` constant, and the k-free part of the stack need (`resetStkMin + 8 ≤ rsp`, implied by
`CallPre (resetNeed k)`).
-/
abbrev resetStkMin : Nat := 0x580 + 0x450

def ResetC (a : RArgs) (t : MachineData) : Prop :=
  a.sp.length = 6 ∧ u8 a.sp 0 < 16 ∧ u8 a.sp 3 ≤ 3 ∧ u8 a.sp 4 ≤ 1 ∧ Scal a.x ∧ a.lb.toNat ≤ 3
  ∧ a.x.ftLow.length = 50 ∧ a.x.ftHigh.length = 98 ∧ a.x.ftNoise.length = 12
  ∧ a.x.ftLim.length = 60 ∧ a.x.pnum.length = 6 ∧ a.x.pstart.length = 6
  ∧ (arg1 t).toNat + 0x60000 < 2 ^ 64
  ∧ isAligned 16 (t.regs.get64 .rsp + 8#64) = true ∧ isAligned 16 (lab "LCPI5_6") = true
  ∧ resetStkMin + 8 ≤ (t.regs.get64 .rsp).toNat

/-- Five pushes and `rbp`, `0x548` bytes of locals, the return slot of a call, the callee's
`k` (`sbr_make_f_tablelim` needs `0x450 + k`). -/
abbrev resetNeed (k : Nat) : Nat := 0x580 + 0x450 + k

abbrev ResetPre (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (resetNeed k) (RF e a t ⋆ a.x.R) ra t ∧ ResetC a t ∧ BandsOK e.lg e.pw

/-- The table lengths (`f_tablelow` … `patch_start_subband`: 50/98/12/60/6/6 bytes). -/
def RLens (x : Args) : Prop :=
  x.ftLow.length = 50 ∧ x.ftHigh.length = 98 ∧ x.ftNoise.length = 12 ∧ x.ftLim.length = 60
  ∧ x.pnum.length = 6 ∧ x.pstart.length = 6

/-- What a return leaves (with the table lengths, on both branches): `reset_spec`'s conclusion, and `spectrum_params`, `usac` kept, or
`spectrum_params` all `0xff` and `usac = 0` after `sbr_turnoff`. `y.R = x.R` and the fields outside `TFrame` that the footprint does not
hold are those of `x`. -/
def ResetOut (a : RArgs) (x' : Args) (sp' : List UInt8) (us' : BitVec 32) : Prop :=
  Scal x' ∧ RLens x' ∧ ∃ y : Args, TFrame a.x y ∧ y.R = a.x.R ∧ y.sampleRate = a.x.sampleRate
    ∧ y.avctx = a.x.avctx
    ∧ ((x' = y.turnoff ∧ sp' = List.replicate 6 0xff ∧ us' = 0)
      ∨ (x' = y ∧ sp' = a.sp ∧ us' = a.us ∧ TabWF y ∧ 1 ≤ y.n0 ∧ 1 ≤ y.npatch))

abbrev ResetPost (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t s : MachineData) : Prop :=
  ∃ (x' : Args) (sp' : List UInt8) (us' : BitVec 32), ResetOut a x' sp' us'
    ∧ CallPost (resetNeed k) (RF e { a with x := x', sp := sp', us := us' } t ⋆ a.x.R) ra t s

/-! ## Callee contracts -/

/-- `powf(a, b)` / `log2f(a)`: the result `pw a b` / `lg a` in the low lane of `xmm0`; the
callee-saved registers, the stack and `Ext` kept. -/
abbrev lo32 (s : MachineData) (r : RegMm) : BitVec 32 := (s.zmms.get (AvxReg.xmm r)).setWidth 32

abbrev PowfSpec (e : REnv) (need : Nat) : Prop :=
  cenv.ProcSpec (entry "powf") (LeafPre need (fun _ => e.Ext) (fun _ => True))
    (fun R ra t s => LeafPost need (fun _ => e.Ext) R ra t s
      ∧ lo32 s .mm0 = e.pw (lo32 t .mm0) (lo32 t .mm1))

abbrev Log2fSpec (e : REnv) (need : Nat) : Prop :=
  cenv.ProcSpec (entry "log2f") (LeafPre need (fun _ => e.Ext) (fun _ => True))
    (fun R ra t s => LeafPost need (fun _ => e.Ext) R ra t s ∧ lo32 s .mm0 = e.lg (lo32 t .mm0))

/-- `sbr_make_f_tablelim(sbr)` (tlim's contract): from `tablelim_spec`'s hypotheses, it writes
`f_tablelim`, `n_lim` as `Tablelim` says. -/
def TlimF (lb : BitVec 32) (a : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := arg0 t
  cell4 (s + 0x2c#64) lb ⋆ (c4 (s + 0x58#64) a.kx1 ⋆ (c4 (s + 0x4c1e0#64) a.n0
    ⋆ (c4 (s + 0x4c1ec#64) a.nlim ⋆ (a.ftLow =@ (s + 0x4c252#64) ⋆ (a.ftLim =@ (s + 0x4c2f2#64)
    ⋆ (c4 (s + 0x4c330#64) a.npatch ⋆ (a.pnum =@ (s + 0x4c334#64)
    ⋆ Blocks [(lab "sbr_make_f_tablelim_bw", 12)])))))))

def TlimC (lb : BitVec 32) (a : Args) (t : MachineData) : Prop :=
  lb.toNat ≤ 3 ∧ a.n0 ≤ 24 ∧ a.npatch ≤ 6 ∧ (0 < lb.toNat → 1 ≤ a.n0 + a.npatch)
  ∧ a.ftLow.length = 50 ∧ a.ftLim.length = 60 ∧ a.pnum.length = 6
  ∧ TabIn a.ftLow a.n0 a.kx1 (a.kx1 + a.m1) ∧ psum a.pnum a.npatch ≤ a.m1 ∧ a.kx1 + a.m1 ≤ 64
  ∧ a.nlim < 2 ^ 32 ∧ (arg0 t).toNat + 0x4c340 < 2 ^ 64

abbrev tlimNeed (k : Nat) : Nat := 0x450 + k

abbrev TlimSpec (k : Nat) : Prop :=
  cenv.ProcSpec (entry "sbr_make_f_tablelim")
    (fun (a : (Mem 64 → Prop) × BitVec 32 × Args) ra t =>
      CallPre (tlimNeed k) (TlimF a.2.1 a.2.2 t ⋆ a.1) ra t ∧ TlimC a.2.1 a.2.2 t)
    (fun a ra t s => ∃ y, Tablelim a.2.1.toNat a.2.2 y
      ∧ CallPost (tlimNeed k) (TlimF a.2.1 y t ⋆ a.1) ra t s)

/-- All callee hypotheses. -/
structure ResetCallees (k : Nat) (e : REnv) : Prop where
  avlog : AvLogSpec e.Ext k
  powf : PowfSpec e k
  log2f : Log2fSpec e k
  memcpy : Parse.MemcpyValSpec k
  tlim : TlimSpec k

abbrev ResetSpec (k : Nat) (e : REnv) : Prop :=
  cenv.ProcSpec (entry "sbr_reset") (ResetPre k e) (ResetPost k e)

end Kraken.Examples.Sbr.Reset
