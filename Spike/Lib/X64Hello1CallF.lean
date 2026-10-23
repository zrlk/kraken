/-
**`hello1.w`'s caller frame across `print` on x64** (G6, items (c) and (a)
of the caller-places note), hand-written for `hello1`: the x64 twin of
`Spike/Lib/A64Hello1CallF.lean`.

> **M3 caveat.** The data here (`wc_main_callF`, the callee's region) is
> written by hand for `hello1` and is to be **generated** for M3, as on
> AArch64 (`wc_<f>_callF` from the Place emitter, `Scc/Cert/Place.lean`).
> `scc` writes no placement data on x64, so the offsets are pinned here to
> `wc_main`'s code instead (`wc_main_stores`: its prologue stores the
> argument registers at them) and the registers to the IR environment of
> `hello1.w`'s placement data (`wc_main_callF_env`, ISA-independent: it
> names IR registers only), so a change to the frame layout fails here
> rather than silently.

The x64 frame (regions as in `Spike/Lib/X64Call.lean`, entry offsets
`⟨8, []⟩`): `wc_main`'s region is based at its saved `%rbp` (`%rbp` after
the prologue), the return address in the cell `[8, 16)`. Its arguments
`a.0`…`a.4` (`%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8`) are stored at
`-8(%rbp)`…`-40(%rbp)`, offsets `-8`…`-40`; the frame is 80 bytes
(`subq $80, %rsp`), so at the call `%rsp` is at offset `-88` and `print`'s
region is `call_nd`'s `W.callee (-96) (-40) 16` (`print`'s
`seg_print_of`: `R.lo ≤ -40`, `16 ≤ R.hi`), the slots above it.

- **The frame condition** (`SlotsF`), `slotsF_stable`, `regVals`,
  `slotsF_of_abs`, `slots_of_dframe`, `slots_of_at`: as on AArch64, over
  x64's `Abs`, `DFrame`, `At`; the callee's region may reach above its base
  (`hi'`, the return address cell), below the slots.
- **`wc_main` at `x15`** (the call's return, `.Lwc_main.x15`):
  `wc_main_sp4_stable`, `wc_main_sp4_slots` (named after the AArch64 node
  for symmetry with the AArch64 names; the x64 return label is `.Lwc_main.x15`).
- **The headroom** (`wc_main_print_fits`): from the stack check's clause at
  `wc_main`'s entry (`lim rS + 88 ≤ e`, the entry `%rsp` `e = b + 8`, `88`
  its need in `hello1Need`), the regions do not wrap and `print`'s lowest
  byte is at least `lim rS - 56`, in the headroom.
-/
import Spike.Lib.X64Call
import Spike.Lib.OwnLim
import Spike.Lib.X64Hello1Code
import Spike.Lib.A64Hello1Place

namespace Spike.Lib.X64.Flow.Hello1.CallF

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.OwnLim (lim)
open Scc.Sem (Range)

/-! ## The frame condition -/

/-- **A call site's frame condition**: for the caller's region base `b` and
its IR registers' values `v`, each slot `b + k` of `L` holds `v r`. -/
def SlotsF (b : BitVec 64) (v : Scc.IR.Reg → BitVec 64) (L : List (Int × Scc.IR.Reg)) (m : MachineData) :
    Prop :=
  ∀ p ∈ L, ∃ j, Mem.loadInt m.dmem (b + BitVec.ofInt 64 p.1) 8 = some j ∧ BitVec.ofInt 64 j = v p.2

/-- **The IR registers' values in an abstract state** `σ` of the caller's
region: each register at its frame slot `rs`. -/
def regVals (rs : Scc.IR.Reg → Option Int) (σ : AS) : Scc.IR.Reg → BitVec 64 :=
  fun r => σ.slot ((rs r).getD 0)

/-- **The slots hold the node invariant's values** (`Abs`, as at a call
node). -/
theorem slotsF_of_abs {W : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs W o m σ)
    {rs : Scc.IR.Reg → Option Int} {L : List (Int × Scc.IR.Reg)} (hrs : ∀ p ∈ L, rs p.2 = some p.1)
    (hL : ∀ p ∈ L, W.Off p.1) : SlotsF W.base (regVals rs σ) L m := by
  intro p hp
  obtain ⟨j, hj, hv⟩ := hA.slot p.1 (hL p hp)
  exact ⟨j, hj, by rw [hv, regVals, hrs p hp]; rfl⟩

/-- **`slots_of_dframe`: the caller's slots are kept by a callee** in
`W.callee kb lo' hi'` (`call_nd`'s, `kb` the callee's base offset), every
slot of `L` an offset of `W` at or above the callee's top `kb + hi'`. -/
theorem slots_of_dframe {W : Region} (hW : W.OK) {kb lo' hi' : Int} (hkl : W.lo ≤ kb) (hkh : kb < W.hi)
    {L : List (Int × Scc.IR.Reg)} (hL : ∀ p ∈ L, W.Off p.1 ∧ kb + hi' ≤ p.1)
    {v : Scc.IR.Reg → BitVec 64} {m0 m : MachineData} (h0 : SlotsF W.base v L m0)
    (hD : DFrame (W.callee kb lo' hi') m0 m) : SlotsF W.base v L m := by
  intro p hp
  obtain ⟨j, hj, hv⟩ := h0 p hp
  obtain ⟨hk, hck⟩ := hL p hp
  refine ⟨j, ?_, hv⟩
  have e := W.addr_toNat hW hk
  have ec := Region.addr_toNat_of hW hkl hkh
  rw [← hj]
  exact hD (W.addr p.1) (W.addr_fit hW hk) (Or.inr (by simp only [Region.callee]; omega))

/-- **The slots survive the callee** (`FStable` of the callee's region). -/
theorem slotsF_stable {W : Region} (hW : W.OK) {kb lo' hi' : Int} (hkl : W.lo ≤ kb) (hkh : kb < W.hi)
    {L : List (Int × Scc.IR.Reg)} (hL : ∀ p ∈ L, W.Off p.1 ∧ kb + hi' ≤ p.1) (v : Scc.IR.Reg → BitVec 64) :
    FStable (W.callee kb lo' hi') (SlotsF W.base v L) :=
  fun _ _ h0 hD => slots_of_dframe hW hkl hkh hL h0 hD

/-- **At every pair of the callee** (`At … (DFrame R' m0)`, the pairs of
`seg_print_of`), the caller's slots hold what they held at the call. -/
theorem slots_of_at {W : Region} (hW : W.OK) {kb lo' hi' : Int} (hkl : W.lo ≤ kb) (hkh : kb < W.hi)
    {L : List (Int × Scc.IR.Reg)} (hL : ∀ p ∈ L, W.Off p.1 ∧ kb + hi' ≤ p.1)
    {v : Scc.IR.Reg → BitVec 64} {m0 : MachineData} (h0 : SlotsF W.base v L m0)
    {exe : _root_.Executable} {endPc : Int64} {n : ND} {s : State} {c : Ctl}
    (h : At exe endPc (W.callee kb lo' hi') (DFrame (W.callee kb lo' hi') m0) n s c) :
    SlotsF W.base v L s.st.1 := by
  obtain ⟨-, -, -, -, -, -, hD, -⟩ := h
  exact slots_of_dframe hW hkl hkh hL h0 hD

/-! ## `wc_main` at its call of `print` -/

/-- **`wc_main`'s words across its call of `print`**: the environment's IR
registers by their frame slots (offsets from the region's base, `%rbp`).
Hand-written (to be generated, see the header). -/
def wc_main_callF : List (Int × Scc.IR.Reg) :=
  [(-8, "a.0"), (-16, "a.1"), (-24, "a.2"), (-32, "a.3"), (-40, "a.4")]

/-- The frame slots of `wc_main_callF` as a map (the x64 `wc_main_rs`'s
part for the environment; `scc` writes no x64 placement data). -/
def wc_main_rs (r : Scc.IR.Reg) : Option Int := (wc_main_callF.find? (·.2 == r)).map (·.1)

open Kraken.X64.Parser in
/-- The offsets are where `wc_main`'s prologue stores its argument registers
`%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8` (`a.0`…`a.4`), after `subq $80, %rsp`
(its 80-byte frame), 19 bytes after `.Lwc_main.chk`. -/
theorem wc_main_stores : Scc.Cert.Rt.X64.blockAtB SccCode.hello1Cells ".Lwc_main.chk" 19
    ((parse("subq $80, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)
movq %rdx, -24(%rbp)
movq %rcx, -32(%rbp)
movq %r8, -40(%rbp)")).zip [4, 4, 4, 4, 4, 4]) = true := by
  decide +kernel

/-- The registers are the environment's at the call's return
(`SccPlace.hello1.wc_main_env .sp4`, IR registers only): `a`'s operands are
exactly them, and every other variable's are among them. -/
theorem wc_main_callF_env :
    ((SccPlace.hello1.wc_main_env .sp4 "a").map (·.2) ==
        some (wc_main_callF.map (Scc.IR.Operand.reg ·.2))) = true ∧
      ["sl", "sl0", "me"].all (fun x => ((SccPlace.hello1.wc_main_env .sp4 x).map (·.2)).all
        (·.all fun o => (wc_main_callF.map (Scc.IR.Operand.reg ·.2)).contains o)) = true := by
  decide +kernel

/-- `wc_main_rs` is `wc_main_callF`'s offsets. -/
theorem wc_main_callF_rs : ∀ p ∈ wc_main_callF, wc_main_rs p.2 = some p.1 := by
  intro p hp
  simp only [wc_main_callF, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The slots are offsets of any region of `wc_main` holding its frame, at
or above `print`'s region's top (`-96 + 16`). -/
theorem wc_main_callF_off {W : Region} (hlo : W.lo ≤ -96) (hhi : 0 ≤ W.hi) :
    ∀ p ∈ wc_main_callF, W.Off p.1 ∧ -96 + 16 ≤ p.1 := by
  intro p hp
  simp only [wc_main_callF, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨⟨by decide, by omega, by omega⟩, by decide⟩

/-- **`print` keeps `wc_main`'s words**: `SlotsF` of `wc_main_callF` is a
frame condition of `print`'s region at the call. -/
theorem wc_main_sp4_stable {W : Region} (hW : W.OK) (hlo : W.lo ≤ -96) (hhi : 0 ≤ W.hi)
    (v : Scc.IR.Reg → BitVec 64) : FStable (W.callee (-96) (-40) 16) (SlotsF W.base v wc_main_callF) :=
  slotsF_stable hW hlo (by omega) (wc_main_callF_off hlo hhi) v

/-- **`wc_main`'s words at every pair of `print`** (the glue of (a) for
`hello1` on x64): at `wc_main`'s call, in its region `W` with abstract
state `σC` (`Abs`, the call node's), at any pair of `print` in its region
at the call with frame condition `DFrame _ m0` (`seg_print_of`'s), the
slots of `a.0`…`a.4` hold their values in `σC`. -/
theorem wc_main_sp4_slots {W : Region} (hW : W.OK) (hlo : W.lo ≤ -96) (hhi : 0 ≤ W.hi) {o : SO}
    {m0 : MachineData} {σC : AS} (hA : Abs W o m0 σC) {exe : _root_.Executable} {endPc : Int64} {n : ND}
    {s : State} {c : Ctl}
    (h : At exe endPc (W.callee (-96) (-40) 16) (DFrame (W.callee (-96) (-40) 16) m0) n s c) :
    SlotsF W.base (regVals wc_main_rs σC) wc_main_callF s.st.1 :=
  slots_of_at hW hlo (by omega) (wc_main_callF_off hlo hhi)
    (slotsF_of_abs hA wc_main_callF_rs (fun p hp => (wc_main_callF_off hlo hhi p hp).1)) h

/-! ## The headroom -/

/-- `wc_main`'s need in the generated table is its frame below the entry
`%rsp`, 88 bytes (the saved `%rbp` and 80): `print` is not counted. -/
theorem wc_main_need : SccCode.hello1Need.find? (·.1 == "wc_main") = some ("wc_main", 88, 88) := by
  decide +kernel

/-- **`print`'s region fits below `wc_main`'s frame**, given the stack
check's clause at `wc_main`'s entry (`lim rS + 88 ≤ b + 8`, the entry
`%rsp`): `wc_main`'s frame `[-96, 0)` below its base and `print`'s region
do not wrap, and `print`'s lowest byte is at least `lim rS - 56`. (The
return address cell `[8, 16)` above the base is the caller's to bound.) -/
theorem wc_main_print_fits {rS : Range} {b : BitVec 64} (hsp : lim rS + 88 ≤ b.toNat + 8) :
    (Region.mk b (-96) 0).OK ∧ ((Region.mk b (-96) 0).callee (-96) (-40) 16).OK ∧
      (rS.lo : Int) + 4040 ≤ (((Region.mk b (-96) 0).callee (-96) (-40) 16).base.toNat : Int) - 40 := by
  have hl : lim rS = rS.lo + 4096 := rfl
  have hb := b.isLt
  have hW : (Region.mk b (-96) 0).OK := ⟨by simp only; omega, by simp only; omega⟩
  have e := Region.addr_toNat_of hW (k := -96) (by simp only; omega) (by simp only; omega)
  simp only [Region.callee] at e ⊢
  exact ⟨hW, ⟨by simp only; omega, by simp only; omega⟩, by omega⟩

end Spike.Lib.X64.Flow.Hello1.CallF
