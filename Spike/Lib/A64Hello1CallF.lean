/-
**`hello1.w`'s caller frame across `print` on AArch64** (G6, item (c) of
the caller-places note: the per-call-site frame condition `F` and the
callee's region bound), hand-written for `hello1`.

> **M3 caveat.** The data here (`wc_main_callF`, the callee's 48 bytes) is
> written by hand for `hello1` and is to be **generated** by the Place
> emitter (`Scc/Cert/Place.lean`), as `wc_<f>_callF : <f>Node → List (Int ×
> Reg)` for each compiled function's return nodes, with the callee's frame
> next to it, for M3. The checks below (`wc_main_callF_rs`,
> `wc_main_callF_env`) pin it to the generated placement data meanwhile, so
> a change to the frame layout fails here rather than silently.

In `hello1` the only call across which a compiled function has words in its
frame is `wc_main`'s call of `scc_rt_print` (return node
`.L19_wc_main.sp4`): `wc_rodata`'s call of the allocator has an environment
of immediates (no slots, `F = True`), and `scc_rt_main` is a runtime frame
with no placement data.

- **The frame condition** (`SlotsF`): the caller's region base `b` (its
  entry `sp`), each listed slot `b + k` holding the value `v r` of its IR
  register `r`. A frame condition no write inside a region below the slots
  breaks (`slotsF_stable`, the `FStable` of `Spike.Lib.A64.Flow.At`).
- **`wc_main` at `sp4`** (`wc_main_callF`): the environment's IR registers
  `a.0`…`a.4` (`sl`, `sl0`, `me`, `a`) at offsets `-96`…`-64` of its 96-byte
  frame, i.e. `sp + 0`…`sp + 32` at the call. `wc_main_sp4_stable`: `print`'s
  region, 48 bytes below the call's `sp` (`seg_print`'s `R.lo ≤ -48`, `R.hi
  = 0`), keeps them.
- **The caller's values at the callee's pairs** (item (a)'s glue):
  `regVals rs σ` is the registers' values in the call node's abstract state
  `σ` (each at its frame slot); `slotsF_of_abs` gives `SlotsF` of them at
  the call; `slots_of_dframe` keeps it under `DFrame` of the callee's region
  (`W.callee kc lo' hi'` of `call_nd`), so at every pair of `seg_print_of`
  (`slots_of_at`). For `hello1`: `wc_main_sp4_slots`, `a.0`…`a.4` holding
  `regVals wc_main_rs σC` at every pair of `print` called from `wc_main`.
  `seg_print`/`seg_print_of` fix the frame condition `DFrame R m0`, while
  `call_nd`'s callee premise asks for every `FStable` frame condition; using
  `print` at a `call_nd` node needs `seg_print` for any such `F` (its block
  nodes only use `FStable.dframe`), which this file does not provide.
- **The headroom** (`wc_main_print_fits`): given the stack check's clause at
  `wc_main`'s entry (`SpOk rS 96`: `lim rS + 96 ≤ sp`, `96` its need in
  `hello1Need`), `wc_main`'s frame and `print`'s region below it do not wrap
  (`Region.OK`) and `print`'s lowest byte is at least `lim rS - 48 ≥ rS.lo`:
  `print` is not stack-checked and runs in the headroom below the limit.
-/
import Spike.Lib.A64Cfg
import Spike.Lib.OwnLim
import Spike.Lib.A64Hello1Code
import Spike.Lib.A64Hello1Place

namespace Spike.Lib.A64.Flow.Hello1.CallF

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.OwnLim (lim)
open Scc.Sem (Range)
open SccPlace.hello1

/-! ## The frame condition -/

/-- **A call site's frame condition**: for the caller's region base `b` and
its IR registers' values `v`, each slot `b + k` of `L` holds `v r`. -/
def SlotsF (b : BitVec 64) (v : Scc.IR.Reg → BitVec 64) (L : List (Int × Scc.IR.Reg)) (m : MachineData) :
    Prop :=
  ∀ p ∈ L, ∃ j, Mem.loadInt m.dmem (b + BitVec.ofInt 64 p.1) 8 = some j ∧ BitVec.ofInt 64 j = v p.2

/-- **The slots survive a callee below them**: in the caller's region `W`
(not wrapping), with every slot of `L` an offset of `W` at or above `c` (an
offset of `W` too), no write inside a region `[W.addr c + lo, W.addr c)`
breaks `SlotsF`. -/
theorem slotsF_stable {W : Region} (hW : W.OK) {c : Int} (hc : W.Off c) {L : List (Int × Scc.IR.Reg)}
    (hL : ∀ p ∈ L, W.Off p.1 ∧ c ≤ p.1) (v : Scc.IR.Reg → BitVec 64) (lo : Int) :
    FStable ⟨W.addr c, lo, 0⟩ (SlotsF W.base v L) := by
  intro m m' hF hD p hp
  obtain ⟨j, hj, hv⟩ := hF p hp
  obtain ⟨hk, hck⟩ := hL p hp
  refine ⟨j, ?_, hv⟩
  have e := W.addr_toNat hW hk
  have ec := W.addr_toNat hW hc
  rw [← hj]
  exact hD (W.addr p.1) (W.addr_fit hW hk) (Or.inr (by simp only; omega))

/-! ## The caller's values, kept through the callee -/

/-- **The IR registers' values in an abstract state** `σ` of the caller's
region: each register at its frame slot `rs` (`wc_<f>_rs`). -/
def regVals (rs : Scc.IR.Reg → Option Int) (σ : AS) : Scc.IR.Reg → BitVec 64 :=
  fun r => σ.slot ((rs r).getD 0)

/-- **The slots hold the node invariant's values**: in a state the caller's
abstract state `σ` describes (`Abs`, as at a call node), `SlotsF` holds of
the registers' values in `σ`, for slots that are offsets of the region at
their registers' frame slots. -/
theorem slotsF_of_abs {W : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs W o m σ)
    {rs : Scc.IR.Reg → Option Int} {L : List (Int × Scc.IR.Reg)} (hrs : ∀ p ∈ L, rs p.2 = some p.1)
    (hL : ∀ p ∈ L, W.Off p.1) : SlotsF W.base (regVals rs σ) L m := by
  intro p hp
  obtain ⟨j, hj, hv⟩ := hA.slot p.1 (hL p hp)
  exact ⟨j, hj, by rw [hv, regVals, hrs p hp]; rfl⟩

/-- **`slots_of_dframe`: the caller's slots are kept by a callee**: with the
callee at offset `kc` of the caller's region `W` (`W.callee kc lo' hi'`, as
in `call_nd`, `hi' ≤ 0`) and every slot of `L` an offset of `W` at or above
`kc`, memory outside the callee's region as at the call (`DFrame`, the
frame condition of `seg_print`/`seg_print_of`) keeps `SlotsF` from the
call's machine data `m0`. -/
theorem slots_of_dframe {W : Region} (hW : W.OK) {kc lo' hi' : Int} (hkl : W.lo ≤ kc) (hkh : kc < W.hi)
    (hhi : hi' ≤ 0) {L : List (Int × Scc.IR.Reg)} (hL : ∀ p ∈ L, W.Off p.1 ∧ kc ≤ p.1)
    {v : Scc.IR.Reg → BitVec 64} {m0 m : MachineData} (h0 : SlotsF W.base v L m0)
    (hD : DFrame (W.callee kc lo' hi') m0 m) : SlotsF W.base v L m := by
  intro p hp
  obtain ⟨j, hj, hv⟩ := h0 p hp
  obtain ⟨hk, hck⟩ := hL p hp
  refine ⟨j, ?_, hv⟩
  have e := W.addr_toNat hW hk
  have ec := Region.addr_toNat_of hW hkl hkh
  rw [← hj]
  exact hD (W.addr p.1) (W.addr_fit hW hk) (Or.inr (by simp only [Region.callee]; omega))

/-- **At every pair of the callee** (`At … (DFrame R' m0)`, the pairs of
`seg_print_of`), the caller's slots hold what they held at the call. -/
theorem slots_of_at {W : Region} (hW : W.OK) {kc lo' hi' : Int} (hkl : W.lo ≤ kc) (hkh : kc < W.hi)
    (hhi : hi' ≤ 0) {L : List (Int × Scc.IR.Reg)} (hL : ∀ p ∈ L, W.Off p.1 ∧ kc ≤ p.1)
    {v : Scc.IR.Reg → BitVec 64} {m0 : MachineData} (h0 : SlotsF W.base v L m0)
    {exe : _root_.Executable} {endPc : Int64} {n : ND} {s : State} {c : Ctl}
    (h : At exe endPc (W.callee kc lo' hi') (DFrame (W.callee kc lo' hi') m0) n s c) :
    SlotsF W.base v L s.st.1 := by
  obtain ⟨-, -, -, -, -, -, hD, -⟩ := h
  exact slots_of_dframe hW hkl hkh hhi hL h0 hD

/-! ## `wc_main` at `sp4` -/

/-- **`wc_main`'s words across each call**: at each return node, the
environment's IR registers by their frame slots (offsets from the region's
base). Hand-written (to be generated, see the header). -/
def wc_main_callF : wc_mainNode → List (Int × Scc.IR.Reg)
  | .b0_entry => []
  | .sp4 => [(-96, "a.0"), (-88, "a.1"), (-80, "a.2"), (-72, "a.3"), (-64, "a.4")]

/-- The offsets are the generated frame slots (`wc_main_rs`). -/
theorem wc_main_callF_rs : (wc_main_callF .sp4).all (fun p => wc_main_rs p.2 == some p.1) = true := by
  decide +kernel

/-- The registers are the environment's at `sp4` (`wc_main_env`): `a`'s
operands are exactly them, and every other variable's are among them. -/
theorem wc_main_callF_env :
    ((wc_main_env .sp4 "a").map (·.2) == some ((wc_main_callF .sp4).map (Scc.IR.Operand.reg ·.2))) = true ∧
      ["sl", "sl0", "me"].all (fun x => ((wc_main_env .sp4 x).map (·.2)).all
        (·.all fun o => ((wc_main_callF .sp4).map (Scc.IR.Operand.reg ·.2)).contains o)) = true := by
  decide +kernel

/-- `wc_main`'s region: its 96-byte frame below the entry `sp` `b`. -/
abbrev wcR (b : BitVec 64) : Region := ⟨b, -96, 0⟩

/-- `print`'s region at the call: 48 bytes below the call's `sp`, `b - 96`. -/
abbrev printR (b : BitVec 64) : Region := ⟨(wcR b).addr (-96), -48, 0⟩

/-- **`print` keeps `wc_main`'s words at `sp4`**: `SlotsF` of
`wc_main_callF .sp4` is a frame condition of `print`'s region. -/
theorem wc_main_sp4_stable {b : BitVec 64} (hW : (wcR b).OK) (v : Scc.IR.Reg → BitVec 64) :
    FStable (printR b) (SlotsF b v (wc_main_callF .sp4)) :=
  slotsF_stable hW (by simp only [Region.Off]; decide) (by
    intro p hp
    simp only [wc_main_callF, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp only [Region.Off] <;> decide) v (-48)

/-- `print`'s region is `call_nd`'s callee region at `wc_main`'s call
(`sp` at offset `-96`, `print`'s frame `[-48, 0)`). -/
theorem printR_callee (b : BitVec 64) : printR b = (wcR b).callee (-96) (-48) 0 := rfl

/-- The slots of `wc_main_callF .sp4` are offsets of any region of
`wc_main` holding its frame, at or above the call's `sp`. -/
theorem wc_main_callF_off {W : Region} (hlo : W.lo ≤ -96) (hhi : 0 ≤ W.hi) :
    ∀ p ∈ wc_main_callF .sp4, W.Off p.1 ∧ -96 ≤ p.1 := by
  intro p hp
  simp only [wc_main_callF, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨⟨by decide, by omega, by omega⟩, by decide⟩

/-- **`wc_main`'s words at every pair of `print`** (the glue of (a) for
`hello1`): at `wc_main`'s call, in its region `W` (any region holding its
frame, based at its entry `sp`) with abstract state `σC` (the call node's
invariant's state, `Abs`), and at any pair of `print` in its region at the
call with frame condition `DFrame _ m0` (`seg_print_of`'s), the slots of
`a.0`…`a.4` hold their values in `σC` (`regVals wc_main_rs σC`). -/
theorem wc_main_sp4_slots {W : Region} (hW : W.OK) (hlo : W.lo ≤ -96) (hhi : 0 ≤ W.hi) {o : SO}
    {m0 : MachineData} {σC : AS} (hA : Abs W o m0 σC) {exe : _root_.Executable} {endPc : Int64} {n : ND}
    {s : State} {c : Ctl} (h : At exe endPc (W.callee (-96) (-48) 0) (DFrame (W.callee (-96) (-48) 0) m0) n s c) :
    SlotsF W.base (regVals wc_main_rs σC) (wc_main_callF .sp4) s.st.1 :=
  slots_of_at hW hlo (by omega) (Int.le_refl 0) (wc_main_callF_off hlo hhi)
    (slotsF_of_abs hA (fun p hp => by
      have := List.all_eq_true.mp wc_main_callF_rs p hp
      simpa using this) (fun p hp => (wc_main_callF_off hlo hhi p hp).1)) h

/-! ## The headroom -/

/-- `wc_main`'s need in the generated table is its frame, 96 bytes: `print`
is not counted, it runs in the headroom. -/
theorem wc_main_need : SccCode.hello1Need.find? (·.1 == "wc_main") = some ("wc_main", 96, 96) := by
  decide +kernel

/-- **`print`'s region fits below `wc_main`'s frame**, given the stack
check's clause at `wc_main`'s entry (`SpOk rS 96` with the entry `sp`
`b`): `wc_main`'s and `print`'s regions do not wrap, and `print`'s lowest
byte is in the headroom, at least `rS.lo`. -/
theorem wc_main_print_fits {rS : Range} {b : BitVec 64} (hsp : lim rS + 96 ≤ b.toNat) :
    (wcR b).OK ∧ (printR b).OK ∧ (rS.lo : Int) + 4048 ≤ ((printR b).base.toNat : Int) - 48 := by
  have hl : lim rS = rS.lo + 4096 := rfl
  have hb := b.isLt
  have hW : (wcR b).OK := ⟨by simp only; omega, by simp only; omega⟩
  have e := (wcR b).addr_toNat hW (k := -96) (by simp only [Region.Off]; decide)
  refine ⟨hW, ⟨by simp only at e ⊢; omega, by simp only at e ⊢; omega⟩, by simp only at e ⊢; omega⟩

end Spike.Lib.A64.Flow.Hello1.CallF
