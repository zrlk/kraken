/-
**The switch depth and stack bounds of `h0In_setup_assembled`** (x86-64;
the twin of `Spike/Lib/LowerA64/StackBounds2A.lean`): on an `Accepted2`
program with a setup block whose output passes `placeOKAt` at a
configuration with `CfgNeedOk`, a switch depth `L` and callee rooms `D1`
(the setup block `wc_rodata`) and `D2` (`wc_main`) with every bound
`h0In_setup_assembled` takes (`hL`, `hLm`, `hL8`, `hD10` … `hD28`, `hD8`,
`hL1`, `hL2`, `hZM`, `hZS`, `hZU`, `hOff`), the callees' frames `ZU1`, `ZU2`
their emitted frames' sizes.

`scc_rt_main`'s frame `Z` is A11's (`setupMC (setupWords2 p)`, A11 taking
`sw < 6`); the stack need table's rows are at the emitter's frames
(`frOf`). The two agree by the code: A11 (`rtCodeOkS`) and A12 (`fnOk1`'s
`prologueIn`) both put the stack check's `leaq -Z(%rsp), %rax` first after
`.Lscc_rt_main.chk` (`blockAtB` reads the first such label), so
`Z = Int64.ofInt size` (`mainZ_eq_frame`; an output where they differ fails
the check). Then A12's rows (`needOk1`: `scc_rt_main` calls `wc_rodata`
and `wc_main`, its frame, saved `%rbp` and return address plus each
callee's need within its own need; each callee's frame and saved `%rbp`
within its need) and A4's budget of at most `12288` (`CfgNeedOk`) give
`Z + 16 + nS, Z + 16 + nM ≤ 12288` for the callees' needs `nS`, `nM`; the
frames being 16-aligned, `32 + Z + fS, 32 + Z + fM ≤ 12288`.

The choice: `D1 = needDRX nS`, `D2 = needDRX nM`, `needDRX n =
8 ⌈(n + 48) / 8⌉ + rtMaxX` (the need, the `48` bytes of the stack check's
path, and the deepest runtime routine's `rtMaxX`; at least `needD`'s two
bounds), `L = 24 + Z + max D1 D2`. The runtime depth is added because
`needOk1` does not count a call of a runtime routine (`scc_rt_alloc`,
`scc_rt_print`, `scc_rt_abort`) in a row's need: it sends such a call into
the stack's headroom (`rtOk`, at most `Tcb.headroom` below the limit), so a
callee's room of the need and `48` alone leaves no room for, e.g.,
`scc_rt_alloc`'s `208` bytes below the callee's frame.

- `blockAtB_same`, `xLea_inj`: two blocks at one place are equal; the
  stack check's `leaq` fixes its frame.
- `mainZ_eq_frame`: A11's `Z` is `scc_rt_main`'s frame (`frOf ir`).
- `toInt_ofNat_lt31`, `toBitVec_ofInt_toNatX`: small `Int64.ofInt`s.
- `userFn2`: a compiled block's stack-checked IR function.
- `calleeRow`: a stack-checked callee of `scc_rt_main` has a row at its
  frame, within `Z` of the budget; `user_mem_callees2`: its two callees.
- `room_le_top`, `room_le_top2`: the limit's room at the first stack's
  top.
- `rtMaxX`, `rtMaxX_eq`, `rtDepth_le_rtMaxX`, `needDRX`, `needDRX_ok`: the
  deepest runtime routine and the callee room with it.
- `stackBounds2`: the bounds.
-/
import Spike.Lib.LowerX64.SetupSwA12
import Spike.Lib.LowerX64.SetupTailOf
import Spike.Lib.LowerX64.MainNeed
import Spike.Lib.LowerX64.MainD
import Spike.Lib.LowerX64.RtMainX
import Spike.Lib.LowerX64.CorrectC
import Spike.Lib.MainCompiled2
import Spike.Lib.X64Switch

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Code1X64 (needOk1 callees fnOk1 fnOk1_of_fnCode1Ok)
open Scc.Cert.Rt.X64 (blockAtB dropBytes)
open Spike.Lib.X64.Rt (rtCodeOkS setupMC)
open Spike.Lib.X64.Flow (xLea prologueIn)
open Spike.Lib.X64 (swR)

/-! ## `scc_rt_main`'s frame is A11's -/

/-- **Two blocks of one length at one place are equal.** -/
theorem blockAtB_same {cells : List (Directive × Nat)} {l : Label} {off : Nat} {b1 b2 : List (Directive × Nat)}
    (h1 : blockAtB cells l off b1 = true) (h2 : blockAtB cells l off b2 = true) (hl : b1.length = b2.length) :
    b1 = b2 := by
  unfold blockAtB at h1 h2
  split at h1
  · rename_i t ht
    rw [ht] at h2
    split at h1
    · rename_i r hr
      simp only [hr, decide_eq_true_eq] at h1 h2
      rw [← h1, ← h2, hl]
    · cases h1
  · cases h1

/-- **The stack check's `leaq` fixes its frame.** -/
theorem xLea_inj {Z1 Z2 : Int64} {z1 z2 : Nat} (h : xLea Z1 z1 = xLea Z2 z2) : Z1 = Z2 := by
  simp [xLea, Kraken.Promising.Lower.X64.op64] at h
  exact h.1

/-- **A11's `Z` is `scc_rt_main`'s frame** (x86-64): on an `Accepted2`
program with a setup block whose output passes `placeOKAt`, `scc_rt_main`
is a stack-checked function of the IR, A11's `sw` is below `6`, and
`setupMC (setupWords2 p)`'s frame is its emitted frame's size (`frOf ir`),
below `2 ^ 31` and 16-aligned. -/
theorem mainZ_eq_frame {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) :
    Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p) ∈
        (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs ∧ Spike.Lib.LowerNode.setupWords2 p < 6 ∧
      (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z = Int64.ofInt (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
        (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).size ∧
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
        (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).size < 2 ^ 31 ∧
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
        (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).size % 16 = 0 := by
  have hc := rtCodeOkS_setupWords2 h hp hs
  have hsw : Spike.Lib.LowerNode.setupWords2 p < 6 := by
    obtain ⟨sw, hsw, hc', -⟩ := Scc.Cert.PlaceOK.X64.setupIn_of_placeOKAt h (tail_setup_of_accepted2 h hp hs)
    rw [sw_eq_setupWords2 h hp hs hc']; exact hsw
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, -, hrt, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_x64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.setupTid, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  rw [he] at hrt
  have h12 := fnCode1_of_placeOKAt h (place_ir_ofEmitted _ _ _)
  generalize (Scc.Lower.X64.lowerAll cfg p).low.ir = ir at hir h12 ⊢
  generalize Spike.Lib.LowerNode.setupWords2 p = sw at hrt hc hsw ⊢
  have hf : Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ sw ∈ ir.funcs := by
    rw [hir]
    exact List.mem_append_left _ (Spike.Lib.mainThread0_mem hrt)
  obtain ⟨n, hn⟩ := mem_starts ir 0 hf
  have hok := fnOk1_of_fnCode1Ok h12 hn rfl
  refine ⟨hf, hsw, ?_⟩
  unfold fnOk1 at hok
  split at hok
  case h_2 => cases hok
  rename_i b0 bs zl zf z1 z2 zs zps hb hz
  split at hok
  case h_2 => cases hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  have hM := hok.1.1.1.1.1.1.2
  simp only [prologueIn, Bool.and_eq_true] at hM
  have hb1 := hM.1.1.1.1.2
  have hR := Scc.Cert.Rt.X64.rtIn_sound hc
  unfold Spike.Lib.X64.Rt.rtCodeTabS at hR
  have hG := (Scc.Cert.Rt.X64.RtAll.append (Scc.Cert.Rt.X64.RtAll.append (Scc.Cert.Rt.X64.RtAll.append
    (Scc.Cert.Rt.X64.RtAll.append hR).1).1).1).2
  have hb2 : blockAtB _ (setupMC sw).sc 0 (xLea (setupMC sw).Z 5) = true := hG.2.2.1.1
  have el : Scc.Cert.Code1X64.chkL (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ sw) = (setupMC sw).sc := by
    show Scc.Emit.X64.labelOf "scc_rt_main" "chk" = ".Lscc_rt_main.chk"; decide +kernel
  rw [el] at hb1
  exact ⟨xLea_inj (blockAtB_same hb2 hb1 rfl), hok.1.1.1.1.1.2, hok.1.1.1.1.2⟩

/-- A small `Int64.ofInt`'s `toInt` is itself. -/
theorem toInt_ofNat_lt31 {k : Nat} (hk : k < 2 ^ 31) : (Int64.ofInt (k : Int)).toInt = k := by
  have hs : Int64.size = 18446744073709551616 := rfl
  rw [Int64.toInt_ofInt, hs]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A small `Int64.ofInt`'s bit vector is itself. -/
theorem toBitVec_ofInt_toNatX {k : Nat} (hk : k < 2 ^ 63) : (Int64.ofInt (k : Int)).toBitVec.toNat = k := by
  rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]; omega

/-! ## The callees' rows -/

/-- **A compiled block's function in the IR** (x86-64): the `j`th compiled
block of an `Accepted2` program whose output passes `placeOKAt` is a
stack-checked function of the IR named `Names.user d.name`. -/
theorem userFn2 {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl} (hd : (Spike.Lib.LowerNode.compiled2 p)[j]? = some d) :
    ∃ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs ∧ f.checkStack = true ∧
      f.name = Scc.Lower.Names.user d.name := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, hws, -, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_x64 cfg hp hem
  obtain ⟨hj, hdj⟩ := List.getElem?_eq_some_iff.mp hd
  have hm := Spike.Lib.LowerNode.mem_progOf_funcs2 cfg.layout rt hws j hj
  rw [← hir] at hm
  exact ⟨_, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hm), rfl,
    by show Scc.Lower.Names.user (Spike.Lib.LowerNode.compiled2 p)[j].name = _; rw [hdj]⟩

/-- **A stack-checked callee of `scc_rt_main` has a row at its frame**
(x86-64): at a configuration with `CfgNeedOk`, a stack-checked function `f`
of the IR that `scc_rt_main` calls has a row of the stack need table at
its emitted frame and saved `%rbp`, a need `n` at least that, and
`Z + 16 + n` within the budget's `12288` (`Z` A11's frame,
`mainZ_eq_frame`; A12's edge from `scc_rt_main`, A4's bound on the thread
entry). -/
theorem calleeRow {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) (hcfg : CfgNeedOk pcfg = true)
    {f : Scc.IR.Func} (hf : f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs) (hck : f.checkStack = true)
    (hcall : f.name ∈ (callees (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).1) :
    ∃ l n, Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need f.name =
        some (l, (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size + 8, n) ∧
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size + 8 ≤ n ∧
      (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + 16 + n ≤ 12288 := by
  obtain ⟨hf0, -, hZ, h31, -⟩ := mainZ_eq_frame h hp hs
  have h12 := fnCode1_of_placeOKAt h (place_ir_ofEmitted _ _ _)
  obtain ⟨n1, hn1⟩ := mem_starts _ 0 hf
  obtain ⟨n0, hn0⟩ := mem_starts _ 0 hf0
  have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok h12 hn1 hck)
  have h2 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok h12 hn0 rfl)
  rw [hZ, toInt_ofNat_lt31 h31]
  simp only [CfgNeedOk, Bool.and_eq_true, decide_eq_true_eq] at hcfg
  have hA := needOk_of_placeOKAt h
  simp only [Scc.Cert.NeedX64.needOk, Bool.and_eq_true] at hA
  have he := List.all_eq_true.mp hA.1 _ (List.contains_iff_mem.mp hcfg.1)
  generalize (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fr at h1 ⊢
  generalize (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
    (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).size = sg at h2 ⊢
  have hn0 : (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p)).name =
      Scc.Lower.Names.mainThread := rfl
  rw [hn0] at h2
  unfold needOk1 at h1 h2
  split at h1
  · next l1 f1 n1 hr1 =>
    split at h2
    · next l2 f2 n2 hr2 =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h1 h2
      rw [hr2] at he
      have hc := h2.1.2 f.name hcall
      rw [hr1] at hc
      simp only [decide_eq_true_eq] at he hc
      obtain ⟨⟨⟨hfr, hle⟩, -⟩, -⟩ := h1
      subst hfr
      exact ⟨l1, n1, hr1, hle, by omega⟩
    · simp at h2
  · simp at h1

/-- **`scc_rt_main` calls the setup block and `main`** (after a setup block
of `sw` words). -/
theorem user_mem_callees2 (sw : Nat) :
    Scc.Lower.Names.user "rodata" ∈ (callees (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ sw)).1 ∧
      Scc.Lower.Names.user "main" ∈ (callees (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ sw)).1 := by
  simp [callees, Scc.Lower.Inv.mainThread0, mainInsts_setup]

/-! ## The bounds -/

/-- **The limit's room below the frame record and `Z` at the first stack's
top**: within the budget's `12288`, the limit `stacksA + 4096` is below the
top less `16` and `Z`. -/
theorem room_le_top (Lr : Spike.Lib.X64.Rt.RuntimeLayout) {Z : Int64} (hZ : Z.toBitVec.toNat + 16 ≤ 12288) :
    Lr.stacksA.toNat + 4096 ≤
      (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 - Z.toBitVec).toNat := by
  rw [show Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab = Lr.stacksA from Lr.lab_stacks]
  simp only [BitVec.toNat_sub, Spike.Lib.X64.Rt.top0_toNat Lr, BitVec.toNat_ofNat]
  have := Lr.pool_fit
  obtain ⟨h1, h2⟩ := Lr.stacks_sub
  simp only at h1 h2
  omega

/-- **The limit's room below `Z` and a callee's frame `U` at the first
stack's top**: within the budget's `12288`, the limit `stacksA + 4096` is
below the top less both and the two calls' `32` bytes. -/
theorem room_le_top2 (Lr : Spike.Lib.X64.Rt.RuntimeLayout) {Z U : Int64}
    (hZ : Z.toBitVec.toNat + U.toBitVec.toNat + 32 ≤ 12288) :
    Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 -
      Z.toBitVec - 8#64 - 8#64 - U.toBitVec).toNat := by
  rw [show Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab = Lr.stacksA from Lr.lab_stacks]
  simp only [BitVec.toNat_sub, Spike.Lib.X64.Rt.top0_toNat Lr, BitVec.toNat_ofNat]
  have := Lr.pool_fit
  obtain ⟨h1, h2⟩ := Lr.stacks_sub
  simp only at h1 h2
  omega

/-- **The deepest runtime routine's depth** below its caller's `rsp`
(`rtDepth`'s largest). -/
def rtMaxX : Nat := (Scc.Cert.Code1X64.rtDepth.map Prod.snd).foldr max 0

theorem rtMaxX_eq : rtMaxX = 208 := by decide

/-- Every runtime routine's depth is at most `rtMaxX`. -/
theorem rtDepth_le_rtMaxX : ∀ e ∈ Scc.Cert.Code1X64.rtDepth, e.2 ≤ rtMaxX := by decide

/-- **A callee's room with the runtime's**: the need and `48` rounded up to
8, and the deepest runtime routine's `rtMaxX`. `needOk1` sends a runtime
call into the headroom (`rtOk`), not into the need `n`, so the room adds its
depth. -/
def needDRX (n : Nat) : Int := 8 * (((n : Int) + 48 + 7) / 8) + rtMaxX

/-- **`needDRX`'s bounds**: at least the need, `48` and `208`, at most `263`
past the need, 8-aligned, nonnegative. -/
theorem needDRX_ok (n : Nat) : (n : Int) + 48 + 208 ≤ needDRX n ∧ needDRX n ≤ (n : Int) + 55 + 208 ∧
    needDRX n % 8 = 0 ∧ 0 ≤ needDRX n := by
  unfold needDRX; rw [rtMaxX_eq]; omega

/-- **The switch depth and stack bounds of `h0In_setup_assembled`**
(x86-64): on an `Accepted2` program with a setup block whose output passes
`placeOKAt` at a configuration with `CfgNeedOk`, at any runtime layout
`Lr`, with `Z` A11's frame `(setupMC (setupWords2 p)).Z`: the rows of the
setup block `wc_rodata` (frame size `fS`, need `nS`) and of `wc_main`
(`fM`, `nM`), the frame size of every stack-checked IR function of each
name its row's, and a switch depth `L` and callee rooms `D1`, `D2` (at
least the need and `48`, the need, `48` and the runtime's `208`, `needDRX`,
and the frame and `48`) with `hL`, `hLm`, `hL8`,
`hD10` … `hD28`, `hD8`, `hL1`, `hL2`, `hZM`, `hZS` / `hZU` at
`ZU1 = Int64.ofInt fS` / `ZU2 = Int64.ofInt fM`, and `hOff`. -/
theorem stackBounds2 {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) (hcfg : CfgNeedOk pcfg = true)
    (Lr : Spike.Lib.X64.Rt.RuntimeLayout) :
    ∃ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
        (Scc.Lower.Names.user "rodata") = some (lS, fS + 8, nS) ∧ fS + 8 ≤ nS ∧ (nS : Int) + 48 ≤ D1 ∧
        (nS : Int) + 48 + 208 ≤ D1 ∧ (fS : Int) + 48 ≤ D1 ∧
      Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
        (Scc.Lower.Names.user "main") = some (lM, fM + 8, nM) ∧ fM + 8 ≤ nM ∧ (nM : Int) + 48 ≤ D2 ∧
        (nM : Int) + 48 + 208 ≤ D2 ∧ (fM : Int) + 48 ≤ D2 ∧
      (∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
        f.name = Scc.Lower.Names.user "rodata" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS) ∧
      (∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
        f.name = Scc.Lower.Names.user "main" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fM) ∧
      8 ≤ L ∧ L ≤ 16384 ∧ L % 8 = 0 ∧ 0 ≤ D1 ∧ D1 % 8 = 0 ∧ 0 ≤ D2 ∧ D2 % 8 = 0 ∧ 8 ≤ D1 ∧
      8 + 8 + (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + 8 + D1 ≤ L ∧
      8 + 8 + (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + 8 + D2 ≤ L ∧
      Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 -
        (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec).toNat ∧
      Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 -
        (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec - 8#64 - 8#64 -
        (Int64.ofInt (fS : Int)).toBitVec).toNat ∧
      Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 -
        (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec - 8#64 - 8#64 -
        (Int64.ofInt (fM : Int)).toBitVec).toNat ∧
      (((swR (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).Off (-16) ∧
        ∀ j < (setupMC (Spike.Lib.LowerNode.setupWords2 p)).sw,
          ((swR (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).Off
            (-24 - 8 * (j : Int))) := by
  obtain ⟨-, hsw, hZ, h31, h16⟩ := mainZ_eq_frame h hp hs
  have hZi := toInt_ofNat_lt31 h31
  have hZb := toBitVec_ofInt_toNatX (k := (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
      (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).size) (by omega)
  rw [← hZ] at hZi hZb
  have hZf := setupMC_Z _ hsw
  have hsw' : (setupMC (Spike.Lib.LowerNode.setupWords2 p)).sw = Spike.Lib.LowerNode.setupWords2 p := rfl
  -- the callees' rows
  obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨jr, dr, hdr, hnr⟩ := Spike.Lib.LowerNode.rodata_compiled2_ofSetupOf hp hty
  obtain ⟨jm, dm, hdm, hnm⟩ := Spike.Lib.LowerNode.main_compiled2_ofAccepted2 hp
  obtain ⟨fr, hfr, hckr, hnr'⟩ := userFn2 h hp hdr
  obtain ⟨fm, hfm, hckm, hnm'⟩ := userFn2 h hp hdm
  rw [hnr] at hnr'
  rw [hnm] at hnm'
  obtain ⟨hcr, hcm⟩ := user_mem_callees2 (Spike.Lib.LowerNode.setupWords2 p)
  obtain ⟨lS, nS, hrS, hfS, hnS⟩ := calleeRow h hp hs hcfg hfr hckr (hnr' ▸ hcr)
  obtain ⟨lM, nM, hrM, hfM, hnM⟩ := calleeRow h hp hs hcfg hfm hckm (hnm' ▸ hcm)
  rw [hnr'] at hrS
  rw [hnm'] at hrM
  have h16S := (frame16_of_placeOKAt h hfr hckr).2
  have h16M := (frame16_of_placeOKAt h hfm hckm).2
  -- every function of each name has the row's frame
  have huniq : ∀ (nm : String) (l : String) (fx nx : Nat),
      Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need nm =
        some (l, fx + 8, nx) →
      ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
        f.name = nm → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fx := by
    intro nm l fx nx hr f hf hck hn
    obtain ⟨k, hk⟩ := mem_starts _ 0 hf
    have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok (fnCode1_of_placeOKAt h (place_ir_ofEmitted _ _ _)) hk hck)
    unfold needOk1 at h1
    rw [hn, hr] at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    omega
  generalize (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir fr).size = fS at hrS hfS h16S
  generalize (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir fm).size = fM at hrM hfM h16M
  obtain ⟨hD1, hDS, hS2, hS3⟩ := needDRX_ok nS
  obtain ⟨hD2, hDM, hM2, hM3⟩ := needDRX_ok nM
  refine ⟨24 + (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + max (needDRX nS) (needDRX nM),
    needDRX nS, needDRX nM, lS, lM, fS, nS, fM, nM,
    hrS, hfS, by omega, hD1, by omega, hrM, hfM, by omega, hD2, by omega, huniq _ _ _ _ hrS, huniq _ _ _ _ hrM,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    room_le_top Lr (by omega), room_le_top2 Lr ?_, room_le_top2 Lr ?_, ?_, ?_⟩
  · rw [toBitVec_ofInt_toNatX (by omega)]; omega
  · rw [toBitVec_ofInt_toNatX (by omega)]; omega
  · refine ⟨?_, ?_, ?_⟩ <;> (try simp only [Region.callee]) <;> omega
  · intro j hj
    rw [hsw'] at hj
    refine ⟨?_, ?_, ?_⟩ <;> (try simp only [Region.callee]) <;> omega

-- The room adds the deepest runtime routine's 208 to the need and `48`,
-- rounded up to 8.
#guard needDRX 0 == 256 && needDRX 48 == 304 && needDRX 81 == 344

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.blockAtB_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms blockAtB_same

/-- info: 'Spike.Lib.LowerX64.xLea_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms xLea_inj

/-- info: 'Spike.Lib.LowerX64.mainZ_eq_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainZ_eq_frame

/-- info: 'Spike.Lib.LowerX64.toInt_ofNat_lt31' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms toInt_ofNat_lt31

/-- info: 'Spike.Lib.LowerX64.toBitVec_ofInt_toNatX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms toBitVec_ofInt_toNatX

/-- info: 'Spike.Lib.LowerX64.userFn2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms userFn2

/-- info: 'Spike.Lib.LowerX64.calleeRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms calleeRow

/-- info: 'Spike.Lib.LowerX64.user_mem_callees2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms user_mem_callees2

/-- info: 'Spike.Lib.LowerX64.rtMaxX_eq' does not depend on any axioms -/
#guard_msgs in #print axioms rtMaxX_eq

/-- info: 'Spike.Lib.LowerX64.rtDepth_le_rtMaxX' does not depend on any axioms -/
#guard_msgs in #print axioms rtDepth_le_rtMaxX

/-- info: 'Spike.Lib.LowerX64.needDRX_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms needDRX_ok

/-- info: 'Spike.Lib.LowerX64.room_le_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms room_le_top

/-- info: 'Spike.Lib.LowerX64.room_le_top2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms room_le_top2

/-- info: 'Spike.Lib.LowerX64.stackBounds2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackBounds2

end Spike.Lib.LowerX64
