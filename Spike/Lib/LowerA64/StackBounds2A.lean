/-
**The switch depth and stack bounds of `h0InA_setup_assembled`** (AArch64;
the twin of `Spike/Lib/LowerX64/StackBounds2.lean`): on an `Accepted2`
program with a setup block whose output passes `placeOKAt` at a
configuration with `CfgNeedOkA`, a switch depth `L` and callee rooms `D1`
(the setup block `wc_rodata`) and `D2` (`wc_main`) with every bound
`h0InA_setup_assembled` takes (`hL0`, `hLm`, `hL8`, `hD10` … `hD28`, `hL1`,
`hL2`, `hZM`, `hZS`, `hZU`, `hOff`), the callees' frames `ZU1`, `ZU2` their
rows' frames.

`scc_rt_main`'s frame `Z` is A11's (`setupMC (setupWords2 p)`); the stack
need table's rows are at the emitter's frames (`ctxOf`). The two agree by
the code: A11 (`rtCodeOkS`) and A12 (`fnOk1`'s `prologueIn`) both put the
stack check's head `chkHead _` first after `.L1_scc_rt_main.stack_check`
(`blockAt` reads the first such label), so `Z = Int64.ofInt frame`
(`mainZ_eq_frameA`; an output where they differ fails the check). Then A12's
rows (`needOk1`: `scc_rt_main` calls `wc_rodata` and `wc_main`, its frame
plus each callee's need within its own need; each callee's frame within
its need) and A4's budget of at most `12288` (`CfgNeedOkA`) give
`Z + nS, Z + nM ≤ 12288` for the callees' needs `nS`, `nM`.

The choice: `D1 = needDR nS`, `D2 = needDR nM` (the need, the `48` bytes
of the stack check's path, and the deepest runtime routine's `rtMaxA`),
`L = Z + max D1 D2`. The runtime depth is added because `needOk1` does not
count a call of a runtime routine (`scc_rt_alloc`, `scc_rt_print`,
`scc_rt_abort`) in a row's need: it sends such a call into the stack's
headroom (`rtOk`, at most `Tcb.headroom` below the limit), so a callee's
room of `needDA n` alone leaves no room for, e.g., `scc_rt_alloc`'s `208`
bytes below the callee's frame (`allocW2_field`'s `hlo`).

- `blockAt_same`, `chkHead_inj`: two blocks at one place are equal; the
  stack check's head fixes its frame.
- `mainZ_eq_frameA`: A11's `Z` is `scc_rt_main`'s frame (`ctxOf ir 1`).
- `toInt_ofNat_le4095`, `toBitVec_ofInt_toNat`: small `Int64.ofInt`s.
- `userFn2A`: a compiled block's stack-checked IR function.
- `calleeRowA`: a stack-checked callee of `scc_rt_main` has a row at its
  frame, within `Z` of the budget; `user_mem_calleesA`: its two callees.
- `room_le_topA`, `room_le_topA2`: the limit's room at the first stack's
  top.
- `rtMaxA`, `rtMaxA_eq`, `rtDepth_le_rtMaxA`, `needDR`, `needDR_ok`: the
  deepest runtime routine and the callee room with it.
- `stackBounds2A`: the bounds.
-/
import Spike.Lib.LowerA64.SetupSwA12A
import Spike.Lib.LowerA64.SetupTailOfA
import Spike.Lib.LowerA64.MainNeed
import Spike.Lib.LowerA64.CorrectC
import Spike.Lib.MainCompiled2
import Spike.Lib.A64Switch

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (ctxOf needOk1 callees fnOk1 fnOk1_of_fnCode1Ok)
open Scc.Cert.Rt.A64 (blockAt)
open Spike.Lib.A64.Rt (rtCodeOkS setupMC)
open Spike.Lib.A64.Flow (chkHead prologueIn swR)

/-! ## `scc_rt_main`'s frame is A11's -/

/-- **Two blocks of one length at one place are equal.** -/
theorem blockAt_same {prog : List Directive} {l : Label} {k : Nat} {b1 b2 : List Directive}
    (h1 : blockAt prog l k b1 = true) (h2 : blockAt prog l k b2 = true) (hl : b1.length = b2.length) :
    b1 = b2 := by
  simp only [blockAt, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  rw [← h1.2, ← h2.2, hl]

/-- **The stack check's head fixes its frame.** -/
theorem chkHead_inj {Z1 Z2 : Int64} (h : chkHead Z1 = chkHead Z2) : Z1 = Z2 := by
  simpa [chkHead] using h

/-- **A11's `Z` is `scc_rt_main`'s frame** (AArch64): on an `Accepted2`
program with a setup block whose output passes `placeOKAt`, `scc_rt_main`
is the IR's second function, and `setupMC (setupWords2 p)`'s frame is its
emitted frame (`ctxOf ir 1`), at most `4095` and 16-aligned. -/
theorem mainZ_eq_frameA {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) :
    (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p), 1) ∈
        (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx ∧
      (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z = Int64.ofInt (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir 1
        (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).frame ∧
      (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir 1
        (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).frame ≤ 4095 ∧
      (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir 1
        (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).frame % 16 = 0 := by
  have hc := rtCodeOkS_setupWords2A h hp hs
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, -, hrt, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_a64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.setupTid, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  rw [he] at hrt
  have h12 := fnCode1_of_placeOKAt h (place_ir_ofEmitted _)
  generalize (Scc.Lower.A64.lowerAll cfg p).low.ir = ir at hir h12 ⊢
  generalize Spike.Lib.LowerNode.setupWords2 p = sw at hrt hc ⊢
  have hf : (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ sw, 1) ∈ ir.funcs.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, hir]
    simp only [Scc.Lower.Inv.progOf]
    have h1 := mainThread0_idx hrt
    have hlt : 1 < rt.length := (List.getElem?_eq_some_iff.mp h1).1
    rw [List.getElem?_append_left hlt, h1]
  have hok := fnOk1_of_fnCode1Ok h12 hf rfl
  refine ⟨hf, ?_⟩
  unfold fnOk1 at hok
  split at hok
  case h_2 => cases hok
  rename_i b0 bs ps hb hps
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  have hM := hok.1.1.1.1.1.1
  split at hM
  case h_2 => cases hM
  simp only [prologueIn, Bool.and_eq_true] at hM
  have hb1 := hM.1.1.1.1.2
  have hR := Scc.Cert.Rt.A64.rtIn_sound hc
  unfold Spike.Lib.A64.Rt.rtCodeTabS at hR
  have hG := (Scc.Cert.Rt.A64.RtAll.append (Scc.Cert.Rt.A64.RtAll.append (Scc.Cert.Rt.A64.RtAll.append
    (Scc.Cert.Rt.A64.RtAll.append hR).1).1).1).2
  have hb2 : blockAt _ (setupMC sw).sc 0 (chkHead (setupMC sw).Z) = true := hG.2.2.1.1
  have el : (ctxOf ir 1 (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ sw)).local "stack_check" = (setupMC sw).sc := by
    rw [mainLocal]; show _ = ".L1_scc_rt_main.stack_check"; decide +kernel
  rw [el] at hb1
  exact ⟨chkHead_inj (blockAt_same hb2 hb1 rfl), hok.1.1.1.1.1.2, hok.1.1.1.1.2⟩

/-- A small `Int64.ofInt`'s `toInt` is itself. -/
theorem toInt_ofNat_le4095 {k : Nat} (hk : k ≤ 4095) : (Int64.ofInt (k : Int)).toInt = k := by
  have hs : Int64.size = 18446744073709551616 := rfl
  rw [Int64.toInt_ofInt, hs]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A small `Int64.ofInt`'s bit vector is itself. -/
theorem toBitVec_ofInt_toNat {k : Nat} (hk : k < 2 ^ 63) : (Int64.ofInt (k : Int)).toBitVec.toNat = k := by
  rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]; omega

/-! ## The callees' rows -/

/-- **A compiled block's function in the IR** (AArch64): the `j`th compiled
block of an `Accepted2` program whose output passes `placeOKAt` is a
stack-checked function of the IR named `Names.user d.name`. -/
theorem userFn2A {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl} (hd : (Spike.Lib.LowerNode.compiled2 p)[j]? = some d) :
    ∃ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx ∧ f.checkStack = true ∧
      f.name = Scc.Lower.Names.user d.name := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, hws, -, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_a64 cfg hp hem
  obtain ⟨hj, hdj⟩ := List.getElem?_eq_some_iff.mp hd
  have hm := Spike.Lib.LowerNode.mem_progOf_funcs2 cfg.layout rt hws j hj
  rw [← hir] at hm
  exact ⟨_, _, hm, rfl, by show Scc.Lower.Names.user (Spike.Lib.LowerNode.compiled2 p)[j].name = _; rw [hdj]⟩

/-- **A stack-checked callee of `scc_rt_main` has a row at its frame**
(AArch64): at a configuration with `CfgNeedOkA`, a stack-checked function
`f` of the IR (at index `fi`) that `scc_rt_main` calls has a row of the
stack need table at its emitted frame, a need `n` at least that frame,
and `Z + n` within the budget's `12288` (`Z` A11's frame, `mainZ_eq_frameA`;
A12's edge from `scc_rt_main`, A4's bound on the thread entry). -/
theorem calleeRowA {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) (hcfg : CfgNeedOkA pcfg = true)
    {f : Scc.IR.Func} {fi : Nat} (hf : (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx)
    (hck : f.checkStack = true)
    (hcall : f.name ∈ (callees (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).1) :
    ∃ l n, Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need f.name =
        some (l, (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame, n) ∧
      (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame ≤ n ∧
      (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + n ≤ 12288 := by
  obtain ⟨hf0, hZ, h4, -⟩ := mainZ_eq_frameA h hp hs
  have h12 := fnCode1_of_placeOKAt h (place_ir_ofEmitted _)
  have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok h12 hf hck)
  have h2 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok h12 hf0 rfl)
  rw [hZ, toInt_ofNat_le4095 h4]
  simp only [CfgNeedOkA, Bool.and_eq_true, decide_eq_true_eq] at hcfg
  have hA := needOk_of_placeOKAt h
  simp only [Scc.Cert.NeedA64.needOk, Bool.and_eq_true] at hA
  have he := List.all_eq_true.mp hA.1 _ (List.contains_iff_mem.mp hcfg.1)
  generalize (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fr at h1 ⊢
  generalize (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir 1
    (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).frame = sg at h2 ⊢
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
theorem user_mem_calleesA (sw : Nat) :
    Scc.Lower.Names.user "rodata" ∈ (callees (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ sw)).1 ∧
      Scc.Lower.Names.user "main" ∈ (callees (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ sw)).1 := by
  simp [callees, Scc.Lower.Inv.mainThread0, mainInsts_setupA]

/-! ## The bounds -/

/-- **The limit's room below `Z` at the first stack's top**: within the
budget's `12288`, the limit `stacksA + 4096` is below the top less `Z`. -/
theorem room_le_topA (Lr : Spike.Lib.A64.Rt.RuntimeLayout) {Z : Int64} (hZ : Z.toBitVec.toNat ≤ 12288) :
    Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - Z.toBitVec).toNat := by
  rw [show Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab = Lr.stacksA from Lr.lab_stacks, BitVec.toNat_sub,
    Spike.Lib.A64.Rt.top0_toNat Lr]
  have := Lr.pool_fit
  obtain ⟨h1, h2⟩ := Lr.stacks_sub
  simp only at h1 h2
  omega

/-- **The limit's room below `Z` and a callee's frame `U` at the first
stack's top**: within the budget's `12288`, the limit `stacksA + 4096` is
below the top less both. -/
theorem room_le_topA2 (Lr : Spike.Lib.A64.Rt.RuntimeLayout) {Z U : Int64}
    (hZ : Z.toBitVec.toNat + U.toBitVec.toNat ≤ 12288) :
    Lr.stacksA.toNat + 4096 ≤
      (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - Z.toBitVec - U.toBitVec).toNat := by
  rw [show Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab = Lr.stacksA from Lr.lab_stacks, BitVec.toNat_sub,
    BitVec.toNat_sub, Spike.Lib.A64.Rt.top0_toNat Lr]
  have := Lr.pool_fit
  obtain ⟨h1, h2⟩ := Lr.stacks_sub
  simp only at h1 h2
  omega

/-- **The deepest runtime routine's depth** below its caller's `sp`
(`rtDepth`'s largest). -/
def rtMaxA : Nat := (Scc.Cert.Code1A64.rtDepth.map Prod.snd).foldr max 0

theorem rtMaxA_eq : rtMaxA = 208 := by decide

/-- Every runtime routine's depth is at most `rtMaxA`. -/
theorem rtDepth_le_rtMaxA : ∀ e ∈ Scc.Cert.Code1A64.rtDepth, e.2 ≤ rtMaxA := by decide

/-- **A callee's room with the runtime's**: `needDA n` and the deepest
runtime routine's `rtMaxA`. `needOk1` sends a runtime call into the
headroom (`rtOk`), not into the need `n`, so the room adds its depth. -/
def needDR (n : Nat) : Int := needDA n + rtMaxA

/-- **`needDR`'s bounds**: at least the need, `48` and `208`, at most `263`
past the need, 8-aligned, nonnegative. -/
theorem needDR_ok (n : Nat) : (n : Int) + 48 + 208 ≤ needDR n ∧ needDR n ≤ (n : Int) + 55 + 208 ∧
    needDR n % 8 = 0 ∧ 0 ≤ needDR n := by
  unfold needDR needDA; rw [rtMaxA_eq]; omega

/-- **The switch depth and stack bounds of `h0InA_setup_assembled`**
(AArch64): on an `Accepted2` program with a setup block whose output
passes `placeOKAt` at a configuration with `CfgNeedOkA`, at any runtime
layout `Lr`, with `Z` A11's frame `(setupMC (setupWords2 p)).Z`: the rows
of the setup block `wc_rodata` (frame `fS`, need `nS`) and of `wc_main`
(`fM`, `nM`), the frame of every stack-checked IR function of each name
its row's, and a switch depth `L` and callee rooms `D1 ≥ nS + 48 + 208`,
`D2 ≥ nM + 48 + 208` (room for the runtime routines, `needDR`) with `hL0`, `hLm`, `hL8`, `hD10` … `hD28`, `hL1`, `hL2`,
`hZM`, `hZS` / `hZU` at `ZU1 = Int64.ofInt fS` / `ZU2 = Int64.ofInt fM`,
and `hOff`. -/
theorem stackBounds2A {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) (hcfg : CfgNeedOkA pcfg = true)
    (Lr : Spike.Lib.A64.Rt.RuntimeLayout) :
    ∃ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
        (Scc.Lower.Names.user "rodata") = some (lS, fS, nS) ∧ fS ≤ nS ∧ (nS : Int) + 48 ≤ D1 ∧
        (nS : Int) + 48 + 208 ≤ D1 ∧
      Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
        (Scc.Lower.Names.user "main") = some (lM, fM, nM) ∧ fM ≤ nM ∧ (nM : Int) + 48 ≤ D2 ∧
        (nM : Int) + 48 + 208 ≤ D2 ∧
      (∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
        f.name = Scc.Lower.Names.user "rodata" → (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fS) ∧
      (∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
        f.name = Scc.Lower.Names.user "main" → (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fM) ∧
      0 ≤ L ∧ L ≤ 16384 ∧ L % 8 = 0 ∧ 0 ≤ D1 ∧ D1 % 8 = 0 ∧ 0 ≤ D2 ∧ D2 % 8 = 0 ∧
      (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + D1 ≤ L ∧
      (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + D2 ≤ L ∧
      Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 -
        (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec).toNat ∧
      Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 -
        (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec - (Int64.ofInt (fS : Int)).toBitVec).toNat ∧
      Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 -
        (setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec - (Int64.ofInt (fM : Int)).toBitVec).toNat ∧
      (swR (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64) (-L) 0).Off
        (-(setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt) := by
  obtain ⟨-, hZ, h4, h16⟩ := mainZ_eq_frameA h hp hs
  have hge : 16 ≤ (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir 1
      (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).frame := by
    simp only [ctxOf, Scc.Emit.A64.fnCtx, Scc.Emit.A64.align16]; omega
  have hZi := toInt_ofNat_le4095 h4
  have hZb := toBitVec_ofInt_toNat (k := (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir 1
      (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).frame) (by omega)
  rw [← hZ] at hZi hZb
  -- the callees' rows
  obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨jr, dr, hdr, hnr⟩ := Spike.Lib.LowerNode.rodata_compiled2_ofSetupOf hp hty
  obtain ⟨jm, dm, hdm, hnm⟩ := Spike.Lib.LowerNode.main_compiled2_ofAccepted2 hp
  obtain ⟨fr, ir, hfr, hckr, hnr'⟩ := userFn2A h hp hdr
  obtain ⟨fm, im, hfm, hckm, hnm'⟩ := userFn2A h hp hdm
  rw [hnr] at hnr'
  rw [hnm] at hnm'
  obtain ⟨hcr, hcm⟩ := user_mem_calleesA (Spike.Lib.LowerNode.setupWords2 p)
  obtain ⟨lS, nS, hrS, hfS, hnS⟩ := calleeRowA h hp hs hcfg hfr hckr (hnr' ▸ hcr)
  obtain ⟨lM, nM, hrM, hfM, hnM⟩ := calleeRowA h hp hs hcfg hfm hckm (hnm' ▸ hcm)
  rw [hnr'] at hrS
  rw [hnm'] at hrM
  -- every function of each name has the row's frame
  have huniq : ∀ (nm : String) (l : String) (fx nx : Nat),
      Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need nm = some (l, fx, nx) →
      ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
        f.name = nm → (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fx := by
    intro nm l fx nx hr f fi hf hck hn
    have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok (fnCode1_of_placeOKAt h (place_ir_ofEmitted _)) hf hck)
    unfold needOk1 at h1
    rw [hn, hr] at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact h1.1.1.1.symm
  obtain ⟨hS1, hDS, hS2, hS3⟩ := needDR_ok nS
  obtain ⟨hM1, hDM, hM2, hM3⟩ := needDR_ok nM
  refine ⟨(setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + max (needDR nS) (needDR nM), needDR nS,
    needDR nM, lS, lM, _, nS, _, nM, hrS, hfS, by omega, hS1, hrM, hfM, by omega, hM1, huniq _ _ _ _ hrS,
    huniq _ _ _ _ hrM,
    by omega, by omega, by omega, hS3, hS2, hM3, hM2, by omega, by omega,
    room_le_topA Lr (by omega), room_le_topA2 Lr ?_, room_le_topA2 Lr ?_, ?_⟩
  · rw [toBitVec_ofInt_toNat (by omega)]; omega
  · rw [toBitVec_ofInt_toNat (by omega)]; omega
  · refine ⟨?_, ?_, ?_⟩ <;> (try simp only [swR]) <;> omega

-- `hello1.w`'s rows (`Spike/Test/A64Hello1NeedOk1.lean`): `wc_rodata`
-- (frame 48, need 48) calls `scc_rt_alloc` (208 below its frame), `wc_main`
-- (frame 96, need 96) calls `scc_rt_print` (96). `needDA` alone fits neither;
-- `needDR` fits both.
#guard needDA 48 == 96 && needDR 48 == 304 && needDA 96 == 144 && needDR 96 == 352
#guard !decide ((48 : Int) + 208 ≤ needDA 48) && !decide ((96 : Int) + 96 ≤ needDA 96)
#guard decide ((48 : Int) + 208 ≤ needDR 48) && decide ((96 : Int) + 96 ≤ needDR 96)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.blockAt_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms blockAt_same

/-- info: 'Spike.Lib.LowerA64.chkHead_inj' depends on axioms: [propext] -/
#guard_msgs in #print axioms chkHead_inj

/-- info: 'Spike.Lib.LowerA64.mainZ_eq_frameA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainZ_eq_frameA

/-- info: 'Spike.Lib.LowerA64.toInt_ofNat_le4095' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms toInt_ofNat_le4095

/-- info: 'Spike.Lib.LowerA64.toBitVec_ofInt_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms toBitVec_ofInt_toNat

/-- info: 'Spike.Lib.LowerA64.userFn2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms userFn2A

/-- info: 'Spike.Lib.LowerA64.calleeRowA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms calleeRowA

/-- info: 'Spike.Lib.LowerA64.user_mem_calleesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms user_mem_calleesA

/-- info: 'Spike.Lib.LowerA64.rtMaxA_eq' does not depend on any axioms -/
#guard_msgs in #print axioms rtMaxA_eq

/-- info: 'Spike.Lib.LowerA64.rtDepth_le_rtMaxA' does not depend on any axioms -/
#guard_msgs in #print axioms rtDepth_le_rtMaxA

/-- info: 'Spike.Lib.LowerA64.needDR_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms needDR_ok

/-- info: 'Spike.Lib.LowerA64.room_le_topA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms room_le_topA

/-- info: 'Spike.Lib.LowerA64.room_le_topA2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms room_le_topA2

/-- info: 'Spike.Lib.LowerA64.stackBounds2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackBounds2A

end Spike.Lib.LowerA64
