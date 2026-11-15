/-
**The stack bounds of the bare start** (AArch64; the twin of
`stackBounds2A`, `Spike/Lib/LowerA64/StackBounds2A.lean`, without a setup
block): on an `Accepted2` program without a setup block whose output
passes `placeOKAt` at a configuration with `CfgNeedOkA`, `main`'s row of
the stack need table (label `lM`, frame `fM`, need `nM`), the frame of
every stack-checked IR function named `main` its row's, `main`'s callee
room `D = needDR nM` and the switch depth `L = 48 + D`.

`scc_rt_main` is `bareMC` (frame `48`, a constant of the output's `.bare`
tail); the IR's `scc_rt_main` is `mainThread0 ⟨.unit, true⟩ 0` (the entry
`entry2 p` without a setup block, no setup words), of a frame at least `48`
(`mainThread0_frameA`). A12's rows (`needOk1`: `scc_rt_main` calls
`main`, its frame plus `main`'s need within its own need) and A4's budget
of at most `12288` (`CfgNeedOkA`) give `nM ≤ 12240`
(`mainNeedOkA_of_rows`), so `bareMC`'s frame and `main`'s need, frame and
room fit the first stack above the limit.

- `rowFrameA`: the frame of every stack-checked IR function of a name with
  a row is its row's.
- `mainThread0_bareA`: the IR's `scc_rt_main` without a setup block.
- `mainRowBareA`: `main`'s row, its frame and need, `nM ≤ 12240`.
- `tail_bare_of_accepted2A`, `mainUIn_bare2A`: the output's tail is bare,
  and A11 checks `scc_rt_main` at `bareMC`.
- `bareZ_toInt`, `bareZ_toNat`: `bareMC`'s frame is `48`.
- `stackBounds0A`: the bounds.
-/
import Spike.Lib.LowerA64.StackBounds2A
import Spike.Lib.Rt.A64RtCode

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (ctxOf needOk1 callees fnOk1 fnOk1_of_fnCode1Ok)
open Spike.Lib.A64.Rt (bareMC)
open Spike.Lib.A64.Flow (swR)

/-- **The frame of a stack-checked function is its row's** (AArch64): at an
output passing `placeOKAt`, every stack-checked IR function named `nm`
with a row of the stack need table at `nm` has the row's frame (A12's
`needOk1`). -/
theorem rowFrameA {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {nm l : String} {fx nx : Nat}
    (hr : Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need nm = some (l, fx, nx)) :
    ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = nm → (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fx := by
  intro f fi hf hck hn
  have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok (fnCode1_of_placeOKAt h (place_ir_ofEmitted _)) hf hck)
  unfold needOk1 at h1
  rw [hn, hr] at h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact h1.1.1.1.symm

/-- **The IR's `scc_rt_main` without a setup block** (AArch64): on an
`Accepted2` program without a setup block whose output passes `placeOKAt`,
`mainThread0 ⟨.unit, true⟩ 0` is an IR function, at some index. -/
theorem mainThread0_bareA {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) :
    ∃ m, (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0, m) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, -, hrt, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_a64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.unit, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  have hw : Spike.Lib.LowerNode.setupWords2 p = 0 := by simp [Spike.Lib.LowerNode.setupWords2, hs]
  have hm : Spike.Lib.LowerNode.setupMask2 p = [] := by simp [Spike.Lib.LowerNode.setupMask2, hs]
  rw [he, hw, hm] at hrt
  have hg : Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0 ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs := by
    rw [hir]; simp only [Scc.Lower.Inv.progOf]; exact List.mem_append_left _ (Spike.Lib.mainThread0_mem hrt)
  obtain ⟨m, hlt, he'⟩ := List.getElem_of_mem hg
  exact ⟨m, by rw [List.mem_zipIdx_iff_getElem?]; exact List.getElem?_eq_some_iff.mpr ⟨hlt, he'⟩⟩

/-- **`main`'s row without a setup block** (AArch64): on an `Accepted2`
program without a setup block whose output passes `placeOKAt` at a
configuration with `CfgNeedOkA`, `main` has a row of the stack need table
at the frame of its stack-checked IR function, a need at least that frame
and at most `12240` (`mainNeedOkA_of_rows`: `scc_rt_main`'s frame of at
least `48` and its edge to `main`, the budget's `12288`). -/
theorem mainRowBareA {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) (hcfg : CfgNeedOkA pcfg = true) :
    ∃ (l : String) (fM nM : Nat),
      Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
        (Scc.Lower.Names.user "main") = some (l, fM, nM) ∧ fM ≤ nM ∧ nM ≤ 12240 := by
  obtain ⟨jm, dm, hdm, hnm⟩ := Spike.Lib.LowerNode.main_compiled2_ofAccepted2 hp
  obtain ⟨f, fi, hf, hck, hn⟩ := userFn2A h hp hdm
  rw [hnm] at hn
  obtain ⟨m, hg⟩ := mainThread0_bareA h hp hs
  have hc := fnCode1_of_placeOKAt h (place_ir_ofEmitted _)
  have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hf hck)
  have h2 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hg rfl)
  simp only [CfgNeedOkA, Bool.and_eq_true, decide_eq_true_eq] at hcfg
  have hA := needOk_of_placeOKAt h
  simp only [Scc.Cert.NeedA64.needOk, Bool.and_eq_true] at hA
  obtain ⟨l, n, hr, hle, hn12, -⟩ := mainNeedOkA_of_rows h1 h2 (mainThread0_frameA _ m)
    (hn ▸ user_main_mem_calleesA) hA.1 hcfg.1 hcfg.2
  rw [hn] at hr
  exact ⟨l, _, n, hr, hle, hn12⟩

/-- **The output of an `Accepted2` program without a setup block has a bare
tail** (the twin of `tail_setup_of_accepted2A`): its checked entry is
`entry2 p`, which takes the unit. -/
theorem tail_bare_of_accepted2A {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) :
    (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.tail = .bare := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨-, -, -, -, hc, -, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_a64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.unit, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  simp only [Out.ofEmitted, placeDataOf, hc, Spike.Lib.LowerNode.checked2, he]
  rfl

/-- **A11's `scc_rt_main` at `bareMC`** without a setup block
(`rtCodeOk_bare_of_placeOKAt` at the bare tail). -/
theorem mainUIn_bare2A {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) :
    Spike.Lib.A64.Rt.mainUIn (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog bareMC = true :=
  (Spike.Lib.A64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h (tail_bare_of_accepted2A h hp hs))).main

/-- `bareMC`'s frame is `48`. -/
theorem bareZ_toInt : bareMC.Z.toInt = 48 := by decide

/-- `bareMC`'s frame's bit vector is `48`. -/
theorem bareZ_toNat : bareMC.Z.toBitVec.toNat = 48 := by decide

/-- **The stack bounds of the bare start** (AArch64; the twin of
`stackBounds2A` without a setup block): on an `Accepted2` program without a
setup block whose output passes `placeOKAt` at a configuration with
`CfgNeedOkA`, at any runtime layout `Lr`: `main`'s row (`lM`, `fM`, `nM`),
the frame of every stack-checked IR function named `main` its row's, a
callee room `D ≥ nM + 48 + 208` (`needDR nM`) and a switch depth `L`
holding `bareMC`'s frame and `D`, 8-aligned within the first stack, the
limit's room below `bareMC`'s frame and below it and `fM` at the first
stack's top, `bareMC`'s frame inside the switch region. -/
theorem stackBounds0A {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) (hcfg : CfgNeedOkA pcfg = true)
    (Lr : Spike.Lib.A64.Rt.RuntimeLayout) :
    ∃ (L D : Int) (lM : String) (fM nM : Nat),
      Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
          (Scc.Lower.Names.user "main") = some (lM, fM, nM) ∧ fM ≤ nM ∧ (nM : Int) + 48 ≤ D ∧
          (nM : Int) + 48 + 208 ≤ D ∧
        (∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
          f.name = Scc.Lower.Names.user "main" → (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fM) ∧
        0 ≤ L ∧ L ≤ 16384 ∧ L % 8 = 0 ∧ 0 ≤ D ∧ D % 8 = 0 ∧
        bareMC.Z.toInt + D ≤ L ∧
        Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 -
          bareMC.Z.toBitVec).toNat ∧
        Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 -
          bareMC.Z.toBitVec - (Int64.ofInt (fM : Int)).toBitVec).toNat ∧
        (swR (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64) (-L) 0).Off (-bareMC.Z.toInt) := by
  obtain ⟨lM, fM, nM, hr, hle, hn⟩ := mainRowBareA h hp hs hcfg
  obtain ⟨hM1, hDM, hM2, hM3⟩ := needDR_ok nM
  have hZi := bareZ_toInt
  have hZb := bareZ_toNat
  refine ⟨48 + needDR nM, needDR nM, lM, fM, nM, hr, hle, by omega, hM1, rowFrameA h hr,
    by omega, by omega, by omega, hM3, hM2, by omega,
    room_le_topA Lr (by omega), room_le_topA2 Lr ?_, ?_⟩
  · rw [toBitVec_ofInt_toNat (by omega)]; omega
  · rw [hZi]; refine ⟨?_, ?_, ?_⟩ <;> (try simp only [swR]) <;> omega

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.rowFrameA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rowFrameA

/-- info: 'Spike.Lib.LowerA64.mainThread0_bareA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainThread0_bareA

/-- info: 'Spike.Lib.LowerA64.mainRowBareA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainRowBareA

/-- info: 'Spike.Lib.LowerA64.tail_bare_of_accepted2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tail_bare_of_accepted2A

/-- info: 'Spike.Lib.LowerA64.mainUIn_bare2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainUIn_bare2A

/-- info: 'Spike.Lib.LowerA64.stackBounds0A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackBounds0A

end Spike.Lib.LowerA64
