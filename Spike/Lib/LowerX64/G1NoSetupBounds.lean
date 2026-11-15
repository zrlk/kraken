/-
**The stack bounds of the bare start** (x86-64): for an `Accepted2`
program without a setup block, `scc_rt_main` is `bareMC` (the output's
`.bare` tail, A11's code there) and calls `main` directly; `main`'s row of
the stack need table, a callee room `D` and a switch depth `L` holding
`scc_rt_main`'s call, its frame and `D`, from the placement check at a
configuration with `CfgNeedOk`. The twin of `stackBounds2`
(`Spike/Lib/LowerX64/StackBounds2.lean`) without the setup block's row.

- `mainThread0_bare`: `scc_rt_main` without a setup block is an IR function;
- `mainRowBare`: `main`'s row at its emitted frame and saved `%rbp`, its
  need within the budget past `bareMC`'s frame and `scc_rt_main`'s call;
- `tail_bare_of_accepted2`, `mainUIn_bare2`: the bare tail and A11's
  `scc_rt_main` at `bareMC`;
- `stackBounds0`: the bounds.
-/
import Spike.Lib.LowerX64.StackBounds2
import Spike.Lib.LowerX64.MainRoomU

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Code1X64 (needOk1 callees fnOk1 fnOk1_of_fnCode1Ok)
open Spike.Lib.X64.Rt (bareMC)
open Spike.Lib.X64 (swR)

/-- **`scc_rt_main` without a setup block is an IR function** (x86-64): on
an `Accepted2` program without a setup block whose output passes
`placeOKAt`, the IR holds `Inv.mainThread0` at the entry taking the unit. -/
theorem mainThread0_bare {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) :
    Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0 ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, -, hrt, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_x64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.unit, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  have hw : Spike.Lib.LowerNode.setupWords2 p = 0 := by simp [Spike.Lib.LowerNode.setupWords2, hs]
  have hm : Spike.Lib.LowerNode.setupMask2 p = [] := by simp [Spike.Lib.LowerNode.setupMask2, hs]
  rw [he, hw, hm] at hrt
  rw [hir]; simp only [Scc.Lower.Inv.progOf]; exact List.mem_append_left _ (Spike.Lib.mainThread0_mem hrt)

/-- **`main`'s row without a setup block** (x86-64): on an `Accepted2`
program without a setup block whose output passes `placeOKAt` at a
configuration with `CfgNeedOk`, a stack-checked IR function `f` named
`main` has a row of the stack need table at its emitted frame and saved
`%rbp`, a need `n` at least that, and `bareMC`'s frame, `16` and `n` within
the budget's `12288` (`scc_rt_main`'s frame at least `32`,
`mainThread0_frame`; its edge to `main`; A4's bound on the thread entry). -/
theorem mainRowBare {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) (hcfg : CfgNeedOk pcfg = true)
    {f : Scc.IR.Func} (hf : f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs) (hck : f.checkStack = true)
    (hn : f.name = Scc.Lower.Names.user "main") :
    ∃ l n, Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need f.name =
        some (l, (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size + 8, n) ∧
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size + 8 ≤ n ∧
      bareMC.Z.toInt + 16 + n ≤ 12288 := by
  have hg := mainThread0_bare h hp hs
  have h12 := fnCode1_of_placeOKAt h (place_ir_ofEmitted _ _ _)
  obtain ⟨n1, hn1⟩ := mem_starts _ 0 hf
  obtain ⟨n0, hn0⟩ := mem_starts _ 0 hg
  have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok h12 hn1 hck)
  have h2 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok h12 hn0 rfl)
  have hsg := mainThread0_frame (Scc.Lower.X64.lowerAll cfg p).low.ir
  have hZ : bareMC.Z.toInt = 32 := by decide
  rw [hZ]
  simp only [CfgNeedOk, Bool.and_eq_true, decide_eq_true_eq] at hcfg
  have hA := needOk_of_placeOKAt h
  simp only [Scc.Cert.NeedX64.needOk, Bool.and_eq_true] at hA
  have he := List.all_eq_true.mp hA.1 _ (List.contains_iff_mem.mp hcfg.1)
  have hcall : f.name ∈ (callees (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0)).1 := hn ▸ user_main_mem_callees
  generalize (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fr at h1 ⊢
  generalize (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0)).size = sg
    at h2 hsg
  have hn0 : (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0).name = Scc.Lower.Names.mainThread := rfl
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

/-- **The output of an `Accepted2` program without a setup block has a bare
tail** (the twin of `tail_setup_of_accepted2`): its checked entry is
`entry2 p`, which takes the unit. -/
theorem tail_bare_of_accepted2 {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) :
    (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.tail = .bare := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨-, -, -, -, hc, -, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_x64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.unit, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  simp only [Out.ofEmitted, placeDataOf, hc, Spike.Lib.LowerNode.checked2, he]
  rfl

/-- **A11's `scc_rt_main` at `bareMC`** without a setup block
(`rtCodeOk_bare_of_placeOKAt` at the bare tail). -/
theorem mainUIn_bare2 {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) :
    Spike.Lib.X64.Rt.mainUIn (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog bareMC = true :=
  (Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h (tail_bare_of_accepted2 h hp hs))).main

/-- `bareMC`'s frame is `32`. -/
theorem bareZ_toIntX : bareMC.Z.toInt = 32 := by decide

/-- `bareMC`'s frame's bit vector is `32`. -/
theorem bareZ_toNatX : bareMC.Z.toBitVec.toNat = 32 := by decide

/-- **The stack bounds of the bare start** (x86-64; the twin of
`stackBounds2` without a setup block): on an `Accepted2` program without a
setup block whose output passes `placeOKAt` at a configuration with
`CfgNeedOk`, at any runtime layout `Lr`: `main`'s row (`lM`, frame size
`fM`, need `nM`), the frame size of every stack-checked IR function named
`main` its row's, a callee room `D` (at least the need, `48` and the
runtime's `208`, `needDRX`, and the frame and `48`) and a switch depth `L`
holding `scc_rt_main`'s call, `bareMC`'s frame, `main`'s call and `D`,
8-aligned within the first stack; the limit's room below `bareMC`'s frame
and below it and `fM` at the first stack's top; `%rdi`'s spill slot
`-16` inside `scc_rt_main`'s callee region. -/
theorem stackBounds0 {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) (hcfg : CfgNeedOk pcfg = true)
    (Lr : Spike.Lib.X64.Rt.RuntimeLayout) :
    ∃ (L D : Int) (lM : String) (fM nM : Nat),
      Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
        (Scc.Lower.Names.user "main") = some (lM, fM + 8, nM) ∧ fM + 8 ≤ nM ∧ (nM : Int) + 48 ≤ D ∧
        (nM : Int) + 48 + 208 ≤ D ∧ (fM : Int) + 48 ≤ D ∧
      (∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
        f.name = Scc.Lower.Names.user "main" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fM) ∧
      8 ≤ L ∧ L ≤ 16384 ∧ L % 8 = 0 ∧ 0 ≤ D ∧ D % 8 = 0 ∧
      8 + 8 + bareMC.Z.toInt + 8 + D ≤ L ∧
      Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 -
        bareMC.Z.toBitVec).toNat ∧
      Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 -
        bareMC.Z.toBitVec - 8#64 - 8#64 - (Int64.ofInt (fM : Int)).toBitVec).toNat ∧
      ((swR (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).Off
        (-16) := by
  have hZi := bareZ_toIntX
  have hZb := bareZ_toNatX
  -- `main`'s row
  obtain ⟨jm, dm, hdm, hnm⟩ := Spike.Lib.LowerNode.main_compiled2_ofAccepted2 hp
  obtain ⟨fm, hfm, hckm, hnm'⟩ := userFn2 h hp hdm
  rw [hnm] at hnm'
  obtain ⟨lM, nM, hrM, hfM, hnM⟩ := mainRowBare h hp hs hcfg hfm hckm hnm'
  rw [hnm'] at hrM
  have h16M := (frame16_of_placeOKAt h hfm hckm).2
  -- every function of the name has the row's frame
  have huniq : ∀ (l : String) (fx nx : Nat),
      Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
        (Scc.Lower.Names.user "main") = some (l, fx + 8, nx) →
      ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
        f.name = Scc.Lower.Names.user "main" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fx := by
    intro l fx nx hr f hf hck hn
    obtain ⟨k, hk⟩ := mem_starts _ 0 hf
    have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok (fnCode1_of_placeOKAt h (place_ir_ofEmitted _ _ _)) hk hck)
    unfold needOk1 at h1
    rw [hn, hr] at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    omega
  generalize (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir fm).size = fM at hrM hfM h16M
  obtain ⟨hD2, hDM, hM2, hM3⟩ := needDRX_ok nM
  refine ⟨24 + bareMC.Z.toInt + needDRX nM, needDRX nM, lM, fM, nM,
    hrM, hfM, by omega, hD2, by omega, huniq _ _ _ hrM,
    by omega, by omega, by omega, hM3, hM2, by omega,
    room_le_top Lr (by omega), room_le_top2 Lr ?_, ?_⟩
  · rw [toBitVec_ofInt_toNatX (by omega)]; omega
  · refine ⟨?_, ?_, ?_⟩ <;> (try simp only [Spike.Lib.Region.callee]) <;> omega

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.mainThread0_bare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainThread0_bare

/-- info: 'Spike.Lib.LowerX64.mainRowBare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainRowBare

/-- info: 'Spike.Lib.LowerX64.tail_bare_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tail_bare_of_accepted2

/-- info: 'Spike.Lib.LowerX64.mainUIn_bare2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainUIn_bare2

/-- info: 'Spike.Lib.LowerX64.bareZ_toIntX' does not depend on any axioms -/
#guard_msgs in #print axioms bareZ_toIntX

/-- info: 'Spike.Lib.LowerX64.bareZ_toNatX' does not depend on any axioms -/
#guard_msgs in #print axioms bareZ_toNatX

/-- info: 'Spike.Lib.LowerX64.stackBounds0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackBounds0

end Spike.Lib.LowerX64
