/-
**`main`'s frame within the limit's room from the placement check**
(x86-64): `hroomU` (the first TCB's limit word, `stacksA + 4096`, at most
`main`'s entry `%rsp` less the saved `%rbp` and the frame) for the user
`main` of an `Accepted1` program passing `placeOKAt` at a configuration with
`CfgNeedOk` (budget at most `12288`), with no per-program frame bound.

The chain: `main`'s row `fr.size + 8 ≤ n`, `scc_rt_main`'s row calling it
`sg + 8 + 8 + n ≤ nr` with `sg` its frame (at least `32`), A4's
`nr ≤ budget ≤ 12288`: `fr.size ≤ 12232`, and `fr.size` is `16`-aligned, so
`fr.size ≤ 12224`, `hroomU_ofPlaceOK'`'s bound.

- `mainThread0_frame`: `scc_rt_main`'s frame is at least `32` bytes, in any
  program;
- `mainFrameU_of_rows`: the arithmetic;
- `mainFrameU_of_placeOKAt`: `main`'s frame at most `12224`.
-/
import Spike.Lib.LowerX64.MainD

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Code1X64 (needOk1 callees fnCode1Ok fnOk1 starts fnOk1_of_fnCode1Ok fnOk1_facts)

/-- **`scc_rt_main`'s frame is at least `32` bytes** in any program: its
registers alone take `32` bytes (16-aligned). -/
theorem mainThread0_frame (ir : Scc.IR.Program) :
    32 ≤ (frOf ir (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0)).size := by
  simp only [frOf, Scc.Emit.X64.frameOf]
  have : 32 ≤ (8 * ((Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0).params ++
      (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0).blocks.flatMap fun b =>
        b.insts.flatMap Scc.Emit.X64.instRegs ++ Scc.Emit.X64.termRegs b.term).eraseDups.length + 15) / 16 * 16 := by
    decide
  omega

/-- **`main`'s frame from the two rows and the budget**: `main`'s row
(`needOk1` at `main`, its frame `16`-aligned), `scc_rt_main`'s row calling
`main` at a frame of at least `32`, and A4's entry bound at a budget of at
most `12288`. -/
theorem mainFrameU_of_rows {tbl : List Scc.Cert.NeedX64.Row} {name : String} {fr : Scc.Emit.X64.Frame}
    {f g : Scc.IR.Func} {sg budget : Nat} {entries : List String}
    (hf : needOk1 tbl name fr.size f = true) (hg : needOk1 tbl Scc.Lower.Names.mainThread sg g = true)
    (hsg : 32 ≤ sg) (h16 : fr.size % 16 = 0) (hcall : name ∈ (callees g).1)
    (hent : entries.all (fun e => match Scc.Cert.NeedX64.row? tbl e with
      | some (_, _, n) => decide (n ≤ budget)
      | none => false) = true)
    (hme : entries.contains Scc.Lower.Names.mainThread = true) (hb : budget ≤ 12288) :
    fr.size ≤ 12224 := by
  unfold needOk1 at hf hg
  split at hf
  · next l1 f1 n1 hr1 =>
    split at hg
    · next l2 f2 n2 hr2 =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hf hg
      have he := List.all_eq_true.mp hent _ (List.contains_iff_mem.mp hme)
      rw [hr2] at he
      have hc := hg.1.2 name hcall
      rw [hr1] at hc
      simp only [decide_eq_true_eq] at he hc
      omega
    · simp at hg
  · simp at hf

/-- **`main`'s frame within the limit's room from the placement check**:
for an `Accepted1` program `p` lowered to `em` and an output passing
`placeOKAt` at a configuration with `CfgNeedOk`, a stack-checked function
`f` of the IR named `main` has a frame of at most `12224` bytes. -/
theorem mainFrameU_of_placeOKAt {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hcfg : CfgNeedOk pcfg = true) {f : Scc.IR.Func}
    (hf : f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs) (hname : f.name = Scc.Lower.Names.user "main")
    (hck : f.checkStack = true) :
    (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size ≤ 12224 := by
  obtain ⟨rs, rt, -, hrt, hir, -⟩ := lowerAll_accepted1_x64 cfg hp hlow
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p sizes labelOffs)
  have hg : Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0 ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs := by
    rw [hir]; simp only [Scc.Lower.Inv.progOf]; exact List.mem_append_left _ (mainThread0_mem hrt)
  obtain ⟨n, hn⟩ := mem_starts _ 0 hf
  obtain ⟨m, hm⟩ := mem_starts _ 0 hg
  have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hn hck)
  have h2 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hm rfl)
  simp only [CfgNeedOk, Bool.and_eq_true, decide_eq_true_eq] at hcfg
  have hA := needOk_of_placeOKAt h
  simp only [Scc.Cert.NeedX64.needOk, Bool.and_eq_true] at hA
  exact mainFrameU_of_rows h1 h2 (mainThread0_frame _) (frame16_of_placeOKAt h hf hck).2
    (hname ▸ user_main_mem_callees) hA.1 hcfg.1 hcfg.2

end Spike.Lib.LowerX64
