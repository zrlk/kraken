/-
**`main`'s user depth from the placement check** (x86-64): the `D` of
`x64_start_segWS` (`Spike/Lib/LowerX64/StartSegS.lean`) for the user
function `main` of an `Accepted1` program passing `placeOKAt` at a
configuration with `CfgNeedOk`, with no per-program frame bound
(`MainFrame1Ok`'s `4096` is not needed: `CfgNeedOk`'s budget bounds `main`'s
need, and the frame by `needOk1`).

- `frame16_of_placeOKAt`: a stack-checked function's frame is `16`-aligned
  and below `2 ^ 31` (`fnOk1`).
- `mainD_of_placeOKAt`: `D := needD fr n` at `main`'s row `n` of the stack
  need table meets `x64_start_segWS`'s `0 ≤ D`, `D % 8 = 0` and
  `D + 56 ≤ 16384`, and covers the frame (`fr.size + 48 ≤ D`) and the need
  (`n + 40 ≤ D`).
-/
import Spike.Lib.LowerX64.MainNeed

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Code1X64 (needOk1 callees fnCode1Ok fnOk1 starts fnOk1_of_fnCode1Ok fnOk1_facts)

/-- **A stack-checked function's frame from the placement check**: for an
`Accepted1` program passing `placeOKAt`, every stack-checked function of
the IR has a `16`-aligned frame below `2 ^ 31` (`fnOk1`). -/
theorem frame16_of_placeOKAt {cfg : Scc.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {f : Scc.IR.Func} (hf : f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs) (hck : f.checkStack = true) :
    (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size < 2 ^ 31 ∧
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size % 16 = 0 := by
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p sizes labelOffs)
  obtain ⟨n, hn⟩ := mem_starts _ 0 hf
  have h1 := fnOk1_of_fnCode1Ok hc hn hck
  obtain ⟨zl, zf, z1, z2, zs, zps, ps, hz, hps⟩ := fnOk1_sizes h1
  match hb : f.blocks with
  | [] => unfold fnOk1 at h1; rw [hb] at h1; cases h1
  | _ :: _ =>
    obtain ⟨-, -, hlt, h16, -⟩ := fnOk1_facts h1 hb hz hps
    exact ⟨hlt, h16⟩

/-- **`main`'s user depth `D` from the placement check**: for an
`Accepted1` program `p` lowered to `em` and an output passing `placeOKAt`
at a configuration with `CfgNeedOk`, a stack-checked function `f` of the IR
named `main` has a row `n` in the output's stack need table at which `D :=
needD fr n` (`fr` its frame) meets `x64_start_segWS`'s hypotheses on `D`
(`0 ≤ D`, `D % 8 = 0`, `D + 56 ≤ 16384`) and covers the frame and the
need; the frame is `16`-aligned and below `2 ^ 31`. -/
theorem mainD_of_placeOKAt {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hcfg : CfgNeedOk pcfg = true) {f : Scc.IR.Func}
    (hf : f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs) (hname : f.name = Scc.Lower.Names.user "main")
    (hck : f.checkStack = true) :
    ∃ l g n, Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
        f.name = some (l, g, n) ∧
      let fr := frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f
      fr.size < 2 ^ 31 ∧ fr.size % 16 = 0 ∧
      0 ≤ needD fr n ∧ needD fr n % 8 = 0 ∧ needD fr n + 56 ≤ 16384 ∧
      (fr.size : Int) + 48 ≤ needD fr n ∧ (n : Int) + 40 ≤ needD fr n := by
  obtain ⟨l, g, n, hr, hcap⟩ := mainNeedOk_row (mainNeedOk_of_placeOKAt hp hlow h hcfg hf hname hck)
  obtain ⟨hlt, h16⟩ := frame16_of_placeOKAt h hf hck
  obtain ⟨hfr, h8, hD, hn⟩ := needD_ok _ n h16 hcap
  exact ⟨l, g, n, hr, hlt, h16, by omega, h8, hD, hfr, hn⟩

end Spike.Lib.LowerX64
